// A simple lexer inspired by work of Sulzmann & Lu
//==================================================
//

import scala.language.reflectiveCalls
import scala.language.implicitConversions

// regular expressions including records
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class OPT(r: Rexp) extends Rexp
case class RANGE(cs: List[Char]) extends Rexp
case class NOT(r: Rexp) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class UPTO(r: Rexp, n:Int) extends Rexp
case class FROM(r: Rexp, n:Int) extends Rexp
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp
case class ALL() extends Rexp
case class RECD(x: String, r: Rexp) extends Rexp  
          // records for extracting strings or tokens
  
// values  
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Pluss(vs: List[Val]) extends Val
case class Optional(v: Val) extends Val
case class Ntimess(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
   
// some convenience for typing in regular expressions

def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case OPT(r) => true 
  case RANGE(_) => false
  case NOT(r) => !nullable(r)
  case PLUS(r) => nullable(r)
  case UPTO(r, i) => true
  case FROM(r, i) => if (i == 0) true else nullable(r)
  case BETWEEN(r, n, m) => if (n <= 0 && m >= 0) true else nullable(r)
  case ALL() => false
  case RECD(_, r1) => nullable(r1)
}

def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2)) else SEQ(der(c, r1), r2)
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))
  case NTIMES(r, i) => if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
  case OPT(r) => der(c, r)
  case RANGE(s) => if(s.contains(c)) ONE else ZERO
  case NOT(r) => NOT(der(c, r))
  case PLUS(r1) => SEQ(der(c, r1), STAR(r1))
  case UPTO(r, i) => if (i == 0) ZERO else SEQ(der(c, r), UPTO(r, i - 1))
  case FROM(r, n) => if (n == 0) SEQ(der(c, r), STAR(r)) else SEQ(der(c, r), FROM(r, n - 1))
  case BETWEEN(r, n, m) => if (m == 0) ZERO else SEQ(der(c, r), BETWEEN(r, n - 1, m - 1))
  case ALL() => ONE
  case RECD(_, r1) => der(c, r1)
}

// extracts a string from a value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) ++ flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Pluss(vs) => vs.map(flatten).mkString
  case Ntimess(vs) => vs.map(flatten).mkString
  case Optional(v) => flatten(v)
  case Rec(_, v) => flatten(v)
}

// extracts an environment from a value;
// used for tokenising a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Pluss(vs) => vs.flatMap(env)
  case Ntimess(vs) => vs.flatMap(env)
  case Optional(v) => env(v)
  case Rec(x, v) => (x, flatten(v))::env(v)
}


// The injection and mkeps part of the lexer
//===========================================

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case PLUS(r) => Stars(List(mkeps(r))) 
  case OPT(r) => Stars(Nil)
  case NTIMES(r, n) => Stars(List.fill(n)(mkeps(r)))
  case RECD(x, r) => Rec(x, mkeps(r))
}


def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs) // PLUS

  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))

  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 

  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs) // NTIMES
                      
  case (OPT(r), v) => Stars(inj(r, c, v)::Nil)                           // OPT

  case (RANGE(_), Empty) => Chr(c)                             // RANGE

  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}

def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

// simplification
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex(r_simp, cs)))
  }
}

def lexing(r: Rexp, s: String) = 
  env(lex(r, s.toList))

// The Lexing Rules for the WHILE Language

val KEYWORD : Rexp = "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip"
val OP: Rexp = ":=" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/" | "&&" | "||" | "=="
val LETTER: Rexp = RANGE("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toList)
val SEMI: Rexp = ";"
val SYM: Rexp = LETTER | RANGE("._><=,:\\".toList) | SEMI
val DIGIT: Rexp = RANGE("0123456789".toList)
val WHITESPACE: Rexp = PLUS(" ") | "\n" | "\t"
val STRING: Rexp = "\"" ~ (SYM | DIGIT | WHITESPACE).% ~ "\""
val ID = PLUS(LETTER) ~ ("_" | LETTER | DIGIT).%
val RCURVPAREN: Rexp = "{"
val LCURVPAREN: Rexp = "}"
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val NUM: Rexp = RANGE("123456789".toList) ~ DIGIT.%
val COM: Rexp = "//" ~ (SYM | DIGIT | " ").% ~ "\n"

val WHILE_REGS = (("k" $ KEYWORD) | 
                  // ("l" $ LETTER) |
                  ("s" $ SEMI) | 
                  ("d" $ DIGIT) |
                  ("id" $ ID) |
                  WHITESPACE |              // filter out WHITESPACES
                  // ("w" $ WHITESPACE) |   // with WHITESPACES
                  ("sym" $ SYM) |
                  COM |                      // filter out COM
                  // ("c" $ COM) |           // with COM
                  ("str" $ STRING) |
                  ("curlp" $ (LCURVPAREN | RCURVPAREN)) |
                  ("p" $ (LPAREN | RPAREN)) | 
                  ("n" $ NUM) | 
                  ("o" $ OP)).%  


case class ~[+A, +B](_1: A, _2: B)


// constraint for the input
type IsSeq[A] = A => Seq[_]


abstract class Parser[I : IsSeq, T]{
  def parse(in: I): Set[(T, I)]

  def parse_all(in: I) : Set[T] =
    for ((hd, tl) <- parse(in); 
        if tl.isEmpty) yield hd
}

// parser combinators

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(in: I) = 
    for ((hd1, tl1) <- p.parse(in); 
         (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], 
                              q: => Parser[I, T]) extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)   
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 f: T => S) extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}

// atomic parser for tocken list
case class TokenParser(s: String) extends Parser[List[(String, String)], String] {
  def parse(t: List[(String, String)]) = {
    if (t.isEmpty) {
        Set()
    } else if (t.head._2 == s) {
        Set((t.head._2, t.tail))
     } else {
         Set()
     }
  }
}

// atomic parser for identifiers
case object IdParser extends Parser[List[(String, String)], String] {
  def parse(t: List[(String, String)]) = {
    if (t.isEmpty) {
        Set()
    } else if(t.head._1 == "id"){
          Set((t.head._2, t.tail))
      }  else {
          Set()
      }
  }
}

// atomica parset for strings that are passed in the code that is to be parsed
case object StrParser extends Parser[List[(String, String)], String] {
  def parse(t: List[(String, String)]) = {
    if (t.isEmpty) {
        Set()
    } else if(t.head._1 == "str"){
          Set((t.head._2.slice(1, t.head._2.size - 1), t.tail))
    } else {
          Set()
    }
  }
}

// atomic parser for numbers and digits
case object NumParser extends Parser[List[(String, String)], Int] {
  def parse(t: List[(String, String)]) = {
    if (t.isEmpty) {
        Set()
    } else if(t.head._1 == "n" || t.head._1 == "d") {
        Set((t.head._2.toInt, t.tail))
    } else {
         Set()
    }
  }
}   

implicit def parser_interpolation(sc: StringContext) = new {
    def p(args: Any*) = TokenParser(sc.s(args:_*))
}   

// more convenient syntax for parser combinators
implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}



// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp 

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Read(s: String) extends Stmt
case class WriteVar(s: String) extends Stmt
case class WriteStr(s: String) extends Stmt

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp


// arithmetic expressions
lazy val AExp: Parser[List[(String, String)], AExp] = {
  (Te ~ p"+" ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("+", x, z) } ||
  (Te ~ p"-" ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("-", x, z) } || Te}
lazy val Te: Parser[List[(String, String)], AExp] = {
  (Fa ~ p"*" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("*", x, z) } || 
  (Fa ~ p"/" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("/", x, z) } || 
  (Fa ~ p"%" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("%", x, z) } || Fa }
lazy val Fa: Parser[List[(String, String)], AExp] = {
   (p"(" ~ AExp ~ p")").map{ case _ ~ y ~ _ => y } || 
   IdParser.map(Var) || 
   NumParser.map(Num) }


// boolean expressions with some simple nesting
lazy val BExp: Parser[List[(String, String)], BExp] = {
   (AExp ~ p"==" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("==", x, z) } || 
   (AExp ~ p"!=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("!=", x, z) } || 
   (AExp ~ p"<" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z) } || 
   (AExp ~ p">" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">", x, z) } ||
   (AExp ~ p"<=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<=", x, z) } || 
   (AExp ~ p">=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">=", x, z) } ||
   (p"(" ~ BExp ~ p")" ~ p"&&" ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => And(y, v) } ||
   (p"(" ~ BExp ~ p")" ~ p"||" ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => Or(y, v) } ||
   (p"true".map[BExp]{ _ => True }) || 
   (p"false".map[BExp]{ _ => False }) ||
   (p"(" ~ BExp ~ p")").map[BExp]{ case _ ~ x ~ _ => x } }

// a single statement 
lazy val Stmt: Parser[List[(String, String)], Stmt] = {
  ((p"skip".map[Stmt]{_ => Skip }) ||
   (IdParser ~ p":=" ~ AExp).map[Stmt]{ case x ~ _ ~ z => Assign(x, z) } ||
   (p"write" ~ StrParser).map[Stmt]{ case _ ~ y => WriteStr(y) } ||
   (p"write" ~ IdParser).map[Stmt]{ case _ ~ y => WriteVar(y) } ||
   (p"write" ~ p"(" ~ IdParser ~ p")").map[Stmt]{ case _ ~ _ ~ y ~ _ => WriteVar(y) } ||
   (p"if" ~ BExp ~ p"then" ~ Block ~ p"else" ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w) } ||
   (p"while" ~ BExp ~ p"do" ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ w => While(y, w) }) ||
   (p"read" ~ IdParser).map[Stmt]{ case _ ~ x => Read(x) } }

// statements
lazy val Stmts: Parser[List[(String, String)], Block] = {
  (Stmt ~ p";" ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) }) }

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[(String, String)], Block] = {
  ((p"{" ~ Stmts ~ p"}").map{ case _ ~ y ~ _ => y } || 
   (Stmt.map(s => List(s)))) }


// an interpreter for the WHILE language
type Env = Map[String, Int]

def eval_aexp(a: AExp, env: Env) : Int = a match {
  case Num(i) => i
  case Var(s) => env(s)
  case Aop("+", a1, a2) => eval_aexp(a1, env) + eval_aexp(a2, env)
  case Aop("-", a1, a2) => eval_aexp(a1, env) - eval_aexp(a2, env)
  case Aop("*", a1, a2) => eval_aexp(a1, env) * eval_aexp(a2, env)
  case Aop("/", a1, a2) => eval_aexp(a1, env) / eval_aexp(a2, env)
  case Aop("%", a1, a2) => eval_aexp(a1, env) % eval_aexp(a2, env)
}

def eval_bexp(b: BExp, env: Env) : Boolean = b match {
  case True => true
  case False => false
  case Bop("==", a1, a2) => eval_aexp(a1, env) == eval_aexp(a2, env)
  case Bop("!=", a1, a2) => !(eval_aexp(a1, env) == eval_aexp(a2, env))
  case Bop(">", a1, a2) => eval_aexp(a1, env) > eval_aexp(a2, env)
  case Bop("<", a1, a2) => eval_aexp(a1, env) < eval_aexp(a2, env)
  case Bop(">=", a1, a2) => eval_aexp(a1, env) >= eval_aexp(a2, env)
  case Bop("<=", a1, a2) => eval_aexp(a1, env) <= eval_aexp(a2, env)
  case And(b1, b2) => eval_bexp(b1, env) && eval_bexp(b2, env)
  case Or(b1, b2) => eval_bexp(b1, env) || eval_bexp(b2, env)
}

def eval_stmt(s: Stmt, env: Env) : Env = s match {
  case Skip => env
  case Assign(x, a) => env + (x -> eval_aexp(a, env))
  case If(b, bl1, bl2) => if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env) 
  case While(b, bl) => 
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env))
    else env
  case WriteVar(x) => { println(env(x)) ; env }
  case WriteStr(x) => { println(x) ; env }  
  case Read(x) => env + (x -> eval_aexp(Num(scala.io.StdIn.readInt()), env))
}

def eval_bl(bl: Block, env: Env) : Env = bl match {
  case Nil => env
  case s::bl => eval_bl(bl, eval_stmt(s, env))
}

def eval(bl: Block) : Env = eval_bl(bl, Map())


// Testing Cases
// val e = "x := x + 5"
// val e = "x := 5; x := x + 5"
// val e = "x := 5; y := 6; while x > 0 do skip"
// val e = "x := 5; read n"
// val e = """n := 5; write n """
// val e = """n := 5; write "HelloWorld" """

// println(lexing(WHILE_REGS, e))
// println(Stmts.parse(lexing(WHILE_REGS, e)))
// println(Stmts.parse_all(lexing(WHILE_REGS, e)))
// println(eval(Stmts.parse_all(lexing(WHILE_REGS, e)).head))

// println(Stmts.parse_all(lexing(WHILE_REGS,"if (a < b) then skip else a := a * b + 1")))

// // Fib
// val fib = """
// write "Fib";
// read n;  
// minus1 := 0;
// minus2 := 1;
// while n > 0 do {
//        temp := minus2;
//        minus2 := minus1 + minus2;
//        minus1 := temp;
//        n := n - 1
// };
// write "Result";
// write minus2 
// """

// println(lexing(WHILE_REGS, fib))
// println(Stmts.parse(lexing(WHILE_REGS, fib)))
// println(Stmts.parse_all(lexing(WHILE_REGS, fib)))
// println(eval(Stmts.parse_all(lexing(WHILE_REGS, fib)).head))

// //Three loops
// val threeloops = """
// start := 1000;
// x := start;
// y := start;
// z := start;
// while 0 < x do {
//   while 0 < y do {
//     while 0 < z do { z := z - 1 };
//     z := start;
//     y := y - 1
//   };
//   y := start;
//   x := x - 1
// }
// """

// def time[R](block: => R): R = {
//     val start = System.nanoTime()
//     val result = block    // call-by-name
//     val end = System.nanoTime()
//     println("Elapsed time: " + (end - start) / 1.0e9 + "s")
//     result
// }

// def time_needed[T](i: Int, code: => T) = {
//   val start = System.nanoTime()
//   for (j <- 1 to i) code
//   val end = System.nanoTime()
//   (end - start) / (i * 1.0e9)
// }

// time { eval(Stmts.parse_all(lexing(WHILE_REGS, threeloops)).head) }

// println(lexing(WHILE_REGS, threeloops))
// println(Stmts.parse(lexing(WHILE_REGS, threeloops)))
// println(Stmts.parse_all(lexing(WHILE_REGS, threeloops)))
// println(eval(Stmts.parse_all(lexing(WHILE_REGS, threeloops)).head))

// // Prime Numbert
// val prime = """
// // prints out prime numbers from 2 to 100

// end := 100;
// n := 2;
// while (n < end) do {
//     f := 2;
//     tmp := 0;
//     while ((f < n / 2 + 1) && (tmp == 0)) do {
//         if ((n / f) * f == n) then { tmp := 1 } else { skip };
//         f := f + 1
//     };
// if (tmp == 0) then { write(n) } else { skip };
// n := n + 1
// }"""

// println(lexing(WHILE_REGS, prime))
// println(Stmts.parse(lexing(WHILE_REGS, prime)))
// println(Stmts.parse_all(lexing(WHILE_REGS, prime)))
// println(eval(Stmts.parse_all(lexing(WHILE_REGS, prime)).head))


// // Collatz
// val collatz = """
// // Collatz series

// // needs writing of strings and numbers; comments

// bnd := 1;
// while bnd < 101 do {
//   write bnd;
//   write ": ";
//   n := bnd;
//   cnt := 0;

//   while n > 1 do {
//     write n;
//     write ",";
    
//     if n % 2 == 0 
//     then n := n / 2 
//     else n := 3 * n+1;

//     cnt := cnt + 1
//   };

//   write " => ";
//   write cnt;
//   write "\n";
//   bnd := bnd + 1
// }
// """


// println(lexing(WHILE_REGS, collatz))
// println(Stmts.parse(lexing(WHILE_REGS, collatz)))
// println(Stmts.parse_all(lexing(WHILE_REGS, collatz)))
// println(eval(Stmts.parse_all(lexing(WHILE_REGS, collatz)).head))
