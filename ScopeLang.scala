//-------------------------------------------------------------------------
// Supporting code for CS558 Programming Languages. 
// Dept of Computer Science, Portland State University
// J. Li (8/22) 
//-------------------------------------------------------------------------

// ScopeLang - An extended imperative language 
//             (with scopes and boxed data)
//
// Grammar:
//   Expr -> <num>                     // int const               
//        |  <id>                      // var                     
//        |  (Op Expr Expr)            // binop                   
//        |  (:= <id> Expr)            // ref assign                  
//        |  (write Expr)              // output                  
//        |  (seq Expr Expr)           // sequence
//        |  (if Expr Expr Expr)       // if                      
//        |  (while Expr Expr)         // while loop              
//        |  (let <id> Expr Expr)      // local scope         
//        |  (pair Expr Expr)          // pair constructor    
//        |  (pair? Expr)              // pair query          
//        |  (#1 Expr)                 // 1st elm of pair     
//        |  (#2 Expr)                 // 2nd elm of pair     
//        |  (set#1 Expr Expr)         // set 1st elm of pair  
//        |  (set#2 Expr Expr)         // set 2nd elm of pair  
//    Op  -> + | - | * | / | %         // arith op                
//        |  < | > | ==                // relational op (== is ref comp)
//        |  deq                       // deep comparison
//   <num>: integer  // "wholeNumber"                  
//   <id> : string   // "ident"
//
import scala.util.parsing.combinator._

object ScopeLang {
  sealed abstract class Expr
  case class Num(i:Int) extends Expr
  case class Var(id:String) extends Expr
  case class Add(l:Expr,r:Expr) extends Expr
  case class Sub(l:Expr,r:Expr) extends Expr
  case class Mul(l:Expr,r:Expr) extends Expr
  case class Div(l:Expr,r:Expr) extends Expr
  case class Rem(l:Expr,r:Expr) extends Expr
  case class Lt(l:Expr,r:Expr) extends Expr
  case class Gt(l:Expr,r:Expr) extends Expr
  case class Eq(l:Expr,r:Expr) extends Expr
  case class Deq(l:Expr,r:Expr) extends Expr
  case class Assgn(id:String,e:Expr) extends Expr
  case class Write(e:Expr) extends Expr
  case class Seq(e1:Expr,e2:Expr) extends Expr
  case class If(c:Expr,t:Expr,e:Expr) extends Expr
  case class While(c:Expr,e:Expr) extends Expr
  case class Let(id:String,e:Expr,b:Expr) extends Expr
  case class Pair(l:Expr,r:Expr) extends Expr
  case class IsPair(e:Expr) extends Expr
  case class Fst(e:Expr) extends Expr
  case class Snd(e:Expr) extends Expr
  case class SetFst(p:Expr,e:Expr) extends Expr
  case class SetSnd(p:Expr,e:Expr) extends Expr

  case class ParseException(string: String) extends RuntimeException

  object SLParse extends JavaTokenParsers {
    // input program is in s-expression form
    def expr: Parser[Expr] = atm | lst
    def atm: Parser[Expr] = 
          wholeNumber ^^ {s => Num(s.toInt)} |
          ident       ^^ {s => Var(s)}
    def lst: Parser[Expr] = 
          "(+" ~> expr~expr <~ ")"       ^^ {case l~r => Add(l,r)}     |
          "(-" ~> expr~expr <~ ")"       ^^ {case l~r => Sub(l,r)}     |
          "(*" ~> expr~expr <~ ")"       ^^ {case l~r => Mul(l,r)}     |
          "(/" ~> expr~expr <~ ")"       ^^ {case l~r => Div(l,r)}     |
          "(%" ~> expr~expr <~ ")"       ^^ {case l~r => Rem(l,r)}     |
          "(<" ~> expr~expr <~ ")"       ^^ {case l~r => Lt(l,r)}      |
          "(>" ~> expr~expr <~ ")"       ^^ {case l~r => Gt(l,r)}      |
          "(==" ~> expr~expr <~ ")"      ^^ {case l~r => Eq(l,r)}      |    
          "(deq" ~> expr~expr <~ ")"     ^^ {case l~r => Deq(l,r)}     |    
          "(:=" ~> ident~expr <~ ")"     ^^ {case x~e => Assgn(x,e)}   |
          "(write" ~> expr <~ ")"        ^^ {e => Write(e)}            |
          "(seq" ~> expr~expr <~ ")"     ^^ {case a~b => Seq(a,b)}     |
          "(if" ~> expr~expr~expr <~ ")" ^^ {case c~l~r => If(c,l,r)} |
          "(while" ~> expr~expr <~ ")"   ^^ {case c~e => While(c,e)}   | 
          "(let" ~> ident~expr~expr <~ ")" ^^ {case x~b~e => Let(x,b,e)} |
          "(pair" ~> expr~expr <~ ")"    ^^ {case l~r => Pair(l,r)}    |
          "(pair?" ~> expr <~ ")"        ^^ {e => IsPair(e)}           | 
          "(#1" ~> expr <~ ")"           ^^ {e => Fst(e)}              | 
          "(#2" ~> expr <~ ")"           ^^ {e => Snd(e)}              | 
          "(set#1" ~> expr~expr <~ ")"   ^^ {case p~e => SetFst(p,e)}  | 
          "(set#2" ~> expr~expr <~ ")"   ^^ {case p~e => SetSnd(p,e)}

    def apply(text: String): Expr = {
      val result = parseAll(expr, text)
      result match {
        case Success(r, _) => r
        case Failure(msg, n) =>
          throw ParseException(msg +
            " (input left: \"" + n.source.toString.drop(n.offset) + "\")")
        case Error(msg, n) =>
          throw ParseException(msg +
            " (input left: \"" + n.source.toString.drop(n.offset) + "\")")
      }
    }
  }

  // Test driver
  import scala.io._
  def main(argv: Array[String]) = {
    try {
      val s = if (argv(0) == "-") StdIn.readLine()
              else Source.fromFile(argv(0)).getLines.mkString("\n")
      val p = SLParse(s)
      println(s)
      println(p)
    } catch {
      case ex: ParseException => { println("Parser Error:" + ex.string) }
    }
  }
}
//
