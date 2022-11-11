// ScopeLang Interpreter
//
// Usage: linux> scala SLInterp <source file>
//
// Name: Camilo Schaser-Hughes
// CS 558 Prog Langs, Prof. Jingke Li
// November 11, 2022
import ScopeLang._

object SLInterp {
  case class InterpException(string: String) extends RuntimeException

  // Value represenation
  sealed abstract class Value
  case class NumV(n:Int) extends Value
  case class PairV(a:Addr) extends Value 

  // Storage represenation
  type Index = Int
  sealed abstract class Store {
    case class UndefinedContents(string: String) extends RuntimeException
    private val contents = collection.mutable.Map[Index,Value]()
    def get(i:Index) = contents.getOrElse(i, throw UndefinedContents("" + i))
    def set(i:Index,v:Value) = contents += (i->v)
    override def toString: String = contents.toString
  }
  // Heap
  class HeapStore extends Store {
    private var nextFreeIndex:Index = 0
    def allocate(n:Int): Addr = {
      val i = nextFreeIndex
      nextFreeIndex += n
      HeapAddr(i)
    }
    // there is no mechanism for deallocation
    override def toString: String = "[next=" + nextFreeIndex + "] " + super.toString
  }
  // Stack
  class StackStore extends Store {
    private var stackPointer:Index = 0;
    def push(): Addr = {
      val i = stackPointer
      stackPointer += 1
      StackAddr(i)
    }
    def pop() = {
      if (stackPointer > 0)
        stackPointer -= 1
      else
        throw InterpException("stack storage is empty")
    }
    def isEmpty(): Boolean = stackPointer == 0
    override def toString: String = "[sp=" + stackPointer + "] " + super.toString
  }

  // Address to storage
  sealed abstract class Addr() {
    def +(offset:Int): Addr
  }
  case class HeapAddr(index:Int) extends Addr {
    def +(offset:Int) = HeapAddr(index+offset)
  }
  case class StackAddr(index:Int) extends Addr {
    def +(offset:Int) = StackAddr(index+offset)
  }

  type Env = Map[String,Addr]

  // Main interpreter function, returns program's value (must be an int)
  def interp(e:Expr, debug:Int = 0): Int = {
    val heap = new HeapStore()
    val stack = new StackStore()
    var env: Env = Map[String,Addr]() // initial env (empty)

    // utility fuctions
    def get(a:Addr) = a match {
      case HeapAddr(i) => heap.get(i)
      case StackAddr(i) => stack.get(i)
    }

    def set(a:Addr,v:Value) = a match {
      case HeapAddr(i) => heap.set(i,v)
      case StackAddr(i) => stack.set(i,v)
    }

    def getAddr(env:Env, x:String): Addr =
      env.getOrElse(x, throw InterpException("undefined variable:" + x))

    def interpBop(env:Env, l: Expr, r:Expr, op:(Int,Int)=>Int) = {
      val lv = interpE(env,l)
      val rv = interpE(env,r)
      (lv,rv) match {
        case (NumV(ln),NumV(rn)) => NumV(op(ln,rn))
        case _ => throw InterpException("non-numeric argument to numeric operator")
      }   
    }

    // interprete an expr in a given env
    def interpE(env:Env, e:Expr): Value = {
      if (debug > 1) {
        println("expr = "+ e)
        println("env = " + env)
        println("stack = " + stack)
        println("heap = " + heap)
      } 
      e match {
        case Num(n) => NumV(n)
        case Var(x) => {
          val a = getAddr(env,x)
          get(a)
        }
        case Add(l,r) => interpBop(env,l,r,(lv,rv)=>lv+rv)
        case Sub(l,r) => interpBop(env,l,r,(lv,rv)=>lv-rv)  
        case Mul(l,r) => interpBop(env,l,r,(lv,rv)=>lv*rv)  
        case Div(l,r) => interpBop(env,l,r,(lv,rv)=> 
               if (rv!=0) lv/rv else throw InterpException("divide by zero"))
        case Rem(l,r) => interpBop(env,l,r,(lv,rv)=> 
               if (rv!=0) lv%rv else throw InterpException("divide by zero"))
        // throws error if not num, returns 1 if true, 0 false.
        case Lt(l,r)  => interpBop(env,l,r,(lv,rv)=> if (lv<rv) 1 else 0)
        case Gt(l,r)  => interpBop(env,l,r,(lv,rv)=> if (lv>rv) 1 else 0)
        // interps both left and right, then runs them through a match statement
        case Eq(l,r)  => {
          val lv = interpE(env,l)
          val rv = interpE(env,r)
          (lv,rv) match {
            case (NumV(ln),NumV(rn)) => if (ln==rn) NumV(1) else NumV(0)
            case (PairV(la),PairV(ra)) => if (la==ra) NumV(1) else NumV(0)
            case _ => throw InterpException("can't compare pairs and nums")
          }
        }
        case Deq(l,r) => {
          // recursion function that checks for equality on nums
          // or recurses left and right for pairs, or zero for non matching
          def unwrap_compare(v1:Value, v2:Value):Value = (v1,v2) match {
            case (NumV(n1),NumV(n2)) => if (n1==n2) NumV(1) else NumV(0)
            case (PairV(a1),PairV(a2)) => {
              if (unwrap_compare(get(a1),get(a2)) == NumV(1) && 
                unwrap_compare(get(a1+1),get(a2+1)) == NumV(1)) NumV(1)
                else NumV(0)
            }
            case _ => NumV(0)
          }
          // evaluates left and right then compares
          val lv = interpE(env,l)
          val rv = interpE(env,r)
          (lv,rv) match {
            case (NumV(ln),NumV(rn)) => unwrap_compare(lv,rv)
            case (PairV(lp),PairV(rp)) => unwrap_compare(lv, rv)
            case _ => NumV(0)
          }
        }
        case Assgn(x,e) => 
          // lookup x's address from env, evaluate e, and set its value
          // to x's storage location; yield e's value as Assgn's value
          // (no need to update env...why?)
          // gets address of x from env, interps e and sets the address
          // since x already points to addy, no need to update env.
          val addy:Addr = getAddr(env, x)
          val ve = interpE(env, e)
          set(addy, ve)
          ve
        case Write(e) => 
          // for num, just print the value; for pair, print its two values
          // in the form (v1.v2)
          // recursion function for printing pairs and nums
          def unwrap_string(v:Value):String = v match {
            case NumV(n) => n.toString
            case PairV(a) => "(" + unwrap_string(get(a)) + "." +
              unwrap_string(get(a+1)) + ")"
          }
          // interps and then prints out recursively
          val ve = interpE(env, e)
          ve match {
            case NumV(n) => print(n + "\n")
            case PairV(a) => {
              print("(" + unwrap_string(get(a)) + "." + 
                unwrap_string(get(a+1)) + ")\n")
            }
            case _ => print("whoops\n")
          }
          ve
        case Seq(e1,e2) => { // was alrady here
          val v1 = interpE(env,e1)
          val v2 = interpE(env,e2)
          v2
        }
        case If(c,t,e)  => {
          val vc = interpE(env, c)
          // if statement becomes a match with exception for pairv's
          vc match {
            case NumV(n) => if (n == 0) interpE(env, e) else interpE(env, t)
            case _ => throw InterpException("value tested needs to be an int")
          }
        }
        case While(c,b) => {
          // interps c and then matches to either recursive call, 0 or err
          val vc = interpE(env, c)
          vc match {
            case NumV(0) => NumV(0)
            case NumV(a) => {
              interpE(env, b)
              interpE(env, While(c,b))
            }
            case _ => throw InterpException("value tested needs to be an int")
          }
        }
        case Let(x,b,e) =>
          // evaluate b and bind it's value to x, and store it on the
          // stack (use push() to get a stack address and set() to store
          // the value); x's binding needs to be added to env for 
          // evaluating e (only); x's value needs to be removed before
          // returning (use pop())
          // interps and pushes to addy, adds to new env for interpreting e
          // pops and returns
          val vb:Value = interpE(env, b)
          val addy:Addr = stack.push()
          set(addy, vb)
          val ne = env + (x -> addy)
          val ve = interpE(ne, e)
          stack.pop()
          ve
        case Pair(l,r)  => 
          // allocate 2 units of space in the heap; store the pairs' two
          // values into the space (use set()); return a pair value
          val lv:Value = interpE(env,l)
          val rv:Value = interpE(env,r)
          val addy:Addr = heap.allocate(2)
          set(addy, lv)
          set(addy + 1, rv)
          PairV(addy)
        case IsPair(e)  => {
          interpE(env, e) match {
            case PairV(i) => NumV(1)
            case _ => NumV(0)
          }
        }
        // gets from a first slot in pair or throws error
        case Fst(e) => {
          interpE(env, e) match {
            case PairV(a) => get(a)
            case _ => throw InterpException("gots to be a pair to get a component")
          }
        }
        case Snd(e) => 
          interpE(env, e) match {
            case PairV(a) => get(a+1)
            case _ => throw InterpException("gots to be a pair to get a component")
          }
          // sets first slot or throws error
        case SetFst(p,e) => {
          val pva = interpE(env, p) match {
            case PairV(a) => a
            case _ => throw InterpException("gots to be a pair to set a component")
          }
          val ve = interpE(env, e)
          set(pva, ve)
          PairV(pva)
        }
        case SetSnd(p,e) => {
          val pva = interpE(env, p) match {
            case PairV(a) => a
            case _ => throw InterpException("gots to be a pair to set a component")
          }
          val ve = interpE(env, e)
          set(pva + 1, ve)
          PairV(pva)
        }
      }
    }

    // process the main body expression
    val v = interpE(env,e)
    if (debug > 0) println("Evaluates to: " + v)
    if (!stack.isEmpty)
      throw InterpException("stack not empty at the end of program exection")
    v match {
      case NumV(n) => n
      case _ => throw InterpException("top-level expr returns non-integer")
    }
  } 
  
  def apply(s:String, debug:Int = 0): Int = {
    if (debug > 0) println("Input:  " + s)
    val e = SLParse(s)
    if (debug > 0) println("AST:    " + e)
    interp(e,debug)
  }

  // Test driver
  import scala.io.Source
  def main(argv: Array[String]) = {
    try {
      val s = Source.fromFile(argv(0)).getLines.mkString("\n")
      val d = if (argv.length > 1) argv(1).toInt else 0
      val v = apply(s,d)
      println(v)
    } catch {
      case ex: ParseException =>  println("Parser Error: " + ex.string)
      case ex: InterpException => println("Interp Error: " + ex.string)
    }
  }
}
//
