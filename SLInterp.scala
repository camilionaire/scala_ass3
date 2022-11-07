// ScopeLang Interpreter
//
// Usage: linux> scala SLInterp <source file>
//
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
        // case Lt(l,r)  => // ... need code ...   
        // case Gt(l,r)  => // ... need code ...   
        // case Eq(l,r)  => // ... need code ...   
        // case Deq(l,r) => // ... need code ...   
        // case Assgn(x,e) => 
        //   // lookup x's address from env, evaluate e, and set its value
        //   // to x's storage location; yield e's value as Assgn's value
        //   // (no need to update env...why?)
        //   // ... need code ...
        // case Write(e) => 
        //   // for num, just print the value; for pair, print its two values
        //   // in the form (v1.v2)
        //   // ... need code ...
        case Seq(e1,e2) => {
          val v1 = interpE(env,e1)
          val v2 = interpE(env,e2)
          v2
        }
        // case If(c,t,e)  => // ... need code ...   
        // case While(c,b) => // ... need code ...   
        case Let(x,b,e) =>
          // evaluate b and bind it's value to x, and store it on the
          // stack (use push() to get a stack address and set() to store
          // the value); x's binding needs to be added to env for 
          // evaluating e (only); x's value needs to be removed before
          // returning (use pop())
          val vb:Value = interpE(env, b)
          val addy:Addr = stack.push()
          set(addy, vb)
          val ne = env + (x -> addy)
          val ve = interpE(ne, e)
          // env.remove(x)
          stack.pop()
          ve
        // case Pair(l,r)  => 
        //   // allocate 2 units of space in the heap; store the pairs' two
        //   // values into the space (use set()); return a pair value
        //   // ... add code ...
        // case IsPair(e)  => // ... need code ...   
        // case Fst(e) => // ... need code ...   
        // case Snd(e) => // ... need code ...   
        // case SetFst(p,e) => // ... need code ...   
        // case SetSnd(p,e) => // ... need code ...   
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
