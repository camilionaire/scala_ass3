//-------------------------------------------------------------------------
// Supporting code for CS558 Programming Languages. 
// Dept of Computer Science, Portland State University
// J. Li (8/2022) 
//-------------------------------------------------------------------------

// Testing ScopeLang interpreter
//
import org.scalatest.FunSuite
import SLInterp._

class TestSLI extends FunSuite {
  
  // compare expected and actual console output (could be multi-lines)
  def assertConsoleOutput(p:String, s:String) = {
    val output = new java.io.ByteArrayOutputStream(10240)
    def assertRes = assertResult(p){SLInterp(s);output.flush();output.toString}
    Console.withOut(output)(assertRes)
  }

  test ("Let") {
    assertResult(3){SLInterp("(let x 1 (let y 2 (+ x y)))")}
    // assertResult(1){SLInterp("(let x 1 (let y 2 (seq (:= y x) y)))")}
    assertResult(1){SLInterp("(let x 1 (seq (let x 2 x) x))")}
    assertResult(3){SLInterp("(let x (let x 2 (+ x 1)) x)")}
  }

  // test ("Pair") {
  //   assertResult(1){SLInterp("(let x (pair 1 2) (pair? x))")}
  //   assertResult(1){SLInterp("(let x (pair 1 2) (< (#1 x) (#2 x)))")}
  //   assertResult(2){SLInterp("(let y (let x 1 (pair x (+ x 1))) (#2 y))")}
  //   assertResult(1){SLInterp("(let x (let x 1 (pair x (+ x 1))) (#1 x))")}
  // }

  // test("Set#1/#2") {
  //   assertResult(3){SLInterp("(#1 (set#2 (pair 3 1) 7))")}
  //   assertResult(3){SLInterp("(#2 (set#1 (pair 1 3) 7))")}
  //   assertResult(7){SLInterp("(#1 (set#1 (pair 1 3) 7))")}
  //   assertResult(7){SLInterp("(#2 (set#2 (pair 3 1) 7))")}
  //   assertResult(3){SLInterp("(let a (pair 1 2) (seq (set#2 a 3) (#2 a)))") }
  //   assertResult(3){SLInterp(
  //                     "(let a (pair 0 0) (seq (set#1 a 3) (- (#1 a) (#2 a))))")}
  //   assertResult(-3){SLInterp(
  //                     "(let a (pair 0 0) (seq (set#2 a 3) (- (#1 a) (#2 a))))")}
  // }

  // test("Eq tests") {
  //   assertResult(1){SLInterp("(== (+ 2 4) (* 2 3))")} 
  //   assertResult(0){SLInterp("(== (pair 2 4) (pair 2 4))")} 
  //   assertResult(1){SLInterp("(let x (pair 1 2) (== x (let y 0 x)))")}
  // }

  // test("Deq tests") {
  //   assertResult(0){SLInterp("(deq 5 (pair 1 2))")}
  //   assertResult(1){SLInterp("(deq (+ 2 4) (* 2 3))")} 
  //   assertResult(1){SLInterp("(deq (pair 2 4) (pair 2 4))")} 
  //   assertResult(1){SLInterp("(deq (pair 2 (pair 1 3)) (pair 2 (pair 1 3)))")} 
  //   assertResult(0){SLInterp("(deq (pair 2 (pair 1 3)) (pair 2 3))")} 
  //   assertResult(1){SLInterp("(let x (pair 1 2) (let y (pair 1 2) (deq x y)))")} 
  //   assertResult(0){SLInterp("(let x (pair 1 2) (let y (pair 1 3) (deq x y)))")} 
  // }

  // test("Write") {
  //   assertConsoleOutput("3\n", "(write 3)")
  //   assertConsoleOutput("2\n1\n", "(seq (write 2) (write 1))")
  //   assertConsoleOutput("(1.2)\n", "(seq (write (pair 1 2)) 0)")
  //   assertConsoleOutput("(1.(2.0))\n", "(seq (write (pair 1 (pair 2 0))) 0)")
  // }

  // test ("Exceptions") {
  //   intercept[InterpException]{SLInterp("(#1 1)")}
  //   intercept[InterpException]{SLInterp("(#2 1)")}
  //   intercept[InterpException]{SLInterp("(set#1 1 2)")}
  //   intercept[InterpException]{SLInterp("(set#2 1 2)")}
  //   intercept[InterpException]{SLInterp("(+ x 4)")}
  //   intercept[InterpException]{SLInterp("(+ 3 (pair 1 2))")}
  //   intercept[InterpException]{SLInterp("(< 3 (pair 1 2))")}
  //   intercept[InterpException]{SLInterp("(if (pair 1 2) 1 2)")}
  //   intercept[InterpException]{SLInterp("(while (pair 1 2) 1)")}
  //   intercept[InterpException]{SLInterp("(== 5 (pair 1 2))")}
  //   intercept[InterpException]{SLInterp("(pair 1 2)")}
  // }
	
}
