/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
/**
 * Test Kaisar parsing
 * @author Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.RandomParserTests
import edu.cmu.cs.ls.keymaerax.tags._
import fastparse.Parsed.{Failure, Success}
import fastparse._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

object AutogeneratedFormulaTests {
  def doParse[T](s: String): Formula = parse(s, ExpressionParser.formula(_)).asInstanceOf[Success[Formula]].value
}
@SlowTest
class AutogeneratedFormulaTests extends RandomParserTests(AutogeneratedFormulaTests.doParse, new RandomFormula(0))

@UsualTest
class KaisarProgramParserTests extends TacticTestBase {
  import KaisarProof._
  val pc = ParserCommon
  val ep = ExpressionParser
  val pp = ProofParser
  val kp = KaisarKeywordParser

  class KPPTestException(msg: String) extends Exception (msg)

  def p[T](s: String, parser: P[_] => P[T]): T =
    parse(s, parser) match {
      case x: Success[T] => x.value
      case x: Failure => throw new KPPTestException(x.trace().toString)
    }

  val (vx, vy, vt, vv, vT, va) = (Variable("x"), Variable("y"), Variable("t"), Variable("v"), Variable("T"), Variable("a"))
  val (dx, dy, dt, dv) = (DifferentialSymbol(vx), DifferentialSymbol(vy), DifferentialSymbol(vt), DifferentialSymbol(vv))

  // terms
  "term parser" should "parse variable" in {
    p("x", ep.term(_)) shouldBe vx
  }

  it should "parse diff variable" in {
    p("x'", ep.term(_)) shouldBe dx
  }

  it should "parse diffterm" in {
    p("(x + y)'", ep.term(_)) shouldBe Differential(Plus(vx, vy))
  }

  it should "parse number" in {
    val num: Number = p("123.0", ep.term(_)).asInstanceOf[Number]
    num.value shouldBe 123.0
  }

  it should "parse plus" in {
    p("x + y", ep.term(_)) shouldBe Plus(vx, vy)
  }

  it should "parse times" in {
    p("x * y", ep.term(_)) shouldBe Times(vx, vy)
  }

  it should "parse minus" in {
    p("x - y", ep.term(_)) shouldBe Minus(vx, vy)
  }

  it should "parse neg" in {
    p("- y", ep.term(_)) shouldBe Neg(vy)
  }

  it should "parse divide" in {
    p("x / y", ep.term(_)) shouldBe Divide(vx, vy)
  }

  it should "parse special functions" in {
    p("abs(x)", ep.term(_)) shouldBe FuncOf(abs, vx)
    p("max(x, y + x)", ep.term(_)) shouldBe FuncOf(max, Pair(vx, Plus(vy, vx)))
    p("min(x, y + x)", ep.term(_)) shouldBe FuncOf(min, Pair(vx, Plus(vy, vx)))
  }

  it should "parse wildcard" in {
    p("*", ep.term(_)) shouldBe wild
  }

  it should "parse at" in {
    p("x@init", ep.term(_)) shouldBe FuncOf(at, Pair(vx, init))
    p("x@init(y)", ep.term(_)) shouldBe makeAt(Variable("x"), LabelRef("init", List(Variable("y"))))
    p("x@init(y, z)", ep.term(_)) shouldBe makeAt(Variable("x"), LabelRef("init", List(Variable("y"),Variable("z"))))
  }

  it should "parse parens" in {
    p("(x)", ep.term(_)) shouldBe vx
  }

  it should "parse power" in {
    p("x^y", ep.term(_)) shouldBe Power(vx, vy)
  }

  it should "parse compound term" in {
    p("(x + -y ^y) * x/x", ep.term(_)) shouldBe Divide(Times(Plus(vx, Neg(Power(vy,vy))), vx), vx)
  }

  it should "respect order of operations" in {
    p("(x - y)*x/y-x+y+-x^x", ep.term(_)) shouldBe Plus(Plus(Minus(Divide(Times(Minus(vx, vy), vx), vy), vx), vy), Neg(Power(vx, vx)))
  }

  // programs
  "program parser" should "parse assignment" in {
    p("x := x + x;", ep.program(_)) shouldBe Assign(vx, Plus(vx, vx))
  }

  it should "parse differential assignment" in {
    p("x' := x + x;", ep.program(_)) shouldBe Assign(dx, Plus(vx, vx))
  }

  it should "parse random assignment" in {
    p("x' := *;", ep.program(_)) shouldBe AssignAny(dx)
  }

  it should "parse singleton ode" in {
    p("x' = 5;", ep.program(_)) shouldBe ODESystem(AtomicODE(dx, Number(5)))
  }

  it should "parse ode product" in {
    p("x' = 5, y' = 2;", ep.program(_)) shouldBe ODESystem(DifferentialProduct(AtomicODE(dx, Number(5)), AtomicODE(dy, Number(2))))
  }

  it should "parse ode with constraint" in {
    p("x' = 5, y' = 2 & x = y;", ep.program(_)) shouldBe ODESystem(DifferentialProduct(AtomicODE(dx, Number(5)), AtomicODE(dy, Number(2))), Equal(vx, vy))
  }

  it should "parse ode with constraint with conjunction" in {
    p("x' = 5, y' = 2 & x = y & y = x;", ep.program(_)) shouldBe ODESystem(DifferentialProduct(AtomicODE(dx, Number(5)), AtomicODE(dy, Number(2))),
      And(Equal(vx, vy), Equal(vy, vx)))
  }

  it should "parse example from 1d car" in {
    p("{x' = v, v' = a, t' = 1 & (t <= T & v>=0)};", ep.program(_)) shouldBe ODESystem(DifferentialProduct(AtomicODE(dx, vv), DifferentialProduct(AtomicODE(dv, va), AtomicODE(dt, Number(1)))),
      And(LessEqual(vt, vT), GreaterEqual(vv, Number(0))))
  }

  it should "parse dual" in {
    p("x' =5;^d", ep.program(_)) shouldBe Dual(ODESystem(AtomicODE(dx, Number(5))))
  }

  it should "parse loop" in {
    p("x := 5;*", ep.program(_)) shouldBe Loop(Assign(vx, Number(5)))
  }

  it should "parse compose" in {
    p("x := 5; x:= 2;", ep.program(_)) shouldBe Compose(Assign(vx, Number(5)), Assign(vx, Number(2)))
  }

  it should "parse braces" in {
    val l = Compose(Assign(vx, Number(1)), Assign(vy, Number(2)))
    val r = Compose(Compose(Assign(vy, Number(5)), AssignAny(vx)), Compose(Assign(vy, Number(5)), Assign(vy, Number(4))))
    p("{x:=1; y:=2;} ++ {y:=5; x:= *;} y:=5; y:=4;", ep.program(_)) shouldBe Choice(l, r)
  }

  it should "parse choice" in {
    p("x:=*; ++ ?x=x;", ep.program(_)) shouldBe Choice(AssignAny(vx), Test(Equal(vx, vx)))
  }

  it should "associate choice" in {
    p("x:=1; ++ x:=2; ++ x:=3;", ep.program(_)) shouldBe Choice(Assign(vx, Number(1)), Choice(Assign(vx, Number(2)), Assign(vx, Number(3))))
  }

  // formulas
  "formula parser" should "parse equal" in {
    p("x=y", ep.formula(_)) shouldBe Equal(vx, vy)
  }

  it should "respect | and & precedence" in {
    p("x=0&y=0 | x=1&y=1", ep.formula(_)) shouldBe Or(And(Equal(vx, Number(0)), Equal(vy, Number(0))), And(Equal(vx, Number(1)),Equal(vy, Number(1))))
  }

  it should "respect [] precedence" in {
    p("x=0 & [x:=1;]x=1 & x=2", ep.formula(_)) shouldBe And(Equal(vx, Number(0)), And(Box(Assign(vx, Number(1)), Equal(vx, Number(1))), Equal(vx, Number(2))))
  }

  it should "respect forall precedence" in {
    p("x=0 & \\forall x x=x & x = 1", ep.formula(_)) shouldBe(And(Equal(vx, Number(0)), And(Forall(List(vx), Equal(vx, vx)), Equal(vx, Number(1)))))
  }

  it should "make imply tighter than equiv" in {
    p("x=0 -> x=1 <-> x=2 -> x=5", ep.formula(_)) shouldBe Equiv(Imply(Equal(vx,Number(0)), Equal(vx, Number(1))), Imply(Equal(vx, Number(2)), Equal(vx, Number(5))))
  }

  it should "parse paren terms" in {
    p("(2) <= (1)", ep.formula(_)) shouldBe LessEqual(Number(2), Number(1))
  }

  it should "parse diffvar 1" in {
    p("20-(1^2/z1-((1)'-z2'))<=1&true", ep.formula(_)) shouldBe
      And(LessEqual(Minus(Number(20), Minus(Divide(Power(Number(1), Number(2)), Variable("z1")), Minus(Differential(Number(1)), DifferentialSymbol(Variable("z2"))))), Number(1)), True)
  }

  it should "parse diffvar 2.1" in {
    p("([z1:=z1;](\\forall z2 (z1')<=(z2')))", ep.prefixTerminal(_)) shouldBe
      Box(Assign(Variable("z1"), Variable("z1")), Forall(List(Variable("z2")), LessEqual(DifferentialSymbol(Variable("z1")), DifferentialSymbol(Variable("z2")))))
  }

  it should "parse diffvar 2" in {
    p("\\forall z1 ([z1:=z1;](\\forall z2 (z1')<=(z2')))", ep.formula(_)) shouldBe
      Forall(List(Variable("z1")), Box(Assign(Variable("z1"), Variable("z1")), Forall(List(Variable("z2")), LessEqual(DifferentialSymbol(Variable("z1")), DifferentialSymbol(Variable("z2"))))))
  }

  it should "parse negative literals" in {
    p("-87!=z3*(z1*z1)", ep.formula(_)) shouldBe NotEqual(Number(-87), Times(Variable("z3"), Times(Variable("z1"), Variable("z1"))))
  }

  it should "parse >=" in {
    p("z1>=(-55)'", ep.infixTerminal(_)) shouldBe GreaterEqual(Variable("z1"), Differential(Number(-55)))
  }

  it should "precede * and /" in {
    p("1/2*3", ep.term(_)) shouldBe Times(Divide(Number(1), Number(2)), Number(3))
  }

  it should "parse random example" in {
    val x1 = p("(true)&((z3) <= ((((-23))*((1)))-((-41))))", ep.formula(_))
    val x2 = p("1>=27/(1-1)*(1*1*z2)&z3'>=z2'+z1'|z2<=z3'", ep.formula(_))
    val x3 = p("true&z3<=-23*1--41", ep.formula(_))
    val x4 = p("[{{?([{?(true);}*](<?(true);>(true)));}++{{z3':=((1))*((1));}++{?(true);}}}++{?((true)->((((1)) >= ((1)))&(<?(true);>(true))));}](<?(((z2)^((2))) = (z2));>(!([{{?(true);}*};{{?(true);}++{?(true);}}]([{?(true);}*](<?(true);>(true))))))", ep.formula(_))
  }

  it should "parse existses" in {
    val x = p("\\forall z2 (\\forall z3 1 < z3*40)'", ep.formula(_))
    println(x)
  }

  // Kaisar proof script language parsers
  // identifier pattern parser
  "id pattern parser" should "parse terminals" in {
    p("", pp.exPat(_)) shouldBe Nothing
    p("x", pp.idPat(_)) shouldBe VarPat("x".asVariable)
    p("*", pp.idPat(_)) shouldBe WildPat()
  }

  it should "parse tuples" in {
    p("(x,y)", pp.idPat(_)) shouldBe TuplePat(List(VarPat("x".asVariable), VarPat("y".asVariable)))
    p("(x,y,z)", pp.idPat(_)) shouldBe TuplePat(List(VarPat("x".asVariable), VarPat("y".asVariable), VarPat("z".asVariable)))
  }

  it should "not parse noPat in tuple" in {
    a[KPPTestException] shouldBe thrownBy(p("(x,)", pp.idPat(_)))
  }

  // forward proof-term parser
  "forward proof-term parser" should "parse proof variables" in {
    p("x", kp.proofTerm(_)) shouldBe ProofVar("x".asVariable)
  }

  it should "parse proof application" in {
    p("X(Y)", kp.proofTerm(_)) shouldBe ProofApp(ProofVar("X".asVariable), ProofVar("Y".asVariable))
  }

  it should "parse proof instantiation" in {
    p("X(\"1\")", kp.proofTerm(_)) shouldBe ProofApp(ProofVar("X".asVariable), ProofInstance(Number(1)))
  }

  // selector parser
  "selector parser" should "parse forward selector" in {
    p("and(X, Y)", kp.proofTerm(_)) shouldBe ProofApp(ProofApp(ProofVar("and".asVariable), ProofVar("X".asVariable)), ProofVar("Y".asVariable))
  }

  it should "parse pattern selector" in {
    p("*", kp.selector(_)) shouldBe PatternSelector(wild)
  }

  // method parser
  "method parser" should "parse terminal methods" in {
    p("by RCF", pp.method(_)) shouldBe Using(List(DefaultSelector), RCF())
    p("by auto", pp.method(_)) shouldBe Using(List(DefaultSelector), Auto())
    p("by prop", pp.method(_)) shouldBe Using(List(DefaultSelector), Prop())
  }

  it should "parse using" in {
    p("using x by auto", pp.method(_)) shouldBe Using(List(ForwardSelector(ProofVar("x".asVariable))), Auto())
  }

  it should "parse by-proof" in {
    p("true", pc.variableTrueFalse(_)) shouldBe True
    p("!(true) by auto;", pp.proof(_)) shouldBe List[Statement](Assert(Nothing, True, Using(List(DefaultSelector), (Auto()))))
    p("proof !(true) by auto; end", pp.method(_)) shouldBe Using(List(DefaultSelector), ByProof(List[Statement](Assert(Nothing, True, Using(List(DefaultSelector), Auto())))))
  }

  // proof-statement parser
  "proof statement parser" should "parse assumption" in {
    p("?x:(true);", pp.statement(_)) shouldBe Assume(Variable("x"), True)
  }

  it should "parse assertion" in {
    p("!x:(true) by auto;", pp.statement(_)) shouldBe Assert(Variable("x"), True, Using(List(DefaultSelector), Auto()))
  }

  it should "parse assignments" in {
    p("x := 2;", ep.expression(_)) shouldBe Assign(Variable("x"), Number(2))
    p("x := 2;", pp.statement(_)) shouldBe Modify(VarPat("x".asVariable), Left(Number(2)))
    p("?p:(x := 2;);", pp.statement(_)) shouldBe Modify(VarPat("x".asVariable, Some(Variable("p"))), Left(Number(2)))
    p("x := *;", pp.statement(_)) shouldBe Modify(VarPat("x".asVariable), Right(()))
    p("?p:(x := *);", pp.statement(_)) shouldBe Modify(VarPat("x".asVariable, Some(Variable("p"))), Right(()))
  }

  it should "parse label" in {
    p("init:", pp.statement(_)) shouldBe Label(LabelDef("init"))
    p("init(x):", pp.statement(_)) shouldBe Label(LabelDef("init", List(Variable("x"))))
    p("init(x,y):", pp.statement(_)) shouldBe Label(LabelDef("init", List(Variable("x"), Variable("y"))))
  }

  it should "parse note" in {
    p("note conj = andI(X, Y);", pp.statement(_)) shouldBe Note("conj".asVariable, ProofApp(ProofApp(ProofVar("andI".asVariable), ProofVar("X".asVariable)), ProofVar("Y".asVariable)))
  }

  it should "parse letfun" in {
    p("let square(x) = x*x;", pp.statement(_)) shouldBe LetFun("square".asVariable,  List("x".asVariable), Times(Variable("x"), Variable("x")))
    p("let prod(x,z) = x*z;", pp.statement(_)) shouldBe LetFun("prod".asVariable,  List("x".asVariable, "z".asVariable), Times(Variable("x"), Variable("z")))
  }

  it should "parse match" in {
    p("let (x * y) = z;", pp.statement(_)) shouldBe Match(Times(Variable("x"), Variable("y")), Variable("z"))
  }

  it should "parse block" in {
    p("{?(true); ?(true);}", pp.statement(_)) shouldBe Block(List(Assume(Nothing, True), Assume(Nothing, True)))
  }

  // @TODO: Switch should allow arguments
  it should "parse switch " in {
    p("switch { case xOne:(x <= 1) => !x: (true) by auto; case xPos:(x >= 0) => !x: (true) by auto;}", pp.statement(_)) shouldBe
      Switch(None, List(
        (Variable("xOne"), LessEqual(Variable("x"), Number(1)), Assert(Variable("x"), True, Using(List(DefaultSelector), Auto()))),
        (Variable("xPos"), GreaterEqual(Variable("x"), Number(0)), Assert(Variable("x"), True, Using(List(DefaultSelector), Auto())))))
  }

  it should "parse box-choice" in {
    p("x := 2; ?x:(1 > 0); ++ x := 3; ?x:(x > 0);", pp.statement(_)) shouldBe BoxChoice(
      block(List(Modify(VarPat("x".asVariable),Left(Number(2))), Assume(Variable("x"), Greater(Number(1), Number(0))))),
      block(List(Modify(VarPat("x".asVariable),Left(Number(3))), Assume(Variable("x"), Greater(Variable("x"), Number(0))))))
  }

  it should "parse while" in {
    p("while (x > 0) { x := x - 1; y := y + 2;}", pp.statement(_)) shouldBe While(Nothing, Greater(Variable("x"), Number(0)),
      block(List(Modify(VarPat("x".asVariable), Left(Minus(Variable("x"), Number(1))))
      , Modify(VarPat("y".asVariable), Left(Plus(Variable("y"), Number(2)))))))
  }

  it should "parse boxloop" in {
    p("{?xPos:(x >= 0); x := x - 1;}*", pp.statement(_)) shouldBe
      BoxLoop(Block(List(Assume(Variable("xPos"), GreaterEqual(Variable("x"), Number(0))), Modify(VarPat("x".asVariable), Left(Minus(Variable("x"), Number(1)))))),
        Some((Variable("x"), Equal(Variable("x"), Minus(Variable("x"), Number(1))))))
  }

  it should "parse ghost" in {
    p("/++ x:= 2; ++/", pp.statement(_)) shouldBe Ghost(Modify(VarPat("x".asVariable), Left(Number(2))))
  }

  it should "parse inverseghost" in {
    p("/-- x:= 2; --/", pp.statement(_)) shouldBe InverseGhost(Modify(VarPat("x".asVariable), Left(Number(2))))
  }

  it should "parse print-goal" in {
    p("print \"hello\";", pp.statement(_)) shouldBe PrintGoal("hello")
  }

  // ODE proofs
  it should "parse simple atomic ode proof" in {
    p("?true;", pp.domainStatement(_)) shouldBe DomAssume(Nothing, True)
  }

  it should "parse simple system proof" in {
    p("x' = y, y' = x;", pp.statement(_)) shouldBe ProveODE(DiffProductStatement(
        AtomicODEStatement(AtomicODE(DifferentialSymbol(BaseVariable("x")), Variable("y"))),
        AtomicODEStatement(AtomicODE(DifferentialSymbol(BaseVariable("y")), Variable("x"))))
      , DomAssume(Nothing, True))
  }

  it should "parse simple system with solution annotations" in {
    p("{xSol: x' = y, ySol: y' = x};", pp.statement(_)) shouldBe ProveODE(DiffProductStatement(
      AtomicODEStatement(AtomicODE(DifferentialSymbol(BaseVariable("x")), Variable("y")), Some(Variable("xSol"))),
      AtomicODEStatement(AtomicODE(DifferentialSymbol(BaseVariable("y")), Variable("x")), Some(Variable("ySol"))))
      , DomAssume(Nothing, True))
  }

  it should "parse diffghost" in {
    p("/++ x' = y ++/;", pp.diffStatement(_)) shouldBe DiffGhostStatement(AtomicODEStatement(
        AtomicODE(DifferentialSymbol(BaseVariable("x")), Variable("y"))))
  }

  it should "parse diffghost with cuts" in {
    p("x' = -x, /++ y' = y * (1/2) ++/ & !inv:(x*y^2 = 1) by auto", pp.proveODE(_)) shouldBe(
      ProveODE(DiffProductStatement(AtomicODEStatement(AtomicODE(DifferentialSymbol(BaseVariable("x")), Neg(BaseVariable("x")))),
        DiffGhostStatement(AtomicODEStatement(AtomicODE(DifferentialSymbol(BaseVariable("y")), Times(Variable("y"), Divide(Number(1), Number(2))))))),
        DomAssert(Variable("inv"), Equal(Times(Variable("x"), Power(Variable("y"), Number(2))), Number(1)), Using(List(DefaultSelector), Auto()))
      )
    )
  }
  it should "parse inverse diffghost" in {
    p("/-- x' = y --/;", pp.diffStatement(_)) shouldBe InverseDiffGhostStatement(AtomicODEStatement(
      AtomicODE(DifferentialSymbol(BaseVariable("x")), Variable("y"))))
  }

  it should "parse diffweak" in {
    p("x' = y & /-- ?dc:(x > 0) --/;", pp.statement(_)) shouldBe ProveODE(AtomicODEStatement(AtomicODE(
      DifferentialSymbol(BaseVariable("x")), Variable("y")
    )), DomWeak(DomAssume(Variable("dc"), Greater(Variable("x"), Number(0)))))
  }

  it should "parse diffcut" in {
    p("x' = y & !dc:(x > 0) by auto;", pp.statement(_)) shouldBe ProveODE(AtomicODEStatement(AtomicODE(
      DifferentialSymbol(BaseVariable("x")), Variable("y")
    )), DomAssert(Variable("dc"), Greater(Variable("x"), Number(0)), Using(List(DefaultSelector),Auto())))
  }

  it should "parse dc-assign" in {
    p("x' = y & t := T;", pp.statement(_)) shouldBe ProveODE(AtomicODEStatement(AtomicODE(
      DifferentialSymbol(BaseVariable("x")), Variable("y")))
    , DomModify(VarPat(Variable("t")), Variable("T")))
  }

  it should "parse conjunction" in {
    p("x' = y & t := T & !dc:(x > 0) by auto;", pp.statement(_)) shouldBe ProveODE(AtomicODEStatement(AtomicODE(
      DifferentialSymbol(BaseVariable("x")), Variable("y")))
      , DomAnd(
          DomModify(VarPat(Variable("t")), Variable("T")),
          DomAssert(Variable("dc"), Greater(Variable("x"), Number(0)), Using(List(DefaultSelector), Auto()))))
  }

  it should "parse example from 1d car" in {
    val nt = Nothing
    p("{{x' = v, v' = a, t' = 1 & ?(t <= T & v>=0)}; }*", pp.statement(_)) shouldBe BoxLoop(ProveODE(DiffProductStatement(
      AtomicODEStatement(AtomicODE(dx, vv)), DiffProductStatement(AtomicODEStatement(AtomicODE(dv, va)), AtomicODEStatement(AtomicODE(dt, Number(1))))),
      DomAssume(nt, And(LessEqual(vt, vT), GreaterEqual(vv, Number(0)))))
    )
  }

  "formula error messages" should "exist" in {
    parse("(x <=2 ", ep.formula(_)) match {
      case (s : Success[Formula]) => println("success: " + s)
      case (f: Failure) => println(f.extra.trace())
    }
  }

  "program error messages" should "exist" in {
    parse("x'=2 & x >= ;", ep.program(_)) match {
      case (s : Success[Program]) => println("success: " + s)
      case (f: Failure) => println(f.extra.trace())
    }
  }
}
