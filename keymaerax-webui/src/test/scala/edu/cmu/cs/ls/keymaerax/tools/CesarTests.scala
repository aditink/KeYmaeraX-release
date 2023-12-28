package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core.{Equiv, Formula, Imply, ODESystem, True}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.tools.ext.SmtLibReader.readFml
import edu.cmu.cs.ls.keymaerax.tools.ext.ceasar.{Cesar, MathTool, PostfixPrinter, Template}

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.concurrent.{Future, _}
import scala.language.postfixOps
import scala.sys.process._

class CesarTests extends TacticTestBase {

  // Benchmarks.
  // DIFFERENT SEMANTICS than dL: initial assumption formulas must hold throughout.

  val gears : String = "1=1 & T>0 ->" +
    "[{{r:=0; ++ r:=1; ++ r:=2; ++ r:=3; ++ r:=4; ++ r:=5; ++ r:=6; ++ r:=7;}^@" +
    "t:=0;{x'=r,t'=1 & t<=T}}*](x<=y)"

  val etcs: String = "A>0 & B>0 & T>0 & v>=0 -> " +
    "[{{a:=A; ++ a:=-B;}^@" +
    "t:=0;{p'=v,v'=a,t'=1 & t<=T & v>=0}}*](e-p>0)"

  val spaceship: String = "a1>0 & a2>0 & a3>0 & b1>0 & b2>0 & b3>0 & T>0 -> " +
    "[{{{ax:=a1;  ay:=a2;  az:=a3;}" +
    "++ {ax:=-b1; ay:=-b2; az:=-b3;}}^@" +
    "t:=0;{px'=vx,vx'=ax, py'=vy, vy'=ay, pz'=vz, vz'=az, t'=1 & t<=T}}*](px+py+pz<R)"

  val tt1d = "V>0 & T>0 -> [{{v:=V; ++ v:=-V;}^@ t:=0; {x'=v,t'=1 & t<=T}}*](x<=X)"

  val reservoir: String = "F>0 & mh>0 & i>0 & i<=F & T>0 & h>=0 ->" +
    "[{{f:=0; ++ f:=F;}^@" +
    "t:=0;{h'=i-f, t'=1 & t<=T & h>=0}}*](h<=mh)"

  val rocket: String = "v>=0 & A>0 & B>0 & T>0 ->" +
    "[{{j:=A; ++ j:=-B;}" +
    "t:=0;{p'=v,v'=a,a'=j,t'=1 & t<=T & v>=0 & a<=0}}*](e-p>0)"

  val reaction: String = "A>0 & B>0 & Ra<A & Rb<B &Ra>0 & Rb>0 & T>0 & X>0 & Y>0 & T>0 ->" +
    "[{{{a:=A; b:=B;} ++ {b:=0; a:=0;}}^@" +
    "t:=0; {x'=a-Ra, y'=b-Rb, t'=1 & t<=T}}*](x>X & y>Y)"

  val merge: String = "tx>0 & ty>0 & v>0 & vy=v & T>0 ->" +
    "[{{vx:=-v; ++ vx:=v;}^@" +
    "t:=0; {x'=vx,y'=vy,t'=1 & t<=T}}*](y<ty | tx<x)"

  val wall: String = "tx>0 & ty>0 & v>0 & vy=v & T>0 ->" +
    "[{{vs:=-v; ++ vx:=v;}^@" +
    "t:=0; {x'=vx, y'=vy, t'=1 & t<=T}}*](y<ty | x<(-tx) | tx<x)"

  val sled: String = "Tx>0 & Ty>0 & V>0 & T>0 ->" +
    "[{{vx:=-V; ++ vx:=V;}^@" +
    "t:=0; {x'=vx, y'=V, t'=1 & t<=T}}*](y<Ty | x<(-Tx) | Tx<x)"

  val movingWall: String = "ty>0 & v>0 & vy=v & T>0 ->" +
    "[{{vx:=-v; ++ vx:=v;}^@" +
    "t:=0; {x'=vx, y'=vy, tx'=1, t'=1 & t<=T}}*](y<ty | x<(-tx) | tx<x)"

  val parachute: String = "(f=0 | v=u) & T>=0 & u>0 & Vx>0 & X>0 ->" +
    "[{{{z:=1;}++{?f=0; f:=1; v:=u;}}^@" +
    "t:=0; {x'=Vx,y'=v,t'=1 & t<=T}}*](y>0 | x<X)"

  val corridor: String = "v>0 & T>0 & R>0 ->" +
    "[{{{vx:=0;vy:=-v;}++{vy:=0;vx:=-v;}}^@" +
    "t:=0; {x'=vx,y'=vy,t'=1 & t<=T}}*]((x>-3*R & -R<y & y<R) | (y<R & -R<x & x<R))"

  val tJunction: String = "v>0 & T>0 & R>0 ->" +
    "[{{{vx:=0;vy:=v;}++{vy:=0;vx:=-v;}++{vy:=0;vx:=v;}}^@" +
    "t:=0; {x'=vx,y'=vy,t'=1 & t<=T}}*]((-R<y & y<R) | (y<R & -R<x & x<R))"

  val loopRoad = ""

  val sputteringCar: String = "T>=0 & v>=0 & A>0 & p<0 & q<0 & r<0 ->" +
    "[{{{a:=*;?a<=A;?a>0;}++{a:=0;}}^@" +
    "t:=0; {x'=v,v'=a+p*v+q*v^2+r*v^3,t'=1 & t<=T & v>=0}}*](v<=V) "

  val curveBot : String =
    "T>0 ->" +
      "[{{om:=-1; ++ om:=0; ++ om:=1;}^@;" +
      "t:=0; {x'=v,y'=w,v'=om*w,w'=-om*v, t'=1 & t<=T}}*" +
      "]!(x=0 & y=0)"

  val parachute2: String =
    "T>0 & p>0 & g>0 & r>0 & m>0 & v>0 ->" +
      "[{{?1=1; ++ r:=p;}^@;" +
      "t:=0; {x'=-v, v'=-r*v^2+g, t'=1 & v>0 & t<=T}}*" +
      "](x<0 | v<m)"

  /** Chemical reaction. */
  val chemicalReaction : String = "kA>0 & kB>0 & kC>0 & kT>0 & T>0 ->" +
    "[{ {o:=0 ++ o:=1}^@;" +
    "t:=0; {A'=-o*A*B*Tmp*kA, B'=-o*A*B*Tmp*kB, C'=o*A*B*Tmp*kC, " +
    "Tmp'=o*A*B*Tmp*kT, t'=1 & t<=T & A>=0 & B>=0 & C>=0 & Tmp>=0}" +
    "}*]Tmp<=Tmpmax"

  val intersectionOld : String = {
    "B>0 & T>0 & vmax>0 & v>=0 ->" +
      "[{ {a:=*;}^@; " +
      "{t:=0; {x'=v, v'=a, timeToRed'=-1, t'=1 & t<=T & v>=0}" +
      "}}*] (-B<=a & a<=0 & v<=vmax & ((timeToRed>0 & !(v=0)) | !(x=0)))"
  }

  val intersection : String = { //"-B<a & a<A & A>0 & B>0 & T>0 & v>=0 ->" +
    // Intersection is x=0.
    "B>0 & T>0 & v>=0 ->" +
      "[{ {a:=-B; ++ a:=0;}^@; " +
      "{t:=0; {x'=v, v'=a, timeToRed'=-1, t'=1 & t<=T & v>=0}" +
      "}}*] ((timeToRed>0 & !(v=0)) | !(x=0))"
  }

  val boat : String = "T>0 & AX>0 & AY>0 & vx>=0 ->" +
    "[{ {{ax:=-AX;ay:=0;} ++ {ay:=AY;ax:=0;}}^@; " +
    "{t:=0; {x'=vx, vx'=ax, y'=vy, vy'=ay, t'=1 & t<=T & vx>=0}}" +
    "}*] (x<mergeX | y>closedY)"

  val powerStation : String = "T=1 & i>=0 ->" +
    "[{ {{ i:=0; slope := 7000000; } " +
    "++  { i := 100; slope := -i*2000; }}^@;" +
    "t:=0; {produced' = i*2000 - i^2*5, stored'=slope, t'=1, gt'=-1 & t<=T} " +
    "}*] (stored>0 & (gt>0 | produced>3000))"

  val coolant : String = "T>0 & F>0 & minAbsorbed>0 & maxDischarge>0 & tempDiff>0 & c>0 ->" +
    "[{ {{ f:=0; } " +
    "++  { f:=F; }}^@;" +
    "t:=0; {absorbed' = f*c*tempDiff, discharged'=f, t'=1, gt'=-1 & t<=T} " +
    "}*] (discharged<maxDischarge & (gt>0 | absorbed>= minAbsorbed))"

  // Exceeds 80k characters.
  val falcon : String = "V>0 & T>0 ->" +
    "[{ {v:=*;}^@;" +
    "t:=0; {x'=v, t'=1, gt'=-1 & t<=T}" +
    "}*](gt>0 | (0<x & x< 10))"

  val falcon2 : String = "V>0 & T>0 & (h=1 | h=1000) ->" +
    "[{ {{v:=-V;{h:=1; ++ h:=1000;}^@;}" +
    " ++ {v:=V;{h:=1; ++ h:=1000;}^@;}" +
    " ++ {v:=v*h;}}^@;" +
    "t:=0; {x'=v, t'=1, gt'=-1 & t<=T}" +
    "}*](gt>0 | (0<x & x< 10))"

  // Too complex: second round forall times out.
  val river : String =
    "T>0 ->" +
      "[{{vx:=*; vy:=*;}^@;" +
      "t:=0; {x'=vx, y'=vy-5, t'=1, gt'=-1 & t<=T}" +
      "}*](vx^2+vy^2=100 & (gt>0 | (x>100 & y>0)))"

  val hydraulicBrake : String = "T>0 & v>=0 & hb>=0 ->" +
    "[{ {{slope:=0;} ++ {slope:=30;}}^@;" +
    "{t:=0; {x'=v, v'=-hb, hb'=slope, t'=1 & t<=T & v>=0}} }*]" +
    "(hb<=100 & x<0)"

  // Map of benchmarks names to their strings.
  val benchmarksMap: Map[String, String] = Map(
    "gears" -> gears,
    "etcs" -> etcs,
    "spaceship" -> spaceship,
    "tt1d" -> tt1d,
    "reservoir" -> reservoir,
    "rocket" -> rocket,
    "reaction" -> reaction,
    "merge" -> merge,
    "tree" -> sled,
    "parachute" -> parachute,
    "corridor" -> corridor,
    "tJunction" -> tJunction,
    "loopRoad" -> loopRoad,
    "sputteringCar" -> sputteringCar
  )

  val TACASBenchmarksMap: Map[String, String] = Map(
    "etcs" -> etcs,
    "sled" -> sled,
    "parachute" -> parachute2,
    "corridor" -> corridor,
    "curveBot" -> curveBot,
    "coolant" -> coolant,
    "intersection" -> intersection,
    "powerStation" -> powerStation,
  )

  // Unit tests.

  "fromFormulaToTemplate" should "extract a template problem from valid input" in {
    val f = etcs.asFormula
    val template: Template = f
    template.init should be("A>0 & B>0 & T>0 & v>=0".asFormula)
    template.body should be("{a:=A;++a:=-B;}^@".asProgram)
    template.dynamics should be("{p'=v,v'=a,t'=1 & t<=T & v>=0}".asProgram)
    template.post should be("e-p>0".asFormula)
  }

  "unboundedTimeDynamics" should "remove t<=T from domain constraints" in {
    val f = etcs.asFormula
    val template: Template = f
    template.unboundedTimeDynamics should be("{p'=v,v'=a,t'=1 & v>=0}".asProgram)
  }

  /** This test is out of date because powerstation no longer has demonic assignment. */
  "noExists" should "catch exists in a template" in {
    val f = powerStation.asFormula
    val template: Template = f
    template.noExists should be(false)
  }

  "noExists" should "catch absence of exists in a template" in {
    val f = corridor.asFormula
    val template: Template = f
    template.noExists should be(true)
  }

  // Synthesis experiments.

  "synthesize" should "solve curveBot invariant" in withMathematica(tool => {
    val f = curveBot.asFormula
    val ceaser = new Cesar(tool, f, debug = true, allowEgg=true)
    val results = ceaser.synthesize
    results should have length 4
    // Print results
    results.foreach(r => println(r.prettyString))
  })

  "synthesize" should "solve intersection invariant" in withMathematica(tool => {
    val f = intersection.asFormula
    val cesar = new Cesar(tool, f, debug = true, n = 0)
    val results = cesar.synthesize
    results should have length 3
    // Print results
    println("Results:")
    results.foreach(r => println(r.prettyString))
  })

  "synthesize" should "solve intersection invariant2" in withMathematica(tool => {
    val f = intersectionOld.asFormula
    val cesar = new Cesar(tool, f, debug = true, n = 0)
    val results = cesar.synthesize
    results should have length 3
    // Print results
    results.foreach(r => println(r.prettyString))
  })

  "synthesize" should "solve powerStation invariant" in withMathematica(tool => {
    val f = powerStation.asFormula
    val cesar = new Cesar(tool, f, debug = true, allowEgg = false, n=2)
    val results = cesar.synthesize
    // Print results
    results.foreach(r => println(r.prettyString))
  })

  "synthesize" should "solve coolant invariant" in withMathematica(tool => {
    val f = coolant.asFormula
    val cesar = new Cesar(tool, f, debug = true, n=1, allowSimplify = false, unfoldBased = true)
    val results = cesar.synthesize
    // Print results
    results.foreach(r => println(r.prettyString))
  })

  "synthesize" should "solve hydraulicBrake invariant" in withMathematica(tool => {
    val f = hydraulicBrake.asFormula
    val cesar = new Cesar(tool, f, debug = true, allowEgg = false, n=1)
    val results = cesar.synthesize
    results should have length 2
    // Print results
    results.foreach(r => println(r.prettyString))
  })

  "synthesize" should "solve gears invariant" in withMathematica(tool => {
    val f = gears.asFormula
    val ceaser = new Cesar(tool, f)
    val results = ceaser.synthesize
    results should have length 9
    results should contain("x<=y".asFormula)
    // Print results
    results.foreach(r => println(r.prettyString))
  })

  "synthesize" should "solve boat invariant" in withMathematica(tool => {
    val f = boat.asFormula
    val ceaser = new Cesar(tool, f, debug = true, n=1)
    val results = ceaser.synthesize
    results should have length 3
    // Print results
    results.foreach(r => println(r.prettyString))
  })

  "synthesize" should "solve falcon invariant" in withMathematica(tool => {
    val f = falcon.asFormula
    val ceaser = new Cesar(tool, f, debug = true, n=1)
    val results = ceaser.synthesize
    // Print results
    results.foreach(r => println(r.prettyString))
  })

  "synthesize" should "solve falcon2 invariant" in withMathematica(tool => {
    val f = falcon2.asFormula
    val ceaser = new Cesar(tool, f, debug = true, n=1)
    val results = ceaser.synthesize
    // Print results
    results.foreach(r => println(r.prettyString))
  })

  "synthesize" should "solve river invariant" in withMathematica(tool => {
    val f = river.asFormula
    val ceaser = new Cesar(tool, f, debug = true, n=0)
    val results = ceaser.synthesize
    // Print results
    results.foreach(r => println(r.prettyString))
  })
  /** Not implemented yet. */
  "synthesize" should "produce proof for gears invariant" in withMathematica(tool => {
    val f = gears.asFormula
    val ceaser = new Cesar(tool, f)
    val (resultFml, tactic) = ceaser.resultFormula
    // Print results
    println(resultFml.prettyString)
    println("Tactic:")
    println(tactic.prettyString)
    // Check that tactic proves result.
    val proofResult = proveBy(f, tactic)
    println(proofResult.prettyString)
  })

  /**
   * Formula does not simplify yet.
   */
  "synthesize" should "solve etcs invariant" in withMathematica(tool => {
    val f = etcs.asFormula
    val ceaser = new Cesar(tool, f, debug = true, allowEgg = true)
    val results = ceaser.synthesize
    results should have length 3
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  "synthesize" should "solve tt1d invariant" in withMathematica(tool => {
    val f = tt1d.asFormula
    val ceaser = new Cesar(tool, f)
    val results = ceaser.synthesize
    results should have length 3
    results should contain("x<=X".asFormula)
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  /* TODO: Investigate why simplification not working very well for this question.
  *  This test fails currently.
  *  But the synthesized solutions are correct. */
  "synthesize" should "solve reservoir invariant" in withMathematica(tool => {
    val f = reservoir.asFormula
    val ceaser = new Cesar(tool, f, true)
    val results = ceaser.synthesize
    results should have length 3
    results should contain("h<=mh".asFormula)
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  /* TODO: Times out. */
  "synthesize" should "solve rocket invariant" in withMathematica(tool => {
    val f = rocket.asFormula
    val ceaser = new Cesar(tool, f, true)
    val results = ceaser.synthesize
    results should have length 3
    results should contain("h<=H".asFormula)
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  "synthesize" should "solve spaceship invariant" in withMathematica(tool => {
    val f = spaceship.asFormula
    val ceaser = new Cesar(tool, f, true)
    val results = ceaser.synthesize
    results should have length 3
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  /* TODO: Weird indexing stuff going on if forward propagation enabled. */
  "synthesize" should "solve reaction invariant" in withMathematica(tool => {
    val f = reaction.asFormula
    val ceaser = new Cesar(tool, f, true)
    val results = ceaser.synthesize
    results should have length 3
    results should contain("x>X&y>Y".asFormula)
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  "synthesize" should "solve merge invariant" in withMathematica(tool => {
    val f = merge.asFormula
    val ceaser = new Cesar(tool, f, true)
    val results = ceaser.synthesize
    results should have length 3
    results should contain("x>X&y>Y".asFormula)
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  "synthesize" should "solve sled invariant" in withMathematica(tool => {
    val f = sled.asFormula
    val ceaser = new Cesar(tool, f, true, allowEgg=true)
    val results = ceaser.synthesize
    results should have length 3
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  "synthesize" should "solve tree invariant" in withMathematica(tool => {
    val f = sled.asFormula
    val ceaser = new Cesar(tool, f, true)
    val results = ceaser.synthesize
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  "synthesize" should "solve movingWall invariant" in withMathematica(tool => {
    val f = movingWall.asFormula
    val ceaser = new Cesar(tool, f, true)
    val results = ceaser.synthesize
    results should have length 3
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  "synthesize" should "solve parachute invariant" in withMathematica(tool => {
    val f = parachute2.asFormula
    val ceaser = new Cesar(tool, f, true, allowEgg = true)
    val results = ceaser.synthesize
    results should have length 3
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  "synthesize" should "solve corridor invariant" in withMathematica(tool => {
    val f = corridor.asFormula
    val ceaser = new Cesar(tool, f, true, allowEgg = true, n=1)
    val results = ceaser.synthesize
    results should have length 3
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  "tJunction" should "solve tJunction invariant" in withMathematica(tool => {
    val f = tJunction.asFormula
    val ceaser = new Cesar(tool, f, true, true, 1)
    val results = ceaser.synthesize
    results should have length 4
    results should contain("x>X&y>Y".asFormula)
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  "synthesize" should "solve sputteringCar invariant" in withMathematica(tool => {
    val f = sputteringCar.asFormula
    val ceaser = new Cesar(tool, f, true, true, 0)
    val results = ceaser.synthesize
    results should have length 3
    results should contain("v<=V".asFormula)
    // Print results
    results.foreach(r => println(r.prettyString))
  }
  )

  // Tool experiments.

  "postfix printer" should "print a dL formula in smtlib syntax" in {
    val inputFml = "B>0 & T>0 & v>=0".asFormula
    val result = PostfixPrinter.print(inputFml)
    println(result)
  }

  "smtlib reader" should "read smtlib formula" in {
    val inputString = "(or (and (= v 0) (distinct x 0)) (and (> v 0) (or (and (< x 0) (or (or (and (= 0 (+ (* 3 timeToRed) (* (* 2 (^ v -1)) x))) (or (and (< T timeToRed) (= B (* (^ timeToRed -1) v))) (and (< (+ (^ v 3) (* (* (* 2 B) v) (+ (* T v) x))) 0) (distinct B (* (^ timeToRed -1) v))))) (or (and (or (and (> (* v (+ (* (* 3 timeToRed) v) (* 2 x))) 0) (< (* v (+ (* timeToRed v) x)) 0)) (and (< (* v (+ (* (* 3 timeToRed) v) (* 2 x))) 0) (> timeToRed 0))) (or (and (< B (* (* 2 (^ timeToRed -2)) (+ (* timeToRed v) x))) (< (+ T (* (^ 2 (/ 1 2)) (^ (* (^ B -1) (+ (* timeToRed v) x)) (/ 1 2)))) timeToRed)) (and (< T timeToRed) (= 0 (+ (* 2 B) (* (^ v 2) (^ (+ (* timeToRed v) x) -1))))))) (> (* v (+ (* timeToRed v) x)) 0))) (and (< (+ (^ v 3) (* (* (* 2 B) v) (+ (* T v) x))) 0) (or (= 0 (+ timeToRed (* (^ v -1) x))) (or (and (distinct (+ (* 2 B) (* (^ v 2) (^ (+ (* timeToRed v) x) -1))) 0) (or (< (* v (+ (* (* 3 timeToRed) v) (* 2 x))) 0) (and (> (* v (+ (* (* 3 timeToRed) v) (* 2 x))) 0) (< (* v (+ (* timeToRed v) x)) 0)))) (<= timeToRed 0)))))) (or (and (> timeToRed 0) (= 0 x)) (> x 0)))))"
    val fml = readFml(inputString)
    println(fml)
  }

  "mathematica" should "check equivalence under assumptions" in withMathematica(tool => {
    val assumptions = "v>0 & T>0 & R>0".asFormula
    val f1 = "(R < x&x < 2*R)&((y>=R&(v<=0|T < t)|(v<=0|T < t)&y<=(- 1)*R)|(y < R&(- 1)*R < y)&(t < 0&(v < t^(- 1)*(R-x)&T < 2*R*v^(- 1)|T < v^(- 1)*(R+t*v+x)&v < t^(- 1)*((- 1)*x-R)&t^(- 1)*(R-x)<=v)|0=t&(v<=0|T < 2*R*v^(- 1))|T < 2*R*v^(- 1)&v < 2*R*t^(- 1)|v<=0|T < t&v>=2*R*t^(- 1)))|x=R&((y>=R&(v<=0|T < t)|(v<=0|T < t)&y<=(- 1)*R)|(y < R&(- 1)*R < y)&(t < 0&T < v^(- 1)*(R+t*v+x)|0=t&(v<=0|T < v^(- 1)*(R+x))|T < v^(- 1)*(R+x)&v < t^(- 1)*(R+x)|v<=0|T < t&v>=t^(- 1)*(R+x)))|((y>=R&(v<=0|T < t)|(v<=0|T < t)&y<=(- 1)*R)|(y < R&(- 1)*R < y)&(t < 0&(v < t^(- 1)*(R-x)&T < 2*R*v^(- 1)|T < v^(- 1)*(R+t*v+x)&v < t^(- 1)*((- 1)*x-R)&t^(- 1)*(R-x)<=v)|0=t&(v<=0|T < 2*R*v^(- 1))|T < 2*R*v^(- 1)&v < 2*R*t^(- 1)|v<=0|T < t&v>=2*R*t^(- 1)))&x>=2*R|(v<=0|T < t)&x<=(- 1)*R|((- 1)*R < x&x < R)&(y < R|y>=R&(v<=0|T < t))".asFormula
    val f2 = "T*v < 2*R&(R>x|y>0|R+y>0)&(R>y|y<=0)&R+x>T*v|y < R&(R>x|x<=0)&(x>0|R+x>0)".asFormula
    val equiv = Equiv(f1, f2)
    val result = tool.simplify(tool.reduce(Imply(assumptions, equiv)), List(assumptions))
    println(result)
  })

  "z3" should "check equivalence under assumptions" in withZ3(ztool => {
    val assumption = "T>0".asFormula
    val f1 = "(!2*v=y|!x=0|!2*v+y=0)&(x=0|!2*v*x*y=x*(2*w*x+x^2+y^2)|!x^3+x*y*(2*v+y)=2*w*x^2)&!y=0".asFormula
    val f2 = "!y=0".asFormula
    val equivFml = Equiv(f1, f2)
    println("Equivalent?: ")
    ztool.check(edu.cmu.cs.ls.keymaerax.core.Not(Imply(assumption, equivFml)))
  })

  "resolveForallTool" should "resolve a conditional forall statement" in withMathematica(tool => {
    // Using resolveForall
    val condition = "t >= 0".asFormula
    val expression = "v + t > 0".asFormula
    val t = "t".asVariable
    val sol = tool.simplify(tool.resolveForall(t, condition, expression),Nil)
    sol should be("v>0".asFormula)

    // Using regular resolve but with implication doesn't work.
    val sol2 = tool.simplify(tool.resolve(Imply(condition, expression)),Nil)
    sol2 should not be "v>0".asFormula
  })

  "mathTool" should "resolve forall" in withMathematica(tool => {
    val mathTool = new MathTool(tool, List())
    // Failing problem.
    val assumption = "A>0&B>0&T>0&vmax>0&v>=0&(0=t|t>=0&a*t+v>=0&t<=T)".asFormula
    val formula = "(!intersection=1/2*(a*t^2+2*t*v+2*x)&a*t+v=0|a*t+v>0&vmax>=a*t+v&(intersection < 1/2*(a*t^2+2*t*v+2*x)&(-1)*t+timeToRed<=0|(-1)*t+timeToRed>0&intersection < ((-1)*t+timeToRed)*(a*t+v)+1/2*(a*t^2+2*t*v+2*x)|2*B*((-1)*t+timeToRed)>a*t+v|2*B*(intersection+(- 1)*(1/2*(a*t^2+2*t*v+2*x)))>(a*t+v)^2))&-B<=a&a<=A&a*t+v<=vmax&((-1)*t+timeToRed>0&!a*t+v=0|!1/2*(a*t^2+2*t*v+2*x)=intersection)".asFormula
    val sol = mathTool.resolveForallCleanAssumptions("t".asVariable, formula, assumption)
    print(sol)
  })

  "integrationTool" should "solve the ODE" in withMathematica(tool => {
    val differentialProg = "{p'=v,v'=a,t'=1}".asProgram.asInstanceOf[ODESystem].ode
    val Some(sol) = tool.odeSolve(differentialProg,
      "t".asVariable,
      Map("p".asVariable -> "p0".asVariable, "v".asVariable -> "v0".asVariable, "a".asVariable -> "a0".asVariable)
    )
    sol should be("p=1/2*(2*p0+a*t^2+2*t*v0)&v=a*t+v0".asFormula)
  }
  )

  "pegasus" should "do first integrals" in withMathematica(tool => {
    val sol = tool.firstIntegral("{x'=v,y'=w,v'=1*w,w'=-1*v,t'=1}".asDifferentialProgram, True, 1)
    sol should contain("v + (-1)*y".asTerm)
    sol should contain("w + x".asTerm)
  })

  "pegasus" should "do darboux polynomials" in withMathematica(tool => {
    val sol = tool.darboux("{x'=-v,v'=-r*v^2+g,t'=1}".asDifferentialProgram, "v > 0".asFormula, 1)
    sol should contain("g^(1/2)".asTerm)
    sol should contain("g^(1/2)+(-1)*r^(1/2)*v".asTerm)
    sol should contain("g^(1/2) + r^(1/2)*v".asTerm)
  })

  "maximizationTool" should "maximize under constraints" in withMathematica(tool => {
    val xTerm = "x".asTerm
    val constraints = "x <= c & x <= 2 + t".asFormula
    val elimVar = "x".asVariable
    val sol = tool.maximize(xTerm, constraints, elimVar)
    println("Maximization solution: " + sol)
    sol should be("x=2+t".asFormula)
  })

  "eggSimplify" should "simplify a formula" in withMathematica (tool =>{
    val mathTool = new MathTool(tool, List())
    val formula = "x<=y | x>y".asFormula
    val assumption = "1=1".asFormula
    val result = mathTool.eggSimplify(formula, assumption)
    println(result)
    result shouldBe "true".asFormula
  })

  "eggSimplify" should "simplify a formula and check equivalence" in withMathematica (tool =>{
    val mathTool = new MathTool(tool, List())
    val formula = "Tx+2*T*V+y < Ty+x&(Tx>x&x>0|Tx+Ty>x+y&Tx<=x)|x=0|Tx+x+y < Ty&(x>0|Tx+x>0&x < 0)|Tx+T*V < x&Tx+Ty<=x+y|Tx+x < 0|Ty>y&Tx+x<=0".asFormula
    val assumption = "(y < Ty&(Ty>Tx+x+y|Ty+x>Tx+y)|Tx < x|Tx+x < 0) & ".asFormula
    val result = mathTool.eggSimplify(formula, assumption)
    println(result)
    val equivFml = Equiv(formula, result)
    val trueWhen = tool.simplify(tool.reduce(Imply(assumption, equivFml)), List(assumption))
    println("Equivalent when: "+trueWhen)
  })

  /** Utility to quickly simplify stuff using eggs.
   * If last line says unsat (printed output of z3.check), then equivalence is true. */
  "eggSimplify" should "simplify a formula and check equivalence using z3" in withZ3(ztool => {
    def eggSimplify(expr: Formula, assumptions: Formula, arg: String = "-s"): Formula = {
      val assumptionsString = PostfixPrinter.print(assumptions)
      val exprString = PostfixPrinter.print(expr)
      println("problem: "+exprString)
      println("assumptions: "+assumptionsString)

      val result = Seq("./my-first-egg", arg, exprString, assumptionsString).!!

      print("Egg Simplification: " + result)
      val resultFormula = readFml(result)
      println("New formula: " + resultFormula)
      resultFormula
    }
    val formula = "Tx+2*T*V+x+y < Ty&(Tx+x=0&Ty>y|Tx+x>0&x < 0&Tx+x+y < Ty|Tx+Ty+x>y&Tx+x < 0)|Tx < x|Tx+y < Ty+x&(x < 0|Tx>x|Tx+x<=0)|Tx+x < 0&Tx+T*V+x < 0&Tx+Ty+x<=y|Tx<=x&Ty>y".asFormula
    val assumption = "Tx>0 & Ty>0 & V>0 & T>0 & (Tx < x|Tx+x < 0|y < Ty&(Ty>Tx+x+y|Ty+x>Tx+y))".asFormula
    val result = eggSimplify(formula, assumption, "-a")
    println(result)
    val equivFml = Equiv(formula, result)
    println("Equivalent?: ")
    ztool.check(edu.cmu.cs.ls.keymaerax.core.Not(Imply(assumption, equivFml)))
  })


  "Cesar" should "solve and time all benchmarks" in withMathematica(tool => {
    val numReps = 5
    val benchmarks = List(
      ("etcs", 0),
      ("spaceship", 0),
      ("corridor", 1),
      ("withMathematica(_ => ion", 0),
      ("powerStation", 2)
    )
    def time[R](block: => R): R = {
      val t0 = System.nanoTime()
      val result = block    // call-by-name
      val t1 = System.nanoTime()
      // Convert to seconds and print t1-t0.
      println("Elapsed time: " + (t1 - t0) / 1000000000.0 + "s")
      println(result)
      result
    }
    // Run all benchmarks without eager simplification with timeout of 1 minute.
    def runWithTimeout[T](timeoutMs: Long)(f: => T) : Option[T] = {
      try {
        Some(Await.result(Future(f), timeoutMs milliseconds))
      }
      catch {
        case e: Throwable => println("Exception caught: " + e.getMessage)
          None
      }
    }
    println("Don't allow egg.")
    for ((benchmark, depth) <- benchmarks) {
      println("Benchmark: " + benchmark)
      val f = TACASBenchmarksMap(benchmark).asFormula
      val ceaser = new Cesar(tool, f, false, true, depth, allowEgg = false, allowSimplify = true)
      time {
        // 10 minute timeout.
        runWithTimeout(600000)(ceaser.synthesize)
      }
    }

    println("allow egg.")
    for ((benchmark, depth) <- benchmarks) {
      println("Benchmark: " + benchmark)
      val f = TACASBenchmarksMap(benchmark).asFormula
      val ceaser = new Cesar(tool, f, false, true, depth, allowEgg = true, allowSimplify = true)
      // 10 minute timeout.
      for (_ <- 1 to numReps)
      {
        time {
          runWithTimeout(600000)(ceaser.synthesize)
        }
      }
    }
  })
}