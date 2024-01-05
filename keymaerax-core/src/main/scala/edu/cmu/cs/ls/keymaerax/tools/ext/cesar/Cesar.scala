package edu.cmu.cs.ls.keymaerax.tools.ext.ceasar

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.TacticHelper.freshNamedSymbol
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{autoClose, loop, unfoldProgramNormalize}
import edu.cmu.cs.ls.keymaerax.core.{And, Assign, AssignAny, AtomicODE, Box, Choice, Compose, Diamond, DifferentialProduct, DifferentialProgram, DifferentialSymbol, Divide, Dual, Equal, Exists, False, Forall, Formula, FuncOf, Greater, GreaterEqual, Imply, Less, LessEqual, Loop, Minus, Neg, Not, NotEqual, Nothing, Number, ODESystem, Or, Plus, Power, PredOf, PredicationalOf, Program, Sequent, StaticSemantics, Term, Test, Times, True, UnitPredicational, Variable}
import edu.cmu.cs.ls.keymaerax.infrastruct.DependencyAnalysis.{analyseModal, scc}
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, SubstitutionHelper}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.tools.ext.Mathematica
import edu.cmu.cs.ls.keymaerax.tools.ext.SmtLibReader.readFml
import edu.cmu.cs.ls.keymaerax.tools.ext.ceasar.Template.fromFormulaToTemplate

import scala.collection.immutable.IndexedSeq
import scala.language.{implicitConversions, postfixOps}
import scala.sys.process._
import scala.util.Random

/**
 * Implementation of the CESAR algorithm.
 */

/** Utility printer to print formulas in postfix notation so as to pass to egg.
 * For example, "v>=0&A>0&B>0&T>0&vmax>0" becomes "& (>= v 0) (& (> A 0) " +
   "(& (> B 0) (& (> T 0) (& (> vmax 0)))))".
 */
object PostfixPrinter {
  def print(f: Formula): String = {
    f match {
      case And(l, r) => "(and " + print(l) + " " + print(r) + ")"
      case Or(l, r) => "(or " + print(l) + " " + print(r) + ")"
      case Imply(l, r) => "(=> " + print(l) + " " + print(r) + ")"
      case Not(f) => "(not " + print(f) + ")"
      case Equal(l, r) => "(= " + print(l) + " " + print(r) + ")"
      case NotEqual(l, r) => "(distinct " + print(l) + " " + print(r) + ")"
      case Less(l, r) => "(< " + print(l) + " " + print(r) + ")"
      case LessEqual(l, r) => "(<= " + print(l) + " " + print(r) + ")"
      case Greater(l, r) => "(> " + print(l) + " " + print(r) + ")"
      case GreaterEqual(l, r) => "(>= " + print(l) + " " + print(r) + ")"
      case _ => f.toString
    }
  }

  /** postfix printing for terms. */
  def print(trm: Term): String = {
    trm match {
      case Plus(l, r) => "(+ " + print(l) + " " + print(r) + ")"
      case Minus(l, r) => "(- " + print(l) + " " + print(r) + ")"
      case Times(l, r) => "(* " + print(l) + " " + print(r) + ")"
      case Divide(l, r) => "(/ " + print(l) + " " + print(r) + ")"
      case Power(l, r) => "(^ " + print(l) + " " + print(r) + ")"
      case Neg(t) => "(- " + print(t) + ")"
      // In the case of a number, avoid extra parens.
      case Number(n) =>
        // Also handle negative numbers specially so that extra optimizations apply.
        if (n<0) {
          "(- " + (-n).toString + ")"
        } else n.toString
      // Assume all instances of FuncOf are nullary (second parameter is unit).
      case FuncOf(f, _) => f.name
      case _ => trm.toString
    }
  }
}

object defuncHelper {

  /** Takes in terms with nullary functions like A() and changes these into variables (like A). */
  private def deFuncTerm(trm: Term): Term = {
    trm match {
      case Plus(l, r) => Plus(deFuncTerm(l), deFuncTerm(r))
      case Minus(l, r) => Minus(deFuncTerm(l), deFuncTerm(r))
      case Times(l, r) => Times(deFuncTerm(l), deFuncTerm(r))
      case Divide(l, r) => Divide(deFuncTerm(l), deFuncTerm(r))
      case Power(l, r) => Power(deFuncTerm(l), deFuncTerm(r))
      case Neg(t) => Neg(deFuncTerm(t))
      case FuncOf(f, c) if c==Nothing => Variable(f.name)
      case _ => trm
    }
  }

  /** Takes in formulas with nullary functions like A() and changes these into variables (like A). */
  def deFunc(fml: Formula): Formula = {
    fml match {
      case And(l, r) => And(deFunc(l), deFunc(r))
      case Or(l, r) => Or(deFunc(l), deFunc(r))
      case Imply(l, r) => Imply(deFunc(l), deFunc(r))
      case Not(f) => Not(deFunc(f))
      case Equal(l, r) => Equal(deFuncTerm(l), deFuncTerm(r))
      case NotEqual(l, r) => NotEqual(deFuncTerm(l), deFuncTerm(r))
      case Less(l, r) => Less(deFuncTerm(l), deFuncTerm(r))
      case LessEqual(l, r) => LessEqual(deFuncTerm(l), deFuncTerm(r))
      case Greater(l, r) => Greater(deFuncTerm(l), deFuncTerm(r))
      case GreaterEqual(l, r) => GreaterEqual(deFuncTerm(l), deFuncTerm(r))
      case Box(p, f) => Box(deFuncProg(p), deFunc(f))
      case Diamond(p, f) => Diamond(deFuncProg(p), deFunc(f))
      case _ => fml
    }
  }

  private def deFuncDifferentialProg(program: DifferentialProgram): DifferentialProgram = {
    program match {
      case AtomicODE(xprime, e) => AtomicODE(xprime, deFuncTerm(e))
      case DifferentialProduct(p1, p2) => DifferentialProduct(deFuncDifferentialProg(p1), deFuncDifferentialProg(p2))
    }
  }

  private def deFuncProg(program: Program): Program = {
    program match {
      case Compose(a, b) => Compose(deFuncProg(a), deFuncProg(b))
      case Dual(a) => Dual(deFuncProg(a))
      case Choice(a, b) => Choice(deFuncProg(a), deFuncProg(b))
      case Assign(x, v) => Assign(x, deFuncTerm(v))
      case Test(f) => Test(deFunc(f))
      case Loop(p) => Loop(deFuncProg(p))
      case ODESystem(ode, domain) => ODESystem(deFuncDifferentialProg(ode), deFunc(domain))
      case _ => program
    }
  }
}

/** Exception for when input formula does not match CESAR's template. */
class TemplateMismatchException(message: String) extends Exception(message) {

  def this(message: String, cause: Throwable) {
    this(message)
    initCause(cause)
  }

  def this(cause: Throwable) {
    this(Option(cause).map(_.toString).orNull, cause)
  }

  def this() {
    this(null: String)
  }
}

/**
 * The template that ceasar fills in the holes of.
 */
case class Template(
                     init: Formula,
                     body: Program,
                     dynamics: ODESystem,
                     post: Formula) {

  /**
   * Special programs/formulas
   */
  private val timeConstr : Formula = "t<=T".asFormula

  /**
   * Relax the t<=T in the input dynamics.
   * @return Dynamics with t<=T removed.
   */
  def unboundedTimeDynamics: ODESystem = {
    // Flatten out constrs
    val constrsList = FormulaTools.conjuncts(dynamics.constraint)
    val filtered = constrsList.filterNot(x => x.equals(timeConstr))
    val newConstr = FormulaTools.conjunctionOfList(filtered)
    ODESystem(dynamics.ode, newConstr)
  }

  /** Get a list of the variables in order of their dependencies. */
  def orderedVarList: List[Variable] = {
    val fml: Formula = this
    val sequent = Sequent(IndexedSeq(), IndexedSeq(fml))
    val Imply(_, Box(prog, _)) = fml

    val adjls = analyseModal(prog, sequent).mapValues(v => v._1)
    val sccs = scc(adjls)

    val flattened = sccs.flatMap(_.toList)
    flattened
  }

  /**
   * Gets all the actions in the body of the problem as programs.
   * @return
   */
  def actions: List[Program] = {
    try{
      val Dual(prog) = body
      prog match {
        case ch@Choice(_, _) => recActions(ch)
        case x => List(x)
      }
    }
    catch {
      case e: MatchError =>
        throw new Exception("Could not extract actions from template: " + this + " because of error " + e.getMessage())
    }
  }

  /** Private helper to extract actions. */
  private def recActions(p: Program) : List[Program] = {
    p match {
      case Choice(l, r) => recActions(l) ++ recActions(r)
      case x => List(x)
    }
  }

  /** True if there is no demonic assignment in the body of this template. */
  def noExists : Boolean = {
    val Dual(prog) = body
    prog match {
      case Choice(l, r) => recNoExists(l) && recNoExists(r)
      case Compose(l, r) => recNoExists(l) && recNoExists(r)
      case AssignAny(_) => false
      case _ => true
    }
  }

  /** Private helper to check for demonic assignments. */
  private def recNoExists(p: Program) : Boolean = {
    p match {
      case Choice(l, r) => recNoExists(l) && recNoExists(r)
      case Compose(l, r) => recNoExists(l) && recNoExists(r)
      case AssignAny(_) => false
      case _ => true
    }
  }

  /**
   * Extracts all the demonic control structures from the program.
   */
  def demonicControlSuffixes: List[Program] = {
    val result = extractDemonic(body, dynamics)
    result.map(x => x._2)
  }

  def demonicControlSuffixesUnbounded: List[Program] = {
    val result = extractDemonic(body, unboundedTimeDynamics)
    result.map(x => x._2)
  }

  /**
   * Private helper function to extract all the demonic control structures from a program.
   * Assumes that prog has no nested demonic control inside a demon choice.
   * @param prog Input program.
   * @param suffix Execution suffix of the demonic control structure.
   * @return List of pairs of the demonic control structure and its execution suffix.
   */
  private def extractDemonic(prog: Program, suffix: Program): List[(Program, Program)] = {
    def isChoice (p: Program) : Boolean = {
      p match {
        case Choice(_,_) => true
        case _ => false
      }
    }

    // Recursive helper function.
    def recExtractDemonic(prog: Program, suffix: Program, dual: Boolean): List[(Program, Program)] = {
      prog match {
        case Compose(l, r) => recExtractDemonic(l, Compose(r,suffix), dual) ++ recExtractDemonic(r, suffix, dual)
        case Choice(l, r) =>
          if (!dual) recExtractDemonic(l, suffix, dual) ++ recExtractDemonic(r, suffix, dual)
          else
            {recExtractDemonic(l, suffix, dual)} ++ {recExtractDemonic(r, suffix, dual)} ++
              (if (!isChoice(l)) {(l, Compose(Dual(l), suffix)) :: Nil} else Nil) ++
              (if (!isChoice(r)) {(r, Compose(Dual(r), suffix)) :: Nil} else Nil)
        case AssignAny(_) => if (!dual) Nil else (prog, suffix) :: Nil
        case Dual(p) => recExtractDemonic(p, suffix, !dual)
        case _ => Nil
      }
    }

    recExtractDemonic(prog, suffix, dual = false)
  }
}

// Define implicit conversion.
object Template {

  /**
   * Constructs a program from the input formula.
   *
   * @param f Input formula.
   * @return The template that the formula translates to.
   */
  implicit def fromFormulaToTemplate(f: Formula): Template = {
    try {
      val Imply(init, rhs) = f
      val Box(boxProg, post) = rhs
      val Loop(prog) = boxProg
      val Compose(body, plant) = prog
      val Compose(_, ode) = plant
      val dynamics@ODESystem(_, _) = ode
      Template(init, body, dynamics, post)
    } catch {
      case e: MatchError =>
        throw new Exception("Could not extract a template from formula: " + f + " because of error " + e.getMessage())
    }
  }

  implicit def fromTemplateToFormula(t: Template): Formula = {
    Imply(t.init, Box(Loop(Compose(Compose(t.body, "t:=0;".asProgram), t.dynamics)), t.post))
  }
}

class ODESolvingException(message: String) extends Exception(message) {

  def this(message: String, cause: Throwable) {
    this(message)
    initCause(cause)
  }

  def this(cause: Throwable) {
    this(Option(cause).map(_.toString).orNull, cause)
  }

  def this() {
    this(null: String)
  }
}

/**
 * Wraps QE and simplification, adding logging and oracle lookups.
 * @param tool is an instance of Mathematica.
 * @param qeChunkSize If the expression has more characters than this, we attempt ot break it down before handing over to mathematica for forall QE.
 * @param eggChunkSize If the expression has more characters than this, during simplification we attempt ot break it down before handing over to egg simplify.
 * @param maxSimplify If the expression has more characters than this, try to break down before passing to Mathematica simplification.
 */
class MathTool(tool: Mathematica, orderedVars: List[Variable], debug: Boolean = true, qeChunkSize: Int = 500, eggChunkSize: Int = 1500, maxSimplify: Int = 150000)
{
  var allowSimplify: Boolean = false
  var allowEgg: Boolean = false

  def setAllowSimplify(value: Boolean): Unit = {
    allowSimplify = value
  }

  def setAllowEgg(value: Boolean): Unit = {
    allowEgg = value
  }

  def eggSimplify(expr: Formula, assumptions: Formula, arg: String = "-a"): Formula = {
    val assumptionsString = PostfixPrinter.print(assumptions)
    val exprString = PostfixPrinter.print(expr)

    if(debug) {
      println("Egg question: "+exprString)
      println("Egg assumptions: "+assumptionsString)
    }

    val result = Seq("./simplify", arg, exprString, assumptionsString).!!

    if (debug) {
      print("Egg Simplification: " + result)
    }
    val resultFormula = readFml(result)
    if (debug) {
      println("New formula: " + resultFormula)
    }
    resultFormula
  }

  /** Light simplification to cleanup a formula with 0s before handing to Mathematica. */
  def eggCleanup(expr: Formula, assumptions: Formula): Formula = {
    if (!allowSimplify) {
      return expr
    }
    val assumptionsString = PostfixPrinter.print(assumptions)
    val exprString = PostfixPrinter.print(expr)

    val result = Seq("./simplify", "-l", exprString, assumptionsString).!!

    if (debug) {
      println("Egg Cleanup: " + result)
    }
    val resultFormula = readFml(result)
    resultFormula
  }

  def darbouxPolynomial(ode: DifferentialProgram, constraint: Formula, n: Int): List[Term] = {
    tool.restart()
    tool.darboux(ode, constraint, n)
  }

  def firstIntegrals(expr: DifferentialProgram, constraint: Formula, n: Int): List[Term] = {
    tool.firstIntegral(expr, constraint, n)
  }

  private def getOrderCandidates(): List[List[Variable]] = {
    if (orderedVars.length <= 1) {
      return List(List())
    }
    val maxCandidates = 0 // Because number of cores in my machine is 6.
    val maxLength = 5
    val combinations = orderedVars.combinations(maxLength).toList
    // Choose as many random combinations as maxCandidates.
    val chosenCombinations = Random.shuffle(combinations).take(maxCandidates)
    // Choose random orders.
    var chosenOrders = chosenCombinations.map(Random.shuffle(_))
    // Add dependency order and reverse dependency order.
    chosenOrders = orderedVars::chosenOrders
    chosenOrders = orderedVars.reverse::chosenOrders
    // Prepend the empty list as the first element.
    chosenOrders = List()::chosenOrders
    chosenOrders
  }

  /* Helper to recurse through a formula when it is a conjunction, and throw
  * out any sub-formulas with v. */
  private def recFilterAssumptions(a: Formula, v: Variable): Formula = {
    a match {
      case And(l, r) => And(recFilterAssumptions(l, v), recFilterAssumptions(r, v))
      case _ => if (StaticSemantics.vars(a).contains(v)) True else a
    }
  }

  def resolveForall(v: Variable, c: Formula, p: Formula, a:List[Formula]): Formula = {
    if (debug) {
      println("Calling resolve ForAll.")
      println("Assumptions: "+c)
      println("Predicate:"+p)
    }
    val cSimplified = tool.simplify(c, a)
    // We now come up with multiple variable orders to run in parallel.
    val chosenOrders = getOrderCandidates()
    // Chunk the formulas if larger than chunkSize.
    val res = if (p.prettyString.length > qeChunkSize) {
      val ps = tool.simplify(p, a)
      ps match {
        case And(l, r) => {
          val left = resolveForall(v, cSimplified, l, a)
          val right = resolveForall(v, And(c, left), r, a)
          And(left, right)
        }
        case _ => tool.firstResultForall(v, chosenOrders, cSimplified, p, a)
      }
    }
    else {
      tool.firstResultForall(v, chosenOrders, cSimplified, p, a)
    }
    if (debug) {
      println("Completed: "+res)
    }
    res
  }

  /** Like resolveForall but also throws out any instance of v in the condition c.
   * output: (v-free predicate, v-free assumption) */
  def resolveForallCleanAssumptions(v: Variable, c: Formula, p: Formula): (Formula, Formula) = {
    val assumptions = recFilterAssumptions(c, v)
    val predicate = resolveForall(v,c,p, List(assumptions))
    (predicate, assumptions)
  }

  /** Like resolveExists but also throws out any instance of v in the condition c.
   * output: (v-free predicate, v-free assumption) */
  def resolveExistsCleanAssumptions(v: Variable, c: Formula, p: Formula): (Formula, Formula) = {
    if (debug) {
      println("Calling resolve exists.")
    }
    val predicate =
    // Chunk if too big.
      if (p.prettyString.length > qeChunkSize) {
        val dnf = FormulaTools.disjunctiveNormalForm(p)
        dnf match {
          case Or(l, r) =>
            println("Split an OR during exists.")
            val left = resolveExists(v, c, l)
            val right = resolveExists(v, c, r)
            Or(left, right)
          case _ => resolveExists(v, c, p)
        }
      }
      else {
        resolveExists(v, c, p)
      }

    /* Helper to recurse through a formula when it is a conjunction, and throw
     * out any sub-formulas with v. */
    def recFilterAssumptions(a: Formula, v: Variable): Formula = {
      a match {
        case And(l, r) => And(recFilterAssumptions(l, v), recFilterAssumptions(r, v))
        case _ => if (StaticSemantics.vars(a).contains(v)) True else a
      }
    }

    val assumptions = recFilterAssumptions(c, v)
    (predicate, assumptions)
  }

  def resolveExists(v: Variable, c: Formula, p: Formula): Formula = {
    // Pick random variable orderings an run QE in parallel, accepting
    // first response.
    if (debug) {
      print("Calling resolveExists on variable " + v + ", condition " + c + ", and predicate " + p)
    }
    val chosenOrders = getOrderCandidates()
    val res = tool.firstResultExists(v, chosenOrders, c, p)
    res
  }

  /** Does arithmetic simplification. */
  def simplifyOracle(expr: Formula, assumption: List[Formula]): Formula = {
    if (!allowSimplify) {
      return expr
    }
    if (debug) {
      // Print the name of the calling function.
      val stackTrace = Thread.currentThread.getStackTrace
      val callingFunction = stackTrace(2).getMethodName
      println("Calling simplifyOracle from " + callingFunction)
      println("Expression length: " + expr.prettyString.length)
      println("Simplifying: " + expr.prettyString)
      println("Assumption: " + assumption.map(_.prettyString))
    }

    try {
      // If the expression is larger than the limit, we should recursively
      // simplify subexpressions.
      val resultMathematica = {
        // If any of the assumptions is false, then Mathematica will error.
        if (assumption.contains(False)) {
          True
        }
        else if (expr.prettyString.length > maxSimplify) {
          expr match {
            case And(l, r) => {
              val leftSimplify = simplifyOracle(l, assumption)
              if (leftSimplify == False) {
                return False
              }
              else {
                val rightSimplify = simplifyOracle(r, assumption)
                if (rightSimplify == False) {
                  return False
                }
                else {
                  tool.simplify(And(leftSimplify, rightSimplify), assumption)
                }
              }
            }
            case Or(l, r) => {
              val leftSimplify = simplifyOracle(l, assumption)
              if (leftSimplify == True) {
                return True
              }
              else {
                val rightSimplify = simplifyOracle(r, assumption)
                if (rightSimplify == True) {
                  return True
                }
                else {
                  tool.simplify(Or(leftSimplify, rightSimplify), assumption)
                }
              }
            }
            case Imply(l, r) => {
              val leftSimplify = simplifyOracle(l, assumption)
              if (leftSimplify == False) {
                return True
              }
              else {
                val rightSimplify = simplifyOracle(r, assumption)
                if (rightSimplify == True) {
                  return True
                }
                else {
                  tool.simplify(Imply(leftSimplify, rightSimplify), assumption)
                }
              }
            }
            case Not(f) => Not(simplifyOracle(f, assumption))
            case _ => if (expr.prettyString.length < maxSimplify) {
              tool.simplify(expr, assumption)
            } else expr
          }
        }
        else {
          if (expr.prettyString.length < maxSimplify) {
            tool.simplify(expr, assumption)
          }
          else {
            expr
          }
        }
      }
      if (debug) {
        println("Mathematica result: " + resultMathematica)
      }
      val resultEgg = {
        if (allowEgg && resultMathematica.toString.length <= eggChunkSize) {
          val assumptionsCollected = {
            if (assumption.isEmpty) "true".asFormula else assumption.reduce(And)
          }
          eggSimplify(resultMathematica, assumptionsCollected)
        }
        else
          resultMathematica
      }
      resultEgg
    }
      // If something went wrong, print the exception and return the original expression.
    catch {
      case e: Throwable =>
        println("Exception in simplify: " + e)
        expr
    }
  }


  def replaceAll(e: Term, repls: Map[Term, Term]): Term = {
    e match {
      case Plus(l, r) => Plus(replaceAll(l, repls), replaceAll(r, repls))
      case Minus(l, r) => Minus(replaceAll(l, repls), replaceAll(r, repls))
      case Times(l, r) => Times(replaceAll(l, repls), replaceAll(r, repls))
      case Divide(l, r) => Divide(replaceAll(l, repls), replaceAll(r, repls))
      case Power(l, r) => Power(replaceAll(l, repls), replaceAll(r, repls))
      case Neg(e) => Neg(replaceAll(e, repls))
      case _ => repls.getOrElse(e, e)
    }
  }

  def replaceAll(f: Formula, repls: Map[Term, Term]): Formula = {
    f match {
      case And(l, r) => And(replaceAll(l, repls), replaceAll(r, repls))
      case Or(l, r) => Or(replaceAll(l, repls), replaceAll(r, repls))
      case Imply(l, r) => Imply(replaceAll(l, repls), replaceAll(r, repls))
      case Forall(_, _) => throw new Exception("replaceAll for forall not implemented.") // v is now bound. Otherwise, Forall(v, replaceAll(p, repls))
      case Exists(_, _) => throw new Exception("replaceAll for exists not implemented.") //Exists(v, replaceAll(p, repls))
      case PredOf(_, _) => throw new Exception("replaceAll for predof not implemented.") //PredOf(p, replaceAll(args, repls))
      case PredicationalOf(_, _) => throw new Exception("replaceAll for predof not implemented.") //PredicationalOf(p, replaceAll(args, repls))
      case Not(f) => Not(replaceAll(f, repls))
      case Equal(l, r) => Equal(replaceAll(l, repls), replaceAll(r, repls))
      case NotEqual(l, r) => NotEqual(replaceAll(l, repls), replaceAll(r, repls))
      case Less(l, r) => Less(replaceAll(l, repls), replaceAll(r, repls))
      case LessEqual(l, r) => LessEqual(replaceAll(l, repls), replaceAll(r, repls))
      case Greater(l, r) => Greater(replaceAll(l, repls), replaceAll(r, repls))
      case GreaterEqual(l, r) => GreaterEqual(replaceAll(l, repls), replaceAll(r, repls))
      case False => False
      case True => True
    }
  }
}

/**
 * Class to run CESAR algorithm.
 * @param tool Mathematica tool.
 * @param inputArg The dGl formula for which to do synthesis.
 * @param debug Print debug information.
 * @param eagerSimplify Do aggressive simplification at each iteration.
 * @param n Number of unfoldings.
 * @param orderedVars Use variable ordering in reduce calls.
 * @param allowEgg Enable simplification using egg. Even if false, egg cleanup and rewrite will still run.
 * @param unfoldBased use reduceDl implementation based on unfold, with no simplification.
 */
class Cesar(tool: Mathematica, inputArg: Formula, debug: Boolean = false, eagerSimplify: Boolean = true, n: Int =0,
            orderedVars:Boolean = true, allowEgg: Boolean = true, allowSimplify: Boolean = false,
            enableDeferredQe: Boolean = true, unfoldBased: Boolean = false) {

  def inputFml: Formula = defuncHelper.deFunc(inputArg)

  def t: Variable = "t".asVariable

  def s: Variable = "s".asVariable

  val mathTool = new MathTool(tool, if (orderedVars) {
    inputFml.orderedVarList
  } else {
    List()
  }, debug = debug)

  // By default mathTool does not allow simplification.
  if (allowSimplify) {
    mathTool.setAllowSimplify(allowSimplify)
  }

  if (allowEgg) {
    mathTool.setAllowEgg(allowEgg)
  }

  /** A formula that keeps track of all the fresh variables introduced. */
  var freshVars: Formula = inputFml

  private def freshen(x: Variable): Variable = {
    val fresh = freshNamedSymbol(x, freshVars)
    // Add the fresh variable to the freshVars formula.
    freshVars = And(freshVars, NotEqual(x, fresh))
    fresh
  }

  /**
   * Applies any assigns if possible.
   */
  private def forwardSimplify(p: Program): Program = {
    p match {
      case Compose(l, r) => {
        l match {
          case Assign(x, e) => {
            val newR = SubstitutionHelper.replaceFree(r)(x, e)
            val newRS = forwardSimplify(newR)
            Compose(l, newRS)
          }
          case Dual(Assign(x, e)) => {
            val newR = SubstitutionHelper.replaceFree(r)(x, e)
            val newRS = forwardSimplify(newR)
            Compose(l, newRS)
          }
          case _ => p
        }
      }
      case _ => p
    }
  }

  /**
   * Let ⟨[α]⟩ ∈ {⟨α⟩, [α]}, ▷◁∈ {↔, →}, and A, Q, and P be formulas in quantifier-free real arithmetic. An ODE reduction oracle odereduce is a function such that
   * A → (odereduce(⟨[{x′ = f (x)&Q}]⟩P, A) ▷◁ ⟨[{x′ = f (x)&Q}]⟩P )
   * is valid. When ▷◁ is ↔ then odereduce is exact, otherwise it is approximating.
   */
  def odeReduce(ode: DifferentialProgram, constraint: Formula, l: Formula, a: Formula, reduceT: Boolean): (Formula, Formula) = {
    // Let the map for initial values of variables be an identity map.
    val varList = StaticSemantics.vars(ode).toSet
    val ivMap = varList map (x => (x, freshen(x))) toMap

    var solF: Formula = True
    // Solve the ODE.
    try {
      val sol: Option[Formula] = tool.odeSolve(ode, t, ivMap)
      solF = sol match {
        case Some(s) => {
          if (s.toString.contains("sin") || s.toString.contains("cos")) {
            throw new ODESolvingException("Solution contains trigonometry for ode " + ode.prettyString)
          }
          else {
            s
          }
        }
        case None => throw new ODESolvingException("Failed to solve " + ode.prettyString)
      }
    }
    catch {
      case _: Throwable =>
        // Try first integrals.

        // Get the initial values of the invariant expressions.
        def makeInitialExpr(e: Term, varsToSubst: List[Variable]): Term = {
          val initialVal = varsToSubst.foldRight(e)((x, acc) => SubstitutionHelper.replaceFree(acc)(x, ivMap(x)))
          initialVal
        }

        def processFirstIntegrals(integrals: List[Term]): Formula = {
          // Collect all the vars appearing in the integrals.
          val integralVars = integrals.flatMap(x => StaticSemantics.vars(x).toSet).toSet
          // Collect the LHS vars of the ODE that also appear in the assumption formula.
          val initVarSet = integralVars
            .filter(x => ivMap.contains(x))
            .filter(x => ivMap.contains(DifferentialSymbol(x)))
            .toList
          val assumps = integrals.map(t => Equal(t, makeInitialExpr(t, initVarSet)))
            .reduceOption(And).getOrElse(True)
          // Substitute mappings for these variables in target formula l.
          val target = initVarSet.foldRight(l)((x, acc) => SubstitutionHelper.replaceFree(acc)(x, ivMap(x)))
          val initVarList = initVarSet.map(ivMap(_))
          // Now we try to do QE with the help of these expressions.
          val reduceFml = Forall(initVarList, Imply(assumps, target))
          val result = tool.resolve(reduceFml)
          result
        }

        try {
          mathTool.setAllowSimplify(true)
          mathTool.setAllowEgg(true)
          val firstIntegrals1: List[Term] = mathTool.firstIntegrals(ode, constraint, 1)
          val result = processFirstIntegrals(firstIntegrals1)
          if (result != False) {
            if (debug) {
              println("Got result from first integrals 1: " + firstIntegrals1)
              println("Result: " + result)
            }
            return (result, True)
          }
          val firstIntegrals2: List[Term] = mathTool.firstIntegrals(ode, constraint, 2)
          val result2 = processFirstIntegrals(firstIntegrals2)
          if (result2 != False) {
            if (debug) {
              println("Got result from first integrals 2: " + firstIntegrals2)
              println("Result: " + result2)
            }
            return (result2, True)
          }
        }
        catch {
          case _: Throwable =>

            // Try Darboux polynomials.

            def filterDbx(dbxPolynomials: List[Term]): (List[Term], List[Variable]) = {
              val variableList = StaticSemantics.vars(ode).toSet
                // x should not be a DifferentialSymbol already.
                .filter(!_.isInstanceOf[DifferentialSymbol])
                .filter(x => ivMap.contains(DifferentialSymbol(x)))
              val filteredDbx = dbxPolynomials.filter(trm => variableList.exists(
                x => StaticSemantics.vars(trm).contains(x)))
              (filteredDbx, variableList.toList)
            }

            def processDbx(dbxPolynomials: List[Term], varList: List[Variable]): (Formula, Formula) = {
              // Keep only the polynomials that include variables, not just constants.
              val invs = dbxPolynomials.map(trm => GreaterEqual(trm, Number(0)))
                .reduceOption(And).getOrElse(True)
              val fml = Forall(varList, Imply(invs, l))
              val result3 = tool.resolve(fml)
              (result3, invs)
            }

            val dbxPolynomials: List[Term] = mathTool.darbouxPolynomial(ode, constraint, 1)
            val (filteredDbx, varList2) = filterDbx(dbxPolynomials)
            val (result3, invs) = processDbx(filteredDbx, varList2)
            if (result3 != False) {
              if (debug) {
                println("Got result from Darboux polynomials: " + filteredDbx)
                println("Result: " + result3)
              }
              return (And(result3, invs), True)
            }

            throw new ODESolvingException("Failed to solve " + ode.prettyString)
        }
    }

    // Substitute back the initial values.
    val ivSubst = ivMap.foldRight(solF)((x, acc) => SubstitutionHelper.replaceFree(acc)(x._2, x._1))

    // Extract solutions as substitution pairs.
    val solFormulas : List[Formula]  = {
      FormulaTools.conjuncts(ivSubst)
    }
    val substPairs = solFormulas.map {
      case Equal(l, r) => (l, r)
      case x => throw new TemplateMismatchException("Expected equality but got " + x.prettyString)
    }
    // The domain constraints with t substituted in.
    val constraintsSubst = substPairs.foldRight(constraint)((x, acc) => SubstitutionHelper.replaceFree(acc)(x._1, x._2))

    // Put the non quantified assumptions together.
    val extraAssumptions = And(inputFml.init, "t>=0".asFormula)

    val premise = And(And("0<=s".asFormula, "s<=t".asFormula),extraAssumptions)
    // The domain constraints as a forall s ... statement.
    val forallSCond = mathTool.resolveForall(s, premise,
      SubstitutionHelper.replaceFree(constraintsSubst)(t, s), List(inputFml.init))

    // Debugging the resolveForAll.
    if (debug) {
      println("Forall s premise: " + premise.prettyString)
      println("Forall s predicate: " + SubstitutionHelper.replaceFree(constraintsSubst)(t, s).prettyString)
      println("Forall s result: " + forallSCond.prettyString)
    }

    // Substitute the solution into the goal formula.
    val repls = substPairs.map(x => (x._1, x._2)).toMap
    val unsimplifiedFml = mathTool.replaceAll(l, repls)

    val unsimplfiedAssumps = And(forallSCond, extraAssumptions)
    val simplifiedAssumps = mathTool.simplifyOracle(unsimplfiedAssumps, List())

    val simplifiedFml = mathTool.simplifyOracle(unsimplifiedFml, List(simplifiedAssumps))

    if (debug) {
      println("Pre-QE formula: " + simplifiedFml.prettyString)
      println("Simplified assumptions: " + simplifiedAssumps.prettyString)
    }

    // If we want to eliminate t.
    if (reduceT) {
      val (simplifiedSol, cleanedAssumps) = mathTool.resolveForallCleanAssumptions(
        t, simplifiedAssumps, simplifiedFml)
      if (debug) {
        println("Resolved formula: " + simplifiedSol.prettyString)
        println("Cleaned assumptions: " + cleanedAssumps.prettyString)
      }

      (simplifiedSol, cleanedAssumps)
    }
    // If we don't want to eliminate t.
    else {
      (simplifiedFml, simplifiedAssumps)
    }
  }

  /** Function reduce takes as an input a loop-free dGL formula F and an assumption A that is a formula.
   * It returns a propositional formula R such that the formula A→(R→F) is valid.
   * If flag dual is true then any appearing dGl should be treated as its dual problem. */
  private def reduceDL(f: Formula, a:Formula, dual:Boolean, reduceT:Boolean): (Formula, Formula) = {

    val (reducedF, reducedA) = f match {
      // Atomic formulas.
      case True | False | Equal(_,_) | NotEqual(_,_) | GreaterEqual(_,_) | Greater(_,_) | LessEqual(_,_) | Less(_,_)
           | PredOf(_,_) | PredicationalOf(_,_) | UnitPredicational(_,_) => (f,a)
      // FOL operators.
      case And(l, r) =>
        val (lReduce, la) = reduceDL(l, a, dual, reduceT)
        val (rReduce, ra) = reduceDL(r, a, dual, reduceT)
        (And(lReduce, rReduce), Or(la, ra))
      case Or(l, r) =>
        val (lReduce, la) = reduceDL(l, a, dual, reduceT)
        val (rReduce, ra) = reduceDL(r, a, dual, reduceT)
        (Or(lReduce, rReduce), Or(la, ra))
      case Imply(l, r) =>
        val (lReduce, la) = reduceDL(l, a, dual, reduceT)
        val (rReduce, ra) = reduceDL(r, a, dual, reduceT)
        (rReduce, And(Or(la, ra), lReduce))
      case Not(l) =>
        val (notF, notA) = reduceDL(l, a, dual, reduceT)
        (Not(notF), notA)
      case Forall(x, l) =>
        val (forallF, forallA) = reduceDL(l, a, dual, reduceT)
        (Forall(x, forallF), forallA)
      case Exists(x, l) =>
        val (existsF, existsA) = reduceDL(l, a, dual, reduceT)
        (Exists(x, existsF), existsA)
      // Modalities.
      case Box(p, l) =>
        p match {
          case Assign(x, e) =>
            val (newF, newA) = (SubstitutionHelper.replaceFree(l)(x, e),
              SubstitutionHelper.replaceFree(a)(x, e))
            // Egg pass cleans up things like x<x.
            (mathTool.eggCleanup(newF, newA), mathTool.eggCleanup(newA, True))
          case AssignAny(x) =>
            if (dual) {
              // If controller assignment, the new target is that there exists a value for x such that the old target is true.
              val (newL, newA) = mathTool.resolveExistsCleanAssumptions(x, a, l)
              (newL, newA)
            }
            else {
              // If plant assignment, the new target is that for all values of x, the old target is true.
              val (newL, newA) = mathTool.resolveForallCleanAssumptions(x, a, l)
              (newL, newA)
            }
          case Test(f) =>
            (Imply(f, l), And(f, a))
          case Compose(alpha, beta) =>
            // Forward propagation.
            // Currently assumes that assumptions a won't change.
            val (bFormula, bAssumption) = reduceDL(Box(beta, l), a, dual, reduceT)
            val newBox = Box(alpha, bFormula)
            val (alphaFormula, alphaAssumption) = reduceDL(newBox, And(a, bAssumption), dual, reduceT)
            (alphaFormula, alphaAssumption)
          case Choice(alpha, beta) =>
            val (alphaFormula, alphaAssumption) = reduceDL(Box(alpha, l), a, dual, reduceT)
            val (betaFormula, betaAssumption) = reduceDL(Box(beta, l), a, dual, reduceT)
            if (!dual)
              (And(alphaFormula, betaFormula), Or(alphaAssumption, betaAssumption))
            else
              (Or(alphaFormula, betaFormula), Or(alphaAssumption, betaAssumption))
          case Dual(inner) => reduceDL(Box(inner, l), a, !dual, reduceT)
          case ODESystem(ode, constraint) =>
            odeReduce(ode, constraint, l, a, reduceT)
          case _ => throw new TemplateMismatchException("Reduce of "+f.prettyString+" not yet handled.")
        }
      case Diamond(p, l) =>
        val (pFormula, pAssumption) = reduceDL(Box(p, l), a, !dual, reduceT)
        (pFormula, And(pAssumption, l))
      case _ => throw new TemplateMismatchException("Reduce of "+f.prettyString+" not yet handled.")
    }

    // Debugging: print output.
    if (debug) {
      println("Input formula: "+f.prettyString)
      println("Reduced formula: "+reducedF.prettyString)
      println("Reduced assumption: "+reducedA.prettyString)
    }

    // Eagerly simplify the reduced formula.
    if (eagerSimplify) {
      val simplifiedA = mathTool.simplifyOracle(And(reducedA, inputFml.init), Nil)
      if (debug) {
        println("Simplified assumption: " + simplifiedA.prettyString)
      }
      val simplifiedF = mathTool.simplifyOracle(reducedF, List(simplifiedA))
      if (debug) {
        println("Simplified formula: " + simplifiedF.prettyString)
      }
      (simplifiedF, simplifiedA)
    }
    else {
      // No eager simplification.
      (reducedF, reducedA)
    }
  }

  /**
   * Uses the CEASAR algorithm to synthesize the loop invariant formula.
   */
  private def getInvariant(input: Template): Formula = {

    def zeroStep(condition: Formula): Formula =
      Box(Compose(input.body, input.unboundedTimeDynamics), condition)

    // Optimization: If there is no existential, execute the all extions before doing QE.
    val zeroShot = if (inputFml.noExists && enableDeferredQe) {
      if (debug) {
        println("No exists. Doing deferred QE optimization while computing I0.")
      }
      // Get actions.
      val actions = inputFml.demonicControlSuffixesUnbounded.map(forwardSimplify)
      // Symbolic execution over body.
      val dlFmls = actions.map(p => Box(p, inputFml.post))
      val fmls = dlFmls.map(p => reduceDL(p, inputFml.init, dual = false, reduceT = false))
      val resolvedFmls = fmls.map(f => mathTool.resolveForall(t, And(inputFml.init, f._2), f._1, List(inputFml.init)))
      val disj = resolvedFmls.reduce(Or)
      mathTool.simplifyOracle(disj, List(inputFml.init))
    } else {
      reduceDL(zeroStep(input.post), input.init, dual=false, reduceT=true)._1
    }
    // Do QE and simplification
    // val zeroShotResult = mathTool.simplifyOracle(zeroShot._1, input.init::Nil)
    val zeroShotResult = zeroShot

    if (debug) {
      println("Zero shot invariant: "+zeroShotResult)
    }
    var i = n
    var iPrev = mathTool.simplifyOracle(And(zeroShotResult, input.post), List(input.init))
    while (i>0) {
      i = i - 1

      // ODE reduce works differently during unrolling:

      // Backward execute iPrev over the ODE without eliminating t.
      val reachesProg = reduceDL(Box(input.unboundedTimeDynamics, iPrev), input.init, dual = false, reduceT = false)
      val reachesAssumps = And("s>=0 & s<=t & t<=s+T".asFormula, And(inputFml.init, reachesProg._2))

      // Backward execute safety contract over the ODE without eliminating t.
      val safeProg = reduceDL(Box(input.unboundedTimeDynamics, input.post), input.init, dual = false, reduceT = false)
      val safeAssumps = And(And(safeProg._2, "0<=t & t<=s+T".asFormula), inputFml.init)

      val newInv: Formula = {
        // Optimization: if there is no instance of an existential, then we can defer doing one-shot QE till after executing actions.
        if (inputFml.noExists && enableDeferredQe) {
          if (debug) {
            println("No exists. Doing deferred QE optimization.")
          }
          // Get actions.
          val actions = inputFml.actions
          // Symbolic execution over body.
          val reachProgs = actions.map(a => Box(a, reachesProg._1))
          val safeProgs = actions.map(a => Box(a, safeProg._1))
          val reachFmls = reachProgs.map(p => reduceDL(p, reachesAssumps, dual = true, reduceT = true)._1)
          val safeFmls = safeProgs.map(p => reduceDL(p, safeAssumps, dual = true, reduceT = true)._1)

          val resolvedReachFmls = reachFmls.map(f => mathTool.resolveForall(t, And(inputFml.init, "s>=0 & s<=t & t<=s+T".asFormula), f, List(inputFml.init)))
          val resolvedSafeFmls = safeFmls.map(f => mathTool.resolveForall(t, And(inputFml.init, "0<=t & t<=s+T".asFormula), f, List(inputFml.init)))

          val reachAndSafe = resolvedReachFmls.zip(resolvedSafeFmls).map(p => And(p._1, p._2))
          val resolvedExists = reachAndSafe.map(f => mathTool.resolveExists(s, And(inputFml.init, "s>=0".asFormula), f))

          val disj = resolvedExists.reduce(Or)
          mathTool.simplifyOracle(disj, List(inputFml.init))
        }
        else {
          if (debug) {
            println("Demonic assignment present. Not doing deferred QE optimization.")
          }

          // Compute the region that reaches iPrev in s<=t<=s+T.
          val reachesPrevious = mathTool.resolveForall(t, reachesAssumps, reachesProg._1, List(inputFml.init))
          val sReachesPrevious = mathTool.simplifyOracle(reachesPrevious, List(inputFml.init))
          if (debug) {
            println("Reaches previous: " + sReachesPrevious.prettyString)
          }

          // Compute the region that is safe for all 0<=t<=s+T.
          val safe = mathTool.resolveForall(t, And(inputFml.init, safeAssumps), safeProg._1, List(inputFml.init))
          val sSafe = mathTool.simplifyOracle(safe, List(inputFml.init))
          if (debug) {
            println("Safe: " + sSafe.prettyString)
          }

          val simplifiedConjunction = mathTool.simplifyOracle(And(sReachesPrevious, sSafe), List(input.init))

          // Defer eliminating existential till after executing rest of the program
          // Symbolic execution over body.
          val remainingProg = Box(inputFml.body, simplifiedConjunction)
          val afterProg = reduceDL(remainingProg, And(inputFml.init, "s>=0".asFormula), dual = false, reduceT = true)._1

          // Eliminate s for safe and reaches previous.
          val existsS = mathTool.resolveExists(s, And("s>=0".asFormula, inputFml.init), afterProg)
          mathTool.simplifyOracle(existsS, List(input.init))
        }
      }

      // Debugging.
      if (debug) {
        println("i-shot result: " + newInv.prettyString)
      }
      iPrev = {
        if (inputFml.noExists && enableDeferredQe) {
          newInv
        } else {
          mathTool.simplifyOracle(And(Or(newInv, iPrev), input.post), List(inputFml.init))
        }
      }

      if (debug) {
        println("New invariant: " + iPrev)
      }
    }

    iPrev
  }

  /**
   * Uses the CEASAR algorithm to synthesize the guards for each action.
   */
  private def getActionGuards(input: Template, inv: Formula): List[Formula] = {
    // Extract from the body of the program, all the demonic control structures
    // requiring synthesis.

    val actions = input.demonicControlSuffixes.map(forwardSimplify)

    // We only need to and with the original post condition if there is an existential.
    val simplifiedTarget = {
      if (inputFml.noExists && enableDeferredQe) {
        inv
      }
      else {
        mathTool.simplifyOracle(And(inv, input.post), List(input.init))
      }
    }

    // Cycle through the demonic choice structures and construct the predicate that they should imply.
    val actionProgs = actions.map{Box(_, simplifiedTarget)}

    // Deferred QE optimization if there is no existential.
    val guards = {
      if (inputFml.noExists && enableDeferredQe) {
        val reducedFmls = actionProgs.map(p => reduceDL(p, input.init, dual=false, reduceT=false))
        val resolvedFmls = reducedFmls.map(f =>
          mathTool.resolveForall(t, And(inputFml.init, f._2), f._1, List(inputFml.init)))
        resolvedFmls
      }
      else {
        actionProgs.map(p => reduceDL(p, input.init, dual=false, reduceT=true))
          .map(_._1)
      }
    }

    if (debug) {
      println("Guards after t eliminated: " + guards.map(_.prettyString))
    }

    // Simplify the guards wrt the invariant.
    if(debug) {
      println("inv: "+inv)
    }

    // Current simplification only works if guard is first structure after the invariant.
    guards.map(g => mathTool.simplifyOracle(g, List(inv, inputFml.init)))
  }

  def synthesize : List[Formula] = {
    val template: Template = inputFml

    var invariant = getInvariant(template)

    // Debugging info.
    if (debug) {
      println("Found Invariant: " + invariant.prettyString)
    }

    var guards = getActionGuards(template, invariant)

    // Here, as we have reached the end,
    // we will override allowSimplify and set it to true for a final simplification. TODO
    if (!allowSimplify || !allowEgg) {
      mathTool.setAllowSimplify(true)
      mathTool.setAllowEgg(true)
      invariant = mathTool.simplifyOracle(invariant, List(template.init))
      guards = guards.map(g => mathTool.simplifyOracle(g, List(invariant,template.init)))
    }
    invariant :: guards
  }

  /** Returns the result of synthesis as a formula with the holes filler in and a tactic. */
  def resultFormula : (Formula, BelleExpr) = {
    val result = synthesize
    val inv = result.head
    val guards = result.tail
    // Collect the solution.
    val assumptions = And(inputFml.init, inv)
    val guardedActions : List[Program] = inputFml.actions.zip(guards)
      .map(elem => Compose( Test(elem._2), elem._1))
    val actionChoice = guardedActions.reduce(Choice)
    val envProg = Compose("t:=0;".asProgram, inputFml.dynamics)
    val envelopeBox = Box( Loop(Compose(actionChoice, envProg)), inputFml.post)
    val newProg = Imply(assumptions, envelopeBox)
    // Collect the tactic.
    val tactic = unfoldProgramNormalize & loop(And(inv, inputFml.init))(1)<(
      autoClose,
      autoClose,
      autoClose)
    (newProg, tactic)
  }
}
