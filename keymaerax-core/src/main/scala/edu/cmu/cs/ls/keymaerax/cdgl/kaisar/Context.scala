/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/** A context is used during proof-checking and elaboration or transformation passes in order to track assumptions.
  * In Kaisar, contexts also track changes to program variables, line labels, and local definitions of function symbols.
  * Because Kaisar contexts must entirely remember the structure of a proof, we reuse the proof data structure as a
  * context.
  *
  * In practice, contexts differ thusly from a "usual" proof object:
  * 1) During proof-checking, assertions and lemmas in a context have already been proven, so their proofs need not
  *  be re-executed.
  * 2) During elaboration or proof-checking, optional annotations may be automatically filled in for a context.
  *    For example, the result of a [[Note]] lemma is inferred in the [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofChecker]]
  * 3) Contexts may introduce meta nodes which do not exist in proofs, but are helpful for proof checking.
  *   For example [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.BoxLoopProgress]] remembers the entirety of a loop while its
  *   body is being processed.
  *
  * @author Brandon Bohrer
  * @see [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof]]
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import KaisarProof._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context.Finder
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{SubstitutionHelper, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

case class Context(s: Statement) {
  /** Add s to the "end" of the context. */
  def :+(other: Statement): Context = {
    s match {
      case _: Triv  => Context(other)
      /* We are processing "pr" and simply remembering the loop "bl" while we do so.
       * the newly-processed "s" should be part of "pr". */
      case BoxLoopProgress(bl, pr) => Context(BoxLoopProgress(bl, Context(pr).:+(other).s))
      case Block(ss) =>
        // recursively handle boxloopprogress inside of sequence
        val (rest, last) = (ss.dropRight(1), Context(ss.last).:+(other).s)
        Context(KaisarProof.block(rest :+ last))
      case sl => Context(Block(List(sl, other)))
    }
  }

  /** Add an assumption to the context */
  def add(x: Ident, fml: Formula): Context = {
    :+(Assume(x, fml))
  }

  /** The set of function symbols defined in a statement. This includes proofs which are defined under a branch or under
    * a binder. */
  def signature: Set[Function] = {
    s match {
      case lf: LetFun => Set(lf.asFunction)
      case Block(ss) => ss.flatMap(s => Context(s).signature).toSet
      case BoxChoice(l, r) => Context(l).signature ++ Context(r).signature
      case Switch(sel, pats) => pats.map(_._3).flatMap(Context(_).signature).toSet
      case Ghost(s) => Context(s).signature
      case Was(now, was) => Context(now).signature
      case While(_, _, body) => Context(body).signature
      case BoxLoop(body, _) => Context(body).signature
      case _: Triv | _: Assume | _: Assert | _: Note | _: PrintGoal | _: InverseGhost | _: ProveODE | _: Modify
           | _: Label | _: Match => Set()
    }
  }

  /** Return all assignments which mention any variant of "x" */
  /* @TODO (soundness): The soundness of this function is questionable. It *may* be sound for SSA, but certainly not
  *    for arbitrary contexts. */
  def getAssignments(x: Variable): List[Formula] =
    searchAll(
      {case (v@BaseVariable(xx, idx, _), Equal(BaseVariable(xxx, idxx,_), f), true) if x.name == xx && xx == xxx && idx == idxx => true
      // @TODO: Indices get renamed here, but is that correct?
      case (v@BaseVariable(xx, idx, _), Equal(BaseVariable(xxx, idxx,_), f), true) if x.name == xx && xx == xxx => true
       case _ => false
      }, isGhost = false).map(_._2)

  /** Look up definitions of a proof variable, starting with the most recent. */
  /** @TODO: Soundness: Is this sound for SSA? What happens when a free variable of a fact is modified after the fact is proved? */
  def searchAll(f: Finder, isGhost: Boolean): List[(Ident, Formula)] = {
    s match {
      case _: Triv => Nil
      case Assume(x, g) => Context.matchAssume(x, g).filter({ case (x, y) => f(x, y, false) }).toList
      case Assert(x, g, _) => Context.matchAssume(x, g).filter({ case (x, y) => f(x, y, false) }).toList
      case Note(x, _, Some(g)) => if (f(x, g, false)) List((x, g)) else Nil
      // While unannotated Note's are allowed in contexts (for transformation passes), they cannot be looked up.
      case Note(x, _, None) => throw ProofCheckException("Note in context needs formula annotation")
      case mod: Modify => Context.findAll(mod, f, isGhost)
      case Block(ss) =>
        def iter(ss: List[Statement], f: Finder): List[(Ident, Formula)] = {
          ss match {
            case Nil => Nil
            case (s: Phi) :: ss =>
              val left =
                Context(s.asgns).searchAll(f, isGhost).filter({case (yx, yf) =>
                  val surrounding = Block(ss.reverse)
                  val t = VariableSets(surrounding)
                  val inter = t.tabooVars.intersect(StaticSemantics(yf).fv.toSet)
                  inter.isEmpty})
              val ff: Finder = ({
                case ((x: Ident, fml: Formula, b: Boolean)) => f(x, Context.substPhi(s, fml), b)
              })
              left ++ iter(ss, ff)
            case s :: ss =>
              val left =
                Context(s).searchAll(f, isGhost) match {
                  case ((yx, yf)) :: _ =>
                    val surrounding = Block(ss.reverse)
                    val t = VariableSets(surrounding)
                    val inter = t.tabooVars.intersect(StaticSemantics(yf).fv.toSet)
                    if (inter.nonEmpty) {
                      throw ProofCheckException(s"Fact $yx inaccessible because ghost variable(s) $inter would escape their scope")
                    }
                    List((yx, yf))
                  case Nil => Nil
                }
              left ++ iter(ss, f)
          }
        }
        iter(ss.reverse, f)
      case BoxChoice(l, r) => Context(l).searchAll(f, isGhost) ++ Context(r).searchAll(f, isGhost)
      // @TODO: Revisit and test this.
      case Switch(sel, pats) =>
        val or: ((Ident, Formula), (Ident, Formula)) => (Ident, Formula) = {
          case ((k1, v1), (k2, v2)) =>
            if (k1 != k2) throw ProofCheckException("recursive call found formula twice with different names")
            else (k1, Or(v1, v2))
        }
        val fmls = pats.flatMap({ case (v, e, s) => Context(s).searchAll(f, isGhost) })
        if (fmls.isEmpty) Nil
        else List(fmls.reduceRight(or))
      case Ghost(s) => Context(s).searchAll(f, isGhost = true)
      // While phi nodes are "ghost" in the sense that they do not appear in the source program, we should allow ProgramVar() selectors
      // to select the equalities introduced by phi nodes.
      case Phi(s) => Context(s).searchAll(f, isGhost = false)
      /* @TODO: Somewhere add a user-friendly message like s"Formula $f should not be selected from statement $s which is an inverse ghost" */
      case InverseGhost(s) => Nil
      case po: ProveODE => Context.findAll(po.dc, f)
      case Was(now, was) => Context(was).searchAll(f, isGhost)
      case _: Label | _: LetFun | _: Match | _: PrintGoal => Nil
      case While(_, _, body) => Context(body).searchAll(f, isGhost)
      case BoxLoop(body, ih) =>
        val matchHere = ih match {case Some((ihVar, ihFml)) if f(ihVar, ihFml, false) => List((ihVar, ihFml)) case _ => Nil}
        matchHere ++ Context(body).searchAll(f, isGhost)
      case BoxLoopProgress(BoxLoop(bl, Some((ihVar, ihFml))), progress) =>
        val ihMatch = if(f(ihVar, ihFml, false)) List((ihVar, ihFml)) else List()
        ihMatch ++ Context(progress).searchAll(f, isGhost)
    }
  }

  // top-level search function wrapper.
  // @TODO: Change lots of functions to be Context methods, get rid of Context.Context
  private def findAll(f: Finder): List[(Ident, Formula)] = {
    searchAll(f, isGhost = false)
  }

  /* Get most recent formula (if any), bound to identifier [[id]]
  * @param wantProgramVar search exclusively for unannotated assignments x:=f rather than facts named "x" */
  def get(id: Ident, wantProgramVar: Boolean = false): Option[Formula] = {
    // gotProgramVar is true only for unannotated assignment statements.
    val f: ((Ident, Formula, Boolean)) => Boolean = {
      case (x: Ident, v: Formula, gotProgramVar) =>
        if (wantProgramVar && gotProgramVar) {
          val Equal(y, f) = v
          id == y
        } else if (wantProgramVar) {
          false
        } else {
          id == x && !gotProgramVar
        }
    }
    searchAll(f, isGhost = false).map(_._2).headOption
  }
  def getHere(id: Ident, wantProgramVar: Boolean = false): Option[Formula] = get(id, wantProgramVar).map(elaborate)

    /** Used in proof statements with implicit assumptions, such as BoxLoop which implicitly finds a base case.
    * @return Most recent fact of context and context of phi assignments since the fact was bound */
  private def lastFactMobile: (Option[(Ident, Formula)], List[Phi]) = {
    s match {
      case Assume(x: Variable, f) => (Some((x, f)), Nil)
      case Assert(x: Variable, f, _) => (Some((x,f)), Nil)
      case Note(x: Variable, pt, opt) => (opt.map((x, _)), Nil)
      case Modify(VarPat(x, Some(p)), Left(f)) => (Some((p, Equal(x, f))), Nil)
      case Modify(VarPat(x, _), Left(f)) => (Some((x, Equal(x, f))), Nil)
      case BoxChoice(l, r) =>
        (Context(l).lastFactMobile, Context(r).lastFactMobile) match {
          case ((Some(resL), Nil), (Some(resR), Nil)) if resL == resR => (Some(resL), Nil)
          case ((Some(resL), _), (Some(resR), _)) => throw new ProofCheckException("Loop inductive statement cannot appear under box choice ++")
          case _ => (None, Nil)
        }
      case BoxLoop(body, _) => Context(body).lastFactMobile
      case While(_, _, body) => Context(body).lastFactMobile
      // Note: After SSA, last statement is phi node, so keep looking to find "real" node
      case Block(ss) =>
        // @TODO: Need a more general way to handle phi assignments
        ss.reverse match {
          case (phi: Phi) :: rest =>
            val (fact, phis) = rest.map(Context(_).lastFactMobile).filter(_._1.isDefined).head
            (fact, phi :: phis)
          case ss =>
            ss.map(Context(_).lastFactMobile).filter(_._1.isDefined).head
        }
      case Was(now, was) => Context(now).lastFactMobile
      case Ghost(s) => Context(s).lastFactMobile
      // Skips all meta nodes and inverse ghosts, for example
      case _ => (None, Nil)
    }
  }

  private def destabilize(f: Formula): Formula =
    SubstitutionHelper.replacesFree(f)(f => KaisarProof.getStable(f))

  def elaborate(f: Formula): Formula = destabilize(f)

  def lastFact: Option[(Ident, Formula)] = {
    val (fml, phis) = lastFactMobile
    val mapped = fml.map({case ((k,fact)) => (k, phis.foldLeft(fact)((fml, phi) => Context.substPhi(phi, fml)))})
    val res =  mapped.map({case (k, v) => (k, destabilize(v))})
    res
  }

  /** Does the context contain a fact named [[id]]? */
  def contains(id: Ident): Boolean = get(id).isDefined

  /** return all facts that unify with a given pattern */
  def unifyAll(pat: Expression): List[(Ident, Formula)] = {
    val f: ((Ident, Formula, Boolean)) => Boolean = {case (x: Ident, fml: Formula, false) =>
      try {
        UnificationMatch(pat, fml)
        true
      } catch {
        case _: ProverException => false
      }
    case _ => false}
    searchAll(f, isGhost = false)
  }
  /** Return first fact that unifies with a pattern, if any. */
  def unify(pat: Expression): Option[(Ident, Formula)] = unifyAll(pat).headOption

  // Base name used for fresh variables generated during proof when no better variable name is available.
  private val ghostVar: String = "ghost"

  /** @return A proof variable name which is not bound in the context. */
  def fresh(ident: String = ghostVar): Ident = {
    var i = 0
    while(contains(Variable(ident + i))) {
      i = i + 1
    }
    Variable(ident + i)
  }

  /**  Bind the next ghost variable to formula f */
  def ghost(f: Formula): Context = add(fresh(), f)
}

object Context {
  // Type of user-supplied predicates used to search the context.
  // fact identifier, fact formula, whether fact is from an assignment
  type Finder = ((Ident, Formula, Boolean)) => Boolean
  def empty: Context = Context(Triv())

  /** Do the head constructors of two expressions match? */
  private def sameHead(e: Expression, f: Expression): Boolean = {
    (e, f) match {
      case (bcf1: BinaryCompositeFormula, bcf2: BinaryCompositeFormula) =>
        bcf1.reapply(bcf2.left, bcf2.right) == bcf2
      case (ucf1: UnaryCompositeFormula, ucf2: UnaryCompositeFormula) =>
        ucf1.reapply(ucf2.child) == ucf2
      // No matching in quantified vars or program, so reapply to q1/m1
      case (q1: Quantified, q2: Quantified) => q1.reapply(q1.vars, q2.child) == q2
      case (m1: Modal, m2: Modal) => m1.reapply(m1.program, m2.child) == m2
    }
  }

  /** @param e the left-hand side of an assumption statement, which is a pattern that binds fact variables
    * @param f the right-hand side of an assumption statement, which is a formula expression
    * @return the set of fact bindings introduced by an assumption statement */
  private def matchAssume(e: Expression, f: Formula): Map[Ident, Formula] = {
    e match {
      case BaseVariable(x, _, _) => Map(Variable(x) -> f)
      case _ =>
        if (!sameHead(e, f))
          throw ProofCheckException(s"Pattern $e does not match formula $f")
        (e, f) match {
          case (bcf1: BinaryCompositeFormula, bcf2: BinaryCompositeFormula) =>
            matchAssume(bcf1.left, bcf2.left) ++ matchAssume(bcf1.right, bcf2.right)
          case (ucf1: BinaryCompositeFormula, ucf2: BinaryCompositeFormula) =>
            matchAssume(ucf1.left, ucf2.left)
          case (q1: Quantified, q2: Quantified) => matchAssume(q1.child, q2.child)
          case (m1: Modal, m2: Modal) =>matchAssume(m1.child, m2.child)
        }
    }
  }

  /** Find all fact bindings which satisfy [[finder]] in statement [[mod]]
    * @param mod  A [[Modify]] statement which is searched for bindings
    * @param finder A user-supplied search predicate
    * @param isGhost Does [[mod]] appear under a [[Ghost]] constructor in its surrounding context?
    * @return all bindings which satisfy [[finder]], starting with the most recent binding (i.e. variable's current value) */
  private def findAll(mod: Modify, finder: Finder, isGhost: Boolean): List[(Ident, Formula)] = {
    mod match {
      case Modify(TuplePat(pat :: pats), Left(Pair(l, r))) =>
        val left = findAll(Modify(pat, Left(l)), finder, isGhost)
        val right = findAll(Modify(TuplePat(pats), Left(r)), finder, isGhost)
        left ++ right
      /* Deterministic assignment that was annotated with a proof variable name for the introduced equality */
      case Modify(VarPat(x, Some(p)), Left(f)) if(finder(p, Equal(x, f), false)) =>
        // Note: Okay to return x=f here because admissibilty of x:=f is ensured in SSA and checked in ProofChecker.
        List((p, Equal(x, f)))
      /* Deterministic assignment which was never annotated with a proof variable name to remember the introduced equality */
      case Modify(VarPat(x, None), Left(f)) if(finder(x, Equal(x, f), true)) =>
        /* @TODO (usability): If another recursive call finds a match for "finder", return that other match. But if *no*
             branch succeeds, somebody, somewhere should give the user an error message like
             "Ghost variable $x inaccessible because it would escape its scope" */
        if (isGhost) {
          List()
        } else
          List((x, Equal(x, f)))
      case Modify(VarPat(x, Some(_)), Right(())) =>
        throw ProofCheckException("Nondeterministic assignment pattern should not bind proof variable")
      case Modify(_, _) => List()
    }
  }

  /** Find all fact bindings which satisfy [[finder]] in statement [[dc]]
    * @param dc  A [[DomainStatement]] statement which is searched for bindings
    * @param f A user-supplied search predicate
    * @return all bindings which satisfy [[finder]] */
  /* @TODO: Does this need an "isGhost" argument */
  private def findAll(dc: DomainStatement, f: Finder): List[(Ident, Formula)] = {
    dc match {
      case DomAssume(x, fml) => matchAssume(x, fml).filter({case (x,y) => f(x, y, false)}).toList//collectFirst({case (mx, mf) if mx == id => mf})
      case DomAssert(x, fml, _ ) => matchAssume(x, fml).filter({case (x,y) => f(x, y, false)}).toList//collectFirst({case (mx, mf) if mx == id => mf})
      case DomAnd(l, r) => findAll(l, f) ++ findAll(r, f)
      case DomWeak(dc) =>
        findAll(dc, f) match {
          case fml :: _ => throw ProofCheckException(s"Weakened domain constraint $dc binds formula $fml, should not be selected")
          case Nil => Nil
        }
      case DomModify(ap, term) => Context(Modify(ap, Left(term))).findAll(f)
    }
  }

  // Rename formula according to assignment from an SSA Phi node
  private def substPhi(phi: Phi, fml: Formula): Formula = {
    val mapping = phi.reverseMap
    SubstitutionHelper.replacesFree(fml)(term => {
      (KaisarProof.getStable(term), term) match {
        case (Some(_), _) => Some(term)
        case (None, v: Variable) => mapping.get(v)
        case (None, _) => None
      }})
  }
}