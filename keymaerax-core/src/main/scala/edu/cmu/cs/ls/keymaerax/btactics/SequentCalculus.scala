/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.macros.Tactic
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig


/**
  * Sequent Calculus for propositional and first-order logic.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see [[SequentCalculus]]
  */
object SequentCalculus extends SequentCalculus

/**
  * Sequent Calculus for propositional and first-order logic.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-008-9103-8 Differential dynamic logic for hybrid systems]]. Journal of Automated Reasoning, 41(2), pages 143-189, 2008.
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
  * @see [[edu.cmu.cs.ls.keymaerax.core.Rule]]
  * @Tactic complete
  */
trait SequentCalculus {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Propositional tactics

  /** Hide/weaken whether left or right */
  val hide    : DependentPositionTactic = ProofRuleTactics.hide
  /** Hide/weaken left: weaken a formula to drop it from the antecedent ([[edu.cmu.cs.ls.keymaerax.core.HideLeft HideLeft]]) */
  @Tactic("WL", premises = "Γ |- Δ",
    conclusion = "Γ, P |- Δ")
  val hideL   : CoreLeftTactic = anon { (pr:ProvableSig, pos:AntePosition) => pr(HideLeft(pos.checkTop), 0) }
  /** Hide/weaken right: weaken a formula to drop it from the succcedent ([[edu.cmu.cs.ls.keymaerax.core.HideRight HideRight]]) */
  @Tactic("WR", premises = "Γ |- Δ",
    conclusion = "Γ |- P, Δ")
  val hideR   : CoreRightTactic = anon { (pr:ProvableSig, pos:SuccPosition) => pr(HideRight(pos.checkTop), 0) }
  /** CoHide/weaken left: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHideLeft CoHideLeft]]) */
  @Tactic("WL", premises = "P |- ",
    conclusion = "Γ, P |- Δ")
  val cohideL : CoreLeftTactic = anon { (pr:ProvableSig, pos:AntePosition) => pr(CoHideLeft(pos.checkTop), 0) }
  /** CoHide/weaken right: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHideRight CoHideRight]]) */
  @Tactic("WR", premises = "|- P",
    conclusion = "Γ |- P, Δ")
  val cohideR : CoreRightTactic = anon { (pr:ProvableSig, pos:SuccPosition) => pr(CoHideRight(pos.checkTop), 0) }
  /** CoHide/coweaken whether left or right: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHideLeft CoHideLeft]]) */
  val cohide  : DependentPositionTactic = ProofRuleTactics.cohide
  /** CoHide2/coweaken2 both left and right: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHide2 CoHide2]]) */
  @Tactic("WLR", codeName = "coHide2", premises = "P |- Q",
    conclusion = "Γ, P |- Q, Δ")
  val cohide2: BuiltInTwoPositionTactic = anon {(pr:ProvableSig, ante: Position, succ: Position) => {
      require(ante.isAnte && succ.isSucc, "Expects an antecedent and a succedent position.")
      pr(CoHide2(ante.checkAnte.top, succ.checkSucc.top), 0)
    }
  }
  /** Cohides in succedent, but leaves antecedent as is. */
  @Tactic("WR", premises = "Γ, P |- Q",
    conclusion = "Γ, P |- Q, Δ")
  val cohideOnlyR: DependentPositionTactic = anon { (pos: Position) =>
    assert(pos.isTopLevel & pos.isSucc, "Expected top-level succedent position, but got " + pos)
    (hideR(1) * pos.checkTop.getIndex) & SaturateTactic(hideR(2))
  }

  /** Cohides in antecedent, but leaves succedent as is. */
  @Tactic("WL", premises = "|- Q, Δ",
    conclusion = "Γ, P |- Q, Δ")
  val cohideOnlyL: DependentPositionTactic = anon { (pos: Position) =>
    assert(pos.isTopLevel & pos.isAnte, "Expected top-level antecedent position, but got " + pos)
    (hideL(-1) * pos.checkTop.getIndex) & SaturateTactic(hideL(-2))
  }

  /** !L Not left: move an negation in the antecedent to the succedent ([[edu.cmu.cs.ls.keymaerax.core.NotLeft NotLeft]]) */
  @Tactic(("¬L", "!L"), premises = "Γ |- P, Δ",
    conclusion = "¬P, Γ |- Δ")
  val notL    : CoreLeftTactic = coreanon { (pr:ProvableSig, pos:AntePosition) => pr(NotLeft(pos.checkTop), 0) }
  /** !R Not right: move an negation in the succedent to the antecedent ([[edu.cmu.cs.ls.keymaerax.core.NotRight NotRight]]) */
  @Tactic(("¬R", "!R"), premises = "Γ, P |- Δ",
    conclusion = "P∧Q, Γ |- Δ")
  val notR    : CoreRightTactic = coreanon { (pr:ProvableSig, pos:SuccPosition) => pr(NotRight(pos.checkTop), 0) }
  /** &L And left: split a conjunction in the antecedent into separate assumptions ([[edu.cmu.cs.ls.keymaerax.core.AndLeft AndLeft]]) */
  @Tactic(("∧L", "&L"), premises = "Γ, P, Q |- Δ",
    conclusion = "¬P, Γ |- Δ")
  val andL    : CoreLeftTactic = coreanon { (pr:ProvableSig, pos:AntePosition) => pr(AndLeft(pos.checkTop), 0) }
  /** Inverse of [[andL]].
    * {{{
    *   G, G', G'', a&b  |- D
    * -------------------------
    *   G, a, G', b, G'' |- D
    * }}}
    */
  def andLi(pos1: AntePos = AntePos(0), pos2: AntePos = AntePos(1)): DependentTactic = PropositionalTactics.andLi(pos1, pos2)
  val andLi: DependentTactic = andLi()
  /** &R And right: prove a conjunction in the succedent on two separate branches ([[edu.cmu.cs.ls.keymaerax.core.AndRight AndRight]]) */
  @Tactic(("∧R", "&R"), premises = "Γ |- P, Δ ;; Γ |- Q, Δ",
    conclusion = "Γ |- P∧Q, Δ")
  val andR    : CoreRightTactic = coreanon { (pr:ProvableSig, pos:SuccPosition) => pr(AndRight(pos.checkTop), 0) }
  /** |L Or left: use a disjunction in the antecedent by assuming each option on separate branches ([[edu.cmu.cs.ls.keymaerax.core.OrLeft OrLeft]]) */
  @Tactic(("∨L", "|L"), premises = "P, Γ |- Δ ;; Q, Γ |- Δ",
    conclusion = "P∨Q, Γ |- Δ")
  val orL     : CoreLeftTactic = coreanon { (pr:ProvableSig, pos:AntePosition) => pr(OrLeft(pos.checkTop), 0) }
  /** Inverse of [[orR]].
    * {{{
    *   G |- D, D', D'', a | b
    * -------------------------
    *   G |- D, a, D', b, D''
    * }}}
    */
  def orRi(pos1: SuccPos = SuccPos(0), pos2: SuccPos = SuccPos(1)): DependentTactic = PropositionalTactics.orRi(pos1, pos2)
  val orRi: DependentTactic = orRi()
  /** |R Or right: split a disjunction in the succedent into separate formulas to show alternatively ([[edu.cmu.cs.ls.keymaerax.core.OrRight OrRight]]) */
  @Tactic(("∨R", "|R"), premises = "Γ |- Δ, P, Q",
    conclusion = "Γ |- P∨Q, Δ")
  val orR     : CoreRightTactic = coreanon { (pr:ProvableSig, pos:SuccPosition) => pr(OrRight(pos.checkTop), 0) }
  /** ->L Imply left: use an implication in the antecedent by proving its left-hand side on one branch and using its right-hand side on the other branch ([[edu.cmu.cs.ls.keymaerax.core.ImplyLeft ImplyLeft]]) */
  @Tactic(("→L", "->L"), premises = "Γ |- Δ, P ;; Q, Γ |- Δ",
    conclusion = "P→Q, Γ |- Δ")
  val implyL  : CoreLeftTactic = coreanon { (pr:ProvableSig, pos:AntePosition) => pr(ImplyLeft(pos.checkTop), 0) }
  /** ->R Imply right: prove an implication in the succedent by assuming its left-hand side and proving its right-hand side ([[edu.cmu.cs.ls.keymaerax.core.ImplyRight ImplyRight]]) */
  @Tactic(("→R", "->R"), premises = "Γ, P |- Q, Δ",
    conclusion = "Γ |- P→Q, Δ")
  val implyR  : CoreRightTactic = coreanon { (pr:ProvableSig, pos:SuccPosition) => pr(ImplyRight(pos.checkTop), 0) }
  /** Inverse of [[implyR]].
    * {{{
    *   G, G' |- D, D', a -> b
    * -------------------------
    *   G, a, G' |- D, b, D'
    * }}}
    */
  def implyRi(keep: Boolean = false): BuiltInTwoPositionTactic = PropositionalTactics.implyRi(keep)
  val implyRi: AppliedBuiltinTwoPositionTactic = implyRi()(AntePos(0), SuccPos(0))
  /** <->L Equiv left: use an equivalence by considering both true or both false cases ([[edu.cmu.cs.ls.keymaerax.core.EquivLeft EquivLeft]]) */
  @Tactic(("↔L", "<->L"), premises = "P∧Q, Γ |- Δ ;; ¬P∧¬Q, Γ |- Δ",
    conclusion = "P↔Q, Γ |- Δ")
  val equivL  : CoreLeftTactic = coreanon { (pr:ProvableSig, pos:AntePosition) => pr(EquivLeft(pos.checkTop), 0) }
  /** <->R Equiv right: prove an equivalence by proving both implications ([[edu.cmu.cs.ls.keymaerax.core.EquivRight EquivRight]]) */
  @Tactic(("↔R", "<->R"), premises = "Γ, P |- Δ, Q ;; Γ, P |- Δ, Q",
    conclusion = "Γ |- P↔Q, Δ")
  val equivR  : CoreRightTactic = coreanon { (pr:ProvableSig, pos:SuccPosition) => pr(EquivRight(pos.checkTop), 0) }

  /** cut a formula in to prove it on one branch and then assume it on the other. Or to perform a case distinction on whether it holds ([[edu.cmu.cs.ls.keymaerax.core.Cut Cut]]).
    * {{{
    * G, c |- D     G |- D, c
    * ----------------------- (cut)
    *         G |- D
    * }}}
    */
  def cut(cut : Formula)      : InputTactic         = ProofRuleTactics.cut(cut)
  /** cut a formula in in place of pos on the right to prove its implication on the second branch and assume it on the first. ([[edu.cmu.cs.ls.keymaerax.core.CutRight CutRight]]).
    * {{{
    * G |- c, D    G |- c->p, D
    * ------------------------- (Cut right)
    *        G |- p, D
    * }}}
    */
  def cutR(cut : Formula): DependentPositionWithAppliedInputTactic =  ProofRuleTactics.cutR(cut)
  /** cut a formula in in place of pos on the left to prove its implication on the second branch and assume it on the first. ([[edu.cmu.cs.ls.keymaerax.core.CutLeft CutLeft]]).
    * {{{
    * c, G |- D    G |- D, p->c
    * ------------------------- (Cut Left)
    *        p, G |- D
    * }}}
    */
  def cutL(cut : Formula): DependentPositionWithAppliedInputTactic = ProofRuleTactics.cutL(cut)
  /** cut a formula in in place of pos to prove its implication on the second branch and assume it on the first (whether pos is left or right). ([[edu.cmu.cs.ls.keymaerax.core.CutLeft CutLeft]] or [[edu.cmu.cs.ls.keymaerax.core.CutRight CutRight]]).
    * {{{
    * c, G |- D    G |- D, p->c
    * ------------------------- (Cut Left at antecedent<0)
    *        p, G |- D
    * }}}
    * {{{
    * G |- c, D    G |- c->p, D
    * ------------------------- (Cut right at succedent>0)
    *        G |- p, D
    * }}}
    */
  def cutLR(cut : Formula): DependentPositionWithAppliedInputTactic = ProofRuleTactics.cutLR(cut)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // First-order tactics

  // quantifiers
  /** all right: Skolemize a universal quantifier in the succedent ([[edu.cmu.cs.ls.keymaerax.core.Skolemize Skolemize]])
    * Skolemization with bound renaming on demand.
    * @see [[edu.cmu.cs.ls.keymaerax.core.Skolemize]]
    * @example {{{
    *     y>5   |- x^2>=0
    *     --------------------------allSkolemize(1)
    *     y>5   |- \forall x x^2>=0
    * }}}
    * @example Uniformly renames other occurrences of the quantified variable in the context on demand to avoid [[SkolemClashException]]. {{{
    *     x_0>0 |- x^2>=0
    *     --------------------------allSkolemize(1)
    *     x>0   |- \forall x x^2>=0
    * }}}
    */
  @Tactic(premises = "Γ |- p(x), Δ",
    conclusion = "Γ |- ∀x p(x), Δ")
  val allR                          : DependentPositionTactic = anon {(pos:Position) => FOQuantifierTactics.allSkolemize(pos)}
  /** all left: instantiate a universal quantifier for variable x in the antecedent by the concrete instance `term`. */
  def allL(x: Variable, inst: Term) : DependentPositionTactic = FOQuantifierTactics.allInstantiate(Some(x), Some(inst))
  /** all left: instantiate a universal quantifier in the antecedent by the concrete instance `term`. */
  def allL(inst: Term)              : DependentPositionTactic = FOQuantifierTactics.allInstantiate(None, Some(inst))
  /** all left: instantiate a universal quantifier in the antecedent by itself. */
  @Tactic(premises = "p(e), Γ |- Δ",
    conclusion = "∀x p(x), Γ |- Δ")
  val allL                          : DependentPositionTactic = anon {(pos:Position) => FOQuantifierTactics.allInstantiate(None, None)(pos)}
  /** all left: instantiate a universal quantifier in the antecedent by the term obtained from position `instPos`. */
  //@todo turn this into a more general function that obtains data from the sequent.
  def allLPos(instPos: Position)    : DependentPositionTactic = "all instantiate pos" by ((pos:Position, sequent:Sequent) => sequent.sub(instPos) match {
    case Some(t: Term) => allL(t)(pos)
    case Some(e) => throw new TacticInapplicableFailure("all instantiate pos only applicable to terms, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
  })
  /** exists left: Skolemize an existential quantifier in the antecedent by introducing a new name for the witness. */
  @Tactic(premises = "p(x), Γ |- Δ",
    conclusion = "∃x p(x), Γ |- Δ")
  val existsL                         : DependentPositionTactic = anon {(pos: Position) => FOQuantifierTactics.existsSkolemize(pos)}
  /** exists right: instantiate an existential quantifier for x in the succedent by a concrete instance `inst` as a witness */
  def existsR(x: Variable, inst: Term): DependentPositionTactic = FOQuantifierTactics.existsInstantiate(Some(x), Some(inst))
  /** exists right: instantiate an existential quantifier in the succedent by a concrete instance `inst` as a witness */
  def existsR(inst: Term)             : DependentPositionTactic = FOQuantifierTactics.existsInstantiate(None, Some(inst))
  /** exists right: instantiate an existential quantifier for x in the succedent by itself as a witness */
  @Tactic(premises = "Γ |- p(e), Δ",
    conclusion = "Γ |- ∃x p(x), Δ")
  val existsR                         : DependentPositionTactic = anon {(pos: Position) => FOQuantifierTactics.existsInstantiate(None, None)(pos)}
  /** exists right: instantiate an existential quantifier in the succedent by a concrete term obtained from position `instPos`. */
  def existsRPos(instPos: Position)   : DependentPositionTactic = "exists instantiate pos" by ((pos:Position, sequent:Sequent) => sequent.sub(instPos) match {
    case Some(t: Term) => existsR(t)(pos)
    case Some(e) => throw new TacticInapplicableFailure("exists instantiate pos only applicable to terms, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
  })


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // closing tactics

  /** close: closes the branch when the same formula is in the antecedent and succedent or true or false close */
    //@todo optimizable seems like complicated and possibly slow code???
  @Tactic(premises = "*", conclusion = "Γ, P |- P, Δ")
  val close: BelleExpr = anon {(seq: Sequent) => {
    seq.succ.zipWithIndex.find({
      case (True, _) => true
      case (fml, _) =>
       val x = seq.ante.contains(fml)
        x
    })
    match {
      case Some((True, i)) =>
        ProofRuleTactics.closeTrue(SuccPos(i))
      case Some((fml, i)) =>
        close(AntePos(seq.ante.indexOf(fml)), SuccPos(i))
      case None => seq.ante.zipWithIndex.find({ case (False, _) => true case _ => false }) match {
        case Some((False, i)) => ProofRuleTactics.closeFalse(AntePos(i))
        case _ => DebuggingTactics.error("Inapplicable close")
      }
    }
  }}
  /** close: closes the branch when the same formula is in the antecedent and succedent ([[edu.cmu.cs.ls.keymaerax.core.Close Close]]) */
  def close(a: AntePos, s: SuccPos): BelleExpr = //cohide2(a, s) & ProofRuleTactics.trivialCloser
    //@note same name (closeId) as SequentCalculus.closeId for serialization
    new BuiltInTactic("closeId") {
      override def result(provable: ProvableSig): ProvableSig = {
        ProofRuleTactics.requireOneSubgoal(provable, "closeId(" + a + "," + s + ")")
        try {
          provable(Close(a, s), 0)
        } catch {
          case ex: NoncriticalCoreException => throw new TacticInapplicableFailure("Tactic " + name +
            " applied at " + a + " and " + s + " is inapplicable in " + provable.prettyString, ex)
        }
      }
    }
  def close(a: Int, s: Int): BelleExpr = close(Position(a).checkAnte.top, Position(s).checkSucc.top)
  /** closeId: closes the branch when the same formula is in the antecedent and succedent ([[edu.cmu.cs.ls.keymaerax.core.Close Close]]) */
  @Tactic(premises = "*",
    conclusion = "Γ, P |- P, Δ",
    codeName = "idWith")
  val closeIdWith: DependentPositionTactic = anon {(pos: Position, s: Sequent) =>
    pos.top match {
      case p@AntePos(_) if s.succ.contains(s(p)) => close(p, SuccPos(s.succ.indexOf(s(p))))
      case p@SuccPos(_) if s.ante.contains(s(p)) => close(AntePos(s.ante.indexOf(s(p))), p)
      case _ => throw new TacticInapplicableFailure("Inapplicable: closeIdWith at " + pos + " cannot close due to missing counterpart")
    }
  }
  //@note do not forward to closeIdWith (performance)
  @Tactic(premises = "*",
    conclusion = "Γ, P |- P, Δ")
  val closeId: DependentTactic = anon {(seq: Sequent) =>
    //@todo optimizable performance avoiding the repeated search
    val fmls = seq.ante.intersect(seq.succ)
    val fml = fmls.headOption.getOrElse(throw new TacticInapplicableFailure("Expects same formula in antecedent and succedent. Found:\n" + seq.prettyString))
    close(AntePos(seq.ante.indexOf(fml)), SuccPos(seq.succ.indexOf(fml)))
  }
  /** closeT: closes the branch when true is in the succedent ([[edu.cmu.cs.ls.keymaerax.core.CloseTrue CloseTrue]]) */
  @Tactic(/*codeName = "closeTrue",*/ premises = "*",
    conclusion = "Γ |- ⊤, Δ")
  val closeT: BelleExpr = anon { ProofRuleTactics.closeTrue('R, True) }
//  val closeT: BelleExpr = "closeTrue" by { ProofRuleTactics.closeTrue('R, True) }
  /** closeF: closes the branch when false is in the antecedent ([[edu.cmu.cs.ls.keymaerax.core.CloseFalse CloseFalse]]) */
  @Tactic(/*codeName = "closeFalse",*/ premises = "*",
    conclusion = "Γ, ⊥ |- Δ")
  val closeF: BelleExpr = anon { ProofRuleTactics.closeFalse('L, False) }
//  val closeF: BelleExpr = "closeFalse" by { ProofRuleTactics.closeFalse('L, False) }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // derived propositional

  /** Turn implication `a->b` on the right into an equivalence `a<->b`, which is useful to prove by CE etc. ([[edu.cmu.cs.ls.keymaerax.core.EquivifyRight EquivifyRight]]) */

  @Tactic(("→2↔", "->2<->R"), premises = "Γ |- P↔Q, Δ",
    conclusion = "Γ |- P→Q, Δ")
  val equivifyR: CoreRightTactic = coreanon { (pr:ProvableSig, pos:SuccPosition) => pr(EquivifyRight(pos.checkTop), 0) }
  /** Modus Ponens: p&(p->q) -> q.
    * @example {{{
    *      p, q, G |- D
    *   ---------------- modusPonens
    *   p, p->q, G |- D
    * }}}
    * @param assumption Position pointing to p
    * @param implication Position pointing to p->q
    */
  def modusPonens(assumption: AntePos, implication: AntePos): BelleExpr = PropositionalTactics.modusPonens(assumption, implication)
  /** Commute equivalence on the left [[edu.cmu.cs.ls.keymaerax.core.CommuteEquivLeft CommuteEquivLeft]] */
  @Tactic(("↔cL", "<->cLR"), premises = "Q↔P, Γ |- Δ",
    conclusion = "P↔Q, Γ |- Δ")
  val commuteEquivL: CoreLeftTactic = coreanon { (pr:ProvableSig, pos:AntePosition) => pr(CommuteEquivLeft(pos.checkTop), 0) }
  /** Commute equivalence on the right [[edu.cmu.cs.ls.keymaerax.core.CommuteEquivRight CommuteEquivRight]] */
  @Tactic(("↔cR", "<->cR"), premises = "Γ |- Q↔P, Δ",
    conclusion = "Γ |- P↔Q, Δ")
  val commuteEquivR: CoreRightTactic = coreanon { (pr:ProvableSig, pos:SuccPosition) => pr(CommuteEquivRight(pos.checkTop), 0) }
  /** Commute equality `a=b` to `b=a` */
  lazy val commuteEqual       : DependentPositionTactic = UnifyUSCalculus.useAt(Ax.equalCommute)

}
