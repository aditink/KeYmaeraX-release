package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, SaturateTactic}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TaylorModelTactics.{TaylorModel, debugTac}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.{BigDecimalTool, RingsLibrary}
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import DerivationInfoAugmentors._

import scala.collection.immutable._

trait TaylorModelOptions {
  val precision: Integer
  val order: Integer
}

trait TimeStepOptions {
  def remainderEstimation(i: Integer) : (BigDecimal, BigDecimal)
}

/**
  * Taylor model arithmetic
  *
  * Here, a Taylor model is a data structure maintaining a proof that some term is element of the Taylor model.
  *
  * */
object TaylorModelArith {
  import PolynomialArithV2.ring._
  import PolynomialArithV2Helpers._

  private def tmFormula(elem: Term, poly: Term, lower: Term, upper: Term) = {
    val err = BaseVariable("err_")
    Exists(Seq(err),
      And(Equal(elem, Plus(poly, err)),
        And(LessEqual(lower, err),
          LessEqual(err, upper)
        ))
    )
  }

  private def weakenWith(context: IndexedSeq[Formula], prv: ProvableSig) : ProvableSig = {
    assert(prv.conclusion.ante.isEmpty)
    ProvableSig.startProof(Sequent(context, prv.conclusion.succ)).apply(CoHideRight(SuccPos(0)), 0).apply(prv, 0)
  }

  /**
    * data structure with certifying computations
    * maintains the invariant
    *   prv: \exists err. elem = poly + err & err \in [lower; upper]
    *
    * */
  case class TM(elem: Term, poly: Polynomial, lower: Term, upper: Term, prv: ProvableSig) {
    val context = prv.conclusion.ante
    assert(prv.conclusion.succ(0) == tmFormula(elem, rhsOf(poly.representation), lower, upper))
    def checkCompatibleContext(other: TM) =
      if (context != other.context) throw new IllegalArgumentException("Incompatible contexts: " + context + " and " + other.context)

    /** exact addition */
    def +!(other: TM)(implicit options: TaylorModelOptions) : TM = {
      checkCompatibleContext(other)
      val newPoly = poly.resetTerm + other.poly.resetTerm

      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(options.precision)(IndexedSeq())(Plus)(lower, upper)(other.lower, other.upper)
      val newPrv = useDirectlyConst(weakenWith(context, Ax.taylorModelPlusPrv.provable), Seq(
        ("elem1_", elem),
        ("poly1_", rhsOf(poly.representation)),
        ("l1_", lower),
        ("u1_", upper),
        ("elem2_", other.elem),
        ("poly2_", rhsOf(other.poly.representation)),
        ("l2_", other.lower),
        ("u2_", other.upper),
        ("poly_", rhsOf(newPoly.representation)),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, other.prv, weakenWith(context, newPoly.representation), weakenWith(context, newIvlPrv)))
      TM(Plus(elem, other.elem), (poly + other.poly).resetTerm, l, u, newPrv)
    }

    /** approximate addition */
    def +(other: TM)(implicit options: TaylorModelOptions) : TM = (this +! other).approx

    /** exact subtraction */
    def -!(other: TM)(implicit options: TaylorModelOptions) : TM = {
      checkCompatibleContext(other)
      val newPoly = poly.resetTerm - other.poly.resetTerm

      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(options.precision)(IndexedSeq())(Minus)(lower, upper)(other.lower, other.upper)
      val newPrv = useDirectlyConst(weakenWith(context, Ax.taylorModelMinusPrv.provable), Seq(
        ("elem1_", elem),
        ("poly1_", rhsOf(poly.representation)),
        ("l1_", lower),
        ("u1_", upper),
        ("elem2_", other.elem),
        ("poly2_", rhsOf(other.poly.representation)),
        ("l2_", other.lower),
        ("u2_", other.upper),
        ("poly_", rhsOf(newPoly.representation)),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, other.prv, weakenWith(context, newPoly.representation), weakenWith(context, newIvlPrv)))
      TM(Minus(elem, other.elem), (poly - other.poly).resetTerm, l, u, newPrv)
    }
    /** approximate subtraction */
    def -(other: TM)(implicit options: TaylorModelOptions) : TM = (this -!other).approx

    /** collect terms of higher order in interval remainder */
    def collectHigherOrderTerms(implicit options: TaylorModelOptions) : TM = {
      val (polyLow, polyHigh, partitionPrv) = poly.resetTerm.partition{case (n, d, powers) => powers.map(_._2).sum <= options.order}
      val hornerPrv = polyHigh.hornerForm()
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(i => Plus(rem, i))(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, Ax.taylorModelCollectPrv.provable), Seq(
        ("elem1_", elem),
        ("poly1_", poly1),
        ("l1_", lower),
        ("u1_", upper),

        ("polyLow_", polyLow.term),
        ("poly_", rhsOf(polyLow.representation)),
        ("polyHigh_", polyHigh.term),
        ("rem_", rem),
        ("l_", l),
        ("u_", u)
      ), Seq(prv,
        weakenWith(context, partitionPrv),
        weakenWith(context, polyLow.representation),
        weakenWith(context, hornerPrv),
        newIvlPrv))
      TM(elem, polyLow.resetTerm, l, u, newPrv)
    }

    /** prove interval enclosure of Taylor model */
    def interval(implicit options: TaylorModelOptions) : (Term, Term, ProvableSig) = {
      val hornerPrv = poly.resetTerm.hornerForm()
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(i => Plus(rem, i))(lower, upper)
      (l, u,
        useDirectlyConst(weakenWith(context, Ax.taylorModelIntervalPrv.provable), Seq(
        ("elem1_", elem),
        ("poly1_", poly1),
        ("l1_", lower),
        ("u1_", upper),

        ("rem_", rem),
        ("l_", l),
        ("u_", u)
      ), Seq(prv,
        weakenWith(context, hornerPrv),
        newIvlPrv)))
    }

    /** returns an equality, no quantifiers */
    def dropEmptyInterval: Option[ProvableSig] = if (lower == Number(0) && upper == Number(0)) Some {
      val poly1 = rhsOf(poly.representation)
      useDirectlyConst(weakenWith(context, Ax.taylorModelEmptyIntervalPrv.provable), Seq(
        ("elem1_", elem),
        ("poly1_", poly1)
      ), Seq(prv))
    } else None

    /** exact multiplication */
    def *!(other: TM)(implicit options: TaylorModelOptions) : TM = {
      checkCompatibleContext(other)
      val (polyLow, polyHigh, partitionPrv) = (poly.resetTerm * other.poly.resetTerm).partition{case (n, d, powers) => powers.map(_._2).sum <= options.order}

      val hornerPrv = polyHigh.hornerForm()
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      val poly2 = rhsOf(other.poly.representation)
      def intervalBounds(i1: Term, i2: Term) : Term = Seq(rem, Times(i1, poly2), Times(i2, poly1), Times(i1, i2)).reduceLeft(Plus)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(options.precision)(context)(intervalBounds)(lower, upper)(other.lower, other.upper)
      val newPrv = useDirectlyConst(weakenWith(context, Ax.taylorModelTimesPrv.provable), Seq(
        ("elem1_", elem),
        ("poly1_", poly1),
        ("l1_", lower),
        ("u1_", upper),
        ("elem2_", other.elem),
        ("poly2_", poly2),
        ("l2_", other.lower),
        ("u2_", other.upper),

        ("polyLow_", polyLow.term),
        ("poly_", rhsOf(polyLow.representation)),
        ("polyHigh_", polyHigh.term),
        ("rem_", rem),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, other.prv,
        weakenWith(context, partitionPrv),
        weakenWith(context, polyLow.representation),
        weakenWith(context, hornerPrv),
        newIvlPrv))
      TM(Times(elem, other.elem), polyLow.resetTerm, l, u, newPrv)
    }
    /** approximate multiplication */
    def *(other: TM)(implicit options: TaylorModelOptions) : TM = (this *! other).approx

    /** exact negation */
    def unary_-(implicit options: TaylorModelOptions) : TM = {
      val newPoly = -(poly.resetTerm)

      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(IndexedSeq())(Neg)(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, Ax.taylorModelNegPrv.provable), Seq(
        ("elem1_", elem),
        ("poly1_", rhsOf(poly.representation)),
        ("l1_", lower),
        ("u1_", upper),
        ("poly_", rhsOf(newPoly.representation)),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, weakenWith(context, newPoly.representation), weakenWith(context, newIvlPrv)))
      TM(Neg(elem), (-poly).resetTerm, l, u, newPrv)
    }

    /** exact square */
    def squareExact(implicit options: TaylorModelOptions) : TM = {
      val (polyLow, polyHigh, partitionPrv) = (poly.resetTerm^2).partition{case (n, d, powers) => powers.map(_._2).sum <= options.order}
      val hornerPrv = polyHigh.hornerForm()
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      def intervalBounds(i1: Term) : Term = Seq(rem, Times(Times(Number(2), i1), poly1), Power(i1, Number(2))).reduceLeft(Plus)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(intervalBounds)(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, Ax.taylorModelSquarePrv.provable), Seq(
        ("elem1_", elem),
        ("poly1_", poly1),
        ("l1_", lower),
        ("u1_", upper),
        ("polyLow_", polyLow.term),
        ("polyHigh_", polyHigh.term),
        ("rem_", rem),
        ("poly_", rhsOf(polyLow.representation)),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, weakenWith(context, partitionPrv),
        weakenWith(context, polyLow.representation),
        weakenWith(context, hornerPrv),
        newIvlPrv))
      TM(Power(elem, Number(2)), (polyLow).resetTerm, l, u, newPrv)
    }
    /** approximate square */
    def square(implicit options: TaylorModelOptions) : TM = this.squareExact.approx

    /** approximate exponentiation */
    def ^(n: Int)(implicit options: TaylorModelOptions) : TM = n match {
      case 1 =>
        val newPrv = useDirectlyConst(weakenWith(context, Ax.taylorModelPowerOne.provable), Seq(
          ("elem1_", elem),
          ("poly1_", rhsOf(poly.representation)),
          ("l1_", lower),
          ("u1_", upper)),
          Seq(prv))
        TM(Power(elem, Number(1)), poly.resetTerm, lower, upper, newPrv)
      case n if n>0 && n%2 == 0 =>
        val m = n / 2
        val mPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(Number(n), Times(Number(2), Number(m))))
        val p = (this ^ m).square(options)
        val newPrv =
          useDirectlyConst(weakenWith(context, Ax.taylorModelPowerEven.provable), Seq(
            ("elem1_", elem),
            ("poly1_", rhsOf(poly.representation)),
            ("l1_", lower),
            ("u1_", upper),
            ("m_", Number(m)),
            ("n_", Number(n)),
            ("l_", p.lower),
            ("u_", p.upper),
            ("poly_", rhsOf(p.poly.representation))
          ),
            Seq(prv, p.prv, weakenWith(context, mPrv)))
        TM(Power(elem, Number(n)), p.poly.resetTerm, p.lower, p.upper, newPrv)
      case n if n>0 =>
        val m = n / 2
        val mPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(Number(n), Plus(Times(Number(2), Number(m)), Number(1))))
        val p = (this ^ m).square * this
        val newPrv =
          useDirectlyConst(weakenWith(context, Ax.taylorModelPowerOdd.provable), Seq(
            ("elem1_", elem),
            ("poly1_", rhsOf(poly.representation)),
            ("l1_", lower),
            ("u1_", upper),
            ("m_", Number(m)),
            ("n_", Number(n)),
            ("l_", p.lower),
            ("u_", p.upper),
            ("poly_", rhsOf(p.poly.representation))
          ),
            Seq(prv, p.prv, weakenWith(context, mPrv)))
        TM(Power(elem, Number(n)), p.poly.resetTerm, p.lower, p.upper, newPrv)
      case _ => throw new IllegalArgumentException("Taylor model ^ n requires n > 0, not n = " + n)
    }

    /** round coefficients of polynomial part, incorporate error in interval */
    def approx(implicit options: TaylorModelOptions) : TM = {
      val (polyApproxPrv, poly1, poly2) = poly.approx(options.precision)
      val poly1rep = rhsOf(poly1.representation)
      val poly2repPrv = poly2.hornerForm()
      val poly2rep = rhsOf(poly2repPrv)
      val (ivlPrv, l2, u2) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(i1 => Plus(poly2rep, i1))(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, Ax.taylorModelApproxPrv.provable),
        Seq(
          ("elem_", elem),
          ("poly_", rhsOf(poly.representation)),
          ("l_", lower),
          ("u_", upper),
          ("poly1_", poly1.term),
          ("poly1rep_", poly1rep),
          ("poly2_", poly2.term),
          ("poly2rep_", poly2rep),
          ("l2_", l2),
          ("u2_", u2)
        ),
        Seq(prv, weakenWith(context, polyApproxPrv), weakenWith(context, poly1.representation), weakenWith(context, poly2repPrv), ivlPrv)
      )
      TM(elem, poly1.resetTerm, l2, u2, newPrv)
    }

    /** theorem with a "prettier" representation of the certificate */
    def prettyPrv(implicit options: TaylorModelOptions): ProvableSig = {
      val (l1, l2) = IntervalArithmeticV2.eval_ivl(options.precision)(HashMap(), HashMap())(lower)
      val (u1, u2) = IntervalArithmeticV2.eval_ivl(options.precision)(HashMap(), HashMap())(upper)
      val prettyLower = if (l1 == l2) Number(l1) else lower
      val prettyUpper = if (u1 == u2) Number(u1) else upper
      val prettyRepresentation = poly.resetTerm.prettyRepresentation
      proveBy(ProvableSig.startProof(Sequent(context, IndexedSeq(tmFormula(elem, rhsOf(prettyRepresentation),
        prettyLower, prettyUpper)))).apply(CutRight(prv.conclusion.succ(0), SuccPos(0)), 0).
        apply(CoHideRight(SuccPos(0)), 1).
        apply(ImplyRight(SuccPos(0)), 1),
        Idioms.<(
          by(prv),
          existsL(-1) & existsR("err_".asTerm)(1) & andL(-1) & andL(-2) & andR(1) &
          Idioms.<(
            cohideOnlyL(-1) &
              useAt(prettyRepresentation, PosInExpr(1::Nil))(1, 1::0::Nil) & closeId
            ,
            hideL(-1) & IntervalArithmeticV2.intervalArithmeticBool(options.precision, new BigDecimalTool)(1)
          )
        )
      )
    }
  }

  /** constructs a Taylor model by proving the required certificate with a tactic */
  def TM(elem: Term, poly: Polynomial, lower: Term, upper: Term, context: IndexedSeq[Formula], be: BelleExpr): TM = {
    TM(elem, poly, lower, upper,
      proveBy(Sequent(context, IndexedSeq(tmFormula(elem, rhsOf(poly.representation), lower, upper))), be & done))
  }

  /** constructs a Taylor model with zero interval part */
  def Exact(elem: Polynomial, context: IndexedSeq[Formula]): TM = {
    val newPrv = useDirectlyConst(weakenWith(context, Ax.taylorModelExactPrv.provable),
      Seq(("elem_", elem.term), ("poly_", rhsOf(elem.representation))),
      Seq(weakenWith(context, elem.representation))
    )
    TM(elem.term, elem.resetTerm, Number(0), Number(0), newPrv)
  }

  // combines provables
  private def mkAndPrv(p1: ProvableSig, p2: ProvableSig) : ProvableSig = {
    assert(p1.conclusion.succ.length==1, "mkAndPrv singleton succedent 1")
    assert(p2.conclusion.succ.length==1, "mkAndPrv singleton succedent 2")
    assert(p1.conclusion.ante == p2.conclusion.ante, "mkAndPrv same antes")
    proveBy(Sequent(p1.conclusion.ante, IndexedSeq(And(p1.conclusion.succ(0), p2.conclusion.succ(0)))),
      andR(1) & Idioms.<(by(p1), by(p2))
    )
  }

  // combines provables
  private def equalTrans(p1: ProvableSig, p2: ProvableSig) : ProvableSig = {
    assert(p1.conclusion.succ.length==1, "mkAndPrv singleton succedent 1")
    assert(p2.conclusion.succ.length==1, "mkAndPrv singleton succedent 2")
    assert(p1.conclusion.ante == p2.conclusion.ante, "mkAndPrv same antes")
    val Llast = -p1.conclusion.ante.length - 1
    proveBy(Sequent(p1.conclusion.ante, IndexedSeq(Equal(lhsOf(p1), rhsOf(p2)))),
        cutR(p1.conclusion.succ(0))(1) &
        Idioms.<(
          by(p1),
            implyR(1) &
            eqL2R(Llast)(1) &
            hideL(Llast) &
            by(p2)
        )
    )
  }

  /* @todo: naming... */
  class TemplateLemmas(ode: DifferentialProgram, order: Int) extends TaylorModel(ode, order) {
    /* time step for the left Taylor model of a (linearly) preconditioned flow pipe (x0 o r0) */
    def timeStepPreconditionedODE(x0: Seq[TM], r0: Seq[TM], t0: ProvableSig, h: BigDecimal)
                                 (implicit options: TaylorModelOptions, timeStepOptions: TimeStepOptions)
    = {
      val qeTool = new BigDecimalTool
      // x0 is the initial state of the ODE
      require(x0.map(_.elem) == state, "require x0 to be the initial state of the ODE")
      // x0 is the *linear* preconditioning, without interval uncertainty
      require(x0.forall(_.poly.degree() <= 1), "require x0 to be linear")
      require(x0.forall(_.lower == Number(0)), "require zero interval uncertainty(lower)")
      require(x0.forall(_.upper == Number(0)), "require zero interval uncertainty(upper)")

      val context = x0(0).context
      require(x0.forall(_.context == context), "require compatible contexts")

      require(lhsOf(t0) == time)

      val rvars = r0.map(_.elem).toIndexedSeq
      val rIntervals = r0.map(_.interval).toIndexedSeq

      def mkTerm(coeff: (BigDecimal, BigDecimal)) : Term = Divide(Number(coeff._1), Number(coeff._2))
      val instantiation = instantiateLemma(options.precision,
        rhsOf(t0),
        Number(h),
        (i, j) => mkTerm(x0(i).poly.coefficient(Seq((rvars(j), 1)))),
        i => mkTerm(x0(i).poly.coefficient(Seq())),
        i => rIntervals(i)._1,
        i => rIntervals(i)._2,
        timeStepOptions.remainderEstimation
      ) ++ USubst(rvars.zipWithIndex.map{ case (r, i) => SubstitutionPair(names.right(i), r) })
      val lemma1 = lemma(instantiation)

      // now discharge assumptions
      val (initialConditionFmls, concl) = lemma1.conclusion.succ(0) match {
        case Imply(And(And(initial_condition, _), _), concl) =>
          (FormulaTools.conjuncts(initial_condition), concl)
        case _ => throw new RuntimeException("Taylor model lemma not of expected shape")
      }
      val rightTmDomain = rIntervals.map(rIvl => rIvl._3).reduceRight(mkAndPrv)
      val initialStateEqs = (x0, initialConditionFmls.tail).zipped.map{ case (x, Equal(y, t)) if x.elem == y =>
        val eq1 = x.dropEmptyInterval.getOrElse(throw new RuntimeException("intervals have been checked for emptiness"))
        val eq2 = weakenWith(x.context, x.poly.resetTerm.equate(ofTerm(t)).getOrElse(throw new RuntimeException("this equality should hold by construction")))
        equalTrans(eq1, eq2)
        case e => throw new RuntimeException("Taylor model lemma (initial condition) not of expected shape: " + e)
      }
      val initialCondition = (Seq(t0)++initialStateEqs).reduceRight(mkAndPrv)
      proveBy(Sequent(context, IndexedSeq(concl)),
        useAt(lemma1, PosInExpr(1::Nil))(1) & andR(1) & Idioms.<(
          andR(1) & Idioms.<(
            by(initialCondition),
            by(rightTmDomain)
          ),
          andR(1) & Idioms.<(
            debugTac("Initial Numberic condition") &
              SaturateTactic(andL('L)) &
              IntervalArithmeticV2.intervalArithmeticBool(options.precision, qeTool)(1) &
              done,
            SaturateTactic(allR(1)) &
              SaturateTactic(implyR(1)) &
              SaturateTactic(andL('L)) &
              debugTac("Numberic condition") &
              IntervalArithmeticV2.intervalArithmeticBool(options.precision, qeTool)(1) &
              done
          )
        )
      )
    }

  }

}
