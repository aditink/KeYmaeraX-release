/**
 * Axioms of KeYmaera X and axiomatic proof rules of KeYmaera X.
 * resulting from differential dynamic logic
 * @note Soundness-critical: Only adopt sound axioms and sound axiomatic rules.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

/**
 * The data base of axioms and axiomatic rules of KeYmaera X as resulting from differential dynamic logic axiomatizations.
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @author aplatzer
 */
private[core] object AxiomBase {
  /**
   * KeYmaera X Axiomatic Proof Rules.
   * @note Soundness-critical: Only return locally sound proof rules.
   * @return immutable list of locally sound axiomatic proof rules (premise, conclusion)
   * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
   * @author aplatzer
   */
  private[core] def loadAxiomaticRules() : scala.collection.immutable.Map[String, (Sequent, Sequent)] = {
    val x = Variable("x_", None, Real)
    val px = ApplyPredicate(Function("p_", None, Real, Bool), x)
    val pny = ApplyPredicate(Function("p_", None, Real, Bool), Anything)
    val qx = ApplyPredicate(Function("q_", None, Real, Bool), x)
    val qny = ApplyPredicate(Function("q_", None, Real, Bool), Anything)
    val fny = Apply(Function("f_", None, Real, Real), Anything)
    val gny = Apply(Function("g_", None, Real, Real), Anything)
    val ctxt = Function("ctx_", None, Real, Real)
    val ctxf = Function("ctx_", None, Real, Bool)
    val context = Function("ctx_", None, Bool, Bool)//@TODO eisegesis predicational should be Function("ctx_", None, Real->Bool, Bool) //@TODO introduce function types or the Predicational datatype
    val a = ProgramConstant("a_")
    val fmlny = ApplyPredicate(Function("F_", None, Real, Bool), Anything)

    scala.collection.immutable.Map(
      /* @derived("Could use CQ equation congruence with p(.)=(ctx_(.)=ctx_(g_(x))) and reflexivity of = instead.") */
      ("CT term congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, fny, gny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, Apply(ctxt, fny), Apply(ctxt, gny)))))),
      ("CQ equation congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, fny, gny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(ApplyPredicate(ctxf, fny), ApplyPredicate(ctxf, gny)))))),
      ("CE congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(ApplyPredicational(context, pny), ApplyPredicational(context, qny)))))),
      ("all generalization",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(px)),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Forall(Seq(x), px))))),
      ("all monotone",
        (Sequent(Seq(), IndexedSeq(px), IndexedSeq(qx)),
          Sequent(Seq(), IndexedSeq(Forall(Seq(x), px)), IndexedSeq(Forall(Seq(x), qx))))),
      ("[] monotone",
        (Sequent(Seq(), IndexedSeq(pny), IndexedSeq(qny)),
          Sequent(Seq(), IndexedSeq(BoxModality(a, pny)), IndexedSeq(BoxModality(a, qny))))),
      ("<> monotone",
        (Sequent(Seq(), IndexedSeq(pny), IndexedSeq(qny)),
          Sequent(Seq(), IndexedSeq(DiamondModality(a, pny)), IndexedSeq(DiamondModality(a, qny))))),
/* @TODO REMOVE */
      //@deprecated("Use CE instead.")
      ("all congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(px, qx))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Forall(Seq(x), px), Forall(Seq(x), qx)))))),
      //@deprecated("Use CE instead.")
      ("exists congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(px, qx))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Exists(Seq(x), px), Exists(Seq(x), qx)))))),
      //@deprecated("Use [] monotone twice or just use CE equivalence congruence")
      //@TODO likewise for the other congruence rules.
      ("[] congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(BoxModality(a, pny), BoxModality(a, qny)))))),
      //@deprecated("Use CE instead.")
      ("<> congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(DiamondModality(a, pny), DiamondModality(a, qny)))))),
      //@deprecated Use "CE equivalence congruence" instead of all these congruence rules.
      // Derived axiomatic rules
      ("-> congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Imply(fmlny, pny), Imply(fmlny, qny)))))),
      //@deprecated("Use CE instead.")
      ("<-> congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Equiv(fmlny, pny), Equiv(fmlny, qny)))))),
      //@deprecated("Use CE instead.")
      ("& congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(And(fmlny, pny), And(fmlny, qny)))))),
      //@deprecated("Use CE instead.")
      ("| congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Or(fmlny, pny), Or(fmlny, qny)))))),
      //@deprecated("Use CE instead.")
      ("! congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Not(pny), Not(qny)))))),
/* @TODO END REMOVE */
      /* UNSOUND FOR HYBRID GAMES */
      ("Goedel", /* unsound for hybrid games */
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(pny)),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(BoxModality(a, pny)))))
    )
  }

  /**
   * Look up an axiom of KeYmaera X,
   * i.e. sound axioms are valid formulas of differential dynamic logic.
   */
  private[core] def loadAxioms() : String =
"""
/**
 * KeYmaera Axioms.
 *
 * @note Soundness-critical: Only adopt valid formulas as axioms.
 *
 * @author Nathan Fulton
 * @author Stefan Mitsch
 * @author Jan-David Quesel
 * @author Andre Platzer
 * 
 * Basic dL Axioms of Differential Dynamic Logic.
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012."
 * @see "Andre Platzer. Dynamic logics of dynamical systems. arXiv 1205.4788, May 2012."
 * @see "Andre Platzer. Differential game logic. arXiv 1408.1980, August 2014."
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
Variables.
  T c().
  T s.
  T s().
  T t.
  T t().
  T x.
  T v. /* TODO-nrf this needs to be a V */
  T f(T).
  T g(T).
  T ctxT_(T).
  P a.
  P b.
  CP c.
  F p.
  F p(T).
  F p(?).
  F q.
  F q(T).
  F r(?).
  F ctxF_(T).
  F H.
  F H(T).
  /* for arithmetic axioms */
  /* T r.
   * T Abs(T).
   * T Max(T, T).
   * T Min(T, T).*/
End.

/**
 * FIRST-ORDER QUANTIFIER AXIOMS
 */
Axiom "all instantiate".
  \forall x. p(x) -> p(t())
End.

Axiom "exists generalize".
  p(t()) -> \exists x. p(x)
End.

Axiom "vacuous exists quantifier".
  p <-> \exists x. p
End.

Axiom "vacuous all quantifier".
  p <-> \forall x. p
End.

Axiom "all dual".
  \forall x . p(x) <-> !(\exists x . (!p(x)))
End.

/* @Derived */
Axiom "exists dual".
  \exists x . p(x) <-> !(\forall x . (!p(x)))
End.

/*
Axiom "all quantifier scope".
  (\forall x. (p(x) & q)) <-> ((\forall x. p(x)) & q)
End.
*/

/**
 * CONGRUENCE RULES
 * MONOTONICITY RULES
 */

Axiom "const congruence".
  s() = t() -> ctxT_(s()) = ctxT_(t())
End.

Axiom "const formula congruence".
  s() = t() -> (ctxF_(s()) <-> ctxF_(t()))
End.

/*
Rule "CT term congruence".
Premise f_(?) = g_(?)
Conclusion ctxT_(f_(?)) = ctxT_(g_(?))
End.

Rule "CQ equation congruence".
Premise f_(?) = g_(?)
Conclusion ctxP_(f_(?)) <-> ctxP_(g_(?))
End.

Rule "CE congruence".
Premise p_(?) = q_(?)
Conclusion ctxF_(p_(?)) <-> ctxF_(q_(?))
End.

Rule "all generalization".
Premise p(x)
Conclusion \forall x . p(x)
End.

Rule "[] monotone".
Premise p(x) ==> q(x)
Conclusion [a;]p(x) ==> [a;]q(x)
End.

Rule "<> monotone".
Premise p(x) ==> q(x)
Conclusion <a;>p(x) ==> <a;>q(x)
End.

// derived rules

// @Derived
// @deprecated
Rule "all congruence".
Premise p(x) <-> q(x)
Conclusion (\forall x . p(x)) <-> (\forall x . q(x))
End.

// @Derived
// @deprecated
Rule "exists congruence".
Premise p(x) <-> q(x)
Conclusion (\exists x . p(x)) <-> (\exists x . q(x))
End.

// @Derived
// @deprecated
Rule "[] congruence".
Premise p(x) <-> q(x)
Conclusion [a;]p(x) <-> [a;]q(x)
End.

// @Derived
// @deprecated
Rule "<> congruence".
Premise p(x) <-> q(x)
Conclusion <a;>p(x) <-> <a;>q(x)
End.

// @Derived
// @deprecated
Rule "-> congruence".
Premise p <-> q
Conclusion (F->p) <-> (F->q)
End.

// @Derived
// @deprecated
Rule "<-> congruence".
Premise p <-> q
Conclusion (F<->p) <-> (F<->q)
End.

// @Derived
// @deprecated
Rule "& congruence".
Premise p <-> q
Conclusion (F & p) <-> (F & q)
End.

// @Derived
// @deprecated
Rule "| congruence".
Premise p <-> q
Conclusion (F | p) <-> (F | q)
End.

// @Derived
// @deprecated
Rule "! congruence".
Premise p <-> q
Conclusion (!p) <-> (!q)
End.
*/

/**
 * HYBRID PROGRAM MODALITIES
 */

Axiom "<> dual".
  <a;>p(?) <-> ![a;](!p(?))
End.

/* @Derived */
Axiom "[] dual".
  [a;]p(?) <-> !<a;>(!p(?))
End.

Axiom "[:=] assign".
  [v:=t();]p(v) <-> p(t())
End.

Axiom "<:=> assign".
  <v:=t();>p(v) <-> p(t())
End.

Axiom "[:=] assign equational".
  [v:=t();]p(v) <-> \forall v . (v=t() -> p(v))
End.

Axiom "[:=] vacuous assign".
  [v:=t();]p <-> p
End.

Axiom "<:=> vacuous assign".
  <v:=t();>p <-> p
End.

Axiom "[':=] differential assign".
  [v':=t();]p(v') <-> p(t())
End.

Axiom "<':=> differential assign".
  <v':=t();>p(v') <-> p(t())
End.

Axiom "[:*] assign nondet".
  [v:=*;]p(v) <-> \forall v. p(v)
End.

Axiom "<:*> assign nondet".
  <v:=*;>p(v) <-> \exists v. p(v)
End.

Axiom "[?] test".
  [?H;]p <-> (H -> p).
End.

Axiom "<?> test".
  <?H;>p <-> (H & p).
End.

Axiom "[++] choice".
  [a ++ b]p(?) <-> ([a;]p(?) & [b;]p(?)).
End.

Axiom "<++> choice".
   <a ++ b;>p(?) <-> (<a;>p(?) | <b;>p(?)).
End.

Axiom "[;] compose".
  [ a; b; ]p(?) <-> [a;][b;]p(?).
End.

Axiom "<;> compose".
  < a; b; >p(?) <-> <a;><b;>p(?).
End.

Axiom "[*] iterate".
  [a*]p(?) <-> (p(?) & [a;][a*] p(?)).
End.

Axiom "<*> iterate".
  <a*>p(?) <-> (p(?) | <a;><a*> p(?)).
End.

/**
 * DIFFERENTIAL EQUATION AXIOMS
 */

Axiom "DW differential weakening".
  [c&H(?);]p(?) <-> ([c&H(?);](H(?)->p(?)))
/* [x'=f(x)&q(x);]p(x) <-> ([x'=f(x)&q(x);](q(x)->p(x))) THEORY */
End.

Axiom "DC differential cut".
  ([c&H(?);]p(?) <-> [c&(H(?)&r(?));]p(?)) <- [c&H(?);]r(?)
/*  ([x'=f(x)&q(x);]p(x) <-> [x'=f(x)&(q(x)&r(x));]p(x)) <- [x'=f(x)&q(x);]r(x) THEORY */
End.

Axiom "DE differential effect".
  [x'=f(x)&q(x);]p(x) <-> [x'=f(x)&q(x);][x':=f(x);]p(x)  /* THEORY */
End.

Axiom "DI differential invariant".
  [c&H(?);]p(?) <- (H(?)-> (p(?) & [c&H(?);](p(?)')))
/* [x'=f(x)&q(x);]p(x) <- (q(x) -> (p(x) & [x'=f(x)&q(x);](p(x)'))) THEORY */
End.

/* Differential Auxiliary / Differential Ghost */
Axiom "DA differential ghost".
  [c&H(?);]p(?) <- ((p(?) <-> \exists x. q(?)) & [c,x'=t()*x+s()&H(?);]q(?))
/*@TODO [c&H(?);]p(?) <-> \exists y. [c,y'=t()*y+s()&H(?);]p(?) */
/* [x'=f(x)&q(x);]p(x) <-> \exists y. [(x'=f(x),y'=a(x)*y+b(x))&q(x);]p(x) THEORY */
End.

Axiom "Dsol differential equation solution".
 <x'=c();>p(x) <-> \exists t. (t>=0 & <x:=x+c()*t;>p(x))
End.

/**
 * DIFFERENTIAL INVARIANTS for SYSTEMS
 */

Axiom "DE differential effect (system)".
    /* @TODO f(?) cannot contain primes */
    /* @NOTE reassociate needed in data structures */
    [x'=f(?),c&H(?);]p(?) <-> [c,x'=f(?)&H(?);][x':=f(?);]p(?)
End.

/**
 * DERIVATION FOR FORMULAS
 */

/* @todo added and probably not nec. */
/* @derived by CE */
Axiom "->' derive imply".
  (p(?) -> q(?))' <-> (!p(?) | q(?))'
End.

Axiom "&' derive and".
  (p(?) & q(?))' <-> ((p(?)') & (q(?)'))
End.

Axiom "|' derive or".
  (p(?) | q(?))' <-> ((p(?)') & (q(?)'))
  /* sic! */
End.

Axiom "forall' derive forall".
  (\forall x. p(?))' <-> (\forall x. (p(?)'))
End.

Axiom "exists' derive exists".
  (\exists x. p(?))' <-> (\forall x. (p(?)'))
  /* sic! */
End.

Axiom "c()' derive constant fn".
  c()' = 0
End.

Axiom "=' derive =".
  (f(?) = g(?))' <-> ((f(?)') = (g(?)'))
End.

Axiom ">=' derive >=".
  (f(?) >= g(?))' <-> ((f(?)') >= (g(?)'))
End.

Axiom ">' derive >".
  (f(?) > g(?))' <-> ((f(?)') >= (g(?)'))
  /* sic! easier */
End.

Axiom "<=' derive <=".
  (f(?) <= g(?))' <-> ((f(?)') <= (g(?)'))
End.

Axiom "<' derive <".
  (f(?) < g(?))' <-> ((f(?)') <= (g(?)'))
  /* sic! easier */
End.

Axiom "!=' derive !=".
  (f(?) != g(?))' <-> ((f(?)') = (g(?)'))
  /* sic! */
End.

/* DERIVATION FOR TERMS */

Axiom "-' derive neg".
  (-f(?))' = -(f(?)')
End.

Axiom "+' derive sum".
  (f(?) + g(?))' = (f(?)') + (g(?)')
End.

Axiom "-' derive minus".
  (f(?) - g(?))' = (f(?)') - (g(?)')
End.

Axiom "*' derive product".
  (f(?) * g(?))' = ((f(?)')*g(?)) + (f(?)*(g(?)'))
End.

Axiom "/' derive quotient".
  (f(?) / g(?))' = (((f(?)')*g(?)) - (f(?)*(g(?)'))) / (g(?)^2)
End.

/*
Axiom "chain rule".
	//@NOTE can be used
End.
*/

/* @TODO c() != 0 */
Axiom "^' derive power".
	(f(?)^c())' = (c()*(f(?)^(c()-1)))*(f(?)') /*<- c() != 0*/
End.


/**
 * EXCLUSIVELY FOR HYBRID PROGRAMS.
 * UNSOUND FOR HYBRID GAMES.
 */

Axiom "V vacuous".
  p -> [a;]p
End.

/*
Rule "Goedel". // unsound for hybrid games
Premise p(x)
Conclusion [a;]p(x)
End.
*/

/* @NOTE Unsound for games */
Axiom "K modal modus ponens".
  [a;](p(?)->q(?)) -> (([a;]p(?)) -> ([a;]q(?)))
End.

Axiom "I induction".
  /*@TODO Use this form instead? which is possibly more helpful: ([a*](p(?) -> [a;] p(?))) -> (p(?) -> [a*]p(?)) */
  (p(?) & [a*](p(?) -> [a;] p(?))) -> [a*]p(?)
End.

/*@TODO Convergence axiom*/

/**
 * Real arithmetic
 */

/* Unused so far
Axiom "+ associative".
  (r + s) + t = r + (s + t)
End.

Axiom "* associative".
  (r * s) * t = r * (s * t)
End.

Axiom "+ commutative".
  s+t = t+s
End.

Axiom "* commutative".
  s*t = t*s
End.

Axiom "distributive".
  r*(s+t) = r*s + r*t
End.

Axiom "+ identity".
  s + 0 = s
End.

Axiom "* identity".
  s * 1 = s
End.

Axiom "+ inverse".
  s + (-s) = 0
End.

Axiom "* inverse".
  s != 0 -> s * (s^-1) = 1
End.

Axiom "positivity".
  0 < s | 0 = s | 0 < -s
End.

Axiom "+ closed".
  (0 < s & 0 < t) -> 0 < s+t
End.

Axiom "* closed".
  (0 < s & 0 < t) -> 0 < s*t
End.

Axiom "<".
  s<t <-> 0 < t-s
End.

Axiom ">".
  s>t <-> t<s
End.
*/

Axiom "<=".
  f(?)<=g(?) <-> (f(?)<g(?) | f(?)=g(?))
End.

Axiom "= negate".
  f(?) = g(?) <-> !(f(?) != g(?))
End.

Axiom "< negate".
  f(?) < g(?) <-> !(f(?) >= g(?))
End.

Axiom ">= flip".
  f(?) >= g(?) <-> (g(?) <= f(?))
End.

Axiom "> flip".
  f(?) > g(?) <-> (g(?) < f(?))
End.

/* Unused so far
Axiom "abs expand".
  Abs(s) = if (s < 0) then -s else s fi
End.
*/
/* Multi-argument don't parse
Axiom "max expand".
  Max(s, t) = if (s > t) then s else t fi
End.

Axiom "min expand".
  Min(s, t) = if (s < t) then s else t fi
End.
*/
"""
}
