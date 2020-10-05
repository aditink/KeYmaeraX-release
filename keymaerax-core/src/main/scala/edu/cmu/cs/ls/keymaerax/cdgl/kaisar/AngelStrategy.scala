/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Executable representation for Angelic strategies.
  * Translations to Angelic strategies and to simplified Demon subset.
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident
import edu.cmu.cs.ls.keymaerax.core._


// @TODO: Massive memory leak, use local data structure instead
/** Used for allocating unique integer IDs */
object IDCounter {
  // Tracks every allocated ID associated to its node
  var idMap: Map[Int, AngelStrategy] = Map()
  // For nodes which arise from a demonization translation, track the original Angel node corresponding to each ID
  var originMap: Map[Int, AngelStrategy] = Map()
  var count: Int = 0
  def next(as: AngelStrategy): Int = {
    val res = count
    count = count + 1
    idMap = idMap.+(res -> as)
    res
  }
  def contains(n: Int): Boolean = idMap.contains(n)
  def hasOriginal(n: Int): Boolean = originMap.contains(n)
  def get(n: Int): Option[AngelStrategy] = idMap.get(n)
  def apply(n: Int): AngelStrategy = idMap(n)
  def getOriginal(n: Int): Option[AngelStrategy] = originMap.get(n)
  def original(n: Int): AngelStrategy = originMap(n)
  def setOriginal(n: Int, as: AngelStrategy): Unit = (originMap = originMap.+(n -> as))
}

/** Directly executable, simply-typed strategy for Angel player */
sealed trait AngelStrategy {
  val nodeID: Int = IDCounter.next(this)
}
/** A simple strategy is one where Angel makes no choices, only Demon */
sealed trait SimpleStrategy extends AngelStrategy

/** Demon must pass test f. Strategies are weak-test, assume f is decidable */
case class DTest(f: Formula) extends SimpleStrategy
/** Deterministic assignment. Works identically for Angel/Demon.*/
case class DAssign(x: Ident, f: Term) extends SimpleStrategy
/** Nondeterministic assignment resolved by demon */
case class NDAssign(x: Ident) extends SimpleStrategy
/** Demonic loop */
case class DLoop(s: AngelStrategy) extends SimpleStrategy
// Note: binary compose is better for backend execution, but n-ary composition looks much nicer in debugger.
/** (n-ary) sequential composition, identical for Demon vs Angel. */
case class DCompose(children: List[AngelStrategy]) extends SimpleStrategy
/** Demonic choice */
case class DChoice(l: AngelStrategy, r: AngelStrategy) extends SimpleStrategy
/** Differential equation with decidable domain constraint and Demonic duration */
case class DODE(ode: ODESystem) extends AngelStrategy

/** Angelic while loop with decidable convergence/guard formula */
case class ALoop(conv: Formula, body: AngelStrategy) extends AngelStrategy
/** Angelic switch statement with decidable branch guards */
case class ASwitch(branches: List[(Formula, AngelStrategy)]) extends AngelStrategy
/** Differential equation with (concrete) angelic duration. */
case class AODE(ode: ODESystem, dur: Term) extends AngelStrategy

/** Smart constructors for DCompose */
object Composed {
  /** Smart constructor that filters out no-ops for readability */
  def apply(children: List[AngelStrategy]): AngelStrategy = {
    // Careful: Should distinguish "real" ?true from no-ops which should be eliminated
    val filtered = children.filter({case DTest(True) => false case _ => true})
    filtered match {
      case Nil => DTest(True)
      case as :: Nil => as
      case _ => DCompose(filtered)
    }
  }

  def apply(l: AngelStrategy, r: AngelStrategy): AngelStrategy = {
    apply(l :: r :: Nil)
  }

  def apply(children: List[SimpleStrategy]): SimpleStrategy = {
    // @TODO: Careful: Should distinguish "real" ?true from no-ops which should be eliminated
    // Note: flattening DCompose's would give more minimal trees, but the unflattened shape is nice in practice:
    // SSA blocks are kept together and can be easily collapsed in debugger
    val filtered = children.filter({case DTest(True) => false case _ => true})
    filtered match {
      case Nil => DTest(True)
      case as :: Nil => as
      case _ => DCompose(filtered)
    }
  }

  def apply(l: SimpleStrategy, r: SimpleStrategy): SimpleStrategy = {
    apply(l :: r :: Nil)
  }
}

object SimpleStrategy {
  /** Demonization pass which inlines Angelic strategies into Demon strategies.
    * The resulting Demon strategy is more complex in the sense that Demon must provide (or simulate) choices which Angel
    * previously made.
    * @see [[BasicDemonStrategy]] wrapper which automatically handles the added complexity of a Demonized strategy, so the
    * Demon driver can be programmed against the original game specification */
  def apply(fs: AngelStrategy): SimpleStrategy = {
    fs match {
      case DLoop(s) => DLoop(apply(s))
      case DCompose(children) => DCompose(children.map(apply))
      case DChoice(l, r) => DChoice(apply(l), apply(r))
      // @TODO: Need better negation of formulas, need more info in Kaisar data structure for that
      case ALoop(conv, body) =>
        val loop = DLoop(Composed(DTest(conv), apply(body)))
        IDCounter.setOriginal(loop.nodeID, fs)
        Composed(loop, DTest(Not(conv)))
      case ASwitch(branches) =>
        val branchStrats = branches.map({case (f, fs) => Composed(DTest(f), apply(fs))})
        val pairs = branchStrats.zip(branches)
        val (xs, x) = (pairs.dropRight(1), pairs.last)
        val (choice, _) = xs.foldLeft[(SimpleStrategy, ASwitch)]((x._1, ASwitch(x._2 :: Nil)))({case ((accStrat, accOrig), (thisStrat, thisOrig)) =>
          val fullOrig = ASwitch(thisOrig :: accOrig.branches)
          val choice = DChoice(thisStrat, accStrat)
          IDCounter.setOriginal(choice.nodeID, fullOrig)
          (choice, fullOrig)
        })
        choice
      // @TODO: Proof rule somewhere should check duration variable binding side conditions
      case ss: SimpleStrategy => ss
      case _: AODE | _: DODE => throw new Exception("ODEs should be eliminated before SimpleStrategy conversion")
    }
  }
}

object AngelStrategy {
  /** Extract executable strategy for ODE from Kaisar proof. */
  private def ofODE(pode: ProveODE): AngelStrategy = {
    val tv = pode.timeVar.getOrElse(Variable("t"))
    val assignT = pode.duration match {
      case Some((_, f)) => DAssign(tv, f)
      case None => NDAssign(tv)
    }
    val coll = pode.dc.collect
    val assms = (coll.assumptions.toList.map(_.f)).reduceRight[Formula](And)
    val invs = (coll.assumptions.toList.map(_.f) ++ coll.assertions.map(_.f)).reduceRight[Formula](And)
    pode.solutions match {
      case None =>
        val assignX = pode.ds.atoms.map(_.dp.xp.x).toList.map(NDAssign)
        val assignDX = pode.ds.atoms.map(_.dp).toList.map({ case AtomicODE(xp, e) => DAssign(xp, e) })
        val conds = pode.timeVar match {
          case Some(t) if !pode.isAngelic => And(GreaterEqual(t, Number(0)), invs)
          case _ => invs
        }
        Composed(assignT :: (assignX ++ assignDX.+:(DTest(conds))))
      case Some(xfs) =>
        val setT = Composed(NDAssign(tv), DTest(GreaterEqual(tv, Number(0))))
        // @TODO: Should test all 0 <= s <= T  but c'est la vie
        val dc = DTest(if (pode.isAngelic) assms else invs)
        val solAssign = Composed(xfs.map({ case (x, f) => DAssign(x, f) }))
        Composed(setT :: dc :: solAssign :: Nil)
    }
  }

  /** Main translation pass from Kaisar to strategies */
  private def body(pf: Statement, isPhi: Boolean): AngelStrategy = {
    pf match {
      case Assume(pat, f) => DTest(f)
      case BoxChoice(left, right) => Composed(body(left, isPhi), body(right, isPhi))
      case InverseGhost(s) => body(s, isPhi)
      case Modify(ids, mods) =>
        Composed(mods.map({
          case (x, None) => NDAssign(x)
          case (x, Some(f)) =>
            val res = DAssign(x, f)
            if(isPhi)
              IDCounter.setOriginal(res.nodeID, DTest(True))
            res
        }))
      case Block(ss) => Composed(ss.map(body(_, isPhi)))
      case Switch(scrutinee, pats) => ASwitch(pats.map({ case (x, f, b) => (f, body(b, isPhi)) }))
      case While(x, j, s) => ALoop(j, body(s, isPhi))
      case BoxLoop(s, ih) => DLoop(body(s, isPhi))
      case pode: ProveODE =>
        val ode = ofODE(pode)
        // ODE does not have an "original" strategy, but we put it in map to indicate that it "was once an ODE"
        //if (pode.isAngelic)
        IDCounter.setOriginal(ode.nodeID, ode)
        ode
      case Phi(s) =>
        val block = body(s, isPhi = true)
        // Phi block does not have an "original" strategy, but we put it in map to indicate that it "is special"
        block
      case _: MetaNode | _: Note | _: Match | _: LetSym | _: Triv | _: Assert | _: Label | _: Ghost => DTest(True)
    }
  }

  /** Extract executable (Angelic) strategy from a (weak-test) Kaisar proof */
  def apply(pf: Statement): AngelStrategy = {
    val fv = VariableSets(pf).freeVars
    val main = body(pf, isPhi = false)
    val inits = fv.toList.map(NDAssign)
    val strat = Composed(inits.:+(main))
    strat
  }
}