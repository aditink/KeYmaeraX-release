/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Check full Kaisar file which can contain, e.g., multiple models / proofs / declarations
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{Ident, ProofCheckException}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.StandardLibrary._
import edu.cmu.cs.ls.keymaerax.core._

object FileChecker {
  /** Context is list of declarations already checked */
  type FileContext = List[KaisarDecl]

  /** Look up result of previous proof */
  private def getTheorem(kc: FileContext, name: Ident): Option[(Statement, Formula)] = {
    kc.flatMap({case td: TheoremDecl => if(td.name == name) List(td) else Nil case _ => Nil}).
      map(td => (td.pf, td.conclusion)).headOption
  }

  /** Convert file-level context to proof-level context for individual proof checking */
  private def toProofContext(kc: FileContext): Context = {
    val ss: List[Statement] = kc.flatMap({ case ld: LetDecl => List(ld.ls) case _ => Nil})
    ss.foldLeft(Context.empty)(_.:+(_))
  }

  /** Check declarations in context */
  def apply(kc: FileContext, file: List[KaisarDecl]): Unit = {
    file match {
      case Nil =>
      case Decls(dcls) :: decls => apply(kc, dcls ++ decls)
      case decl :: decls =>
        val newDecls: List[KaisarDecl] =
          decl match {
            case PragmaDecl(pd) => Pragma.apply(pd); Nil
            case ld: LetDecl => // @TODO: check admissibility
              List(ld)
            case TheoremDecl(name, pf, _conclusion) =>
              val proofCon = toProofContext(kc)
              val (outCon, cncl) = ProofChecker(proofCon, pf)
              List(TheoremDecl(name, pf, cncl))
            case ProvesDecl(thmName, conclusion) =>
              // @TODO: Elaborate conclusion, apply SSA
              getTheorem(kc, thmName) match {
                case None => throw ProofCheckException("Couldn't find theorem named " + thmName)
                case Some((pf, _fml)) =>
                  val Box(a, p) = asBox(conclusion)
                  RefinementChecker(pf, a);
                  Nil
              }
            case ConclusionDecl(thmName) =>
              getTheorem(kc, thmName) match {
                case None => throw ProofCheckException("Couldn't find theorem named " + thmName)
                case Some((_pf, fml)) =>
                  println(s"Printing conclusion of theorem $thmName:\n" + fml.prettyString)
                  Nil
              }
            case SynthesizeDecl(thmName) =>
              getTheorem(kc, thmName) match {
                case None => throw ProofCheckException("Couldn't find theorem named " + thmName)
                case Some((pf, _fml)) =>
                  // @TODO: Pretty-printer for strategies, or add command that executes them.
                  val strat = SimpleStrategy(AngelStrategy(pf))
                  println(s"Printing strategy synthesized from theorem $thmName:\n" + strat)
                  Nil
              }
          }
        apply(kc ++ newDecls, decls)
    }
  }

  /** Entry point */
  def apply(decl: Decls): Unit = {
    apply(Nil, decl.dcls)
  }
}
