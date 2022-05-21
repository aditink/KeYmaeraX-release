package edu.cmu.cs.ls.keymaerax.parser

/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
import edu.cmu.cs.ls.keymaerax.bellerophon.{Cancellable, LazySequentialInterpreter, ReflectiveExpressionBuilder}
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import org.scalatest._
import org.scalamock.scalatest.MockFactory

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BellePrettyPrinter, DLBelleParser}
import edu.cmu.cs.ls.keymaerax.btactics.FixedGenerator

import scala.collection.immutable._

class ParserErrorTests extends FlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll with MockFactory {
  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "false",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName
    ))
  }
  override def afterEach(): Unit = { Parser.parser.setAnnotationListener((_, _) => {}) }

  // General goal:
  // Expected: "human-readable message, not necessarily most detailed/accurate follow sets"
  // Found: "the error found"
  // Hint: "Try (detailed follow set generated by parser library)"

  "dL parser" should "report missing problem" in {
    val archiveParser = new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _)))
    val input =
      """
        |ArchiveEntry "fo"
        |End.
      """.stripMargin
    try {
      archiveParser.parse(input)
    }
    catch {
      case e: ParseException => {
        println("Expected: ",e.expect)
        println("Found: ",e.found)
        println("Hint: ",e.hint)
        e.expect shouldBe "\"Problem\" at 3:1"
        e.found shouldBe "\"End.\\n     \""
        e.hint shouldBe "Try (\"Description\" | \"Title\" | \"Link\" | \"Author\" | \"See\" | programVariables | definitions | \"Problem\")"
      }
    }
  }

  // TODO
  it should "bad start of entry" in {
    val archiveParser = new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _)))
    val input =
      """BadEntry
        |End.
      """.stripMargin
    try {
      archiveParser.parse(input)
    }
    catch {
      case e: ParseException => {
        e.expect shouldBe "Start of ArchiveEntry at 1:1"
        e.found shouldBe "\"BadEntry\\nE\""
        e.hint shouldBe "Try (sharedDefinitions | \"ArchiveEntry\" | \"Lemma\" | \"Theorem\" | \"Exercise\")"
      }
    }
  }

  // TODO is this still a required feature?
  it should "mismatched start and end label" in {
    val archiveParser = new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _)))
    val input =
      """ArchiveEntry asdf:"05: Short Bouncing Ball: single hop"
        |Problem
        |5=5
        |End.
        |End asd.
      """.stripMargin
    try {
      val entry = archiveParser.parse(input)
      println(entry)
    }
    catch {
      case e: ParseException => {
        println(e.expect)
        println(e.found)
        println(e.hint)
        e.expect shouldBe "end label: Some(asd) is optional but should be the same as the start label: Some(asdf) at 5:9"
        e.found shouldBe "\"\\n      \""
        e.hint shouldBe "Try: end label: Some(asd) is optional but should be the same as the start label: Some(asdf)"
      }
    }
  }

  it should "domain missing" in {
    val archiveParser = new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _)))
    val input =
      """ArchiveEntry "foo"
        |Problem
        |[{x'=x&x}]x>=0
        |End.
        |End.
      """.stripMargin
    try {
      val entry = archiveParser.parse(input)
      println(entry)
    }
    catch {
      case e: ParseException => {
        println(e.expect)
        println(e.found)
        println(e.hint)
        e.expect shouldBe "formula, but got term at 3:9"
        e.found shouldBe "\"}]x>=0\\nEnd\""
        // todo: maybe provide verbose suggestions here somehow??
        e.hint shouldBe "Try: >, < ... et"
      }
    }
  }

  it should "domain missing 2" in {
    val archiveParser = new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _)))
    val input =
      """ArchiveEntry "foo"
        |Problem
        |[{x'=x&}]x>=0
        |End.
        |End.
      """.stripMargin
    try {
      val entry = archiveParser.parse(input)
      println(entry)
    }
    catch {
      case e: ParseException => {
        println(e.expect)
        println(e.found)
        println(e.hint)
        e.expect shouldBe "formula at 3:9"
        e.found shouldBe "\"}]x>=0\\nEnd\""
        // todo: maybe provide verbose suggestions here somehow??
        e.hint shouldBe "Try: (\"true\" | \"false\" | \"\\\\forall\" | \"\\\\exists\" | \"[\" | \"<\" | \"!\" | predicational | ident | \"(\" | term)"
      }
    }
  }
}
