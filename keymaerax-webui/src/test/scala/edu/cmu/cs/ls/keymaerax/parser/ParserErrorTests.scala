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
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "true",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName
    ))
    Parser.setParser(DLParser)
    ArchiveParser.setParser(
      new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _)))
    )
  }
  override def afterEach(): Unit = { Parser.parser.setAnnotationListener((_, _) => {}) }

  // General goal:
  // Expected: "human-readable message, not necessarily most detailed/accurate follow sets"
  // Found: "the error found"
  // Hint: "Try (detailed follow set generated by parser library)"

  "dL parser" should "report expected term on rhs" in {
    val input = "(( (( f_() )) + #"
    val ex = the [ParseException] thrownBy Parser.parser.termParser(input)
    ex.msg should include("baseTerm")
  }

  it should "report expected term on rhs FROM FORMULA" in {
    val input = "(( (( f_() )) + #"
    val ex = the [ParseException] thrownBy Parser.parser.formulaParser(input)
    ex.msg should include("baseTerm")
  }

  "dL archive parser" should "report missing problem" in {
    val input =
      """
        |ArchiveEntry "fo"
        |End.
      """.stripMargin
    val e = the [ParseException] thrownBy ArchiveParser.parse(input)
    e.expect shouldBe "\"Problem\" at 3:1"
    e.found shouldBe "\"End.\\n     \""
    e.hint shouldBe "Try (\"Description\" | \"Title\" | \"Link\" | \"Author\" | \"See\" | programVariables | definitions | \"Problem\")"
  }

  it should "report wrong sort" in {
    val input =
      """
        |ArchiveEntry "foo"
        |Definitions
        |  R H;
        |End.
        |Problem
        |  H > 0
        |End.
        |End.
      """.stripMargin
    val e = the [ParseException] thrownBy ArchiveParser.parse(input)
    e.hint should include("Real")
  }

  // TODO
  it should "bad start of entry" in {
    val input =
      """BadEntry
        |End.
      """.stripMargin

    val e = the [ParseException] thrownBy ArchiveParser.parse(input)
    e.expect shouldBe "Start of ArchiveEntry at 1:1"
    e.found shouldBe "\"BadEntry\\nE\""
    e.hint shouldBe "Try (sharedDefinitions | \"ArchiveEntry\" | \"Lemma\" | \"Theorem\" | \"Exercise\")"
  }

  // TODO is this still a required feature?
  it should "mismatched start and end label" in {
    val input =
      """ArchiveEntry asdf:"05: Short Bouncing Ball: single hop"
        |Problem
        |5=5
        |End.
        |End asd.
      """.stripMargin
    val e = the [ParseException] thrownBy ArchiveParser.parse(input)
    e.expect shouldBe "end label: Some(asd) is optional but should be the same as the start label: Some(asdf) at 5:9"
    e.found shouldBe "\"\\n      \""
    e.hint shouldBe "Try: end label: Some(asd) is optional but should be the same as the start label: Some(asdf)"
  }

  it should "domain missing" in {
    val input =
      """ArchiveEntry "foo"
        |Problem
        |[{x'=x&x}]x>=0
        |End.
        |End.
      """.stripMargin
    val e = the [ParseException] thrownBy ArchiveParser.parse(input)
    e.expect shouldBe "formula, but got term at 3:9"
    e.found shouldBe "\"}]x>=0\\nEnd\""
    // todo: maybe provide verbose suggestions here somehow??
    e.hint shouldBe "Try: >, < ... et"
  }

  it should "domain missing 2" in {
    val input =
      """ArchiveEntry "foo"
        |Problem
        |[{x'=x&}]x>=0
        |End.
        |End.
      """.stripMargin
    val e = the [ParseException] thrownBy ArchiveParser.parse(input)
    e.expect shouldBe "formula at 3:9"
    e.found shouldBe "\"}]x>=0\\nEnd\""
    // todo: maybe provide verbose suggestions here somehow??
    e.hint shouldBe "Try (\"true\" | \"false\" | \"\\\\forall\" | \"\\\\exists\" | \"[\" | \"<\" | \"!\" | predicational | ident | \"(\" | term)"
  }

  it should "give correct error location for disallowed identifier" in {
    val input =
      """ArchiveEntry "foo"
        |Problem
        |5 < 5+ax__
        |End.
        |End.
      """.stripMargin
    val e = the [ParseException] thrownBy ArchiveParser.parse(input)
    print(e)
    e.expect shouldBe "term at 3:5"
    e.found shouldBe "\"ax__\\nEnd.\\n\""
    e.hint should include("ident")
  }

  it should "give correct error location for invalid formula extension" in {
    val input =
      """ArchiveEntry "foo"
        |Problem
        |x=5+a<5
        |End.
        |End.
      """.stripMargin
    val e = the [ParseException] thrownBy ArchiveParser.parse(input)
    //TODO: what to do?
    e.msg should include("End")
    e.expect shouldBe "problem at 3:4"
    e.found shouldBe "<5\\nEnd.\""
    e.hint should include("End")
  }

}