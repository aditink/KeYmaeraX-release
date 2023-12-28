/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.OptionMap
import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, ParsedArchiveEntry}
import edu.cmu.cs.ls.keymaerax.tools.ext.Mathematica
import edu.cmu.cs.ls.keymaerax.tools.ext.ceasar.Cesar

import java.nio.file._
import java.nio.file.attribute.BasicFileAttributes
import scala.collection.immutable.{List, Nil}
import scala.collection.mutable.ListBuffer

/** CESAR Synthesis command-line interface implementation. */
object CesarCli {

  /** Identical to KeymaeraXProofChecker. Extract? */
  private def findFiles(fileName: String): List[Path] = {
    // specific file, no wildcard support when referring to a specific entry
    if (new java.io.File(fileName).exists || fileName.contains("#")) Paths.get(fileName).toAbsolutePath :: Nil
    else {
      val path = Paths.get(fileName).toAbsolutePath
      val dir = path.getParent
      val pattern = path.getFileName
      val files: ListBuffer[Path] = new ListBuffer[Path]()
      print("Looking for files: "+files)
      val finder = new SimpleFileVisitor[Path] {
        private val matcher = FileSystems.getDefault.getPathMatcher("glob:" + pattern)
        override def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult = {
          if (matcher.matches(file.getFileName)) files.append(file)
          FileVisitResult.CONTINUE
        }
      }
      Files.walkFileTree(dir, finder)
      files.toList
    }
  }

  /** Calls the cesar tool synthesize. */
  def synthesize(options: OptionMap, usage: String): List[Formula] = {
    require(options.contains('in), usage)
    val inputFileName = options('in).toString
    val inFiles = {
      findFiles(inputFileName)
    }
    val archiveContent = inFiles.map(p => p -> ArchiveParser.parseFromFile(p.toFile.getAbsolutePath).filterNot(_.isExercise))
    val outFilePath = options.get('out) match {
      case Some(out) => Paths.get(out.toString)
      case None => Paths.get("cesar_" + inputFileName)
    }
    val unrollingNumber = options.getOrElse('bound, "0").toString.toInt

    def synthesize(l:List[ParsedArchiveEntry]): List[Formula] = {
      l.map(e => {
        // Get a Mathematica tool.
        val tool = ToolProvider.defaultTool()
        if (!tool.isInstanceOf[Some[Mathematica]]) {
          throw new Exception("CESAR requires Mathematica")
        }
        val mathematica = tool.get.asInstanceOf[Mathematica]

        if (!e.model.isInstanceOf[Formula]) {
          throw new Exception("Expected formula as input but got "+e.model.prettyString)
        }
        val cesar = new Cesar(mathematica, e.model.asInstanceOf[Formula], n = unrollingNumber, allowSimplify = true, allowEgg = false)
        val (resultFml, _) = cesar.resultFormula
        // Write results to file of the form cesar_<formula>.kyx.
        val outFile = outFilePath.toFile
        outFile.createNewFile() // if file already exists will do nothing
        val out = new java.io.PrintWriter(outFile)
        out.println("ArchiveEntry \"" + e.name + "\"")
        out.println("Problem\n" + resultFml.prettyString)
        out.println("End.\n")
        out.println("End.\n")
        out.close()
        resultFml
      })
    }

    archiveContent.flatMap(p => synthesize(p._2))
  }
}