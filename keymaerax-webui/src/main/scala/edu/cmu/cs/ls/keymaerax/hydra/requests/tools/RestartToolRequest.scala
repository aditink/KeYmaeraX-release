/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.tools

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, GenericOKResponse, LocalhostOnlyRequest, Response}
import edu.cmu.cs.ls.keymaerax.tools.Tool

import scala.collection.immutable.{List, Nil}

class RestartToolRequest(db: DBAbstraction, toolId: String) extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    ToolProvider.tool(toolId) match {
      case Some(t: Tool) =>
        t.restart()
        new GenericOKResponse :: Nil
      case _ => new ErrorResponse(s"Restarting failed: unknown tool '$toolId'. Please check the tool configuration.") :: Nil
    }

  }
}
