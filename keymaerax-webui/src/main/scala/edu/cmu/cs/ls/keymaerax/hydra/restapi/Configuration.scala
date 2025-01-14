/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.restapi

import akka.http.scaladsl.server.Route
import spray.json._
import akka.http.scaladsl.server.Directives._
import edu.cmu.cs.ls.keymaerax.hydra.RestApi.{completeRequest, database}
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.hydra.requests.configuration._

import scala.language.postfixOps

object Configuration {

  val kyxConfig: Route = path("kyxConfig") {
    pathEnd {
      get {
        val request = new KyxConfigRequest
        completeRequest(request, EmptyToken())
      }
    }
  }

  val keymaeraXVersion: Route = path("keymaeraXVersion") {
    pathEnd {
      get {
        val request = new KeymaeraXVersionRequest()
        completeRequest(request, EmptyToken())
      }
    }
  }

  val mathConfSuggestion: Route = path("config" / "mathematica" / "suggest") {
    pathEnd {
      get {
        val request = new GetMathematicaConfigSuggestionRequest(database)
        completeRequest(request, EmptyToken())
      }
    }
  }

  val wolframEngineConfSuggestion: Route = path("config" / "wolframengine" / "suggest") {
    pathEnd {
      get {
        val request = new GetWolframEngineConfigSuggestionRequest(database)
        completeRequest(request, EmptyToken())
      }
    }
  }

  val wolframScriptConfSuggestion: Route = path("config" / "wolframscript" / "suggest") {
    pathEnd {
      get {
        val request = new GetWolframScriptConfigSuggestionRequest
        completeRequest(request, EmptyToken())
      }
    }
  }

  val z3ConfSuggestion: Route = path("config" / "z3" / "suggest") {
    pathEnd {
      get {
        completeRequest(new GetZ3ConfigSuggestionRequest(), EmptyToken())
      }
    }
  }

  val tool: Route = path("config" / "tool") {
    pathEnd {
      get {
        edu.cmu.cs.ls.keymaerax.Configuration(edu.cmu.cs.ls.keymaerax.Configuration.Keys.QE_TOOL) match {
          case "mathematica" => completeRequest(new MathematicaConfigStatusRequest(database), EmptyToken())
          case "wolframengine" => completeRequest(new WolframEngineConfigStatusRequest(database), EmptyToken())
          case "wolframscript" => completeRequest(new WolframScriptConfigStatusRequest, EmptyToken())
          case "z3" => completeRequest(new Z3ConfigStatusRequest, EmptyToken())
        }
      } ~
        post {
          entity(as[String]) { tool =>
            val request = new SetToolRequest(database, tool)
            completeRequest(request, EmptyToken())
          }
        }
    }
  }

  private def completeWolframMathematicaRequest(params: String, toolName: String) = {
    val p = JsonParser(params).asJsObject.fields.map(param => param._1 -> param._2.asInstanceOf[JsString].value)
    assert(p.contains("linkName"), "linkName not in: " + p.keys.toString())
    assert(p.contains("jlinkLibDir"), "jlinkLibDir not in: " + p.keys.toString()) //@todo These are schema violations and should be checked as such, but I needed to disable the validator.
    assert(p.contains("jlinkTcpip"), "jlinkTcpip not in: " + p.keys.toString())
    val linkName: String = p("linkName")
    val jlinkLibDir: String = p("jlinkLibDir")
    val jlinkTcpip: String = p("jlinkTcpip")
    val request = new ConfigureMathematicaRequest(toolName, linkName, jlinkLibDir, jlinkTcpip)
    completeRequest(request, EmptyToken())
  }

  val mathematicaConfig: Route = path("config" / "mathematica") {
    pathEnd {
      get {
        val request = new GetMathematicaConfigurationRequest(database, "mathematica")
        completeRequest(request, EmptyToken())
      } ~
        post {
          entity(as[String]) { completeWolframMathematicaRequest(_, "mathematica")
        }}
    }
  }

  val wolframEngineConfig: Route = path("config" / "wolframengine") {
    pathEnd {
      get {
        val request = new GetMathematicaConfigurationRequest(database, "wolframengine")
        completeRequest(request, EmptyToken())
      } ~
        post {
          entity(as[String]) { completeWolframMathematicaRequest(_, "wolframengine")
        }}
    }
  }

  val z3Config: Route = path("config" / "z3") {
    pathEnd {
      get {
        completeRequest(new GetZ3ConfigurationRequest(), EmptyToken())
      } ~
        post {
          entity(as[String]) { params => {
            val p = JsonParser(params).asJsObject.fields.map(param => param._1 -> param._2.asInstanceOf[JsString].value)
            assert(p.contains("z3Path"), "z3 path not in: " + p.keys.toString())
            val z3Path: String = p("z3Path")
            completeRequest(new ConfigureZ3Request(z3Path), EmptyToken())
          }}
        }
    }
  }

  val fullConfig: Route = path("config" / "fullContent") {
    pathEnd {
      get {
        completeRequest(new GetFullConfigRequest(), EmptyToken())
      } ~
        post {
          entity(as[String]) { params => {
            val content = params.parseJson.asJsObject.fields("content") match { case JsString(s) => s }
            completeRequest(new SaveFullConfigRequest(content), EmptyToken())
          }}
        }
    }
  }

  val systemInfo: Route = path("config" / "systeminfo") {
    pathEnd {
      get {
        completeRequest(new SystemInfoRequest(database), EmptyToken())
      }
    }
  }

  val licenses: Route = path("licenses") {
    pathEnd {
      get {
        completeRequest(new LicensesRequest(), EmptyToken())
      }
    }
  }

  val isLocal: Route = path("isLocal") { pathEnd { get {
    implicit val sessionUser = None
    completeRequest(new IsLocalInstanceRequest(), EmptyToken())
  }}}

  val shutdown: Route = path("shutdown") { pathEnd { get {
    implicit val sessionUser = None
    completeRequest(new ShutdownRequest(), EmptyToken())
  }}}

  val extractdb: Route = path("extractdb") { pathEnd { post {
    implicit val sessionUser = None
    completeRequest(new ExtractDatabaseRequest(), EmptyToken())
  }}}

  val hotkeys: Route = path("hotkeys") {
    pathEnd {
      get {
        completeRequest(new HotkeysRequest(), EmptyToken())
      }
    }
  }

}
