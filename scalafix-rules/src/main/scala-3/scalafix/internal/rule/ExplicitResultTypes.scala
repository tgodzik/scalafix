package scalafix.internal.rule

import scala.meta.*

import metaconfig.Configured
import scalafix.internal.pc.ExplicitResultTypesFallback
import scalafix.patch.Patch
import scalafix.v1.*

final class ExplicitResultTypes(
    val config: ExplicitResultTypesConfig,
    fallback: Option[ExplicitResultTypesFallback]
) extends SemanticRule("ExplicitResultTypes")
    with ExplicitResultTypesBase[Scala3Printer] {

  def this() = this(ExplicitResultTypesConfig.default, None)

  override def description: String =
    "Inserts type annotations for inferred public members."

  override def isRewrite: Boolean = true

  override def afterComplete(): Unit = {
    shutdownCompiler()
  }

  private def shutdownCompiler(): Unit = {
    fallback.foreach(_.shutdownCompiler())
  }

  override def withConfiguration(config: Configuration): Configured[Rule] = {
    config.conf // Support deprecated explicitReturnTypes config
      .getOrElse("explicitReturnTypes", "ExplicitResultTypes")(
        ExplicitResultTypesConfig.default
      )
      .map(c =>
        new ExplicitResultTypes(c, Option(ExplicitResultTypesFallback(config)))
      )
  }

  override def fix(implicit ctx: SemanticDocument): Patch =
    try {
      implicit val printer = new Scala3Printer(fallback)
      unsafeFix()
    } catch {
      case _: Throwable if !config.fatalWarnings =>
        Patch.empty
    }

}

class Scala3Printer(
    fallback: Option[ExplicitResultTypesFallback]
) extends Printer {

  def defnType(
      defn: Defn,
      replace: Token,
      space: String
  )(implicit
      ctx: SemanticDocument
  ): Option[Patch] = {
    fallback.flatMap(_.defnType(replace))
  }
}
