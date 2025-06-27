package scalafix.internal.rule

import scala.meta._

import scalafix.v1._

class RemoveUnnecessaryNn extends SemanticRule("RemoveUnnecessaryNn") {

  override def description: String =
    "Removes unnecessary .nn calls when the compiler reports they are not needed"
  override def isRewrite: Boolean = true

  override def fix(implicit doc: SemanticDocument): Patch = {
    val unnecessaryNnCalls: Set[Position] =
      doc.diagnostics.collect {
        case message
            if message.message.contains("unnecessary") && 
               message.message.contains(".nn") =>
          message.position
      }.toSet

    doc.tree
      .collect {
        case Term.Select(expr, Term.Name("nn")) 
            if unnecessaryNnCalls.exists(pos => 
              pos.start <= expr.pos.start && expr.pos.end <= pos.end
            ) =>
          Patch.replaceTree(Term.Select(expr, Term.Name("nn")), expr.syntax)
      }
      .map(_.atomic)
      .asPatch
  }
} 