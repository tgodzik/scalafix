package scalafix.internal.rule

import java.net.URI
import java.nio.file.Paths
import java.util.concurrent.CompletableFuture
import java.util.concurrent.CompletionStage

import scala.jdk.CollectionConverters.*
import scala.util.Random
import scala.util.Try

import scala.meta.*
import scala.meta.contrib.*
import scala.meta.inputs.Input.File
import scala.meta.inputs.Input.VirtualFile
import scala.meta.pc.CancelToken
import scala.meta.pc.OffsetParams
import scala.meta.pc.PresentationCompiler
import scala.meta.trees.Origin.DialectOnly
import scala.meta.trees.Origin.Parsed

import buildinfo.RulesBuildInfo
import metaconfig.Configured
import scalafix.internal.v1.LazyValue
import scalafix.patch.Patch
import scalafix.patch.Patch.empty
import scalafix.util.TokenOps
import scalafix.v1.*

final class ExplicitResultTypes(
    config: ExplicitResultTypesConfig,
    pc: LazyValue[Option[PresentationCompiler]]
) extends SemanticRule("ExplicitResultTypes") {

  def this() = this(ExplicitResultTypesConfig.default, LazyValue.now(None))

  val compilerScalaVersion: String = RulesBuildInfo.scalaVersion

  private def toBinaryVersion(v: String) =
    if (v.startsWith("3.")) "3"
    else v.split('.').take(2).mkString(".")

  override def description: String =
    "Inserts type annotations for inferred public members."

  override def isRewrite: Boolean = true

  override def afterComplete(): Unit = {
    shutdownCompiler()
  }

  private def shutdownCompiler(): Unit = {}

  override def withConfiguration(config: Configuration): Configured[Rule] = {
    val symbolReplacements =
      config.conf.dynamic.ExplicitResultTypes.symbolReplacements
        .as[Map[String, String]]
        .getOrElse(Map.empty)
    val inputBinaryScalaVersion =
      toBinaryVersion(config.scalaVersion)
    val runtimeBinaryScalaVersion =
      toBinaryVersion(compilerScalaVersion)

    if (
      config.scalacClasspath.nonEmpty && inputBinaryScalaVersion != runtimeBinaryScalaVersion
    ) {
      Configured.error(
        s"The ExplicitResultTypes was run with ${runtimeBinaryScalaVersion}, " +
          s"this rule needs to run with the same Scala binary version as the one used to compile target sources ($inputBinaryScalaVersion). " +
          s"To fix this problem, either remove ExplicitResultTypes from .scalafix.conf or make sure Scalafix is loaded with $inputBinaryScalaVersion."
      )
    } else {
      val newPc: LazyValue[Option[PresentationCompiler]] =
        LazyValue.from { () =>
          Try(
            Embedded
              .presentationCompiler(config.scalaVersion)
              .withConfiguration(
                new PresentationCompilerConfigImpl(
                  symbolPrefixes = symbolReplacements.asJava
                )
              )
              .newInstance(
                this.name.toString,
                config.scalacClasspath.map(_.toNIO).asJava,
                // getting assertion errors if included
                config.scalacOptions.filter(!_.contains("-release")).asJava
              )
          )
        }
      config.conf // Support deprecated explicitReturnTypes config
        .getOrElse("explicitReturnTypes", "ExplicitResultTypes")(
          ExplicitResultTypesConfig.default
        )
        .map(c => new ExplicitResultTypes(c, newPc))
    }
  }

  override def fix(implicit ctx: SemanticDocument): Patch =
    try unsafeFix()
    catch {
      case _: Throwable if !config.fatalWarnings =>
        Patch.empty
    }

  def unsafeFix()(implicit ctx: SemanticDocument): Patch = {
    ctx.tree.collect {
      case t @ Defn.Val(mods, Pat.Var(name) :: Nil, None, body)
          if isRuleCandidate(t, name, mods, body) =>
        fixDefinition(t, body)

      case t @ Defn.Var(mods, Pat.Var(name) :: Nil, None, Some(body))
          if isRuleCandidate(t, name, mods, body) =>
        fixDefinition(t, body)

      case t @ Defn.Def(mods, name, _, _, None, body)
          if isRuleCandidate(t, name, mods, body) =>
        fixDefinition(t, body)
    }.asPatch
  }

  // Don't explicitly annotate vals when the right-hand body is a single call
  // to `implicitly` or `summon`. Prevents ambiguous implicit. Not annotating in such cases,
  // this a common trick employed implicit-heavy code to workaround SI-2712.
  // Context: https://gitter.im/typelevel/cats?at=584573151eb3d648695b4a50
  private def isImplicitly(term: Term): Boolean = term match {
    case Term.ApplyType(Term.Name("implicitly"), _) => true
    case Term.ApplyType(Term.Name("summon"), _) => true
    case _ => false
  }

  def defnName(defn: Defn): Option[Name] = Option(defn).collect {
    case Defn.Val(_, Pat.Var(name) :: Nil, _, _) => name
    case Defn.Var(_, Pat.Var(name) :: Nil, _, _) => name
    case Defn.Def(_, name, _, _, _, _) => name
  }

  def defnBody(defn: Defn): Option[Term] = Option(defn).collect {
    case Defn.Val(_, _, _, term) => term
    case Defn.Var(_, _, _, Some(term)) => term
    case Defn.Def(_, _, _, _, _, term) => term
  }

  def visibility(mods: Iterable[Mod]): MemberVisibility =
    mods
      .collectFirst {
        case _: Mod.Private => MemberVisibility.Private
        case _: Mod.Protected => MemberVisibility.Protected
      }
      .getOrElse(MemberVisibility.Public)

  def kind(defn: Defn): Option[MemberKind] = Option(defn).collect {
    case _: Defn.Val => MemberKind.Val
    case _: Defn.Def => MemberKind.Def
    case _: Defn.Var => MemberKind.Var
  }

  def isRuleCandidate[D <: Defn](
      defn: D,
      nm: Name,
      mods: Iterable[Mod],
      body: Term
  )(implicit ev: Extract[D, Mod], ctx: SemanticDocument): Boolean = {
    import config._

    def matchesMemberVisibility(): Boolean =
      memberVisibility.contains(visibility(mods))

    def matchesMemberKind(): Boolean =
      kind(defn).exists(memberKind.contains)

    def isFinalLiteralVal: Boolean =
      defn.is[Defn.Val] &&
        mods.exists(_.is[Mod.Final]) &&
        body.is[Lit]

    def matchesSimpleDefinition(): Boolean =
      config.skipSimpleDefinitions.isSimpleDefinition(body)

    def isImplicit: Boolean = false
    defn.hasMod(Mod.Implicit()) && !isImplicitly(body)

    def hasParentWihTemplate: Boolean =
      defn.parent.exists(_.is[Template])

    def qualifyingImplicit: Boolean =
      isImplicit && !isFinalLiteralVal

    def matchesConfig: Boolean =
      matchesMemberKind() && matchesMemberVisibility() && !matchesSimpleDefinition()

    def qualifyingNonImplicit: Boolean = {
      !onlyImplicits &&
      hasParentWihTemplate &&
      !defn.hasMod(Mod.Implicit())
    }

    matchesConfig && {
      qualifyingImplicit || qualifyingNonImplicit
    }
  }

  def defnType(
      defn: Defn,
      replace: Token,
      space: String
  )(implicit
      ctx: SemanticDocument
  ): Option[Patch] =
    for {
      name <- defnName(defn)
      defnSymbol <- name.symbol.asNonEmpty
      pc <- pc.value
    } yield {
      ctx.tree.origin match
        case _: DialectOnly => empty
        case scala.meta.trees.Origin.None => empty
        case parsed: Parsed =>
          val text = parsed.source.input.text
          val uri = parsed.source.input match
            // case Ammonite(input) =>
            case File(path, _) => path.toURI
            case VirtualFile(path, _) => Paths.get(path).toUri()
            case _ => Paths.get(s"./A${Random.nextInt()}.scala").toUri()
          val params = new CompilerOffsetParams(
            uri,
            text,
            replace.pos.end
          )
          val result = pc.insertInferredType(params).get()
          result.asScala.toList
            .map { edit =>
              val start = edit.getRange().getStart()
              val last = ctx.tokens.tokens.takeWhile { token =>
                val beforeLine = token.pos.endLine < start.getLine()
                val beforeColumn = token.pos.endLine == start
                  .getLine() && token.pos.endColumn <= start.getCharacter()
                beforeLine || beforeColumn

              }.last
              Patch.addRight(last, edit.getNewText())
            }
            .reduce { case (p1, p2) =>
              p1 + p2
            }

    }

  def fixDefinition(defn: Defn, body: Term)(implicit
      ctx: SemanticDocument
  ): Patch = {
    val lst = ctx.tokenList
    // val option = SymbolMatcher.exact("scala/Option.")
    // val list = SymbolMatcher.exact(
    //   "scala/package.List.",
    //   "scala/collection/immutable/List."
    // )
    // val seq = SymbolMatcher.exact(
    //   "scala/package.Seq.",
    //   "scala/collection/Seq.",
    //   "scala/collection/immutable/Seq."
    // )
    // def patchEmptyValue(term: Term): Patch = {
    //   term match {
    //     // case q"${option(_)}.empty[$_]" =>
    //     //   Patch.replaceTree(term, "None")
    //     // case q"${list(_)}.empty[$_]" =>
    //     //   Patch.replaceTree(term, "Nil")
    //     // case q"${seq(_)}.empty[$_]" =>
    //     //   Patch.replaceTree(term, "Nil")
    //     case _ =>
    //       Patch.empty
    //   }
    // }
    def patchEmptyValue(term: Term): Patch = Patch.empty
    import lst._
    for {
      start <- defn.tokens.headOption
      end <- body.tokens.headOption
      // Left-hand side tokens in definition.
      // Example: `val x = ` from `val x = rhs.banana`
      lhsTokens = slice(start, end)
      replace <- lhsTokens.reverseIterator.find(x =>
        !x.is[Token.Equals] && !x.is[Trivia]
      )
      space = {
        if (TokenOps.needsLeadingSpaceBeforeColon(replace)) " "
        else ""
      }
      typePatch <- defnType(defn, replace, space)
      valuePatchOpt = defnBody(defn).map(patchEmptyValue)
    } yield typePatch + valuePatchOpt
  }.asPatch.atomic

  case class CompilerOffsetParams(
      uri: URI,
      text: String,
      offset: Int
  ) extends OffsetParams {

    override def token(): CancelToken = new CancelToken {

      override def checkCanceled(): Unit = ()

      override def onCancel(): CompletionStage[java.lang.Boolean] =
        CompletableFuture.completedFuture(java.lang.Boolean.FALSE)

    }

  }
}
