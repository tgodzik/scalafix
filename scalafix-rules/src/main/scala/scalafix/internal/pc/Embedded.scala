package scalafix.internal.pc

import java.net.URLClassLoader
import java.nio.file.Path
import java.util.ServiceLoader

import scala.jdk.CollectionConverters._

import scala.meta.pc.PresentationCompiler

import coursierapi.Dependency
import coursierapi.Fetch
import coursierapi.MavenRepository

object Embedded {

  def presentationCompiler(
      scalaVersion: String
  ): PresentationCompiler = {
    val deps =
      scala3PresentationCompilerDependencies(scalaVersion)
    val jars = Fetch
      .create()
      .addDependencies(deps:_*)
      .addRepositories(
        MavenRepository.of(
          "https://oss.sonatype.org/content/repositories/snapshots"
        )
      )
      .fetch()
      .asScala
      .map(_.toPath())
      .toSeq
    val classloader = newPresentationCompilerClassLoader(jars)

    val presentationCompilerClassname =
      if (supportPresentationCompilerInDotty(scalaVersion)) {
        "dotty.tools.pc.ScalaPresentationCompiler"
      } else {
        "scala.meta.pc.ScalaPresentationCompiler"
      }

    serviceLoader(
      classOf[PresentationCompiler],
      presentationCompilerClassname,
      classloader
    )
  }

  private def supportPresentationCompilerInDotty(scalaVersion: String) = {
    scalaVersion.split("\\.").take(3).map(_.toInt) match {
      case Array(3, minor, patch) => minor > 3 || minor == 3 && patch >= 4
      case _ => false
    }
  }

  private def scala3PresentationCompilerDependencies(version: String) =
    if (supportPresentationCompilerInDotty(version))
      List(
        Dependency
          .of("org.scala-lang", "scala3-presentation-compiler_3", version)
      )
    else
      List(
        // TODO should use build info etc. instead of using 1.3.4
        Dependency.of("org.scalameta", s"mtags_${version}", "1.3.4")
      )

  private def serviceLoader[T](
      cls: Class[T],
      className: String,
      classloader: URLClassLoader
  ): T = {
    val services = ServiceLoader.load(cls, classloader).iterator()
    if (services.hasNext) services.next()
    else {
      val cls = classloader.loadClass(className)
      val ctor = cls.getDeclaredConstructor()
      ctor.setAccessible(true)
      ctor.newInstance().asInstanceOf[T]
    }
  }

  private def newPresentationCompilerClassLoader(
      jars: Seq[Path]
  ): URLClassLoader = {
    val allJars = jars.iterator
    val allURLs = allJars.map(_.toUri.toURL).toArray
    // Share classloader for a subset of types.
    val parent =
      new scalafix.internal.pc.PresentationCompilerClassLoader(this.getClass.getClassLoader)
    new URLClassLoader(allURLs, parent)
  }
}
