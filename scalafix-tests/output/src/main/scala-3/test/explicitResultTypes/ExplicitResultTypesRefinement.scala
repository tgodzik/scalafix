package test.explicitResultTypes

import java.io.Serializable
import scala.language.reflectiveCalls

object ExplicitResultTypesRefinement {
  val field: field = new field
  class field extends Serializable {
    val results: List[Int] = List(1)
  }
  val conflict: conflict2 = new conflict2
  class conflict2 extends Serializable {
    val results: List[Int] = List(1)
  }
  class conflict
  class conflict1
  def method(param: Int): method = new method(param)
  class method(param: Int) extends Serializable {
    val results: List[Int] = List(param)
  }
  def method(param: String): method1 = new method1(param)
  class method1(param: String) extends Serializable {
    val results: List[String] = List(param)
  }
  def curried(param: Int)(param2: Int, param3: String): curried = new curried(param)(param2, param3)
  class curried(param: Int)(param2: Int, param3: String) extends Serializable {
    val results: List[Int] = List(param2, param3.length(), param)
  }
  def tparam[T <: CharSequence](e: T): tparam[T] = new tparam[T](e)
  class tparam[T <: CharSequence](e: T) extends Serializable {
    val results: List[Int] = List(e.length())
  }
  val access: Serializable = new Serializable {
    private val results: List[Int] = List.empty
    protected val results2: List[Int] = List.empty
  }
  val product: Product = new Product {
    override def productArity: Int = ???
    override def productElement(n: Int): Any = ???
    override def canEqual(that: Any): Boolean = ???
  }
  val productWithSerializable: Product with Serializable = new Product with Serializable {
    override def productArity: Int = ???
    override def productElement(n: Int): Any = ???
    override def canEqual(that: Any): Boolean = ???
  }
  val test: conflict = new conflict with Product with Serializable {
    override def productArity: Int = ???
    override def productElement(n: Int): Any = ???
    override def canEqual(that: Any): Boolean = ???
  }
  trait Chars { def chars: CharSequence }
  val chars: Chars = new Chars {
    val chars = 42.toString()
  }
  def app(): Unit = {
    println(field.results)
    println(method(42).results)
  }
}
