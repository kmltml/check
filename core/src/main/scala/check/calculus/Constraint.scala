package check
package calculus

sealed abstract class Constraint extends Product with Serializable {

  import Constraint._

  def reduce(consts: PartialFunction[String, PartialFunction[List[Term], Term]]): Constraint = this match {
    case Iden(a, b, o) => Iden(a.reduce(consts), b.reduce(consts), o)
  }

}

object Constraint {

  final case class Iden(a: Term, b: Term, origin: Term) extends Constraint

}
