package check
package calculus

sealed abstract class Term extends Product with Serializable {

  import Term._

  def app(as: Term*): Term = App(this, as.toList)

  def ->:(nametyp: (String, Term)) = Pi(nametyp._1, nametyp._2, this)

  def prettyprint(variables: Int => String, precedence: Int = Precedence.Top): String = this match {
    case Var(i) => variables(i)
    case Meta(i) => s"?$i"
    case Nat(n) => n.toString
    case Const(name) => name
    case App(f, as) =>
      val s = as.foldLeft(f.prettyprint(variables, Precedence.App))(
        (s, t) => s"$s ${t.prettyprint(variables, Precedence.App - 1)}")
      parenthesize(Precedence.App, precedence, s)
    case Abs(_, _, _) =>
      def gather(t: Term, vars: Int => String, acc: String): String = t match {
        case Abs(n, t, b) =>
          val s = s"($n : ${t.prettyprint(vars, Precedence.Top)})"
          gather(b, prepend(n, vars), acc ++ s)

        case t => s"λ $acc → ${t.prettyprint(vars, Precedence.Abs)}"
      }
      parenthesize(Precedence.Abs, precedence, gather(this, variables, ""))
    case Pi(name, typ, result) =>
      def gatherOrdinary(t: Term, vars: Int => String, acc: String): Option[String] = t match {
        case Pi(n, t, r) if !r.freeVars.contains(0) =>
          gatherOrdinary(r, prepend(n, vars), acc ++ s"${t.prettyprint(vars, Precedence.Pi - 1)} → ")
        case Pi(_, _, _) => None
        case t => Some(s"$acc${t.prettyprint(vars, Precedence.Pi)}")
      }
      def gather(term: Term, vars: Int => String, acc: String): String = term match {
        case Pi(n, t, r) =>
          gatherOrdinary(term, vars, "") match {
            case Some(s) => if(acc.nonEmpty) s"Π $acc → $s" else s
            case None =>
              val s = s"($n : ${t.prettyprint(vars, Precedence.Top)})"
              gather(r, prepend(n, vars), acc ++ s)
          }
        case t => s"Π $acc → ${t.prettyprint(vars, Precedence.Pi)}"
      }
      parenthesize(Precedence.Pi, precedence, gather(this, variables, ""))
    case Type => "Type"
  }

  override def toString(): String = prettyprint(i => s"$$$i")

  def freeVars: Set[Int] = this match {
    case Var(i) => Set(i)
    case Const(_) | Type | Meta(_) => Set.empty
    case App(f, as) => f.freeVars ++ as.flatMap(_.freeVars)
    case Abs(_, t, b) => t.freeVars ++ (b.freeVars - 0).map(_ - 1)
    case Pi(_, t, r) => t.freeVars ++ (r.freeVars - 0).map(_ - 1)
  }

  def metas: Set[Meta] = this match {
    case Var(_) | Const(_) | Type => Set.empty
    case m: Meta => Set(m)
    case App(f, as) => f.metas ++ as.flatMap(_.metas)
    case Abs(_, t, b) => t.metas ++ b.metas
    case Pi(_, t, r) => t.metas ++ r.metas
  }

  def shift(amount: Int, cutoff: Int = 0): Term = this match {
    case Const(_) | Type | Meta(_) => this
    case Var(i) => if(i >= cutoff) Var(i + amount) else this
    case App(f, as) => App(f.shift(amount, cutoff), as.map(_.shift(amount, cutoff)))
    case Abs(n, t, b) => Abs(n, t.shift(amount, cutoff), b.shift(amount, cutoff + 1))
    case Pi(n, t, r) => Pi(n, t.shift(amount, cutoff), r.shift(amount, cutoff + 1))
  }

  def subst(substs: Map[Int, Term], depth: Int = 0): Term = this match {
    case Const(_) | Type | Meta(_) => this
    case Var(i) =>
      substs.get(i - depth).map(_.shift(depth)).getOrElse(this)
    case App(f, as) => App(f.subst(substs, depth), as.map(_.subst(substs, depth)))
    case Abs(n, t, b) => Abs(n, t.subst(substs, depth), b.subst(substs, depth + 1))
    case Pi(n, t, r) => Pi(n, t.subst(substs, depth), r.subst(substs, depth + 1))
  }

  def substMeta(substs: Map[Meta, Term], depth: Int = 0): Term = this match {
    case Const(_) | Type | Var(_) => this
    case m: Meta =>
      substs.get(m).getOrElse(this)
    case App(f, as) => App(f.substMeta(substs, depth), as.map(_.substMeta(substs, depth)))
    case Abs(n, t, b) => Abs(n, t.substMeta(substs, depth), b.substMeta(substs, depth + 1))
    case Pi(n, t, r) => Pi(n, t.substMeta(substs, depth), r.substMeta(substs, depth + 1))
  }

  def reduce(consts: PartialFunction[String, PartialFunction[List[Term], Term]]): Term = this match {
    case Const(c) => consts.lift(c).flatMap(_.lift(Nil)).getOrElse(this)
    case Type | Var(_) | Meta(_) => this
    case App(f, Nil) => f.reduce(consts)
    case App(App(f, as), bs) => App(f, as ++ bs).reduce(consts)
    case App(f, as) => App(f.reduce(consts), as.map(_.reduce(consts))).reduceHere(consts)
    case Abs(n, t, b) => Abs(n, t.reduce(consts), b.reduce(consts))
    case Pi(n, t, r) => Pi(n, t.reduce(consts), r.reduce(consts))
  }

  def reduceHere(consts: PartialFunction[String, PartialFunction[List[Term], Term]]): Term = this match {
    case App(Abs(_, _, b), a :: as) if b.metas.isEmpty =>
      App(b.subst(Map(0 -> a.shift(1))).shift(-1), as).reduce(consts)
    case App(Const(f), as) =>
      consts.lift(f).flatMap(_.lift(as)).map(_.reduce(consts)).getOrElse(this)
    case _ => this
  }

  def equiv(t: Term): Boolean = this == t || ((this, t) match {
    case (App(fa, aa), App(fb, ab)) =>
      (fa equiv fb) && aa.size == ab.size && (aa zip ab).forall { case (a, b) => a equiv b }
    case (Abs(_, ta, ba), Abs(_, tb, bb)) =>
      (ta equiv tb) && (ba equiv bb)
    case (Pi(_, ta, ra), Pi(_, tb, rb)) =>
      (ta equiv tb) && (ra equiv rb)
    case _ => false
  })

}

object Term {

  final case class Var(index: Int) extends Term
  final case class Meta(index: Int) extends Term
  final case class Const(name: String) extends Term
  final case class App(function: Term, arguments: List[Term]) extends Term
  final case class Abs(name: String, typ: Term, body: Term) extends Term
  final case class Pi(name: String, typ: Term, result: Term) extends Term
  case object Type extends Term


  private def prepend(v: String, f: Int => String)(i: Int) =
    if(i == 0) v else f(i - 1)

  private def parenthesize(here: Int, environment: Int, s: String): String =
    if(here > environment) s"($s)" else s

  def lambda(args: (String, Term)*)(body: Term): Term =
    args.foldRight(body){ case ((n, t), b) => Abs(n, t, b) }
  def λ(args: (String, Term)*)(body: Term): Term = lambda(args: _*)(body)

  object Precedence {

    val App = 1
    val Abs = 2
    val Pi = 2

    val Top = 10

  }


  object Nat {

    def unapply(t: Term): Option[Int] = t match {
      case Const("Z") => Some(0)
      case App(Const("S"), List(Nat(n))) => Some(n + 1)
      case _ => None
    }

  }

}
