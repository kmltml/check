package check
package calculus

import cats._, cats.data.{Const => _, _}, cats.implicits._
import org.atnos.eff._, org.atnos.eff.all._, org.atnos.eff.syntax.all._

import scala.language.higherKinds

import Constraint.Iden
import Term._

object Unification {

  final case class S(nextMeta: Int = 0, metaTypes: Map[Meta, Meta] = Map.empty) {
    def getNextMeta: (S, Int) = (copy(nextMeta = nextMeta + 1), nextMeta)
    def withMetaType(m: Meta, t: Meta): S = copy(metaTypes = metaTypes + (m -> t))
  }

  def nextMeta[R](implicit S: State[S, ?] |= R): Eff[R, Meta] = for {
    t <- gets((_: S).getNextMeta)
    _ <- put(t._1)
  } yield Term.Meta(t._2)

  def getMetaType[R](meta: Meta)(implicit _s: State[S, ?] |= R): Eff[R, Meta] = for {
    r_? <- gets((_: S).metaTypes.get(meta))
    r <- r_? match {
      case Some(r) => Eff.pure[R, Meta](r)
      case None => for {
        r <- nextMeta
        _ <- modify[R, S]((_: S).withMetaType(meta, r))
      } yield r
    }
  } yield r

  def genConstraints[R](t: Term, bindings: List[Term], consts: PartialFunction[String, Term])(implicit
    W: Writer[Vector[Constraint], ?] |= R,
    S: State[S, ?] |= R,
    E: Either[String, ?] |= R
  ): Eff[R, Term] = {
    t match {
      case Var(i) => Eff.pure(bindings(i).shift(i + 1))
      case m: Meta => getMetaType(m).widen
      case Const(c) =>
        optionEither(consts.lift(c), s"Unknown constant $c")
      case App(f, as) => for {
          ft <- genConstraints(f, bindings, consts) 
          res <- as.foldLeftM(ft) { (ft, a) =>
            for {
              at <- genConstraints(a, bindings, consts)
              rm <- nextMeta
              _ <- tell[R, Vector[Constraint]](Vector(Iden(ft, Pi(s"x${rm.index}", at, rm), App(f, List(a)))))
            } yield lambda((s"x${rm.index}", at))(rm).app(a)
        }
      } yield res
      case Abs(n, t, b) => for {
        tt <- genConstraints(t, bindings, consts)
        newbindings = t :: bindings
        bt <- genConstraints(b, newbindings, consts)
        _ <- tell[R, Vector[Constraint]](Vector(
          Iden(tt, Type, Abs(n, t, b)))
        )
      } yield Pi(n, t, bt)
      case pi @ Pi(n, t, r) => for {
        tt <- genConstraints(t, bindings, consts)
        newbindings = tt :: bindings
        rt <- genConstraints(r, newbindings, consts)
        m <- nextMeta
        _ <- tell[R, Vector[Constraint]](Vector(
          Iden(rt, Type, pi),
          Iden(m, Type, pi)
        ))
      } yield m
      case Type => Eff.pure(Type)
    }
  }

  def genConstraints(t: Term, consts: PartialFunction[String, Term]): Either[String, (Term, Vector[Constraint])] = {
    val nextMeta = {
      val metas = t.metas.map(_.index)
      if(metas.isEmpty) 0 else metas.max + 1
    }
    type R = Fx.fx3[Either[String, ?], State[S, ?], Writer[Vector[Constraint], ?]]
    // StateT[Id, S, ?]
    val res = genConstraints[R](t, Nil, consts)
      .evalState(S(nextMeta))
      .runWriter
      .runEither
      .run
    res.map { case (t, cs) => (t, cs.combineAll) }
  }

  def unify[R](constraint: Constraint, consts: PartialFunction[String, PartialFunction[List[Term], Term]])
      (implicit s: State[Map[Meta, Term], ?] |= R): Eff[R, Vector[Constraint]] = constraint match {
    case Iden(a: Meta, b: Meta, o) =>
      for(x <- repr(a); y <- repr(b); res <- unifyShallow(Iden(x, b, o), consts)) yield res
    case Iden(App(Abs(n, t, b), List(a)), other, origin) if b.metas.nonEmpty =>
      for {
        m <- get[R, Map[Meta, Term]]
        res <- unifyShallow(Iden(App(Abs(n, t, b.substMeta(m)), List(a)), other, origin), consts)
      } yield res
    case Iden(other, App(Abs(n, t, b), List(a)), origin) if b.metas.nonEmpty =>
      for {
        m <- get[R, Map[Meta, Term]]
        res <- unifyShallow(Iden(App(Abs(n, t, b.substMeta(m)), List(a)), other, origin), consts)
      } yield res
    case c => unifyShallow(c, consts)
  }

  type UFT = Map[Meta, Term]

  private def unifyShallow[R](constraint: Constraint, consts: PartialFunction[String, PartialFunction[List[Term], Term]])
    (implicit S: State[UFT, ?] |= R): Eff[R, Vector[Constraint]] = {
    
    constraint.reduce(consts) match {
      case Iden(a, b, _) if a equiv b => Eff.pure(Vector.empty)
      case Iden(m: Meta, s, _) =>
        StateEffect.modify[R, UFT](_ + (m -> s)).as(Vector.empty)
      case Iden(s, m: Meta, _) =>
        StateEffect.modify[R, UFT](_ + (m -> s)).as(Vector.empty)
      case Iden(Pi(an, at, ar), Pi(bn, bt, br), origin) =>
        for {
          tf <- unify(Iden(at, bt, origin), consts)
          rf <- unify(Iden(ar, br, origin), consts)
        } yield tf ++ rf
      case id => Eff.pure(Vector(id))
    }
  }

  // private def equiv(a: Term, b: Term, uft: UFT): Boolean = (a, b) match {
  //   case 
  // }

  def unifyAll(constraints: Vector[Constraint], consts: PartialFunction[String, PartialFunction[List[Term], Term]]):
      (Vector[Constraint], UFT) = {
    type R = Fx.fx1[State[UFT, ?]]
    val res = constraints.traverse(unify[R](_, consts)).runState(Map.empty[Meta, Term]).run
    (res._1.flatten, res._2)
  }

  private def repr[R](meta: Meta)
    (implicit s: State[UFT, ?] |= R): Eff[R, Term] =
    for {
      p <- StateEffect.gets[R, UFT, Option[Term]](_.get(meta))
      pr <- p match {
        case None => Eff.pure[R, Term](meta: Term)
        case Some(r) => for {
          res <- r match {
            case m: Meta => repr[R](m)
            case _ => Eff.pure[R, Term](r)
          }
          _ <- StateEffect.modify[R, UFT](_ + (meta -> res))
        } yield res
      }
    } yield pr

}
