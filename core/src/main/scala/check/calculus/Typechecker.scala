package check
package calculus

import Term._

object Typechecker {

  def typecheck(t: Term, ctxt: List[(String, Term)],
    consts: PartialFunction[String, Term],
    constReds: PartialFunction[String, PartialFunction[List[Term], Term]]
  ): Either[String, Term] = {
    val names = ctxt.map(_._1)
    t match {
      case Var(i) => Right(ctxt(i)._2.shift(i + 1))
      case Type(l) => Right(Type(l + 1))
      case Const(c) => consts.lift(c).toRight(s"Unknown constant: $c")
      case App(f, Nil) => typecheck(f, ctxt, consts, constReds)
      case App(f, as) =>
        def go(ft: Term, as: List[Term]): Either[String, Term] = as match {
          case Nil => Right(ft)
          case a :: as => for {
            at <- typecheck(a, ctxt, consts, constReds).map(_.reduce(constReds))
            newft <- ft match {
              case Pi(_, t, r) =>
                if(at equiv t) Right(r.subst(Map(0 -> a.shift(1))).shift(-1))
                else {
                  Left(s"Wrong argument type, expected ${t.prettyprint(names)}, found ${at.prettyprint(names)}")
                }
              case ft =>
                Left(s"Application does not take any arguments. Function type is: ${ft.prettyprint(names)}")
            }
            res <- go(newft, as)
          } yield res
        }
        typecheck(f, ctxt, consts, constReds)
          .map(_.reduce(constReds))
          .flatMap(go(_, as))
      case Abs(n, t, b) => for {
        tt <- typecheck(t, ctxt, consts, constReds)
        _ <- tt match {
          case Type(_) => Right(())
          case t => Left(s"Wrong kind of abstraction argument type: ${t.prettyprint(names)}")
        }
        newctxt = (n, t) :: ctxt
        bt <- typecheck(b, newctxt, consts, constReds)
      } yield Pi(n, t, bt)
      case Pi(n, t, r) => for {
        tt <- typecheck(t, ctxt, consts, constReds)
        tl <- tt match {
          case Type(l) => Right(l)
          case t => Left(s"Wrong kind of Pi argument type: ${t.prettyprint(names)}")
        }
        newctxt = (n, t) :: ctxt
        rt <- typecheck(r, newctxt, consts, constReds)
        rl <- rt match {
          case Type(l) => Right(l)
          case t => Left(s"Wrong kind of Pi result: ${t.prettyprint(newctxt.map(_._1))}")
        }
      } yield Type(tl max rl)
    }
  }

}
