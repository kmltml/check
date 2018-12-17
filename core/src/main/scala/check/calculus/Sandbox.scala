package check
package calculus

import Term._

object Sandbox {

  val Nat = Const("Nat")
  val S = Const("S")
  val Z = Const("Z")
  val PEq = Const("=")
  val refl = Const("refl")
  val id = Const("id")

  def constReducer(arity: Int)(f: List[Term] => Term): PartialFunction[List[Term], Term] = {
    case as if as.size == arity =>
      f(as)
    case as if as.size > arity =>
      App(f(as.take(arity)), as.drop(arity))
  }

  val consts: Map[String, PartialFunction[List[Term], Term]] = Map(
    "Nat-rec" -> {
      case List(a, z, _, Const("Z")) => z
      case List(a, z, s, App(Const("S"), List(n))) =>
        App(s, List(n, App(Const("Nat-rec"), List(a, z, s, n)))) // Ps n (ℕ-ind P Pz Ps n)
    },
    "+" -> constReducer(0) {
      case Nil =>
        Abs("a", Nat, Abs("b", Nat, App(Const("Nat-rec"), List(
          Nat,
          Var(0),
          Abs("x", Nat, Const("S")),
          Var(1)
        ))))
    },
    "*" -> constReducer(0) {
      case Nil =>
        Abs("a", Nat, Abs("b", Nat, Const("Nat-rec").app(
          Nat,
          nat(0),
          Abs("x", Nat, Const("+").app(Var(1))),
          Var(1)
        )))
    },
    "id" -> constReducer(0) {
      case Nil => lambda(("A", Type), ("x", Var(0)))(Var(0))
    }
  )

  val constTypes: Map[String, Term] = Map(
    "Nat" -> Type,
    "S" -> Pi("n", Nat, Nat),
    "Z" -> Nat,
    "=" -> Pi("A", Type, Pi("x", Var(0), Pi("y", Var(1), Type))),
    "refl" -> Pi("A", Type, Pi("x", Var(0), PEq.app(Var(1), Var(0), Var(0)))),
    "+" -> Pi("a", Nat, Pi("b", Nat, Nat)),
    "*" -> Pi("a", Nat, Pi("b", Nat, Nat)),
    "Nat-rec" -> Pi("A", Type, Pi(
      "a", Var(0), Pi(
        "f", Pi("n", Nat, Pi("b", Var(2), Var(3))), Pi(
          "c", Nat, Var(3))))), // ∀ {A : Set} → A → (ℕ → A → A) → ℕ → A
    "id" -> (("A", Type) ->: ("x", Var(0)) ->: Var(1))
  )

  def nat(i: Int): Term =
    (0 until i).foldLeft(Const("Z"): Term)((t, i) => App(Const("S"), List(t)))

  def tc(t: Term): Either[String, Term] =
    Typechecker.typecheck(t, Nil, constTypes, consts)

  def normalize(t: Term): String = t.reduce(consts).prettyprint(Nil)

}
