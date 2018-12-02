package check
package calculus

import Term._

object Sandbox {

  val Nat = Const("Nat")
  val S = Const("S")
  val Z = Const("Z")

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
    }
  )

  val constTypes: Map[String, Term] = Map(
    "Nat" -> Type(0),
    "S" -> Pi("n", Nat, Nat),
    "Z" -> Nat,
    "+" -> Pi("a", Nat, Pi("b", Nat, Nat)),
    "Nat-rec" -> Pi("A", Type(0), Pi(
      "a", Var(0), Pi(
        "f", Pi("n", Nat, Pi("b", Var(2), Var(3))), Pi(
          "c", Nat, Var(3))))) // ∀ {A : Set} → A → (ℕ → A → A) → ℕ → A
  )

  def nat(i: Int): Term =
    (0 until i).foldLeft(Const("Z"): Term)((t, i) => App(Const("S"), List(t)))

  def tc(t: Term): Either[String, Term] =
    Typechecker.typecheck(t, Nil, constTypes, consts)

}
