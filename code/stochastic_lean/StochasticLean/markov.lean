import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open Finset


/-- Eine Markov-Kette auf einem endlich-dimensionalen Zustandsraum α. -/
structure MarkovChain (α : Type) [Fintype α] [DecidableEq α] where
  transition : α → α → ℝ
  probability  : ∀ i : α, ∑ j ∈ Finset.univ, transition i j = 1
  nonneg       : ∀ i j : α, 0 ≤ transition i j

namespace MarkovChain

variable {α : Type} [Fintype α] [DecidableEq α]
variable (P : MarkovChain α)

/-- Die \(n\)-Schritt-Übergangswahrscheinlichkeit:
- Für \(n=0\) entspricht sie der Einheitsmatrix,
- Für \(n+1\) wird sie rekursiv über einen Schritt und die \(n\)-Schritt-Wahrscheinlichkeiten definiert. -/
def nstep : ℕ → (α → α → ℝ)
| 0     => fun i j => if i = j then 1 else 0
| (n+1) => fun i j => ∑ k ∈ Finset.univ, P.transition i k * nstep n k j

/-- Lemma: Für \(n=0\) gilt \(nstep\ P\ 0\ i\ j = 1\) genau dann, wenn \(i = j\) ist, andernfalls 0. -/
lemma nstep_zero (i j : α) :
  nstep P 0 i j = if i = j then 1 else 0 :=
by rfl


end MarkovChain
