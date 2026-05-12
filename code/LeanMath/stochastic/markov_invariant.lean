/-
  Markov Chains: Invariant Distributions
  =======================================
  Formalization of finite-state Markov chains and the main theorem
  on existence, uniqueness, and positivity of invariant distributions.

  Corresponds to the lecture slides:
    Folien_TINF24CS1/dhbw_stochastik_markov.tex

  Key results:
  - IsTransitionMatrix: definition of stochastic matrix
  - IsInvariant: π P = π
  - IsIrreducible: all states communicate
  - IsAperiodic: gcd of return times = 1
  - stationary_exists: existence via Cesàro means
  - stationary_pos: π_i > 0 for all i (irreduzibel)
  - stationary_unique: uniqueness (irreduzibel)
  - detailedBalance_implies_invariant: detailed balance ⟹ invariant
  - Weather example (2 states) and mood example (3 states)
-/

import Mathlib

open scoped BigOperators
open Finset

section FiniteMarkovInvariant

variable {N : ℕ} [NeZero N]

/-- State space: Fin N -/
abbrev S (N : ℕ) := Fin N

/-! ## Basic Definitions -/

/-- A stochastic (transition) matrix: nonneg entries, row sums = 1 -/
def IsTransitionMatrix (P : S N → S N → ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧
  (∀ x, (∑ y : S N, P x y) = 1)

/-- A probability distribution on S N -/
def IsDistribution (π : S N → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ (∑ i : S N, π i) = 1

/-- π is an invariant (stationary) distribution for P:
    ∀ j, ∑_i π_i P_{ij} = π_j  (i.e., π P = π as row vector) -/
def IsInvariant (P : S N → S N → ℝ) (π : S N → ℝ) : Prop :=
  ∀ j : S N, (∑ i : S N, π i * P i j) = π j

/-! ## Matrix Operations -/

/-- Matrix multiplication for functions S N → S N → ℝ -/
noncomputable def matMul (P Q : S N → S N → ℝ) : S N → S N → ℝ :=
  fun x z => ∑ y : S N, P x y * Q y z

/-- Matrix power -/
noncomputable def matPow (P : S N → S N → ℝ) : ℕ → S N → S N → ℝ
  | 0     => fun x z => if x = z then 1 else 0
  | n + 1 => matMul (matPow P n) P

/-- Step operator: (Pf)(x) = ∑_y P(x,y) f(y) -/
noncomputable def stepOp (P : S N → S N → ℝ) (f : S N → ℝ) : S N → ℝ :=
  fun x => ∑ y : S N, P x y * f y

/-! ## Irreducibility and Aperiodicity -/

/-- A chain is irreducible if every state can reach every other state -/
def IsIrreducible (P : S N → S N → ℝ) : Prop :=
  ∀ i j : S N, ∃ n : ℕ, 0 < n ∧ 0 < matPow P n i j

/-- A chain is aperiodic if all return times have gcd 1 -/
def IsAperiodic (P : S N → S N → ℝ) : Prop :=
  ∀ i : S N, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → 0 < matPow P n i i

/-! ## Harmonicity (Maximum Principle) -/

/-- f is harmonic for P: Pf = f -/
def IsHarmonic (P : S N → S N → ℝ) (f : S N → ℝ) : Prop :=
  ∀ x : S N, stepOp P f x = f x

/-! ## Detailed Balance -/

/-- Detailed balance: π_i P_{ij} = π_j P_{ji} for all i, j -/
def DetailedBalance (P : S N → S N → ℝ) (π : S N → ℝ) : Prop :=
  ∀ i j : S N, π i * P i j = π j * P j i

/-! ## Key Lemmas -/

/-- Product of transition matrices is a transition matrix -/
lemma matMul_isTransition (P Q : S N → S N → ℝ)
    (hP : IsTransitionMatrix P) (hQ : IsTransitionMatrix Q) :
    IsTransitionMatrix (matMul P Q) := by
  constructor
  · intro x z
    apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (hP.1 x y) (hQ.1 y z)
  · intro x
    simp only [matMul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp [hQ.2, hP.2]

/-- Invariant distribution is preserved under multiple steps: π P^n = π -/
lemma invariant_of_pow (P : S N → S N → ℝ) (π : S N → ℝ)
    (hInv : IsInvariant P π) :
    ∀ n : ℕ, ∀ j : S N, (∑ i : S N, π i * matPow P n i j) = π j := by
  intro n
  induction n with
  | zero =>
    intro j
    simp [matPow]
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ j]
    simp
  | succ n ih =>
    intro j
    simp only [matPow, matMul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    conv_lhs =>
      arg 1; ext y
      rw [show (∑ i : S N, π i * (∑ k : S N, matPow P n i k * P k y)) =
          ∑ k : S N, (∑ i : S N, π i * matPow P n i k) * P k y from by
        rw [Finset.sum_comm]; congr 1; ext k
        rw [← Finset.sum_mul]; congr 1; ext i; ring]
    simp_rw [ih]
    exact hInv j

/-! ## Main Theorem: Uniqueness of Invariant Distribution -/

/-- Maximum principle: a harmonic function on a finite irreducible chain is constant -/
theorem harmonic_const_of_irreducible (P : S N → S N → ℝ)
    (hP : IsTransitionMatrix P)
    (hirr : IsIrreducible P)
    (f : S N → ℝ)
    (hf : IsHarmonic P f) :
    ∀ i j : S N, f i = f j := by
  -- The proof uses the maximum principle:
  -- At the maximum, f(i*) = ∑_j P(i*,j) f(j) forces f(j) = f(i*) for all
  -- reachable j by convexity. Irreducibility propagates to all states.
  sorry

/-- **Hauptsatz (Eindeutigkeit):**
    An irreducible finite Markov chain has at most one invariant distribution. -/
theorem stationary_unique (P : S N → S N → ℝ)
    (hP : IsTransitionMatrix P)
    (hirr : IsIrreducible P)
    (π₁ π₂ : S N → ℝ)
    (hπ₁_dist : IsDistribution π₁)
    (hπ₂_dist : IsDistribution π₂)
    (hπ₁_inv : IsInvariant P π₁)
    (hπ₂_inv : IsInvariant P π₂) :
    π₁ = π₂ := by
  -- Define f = π₁ - π₂. Then f is harmonic and sums to 0.
  -- By the maximum principle for irreducible chains, f is constant.
  -- Since ∑ f_i = 0, f = 0, hence π₁ = π₂.
  have hf_harm : IsHarmonic P (fun i => π₁ i - π₂ i) := by
    intro x
    simp only [stepOp]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [hπ₁_inv x, hπ₂_inv x]
  have hf_const := harmonic_const_of_irreducible P hP hirr _ hf_harm
  funext i
  have hf_sum : (∑ k : S N, (π₁ k - π₂ k)) = 0 := by
    rw [Finset.sum_sub_distrib, hπ₁_dist.2, hπ₂_dist.2, sub_self]
  -- All values of f are equal (by hf_const) and sum to 0
  -- Pick any j₀. Then f(i) = f(j₀) for all i, and |S| * f(j₀) = 0.
  have h_all_eq : ∀ k : S N, π₁ k - π₂ k = π₁ i - π₂ i :=
    fun k => hf_const k i
  have h_card_mul : (Fintype.card (S N)) * (π₁ i - π₂ i) = 0 := by
    have : (∑ k : S N, (π₁ k - π₂ k)) = (Fintype.card (S N)) * (π₁ i - π₂ i) := by
      rw [← Finset.sum_const]
      exact (Finset.sum_congr rfl fun k _ => h_all_eq k).symm
    linarith
  have hcard_pos : 0 < Fintype.card (S N) := Fintype.card_pos
  have : π₁ i - π₂ i = 0 := by
    by_contra h
    have := mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_of_ne_zero
      (by omega : Fintype.card (S N) ≠ 0))) h
    exact this h_card_mul
  linarith

/-- **Hauptsatz (Positivität):**
    The unique invariant distribution of an irreducible chain is strictly positive. -/
theorem stationary_pos (P : S N → S N → ℝ)
    (hP : IsTransitionMatrix P)
    (hirr : IsIrreducible P)
    (π : S N → ℝ)
    (hπ_dist : IsDistribution π)
    (hπ_inv : IsInvariant P π) :
    ∀ i : S N, 0 < π i := by
  -- By irred., for any i there exists j with π_j > 0 and n s.t. P^n(j,i) > 0.
  -- Then π_i = ∑_k π_k P^n(k,i) ≥ π_j P^n(j,i) > 0.
  intro i
  -- There exists some j with π j > 0
  have ⟨j, hj⟩ : ∃ j : S N, 0 < π j := by
    by_contra h
    push_neg at h
    have : (∑ k : S N, π k) ≤ 0 :=
      Finset.sum_nonpos fun k _ => le_antisymm (h k) (hπ_dist.1 k) ▸ le_refl 0
    linarith [hπ_dist.2]
  -- By irreducibility, j can reach i
  obtain ⟨n, hn_pos, hn_val⟩ := hirr j i
  -- Use π = π P^n
  have h_inv_n := invariant_of_pow P π hπ_inv n i
  rw [← h_inv_n]
  -- π_i = ∑_k π_k P^n(k,i) ≥ π_j P^n(j,i) > 0
  sorry

/-- **Hauptsatz (Existenz):**
    An irreducible finite Markov chain has an invariant distribution.
    (Existence via Cesàro means and compactness.) -/
theorem stationary_exists (P : S N → S N → ℝ)
    (hP : IsTransitionMatrix P)
    (hirr : IsIrreducible P) :
    ∃ π : S N → ℝ, IsDistribution π ∧ IsInvariant P π := by
  -- The Cesàro mean (1/n) ∑_{k=0}^{n-1} P^k has rows in the probability simplex.
  -- By compactness (Bolzano-Weierstraß), a convergent subsequence exists.
  -- Its limit satisfies Q P = Q, giving an invariant distribution.
  sorry

/-! ## Detailed Balance implies Invariance -/

/-- If π satisfies detailed balance w.r.t. P, then π is invariant for P. -/
theorem detailedBalance_implies_invariant (P : S N → S N → ℝ)
    (hP : IsTransitionMatrix P)
    (π : S N → ℝ)
    (hdb : DetailedBalance P π) :
    IsInvariant P π := by
  intro j
  -- ∑_i π_i P_{ij} = ∑_i π_j P_{ji} = π_j ∑_i P_{ji} = π_j · 1
  calc ∑ i : S N, π i * P i j
      = ∑ i : S N, π j * P j i := by
        congr 1; ext i; exact hdb i j
    _ = π j * ∑ i : S N, P j i := by rw [Finset.mul_sum]
    _ = π j * 1 := by rw [hP.2 j]
    _ = π j := mul_one _

end FiniteMarkovInvariant

/-! ## Concrete Examples -/

section WeatherExample

/-- Weather transition matrix: S(onne) ↔ R(egen) -/
def weatherP : S 2 → S 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 0.8
  | ⟨0, _⟩, ⟨1, _⟩ => 0.2
  | ⟨1, _⟩, ⟨0, _⟩ => 0.4
  | ⟨1, _⟩, ⟨1, _⟩ => 0.6

/-- Invariant distribution for weather: π = (2/3, 1/3) -/
def weatherπ : S 2 → ℝ
  | ⟨0, _⟩ => 2/3
  | ⟨1, _⟩ => 1/3

/-- weatherP is a valid transition matrix -/
lemma weatherP_isTransition : IsTransitionMatrix (N := 2) weatherP := by
  constructor
  · intro x y; fin_cases x <;> fin_cases y <;> simp [weatherP] <;> norm_num
  · intro x; fin_cases x <;> simp [weatherP, Fin.sum_univ_two] <;> norm_num

/-- weatherπ is a valid distribution -/
lemma weatherπ_isDistribution : IsDistribution (N := 2) weatherπ := by
  constructor
  · intro i; fin_cases i <;> simp [weatherπ] <;> norm_num
  · simp [weatherπ, Fin.sum_univ_two]; norm_num

/-- weatherπ is invariant for weatherP: π P = π -/
lemma weatherπ_isInvariant : IsInvariant (N := 2) weatherP weatherπ := by
  intro j
  fin_cases j <;> simp [weatherP, weatherπ, Fin.sum_univ_two] <;> ring

/-- weatherP satisfies detailed balance w.r.t. weatherπ -/
lemma weather_detailedBalance :
    DetailedBalance (N := 2) weatherP weatherπ := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [weatherP, weatherπ] <;> ring

/-- weatherP is irreducible -/
lemma weatherP_irreducible : IsIrreducible (N := 2) weatherP := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨1, Nat.one_pos, by simp [matPow, matMul, weatherP, Fin.sum_univ_two]; norm_num⟩
  · exact ⟨1, Nat.one_pos, by simp [matPow, matMul, weatherP, Fin.sum_univ_two]; norm_num⟩
  · exact ⟨1, Nat.one_pos, by simp [matPow, matMul, weatherP, Fin.sum_univ_two]; norm_num⟩
  · exact ⟨1, Nat.one_pos, by simp [matPow, matMul, weatherP, Fin.sum_univ_two]; norm_num⟩

end WeatherExample


section MoodExample

/-- Mood model: G(ut), N(eutral), S(chlecht) with 3 states -/
def moodP : S 3 → S 3 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 0.5
  | ⟨0, _⟩, ⟨1, _⟩ => 0.4
  | ⟨0, _⟩, ⟨2, _⟩ => 0.1
  | ⟨1, _⟩, ⟨0, _⟩ => 0.3
  | ⟨1, _⟩, ⟨1, _⟩ => 0.4
  | ⟨1, _⟩, ⟨2, _⟩ => 0.3
  | ⟨2, _⟩, ⟨0, _⟩ => 0.2
  | ⟨2, _⟩, ⟨1, _⟩ => 0.3
  | ⟨2, _⟩, ⟨2, _⟩ => 0.5

/-- moodP is a valid transition matrix -/
lemma moodP_isTransition : IsTransitionMatrix (N := 3) moodP := by
  constructor
  · intro x y; fin_cases x <;> fin_cases y <;> simp [moodP] <;> norm_num
  · intro x; fin_cases x <;> simp [moodP, Fin.sum_univ_three] <;> norm_num

/-- moodP is irreducible (all entries on first step are positive) -/
lemma moodP_irreducible : IsIrreducible (N := 3) moodP := by
  intro i j
  exact ⟨1, Nat.one_pos, by
    fin_cases i <;> fin_cases j <;>
      simp [matPow, matMul, moodP, Fin.sum_univ_three] <;> norm_num⟩

end MoodExample


section PeriodicExample

/-- Periodic chain: always alternates between states -/
def periodicP : S 2 → S 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 0

/-- The periodic chain has π = (1/2, 1/2) as invariant distribution,
    but P^n does NOT converge (it oscillates). -/
def periodicπ : S 2 → ℝ
  | ⟨0, _⟩ => 1/2
  | ⟨1, _⟩ => 1/2

lemma periodicπ_isInvariant : IsInvariant (N := 2) periodicP periodicπ := by
  intro j
  fin_cases j <;> simp [periodicP, periodicπ, Fin.sum_univ_two] <;> ring

end PeriodicExample
