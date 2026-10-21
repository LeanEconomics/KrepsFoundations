/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic

/-!
# Dyadic grids for ordered bisymmetric means

The algebraic stage of the cardinal-scale construction used in Proposition 2.14.
No additive representation is assumed: a reflexive symmetric bisymmetric mean
generates its own nested grid, and bisymmetry supplies the midpoint identity.
-/

namespace Kreps.PreferenceProperties

/-- The algebraic and order properties of a strict symmetric bisymmetric mean. -/
structure OrderedBisymmetricMean (α : Type*) [LinearOrder α] where
  mean : α → α → α
  reflexive : ∀ x, mean x x = x
  symmetric : ∀ x y, mean x y = mean y x
  bisymmetric : ∀ x y z w, mean (mean x y) (mean z w) = mean (mean x z) (mean y w)
  strictMono_left : ∀ y, StrictMono (fun x => mean x y)
  strictMono_right : ∀ x, StrictMono (mean x)

variable {α : Type*} [LinearOrder α]

/-- Repeated midpoint subdivision, with the endpoint values retained at even grid indices. -/
def MeanDyadicGrid (F : α → α → α) (a b : α) : ℕ → ℕ → α
  | 0, k => if k = 0 then a else b
  | n + 1, k => F (MeanDyadicGrid F a b n (k / 2))
      (MeanDyadicGrid F a b n ((k + 1) / 2))

/-- A strict mean lies strictly between unequal ordered arguments. -/
theorem orderedMean_between (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b) :
    a < M.mean a b ∧ M.mean a b < b := by
  constructor
  · exact by simpa only [M.reflexive] using M.strictMono_right a hab
  · exact by simpa only [M.reflexive] using M.strictMono_left b hab

/-- Refining the grid preserves an old point at twice its former index. -/
theorem meanDyadicGrid_even (M : OrderedBisymmetricMean α) (a b : α) (n k : ℕ) :
    MeanDyadicGrid M.mean a b (n + 1) (2 * k) = MeanDyadicGrid M.mean a b n k := by
  have h₀ : 2 * k / 2 = k := by omega
  have h₁ : (2 * k + 1) / 2 = k := by omega
  simp only [MeanDyadicGrid, h₀, h₁, M.reflexive]

/-- New odd-index points are means of neighboring old points. -/
theorem meanDyadicGrid_odd (M : OrderedBisymmetricMean α) (a b : α) (n k : ℕ) :
    MeanDyadicGrid M.mean a b (n + 1) (2 * k + 1) =
      M.mean (MeanDyadicGrid M.mean a b n k) (MeanDyadicGrid M.mean a b n (k + 1)) := by
  have h₀ : (2 * k + 1) / 2 = k := by omega
  have h₁ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp only [MeanDyadicGrid, h₀, h₁]

/-- Every refinement starts at the designated left endpoint. -/
theorem meanDyadicGrid_left (M : OrderedBisymmetricMean α) (a b : α) (n : ℕ) :
    MeanDyadicGrid M.mean a b n 0 = a := by
  induction n with
  | zero => simp [MeanDyadicGrid]
  | succ n ih => simpa only [Nat.mul_zero, ih] using meanDyadicGrid_even M a b n 0

/-- Every refinement ends at the designated right endpoint. -/
theorem meanDyadicGrid_right (M : OrderedBisymmetricMean α) (a b : α) (n : ℕ) :
    MeanDyadicGrid M.mean a b n (2 ^ n) = b := by
  induction n with
  | zero => simp [MeanDyadicGrid]
  | succ n ih =>
    rw [pow_succ, Nat.mul_comm, meanDyadicGrid_even, ih]

/-- A two-step interval has its middle grid point as its mean. -/
theorem meanDyadicGrid_near (M : OrderedBisymmetricMean α) (a b : α) (n : ℕ)
    (hmid : ∀ i j, i ≤ 2 ^ n → j ≤ 2 ^ n →
      M.mean (MeanDyadicGrid M.mean a b n i) (MeanDyadicGrid M.mean a b n j) =
        MeanDyadicGrid M.mean a b (n + 1) (i + j))
    (k : ℕ) (hk : k + 2 ≤ 2 ^ (n + 1)) :
    M.mean (MeanDyadicGrid M.mean a b (n + 1) k)
      (MeanDyadicGrid M.mean a b (n + 1) (k + 2)) =
        MeanDyadicGrid M.mean a b (n + 1) (k + 1) := by
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  by_cases he : k % 2 = 0
  · have hk' : k = 2 * (k / 2) := by omega
    have hk₂ : k + 2 = 2 * (k / 2 + 1) := by omega
    have hk₁ : k + 1 = 2 * (k / 2) + 1 := by omega
    have hl := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk').trans
      (meanDyadicGrid_even M a b n (k / 2))
    have hr := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₂).trans
      (meanDyadicGrid_even M a b n (k / 2 + 1))
    have hm := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₁).trans
      (meanDyadicGrid_odd M a b n (k / 2))
    rw [hl, hr, hm]
  · have hk' : k = 2 * (k / 2) + 1 := by omega
    have hk₂ : k + 2 = 2 * (k / 2 + 1) + 1 := by omega
    have hk₁ : k + 1 = 2 * (k / 2 + 1) := by omega
    have hl := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk').trans
      (meanDyadicGrid_odd M a b n (k / 2))
    have hr := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₂).trans
      (meanDyadicGrid_odd M a b n (k / 2 + 1))
    have hm := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₁).trans
      (meanDyadicGrid_even M a b n (k / 2 + 1))
    rw [hl, hr, hm]
    rw [M.symmetric (MeanDyadicGrid M.mean a b n (k / 2 + 1))
      (MeanDyadicGrid M.mean a b n (k / 2 + 1 + 1)), M.bisymmetric, M.reflexive]
    have hi : k / 2 ≤ 2 ^ n := by omega
    have hj : k / 2 + 1 + 1 ≤ 2 ^ n := by omega
    rw [hmid _ _ hi hj]
    have hsum : k / 2 + (k / 2 + 1 + 1) = 2 * (k / 2 + 1) := by omega
    rw [hsum, meanDyadicGrid_even, M.reflexive]

/-- Bisymmetry makes arbitrary grid pairs average their dyadic indices. -/
theorem meanDyadicGrid_midpoint (M : OrderedBisymmetricMean α) (a b : α) (n i j : ℕ)
    (hi : i ≤ 2 ^ n) (hj : j ≤ 2 ^ n) :
    M.mean (MeanDyadicGrid M.mean a b n i) (MeanDyadicGrid M.mean a b n j) =
      MeanDyadicGrid M.mean a b (n + 1) (i + j) := by
  induction n generalizing i j with
  | zero =>
    norm_num at hi hj
    interval_cases i <;> interval_cases j <;>
      simp [MeanDyadicGrid, M.reflexive, M.symmetric]
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
    have hi₀ : i / 2 ≤ 2 ^ n := by omega
    have hi₁ : (i + 1) / 2 ≤ 2 ^ n := by omega
    have hj₀ : j / 2 ≤ 2 ^ n := by omega
    have hj₁ : (j + 1) / 2 ≤ 2 ^ n := by omega
    change M.mean
      (M.mean (MeanDyadicGrid M.mean a b n (i / 2))
        (MeanDyadicGrid M.mean a b n ((i + 1) / 2)))
      (M.mean (MeanDyadicGrid M.mean a b n (j / 2))
        (MeanDyadicGrid M.mean a b n ((j + 1) / 2))) =
      M.mean (MeanDyadicGrid M.mean a b (n + 1) ((i + j) / 2))
        (MeanDyadicGrid M.mean a b (n + 1) ((i + j + 1) / 2))
    rw [M.bisymmetric, ih _ _ hi₀ hj₀, ih _ _ hi₁ hj₁]
    by_cases hei : i % 2 = 0
    · congr 2 <;> omega
    · by_cases hej : j % 2 = 0
      · congr 2 <;> omega
      · have hright : (i + 1) / 2 + (j + 1) / 2 = i / 2 + j / 2 + 2 := by omega
        have hmiddle : (i + j) / 2 = i / 2 + j / 2 + 1 := by omega
        have hmiddle' : (i + j + 1) / 2 = i / 2 + j / 2 + 1 := by omega
        rw [hright, hmiddle, hmiddle', M.reflexive]
        exact meanDyadicGrid_near M a b n ih (i / 2 + j / 2) (by omega)

/-- Consecutive dyadic grid points are strictly ordered between distinct endpoints. -/
theorem meanDyadicGrid_lt_succ (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b)
    (n k : ℕ) (hk : k < 2 ^ n) :
    MeanDyadicGrid M.mean a b n k < MeanDyadicGrid M.mean a b n (k + 1) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by norm_num at hk; omega
    subst k
    simpa [MeanDyadicGrid] using hab
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
    have hkhalf : k / 2 < 2 ^ n := by omega
    have hbetween := orderedMean_between M (ih (k / 2) hkhalf)
    by_cases he : k % 2 = 0
    · have hk' : k = 2 * (k / 2) := by omega
      have hk₁ : k + 1 = 2 * (k / 2) + 1 := by omega
      have hl := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk').trans
        (meanDyadicGrid_even M a b n (k / 2))
      have hr := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₁).trans
        (meanDyadicGrid_odd M a b n (k / 2))
      rw [hl, hr]
      exact hbetween.1
    · have hk' : k = 2 * (k / 2) + 1 := by omega
      have hk₁ : k + 1 = 2 * (k / 2 + 1) := by omega
      have hl := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk').trans
        (meanDyadicGrid_odd M a b n (k / 2))
      have hr := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₁).trans
        (meanDyadicGrid_even M a b n (k / 2 + 1))
      rw [hl, hr]
      exact hbetween.2

/-- Each finite grid is strictly increasing in its valid index interval. -/
theorem meanDyadicGrid_strictMonoOn (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b)
    (n : ℕ) : StrictMonoOn (MeanDyadicGrid M.mean a b n) (Set.Iic (2 ^ n)) :=
  strictMonoOn_Iic_of_lt_succ (fun k hk => meanDyadicGrid_lt_succ M hab n k hk)

/-- Repeated refinement does not change any existing grid point. -/
theorem meanDyadicGrid_refine (M : OrderedBisymmetricMean α) (a b : α) (n m k : ℕ) :
    MeanDyadicGrid M.mean a b (n + m) (k * 2 ^ m) = MeanDyadicGrid M.mean a b n k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hindex : k * 2 ^ (m + 1) = 2 * (k * 2 ^ m) := by rw [pow_succ]; ring
    rw [Nat.add_succ, hindex, meanDyadicGrid_even, ih]

/-- The union of all finite dyadic mean grids. -/
def MeanDyadicPoints (M : OrderedBisymmetricMean α) (a b : α) : Set α :=
  {x | ∃ n k, k ≤ 2 ^ n ∧ x = MeanDyadicGrid M.mean a b n k}

/-- The dyadic points are closed under the mean operation. -/
theorem meanDyadicPoints_mean (M : OrderedBisymmetricMean α) (a b : α) {x y : α}
    (hx : x ∈ MeanDyadicPoints M a b) (hy : y ∈ MeanDyadicPoints M a b) :
    M.mean x y ∈ MeanDyadicPoints M a b := by
  obtain ⟨n, i, hi, rfl⟩ := hx
  obtain ⟨m, j, hj, rfl⟩ := hy
  have hi' : i * 2 ^ m ≤ 2 ^ (n + m) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hi
  have hj' : j * 2 ^ n ≤ 2 ^ (n + m) := by
    rw [Nat.add_comm n m, pow_add]
    exact Nat.mul_le_mul_right _ hj
  refine ⟨n + m + 1, i * 2 ^ m + j * 2 ^ n, ?_, ?_⟩
  · rw [pow_succ]
    omega
  · have hleft := meanDyadicGrid_refine M a b n m i
    have hright := meanDyadicGrid_refine M a b m n j
    rw [Nat.add_comm m n] at hright
    rw [← hleft, ← hright]
    exact meanDyadicGrid_midpoint M a b (n + m) _ _ hi' hj'

end Kreps.PreferenceProperties
