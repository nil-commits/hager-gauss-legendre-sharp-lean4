import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# PPL 031: Hager's Sharper Gauss-Legendre Reverse-Markov Inequality

We prove the sharper Gauss-Legendre conjecture from W. W. Hager's 2015 prize problem PDF:
for any `n ≥ 1`, any polynomial `p : Polynomial ℝ` of degree `≤ n` with `p(-1) = 0` and
`|p'(τ_i)| ≤ 1` at the `n` Gauss-Legendre nodes `-1 < τ_1 < ... < τ_n < 1`, we have
`|p(τ_i)| ≤ 1 + τ_n` for all `1 ≤ i ≤ n` (sharp, attained by `p(t) = 1 + t`).

As a unified companion from Part 1 of the proof, we also prove Hager's bound `|p(τ_i)| ≤ 2`
for the `n` Gauss-Radau nodes (`τ_n = 1`).
-/

namespace PPL031_HagerGaussSharp

open scoped BigOperators
open Polynomial Finset MeasureTheory intervalIntegral

section LegendreCore

/-- The coefficient `c(n, k) = (-1)^k * C(n, k) * C(n + k, k)` in the shifted expansion. -/
noncomputable def legCoeff (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * ((Nat.choose n k : ℝ) * (Nat.choose (n + k) k : ℝ))

/-- Explicit shifted-hypergeometric definition of the degree-`n` Legendre polynomial `P_n`,
normalized by `P_n(1) = 1`. -/
noncomputable def legendreP (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), C (legCoeff n k) * (C (1 / 2 : ℝ) * (1 - X)) ^ k

lemma legendreP_eq_sum (n : ℕ) :
    legendreP n = ∑ k ∈ Finset.range (n + 1), C (legCoeff n k) * (C (1 / 2 : ℝ) * (1 - X)) ^ k :=
  rfl

lemma legCoeff_zero (n : ℕ) : legCoeff n 0 = 1 := by
  simp [legCoeff]

lemma legCoeff_succ (n k : ℕ) :
    ((k + 1 : ℕ) : ℝ) ^ 2 * legCoeff n (k + 1) =
      -(((n * (n + 1) : ℝ) - (k * (k + 1) : ℝ)) * legCoeff n k) := by
  by_cases hkn : k < n
  · have h1 : Nat.choose n (k + 1) * (k + 1) = Nat.choose n k * (n - k) :=
      Nat.choose_succ_right_eq n k
    have h2 : Nat.choose (n + (k + 1)) (k + 1) * (k + 1) =
        (n + k + 1) * Nat.choose (n + k) k := by
      have hsc := Nat.add_one_mul_choose_eq (n + k) k
      have hnk : n + (k + 1) = n + k + 1 := by omega
      rw [hnk]
      linarith
    have h1r : ((k + 1 : ℕ) : ℝ) * (Nat.choose n (k + 1) : ℝ) =
        ((n : ℝ) - (k : ℝ)) * (Nat.choose n k : ℝ) := by
      have h1' : ((Nat.choose n (k + 1) * (k + 1) : ℕ) : ℝ) =
          ((Nat.choose n k * (n - k) : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (le_of_lt hkn)] at h1'
      linarith
    have h2r : ((k + 1 : ℕ) : ℝ) * (Nat.choose (n + (k + 1)) (k + 1) : ℝ) =
        ((n : ℝ) + (k : ℝ) + 1) * (Nat.choose (n + k) k : ℝ) := by
      have h2' : ((Nat.choose (n + (k + 1)) (k + 1) * (k + 1) : ℕ) : ℝ) =
          (((n + k + 1) * Nat.choose (n + k) k : ℕ) : ℝ) := by exact_mod_cast h2
      rw [Nat.cast_mul, Nat.cast_mul] at h2'
      push_cast at h2' ⊢
      linarith
    unfold legCoeff
    calc
      ((k + 1 : ℕ) : ℝ) ^ 2 *
          ((-1 : ℝ) ^ (k + 1) * ((Nat.choose n (k + 1) : ℝ) * (Nat.choose (n + (k + 1)) (k + 1) : ℝ)))
        = (-1 : ℝ) ^ (k + 1) *
            ((((k + 1 : ℕ) : ℝ) * (Nat.choose n (k + 1) : ℝ)) *
              (((k + 1 : ℕ) : ℝ) * (Nat.choose (n + (k + 1)) (k + 1) : ℝ))) := by ring
      _ = (-1 : ℝ) ^ (k + 1) *
            ((((n : ℝ) - (k : ℝ)) * (Nat.choose n k : ℝ)) *
              (((n : ℝ) + (k : ℝ) + 1) * (Nat.choose (n + k) k : ℝ))) := by rw [h1r, h2r]
      _ = -(((n * (n + 1) : ℝ) - (k * (k + 1) : ℝ)) *
            ((-1 : ℝ) ^ k * ((Nat.choose n k : ℝ) * (Nat.choose (n + k) k : ℝ)))) := by
          rw [pow_succ]; ring
  · have hge : n ≤ k := not_lt.mp hkn
    by_cases hEq : k = n
    · rw [hEq]
      simp [legCoeff]
    · have hgt : n < k := lt_of_le_of_ne hge (Ne.symm hEq)
      have hch1 : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt hgt
      have hch2 : Nat.choose n (k + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_lt hgt)
      simp [legCoeff, hch1, hch2]

lemma legendreP_eval_one (n : ℕ) : (legendreP n).eval 1 = 1 := by
  rw [legendreP_eq_sum, eval_finsetSum]
  rw [Finset.sum_eq_single 0]
  · simp [legCoeff_zero]
  · intro k _ hk0
    simp [hk0]
  · simp

lemma legendreP_zero : legendreP 0 = 1 := by
  simp [legendreP, legCoeff]

lemma legendreP_one : legendreP 1 = X := by
  rw [legendreP_eq_sum, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : legCoeff 1 0 = 1 := legCoeff_zero 1
  have h1 : legCoeff 1 1 = -2 := by norm_num [legCoeff]
  rw [h0, h1]
  have hm : (C (-2 : ℝ) : Polynomial ℝ) * C (1 / 2 : ℝ) = -1 := by
    rw [← C_mul]; norm_num
  calc
    C (1 : ℝ) * (C (1 / 2 : ℝ) * (1 - X)) ^ 0 + C (-2 : ℝ) * (C (1 / 2 : ℝ) * (1 - X)) ^ 1
      = 1 + (C (-2 : ℝ) * C (1 / 2 : ℝ)) * (1 - X) := by simp [pow_zero, pow_one, mul_assoc]
    _ = 1 + (-1) * (1 - X) := by rw [hm]
    _ = X := by ring

lemma shiftY_eq : (C (1 / 2 : ℝ) * (1 - X) : Polynomial ℝ) = C (-1 / 2 : ℝ) * X + C (1 / 2 : ℝ) := by
  have hneg : (C (-1 / 2 : ℝ) : Polynomial ℝ) = -C (1 / 2 : ℝ) := by
    rw [← C_neg]; congr 1; ring
  rw [hneg]; ring

lemma shiftY_natDegree : (C (1 / 2 : ℝ) * (1 - X) : Polynomial ℝ).natDegree = 1 := by
  rw [shiftY_eq]
  compute_degree!

lemma shiftY_leadingCoeff : (C (1 / 2 : ℝ) * (1 - X) : Polynomial ℝ).leadingCoeff = -1 / 2 := by
  rw [leadingCoeff, shiftY_natDegree, shiftY_eq]
  simp

lemma legendreP_natDegree_le (n : ℕ) : (legendreP n).natDegree ≤ n := by
  rw [legendreP_eq_sum]
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc
    (C (legCoeff n k) * (C (1 / 2 : ℝ) * (1 - X)) ^ k).natDegree
      ≤ (C (legCoeff n k)).natDegree + ((C (1 / 2 : ℝ) * (1 - X)) ^ k).natDegree :=
        natDegree_mul_le
    _ ≤ 0 + k * (C (1 / 2 : ℝ) * (1 - X)).natDegree := by
        rw [natDegree_C]
        exact Nat.add_le_add_left natDegree_pow_le 0
    _ = k := by rw [shiftY_natDegree]; omega
    _ ≤ n := hkn

lemma legendreP_coeff_top (n : ℕ) :
    (legendreP n).coeff n = (Nat.choose (2 * n) n : ℝ) / 2 ^ n := by
  rw [legendreP_eq_sum, finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · have hdeg : ((C (1 / 2 : ℝ) * (1 - X) : Polynomial ℝ) ^ n).natDegree = n := by
      rw [natDegree_pow, shiftY_natDegree, mul_one]
    have hlc : ((C (1 / 2 : ℝ) * (1 - X) : Polynomial ℝ) ^ n).coeff n = (-1 / 2 : ℝ) ^ n := by
      have h := leadingCoeff_pow (C (1 / 2 : ℝ) * (1 - X)) n
      rw [leadingCoeff, hdeg, shiftY_leadingCoeff] at h
      exact h
    rw [coeff_C_mul, hlc]
    unfold legCoeff
    have hnn : n + n = 2 * n := by omega
    rw [hnn, Nat.choose_self]
    have h1 : (-1 : ℝ) ^ n * (-1 / 2 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
      rw [← mul_pow]; norm_num
    push_cast
    calc
      (-1 : ℝ) ^ n * (1 * (Nat.choose (2 * n) n : ℝ)) * (-1 / 2 : ℝ) ^ n
        = (Nat.choose (2 * n) n : ℝ) * ((-1 : ℝ) ^ n * (-1 / 2 : ℝ) ^ n) := by ring
      _ = (Nat.choose (2 * n) n : ℝ) * (1 / 2 : ℝ) ^ n := by rw [h1]
      _ = (Nat.choose (2 * n) n : ℝ) / 2 ^ n := by rw [one_div, inv_pow, div_eq_mul_inv]
  · intro k hk hkn
    have hlt : k < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkn
    apply coeff_eq_zero_of_natDegree_lt
    calc
      (C (legCoeff n k) * (C (1 / 2 : ℝ) * (1 - X)) ^ k).natDegree
        ≤ (C (legCoeff n k)).natDegree + ((C (1 / 2 : ℝ) * (1 - X)) ^ k).natDegree :=
          natDegree_mul_le
      _ ≤ 0 + k * (C (1 / 2 : ℝ) * (1 - X)).natDegree := by
          rw [natDegree_C]; exact Nat.add_le_add_left natDegree_pow_le 0
      _ = k := by rw [shiftY_natDegree]; omega
      _ < n := hlt
  · simp

lemma legendreP_coeff_top_pos (n : ℕ) : 0 < (legendreP n).coeff n := by
  rw [legendreP_coeff_top]
  apply div_pos
  · exact_mod_cast Nat.choose_pos (by omega : n ≤ 2 * n)
  · positivity

lemma legendreP_natDegree (n : ℕ) : (legendreP n).natDegree = n := by
  apply le_antisymm (legendreP_natDegree_le n)
  exact le_natDegree_of_ne_zero (ne_of_gt (legendreP_coeff_top_pos n))

lemma legendreP_leadingCoeff (n : ℕ) :
    (legendreP n).leadingCoeff = (Nat.choose (2 * n) n : ℝ) / 2 ^ n := by
  rw [leadingCoeff, legendreP_natDegree, legendreP_coeff_top]

lemma legendreP_leadingCoeff_pos (n : ℕ) : 0 < (legendreP n).leadingCoeff := by
  rw [leadingCoeff, legendreP_natDegree]
  exact legendreP_coeff_top_pos n

lemma legendreP_ne_zero (n : ℕ) : legendreP n ≠ 0 := by
  intro h
  have := legendreP_leadingCoeff_pos n
  rw [h, leadingCoeff_zero] at this
  linarith

lemma legendreP_leadingCoeff_ratio (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * (legendreP (n + 1)).leadingCoeff =
      ((2 * n + 1 : ℕ) : ℝ) * (legendreP n).leadingCoeff := by
  rw [legendreP_leadingCoeff, legendreP_leadingCoeff]
  have h1 : Nat.choose (2 * (n + 1)) (n + 1) * (n + 1) =
      2 * (2 * n + 1) * Nat.choose (2 * n) n := by
    have ha := Nat.add_one_mul_choose_eq (2 * n + 1) n
    have h2n : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    have hsub : 2 * n + 1 - n = n + 1 := by omega
    have hsym : Nat.choose (2 * n + 1) (n + 1) = Nat.choose (2 * n + 1) n := by
      have := Nat.choose_symm (by omega : n ≤ 2 * n + 1)
      rwa [hsub] at this
    have hc := Nat.add_one_mul_choose_eq (2 * n) n
    rw [h2n]
    nlinarith [ha, hc, hsym]
  have h1r : (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) * ((n + 1 : ℕ) : ℝ) =
      2 * ((2 * n + 1 : ℕ) : ℝ) * (Nat.choose (2 * n) n : ℝ) := by
    have : ((Nat.choose (2 * (n + 1)) (n + 1) * (n + 1) : ℕ) : ℝ) =
        ((2 * (2 * n + 1) * Nat.choose (2 * n) n : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this ⊢
    linarith
  rw [pow_succ]
  have h2p : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp [h2p]
  linarith

/-- Key polynomial identity for the Legendre differential operator acting on `Y^k`,
where `Y = (1 - X) / 2`. -/
lemma legendre_op_shiftY_pow (k : ℕ) :
    (((1 - X ^ 2 : Polynomial ℝ) * ((C (1 / 2 : ℝ) * (1 - X)) ^ k).derivative)).derivative =
      C ((k : ℝ) ^ 2) * (C (1 / 2 : ℝ) * (1 - X)) ^ (k - 1) -
        C ((k : ℝ) * ((k : ℝ) + 1)) * (C (1 / 2 : ℝ) * (1 - X)) ^ k := by
  set Y : Polynomial ℝ := C (1 / 2 : ℝ) * (1 - X) with hY
  have hYd : Y.derivative = C (-1 / 2 : ℝ) := by
    rw [hY, derivative_C_mul, derivative_sub, derivative_one, derivative_X]
    have hneg : (C (-1 / 2 : ℝ) : Polynomial ℝ) = -C (1 / 2 : ℝ) := by
      rw [← C_neg]; congr 1; ring
    rw [hneg]; ring
  have h1mX2 : (1 - X ^ 2 : Polynomial ℝ) = C 4 * Y * (1 - Y) := by
    rw [hY]
    have h42 : (C 4 : Polynomial ℝ) * C (1 / 2 : ℝ) = C 2 := by rw [← C_mul]; norm_num
    have h22 : (C 2 : Polynomial ℝ) * C (1 / 2 : ℝ) = 1 := by rw [← C_mul]; norm_num
    have hC2 : (C (2 : ℝ) : Polynomial ℝ) = 1 + 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, C_add, C_1]
    have h1pX : C (2 : ℝ) * (1 - C (1 / 2 : ℝ) * (1 - X)) = 1 + X := by
      calc
        C (2 : ℝ) * (1 - C (1 / 2 : ℝ) * (1 - X))
          = C 2 - (C 2 * C (1 / 2 : ℝ)) * (1 - X) := by ring
        _ = (1 + 1) - 1 * (1 - X) := by rw [h22, hC2]
        _ = 1 + X := by ring
    calc
      (1 - X ^ 2 : Polynomial ℝ)
        = (1 - X) * (1 + X) := by ring
      _ = (1 - X) * (C 2 * (1 - C (1 / 2 : ℝ) * (1 - X))) := by rw [h1pX]
      _ = (C 2 * (1 - X)) * (1 - C (1 / 2 : ℝ) * (1 - X)) := by ring
      _ = C 4 * (C (1 / 2 : ℝ) * (1 - X)) * (1 - C (1 / 2 : ℝ) * (1 - X)) := by
          rw [← mul_assoc (C 4), h42]
  cases k with
  | zero =>
    simp
  | succ m =>
    have hpow : (Y ^ (m + 1)).derivative = C ((m + 1 : ℕ) : ℝ) * Y ^ m * C (-1 / 2 : ℝ) := by
      rw [derivative_pow, hYd, C_eq_natCast]
      simp only [Nat.add_sub_cancel]
    have hmul : (1 - X ^ 2) * (Y ^ (m + 1)).derivative =
        C (-2 * ((m + 1 : ℕ) : ℝ)) * (Y ^ (m + 1) - Y ^ (m + 2)) := by
      rw [h1mX2, hpow]
      have h4 : (C 4 : Polynomial ℝ) * C (-1 / 2 : ℝ) = C (-2 : ℝ) := by
        rw [← C_mul]; norm_num
      calc
        C 4 * Y * (1 - Y) * (C ((m + 1 : ℕ) : ℝ) * Y ^ m * C (-1 / 2 : ℝ))
          = (C 4 * C (-1 / 2 : ℝ)) * C ((m + 1 : ℕ) : ℝ) * (Y * Y ^ m * (1 - Y)) := by ring
        _ = C (-2 : ℝ) * C ((m + 1 : ℕ) : ℝ) * (Y ^ (m + 1) - Y ^ (m + 2)) := by
            rw [h4]; ring
        _ = C (-2 * ((m + 1 : ℕ) : ℝ)) * (Y ^ (m + 1) - Y ^ (m + 2)) := by
            rw [← C_mul]
    rw [hmul, derivative_C_mul, derivative_sub, derivative_pow, derivative_pow, hYd]
    have hsub1 : m + 1 - 1 = m := by omega
    have hsub2 : m + 2 - 1 = m + 1 := by omega
    rw [hsub1, hsub2, mul_sub]
    have hC1 : C (-2 * ((m + 1 : ℕ) : ℝ)) * (C ((m + 1 : ℕ) : ℝ) * Y ^ m * C (-1 / 2 : ℝ)) =
        C ((((m + 1 : ℕ) : ℝ)) ^ 2) * Y ^ m := by
      calc
        C (-2 * ((m + 1 : ℕ) : ℝ)) * (C ((m + 1 : ℕ) : ℝ) * Y ^ m * C (-1 / 2 : ℝ))
          = (C (-2 * ((m + 1 : ℕ) : ℝ)) * C ((m + 1 : ℕ) : ℝ) * C (-1 / 2 : ℝ)) * Y ^ m := by ring
        _ = C (((m + 1 : ℕ) : ℝ) ^ 2) * Y ^ m := by
            rw [← C_mul, ← C_mul]; congr 1; ring
    have hC2 : C (-2 * ((m + 1 : ℕ) : ℝ)) * (C ((m + 2 : ℕ) : ℝ) * Y ^ (m + 1) * C (-1 / 2 : ℝ)) =
        C (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 1)) * Y ^ (m + 1) := by
      calc
        C (-2 * ((m + 1 : ℕ) : ℝ)) * (C ((m + 2 : ℕ) : ℝ) * Y ^ (m + 1) * C (-1 / 2 : ℝ))
          = (C (-2 * ((m + 1 : ℕ) : ℝ)) * C ((m + 2 : ℕ) : ℝ) * C (-1 / 2 : ℝ)) * Y ^ (m + 1) := by ring
        _ = C (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 1)) * Y ^ (m + 1) := by
            rw [← C_mul, ← C_mul]; congr 1; push_cast; ring
    rw [hC1, hC2]

/-- The Legendre differential equation: `((1 - X^2) P_n')' + n(n+1) P_n = 0`. -/
theorem legendreP_ode (n : ℕ) :
    ((1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative).derivative +
      C ((n : ℝ) * ((n : ℝ) + 1)) * legendreP n = 0 := by
  set Y : Polynomial ℝ := C (1 / 2 : ℝ) * (1 - X)
  rw [legendreP_eq_sum, derivative_sum, Finset.mul_sum, derivative_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((1 - X ^ 2 : Polynomial ℝ) * (C (legCoeff n k) * Y ^ k).derivative).derivative +
        C ((n : ℝ) * ((n : ℝ) + 1)) * (C (legCoeff n k) * Y ^ k) =
      C ((k : ℝ) ^ 2 * legCoeff n k) * Y ^ (k - 1) +
        C (((n : ℝ) * ((n : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1)) * legCoeff n k) * Y ^ k := by
    intro k _
    rw [derivative_C_mul, mul_left_comm, derivative_C_mul, legendre_op_shiftY_pow]
    calc
      C (legCoeff n k) * (C ((k : ℝ) ^ 2) * Y ^ (k - 1) - C ((k : ℝ) * ((k : ℝ) + 1)) * Y ^ k) +
          C ((n : ℝ) * ((n : ℝ) + 1)) * (C (legCoeff n k) * Y ^ k)
        = (C (legCoeff n k) * C ((k : ℝ) ^ 2)) * Y ^ (k - 1) +
            (C ((n : ℝ) * ((n : ℝ) + 1)) * C (legCoeff n k) -
              C (legCoeff n k) * C ((k : ℝ) * ((k : ℝ) + 1))) * Y ^ k := by ring
      _ = C ((k : ℝ) ^ 2 * legCoeff n k) * Y ^ (k - 1) +
            C (((n : ℝ) * ((n : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1)) * legCoeff n k) * Y ^ k := by
          rw [← C_mul, ← C_mul, ← C_mul, ← C_sub]
          congr 2 <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hsum1 : ∑ k ∈ Finset.range (n + 1), C ((k : ℝ) ^ 2 * legCoeff n k) * Y ^ (k - 1) =
      ∑ m ∈ Finset.range n, C (((m + 1 : ℕ) : ℝ) ^ 2 * legCoeff n (m + 1)) * Y ^ m := by
    rw [Finset.sum_range_succ']
    simp
  have hsum2 : ∑ k ∈ Finset.range (n + 1),
        C (((n : ℝ) * ((n : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1)) * legCoeff n k) * Y ^ k =
      ∑ m ∈ Finset.range n,
        C (((n : ℝ) * ((n : ℝ) + 1) - (m : ℝ) * ((m : ℝ) + 1)) * legCoeff n m) * Y ^ m := by
    rw [Finset.sum_range_succ]
    simp
  rw [hsum1, hsum2, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro m _
  rw [legCoeff_succ]
  simp only [C_neg, neg_mul, neg_add_cancel]

lemma legendreP_ode_eval (n : ℕ) (t : ℝ) :
    ((1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative).derivative.eval t +
      (n : ℝ) * ((n : ℝ) + 1) * (legendreP n).eval t = 0 := by
  have h := congr_arg (fun p => p.eval t) (legendreP_ode n)
  simpa [eval_add, eval_mul, eval_C] using h

/-- Orthogonality of distinct Legendre polynomials on `[-1, 1]`, proved directly from the ODE. -/
theorem legendreP_orthog {m n : ℕ} (hmn : m ≠ n) :
    ∫ t in (-1 : ℝ)..1, (legendreP m).eval t * (legendreP n).eval t = 0 := by
  let A : Polynomial ℝ := (1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative
  let B : Polynomial ℝ := (1 - X ^ 2 : Polynomial ℝ) * (legendreP m).derivative
  let G : Polynomial ℝ := A * legendreP m - B * legendreP n
  have hdA : A.derivative = -C ((n : ℝ) * ((n : ℝ) + 1)) * legendreP n := by
    have := eq_neg_of_add_eq_zero_left (legendreP_ode n)
    simpa [A, neg_mul] using this
  have hdB : B.derivative = -C ((m : ℝ) * ((m : ℝ) + 1)) * legendreP m := by
    have := eq_neg_of_add_eq_zero_left (legendreP_ode m)
    simpa [B, neg_mul] using this
  have hGderiv : G.derivative =
      C (((m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1))) * (legendreP m * legendreP n) := by
    have hsub : (A * legendreP m - B * legendreP n).derivative =
        (A * legendreP m).derivative - (B * legendreP n).derivative := derivative_sub
    have hm1 : (A * legendreP m).derivative =
        A.derivative * legendreP m + A * (legendreP m).derivative := derivative_mul
    have hm2 : (B * legendreP n).derivative =
        B.derivative * legendreP n + B * (legendreP n).derivative := derivative_mul
    calc
      G.derivative = (A.derivative * legendreP m + A * (legendreP m).derivative) -
          (B.derivative * legendreP n + B * (legendreP n).derivative) := by
            change (A * legendreP m - B * legendreP n).derivative = _
            rw [hsub, hm1, hm2]
      _ = C (((m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1))) * (legendreP m * legendreP n) := by
            rw [hdA, hdB, C_sub]; dsimp only [A, B]; ring
  have hint : ∫ t in (-1 : ℝ)..1, G.derivative.eval t = G.eval 1 - G.eval (-1) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => G.hasDerivAt t) ?_
    exact G.derivative.continuous.intervalIntegrable (-1) 1
  have hG1 : G.eval 1 = 0 := by simp [G, A, B]
  have hGm1 : G.eval (-1) = 0 := by simp [G, A, B]
  rw [hG1, hGm1, sub_self, hGderiv] at hint
  simp only [eval_mul, eval_C] at hint
  rw [intervalIntegral.integral_const_mul] at hint
  have hne : ((m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1)) ≠ 0 := by
    intro heq
    have hfac : ((m : ℝ) - (n : ℝ)) * ((m : ℝ) + (n : ℝ) + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h | h
    · exact hmn (by exact_mod_cast sub_eq_zero.mp h)
    · have hpos : (0 : ℝ) < (m : ℝ) + (n : ℝ) + 1 := by positivity
      linarith
  exact (mul_eq_zero.mp hint).resolve_left hne

/-- Any polynomial of degree `≤ d` is a linear combination of `legendreP 0, ..., legendreP d`. -/
lemma poly_eq_sum_legendreP (q : Polynomial ℝ) :
    ∃ c : ℕ → ℝ, q = ∑ k ∈ Finset.range (q.natDegree + 1), C (c k) * legendreP k := by
  induction hd : q.natDegree using Nat.strong_induction_on generalizing q with
  | h d ih =>
    by_cases hq : q = 0
    · refine ⟨fun _ => 0, ?_⟩
      simp [hq]
    · by_cases hd0 : d = 0
      · refine ⟨fun _ => q.coeff 0, ?_⟩
        rw [hd0, Finset.sum_range_one, legendreP_zero, mul_one]
        exact eq_C_of_natDegree_eq_zero (hd.trans hd0)
      · set α : ℝ := q.leadingCoeff / (legendreP d).leadingCoeff
        set r : Polynomial ℝ := q - C α * legendreP d
        have hr_lt : r.natDegree < d := by
          have hdeg_term : (C α * legendreP d).natDegree = d := by
            have hα : α ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hq)
              (ne_of_gt (legendreP_leadingCoeff_pos d))
            rw [natDegree_C_mul hα, legendreP_natDegree]
          have hr_le : r.natDegree ≤ d := by
            calc r.natDegree ≤ max q.natDegree (C α * legendreP d).natDegree := natDegree_sub_le _ _
              _ = d := by rw [hd, hdeg_term, max_self]
          have hcoeff_d : r.coeff d = 0 := by
            simp only [r, coeff_sub, coeff_C_mul]
            have hqtop : q.coeff d = q.leadingCoeff := by rw [← hd, coeff_natDegree]
            have hPtop : (legendreP d).coeff d = (legendreP d).leadingCoeff := by
              rw [leadingCoeff, legendreP_natDegree]
            rw [hqtop, hPtop, div_mul_cancel₀ _ (ne_of_gt (legendreP_leadingCoeff_pos d)), sub_self]
          by_contra hge
          push Not at hge
          have hreq : r.natDegree = d := le_antisymm hr_le hge
          have hr0 : r ≠ 0 := by intro hr; rw [hr, natDegree_zero] at hreq; exact hd0 hreq.symm
          have := leadingCoeff_ne_zero.mpr hr0
          rw [leadingCoeff, hreq] at this
          exact this hcoeff_d
        obtain ⟨c', hc'⟩ := ih r.natDegree hr_lt r rfl
        set dr := r.natDegree with hdr
        refine ⟨fun k => if k ≤ dr then c' k else if k = d then α else 0, ?_⟩
        rw [Finset.sum_range_succ]
        dsimp only
        rw [if_neg (not_le.mpr hr_lt), if_pos rfl]
        have hsum_eq : ∑ k ∈ Finset.range d,
            C (if k ≤ dr then c' k else if k = d then α else 0) * legendreP k = r := by
          rw [hc']
          symm
          refine Finset.sum_subset_zero_on_sdiff (Finset.range_mono (Nat.succ_le_of_lt hr_lt)) ?_ ?_
          · intro k hk
            simp only [Finset.mem_sdiff, Finset.mem_range] at hk
            have hkn : ¬ k ≤ dr := by omega
            have hkd : k ≠ d := ne_of_lt hk.1
            simp [hkn, hkd]
          · intro k hk
            have hkle : k ≤ dr := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            simp [hkle]
        rw [hsum_eq]
        simp [r]

lemma legendreP_orthog_lt {n : ℕ} {q : Polynomial ℝ} (hq : q.natDegree < n) :
    ∫ t in (-1 : ℝ)..1, (legendreP n).eval t * q.eval t = 0 := by
  obtain ⟨c, hc⟩ := poly_eq_sum_legendreP q
  have hfn : ∀ t : ℝ, (legendreP n).eval t * q.eval t =
      ∑ k ∈ Finset.range (q.natDegree + 1), c k * ((legendreP k).eval t * (legendreP n).eval t) := by
    intro t
    conv_lhs => rw [hc]
    rw [eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [eval_mul, eval_C]; ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro k hk
    rw [intervalIntegral.integral_const_mul]
    have hkn : k ≠ n := by
      have := Finset.mem_range.mp hk
      omega
    rw [legendreP_orthog hkn, mul_zero]
  · intro k _
    exact (Continuous.intervalIntegrable (by fun_prop) (-1) 1)

lemma poly_eq_zero_of_integral_sq_eq_zero {R : Polynomial ℝ}
    (h : ∫ t in (-1 : ℝ)..1, (R.eval t) ^ 2 = 0) : R = 0 := by
  have hzero : ∀ t ∈ Set.Icc (-1 : ℝ) 1, (R.eval t) ^ 2 = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at h
    have hzero_io : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, (R.eval t) ^ 2 = 0 := by
      have hae : (fun t => (R.eval t) ^ 2) =ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)] 0 :=
        (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
          (Filter.Eventually.of_forall fun t => sq_nonneg (R.eval t))
          ((R.continuous.pow 2).integrableOn_Ioc)).mp h
      intro t ht
      by_contra hne
      have hpos : 0 < (R.eval t) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have hopen : IsOpen {x : ℝ | 0 < (R.eval x) ^ 2} :=
        isOpen_lt continuous_const (R.continuous.pow 2)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t hpos
      set δ := min ε (min (t + 1) (1 - t))
      have hδ : 0 < δ := by
        simp only [δ, lt_min_iff]; exact ⟨hε, by linarith [ht.1], by linarith [ht.2]⟩
      have hsub : Set.Ioo (t - δ) (t + δ) ⊆ Set.Ioc (-1 : ℝ) 1 := fun x hx =>
        ⟨by linarith [hx.1, min_le_right ε (min (t + 1) (1 - t)), min_le_left (t + 1) (1 - t)],
         by linarith [hx.2, min_le_right ε (min (t + 1) (1 - t)), min_le_right (t + 1) (1 - t)]⟩
      have hpos_on : ∀ x ∈ Set.Ioo (t - δ) (t + δ), 0 < (R.eval x) ^ 2 := fun x hx =>
        hball (by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          exact ⟨by linarith [hx.1, min_le_left ε (min (t + 1) (1 - t))],
                 by linarith [hx.2, min_le_left ε (min (t + 1) (1 - t))]⟩)
      have hmeas_pos : 0 < volume (Set.Ioo (t - δ) (t + δ)) := by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
      have hzero_ae' : volume {x : ℝ | ¬ (x ∈ Set.Ioc (-1 : ℝ) 1 → (R.eval x) ^ 2 = 0)} = 0 :=
        (ae_restrict_iff' measurableSet_Ioc).mp hae
      have hsub2 : Set.Ioo (t - δ) (t + δ) ⊆
          {x : ℝ | ¬ (x ∈ Set.Ioc (-1 : ℝ) 1 → (R.eval x) ^ 2 = 0)} :=
        fun x hx h0 => ne_of_gt (hpos_on x hx) (h0 (hsub hx))
      have hsub_null : volume (Set.Ioo (t - δ) (t + δ)) = 0 :=
        measure_mono_null hsub2 hzero_ae'
      exact ne_of_gt hmeas_pos hsub_null
    intro t ht
    have hcl : t ∈ closure (Set.Ioo (-1 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]; exact ht
    exact closure_minimal hzero_io (isClosed_eq (R.continuous.pow 2) continuous_const) hcl
  by_contra hR
  have hfin : (R.roots.toFinset : Set ℝ).Finite := Finset.finite_toSet _
  have hinf : (Set.Icc (-1 : ℝ) 1).Infinite := Set.Icc_infinite (by norm_num)
  obtain ⟨t, htI, htNot⟩ := (hinf.sdiff hfin).nonempty
  have hRt : R.eval t = 0 := sq_eq_zero_iff.mp (hzero t htI)
  exact htNot (Multiset.mem_toFinset.mpr ((mem_roots hR).mpr hRt))

lemma legendreP_integral_sq_pos (n : ℕ) :
    0 < ∫ t in (-1 : ℝ)..1, ((legendreP n).eval t) ^ 2 := by
  have hnn : 0 ≤ ∫ t in (-1 : ℝ)..1, ((legendreP n).eval t) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  refine lt_of_le_of_ne hnn fun h0 => ?_
  exact legendreP_ne_zero n (poly_eq_zero_of_integral_sq_eq_zero h0.symm)

lemma eq_smul_legendreP_of_orthog {n : ℕ} {P : Polynomial ℝ}
    (hdeg : P.natDegree = n)
    (horth : ∀ q : Polynomial ℝ, q.natDegree < n → ∫ t in (-1 : ℝ)..1, P.eval t * q.eval t = 0) :
    P = C (P.leadingCoeff / (legendreP n).leadingCoeff) * legendreP n := by
  set c : ℝ := P.leadingCoeff / (legendreP n).leadingCoeff
  set R : Polynomial ℝ := P - C c * legendreP n
  suffices hR : R = 0 by exact sub_eq_zero.mp hR
  by_cases hR0 : R = 0
  · exact hR0
  · have hRdeg : R.natDegree < n := by
      have hle : R.natDegree ≤ n := by
        calc R.natDegree ≤ max P.natDegree (C c * legendreP n).natDegree := natDegree_sub_le _ _
          _ ≤ max n n := by
              apply max_le_max (le_of_eq hdeg)
              calc (C c * legendreP n).natDegree ≤ (C c).natDegree + (legendreP n).natDegree :=
                    natDegree_mul_le
                _ = n := by rw [natDegree_C, zero_add, legendreP_natDegree]
          _ = n := max_self n
      have htop : R.coeff n = 0 := by
        simp only [R, coeff_sub, coeff_C_mul]
        have h1 : P.coeff n = P.leadingCoeff := by rw [← hdeg, coeff_natDegree]
        have h2 : (legendreP n).coeff n = (legendreP n).leadingCoeff := by
          rw [leadingCoeff, legendreP_natDegree]
        rw [h1, h2, div_mul_cancel₀ _ (ne_of_gt (legendreP_leadingCoeff_pos n)), sub_self]
      by_contra hge
      push Not at hge
      have heq : R.natDegree = n := le_antisymm hle hge
      have := leadingCoeff_ne_zero.mpr hR0
      rw [leadingCoeff, heq] at this
      exact this htop
    have hint : ∫ t in (-1 : ℝ)..1, (R.eval t) ^ 2 = 0 := by
      have hsplit : ∀ t : ℝ, (R.eval t) ^ 2 =
          P.eval t * R.eval t - c * ((legendreP n).eval t * R.eval t) := by
        intro t; simp only [R, eval_sub, eval_mul, eval_C]; ring
      simp_rw [hsplit]
      rw [intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_const_mul, horth R hRdeg, legendreP_orthog_lt hRdeg]
      ring
    exact poly_eq_zero_of_integral_sq_eq_zero hint

/-- Parity symmetry: `P_n(-t) = (-1)^n P_n(t)`. -/
lemma legendreP_comp_neg (n : ℕ) :
    (legendreP n).comp (-X) = C ((-1 : ℝ) ^ n) * legendreP n := by
  set Q : Polynomial ℝ := (legendreP n).comp (-X)
  have hQdeg : Q.natDegree = n := by
    rw [natDegree_comp, legendreP_natDegree, natDegree_neg, natDegree_X, mul_one]
  have hQlc : Q.leadingCoeff = (-1 : ℝ) ^ n * (legendreP n).leadingCoeff := by
    have hlc := leadingCoeff_comp (p := legendreP n) (q := (-X : Polynomial ℝ))
      (by rw [natDegree_neg, natDegree_X]; exact Nat.one_ne_zero)
    rw [legendreP_natDegree, leadingCoeff_neg, leadingCoeff_X] at hlc
    rw [hlc, mul_comm]
  have hQorth : ∀ q : Polynomial ℝ, q.natDegree < n →
      ∫ t in (-1 : ℝ)..1, Q.eval t * q.eval t = 0 := by
    intro q hq
    have hfn : ∀ t : ℝ, Q.eval t * q.eval t =
        (legendreP n).eval (-t) * (q.comp (-X)).eval (-t) := by
      intro t; simp [Q, eval_comp]
    simp_rw [hfn]
    have hcomp := intervalIntegral.integral_comp_neg
      (fun u => (legendreP n).eval u * (q.comp (-X)).eval u) (a := (-1 : ℝ)) (b := 1)
    simp only [neg_neg] at hcomp
    have hqdeg' : (q.comp (-X)).natDegree < n := by
      rw [natDegree_comp, natDegree_neg, natDegree_X, mul_one]; exact hq
    exact hcomp.trans (legendreP_orthog_lt hqdeg')
  have heq := eq_smul_legendreP_of_orthog hQdeg hQorth
  rw [hQlc, mul_div_cancel_right₀ _ (ne_of_gt (legendreP_leadingCoeff_pos n))] at heq
  exact heq

lemma legendreP_eval_neg (n : ℕ) (t : ℝ) :
    (legendreP n).eval (-t) = (-1 : ℝ) ^ n * (legendreP n).eval t := by
  have h := congr_arg (fun p => p.eval t) (legendreP_comp_neg n)
  simpa [eval_comp] using h

lemma legendreP_eval_neg_one (n : ℕ) : (legendreP n).eval (-1) = (-1 : ℝ) ^ n := by
  have h := legendreP_eval_neg n 1
  rw [legendreP_eval_one, mul_one] at h
  exact h

/-- Three-term recurrence: `(n + 1) P_{n+1} = (2n + 1) X P_n - n P_{n-1}` for `n ≥ 1`. -/
theorem legendreP_three_term (n : ℕ) (hn : 1 ≤ n) :
    C ((n + 1 : ℕ) : ℝ) * legendreP (n + 1) =
      C ((2 * n + 1 : ℕ) : ℝ) * X * legendreP n - C (n : ℝ) * legendreP (n - 1) := by
  set D : Polynomial ℝ :=
    C ((n + 1 : ℕ) : ℝ) * legendreP (n + 1) -
      (C ((2 * n + 1 : ℕ) : ℝ) * X * legendreP n - C (n : ℝ) * legendreP (n - 1))
  suffices hD : D = 0 by exact sub_eq_zero.mp hD
  have hD_le : D.natDegree ≤ n := by
    have h1 : (C ((n + 1 : ℕ) : ℝ) * legendreP (n + 1)).natDegree ≤ n + 1 := by
      calc _ ≤ (C ((n + 1 : ℕ) : ℝ)).natDegree + (legendreP (n + 1)).natDegree := natDegree_mul_le
        _ = n + 1 := by rw [natDegree_C, zero_add, legendreP_natDegree]
    have h2 : (C ((2 * n + 1 : ℕ) : ℝ) * X * legendreP n).natDegree ≤ n + 1 := by
      calc _ ≤ (C ((2 * n + 1 : ℕ) : ℝ) * X).natDegree + (legendreP n).natDegree := natDegree_mul_le
        _ ≤ (0 + 1) + n := by
            apply Nat.add_le_add _ (le_of_eq (legendreP_natDegree n))
            calc _ ≤ (C ((2 * n + 1 : ℕ) : ℝ)).natDegree + X.natDegree := natDegree_mul_le
              _ = 0 + 1 := by rw [natDegree_C, natDegree_X]
        _ = n + 1 := by omega
    have h3 : (C (n : ℝ) * legendreP (n - 1)).natDegree < n + 1 := by
      calc _ ≤ (C (n : ℝ)).natDegree + (legendreP (n - 1)).natDegree := natDegree_mul_le
        _ = n - 1 := by rw [natDegree_C, zero_add, legendreP_natDegree]
        _ < n + 1 := by omega
    have hle1 : D.natDegree ≤ n + 1 := by
      have := natDegree_sub_le_of_le h1 (natDegree_sub_le_of_le h2 (le_of_lt h3))
      simpa [D] using this
    have htop : D.coeff (n + 1) = 0 := by
      simp only [D, coeff_sub, coeff_C_mul]
      have h3' : (legendreP (n - 1)).coeff (n + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [legendreP_natDegree]; omega)
      rw [mul_assoc, coeff_C_mul, coeff_X_mul, h3', mul_zero, sub_zero]
      have ha : (legendreP (n + 1)).coeff (n + 1) = (legendreP (n + 1)).leadingCoeff := by
        rw [leadingCoeff, legendreP_natDegree]
      have hb : (legendreP n).coeff n = (legendreP n).leadingCoeff := by
        rw [leadingCoeff, legendreP_natDegree]
      rw [ha, hb, legendreP_leadingCoeff_ratio n, sub_self]
    by_contra hgt
    push Not at hgt
    have heq : D.natDegree = n + 1 := le_antisymm hle1 hgt
    have hDne : D ≠ 0 := by intro h; rw [h, natDegree_zero] at heq; omega
    have := leadingCoeff_ne_zero.mpr hDne
    rw [leadingCoeff, heq] at this
    exact this htop
  -- Expand D in the Legendre basis up to degree D.natDegree ≤ n
  obtain ⟨c, hc⟩ := poly_eq_sum_legendreP D
  -- Helper: D ⊥ P_k for k ≠ n - 1 and k ≤ n
  have hDorth : ∀ k, k ≤ n → k ≠ n - 1 →
      ∫ t in (-1 : ℝ)..1, D.eval t * (legendreP k).eval t = 0 := by
    intro k hk hkne
    by_cases hkn : k < n - 1
    · have hfn : ∀ t : ℝ, D.eval t * (legendreP k).eval t =
          ((n + 1 : ℕ) : ℝ) * ((legendreP (n + 1)).eval t * (legendreP k).eval t) -
            (((2 * n + 1 : ℕ) : ℝ) * ((legendreP n).eval t * (X * legendreP k).eval t) -
              (n : ℝ) * ((legendreP (n - 1)).eval t * (legendreP k).eval t)) := by
        intro t; simp only [D, eval_sub, eval_mul, eval_C, eval_X]; ring
      simp_rw [hfn]
      rw [intervalIntegral.integral_sub
            (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_sub
            (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      have hqdeg : (X * legendreP k).natDegree < n := by
        rw [natDegree_X_mul (legendreP_ne_zero k), legendreP_natDegree]; omega
      rw [legendreP_orthog (by omega : n + 1 ≠ k), legendreP_orthog_lt hqdeg,
          legendreP_orthog (by omega : n - 1 ≠ k)]
      ring
    · have hkeq : k = n := by omega
      rw [hkeq]
      -- Odd integrand: D(-t) * P_n(-t) = - (D(t) * P_n(t))
      have hodd : ∀ t : ℝ, D.eval (-t) * (legendreP n).eval (-t) =
          -(D.eval t * (legendreP n).eval t) := by
        intro t
        simp only [D, eval_sub, eval_mul, eval_C, eval_X, legendreP_eval_neg]
        have hp0 : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
        have hp1 : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ n = -1 := by
          rw [pow_succ, mul_assoc, mul_comm (-1 : ℝ), ← mul_assoc, hp0]; ring
        have hp2 : (-1 : ℝ) ^ (n - 1) * (-1 : ℝ) ^ n = -1 := by
          obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
          rw [add_comm 1 m, Nat.add_sub_cancel, pow_succ, ← mul_assoc]
          have : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
          rw [this]; ring
        calc
          (((n + 1 : ℕ) : ℝ) * ((-1 : ℝ) ^ (n + 1) * (legendreP (n + 1)).eval t) -
              (((2 * n + 1 : ℕ) : ℝ) * (-t) * ((-1 : ℝ) ^ n * (legendreP n).eval t) -
                (n : ℝ) * ((-1 : ℝ) ^ (n - 1) * (legendreP (n - 1)).eval t))) *
            ((-1 : ℝ) ^ n * (legendreP n).eval t)
            = ((n + 1 : ℕ) : ℝ) * (legendreP (n + 1)).eval t * (legendreP n).eval t *
                ((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ n) +
              ((2 * n + 1 : ℕ) : ℝ) * t * (legendreP n).eval t * (legendreP n).eval t *
                ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) +
              (n : ℝ) * (legendreP (n - 1)).eval t * (legendreP n).eval t *
                ((-1 : ℝ) ^ (n - 1) * (-1 : ℝ) ^ n) := by ring
          _ = -((((n + 1 : ℕ) : ℝ) * (legendreP (n + 1)).eval t -
                (((2 * n + 1 : ℕ) : ℝ) * t * (legendreP n).eval t -
                  (n : ℝ) * (legendreP (n - 1)).eval t)) * (legendreP n).eval t) := by
              rw [hp0, hp1, hp2]; ring
      have hcomp := intervalIntegral.integral_comp_neg
        (fun t => D.eval t * (legendreP n).eval t) (a := (-1 : ℝ)) (b := 1)
      simp only [neg_neg] at hcomp
      have hneg : ∫ t in (-1 : ℝ)..1, D.eval (-t) * (legendreP n).eval (-t) =
          -(∫ t in (-1 : ℝ)..1, D.eval t * (legendreP n).eval t) := by
        simp_rw [hodd, intervalIntegral.integral_neg]
      linarith
  -- From orthogonality, c k = 0 for all k ∈ range (D.natDegree + 1) with k ≠ n - 1
  have hc_zero : ∀ k ∈ Finset.range (D.natDegree + 1), k ≠ n - 1 → c k = 0 := by
    intro k hk hkne
    have hkle : k ≤ n := by have := Finset.mem_range.mp hk; omega
    have hint0 := hDorth k hkle hkne
    have hfn : ∀ t : ℝ, D.eval t * (legendreP k).eval t =
        ∑ j ∈ Finset.range (D.natDegree + 1),
          c j * ((legendreP j).eval t * (legendreP k).eval t) := by
      intro t
      conv_lhs => rw [hc]
      rw [eval_finsetSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [eval_mul, eval_C]; ring
    simp_rw [hfn] at hint0
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
          Continuous.intervalIntegrable (by fun_prop) _ _)] at hint0
    rw [Finset.sum_eq_single k] at hint0
    · rw [intervalIntegral.integral_const_mul] at hint0
      have hsq : ∫ t in (-1 : ℝ)..1, (legendreP k).eval t * (legendreP k).eval t =
          ∫ t in (-1 : ℝ)..1, ((legendreP k).eval t) ^ 2 := by
        refine intervalIntegral.integral_congr fun t _ => (sq _).symm
      rw [hsq] at hint0
      exact (mul_eq_zero.mp hint0).resolve_right (ne_of_gt (legendreP_integral_sq_pos k))
    · intro j _ hjk
      rw [intervalIntegral.integral_const_mul, legendreP_orthog hjk, mul_zero]
    · intro hnot; exact absurd hk hnot
  -- Hence D = (if n - 1 ∈ range (D.natDegree + 1) then C (c (n-1)) * P_{n-1} else 0)
  by_cases hmem : n - 1 ∈ Finset.range (D.natDegree + 1)
  · have hDeq : D = C (c (n - 1)) * legendreP (n - 1) := by
      rw [hc, Finset.sum_eq_single (n - 1)]
      · intro k hk hkne; rw [hc_zero k hk hkne, C_0, zero_mul]
      · intro hnot; exact absurd hmem hnot
    have hD1 : D.eval 1 = 0 := by
      simp only [D, eval_sub, eval_mul, eval_C, eval_X, legendreP_eval_one]
      push_cast; ring
    have hc1 : c (n - 1) = 0 := by
      have := congr_arg (fun p => p.eval 1) hDeq
      simp only [hD1, eval_mul, eval_C, legendreP_eval_one, mul_one] at this
      exact this.symm
    rw [hDeq, hc1, C_0, zero_mul]
  · rw [hc]
    apply Finset.sum_eq_zero
    intro k hk
    have hkne : k ≠ n - 1 := fun h => hmem (h ▸ hk)
    rw [hc_zero k hk hkne, C_0, zero_mul]

/-- Exact $L^2([-1, 1])$ norm: `∫_{-1}^1 P_n(t)^2 dt = 2 / (2n + 1)`. -/
theorem legendreP_integral_sq (n : ℕ) :
    ∫ t in (-1 : ℝ)..1, ((legendreP n).eval t) ^ 2 = 2 / ((2 * n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero =>
    simp [legendreP_zero]; norm_num
  | succ k ih =>
    cases k with
    | zero =>
      rw [legendreP_one]
      have hderiv : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ 3 / 3) (t ^ 2) t := by
        intro t _
        have h := (hasDerivAt_pow 3 t).div_const (3 : ℝ)
        have heq : ((3 : ℕ) : ℝ) * t ^ (3 - 1) / 3 = t ^ 2 := by
          norm_num
        rwa [heq] at h
      have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      simp only [eval_X]
      rw [hint]; norm_num
    | succ m =>
      set k := m + 1
      have hk1 : 1 ≤ k := by omega
      have hrec1 := legendreP_three_term k hk1
      have h1 : ((k + 1 : ℕ) : ℝ) * ∫ t in (-1 : ℝ)..1, ((legendreP (k + 1)).eval t) ^ 2 =
          ((2 * k + 1 : ℕ) : ℝ) * ∫ t in (-1 : ℝ)..1, t * (legendreP k).eval t * (legendreP (k + 1)).eval t := by
        have hfn : ∀ t : ℝ, ((k + 1 : ℕ) : ℝ) * ((legendreP (k + 1)).eval t) ^ 2 =
            ((2 * k + 1 : ℕ) : ℝ) * (t * (legendreP k).eval t * (legendreP (k + 1)).eval t) -
              (k : ℝ) * ((legendreP (k - 1)).eval t * (legendreP (k + 1)).eval t) := by
          intro t
          have hv := congr_arg (fun p => p.eval t) hrec1
          simp only [eval_mul, eval_C, eval_sub, eval_X] at hv
          calc
            ((k + 1 : ℕ) : ℝ) * ((legendreP (k + 1)).eval t) ^ 2
              = (((k + 1 : ℕ) : ℝ) * (legendreP (k + 1)).eval t) * (legendreP (k + 1)).eval t := by ring
            _ = (((2 * k + 1 : ℕ) : ℝ) * t * (legendreP k).eval t -
                  (k : ℝ) * (legendreP (k - 1)).eval t) * (legendreP (k + 1)).eval t := by rw [hv]
            _ = _ := by ring
        rw [← intervalIntegral.integral_const_mul]
        simp_rw [hfn]
        rw [intervalIntegral.integral_sub
              (Continuous.intervalIntegrable (by fun_prop) _ _)
              (Continuous.intervalIntegrable (by fun_prop) _ _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            legendreP_orthog (by omega : k - 1 ≠ k + 1)]
        ring
      have hrec2 := legendreP_three_term (k + 1) (by omega)
      have h2 : ((2 * (k + 1) + 1 : ℕ) : ℝ) *
            ∫ t in (-1 : ℝ)..1, t * (legendreP k).eval t * (legendreP (k + 1)).eval t =
          ((k + 1 : ℕ) : ℝ) * ∫ t in (-1 : ℝ)..1, ((legendreP k).eval t) ^ 2 := by
        have hfn : ∀ t : ℝ, ((2 * (k + 1) + 1 : ℕ) : ℝ) *
              (t * (legendreP k).eval t * (legendreP (k + 1)).eval t) =
            ((k + 1 + 1 : ℕ) : ℝ) * ((legendreP (k + 1 + 1)).eval t * (legendreP k).eval t) +
              ((k + 1 : ℕ) : ℝ) * ((legendreP k).eval t) ^ 2 := by
          intro t
          have hv := congr_arg (fun p => p.eval t) hrec2
          simp only [eval_mul, eval_C, eval_sub, eval_X, Nat.add_sub_cancel] at hv
          have hv' : ((2 * (k + 1) + 1 : ℕ) : ℝ) * t * (legendreP (k + 1)).eval t =
              ((k + 1 + 1 : ℕ) : ℝ) * (legendreP (k + 1 + 1)).eval t +
                ((k + 1 : ℕ) : ℝ) * (legendreP k).eval t := by linarith
          calc
            ((2 * (k + 1) + 1 : ℕ) : ℝ) * (t * (legendreP k).eval t * (legendreP (k + 1)).eval t)
              = (((2 * (k + 1) + 1 : ℕ) : ℝ) * t * (legendreP (k + 1)).eval t) * (legendreP k).eval t := by ring
            _ = (((k + 1 + 1 : ℕ) : ℝ) * (legendreP (k + 1 + 1)).eval t +
                  ((k + 1 : ℕ) : ℝ) * (legendreP k).eval t) * (legendreP k).eval t := by rw [hv']
            _ = _ := by ring
        rw [← intervalIntegral.integral_const_mul]
        simp_rw [hfn]
        rw [intervalIntegral.integral_add
              (Continuous.intervalIntegrable (by fun_prop) _ _)
              (Continuous.intervalIntegrable (by fun_prop) _ _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            legendreP_orthog (by omega : k + 1 + 1 ≠ k)]
        ring
      rw [ih] at h2
      have hpos1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hpos2 : (0 : ℝ) < ((2 * (k + 1) + 1 : ℕ) : ℝ) := by positivity
      have hpos3 : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
      have hmul : ((k + 1 : ℕ) : ℝ) * ((2 * (k + 1) + 1 : ℕ) : ℝ) *
          ∫ t in (-1 : ℝ)..1, ((legendreP (k + 1)).eval t) ^ 2 =
          ((k + 1 : ℕ) : ℝ) * 2 := by
        calc
          ((k + 1 : ℕ) : ℝ) * ((2 * (k + 1) + 1 : ℕ) : ℝ) *
              ∫ t in (-1 : ℝ)..1, ((legendreP (k + 1)).eval t) ^ 2
            = ((2 * (k + 1) + 1 : ℕ) : ℝ) *
                (((k + 1 : ℕ) : ℝ) * ∫ t in (-1 : ℝ)..1, ((legendreP (k + 1)).eval t) ^ 2) := by ring
          _ = ((2 * k + 1 : ℕ) : ℝ) *
                (((2 * (k + 1) + 1 : ℕ) : ℝ) *
                  ∫ t in (-1 : ℝ)..1, t * (legendreP k).eval t * (legendreP (k + 1)).eval t) := by
              rw [h1]; ring
          _ = ((2 * k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (2 / ((2 * k + 1 : ℕ) : ℝ))) := by
              rw [h2]
          _ = ((k + 1 : ℕ) : ℝ) * 2 := by
              field_simp [ne_of_gt hpos3]
      have hcancel : ((2 * (k + 1) + 1 : ℕ) : ℝ) *
          ∫ t in (-1 : ℝ)..1, ((legendreP (k + 1)).eval t) ^ 2 = 2 := by
        nlinarith [hmul, hpos1]
      exact (eq_div_iff (ne_of_gt hpos2)).mpr (by linarith)

/-- Antiderivative identity: `(2k + 1) P_k = P_{k+1}' - P_{k-1}'` for `k ≥ 1`. -/
theorem legendreP_antideriv (k : ℕ) (hk : 1 ≤ k) :
    (legendreP (k + 1)).derivative - (legendreP (k - 1)).derivative =
      C ((2 * k + 1 : ℕ) : ℝ) * legendreP k := by
  set Q : Polynomial ℝ := (legendreP (k + 1)).derivative - (legendreP (k - 1)).derivative
  have h1deg : ((legendreP (k + 1)).derivative).natDegree = k := by
    apply le_antisymm
    · calc _ ≤ (legendreP (k + 1)).natDegree - 1 := natDegree_derivative_le _
        _ = k := by rw [legendreP_natDegree]; omega
    · apply le_natDegree_of_ne_zero
      rw [coeff_derivative]
      have htop : (legendreP (k + 1)).coeff (k + 1) = (legendreP (k + 1)).leadingCoeff := by
        rw [leadingCoeff, legendreP_natDegree]
      rw [htop]
      exact mul_ne_zero (ne_of_gt (legendreP_leadingCoeff_pos (k + 1))) (by positivity)
  have h2deg : ((legendreP (k - 1)).derivative).natDegree < k := by
    calc _ ≤ (legendreP (k - 1)).natDegree - 1 := natDegree_derivative_le _
      _ = (k - 1) - 1 := by rw [legendreP_natDegree]
      _ < k := by omega
  have hQdeg : Q.natDegree = k := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by omega : _ < _)]
    exact h1deg
  have hQlc : Q.leadingCoeff = ((2 * k + 1 : ℕ) : ℝ) * (legendreP k).leadingCoeff := by
    rw [leadingCoeff, hQdeg, coeff_sub, coeff_eq_zero_of_natDegree_lt h2deg, sub_zero,
        coeff_derivative]
    have htop : (legendreP (k + 1)).coeff (k + 1) = (legendreP (k + 1)).leadingCoeff := by
      rw [leadingCoeff, legendreP_natDegree]
    rw [htop, mul_comm]
    have hrat := legendreP_leadingCoeff_ratio k
    push_cast at hrat ⊢
    exact hrat
  have hQorth : ∀ q : Polynomial ℝ, q.natDegree < k →
      ∫ t in (-1 : ℝ)..1, Q.eval t * q.eval t = 0 := by
    intro q hq
    set F : Polynomial ℝ := legendreP (k + 1) - legendreP (k - 1)
    have hFd : F.derivative = Q := by simp [F, Q]
    have hF1 : F.eval 1 = 0 := by simp [F, legendreP_eval_one]
    have hFm1 : F.eval (-1) = 0 := by
      simp only [F, eval_sub, legendreP_eval_neg_one]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [add_comm 1 m, Nat.add_sub_cancel, show m + 1 + 1 = m + 2 by omega, pow_add]
      norm_num
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun t => q.eval t) (u' := fun t => q.derivative.eval t)
      (v := fun t => F.eval t) (v' := fun t => Q.eval t)
      (a := (-1 : ℝ)) (b := 1)
      (fun t _ => q.hasDerivAt t)
      (fun t _ => by rw [← hFd]; exact F.hasDerivAt t)
      (q.derivative.continuous.intervalIntegrable _ _)
      (Q.continuous.intervalIntegrable _ _)
    have hcomm : ∫ t in (-1 : ℝ)..1, Q.eval t * q.eval t =
        ∫ t in (-1 : ℝ)..1, q.eval t * Q.eval t := by
      refine intervalIntegral.integral_congr fun t _ => mul_comm _ _
    rw [hcomm, hibp, hF1, hFm1, mul_zero, mul_zero, sub_self, zero_sub]
    by_cases hqd0 : q.derivative = 0
    · simp [hqd0]
    · have hqpos : 1 ≤ q.natDegree := by
        by_contra h0
        push Not at h0
        have : q.natDegree = 0 := by omega
        rw [eq_C_of_natDegree_eq_zero this, derivative_C] at hqd0
        exact hqd0 rfl
      have hqd_lt1 : q.derivative.natDegree < k + 1 := by
        calc q.derivative.natDegree ≤ q.natDegree - 1 := natDegree_derivative_le _
          _ < k + 1 := by omega
      have hqd_lt2 : q.derivative.natDegree < k - 1 := by
        calc q.derivative.natDegree ≤ q.natDegree - 1 := natDegree_derivative_le _
          _ < k - 1 := by omega
      have hsplit : ∀ t : ℝ, q.derivative.eval t * F.eval t =
          (legendreP (k + 1)).eval t * q.derivative.eval t -
            (legendreP (k - 1)).eval t * q.derivative.eval t := by
        intro t; simp only [F, eval_sub]; ring
      simp_rw [hsplit]
      rw [intervalIntegral.integral_sub
            (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          legendreP_orthog_lt hqd_lt1, legendreP_orthog_lt hqd_lt2, sub_self, neg_zero]
  have heq := eq_smul_legendreP_of_orthog hQdeg hQorth
  rw [hQlc, mul_div_cancel_right₀ _ (ne_of_gt (legendreP_leadingCoeff_pos k))] at heq
  exact heq

/-- Derivative identity: `(1 - X^2) P_n' = n (P_{n-1} - X P_n)` for `n ≥ 1`. -/
theorem legendreP_deriv_identity (n : ℕ) (hn : 1 ≤ n) :
    (1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative =
      C (n : ℝ) * (legendreP (n - 1) - X * legendreP n) := by
  -- From 3-term recurrence: (2n+1)(P_{n-1} - X P_n) = (n+1)(P_{n-1} - P_{n+1})
  have hrec := legendreP_three_term n hn
  have hrhs : C ((2 * n + 1 : ℕ) : ℝ) * (C (n : ℝ) * (legendreP (n - 1) - X * legendreP n)) =
      C ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) * (legendreP (n - 1) - legendreP (n + 1)) := by
    have hX : C ((2 * n + 1 : ℕ) : ℝ) * X * legendreP n =
        C ((n + 1 : ℕ) : ℝ) * legendreP (n + 1) + C (n : ℝ) * legendreP (n - 1) := by
      have := hrec; linear_combination -this
    have hc : C ((2 * n + 1 : ℕ) : ℝ) - C (n : ℝ) = C ((n + 1 : ℕ) : ℝ) := by
      rw [← C_sub]; congr 1; push_cast; ring
    calc
      C ((2 * n + 1 : ℕ) : ℝ) * (C (n : ℝ) * (legendreP (n - 1) - X * legendreP n))
        = C (n : ℝ) * (C ((2 * n + 1 : ℕ) : ℝ) * legendreP (n - 1) -
            C ((2 * n + 1 : ℕ) : ℝ) * X * legendreP n) := by ring
      _ = C (n : ℝ) * (C ((2 * n + 1 : ℕ) : ℝ) * legendreP (n - 1) -
            (C ((n + 1 : ℕ) : ℝ) * legendreP (n + 1) + C (n : ℝ) * legendreP (n - 1))) := by
          rw [hX]
      _ = C (n : ℝ) * ((C ((2 * n + 1 : ℕ) : ℝ) - C (n : ℝ)) * legendreP (n - 1) -
            C ((n + 1 : ℕ) : ℝ) * legendreP (n + 1)) := by ring
      _ = C (n : ℝ) * (C ((n + 1 : ℕ) : ℝ) * legendreP (n - 1) -
            C ((n + 1 : ℕ) : ℝ) * legendreP (n + 1)) := by rw [hc]
      _ = C ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) * (legendreP (n - 1) - legendreP (n + 1)) := by
          rw [C_mul]; ring
  -- Differentiate both sides of D := (2n+1)*(1-X^2)*P_n' - n*(n+1)*(P_{n-1} - P_{n+1})
  set D : Polynomial ℝ :=
    C ((2 * n + 1 : ℕ) : ℝ) * ((1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative) -
      C ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) * (legendreP (n - 1) - legendreP (n + 1))
  have hDd : D.derivative = 0 := by
    have hode : ((1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative).derivative =
        -C ((n : ℝ) * ((n : ℝ) + 1)) * legendreP n := by
      have := eq_neg_of_add_eq_zero_left (legendreP_ode n)
      simpa [neg_mul] using this
    have hant := legendreP_antideriv n hn
    have hsub : (legendreP (n - 1) - legendreP (n + 1)).derivative =
        -C ((2 * n + 1 : ℕ) : ℝ) * legendreP n := by
      rw [derivative_sub]
      have : (legendreP (n - 1)).derivative - (legendreP (n + 1)).derivative =
          -((legendreP (n + 1)).derivative - (legendreP (n - 1)).derivative) := by ring
      rw [this, hant]; ring
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    dsimp only [D]
    rw [derivative_sub, derivative_C_mul, derivative_C_mul, hode, hsub, hcast]
    ring
  have hD_const : D = C (D.eval 1) := by
    have h0 := eq_C_of_derivative_eq_zero hDd
    rw [h0, eval_C]
  have hD1 : D.eval 1 = 0 := by
    simp [D, legendreP_eval_one]
  have hD0 : D = 0 := by rw [hD_const, hD1, C_0]
  have hmul : C ((2 * n + 1 : ℕ) : ℝ) * ((1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative) =
      C ((2 * n + 1 : ℕ) : ℝ) * (C (n : ℝ) * (legendreP (n - 1) - X * legendreP n)) := by
    rw [hrhs]
    exact sub_eq_zero.mp hD0
  have hCne : (C ((2 * n + 1 : ℕ) : ℝ) : Polynomial ℝ) ≠ 0 :=
    C_ne_zero.mpr (by positivity)
  exact mul_left_cancel₀ hCne hmul

/-- Christoffel-Darboux polynomial identity (in `X`, with parameter `y : ℝ`). -/
theorem christoffel_darboux_poly (n : ℕ) (hn : 1 ≤ n) (y : ℝ) :
    (X - C y) * ∑ k ∈ Finset.range n,
        C (((2 * k + 1 : ℕ) : ℝ) / 2 * (legendreP k).eval y) * legendreP k =
      C ((n : ℝ) / 2) *
        (C ((legendreP (n - 1)).eval y) * legendreP n -
          C ((legendreP n).eval y) * legendreP (n - 1)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_one]
    simp only [Nat.sub_self, legendreP_zero, legendreP_one, eval_one, eval_X]
    have h12 : (C (1 / 2 : ℝ) : Polynomial ℝ) = C ((1 : ℝ) / 2) := rfl
    simp only [Nat.mul_zero, zero_add, Nat.cast_one, mul_one, C_1, one_mul]
    ring
  | succ m hm ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    -- Use 3-term recurrence at m for both X and y:
    -- (2m+1)(X - y) P_m(X) P_m(y) = (m+1)(P_{m+1}(X)P_m(y) - P_m(X)P_{m+1}(y))
    --                              - m(P_m(X)P_{m-1}(y) - P_{m-1}(X)P_m(y))
    have hrecX := legendreP_three_term m hm
    have hrecy := congr_arg (fun p => p.eval y) hrecX
    simp only [eval_mul, eval_C, eval_sub, eval_X] at hrecy
    have hterm : (X - C y) * (C (((2 * m + 1 : ℕ) : ℝ) / 2 * (legendreP m).eval y) * legendreP m) =
        C (((m + 1 : ℕ) : ℝ) / 2) *
          (C ((legendreP m).eval y) * legendreP (m + 1) -
            C ((legendreP (m + 1)).eval y) * legendreP m) -
        C ((m : ℝ) / 2) *
          (C ((legendreP (m - 1)).eval y) * legendreP m -
            C ((legendreP m).eval y) * legendreP (m - 1)) := by
      have hhalf : ∀ a : ℝ, (C (a / 2) : Polynomial ℝ) = C (1 / 2 : ℝ) * C a := by
        intro a; rw [← C_mul]; congr 1; ring
      have hstep : C ((2 * m + 1 : ℕ) : ℝ) * (X - C y) * C ((legendreP m).eval y) * legendreP m =
          C ((m + 1 : ℕ) : ℝ) *
            (C ((legendreP m).eval y) * legendreP (m + 1) -
              C ((legendreP (m + 1)).eval y) * legendreP m) -
          C (m : ℝ) *
            (C ((legendreP (m - 1)).eval y) * legendreP m -
              C ((legendreP m).eval y) * legendreP (m - 1)) := by
        have hX' : C ((2 * m + 1 : ℕ) : ℝ) * X * legendreP m =
            C ((m + 1 : ℕ) : ℝ) * legendreP (m + 1) + C (m : ℝ) * legendreP (m - 1) := by
          linear_combination -hrecX
        have hy' : C (((2 * m + 1 : ℕ) : ℝ) * y * (legendreP m).eval y) =
            C (((m + 1 : ℕ) : ℝ) * (legendreP (m + 1)).eval y +
              (m : ℝ) * (legendreP (m - 1)).eval y) := by
          congr 1; linarith
        simp only [C_add, C_mul] at hy'
        calc
          C ((2 * m + 1 : ℕ) : ℝ) * (X - C y) * C ((legendreP m).eval y) * legendreP m
            = (C ((2 * m + 1 : ℕ) : ℝ) * X * legendreP m) * C ((legendreP m).eval y) -
                (C ((2 * m + 1 : ℕ) : ℝ) * C y * C ((legendreP m).eval y)) * legendreP m := by ring
          _ = (C ((m + 1 : ℕ) : ℝ) * legendreP (m + 1) + C (m : ℝ) * legendreP (m - 1)) *
                  C ((legendreP m).eval y) -
                (C ((m + 1 : ℕ) : ℝ) * C ((legendreP (m + 1)).eval y) +
                  C (m : ℝ) * C ((legendreP (m - 1)).eval y)) * legendreP m := by
              rw [hX', hy']
          _ = _ := by ring
      calc
        (X - C y) * (C (((2 * m + 1 : ℕ) : ℝ) / 2 * (legendreP m).eval y) * legendreP m)
          = C (1 / 2 : ℝ) *
              (C ((2 * m + 1 : ℕ) : ℝ) * (X - C y) * C ((legendreP m).eval y) * legendreP m) := by
              rw [C_mul, hhalf]; ring
        _ = C (1 / 2 : ℝ) *
              (C ((m + 1 : ℕ) : ℝ) *
                (C ((legendreP m).eval y) * legendreP (m + 1) -
                  C ((legendreP (m + 1)).eval y) * legendreP m) -
              C (m : ℝ) *
                (C ((legendreP (m - 1)).eval y) * legendreP m -
                  C ((legendreP m).eval y) * legendreP (m - 1))) := by rw [hstep]
        _ = _ := by rw [hhalf ((m + 1 : ℕ) : ℝ), hhalf (m : ℝ)]; ring
    rw [hterm, Nat.add_sub_cancel]
    ring

/-- Diagonal Christoffel-Darboux identity at any root `τ` of `P_n` (purely algebraic!):
`∑_{k=0}^{n-1} ((2k+1)/2) P_k(τ)^2 = (1/2) (1 - τ^2) P_n'(τ)^2`. -/
theorem christoffel_darboux_root (n : ℕ) (hn : 1 ≤ n) {τ : ℝ}
    (hτ : (legendreP n).eval τ = 0) :
    ∑ k ∈ Finset.range n, ((2 * k + 1 : ℕ) : ℝ) / 2 * ((legendreP k).eval τ) ^ 2 =
      (1 - τ ^ 2) * ((legendreP n).derivative.eval τ) ^ 2 / 2 := by
  have hdvd : (X - C τ) ∣ legendreP n := dvd_iff_isRoot.mpr hτ
  obtain ⟨Q, hQ⟩ := hdvd
  have hQeval : Q.eval τ = (legendreP n).derivative.eval τ := by
    have hd := congr_arg Polynomial.derivative hQ
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at hd
    have hev := congr_arg (fun p => p.eval τ) hd
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at hev
    exact hev.symm
  have hcd := christoffel_darboux_poly n hn τ
  rw [hτ, C_0, zero_mul, sub_zero, hQ] at hcd
  have hcd' : (X - C τ) * ∑ k ∈ Finset.range n,
      C (((2 * k + 1 : ℕ) : ℝ) / 2 * (legendreP k).eval τ) * legendreP k =
      (X - C τ) * (C ((n : ℝ) / 2) * C ((legendreP (n - 1)).eval τ) * Q) := by
    rw [hcd]; ring
  have hXne : (X - C τ : Polynomial ℝ) ≠ 0 := X_sub_C_ne_zero τ
  have hcancel := mul_left_cancel₀ hXne hcd'
  have hev := congr_arg (fun p => p.eval τ) hcancel
  rw [eval_finsetSum] at hev
  simp only [eval_mul, eval_C, hQeval] at hev
  have hlhs : ∑ k ∈ Finset.range n, ((2 * k + 1 : ℕ) : ℝ) / 2 * ((legendreP k).eval τ) ^ 2 =
      (n : ℝ) / 2 * (legendreP (n - 1)).eval τ * (legendreP n).derivative.eval τ := by
    have : ∑ k ∈ Finset.range n, ((2 * k + 1 : ℕ) : ℝ) / 2 * ((legendreP k).eval τ) ^ 2 =
        ∑ k ∈ Finset.range n, ((2 * k + 1 : ℕ) : ℝ) / 2 * (legendreP k).eval τ * (legendreP k).eval τ := by
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [this, hev]
  -- Now use legendreP_deriv_identity at τ: (1 - τ^2) P_n'(τ) = n P_{n-1}(τ)
  have hdi := congr_arg (fun p => p.eval τ) (legendreP_deriv_identity n hn)
  simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_C, hτ, mul_zero, sub_zero] at hdi
  rw [hlhs]
  have : (n : ℝ) * (legendreP (n - 1)).eval τ = (1 - τ ^ 2) * (legendreP n).derivative.eval τ := hdi.symm
  calc
    (n : ℝ) / 2 * (legendreP (n - 1)).eval τ * (legendreP n).derivative.eval τ
      = ((n : ℝ) * (legendreP (n - 1)).eval τ) * (legendreP n).derivative.eval τ / 2 := by ring
    _ = ((1 - τ ^ 2) * (legendreP n).derivative.eval τ) * (legendreP n).derivative.eval τ / 2 := by
        rw [this]
    _ = (1 - τ ^ 2) * ((legendreP n).derivative.eval τ) ^ 2 / 2 := by ring

end LegendreCore

section RootsQuadraturePart1

/-- A nonzero polynomial whose roots in `(-1, 1)` all have even multiplicity has constant sign
on `[-1, 1]`. -/
lemma poly_sign_const_of_even_roots (F : Polynomial ℝ) (hF : F ≠ 0)
    (heven : ∀ r ∈ Set.Ioo (-1 : ℝ) 1, Even (F.rootMultiplicity r)) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ F.eval t) ∨ (∀ t ∈ Set.Icc (-1 : ℝ) 1, F.eval t ≤ 0) := by
  induction hd : F.natDegree using Nat.strong_induction_on generalizing F with
  | h d ih =>
    by_cases hroot : ∃ r ∈ Set.Ioo (-1 : ℝ) 1, F.eval r = 0
    · obtain ⟨r, hrI, hr0⟩ := hroot
      have hmult_pos : 0 < F.rootMultiplicity r := (rootMultiplicity_pos hF).mpr hr0
      obtain ⟨k, hk⟩ := heven r hrI
      have hmult_ge2 : 2 ≤ F.rootMultiplicity r := by omega
      have hdvd : (X - C r) ^ 2 ∣ F :=
        dvd_trans (pow_dvd_pow (X - C r) hmult_ge2) (pow_rootMultiplicity_dvd F r)
      obtain ⟨G, hGeq⟩ := hdvd
      have hGne : G ≠ 0 := by intro h0; rw [h0, mul_zero] at hGeq; exact hF hGeq
      have hdeg_sq : ((X - C r) ^ 2).natDegree = 2 := by
        rw [natDegree_pow, natDegree_X_sub_C]
      have hGdeg : G.natDegree < d := by
        have hsum : F.natDegree = ((X - C r) ^ 2).natDegree + G.natDegree := by
          rw [hGeq, natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero r)) hGne]
        rw [hdeg_sq] at hsum
        omega
      have hGeven : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, Even (G.rootMultiplicity x) := by
        intro x hx
        have hadd := rootMultiplicity_mul (p := (X - C r) ^ 2) (q := G) (x := x)
          (by rw [← hGeq]; exact hF)
        rw [← hGeq] at hadd
        have hsq_mult : ((X - C r) ^ 2).rootMultiplicity x = if x = r then 2 else 0 := by
          rw [sq, rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero r) (X_sub_C_ne_zero r)),
              rootMultiplicity_X_sub_C]
          by_cases hxr : x = r
          · subst hxr; simp
          · simp [hxr]
        rw [hsq_mult] at hadd
        obtain ⟨m, hm⟩ := heven x hx
        by_cases hxr : x = r
        · rw [if_pos hxr] at hadd
          exact ⟨m - 1, by omega⟩
        · rw [if_neg hxr, zero_add] at hadd
          exact ⟨m, by omega⟩
      rcases ih G.natDegree hGdeg G hGne hGeven rfl with hpos | hneg
      · left
        intro t ht
        rw [hGeq, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
        exact mul_nonneg (sq_nonneg _) (hpos t ht)
      · right
        intro t ht
        rw [hGeq, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hneg t ht)
    · -- No root in (-1, 1): constant sign on (-1, 1) by IVT, then closure to [-1, 1]
      push Not at hroot
      have hconst : (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ F.eval t) ∨
          (∀ t ∈ Set.Ioo (-1 : ℝ) 1, F.eval t ≤ 0) := by
        by_contra hboth
        push Not at hboth
        obtain ⟨⟨a, haI, ha_neg⟩, ⟨b, hbI, hb_pos⟩⟩ := hboth
        rcases lt_or_gt_of_ne (show a ≠ b by intro h; subst h; linarith) with hab | hba
        · have h0mem : (0 : ℝ) ∈ Set.Icc (F.eval a) (F.eval b) := ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
          obtain ⟨c, hcI, hc0⟩ := intermediate_value_Icc (le_of_lt hab) F.continuous.continuousOn h0mem
          exact hroot c ⟨lt_of_lt_of_le haI.1 hcI.1, lt_of_le_of_lt hcI.2 hbI.2⟩ hc0
        · have h0mem : (0 : ℝ) ∈ Set.Icc (F.eval a) (F.eval b) := ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
          obtain ⟨c, hcI, hc0⟩ := intermediate_value_Icc' (le_of_lt hba) F.continuous.continuousOn h0mem
          exact hroot c ⟨lt_of_lt_of_le hbI.1 hcI.1, lt_of_le_of_lt hcI.2 haI.2⟩ hc0
      rcases hconst with hpos | hneg
      · left
        intro t ht
        have hcl : t ∈ closure (Set.Ioo (-1 : ℝ) 1) := by
          rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]; exact ht
        exact closure_minimal hpos (isClosed_le continuous_const F.continuous) hcl
      · right
        intro t ht
        have hcl : t ∈ closure (Set.Ioo (-1 : ℝ) 1) := by
          rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]; exact ht
        exact closure_minimal hneg (isClosed_le F.continuous continuous_const) hcl

/-- A continuous nonnegative function on `[-1, 1]` that is strictly positive at some point of
`(-1, 1)` has strictly positive integral on `[-1, 1]`. -/
lemma integral_pos_of_nonneg_of_pos_at {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (-1 : ℝ) 1) (hpos : 0 < f t₀) :
    0 < ∫ t in (-1 : ℝ)..1, f t := by
  have hge : 0 ≤ ∫ t in (-1 : ℝ)..1, f t :=
    intervalIntegral.integral_nonneg (by norm_num) hnn
  refine lt_of_le_of_ne hge fun h0 => ?_
  have hint0 : ∫ t in (-1 : ℝ)..1, f t = 0 := h0.symm
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hint0
  have hae : f =ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun t ht => hnn t ⟨le_of_lt ht.1, ht.2⟩))
      (hf.integrableOn_Ioc)).mp hint0
  have hopen : IsOpen {x : ℝ | 0 < f x} := isOpen_lt continuous_const hf
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t₀ hpos
  set δ := min ε (min (t₀ + 1) (1 - t₀))
  have hδ : 0 < δ := by
    simp only [δ, lt_min_iff]; exact ⟨hε, by linarith [ht₀.1], by linarith [ht₀.2]⟩
  have hsub : Set.Ioo (t₀ - δ) (t₀ + δ) ⊆ Set.Ioc (-1 : ℝ) 1 := fun x hx =>
    ⟨by linarith [hx.1, min_le_right ε (min (t₀ + 1) (1 - t₀)), min_le_left (t₀ + 1) (1 - t₀)],
     by linarith [hx.2, min_le_right ε (min (t₀ + 1) (1 - t₀)), min_le_right (t₀ + 1) (1 - t₀)]⟩
  have hpos_on : ∀ x ∈ Set.Ioo (t₀ - δ) (t₀ + δ), 0 < f x := fun x hx =>
    hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1, min_le_left ε (min (t₀ + 1) (1 - t₀))],
             by linarith [hx.2, min_le_left ε (min (t₀ + 1) (1 - t₀))]⟩)
  have hmeas_pos : 0 < volume (Set.Ioo (t₀ - δ) (t₀ + δ)) := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
  have hzero_ae' : volume {x : ℝ | ¬ (x ∈ Set.Ioc (-1 : ℝ) 1 → f x = 0)} = 0 :=
    (ae_restrict_iff' measurableSet_Ioc).mp hae
  have hsub2 : Set.Ioo (t₀ - δ) (t₀ + δ) ⊆ {x : ℝ | ¬ (x ∈ Set.Ioc (-1 : ℝ) 1 → f x = 0)} :=
    fun x hx hfx => ne_of_gt (hpos_on x hx) (hfx (hsub hx))
  exact ne_of_gt hmeas_pos (measure_mono_null hsub2 hzero_ae')

/-- Multiplicity of `x` in `∏ r ∈ S, (X - C r)`. -/
lemma rootMultiplicity_prod_X_sub_C (S : Finset ℝ) (x : ℝ) :
    (∏ r ∈ S, (X - C r)).rootMultiplicity x = if x ∈ S then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [rootMultiplicity_eq_zero_iff]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hpne : (X - C a) * ∏ r ∈ s, (X - C r) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero a) (Finset.prod_ne_zero_iff.mpr fun r _ => X_sub_C_ne_zero r)
    rw [rootMultiplicity_mul hpne, rootMultiplicity_X_sub_C, ih]
    by_cases hxa : x = a
    · subst hxa
      simp [ha]
    · simp [hxa]

/-- Any nonzero degree-`d` polynomial orthogonal on `[-1, 1]` to all polynomials of degree `< d`
with respect to a positive continuous weight `w` has `d` distinct simple roots in `(-1, 1)`
(and no other roots anywhere in `ℝ`). -/
theorem roots_of_orthog_weight {d : ℕ} {P : Polynomial ℝ} {w : ℝ → ℝ}
    (hw_cont : Continuous w)
    (hw_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < w t)
    (hw_nn : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ w t)
    (hPne : P ≠ 0)
    (hdeg : P.natDegree = d)
    (horth : ∀ q : Polynomial ℝ, q.natDegree < d →
      ∫ t in (-1 : ℝ)..1, w t * P.eval t * q.eval t = 0) :
    ∃ τ : Fin d → ℝ, StrictMono τ ∧
      (∀ i, -1 < τ i ∧ τ i < 1) ∧
      (∀ i, P.eval (τ i) = 0) ∧
      (∀ x : ℝ, P.eval x = 0 → ∃ i, τ i = x) ∧
      (∀ i, P.derivative.eval (τ i) ≠ 0) := by
  by_cases hd0 : d = 0
  · subst hd0
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    intro x hx
    have hPeq : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
    have hc0 : P.coeff 0 = 0 := by rw [hPeq, eval_C] at hx; exact hx
    exact absurd (by rw [hPeq, hc0, C_0]) hPne
  · let S : Finset ℝ :=
      P.roots.toFinset.filter fun r => -1 < r ∧ r < 1 ∧ Odd (P.rootMultiplicity r)
    have hScard_le : S.card ≤ d := by
      calc S.card ≤ P.roots.toFinset.card := Finset.card_filter_le _ _
        _ ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := card_roots' P
        _ = d := hdeg
    have hScard_ge : d ≤ S.card := by
      by_contra hlt
      push Not at hlt
      let q : Polynomial ℝ := ∏ r ∈ S, (X - C r)
      have hqne : q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r _ => X_sub_C_ne_zero r
      have hqdeg : q.natDegree = S.card := by
        rw [natDegree_prod _ _ fun r _ => X_sub_C_ne_zero r]
        simp
      have hint0 : ∫ t in (-1 : ℝ)..1, w t * P.eval t * q.eval t = 0 :=
        horth q (by omega)
      have hPqne : P * q ≠ 0 := mul_ne_zero hPne hqne
      have heven : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, Even ((P * q).rootMultiplicity x) := by
        intro x hx
        rw [rootMultiplicity_mul hPqne, rootMultiplicity_prod_X_sub_C]
        by_cases hxS : x ∈ S
        · rw [if_pos hxS]
          have hodd : Odd (P.rootMultiplicity x) := (Finset.mem_filter.mp hxS).2.2.2
          obtain ⟨k, hk⟩ := hodd
          exact ⟨k + 1, by omega⟩
        · rw [if_neg hxS, add_zero]
          by_contra hnot_even
          rw [Nat.not_even_iff_odd] at hnot_even
          have hmult_pos : 0 < P.rootMultiplicity x := by
            obtain ⟨k, hk⟩ := hnot_even; omega
          have hxroot : P.eval x = 0 := (rootMultiplicity_pos hPne).mp hmult_pos
          have hxmem : x ∈ S := Finset.mem_filter.mpr
            ⟨Multiset.mem_toFinset.mpr ((mem_roots hPne).mpr hxroot), hx.1, hx.2, hnot_even⟩
          exact hxS hxmem
      have hfin : ((P * q).roots.toFinset : Set ℝ).Finite := Finset.finite_toSet _
      have hinf : (Set.Ioo (-1 : ℝ) 1).Infinite := Set.Ioo_infinite (by norm_num)
      obtain ⟨t₀, ht₀I, ht₀Not⟩ := (hinf.sdiff hfin).nonempty
      have ht₀ne : (P * q).eval t₀ ≠ 0 := fun h0 =>
        ht₀Not (Multiset.mem_toFinset.mpr ((mem_roots hPqne).mpr h0))
      rcases poly_sign_const_of_even_roots (P * q) hPqne heven with hpos | hneg
      · have hgt : 0 < ∫ t in (-1 : ℝ)..1, w t * (P * q).eval t := by
          refine integral_pos_of_nonneg_of_pos_at
            (hw_cont.mul (P * q).continuous)
            (fun t ht => mul_nonneg (hw_nn t ht) (hpos t ht))
            ht₀I
            (mul_pos (hw_pos t₀ ht₀I)
              (lt_of_le_of_ne (hpos t₀ ⟨le_of_lt ht₀I.1, le_of_lt ht₀I.2⟩) (Ne.symm ht₀ne)))
        have heq : ∫ t in (-1 : ℝ)..1, w t * (P * q).eval t =
            ∫ t in (-1 : ℝ)..1, w t * P.eval t * q.eval t := by
          refine intervalIntegral.integral_congr fun t _ => ?_; simp [eval_mul]; ring
        linarith
      · have hgt : 0 < ∫ t in (-1 : ℝ)..1, w t * (-(P * q).eval t) := by
          refine integral_pos_of_nonneg_of_pos_at
            (hw_cont.mul (P * q).continuous.neg)
            (fun t ht => mul_nonneg (hw_nn t ht) (neg_nonneg.mpr (hneg t ht)))
            ht₀I
            (mul_pos (hw_pos t₀ ht₀I)
              (neg_pos.mpr (lt_of_le_of_ne (hneg t₀ ⟨le_of_lt ht₀I.1, le_of_lt ht₀I.2⟩) ht₀ne)))
        have heq : ∫ t in (-1 : ℝ)..1, w t * (-(P * q).eval t) =
            -(∫ t in (-1 : ℝ)..1, w t * P.eval t * q.eval t) := by
          rw [← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_congr fun t _ => ?_; simp [eval_mul]; ring
        linarith
    have hScard : S.card = d := le_antisymm hScard_le hScard_ge
    let e := S.orderEmbOfFin hScard
    refine ⟨e, e.strictMono, ?_, ?_, ?_, ?_⟩
    · intro i
      have hi := Finset.mem_filter.mp (S.orderEmbOfFin_mem hScard i)
      exact ⟨hi.2.1, hi.2.2.1⟩
    · intro i
      have hi := Finset.mem_filter.mp (S.orderEmbOfFin_mem hScard i)
      exact (mem_roots hPne).mp (Multiset.mem_toFinset.mp hi.1)
    · intro x hx
      have hxroot : x ∈ P.roots := (mem_roots hPne).mpr hx
      have hsub_eq : S = P.roots.toFinset := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
          _ ≤ P.natDegree := card_roots' P
          _ = d := hdeg
          _ = S.card := hScard.symm
      have hxS : x ∈ (S : Set ℝ) := by
        rw [Finset.mem_coe, hsub_eq]
        exact Multiset.mem_toFinset.mpr hxroot
      rw [← Finset.range_orderEmbOfFin S hScard] at hxS
      exact hxS
    · intro i
      have hcard_roots : P.roots.card = d := by
        apply le_antisymm (hdeg ▸ card_roots' P)
        calc d = S.card := hScard.symm
          _ ≤ P.roots.toFinset.card := Finset.card_filter_le _ _
          _ ≤ P.roots.card := Multiset.toFinset_card_le _
      have hnodup : P.roots.Nodup := by
        rw [← Multiset.toFinset_card_eq_card_iff_nodup]
        apply le_antisymm (Multiset.toFinset_card_le _)
        calc P.roots.card = d := hcard_roots
          _ = S.card := hScard.symm
          _ ≤ P.roots.toFinset.card := Finset.card_filter_le _ _
      have hi := Finset.mem_filter.mp (S.orderEmbOfFin_mem hScard i)
      have hmem : e i ∈ P.roots := Multiset.mem_toFinset.mp hi.1
      have hcnt : P.roots.count (e i) = 1 := Multiset.count_eq_one_of_mem hnodup hmem
      have hmult1 : P.rootMultiplicity (e i) = 1 := by
        rw [← count_roots P, hcnt]
      intro hd0'
      have hge2 : 2 ≤ P.rootMultiplicity (e i) := by
        have hroot_i : P.eval (e i) = 0 := (mem_roots hPne).mp hmem
        have hdvd1 : (X - C (e i)) ∣ P := dvd_iff_isRoot.mpr hroot_i
        obtain ⟨Q, hQ⟩ := hdvd1
        have hQ0 : Q.eval (e i) = 0 := by
          have hd := congr_arg Polynomial.derivative hQ
          rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at hd
          have hev := congr_arg (fun p => p.eval (e i)) hd
          simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at hev
          rw [hd0'] at hev
          exact hev.symm
        have hdvd2 : (X - C (e i)) ∣ Q := dvd_iff_isRoot.mpr hQ0
        obtain ⟨Q2, hQ2⟩ := hdvd2
        have hdvd_sq : (X - C (e i)) ^ 2 ∣ P := ⟨Q2, by rw [hQ, hQ2]; ring⟩
        exact (le_rootMultiplicity_iff hPne).mpr hdvd_sq
      omega

/-- Two strictly increasing `Fin n → ℝ` enumerations with the same image are equal. -/
lemma strictMono_eq_of_range_eq {n : ℕ} {τ₁ τ₂ : Fin n → ℝ}
    (h1 : StrictMono τ₁) (h2 : StrictMono τ₂)
    (hrange : Set.range τ₁ = Set.range τ₂) : τ₁ = τ₂ := by
  -- Use Finset.orderEmbOfFin uniqueness via OrderIso / induction on i
  have hmem1 : ∀ i, ∃ j, τ₂ j = τ₁ i := fun i => by
    have : τ₁ i ∈ Set.range τ₂ := hrange ▸ Set.mem_range_self i
    exact this
  have hmem2 : ∀ j, ∃ i, τ₁ i = τ₂ j := fun j => by
    have : τ₂ j ∈ Set.range τ₁ := hrange.symm ▸ Set.mem_range_self j
    exact this
  -- Build an order isomorphism Fin n ≃o Fin n? Even simpler: strong induction on i.val!
  suffices h : ∀ k (hk : k < n), τ₁ ⟨k, hk⟩ = τ₂ ⟨k, hk⟩ by
    funext i; exact h i.val i.isLt
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- τ₁ k < τ₂ k; pick j with τ₂ j = τ₁ k. Since τ₂ j < τ₂ k, j < k.
      obtain ⟨j, hj⟩ := hmem1 ⟨k, hk⟩
      have hjk : j.val < k := by
        have : j < ⟨k, hk⟩ := h2.lt_iff_lt.mp (by rw [hj]; exact hlt)
        exact this
      have heq := ih j.val hjk j.isLt
      have hlt1 : τ₁ j < τ₁ ⟨k, hk⟩ := h1 hjk
      linarith
    · obtain ⟨i, hi⟩ := hmem2 ⟨k, hk⟩
      have hik : i.val < k := by
        have : i < ⟨k, hk⟩ := h1.lt_iff_lt.mp (by rw [hi]; exact hgt)
        exact this
      have heq := ih i.val hik i.isLt
      have hlt2 : τ₂ i < τ₂ ⟨k, hk⟩ := h2 hik
      linarith

/-- Any `StrictMono` enumeration of `n` roots of a degree-`n` polynomial `P` whose roots all lie
in `Set.range τ₀` (also `StrictMono`) must equal `τ₀`. -/
lemma roots_enum_unique {n : ℕ} {P : Polynomial ℝ} {τ τ₀ : Fin n → ℝ}
    (h1 : StrictMono τ) (h2 : StrictMono τ₀)
    (hτ : ∀ i, P.eval (τ i) = 0)
    (hsub : ∀ x, P.eval x = 0 → ∃ i, τ₀ i = x) : τ = τ₀ := by
  have hcard : (Finset.image τ Finset.univ).card = (Finset.image τ₀ Finset.univ).card := by
    rw [Finset.card_image_of_injective _ h1.injective, Finset.card_image_of_injective _ h2.injective]
  have hsub_fin : Finset.image τ Finset.univ ⊆ Finset.image τ₀ Finset.univ := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj⟩ := hsub (τ i) (hτ i)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
  have heq_fin : Finset.image τ Finset.univ = Finset.image τ₀ Finset.univ :=
    Finset.eq_of_subset_of_card_le hsub_fin (le_of_eq hcard.symm)
  have hrange : Set.range τ = Set.range τ₀ := by
    ext x
    simp only [Set.mem_range]
    have := Finset.ext_iff.mp heq_fin x
    simpa [Finset.mem_image] using this
  exact strictMono_eq_of_range_eq h1 h2 hrange

/-- Lagrange basis polynomial `ℓ_j` associated with injective nodes `τ : Fin n → ℝ`. -/
noncomputable def lagBasis {n : ℕ} (τ : Fin n → ℝ) (j : Fin n) : Polynomial ℝ :=
  Lagrange.basis Finset.univ τ j

lemma lagBasis_eval_self {n : ℕ} {τ : Fin n → ℝ} (hτ : Function.Injective τ) (j : Fin n) :
    (lagBasis τ j).eval (τ j) = 1 :=
  Lagrange.eval_basis_self (Set.injOn_of_injective hτ) (Finset.mem_univ j)

lemma lagBasis_eval_of_ne {n : ℕ} {τ : Fin n → ℝ} {i j : Fin n} (hij : i ≠ j) :
    (lagBasis τ j).eval (τ i) = 0 :=
  Lagrange.eval_basis_of_ne hij.symm (Finset.mem_univ i)

lemma lagBasis_natDegree_le {n : ℕ} (_hn : 1 ≤ n) {τ : Fin n → ℝ} (hτ : Function.Injective τ)
    (j : Fin n) : (lagBasis τ j).natDegree ≤ n - 1 := by
  have hdeg := Lagrange.degree_basis (Set.injOn_of_injective hτ) (Finset.mem_univ j)
  have hcard : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
  rw [hcard] at hdeg
  exact le_of_eq (Polynomial.natDegree_eq_of_degree_eq_some hdeg)

lemma lagBasis_ne_zero {n : ℕ} {τ : Fin n → ℝ} (hτ : Function.Injective τ) (j : Fin n) :
    lagBasis τ j ≠ 0 := by
  intro h0
  have h1 := lagBasis_eval_self hτ j
  rw [h0, eval_zero] at h1
  norm_num at h1

lemma poly_eq_lagrange_sum {n : ℕ} {τ : Fin n → ℝ} (hτ : Function.Injective τ)
    {q : Polynomial ℝ} (hq : q.natDegree < n) :
    q = ∑ j : Fin n, C (q.eval (τ j)) * lagBasis τ j := by
  have hdeg : q.degree < ((Finset.univ : Finset (Fin n)).card : WithBot ℕ) := by
    rw [Finset.card_fin]
    by_cases hq0 : q = 0
    · rw [hq0, degree_zero]; exact WithBot.bot_lt_coe n
    · rw [degree_eq_natDegree hq0]; exact_mod_cast hq
  have hint := Lagrange.eq_interpolate (s := (Finset.univ : Finset (Fin n))) (v := τ)
    (Set.injOn_of_injective hτ) hdeg
  conv_lhs => rw [hint]
  rw [Lagrange.interpolate_apply]
  rfl

lemma sum_lagBasis_eq_one {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ} (hτ : Function.Injective τ) :
    ∑ j : Fin n, lagBasis τ j = 1 := by
  have h1 := poly_eq_lagrange_sum hτ (q := (1 : Polynomial ℝ)) (by simp; omega)
  simpa using h1.symm

/-- Interpolatory quadrature weight `w_j = ∫_{-1}^1 ℓ_j(t) dt`. -/
noncomputable def quadWeight {n : ℕ} (τ : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∫ t in (-1 : ℝ)..1, (lagBasis τ j).eval t

/-- Integration matrix entry `A_{ij} = ∫_{-1}^{τ_i} ℓ_j(t) dt`. -/
noncomputable def intMatA {n : ℕ} (τ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∫ t in (-1 : ℝ)..(τ i), (lagBasis τ j).eval t

/-- Tail integration matrix entry `B_{ij} = ∫_{τ_i}^1 ℓ_j(t) dt`. -/
noncomputable def intMatB {n : ℕ} (τ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∫ t in (τ i)..1, (lagBasis τ j).eval t

lemma intMatA_add_intMatB {n : ℕ} (τ : Fin n → ℝ) (i j : Fin n) :
    intMatA τ i j + intMatB τ i j = quadWeight τ j := by
  exact intervalIntegral.integral_add_adjacent_intervals
    ((lagBasis τ j).continuous.intervalIntegrable _ _)
    ((lagBasis τ j).continuous.intervalIntegrable _ _)

lemma sum_intMatA {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ} (hτ : Function.Injective τ) (i : Fin n) :
    ∑ j : Fin n, intMatA τ i j = 1 + τ i := by
  unfold intMatA
  rw [← intervalIntegral.integral_finsetSum (fun j _ => (lagBasis τ j).continuous.intervalIntegrable _ _)]
  have h1 : ∀ t : ℝ, ∑ j : Fin n, (lagBasis τ j).eval t = 1 := fun t => by
    rw [← eval_finsetSum, sum_lagBasis_eq_one hn hτ, eval_one]
  simp_rw [h1]
  simp
  ring

/-- Polynomial representation via integration matrix: if `p.natDegree ≤ n` and `p(-1) = 0`, then
`p(τ_i) = ∑_j A_{ij} p'(τ_j)`. -/
lemma poly_eval_eq_sum_intMatA {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ} (hτ : Function.Injective τ)
    {p : Polynomial ℝ} (hpdeg : p.natDegree ≤ n) (hp_m1 : p.eval (-1) = 0) (i : Fin n) :
    p.eval (τ i) = ∑ j : Fin n, intMatA τ i j * p.derivative.eval (τ j) := by
  have hddeg : p.derivative.natDegree < n := by
    by_cases hp0 : p.natDegree = 0
    · have : p.derivative = 0 := by rw [eq_C_of_natDegree_eq_zero hp0, derivative_C]
      rw [this, natDegree_zero]; omega
    · calc p.derivative.natDegree ≤ p.natDegree - 1 := natDegree_derivative_le _
        _ < n := by omega
  have hlag := poly_eq_lagrange_sum hτ hddeg
  have hftc : ∫ t in (-1 : ℝ)..(τ i), p.derivative.eval t = p.eval (τ i) - p.eval (-1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => p.hasDerivAt t)
      (p.derivative.continuous.intervalIntegrable _ _)
  rw [hp_m1, sub_zero] at hftc
  rw [← hftc]
  have hfn : ∀ t : ℝ, p.derivative.eval t =
      ∑ j : Fin n, p.derivative.eval (τ j) * (lagBasis τ j).eval t := by
    intro t
    conv_lhs => rw [hlag]
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => by simp only [eval_mul, eval_C]
  rw [intervalIntegral.integral_congr (fun t _ => hfn t)]
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
        Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, mul_comm]
  rfl

lemma poly_abs_bound_of_sum_abs_intMatA {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ}
    (hτ : Function.Injective τ) {p : Polynomial ℝ} (hpdeg : p.natDegree ≤ n)
    (hp_m1 : p.eval (-1) = 0) (hderiv : ∀ j : Fin n, |p.derivative.eval (τ j)| ≤ 1) (i : Fin n) :
    |p.eval (τ i)| ≤ ∑ j : Fin n, |intMatA τ i j| := by
  rw [poly_eval_eq_sum_intMatA hn hτ hpdeg hp_m1 i]
  calc
    |∑ j : Fin n, intMatA τ i j * p.derivative.eval (τ j)|
      ≤ ∑ j : Fin n, |intMatA τ i j * p.derivative.eval (τ j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |intMatA τ i j| * |p.derivative.eval (τ j)| := by
        refine Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ j : Fin n, |intMatA τ i j| * 1 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hderiv j) (abs_nonneg _)
    _ = ∑ j : Fin n, |intMatA τ i j| := by simp

/-- Exactness of interpolatory quadrature on polynomials of degree `< n + m` when the nodal
polynomial `R` of degree `n` is orthogonal to all polynomials of degree `< m`. -/
theorem quad_exact_of_orthog {n m : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ} (hτ : Function.Injective τ)
    {R : Polynomial ℝ} (hRdeg : R.natDegree = n) (hRroots : ∀ j : Fin n, R.eval (τ j) = 0)
    (hRorth : ∀ q : Polynomial ℝ, q.natDegree < m → ∫ t in (-1 : ℝ)..1, R.eval t * q.eval t = 0)
    {f : Polynomial ℝ} (hf : f.natDegree < n + m) :
    ∫ t in (-1 : ℝ)..1, f.eval t = ∑ j : Fin n, quadWeight τ j * f.eval (τ j) := by
  have hRne : R ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hRdeg; omega
  set q := f / R
  set r := f % R
  have hdiv : R * q + r = f := EuclideanDomain.div_add_mod f R
  have hr_deg : r.natDegree < n := by
    by_cases hr0 : r = 0
    · rw [hr0, natDegree_zero]; omega
    · have hlt := Polynomial.degree_mod_lt f hRne
      rw [degree_eq_natDegree hr0, degree_eq_natDegree hRne, hRdeg] at hlt
      exact_mod_cast hlt
  have hint_Rq : ∫ t in (-1 : ℝ)..1, (R * q).eval t = 0 := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · have hq_deg : q.natDegree < m := by
        have hRq_deg : (R * q).natDegree = n + q.natDegree := by
          rw [natDegree_mul hRne hq0, hRdeg]
        have hf_eq : (R * q + r).natDegree = n + q.natDegree := by
          rw [natDegree_add_eq_left_of_natDegree_lt (by omega : r.natDegree < (R * q).natDegree)]
          exact hRq_deg
        rw [hdiv] at hf_eq
        omega
      have hfn : ∀ t : ℝ, (R * q).eval t = R.eval t * q.eval t := fun t => eval_mul
      simp_rw [hfn]
      exact hRorth q hq_deg
  have hr_eval : ∀ j : Fin n, r.eval (τ j) = f.eval (τ j) := fun j => by
    have := congr_arg (fun p => p.eval (τ j)) hdiv
    simp only [eval_add, eval_mul, hRroots j, zero_mul, zero_add] at this
    exact this
  have hr_lag := poly_eq_lagrange_sum hτ hr_deg
  have hint_r : ∫ t in (-1 : ℝ)..1, r.eval t = ∑ j : Fin n, quadWeight τ j * f.eval (τ j) := by
    have hfn : ∀ t : ℝ, r.eval t = ∑ j : Fin n, f.eval (τ j) * (lagBasis τ j).eval t := by
      intro t
      conv_lhs => rw [hr_lag]
      rw [eval_finsetSum]
      refine Finset.sum_congr rfl fun j _ => by simp [eval_mul, eval_C, hr_eval j]
    simp_rw [hfn]
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
          Continuous.intervalIntegrable (by fun_prop) _ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul, mul_comm]; rfl
  have hf_int : ∫ t in (-1 : ℝ)..1, f.eval t =
      (∫ t in (-1 : ℝ)..1, (R * q).eval t) + ∫ t in (-1 : ℝ)..1, r.eval t := by
    rw [← intervalIntegral.integral_add
          ((R * q).continuous.intervalIntegrable _ _) (r.continuous.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [← eval_add, hdiv]
  rw [hf_int, hint_Rq, zero_add, hint_r]

/-- Positive quadrature weights whenever quadrature is exact on degree `≤ 2(n - 1)`. -/
lemma quadWeight_eq_integral_sq {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ} (hτ : Function.Injective τ)
    (hexact : ∀ f : Polynomial ℝ, f.natDegree ≤ 2 * (n - 1) →
      ∫ t in (-1 : ℝ)..1, f.eval t = ∑ j : Fin n, quadWeight τ j * f.eval (τ j))
    (j : Fin n) :
    quadWeight τ j = ∫ t in (-1 : ℝ)..1, ((lagBasis τ j).eval t) ^ 2 := by
  have hdeg : ((lagBasis τ j) ^ 2).natDegree ≤ 2 * (n - 1) := by
    calc ((lagBasis τ j) ^ 2).natDegree ≤ 2 * (lagBasis τ j).natDegree := natDegree_pow_le
      _ ≤ 2 * (n - 1) := Nat.mul_le_mul_left 2 (lagBasis_natDegree_le hn hτ j)
  have h := hexact ((lagBasis τ j) ^ 2) hdeg
  have heval : ∀ k : Fin n, ((lagBasis τ j) ^ 2).eval (τ k) = if k = j then 1 else 0 := by
    intro k
    rw [eval_pow]
    by_cases hkj : k = j
    · subst hkj; rw [if_pos rfl, lagBasis_eval_self hτ k, one_pow]
    · rw [if_neg hkj, lagBasis_eval_of_ne hkj, zero_pow (by norm_num)]
  simp_rw [heval] at h
  rw [Finset.sum_eq_single j] at h
  · simp only [eval_pow] at h
    simpa using h.symm
  · intro k _ hkj; simp [hkj]
  · intro hnot; exact absurd (Finset.mem_univ j) hnot

lemma quadWeight_pos {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ} (hτ : Function.Injective τ)
    (hexact : ∀ f : Polynomial ℝ, f.natDegree ≤ 2 * (n - 1) →
      ∫ t in (-1 : ℝ)..1, f.eval t = ∑ j : Fin n, quadWeight τ j * f.eval (τ j))
    (j : Fin n) : 0 < quadWeight τ j := by
  rw [quadWeight_eq_integral_sq hn hτ hexact j]
  have hnn : 0 ≤ ∫ t in (-1 : ℝ)..1, ((lagBasis τ j).eval t) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  refine lt_of_le_of_ne hnn fun h0 => ?_
  exact lagBasis_ne_zero hτ j (poly_eq_zero_of_integral_sq_eq_zero h0.symm)

/-- **Part 1 (Unified Quadrature Bound):** For ANY `n`-point quadrature rule `(τ, w)` on `[-1, 1]`
exact on polynomials of degree `≤ 2(n - 1)` (covering BOTH Gauss-Legendre and Gauss-Radau!),
every row `i` with `τ i ∈ [-1, 1]` satisfies `∑_j |A_{ij}| ≤ (3 + τ i) / 2`. -/
theorem sum_abs_intMatA_le_three_add_div_two {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ}
    (hτ : Function.Injective τ)
    (hexact : ∀ f : Polynomial ℝ, f.natDegree ≤ 2 * (n - 1) →
      ∫ t in (-1 : ℝ)..1, f.eval t = ∑ j : Fin n, quadWeight τ j * f.eval (τ j))
    {i : Fin n} (hτi : τ i ∈ Set.Icc (-1 : ℝ) 1) :
    ∑ j : Fin n, |intMatA τ i j| ≤ (3 + τ i) / 2 := by
  -- Define K̃_i, the degree-(n-1) L²([-1,1]) projection of 1_{[τ_i, 1]}:
  let c : ℕ → ℝ := fun k => ((2 * k + 1 : ℕ) : ℝ) / 2 * ∫ s in (τ i)..1, (legendreP k).eval s
  let K : Polynomial ℝ := ∑ k ∈ Finset.range n, C (c k) * legendreP k
  have hKdeg : K.natDegree ≤ n - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    have hkn : k < n := Finset.mem_range.mp hk
    calc (C (c k) * legendreP k).natDegree
        ≤ (C (c k)).natDegree + (legendreP k).natDegree := natDegree_mul_le
      _ = k := by rw [natDegree_C, zero_add, legendreP_natDegree]
      _ ≤ n - 1 := by omega
  -- Step 1: Projection property: for every q of degree ≤ n - 1, ∫_{-1}^1 K * q = ∫_{τ_i}^1 q
  have hproj_leg : ∀ m < n,
      ∫ t in (-1 : ℝ)..1, K.eval t * (legendreP m).eval t = ∫ s in (τ i)..1, (legendreP m).eval s := by
    intro m hm
    have hfn : ∀ t : ℝ, K.eval t * (legendreP m).eval t =
        ∑ k ∈ Finset.range n, c k * ((legendreP k).eval t * (legendreP m).eval t) := by
      intro t
      simp only [K, eval_finsetSum, eval_mul, eval_C, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hfn]
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
          Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [Finset.sum_eq_single m]
    · rw [intervalIntegral.integral_const_mul]
      have hsq : ∫ t in (-1 : ℝ)..1, (legendreP m).eval t * (legendreP m).eval t =
          2 / ((2 * m + 1 : ℕ) : ℝ) := by
        have := legendreP_integral_sq m
        rw [← this]
        exact intervalIntegral.integral_congr fun t _ => (sq _).symm
      rw [hsq]
      dsimp only [c]
      have hpos : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hpos]
    · intro k _ hkm
      rw [intervalIntegral.integral_const_mul, legendreP_orthog hkm, mul_zero]
    · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
  have hproj : ∀ q : Polynomial ℝ, q.natDegree ≤ n - 1 →
      ∫ t in (-1 : ℝ)..1, K.eval t * q.eval t = ∫ s in (τ i)..1, q.eval s := by
    intro q hq
    obtain ⟨α, hα⟩ := poly_eq_sum_legendreP q
    have hfn1 : ∀ t : ℝ, K.eval t * q.eval t =
        ∑ k ∈ Finset.range (q.natDegree + 1), α k * (K.eval t * (legendreP k).eval t) := by
      intro t
      conv_lhs => rw [hα]
      simp only [eval_finsetSum, eval_mul, eval_C, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    have hfn2 : ∀ s : ℝ, q.eval s =
        ∑ k ∈ Finset.range (q.natDegree + 1), α k * (legendreP k).eval s := by
      intro s
      conv_lhs => rw [hα]
      simp only [eval_finsetSum, eval_mul, eval_C]
    simp_rw [hfn1, hfn2]
    rw [intervalIntegral.integral_finsetSum (fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_finsetSum (fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k < n := by have := Finset.mem_range.mp hk; omega
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hproj_leg k hkn]
  -- Step 2: B_{ij} = w_j * K(τ_j)
  have hB : ∀ j : Fin n, intMatB τ i j = quadWeight τ j * K.eval (τ j) := by
    intro j
    have hdeg_Kl : (K * lagBasis τ j).natDegree ≤ 2 * (n - 1) := by
      calc (K * lagBasis τ j).natDegree ≤ K.natDegree + (lagBasis τ j).natDegree := natDegree_mul_le
        _ ≤ (n - 1) + (n - 1) := Nat.add_le_add hKdeg (lagBasis_natDegree_le hn hτ j)
        _ = 2 * (n - 1) := by omega
    have h1 := hexact (K * lagBasis τ j) hdeg_Kl
    have h2 : ∫ t in (-1 : ℝ)..1, (K * lagBasis τ j).eval t = intMatB τ i j := by
      have : ∫ t in (-1 : ℝ)..1, (K * lagBasis τ j).eval t =
          ∫ t in (-1 : ℝ)..1, K.eval t * (lagBasis τ j).eval t := by
        refine intervalIntegral.integral_congr fun t _ => eval_mul
      rw [this, hproj (lagBasis τ j) (lagBasis_natDegree_le hn hτ j)]
      rfl
    rw [← h2, h1, Finset.sum_eq_single j]
    · rw [eval_mul, lagBasis_eval_self hτ j, mul_one]
    · intro k _ hkj; rw [eval_mul, lagBasis_eval_of_ne hkj, mul_zero, mul_zero]
    · intro hnot; exact absurd (Finset.mem_univ j) hnot
  -- Step 3: Bessel inequality: ∑_j w_j K(τ_j)^2 = ∫_{-1}^1 K^2 ≤ 1 - τ_i
  have hBessel : ∑ j : Fin n, quadWeight τ j * (K.eval (τ j)) ^ 2 ≤ 1 - τ i := by
    have hdeg_K2 : (K ^ 2).natDegree ≤ 2 * (n - 1) := by
      calc (K ^ 2).natDegree ≤ 2 * K.natDegree := natDegree_pow_le
        _ ≤ 2 * (n - 1) := Nat.mul_le_mul_left 2 hKdeg
    have hqK2 := hexact (K ^ 2) hdeg_K2
    simp only [eval_pow] at hqK2
    rw [← hqK2]
    have hK2_eq : ∫ t in (-1 : ℝ)..1, (K.eval t) ^ 2 = ∫ s in (τ i)..1, K.eval s := by
      have hsq : ∀ t : ℝ, (K.eval t) ^ 2 = K.eval t * K.eval t := fun t => sq _
      simp_rw [hsq]
      exact hproj K hKdeg
    -- 0 ≤ ∫_{-1}^{τ_i} K^2 + ∫_{τ_i}^1 (1 - K)^2 = ∫_{-1}^1 K^2 + (1 - τ_i) - 2 ∫_{τ_i}^1 K
    -- = (1 - τ_i) - ∫_{-1}^1 K^2!
    have hnonneg1 : 0 ≤ ∫ t in (-1 : ℝ)..(τ i), (K.eval t) ^ 2 :=
      intervalIntegral.integral_nonneg hτi.1 fun t _ => sq_nonneg _
    have hnonneg2 : 0 ≤ ∫ t in (τ i)..1, (1 - K.eval t) ^ 2 :=
      intervalIntegral.integral_nonneg hτi.2 fun t _ => sq_nonneg _
    have hexpand : ∫ t in (τ i)..1, (1 - K.eval t) ^ 2 =
        (1 - τ i) - 2 * (∫ t in (τ i)..1, K.eval t) + ∫ t in (τ i)..1, (K.eval t) ^ 2 := by
      have hfn : ∀ t : ℝ, (1 - K.eval t) ^ 2 = (1 - 2 * K.eval t) + (K.eval t) ^ 2 := fun t => by ring
      simp_rw [hfn]
      rw [intervalIntegral.integral_add
            (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_sub
            (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_const_mul]
      simp
    have hsplit : (∫ t in (-1 : ℝ)..(τ i), (K.eval t) ^ 2) + (∫ t in (τ i)..1, (K.eval t) ^ 2) =
        ∫ t in (-1 : ℝ)..1, (K.eval t) ^ 2 :=
      intervalIntegral.integral_add_adjacent_intervals
        ((K.continuous.pow 2).intervalIntegrable _ _)
        ((K.continuous.pow 2).intervalIntegrable _ _)
    linarith
  -- Step 4: Elementary inequality |a| ≤ a + (1/2) * w * x^2 when a = w * (1 - x) and w ≥ 0!
  -- Because |1 - x| - (1 - x) = 2 * max(x - 1, 0) ≤ (1/2) * x^2!
  have hpointwise : ∀ j : Fin n,
      |intMatA τ i j| ≤ intMatA τ i j + (1 / 2 : ℝ) * (quadWeight τ j * (K.eval (τ j)) ^ 2) := by
    intro j
    have hwpos : 0 < quadWeight τ j := quadWeight_pos hn hτ hexact j
    have hAeq : intMatA τ i j = quadWeight τ j * (1 - K.eval (τ j)) := by
      have hadd := intMatA_add_intMatB τ i j
      rw [hB j] at hadd
      linarith
    rw [hAeq, abs_mul, abs_of_pos hwpos]
    set x := K.eval (τ j)
    have hkey : |1 - x| ≤ (1 - x) + (1 / 2 : ℝ) * x ^ 2 := by
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg (x - 2)]
      · nlinarith [sq_nonneg x]
    nlinarith
  calc
    ∑ j : Fin n, |intMatA τ i j|
      ≤ ∑ j : Fin n, (intMatA τ i j + (1 / 2 : ℝ) * (quadWeight τ j * (K.eval (τ j)) ^ 2)) :=
        Finset.sum_le_sum fun j _ => hpointwise j
    _ = (∑ j : Fin n, intMatA τ i j) +
          (1 / 2 : ℝ) * (∑ j : Fin n, quadWeight τ j * (K.eval (τ j)) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (1 + τ i) + (1 / 2 : ℝ) * (∑ j : Fin n, quadWeight τ j * (K.eval (τ j)) ^ 2) := by
        rw [sum_intMatA hn hτ i]
    _ ≤ (1 + τ i) + (1 / 2 : ℝ) * (1 - τ i) := by linarith [hBessel]
    _ = (3 + τ i) / 2 := by ring

/-- Non-vacuity witness for Gauss-Legendre nodes: for every `n ≥ 1`, `legendreP n` has degree `n`,
is orthogonal on `[-1, 1]` to all polynomials of degree `< n`, and has `n` strictly increasing
simple roots in `(-1, 1)`. -/
theorem exists_gauss_legendre_nodes (n : ℕ) (_hn : 1 ≤ n) :
    ∃ (P : Polynomial ℝ) (τ : Fin n → ℝ),
      P.natDegree = n ∧
      (∀ q : Polynomial ℝ, q.natDegree < n → ∫ t in (-1 : ℝ)..1, P.eval t * q.eval t = 0) ∧
      StrictMono τ ∧
      (∀ i : Fin n, -1 < τ i ∧ τ i < 1) ∧
      (∀ i : Fin n, P.eval (τ i) = 0) := by
  obtain ⟨τ, hmono, hIoo, hroots, _, _⟩ := roots_of_orthog_weight
    (d := n) (P := legendreP n) (w := fun _ => 1)
    continuous_const (fun _ _ => zero_lt_one) (fun _ _ => zero_le_one)
    (legendreP_ne_zero n) (legendreP_natDegree n)
    (fun q hq => by simpa using legendreP_orthog_lt hq)
  exact ⟨legendreP n, τ, legendreP_natDegree n, fun q hq => legendreP_orthog_lt hq,
    hmono, hIoo, hroots⟩

/-- Non-vacuity witness for Gauss-Radau nodes: for every `n ≥ 1`, `P_n - P_{n-1}` has degree `n`,
vanishes at `1`, is orthogonal on `[-1, 1]` to all polynomials of degree `< n - 1`, and has `n`
strictly increasing roots in `(-1, 1]` with `τ_{n-1} = 1`. -/
theorem exists_radau_nodes (n : ℕ) (hn : 1 ≤ n) :
    ∃ (R : Polynomial ℝ) (τ : Fin n → ℝ),
      R.natDegree = n ∧
      R.eval 1 = 0 ∧
      (∀ q : Polynomial ℝ, q.natDegree < n - 1 → ∫ t in (-1 : ℝ)..1, R.eval t * q.eval t = 0) ∧
      StrictMono τ ∧
      (∀ i : Fin n, -1 < τ i ∧ τ i ≤ 1) ∧
      τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ = 1 ∧
      (∀ i : Fin n, R.eval (τ i) = 0) := by
  let R : Polynomial ℝ := legendreP n - legendreP (n - 1)
  have hRdeg : R.natDegree = n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · exact legendreP_natDegree n
    · rw [legendreP_natDegree, legendreP_natDegree]; omega
  have hR1 : R.eval 1 = 0 := by simp [R, legendreP_eval_one]
  have hRorth : ∀ q : Polynomial ℝ, q.natDegree < n - 1 →
      ∫ t in (-1 : ℝ)..1, R.eval t * q.eval t = 0 := by
    intro q hq
    have hfn : ∀ t : ℝ, R.eval t * q.eval t =
        (legendreP n).eval t * q.eval t - (legendreP (n - 1)).eval t * q.eval t := fun t => by
      simp [R, eval_sub]; ring
    simp_rw [hfn]
    rw [intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        legendreP_orthog_lt (by omega : q.natDegree < n),
        legendreP_orthog_lt hq, sub_self]
  have hdvd : (X - C (1 : ℝ)) ∣ R := dvd_iff_isRoot.mpr hR1
  obtain ⟨Q, hQ⟩ := hdvd
  have hRne : R ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hRdeg; omega
  have hQne : Q ≠ 0 := by intro h0; rw [h0, mul_zero] at hQ; exact hRne hQ
  have hQdeg : Q.natDegree = n - 1 := by
    have hmul := natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hQne
    rw [← hQ, hRdeg, natDegree_X_sub_C] at hmul
    omega
  have hQorth : ∀ q : Polynomial ℝ, q.natDegree < n - 1 →
      ∫ t in (-1 : ℝ)..1, (1 - t) * Q.eval t * q.eval t = 0 := by
    intro q hq
    have hfn : ∀ t : ℝ, (1 - t) * Q.eval t * q.eval t = -(R.eval t * q.eval t) := fun t => by
      have hv := congr_arg (fun p => p.eval t) hQ
      simp only [eval_mul, eval_sub, eval_X, eval_C] at hv
      rw [hv]; ring
    simp_rw [hfn]
    rw [intervalIntegral.integral_neg, hRorth q hq, neg_zero]
  obtain ⟨σ, hσmono, hσIoo, hσroots, _, _⟩ := roots_of_orthog_weight
    (d := n - 1) (P := Q) (w := fun t => 1 - t)
    (by fun_prop) (fun t ht => by linarith [ht.2]) (fun t ht => by linarith [ht.2])
    hQne hQdeg hQorth
  let τ : Fin n → ℝ := fun i =>
    if h : i.val < n - 1 then σ ⟨i.val, h⟩ else 1
  refine ⟨R, τ, hRdeg, hR1, hRorth, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    dsimp only [τ]
    by_cases hi : i.val < n - 1
    · by_cases hj : j.val < n - 1
      · rw [dif_pos hi, dif_pos hj]
        exact hσmono (show (⟨i.val, hi⟩ : Fin (n - 1)) < ⟨j.val, hj⟩ from hij)
      · rw [dif_pos hi, dif_neg hj]
        exact (hσIoo ⟨i.val, hi⟩).2
    · exfalso
      have : j.val < n := j.isLt
      have : i.val < j.val := hij
      omega
  · intro i
    dsimp only [τ]
    by_cases hi : i.val < n - 1
    · rw [dif_pos hi]
      exact ⟨(hσIoo ⟨i.val, hi⟩).1, le_of_lt (hσIoo ⟨i.val, hi⟩).2⟩
    · rw [dif_neg hi]; norm_num
  · dsimp only [τ]
    rw [dif_neg (lt_irrefl _)]
  · intro i
    dsimp only [τ]
    by_cases hi : i.val < n - 1
    · rw [dif_pos hi, hQ, eval_mul, hσroots ⟨i.val, hi⟩, mul_zero]
    · rw [dif_neg hi]; exact hR1

/-- **Companion Challenge Theorem (Hager's Radau Reverse-Markov Bound `|p(τ_i)| ≤ 2`):**
Stated in pure Mathlib with ZERO custom definitions. -/
theorem hager_radau_bound_challenge
    (n : ℕ) (hn : 1 ≤ n)
    (R : Polynomial ℝ) (hRdeg : R.natDegree = n) (hR1 : R.eval 1 = 0)
    (hRorth : ∀ q : Polynomial ℝ, q.natDegree < n - 1 →
      ∫ t in (-1 : ℝ)..1, R.eval t * q.eval t = 0)
    (τ : Fin n → ℝ) (hτmono : StrictMono τ) (hτroots : ∀ i : Fin n, R.eval (τ i) = 0)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ n) (hp_m1 : p.eval (-1) = 0)
    (hderiv : ∀ i : Fin n, |p.derivative.eval (τ i)| ≤ 1) :
    ∀ i : Fin n, |p.eval (τ i)| ≤ 2 := by
  -- First deduce from R's hypotheses that every root of R lies in (-1, 1]
  have hRne : R ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hRdeg; omega
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hR1
  have hQne : Q ≠ 0 := by intro h0; rw [h0, mul_zero] at hQ; exact hRne hQ
  have hQdeg : Q.natDegree = n - 1 := by
    have hmul := natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hQne
    rw [← hQ, hRdeg, natDegree_X_sub_C] at hmul
    omega
  have hQorth : ∀ q : Polynomial ℝ, q.natDegree < n - 1 →
      ∫ t in (-1 : ℝ)..1, (1 - t) * Q.eval t * q.eval t = 0 := by
    intro q hq
    have hfn : ∀ t : ℝ, (1 - t) * Q.eval t * q.eval t = -(R.eval t * q.eval t) := fun t => by
      have hv := congr_arg (fun p => p.eval t) hQ
      simp only [eval_mul, eval_sub, eval_X, eval_C] at hv
      rw [hv]; ring
    simp_rw [hfn]
    rw [intervalIntegral.integral_neg, hRorth q hq, neg_zero]
  obtain ⟨σ, _, hσIoo, _, hσall, _⟩ := roots_of_orthog_weight
    (d := n - 1) (P := Q) (w := fun t => 1 - t)
    (by fun_prop) (fun t ht => by linarith [ht.2]) (fun t ht => by linarith [ht.2])
    hQne hQdeg hQorth
  have hτIcc : ∀ i : Fin n, τ i ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i
    have hri := hτroots i
    rw [hQ, eval_mul, eval_sub, eval_X, eval_C] at hri
    rcases mul_eq_zero.mp hri with h1 | h2
    · have : τ i = 1 := sub_eq_zero.mp h1
      rw [this]; norm_num
    · obtain ⟨j, hj⟩ := hσall (τ i) h2
      rw [← hj]
      exact ⟨le_of_lt (hσIoo j).1, le_of_lt (hσIoo j).2⟩
  have hexact : ∀ f : Polynomial ℝ, f.natDegree ≤ 2 * (n - 1) →
      ∫ t in (-1 : ℝ)..1, f.eval t = ∑ j : Fin n, quadWeight τ j * f.eval (τ j) := by
    intro f hf
    exact quad_exact_of_orthog hn hτmono.injective hRdeg hτroots hRorth (by omega)
  intro i
  calc
    |p.eval (τ i)| ≤ ∑ j : Fin n, |intMatA τ i j| :=
      poly_abs_bound_of_sum_abs_intMatA hn hτmono.injective hpdeg hp_m1 hderiv i
    _ ≤ (3 + τ i) / 2 :=
      sum_abs_intMatA_le_three_add_div_two hn hτmono.injective hexact (hτIcc i)
    _ ≤ 2 := by linarith [(hτIcc i).2]

end RootsQuadraturePart1

section Part2RootGap

/-- Alternating sum of a nonnegative decreasing sequence is nonnegative. -/
lemma alt_sum_nonneg_gen :
    ∀ m : ℕ, ∀ a : ℕ → ℝ, (∀ k, 0 ≤ a k) → (∀ k, a (k + 1) ≤ a k) →
      0 ≤ ∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * a k := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a hnn hdec
    match m with
    | 0 => simp
    | 1 => simp [hnn 0]
    | k + 2 =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hshift : ∑ j ∈ Finset.range k, (-1 : ℝ) ^ (j + 1 + 1) * a (j + 1 + 1) =
          ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * a (j + 2) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ, pow_succ]; ring
      rw [hshift]
      have htail := ih k (by omega) (fun j => a (j + 2))
        (fun j => hnn (j + 2)) (fun j => hdec (j + 2))
      have h01 : 0 ≤ a 0 - a 1 := sub_nonneg.mpr (hdec 0)
      simp only [zero_add, pow_zero, one_mul, pow_one, neg_mul]
      linarith

/-- Scaled positive term `a_k(n, u)` in `P_n(1 - 2u / N) = ∑_{k=0}^n (-1)^k a_k(n, u)`. -/
noncomputable def legTerm (n : ℕ) (u : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * (Nat.choose (n + k) k : ℝ) * (u / ((n : ℝ) * ((n : ℝ) + 1))) ^ k

/-- Scaled positive term `b_m(n, u)` in `(2 / N) P_n'(1 - 2u / N) = ∑_{m=0}^{n-1} (-1)^m b_m(n, u)`. -/
noncomputable def legDerivTerm (n : ℕ) (u : ℝ) (m : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) *
    (Nat.choose n (m + 1) : ℝ) * (Nat.choose (n + (m + 1)) (m + 1) : ℝ) *
    (u / ((n : ℝ) * ((n : ℝ) + 1))) ^ m

lemma legTerm_nonneg {n : ℕ} {u : ℝ} (hu : 0 ≤ u) (k : ℕ) : 0 ≤ legTerm n u k := by
  unfold legTerm
  have hN : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) := by positivity
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (pow_nonneg (div_nonneg hu hN) k)

lemma legDerivTerm_nonneg {n : ℕ} {u : ℝ} (hu : 0 ≤ u) (m : ℕ) : 0 ≤ legDerivTerm n u m := by
  unfold legDerivTerm
  have hN : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) := by positivity
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hN) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))
    (pow_nonneg (div_nonneg hu hN) m)

lemma legTerm_zero (n : ℕ) (u : ℝ) : legTerm n u 0 = 1 := by
  simp [legTerm]

lemma legTerm_succ {n : ℕ} (hn : 1 ≤ n) (u : ℝ) (k : ℕ) :
    legTerm n u (k + 1) =
      legTerm n u k *
        ((1 - (k : ℝ) * ((k : ℝ) + 1) / ((n : ℝ) * ((n : ℝ) + 1))) *
          (u / (((k + 1 : ℕ) : ℝ) ^ 2))) := by
  set N : ℝ := (n : ℝ) * ((n : ℝ) + 1)
  have hNpos : 0 < N := by positivity
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hk1ne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hrec := legCoeff_succ n k
  unfold legCoeff at hrec
  have hrec' : ((k + 1 : ℕ) : ℝ) ^ 2 *
      ((Nat.choose n (k + 1) : ℝ) * (Nat.choose (n + (k + 1)) (k + 1) : ℝ)) =
      (N - (k : ℝ) * ((k : ℝ) + 1)) *
        ((Nat.choose n k : ℝ) * (Nat.choose (n + k) k : ℝ)) := by
    have hsign : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by rw [pow_succ]; ring
    rw [hsign] at hrec
    have hpow_ne : (-1 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    apply mul_left_cancel₀ hpow_ne
    dsimp only [N]
    nlinarith [hrec]
  unfold legTerm
  rw [pow_succ]
  have hcast : (n : ℝ) * ((n : ℝ) + 1) = N := rfl
  rw [hcast]
  field_simp [hNne, hk1ne]
  have hmul := congr_arg (fun z => z * (u * (u / N) ^ k)) hrec'
  linarith [hmul]

lemma legDerivTerm_eq_legTerm {n : ℕ} (u : ℝ) (m : ℕ) :
    legDerivTerm n u m * u = ((m + 1 : ℕ) : ℝ) * legTerm n u (m + 1) := by
  unfold legDerivTerm legTerm
  rw [pow_succ]
  ring

lemma legDerivTerm_zero {n : ℕ} (hn : 1 ≤ n) (u : ℝ) : legDerivTerm n u 0 = 1 := by
  unfold legDerivTerm
  have hNpos : 0 < (n : ℝ) * ((n : ℝ) + 1) := by positivity
  simp only [Nat.zero_add, Nat.cast_one, Nat.choose_one_right, pow_zero, mul_one]
  push_cast
  field_simp [ne_of_gt hNpos]

lemma legDerivTerm_succ {n : ℕ} (hn : 1 ≤ n) (u : ℝ) (m : ℕ) :
    legDerivTerm n u (m + 1) =
      legDerivTerm n u m *
        ((1 - ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) + 1))) *
          (u / (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)))) := by
  set N : ℝ := (n : ℝ) * ((n : ℝ) + 1)
  have hNne : N ≠ 0 := by positivity
  have hm1ne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hm2ne : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hrec := legCoeff_succ n (m + 1)
  unfold legCoeff at hrec
  have hrec' : ((m + 2 : ℕ) : ℝ) ^ 2 *
      ((Nat.choose n (m + 2) : ℝ) * (Nat.choose (n + (m + 2)) (m + 2) : ℝ)) =
      (N - ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) *
        ((Nat.choose n (m + 1) : ℝ) * (Nat.choose (n + (m + 1)) (m + 1) : ℝ)) := by
    have hsign : (-1 : ℝ) ^ (m + 1 + 1) = -((-1 : ℝ) ^ (m + 1)) := by rw [pow_succ]; ring
    rw [hsign] at hrec
    have hpow_ne : (-1 : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero (m + 1) (by norm_num)
    apply mul_left_cancel₀ hpow_ne
    have hcast : ((m + 2 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    dsimp only [N]
    push_cast at hrec ⊢
    nlinarith [hrec]
  unfold legDerivTerm
  change ((m + 2 : ℕ) : ℝ) / N * (Nat.choose n (m + 2) : ℝ) *
      (Nat.choose (n + (m + 2)) (m + 2) : ℝ) * (u / N) ^ (m + 1) =
    ((m + 1 : ℕ) : ℝ) / N * (Nat.choose n (m + 1) : ℝ) *
      (Nat.choose (n + (m + 1)) (m + 1) : ℝ) * (u / N) ^ m *
      ((1 - ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) / N) *
        (u / (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ))))
  rw [pow_succ]
  have hmul : ((m + 2 : ℕ) : ℝ) ^ 2 *
      (((m + 2 : ℕ) : ℝ) / N * (Nat.choose n (m + 2) : ℝ) *
        (Nat.choose (n + (m + 2)) (m + 2) : ℝ) * ((u / N) ^ m * (u / N))) =
      ((m + 2 : ℕ) : ℝ) ^ 2 *
      (((m + 1 : ℕ) : ℝ) / N * (Nat.choose n (m + 1) : ℝ) *
        (Nat.choose (n + (m + 1)) (m + 1) : ℝ) * (u / N) ^ m *
        ((1 - ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) / N) *
          (u / (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ))))) := by
    have h1 : ((m + 2 : ℕ) : ℝ) ^ 2 *
        (((m + 2 : ℕ) : ℝ) / N * (Nat.choose n (m + 2) : ℝ) *
          (Nat.choose (n + (m + 2)) (m + 2) : ℝ) * ((u / N) ^ m * (u / N))) =
        (((m + 2 : ℕ) : ℝ) ^ 2 *
          ((Nat.choose n (m + 2) : ℝ) * (Nat.choose (n + (m + 2)) (m + 2) : ℝ))) *
          (((m + 2 : ℕ) : ℝ) / N * ((u / N) ^ m * (u / N))) := by ring
    rw [h1, hrec']
    field_simp [hNne, hm1ne, hm2ne]
  exact mul_left_cancel₀ (pow_ne_zero 2 hm2ne) hmul

lemma legendreP_eval_shifted {n : ℕ} (_hn : 1 ≤ n) (u : ℝ) :
    (legendreP n).eval (1 - 2 * u / ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * legTerm n u k := by
  rw [legendreP_eq_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X, legCoeff, legTerm]
  have harg : 1 / 2 * (1 - (1 - 2 * u / ((n : ℝ) * ((n : ℝ) + 1)))) =
      u / ((n : ℝ) * ((n : ℝ) + 1)) := by ring
  rw [harg]
  ring

lemma legendreP_deriv_eval_shifted {n : ℕ} (_hn : 1 ≤ n) (u : ℝ) :
    2 / ((n : ℝ) * ((n : ℝ) + 1)) *
        (legendreP n).derivative.eval (1 - 2 * u / ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * legDerivTerm n u m := by
  set N : ℝ := (n : ℝ) * ((n : ℝ) + 1)
  have hYderiv : (C (1 / 2 : ℝ) * (1 - X) : Polynomial ℝ).derivative = C (-1 / 2 : ℝ) := by
    rw [derivative_C_mul, derivative_sub, derivative_one, derivative_X]
    have hneg : (C (-1 / 2 : ℝ) : Polynomial ℝ) = -C (1 / 2 : ℝ) := by
      rw [← C_neg]; congr 1; ring
    rw [hneg]; ring
  rw [legendreP_eq_sum, derivative_sum, eval_finsetSum, Finset.mul_sum]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one, derivative_C, eval_zero, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [derivative_C_mul, derivative_pow, hYderiv]
  simp only [Nat.add_sub_cancel, eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X,
    legCoeff, legDerivTerm]
  have harg : 1 / 2 * (1 - (1 - 2 * u / N)) = u / N := by ring
  rw [harg, pow_succ]
  ring

/-- **Lemma 2.1 (Strict Monotonicity on `u ∈ [0, 3]`):** For all `n ≥ 3` and `u ∈ [0, 3]`,
`P_n'(1 - 2u / N) > 0` via a 1-line `ring` SOS identity on `144 L_3(x, u) ≥ 9`. -/
theorem legendreP_deriv_pos_on_Icc {n : ℕ} (hn : 3 ≤ n) {u : ℝ} (hu0 : 0 ≤ u) (hu3 : u ≤ 3) :
    0 < (legendreP n).derivative.eval (1 - 2 * u / ((n : ℝ) * ((n : ℝ) + 1))) := by
  set N : ℝ := (n : ℝ) * ((n : ℝ) + 1)
  have hNge : (12 : ℝ) ≤ N := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp only [N]; nlinarith
  have hNpos : 0 < N := by linarith
  have h2N : 0 < 2 / N := by positivity
  suffices hsum : 0 < ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * legDerivTerm n u m by
    have heq := legendreP_deriv_eval_shifted (by omega : 1 ≤ n) u
    nlinarith
  -- Extend range to max n 4 (terms with m ≥ n are 0 since choose n (m+1) = 0)
  let M := max n 4
  have hpad : ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * legDerivTerm n u m =
      ∑ m ∈ Finset.range M, (-1 : ℝ) ^ m * legDerivTerm n u m := by
    refine Finset.sum_subset (Finset.range_mono (le_max_left n 4)) ?_
    intro m _ hnot
    have hge : n ≤ m := by rw [Finset.mem_range] at hnot; omega
    have hch : Nat.choose n (m + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [legDerivTerm, hch]
  rw [hpad]
  have hM4 : 4 ≤ M := le_max_right n 4
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hM4
  rw [hr, Finset.sum_range_add]
  have htail_nn : 0 ≤ ∑ j ∈ Finset.range r, (-1 : ℝ) ^ (4 + j) * legDerivTerm n u (4 + j) := by
    have hsign : ∀ j : ℕ, (-1 : ℝ) ^ (4 + j) = (-1 : ℝ) ^ j := fun j => by
      rw [pow_add]; norm_num
    simp_rw [hsign]
    refine alt_sum_nonneg_gen r (fun j => legDerivTerm n u (4 + j))
      (fun j => legDerivTerm_nonneg hu0 (4 + j)) ?_
    intro j
    have hstep := legDerivTerm_succ (by omega : 1 ≤ n) u (4 + j)
    have hidx : 4 + j + 1 = 4 + (j + 1) := by omega
    rw [← hidx, hstep]
    have hfac : (1 - ((4 + j + 1 : ℕ) : ℝ) * ((4 + j + 2 : ℕ) : ℝ) / N) *
        (u / (((4 + j + 1 : ℕ) : ℝ) * ((4 + j + 2 : ℕ) : ℝ))) ≤ 1 := by
      have h1 : 1 - ((4 + j + 1 : ℕ) : ℝ) * ((4 + j + 2 : ℕ) : ℝ) / N ≤ 1 := by
        have : 0 ≤ ((4 + j + 1 : ℕ) : ℝ) * ((4 + j + 2 : ℕ) : ℝ) / N := by positivity
        linarith
      have h2 : 0 ≤ u / (((4 + j + 1 : ℕ) : ℝ) * ((4 + j + 2 : ℕ) : ℝ)) := by positivity
      have h3 : u / (((4 + j + 1 : ℕ) : ℝ) * ((4 + j + 2 : ℕ) : ℝ)) ≤ 1 := by
        have hden : (30 : ℝ) ≤ ((4 + j + 1 : ℕ) : ℝ) * ((4 + j + 2 : ℕ) : ℝ) := by
          have ha : (5 : ℝ) ≤ ((4 + j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ 4 + j + 1)
          have hb : (6 : ℝ) ≤ ((4 + j + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 6 ≤ 4 + j + 2)
          nlinarith
        rw [div_le_one (by linarith)]
        linarith
      nlinarith
    have hnn := legDerivTerm_nonneg (n := n) hu0 (4 + j)
    dsimp only [N] at hfac
    nlinarith
  -- Compute the first 4 terms explicitly: b0 - b1 + b2 - b3
  set x : ℝ := 1 / N
  have hx0 : 0 ≤ x := by positivity
  have hx12 : 12 * x ≤ 1 := by
    dsimp only [x]
    rw [mul_one_div, div_le_one hNpos]
    exact hNge
  set t : ℝ := 12 * x
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have ht1 : t ≤ 1 := hx12
  have hb0 : legDerivTerm n u 0 = 1 := legDerivTerm_zero (by omega) u
  have hb1 : legDerivTerm n u 1 = (1 - 2 * x) * u / 2 := by
    have h := legDerivTerm_succ (by omega : 1 ≤ n) u 0
    rw [hb0] at h
    dsimp only [x]
    push_cast at h ⊢
    rw [h]; ring
  have hb2 : legDerivTerm n u 2 = (1 - 2 * x) * (1 - 6 * x) * u ^ 2 / 12 := by
    have h := legDerivTerm_succ (by omega : 1 ≤ n) u 1
    rw [hb1] at h
    dsimp only [x]
    push_cast at h ⊢
    rw [h]; ring
  have hb3 : legDerivTerm n u 3 = (1 - 2 * x) * (1 - 6 * x) * (1 - 12 * x) * u ^ 3 / 144 := by
    have h := legDerivTerm_succ (by omega : 1 ≤ n) u 2
    rw [hb2] at h
    dsimp only [x]
    push_cast at h ⊢
    rw [h]; ring
  have hhead : ∑ m ∈ Finset.range 4, (-1 : ℝ) ^ m * legDerivTerm n u m =
      legDerivTerm n u 0 - legDerivTerm n u 1 + legDerivTerm n u 2 - legDerivTerm n u 3 := by
    simp [Finset.sum_range_succ]; ring
  have hL3_pos : 0 < legDerivTerm n u 0 - legDerivTerm n u 1 + legDerivTerm n u 2 - legDerivTerm n u 3 := by
    rw [hb0, hb1, hb2, hb3]
    have hsos : 144 * (1 - (1 - 2 * x) * u / 2 + (1 - 2 * x) * (1 - 6 * x) * u ^ 2 / 12 -
        (1 - 2 * x) * (1 - 6 * x) * (1 - 12 * x) * u ^ 3 / 144) =
      9 + (3 - u) * ((u - 9 / 2) ^ 2 + 99 / 4) +
        x * u * (12 * t * (3 - u) * (4 - u) + (1 - t) * ((4 * u - 12) ^ 2 + (4 - t) * u ^ 2)) := by
      dsimp only [t]; ring
    have hp1 : 0 ≤ (3 - u) * ((u - 9 / 2) ^ 2 + 99 / 4) :=
      mul_nonneg (by linarith) (by positivity)
    have hp2 : 0 ≤ 12 * t * (3 - u) * (4 - u) := by
      have : 0 ≤ (3 - u) * (4 - u) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hp3 : 0 ≤ (1 - t) * ((4 * u - 12) ^ 2 + (4 - t) * u ^ 2) :=
      mul_nonneg (by linarith) (add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _)))
    have hp4 : 0 ≤ x * u * (12 * t * (3 - u) * (4 - u) +
        (1 - t) * ((4 * u - 12) ^ 2 + (4 - t) * u ^ 2)) :=
      mul_nonneg (mul_nonneg hx0 hu0) (add_nonneg hp2 hp3)
    linarith
  linarith

/-- **Lemma 2.2 (Strict Negativity on `u ∈ [3/2, 5]`):** For all `n ≥ 3` and `u ∈ [3/2, 5]`,
`P_n(1 - 2u / N) < 0` via a 1-line `ring` SOS identity on `576 U_4(x, u) < 0`. -/
theorem legendreP_neg_on_Icc {n : ℕ} (hn : 3 ≤ n) {u : ℝ} (hu_lo : 3 / 2 ≤ u) (hu_hi : u ≤ 5) :
    (legendreP n).eval (1 - 2 * u / ((n : ℝ) * ((n : ℝ) + 1))) < 0 := by
  set N : ℝ := (n : ℝ) * ((n : ℝ) + 1)
  have hNge : (12 : ℝ) ≤ N := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp only [N]; nlinarith
  have hNpos : 0 < N := by linarith
  have hu0 : 0 ≤ u := by linarith
  rw [legendreP_eval_shifted (by omega : 1 ≤ n) u]
  let M := max (n + 1) 5
  have hpad : ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * legTerm n u k =
      ∑ k ∈ Finset.range M, (-1 : ℝ) ^ k * legTerm n u k := by
    refine Finset.sum_subset (Finset.range_mono (le_max_left (n + 1) 5)) ?_
    intro k _ hnot
    have hgt : n < k := by rw [Finset.mem_range] at hnot; omega
    have hch : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt hgt
    simp [legTerm, hch]
  rw [hpad]
  have hM5 : 5 ≤ M := le_max_right (n + 1) 5
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hM5
  rw [hr, Finset.sum_range_add]
  have htail_np : ∑ j ∈ Finset.range r, (-1 : ℝ) ^ (5 + j) * legTerm n u (5 + j) ≤ 0 := by
    have hsign : ∀ j : ℕ, (-1 : ℝ) ^ (5 + j) * legTerm n u (5 + j) =
        -((-1 : ℝ) ^ j * legTerm n u (5 + j)) := fun j => by
      rw [pow_add]; norm_num
    simp_rw [hsign, Finset.sum_neg_distrib, neg_nonpos]
    refine alt_sum_nonneg_gen r (fun j => legTerm n u (5 + j))
      (fun j => legTerm_nonneg hu0 (5 + j)) ?_
    intro j
    have hstep := legTerm_succ (by omega : 1 ≤ n) u (5 + j)
    have hidx : 5 + j + 1 = 5 + (j + 1) := by omega
    rw [← hidx, hstep]
    have hfac : (1 - ((5 + j : ℕ) : ℝ) * (((5 + j : ℕ) : ℝ) + 1) / N) *
        (u / (((5 + j + 1 : ℕ) : ℝ) ^ 2)) ≤ 1 := by
      have h1 : 1 - ((5 + j : ℕ) : ℝ) * (((5 + j : ℕ) : ℝ) + 1) / N ≤ 1 := by
        have : 0 ≤ ((5 + j : ℕ) : ℝ) * (((5 + j : ℕ) : ℝ) + 1) / N := by positivity
        linarith
      have h2 : 0 ≤ u / (((5 + j + 1 : ℕ) : ℝ) ^ 2) := by positivity
      have h3 : u / (((5 + j + 1 : ℕ) : ℝ) ^ 2) ≤ 1 := by
        have hden : (36 : ℝ) ≤ (((5 + j + 1 : ℕ) : ℝ) ^ 2) := by
          have ha : (6 : ℝ) ≤ ((5 + j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 6 ≤ 5 + j + 1)
          nlinarith
        rw [div_le_one (by linarith)]
        linarith
      nlinarith
    have hnn := legTerm_nonneg (n := n) hu0 (5 + j)
    dsimp only [N] at hfac
    nlinarith
  set x : ℝ := 1 / N
  have hx0 : 0 ≤ x := by positivity
  have hx12 : 12 * x ≤ 1 := by
    dsimp only [x]; rw [mul_one_div, div_le_one hNpos]; exact hNge
  set t : ℝ := 12 * x
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have ht1 : t ≤ 1 := hx12
  have ha0 : legTerm n u 0 = 1 := legTerm_zero n u
  have ha1 : legTerm n u 1 = u := by
    have h := legTerm_succ (by omega : 1 ≤ n) u 0
    rw [ha0] at h; push_cast at h ⊢; rw [h]; ring
  have ha2 : legTerm n u 2 = (1 - 2 * x) * u ^ 2 / 4 := by
    have h := legTerm_succ (by omega : 1 ≤ n) u 1
    rw [ha1] at h; dsimp only [x]; push_cast at h ⊢; rw [h]; ring
  have ha3 : legTerm n u 3 = (1 - 2 * x) * (1 - 6 * x) * u ^ 3 / 36 := by
    have h := legTerm_succ (by omega : 1 ≤ n) u 2
    rw [ha2] at h; dsimp only [x]; push_cast at h ⊢; rw [h]; ring
  have ha4 : legTerm n u 4 = (1 - 2 * x) * (1 - 6 * x) * (1 - 12 * x) * u ^ 4 / 576 := by
    have h := legTerm_succ (by omega : 1 ≤ n) u 3
    rw [ha3] at h; dsimp only [x]; push_cast at h ⊢; rw [h]; ring
  have hhead : ∑ k ∈ Finset.range 5, (-1 : ℝ) ^ k * legTerm n u k =
      legTerm n u 0 - legTerm n u 1 + legTerm n u 2 - legTerm n u 3 + legTerm n u 4 := by
    simp [Finset.sum_range_succ]; ring
  have hU4_neg : legTerm n u 0 - legTerm n u 1 + legTerm n u 2 - legTerm n u 3 + legTerm n u 4 < 0 := by
    rw [ha0, ha1, ha2, ha3, ha4]
    have hsos : 576 * (1 - u + (1 - 2 * x) * u ^ 2 / 4 -
        (1 - 2 * x) * (1 - 6 * x) * u ^ 3 / 36 +
        (1 - 2 * x) * (1 - 6 * x) * (1 - 12 * x) * u ^ 4 / 576) =
      ((u - 3 / 2) * (u - 5) * ((u - 19 / 4) ^ 2 + 835 / 16) + (-151 / 8 * u + 123 / 8)) +
        x * u ^ 2 * ((1 - t) * (-288 + 128 * u - (20 - t) * u ^ 2) +
          t * (-288 + 112 * u - 12 * u ^ 2)) := by
      dsimp only [t]; ring
    have hq1 : (u - 3 / 2) * (u - 5) * ((u - 19 / 4) ^ 2 + 835 / 16) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
        (by positivity)
    have hlin : -151 / 8 * u + 123 / 8 < 0 := by linarith
    have hbr1 : -288 + 128 * u - (20 - t) * u ^ 2 ≤ 0 := by
      have h19 : 19 * u ^ 2 - 128 * u + 288 = 19 * (u - 64 / 19) ^ 2 + 1376 / 19 := by ring
      have : 0 ≤ 19 * u ^ 2 - 128 * u + 288 := by rw [h19]; positivity
      nlinarith [sq_nonneg u]
    have hbr2 : -288 + 112 * u - 12 * u ^ 2 ≤ 0 := by
      have h12 : 12 * u ^ 2 - 112 * u + 288 = 12 * (u - 14 / 3) ^ 2 + 80 / 3 := by ring
      have : 0 ≤ 12 * u ^ 2 - 112 * u + 288 := by rw [h12]; positivity
      linarith
    have hbr : x * u ^ 2 * ((1 - t) * (-288 + 128 * u - (20 - t) * u ^ 2) +
        t * (-288 + 112 * u - 12 * u ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hx0 (sq_nonneg u))
        (add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) hbr1)
          (mul_nonpos_of_nonneg_of_nonpos ht0 hbr2))
    linarith
  linarith

/-- **Part 2 Main Theorem (Root-Gap Inequality):** For all `n ≥ 2`, the two largest roots
`τ_{n-2} < τ_{n-1}` of `legendreP n` satisfy `3 * (1 - τ_{n-1}) < 1 - τ_{n-2}`. -/
theorem legendreP_root_gap {n : ℕ} (hn : 2 ≤ n) {τ : Fin n → ℝ}
    (hmono : StrictMono τ) (hroots : ∀ i : Fin n, (legendreP n).eval (τ i) = 0) :
    3 * (1 - τ ⟨n - 1, by omega⟩) < 1 - τ ⟨n - 2, by omega⟩ := by
  by_cases hn2 : n = 2
  · subst hn2
    have hP2 : ∀ t : ℝ, (legendreP 2).eval t = (3 * t ^ 2 - 1) / 2 := by
      intro t
      rw [legendreP_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      have hch42 : Nat.choose 4 2 = 6 := by decide
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X, legCoeff]
      norm_num [hch42]
      ring
    have hr0 := hroots ⟨0, by omega⟩
    have hr1 := hroots ⟨1, by omega⟩
    rw [hP2] at hr0 hr1
    have hlt : τ ⟨0, by omega⟩ < τ ⟨1, by omega⟩ := hmono (show (⟨0, by omega⟩ : Fin 2) < ⟨1, by omega⟩ by decide)
    have hsq0 : 3 * (τ ⟨0, by omega⟩) ^ 2 = 1 := by linarith
    have hsq1 : 3 * (τ ⟨1, by omega⟩) ^ 2 = 1 := by linarith
    have hsum0 : (τ ⟨1, by omega⟩ - τ ⟨0, by omega⟩) * (τ ⟨1, by omega⟩ + τ ⟨0, by omega⟩) = 0 := by
      nlinarith
    have hneg : τ ⟨0, by omega⟩ = -τ ⟨1, by omega⟩ := by
      rcases mul_eq_zero.mp hsum0 with h | h <;> linarith
    have hpos1 : 0 < τ ⟨1, by omega⟩ := by linarith
    have hgt_half : (1 / 2 : ℝ) < τ ⟨1, by omega⟩ := by nlinarith
    linarith
  · have hn3 : 3 ≤ n := by omega
    set N : ℝ := (n : ℝ) * ((n : ℝ) + 1)
    have hNpos : 0 < N := by positivity
    set τ_last := τ ⟨n - 1, by omega⟩
    set τ_prev := τ ⟨n - 2, by omega⟩
    have hlt_nodes : τ_prev < τ_last :=
      hmono (show (⟨n - 2, by omega⟩ : Fin n) < ⟨n - 1, by omega⟩ from by simp; omega)
    -- Obtain the full root enumeration of legendreP n to know every root is in Set.range τ
    obtain ⟨τ₀, hmono₀, hIoo₀, hroots₀, hall₀, _⟩ := roots_of_orthog_weight
      (d := n) (P := legendreP n) (w := fun _ => 1)
      continuous_const (fun _ _ => zero_lt_one) (fun _ _ => zero_le_one)
      (legendreP_ne_zero n) (legendreP_natDegree n)
      (fun q hq => by simpa using legendreP_orthog_lt hq)
    have hτeq : τ = τ₀ := roots_enum_unique hmono hmono₀ hroots hall₀
    have hall : ∀ x : ℝ, (legendreP n).eval x = 0 → ∃ i : Fin n, τ i = x := by
      rw [hτeq]; exact hall₀
    have hτ_le_last : ∀ i : Fin n, τ i ≤ τ_last := fun i =>
      hmono.monotone (show i ≤ ⟨n - 1, by omega⟩ from Nat.le_sub_one_of_lt i.isLt)
    have hlast_lt1 : τ_last < 1 := by
      have := (hIoo₀ ⟨n - 1, by omega⟩).2
      rwa [← hτeq] at this
    -- Step 1: 1 - τ_last < 3 / N via IVT on [1 - 3/N, 1]
    have hupper : 1 - τ_last < 3 / N := by
      have hneg := legendreP_neg_on_Icc hn3 (u := 3 / 2) (le_refl _) (by norm_num)
      have harg : (1 : ℝ) - 2 * (3 / 2) / N = 1 - 3 / N := by ring
      rw [harg] at hneg
      have hpos1 : 0 < (legendreP n).eval 1 := by rw [legendreP_eval_one]; norm_num
      have h0mem : (0 : ℝ) ∈ Set.Icc ((legendreP n).eval (1 - 3 / N)) ((legendreP n).eval 1) :=
        ⟨le_of_lt hneg, le_of_lt hpos1⟩
      obtain ⟨c, hcI, hc0⟩ := intermediate_value_Icc (by linarith [div_pos (by norm_num : (0:ℝ) < 3) hNpos])
        (legendreP n).continuous.continuousOn h0mem
      obtain ⟨i, hi⟩ := hall c hc0
      have hcle : c ≤ τ_last := hi ▸ hτ_le_last i
      have hcgt : 1 - 3 / N < c := lt_of_le_of_ne hcI.1 (fun h => by rw [← h] at hc0; linarith)
      linarith
    -- Step 2: 10 / N < 1 - τ_prev (no root besides τ_last lies in [1 - 10/N, 1])
    have hlower : 10 / N < 1 - τ_prev := by
      by_contra hnot
      push Not at hnot
      -- So 1 - 10/N ≤ τ_prev < τ_last < 1.
      by_cases hmid : τ_prev ≤ 1 - 3 / N
      · -- Then u = N * (1 - τ_prev) / 2 ∈ [3/2, 5], contradicting legendreP_neg_on_Icc!
        set u := N * (1 - τ_prev) / 2
        have hu_lo : 3 / 2 ≤ u := by
          dsimp only [u]
          have : 3 / N ≤ 1 - τ_prev := by linarith
          have : 3 ≤ N * (1 - τ_prev) := by
            have := mul_le_mul_of_nonneg_left this (le_of_lt hNpos)
            rwa [mul_div_cancel₀ _ (ne_of_gt hNpos)] at this
          linarith
        have hu_hi : u ≤ 5 := by
          dsimp only [u]
          have : N * (1 - τ_prev) ≤ 10 := by
            have := mul_le_mul_of_nonneg_left hnot (le_of_lt hNpos)
            rwa [mul_div_cancel₀ _ (ne_of_gt hNpos)] at this
          linarith
        have hneg := legendreP_neg_on_Icc hn3 hu_lo hu_hi
        have harg : 1 - 2 * u / N = τ_prev := by
          dsimp only [u]; field_simp [ne_of_gt hNpos]; ring
        rw [harg, hroots ⟨n - 2, by omega⟩] at hneg
        linarith
      · -- Otherwise 1 - 3/N < τ_prev < τ_last < 1, so by Rolle's theorem ∃ ξ ∈ (τ_prev, τ_last)
        -- with P_n'(ξ) = 0, contradicting legendreP_deriv_pos_on_Icc on [1 - 6/N, 1]!
        push Not at hmid
        obtain ⟨ξ, hξI, hξderiv⟩ := exists_deriv_eq_zero (f := fun t => (legendreP n).eval t)
          hlt_nodes (legendreP n).continuous.continuousOn
          (by rw [hroots ⟨n - 2, by omega⟩, hroots ⟨n - 1, by omega⟩])
        have hξ0 : (legendreP n).derivative.eval ξ = 0 := by
          have hd := ((legendreP n).hasDerivAt ξ).deriv
          rw [hd] at hξderiv
          exact hξderiv
        set u := N * (1 - ξ) / 2
        have hu0 : 0 ≤ u := by
          dsimp only [u]
          have : ξ < 1 := lt_trans hξI.2 hlast_lt1
          nlinarith
        have hu3 : u ≤ 3 := by
          dsimp only [u]
          have h1 : 1 - ξ < 3 / N := by linarith [hξI.1]
          have h2 : N * (1 - ξ) < 3 := by
            have := mul_lt_mul_of_pos_left h1 hNpos
            rwa [mul_div_cancel₀ _ (ne_of_gt hNpos)] at this
          linarith
        have hpos := legendreP_deriv_pos_on_Icc hn3 hu0 hu3
        have harg : 1 - 2 * u / N = ξ := by
          dsimp only [u]; field_simp [ne_of_gt hNpos]; ring
        rw [harg, hξ0] at hpos
        linarith
    have h9lt10 : 3 * (3 / N) < 10 / N := by
      rw [show (3 : ℝ) * (3 / N) = 9 / N by ring]
      exact div_lt_div_of_pos_right (by norm_num) hNpos
    linarith

end Part2RootGap

section Part3EnergyAndChallenge

/-- Legendre expansion of the Gauss-Legendre Lagrange basis polynomial `ℓ_j`:
`ℓ_j = ∑_{k=0}^{n-1} ((2k + 1)/2) w_j P_k(τ_j) P_k`. -/
lemma gauss_lagBasis_legendre_expansion {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ}
    (hτ : Function.Injective τ) (hroots : ∀ i : Fin n, (legendreP n).eval (τ i) = 0) (j : Fin n) :
    lagBasis τ j =
      ∑ k ∈ Finset.range n,
        C (((2 * k + 1 : ℕ) : ℝ) / 2 * quadWeight τ j * (legendreP k).eval (τ j)) * legendreP k := by
  let S : Polynomial ℝ :=
    ∑ k ∈ Finset.range n,
      C (((2 * k + 1 : ℕ) : ℝ) / 2 * quadWeight τ j * (legendreP k).eval (τ j)) * legendreP k
  let D : Polynomial ℝ := lagBasis τ j - S
  suffices hD : D = 0 by exact sub_eq_zero.mp hD
  have hSdeg : S.natDegree ≤ n - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    have hkn : k < n := Finset.mem_range.mp hk
    calc (C _ * legendreP k).natDegree ≤ (C _).natDegree + (legendreP k).natDegree := natDegree_mul_le
      _ = k := by rw [natDegree_C, zero_add, legendreP_natDegree]
      _ ≤ n - 1 := by omega
  have hDdeg : D.natDegree ≤ n - 1 := by
    have := natDegree_sub_le_of_le (lagBasis_natDegree_le hn hτ j) hSdeg
    simpa [D] using this
  have hDorth : ∀ m < n, ∫ t in (-1 : ℝ)..1, D.eval t * (legendreP m).eval t = 0 := by
    intro m hm
    have h1 : ∫ t in (-1 : ℝ)..1, (lagBasis τ j).eval t * (legendreP m).eval t =
        quadWeight τ j * (legendreP m).eval (τ j) := by
      have hdeg_prod : (lagBasis τ j * legendreP m).natDegree < n + n := by
        calc (lagBasis τ j * legendreP m).natDegree
            ≤ (lagBasis τ j).natDegree + (legendreP m).natDegree := natDegree_mul_le
          _ ≤ (n - 1) + m := Nat.add_le_add (lagBasis_natDegree_le hn hτ j) (le_of_eq (legendreP_natDegree m))
          _ < n + n := by omega
      have hq := quad_exact_of_orthog hn hτ (legendreP_natDegree n) hroots
        (fun q hq => legendreP_orthog_lt hq) hdeg_prod
      have hconv : ∫ t in (-1 : ℝ)..1, (lagBasis τ j).eval t * (legendreP m).eval t =
          ∫ t in (-1 : ℝ)..1, (lagBasis τ j * legendreP m).eval t :=
        intervalIntegral.integral_congr fun t _ => (eval_mul).symm
      rw [hconv, hq, Finset.sum_eq_single j]
      · rw [eval_mul, lagBasis_eval_self hτ j, one_mul]
      · intro k _ hkj; rw [eval_mul, lagBasis_eval_of_ne hkj, zero_mul, mul_zero]
      · intro hnot; exact absurd (Finset.mem_univ j) hnot
    have h2 : ∫ t in (-1 : ℝ)..1, S.eval t * (legendreP m).eval t =
        quadWeight τ j * (legendreP m).eval (τ j) := by
      have hfn : ∀ t : ℝ, S.eval t * (legendreP m).eval t =
          ∑ k ∈ Finset.range n,
            (((2 * k + 1 : ℕ) : ℝ) / 2 * quadWeight τ j * (legendreP k).eval (τ j)) *
              ((legendreP k).eval t * (legendreP m).eval t) := by
        intro t
        simp only [S, eval_finsetSum, eval_mul, eval_C, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [intervalIntegral.integral_congr (fun t _ => hfn t)]
      rw [intervalIntegral.integral_finsetSum (fun k _ =>
            Continuous.intervalIntegrable (by fun_prop) _ _)]
      rw [Finset.sum_eq_single m]
      · rw [intervalIntegral.integral_const_mul]
        have hsq : ∫ t in (-1 : ℝ)..1, (legendreP m).eval t * (legendreP m).eval t =
            2 / ((2 * m + 1 : ℕ) : ℝ) := by
          rw [← legendreP_integral_sq m]
          exact intervalIntegral.integral_congr fun t _ => (sq _).symm
        rw [hsq]
        have hpos : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hpos]
      · intro k _ hkm
        rw [intervalIntegral.integral_const_mul, legendreP_orthog hkm, mul_zero]
      · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
    have hsplit : ∀ t : ℝ, D.eval t * (legendreP m).eval t =
        (lagBasis τ j).eval t * (legendreP m).eval t - S.eval t * (legendreP m).eval t := fun t => by
      simp only [D, eval_sub]; ring
    rw [intervalIntegral.integral_congr (fun t _ => hsplit t),
        intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        h1, h2, sub_self]
  -- Hence ∫_{-1}^1 D^2 = 0, so D = 0!
  obtain ⟨α, hα⟩ := poly_eq_sum_legendreP D
  have hint0 : ∫ t in (-1 : ℝ)..1, (D.eval t) ^ 2 = 0 := by
    have hfn : ∀ t : ℝ, (D.eval t) ^ 2 =
        ∑ k ∈ Finset.range (D.natDegree + 1), α k * (D.eval t * (legendreP k).eval t) := by
      intro t
      rw [sq]
      conv_lhs => arg 2; rw [hα]
      simp only [eval_finsetSum, eval_mul, eval_C, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [intervalIntegral.integral_congr (fun t _ => hfn t)]
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
          Continuous.intervalIntegrable (by fun_prop) _ _)]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := by have := Finset.mem_range.mp hk; omega
    rw [intervalIntegral.integral_const_mul, hDorth k hkn, mul_zero]
  exact poly_eq_zero_of_integral_sq_eq_zero hint0

/-- Explicit Gauss-Legendre weight formula: `w_j = 2 / ((1 - τ_j^2) P_n'(τ_j)^2)`. -/
theorem gauss_quadWeight_eq {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ}
    (hτ : Function.Injective τ) (hroots : ∀ i : Fin n, (legendreP n).eval (τ i) = 0) (j : Fin n) :
    quadWeight τ j * ((1 - (τ j) ^ 2) * ((legendreP n).derivative.eval (τ j)) ^ 2) = 2 := by
  have hexp := congr_arg (fun p => p.eval (τ j)) (gauss_lagBasis_legendre_expansion hn hτ hroots j)
  rw [lagBasis_eval_self hτ j, eval_finsetSum] at hexp
  have hsum : ∑ k ∈ Finset.range n,
      (C (((2 * k + 1 : ℕ) : ℝ) / 2 * quadWeight τ j * (legendreP k).eval (τ j)) * legendreP k).eval (τ j) =
      quadWeight τ j * ∑ k ∈ Finset.range n, ((2 * k + 1 : ℕ) : ℝ) / 2 * ((legendreP k).eval (τ j)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [eval_mul, eval_C]; ring
  rw [hsum, christoffel_darboux_root n hn (hroots j)] at hexp
  linarith

/-- Exact diagonal identity for the Gauss-Legendre integration matrix: `A_{ii} = w_i / 2`. -/
theorem gauss_intMatA_diag {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ}
    (hτ : Function.Injective τ) (hroots : ∀ i : Fin n, (legendreP n).eval (τ i) = 0) (i : Fin n) :
    intMatA τ i i = quadWeight τ i / 2 := by
  have hexp := gauss_lagBasis_legendre_expansion hn hτ hroots i
  unfold intMatA
  have hfn : ∀ t : ℝ, (lagBasis τ i).eval t =
      ∑ k ∈ Finset.range n,
        (((2 * k + 1 : ℕ) : ℝ) / 2 * quadWeight τ i * (legendreP k).eval (τ i)) *
          (legendreP k).eval t := by
    intro t
    conv_lhs => rw [hexp]
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => by simp only [eval_mul, eval_C]
  rw [intervalIntegral.integral_congr (fun t _ => hfn t)]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
        Continuous.intervalIntegrable (by fun_prop) _ _)]
  -- Split off k = 0 from range n (since n ≥ 1)
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have hn_eq : n = m + 1 := by omega
  have hrange_eq : Finset.range n = Finset.range (m + 1) := congr_arg Finset.range hn_eq
  rw [hrange_eq, Finset.sum_range_succ']
  have hk0 : ∫ t in (-1 : ℝ)..(τ i),
      (((2 * 0 + 1 : ℕ) : ℝ) / 2 * quadWeight τ i * (legendreP 0).eval (τ i)) *
        (legendreP 0).eval t =
      quadWeight τ i * ((1 + (legendreP 1).eval (τ i)) / 2) := by
    simp only [legendreP_zero, legendreP_one, eval_one, eval_X, Nat.mul_zero, zero_add,
      Nat.cast_one, mul_one]
    rw [intervalIntegral.integral_const]
    simp; ring
  have hk_ge1 : ∀ k ∈ Finset.range m,
      ∫ t in (-1 : ℝ)..(τ i),
        (((2 * (k + 1) + 1 : ℕ) : ℝ) / 2 * quadWeight τ i * (legendreP (k + 1)).eval (τ i)) *
          (legendreP (k + 1)).eval t =
      quadWeight τ i / 2 *
        ((legendreP (k + 1)).eval (τ i) * (legendreP (k + 2)).eval (τ i) -
          (legendreP k).eval (τ i) * (legendreP (k + 1)).eval (τ i)) := by
    intro k _
    rw [intervalIntegral.integral_const_mul]
    have hant := legendreP_antideriv (k + 1) (by omega)
    set F : Polynomial ℝ := legendreP (k + 2) - legendreP k
    have hFd : ∀ t : ℝ, F.derivative.eval t =
        ((2 * (k + 1) + 1 : ℕ) : ℝ) * (legendreP (k + 1)).eval t := fun t => by
      have hv := congr_arg (fun p => p.eval t) hant
      simp only [F, derivative_sub, eval_sub, eval_mul, eval_C, Nat.add_sub_cancel] at hv ⊢
      exact hv
    have hftc : ∫ t in (-1 : ℝ)..(τ i), F.derivative.eval t = F.eval (τ i) - F.eval (-1) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => F.hasDerivAt t)
        (F.derivative.continuous.intervalIntegrable _ _)
    have hFm1 : F.eval (-1) = 0 := by
      simp only [F, eval_sub, legendreP_eval_neg_one, pow_add]; norm_num
    rw [hFm1, sub_zero] at hftc
    have hint_P : ((2 * (k + 1) + 1 : ℕ) : ℝ) * ∫ t in (-1 : ℝ)..(τ i), (legendreP (k + 1)).eval t =
        (legendreP (k + 2)).eval (τ i) - (legendreP k).eval (τ i) := by
      rw [← intervalIntegral.integral_const_mul]
      have : ∫ t in (-1 : ℝ)..(τ i), ((2 * (k + 1) + 1 : ℕ) : ℝ) * (legendreP (k + 1)).eval t =
          ∫ t in (-1 : ℝ)..(τ i), F.derivative.eval t :=
        intervalIntegral.integral_congr fun t _ => (hFd t).symm
      rw [this, hftc]
      simp [F]
    calc
      (((2 * (k + 1) + 1 : ℕ) : ℝ) / 2 * quadWeight τ i * (legendreP (k + 1)).eval (τ i)) *
          ∫ t in (-1 : ℝ)..(τ i), (legendreP (k + 1)).eval t
        = quadWeight τ i / 2 * (legendreP (k + 1)).eval (τ i) *
            (((2 * (k + 1) + 1 : ℕ) : ℝ) * ∫ t in (-1 : ℝ)..(τ i), (legendreP (k + 1)).eval t) := by
            ring
      _ = quadWeight τ i / 2 * (legendreP (k + 1)).eval (τ i) *
            ((legendreP (k + 2)).eval (τ i) - (legendreP k).eval (τ i)) := by rw [hint_P]
      _ = _ := by ring
  rw [hk0, Finset.sum_congr rfl hk_ge1, ← Finset.mul_sum]
  -- Telescope ∑_{k < m} (g (k+1) - g k) = g m - g 0 where g k = P_k(τ_i) * P_{k+1}(τ_i)!
  let g : ℕ → ℝ := fun k => (legendreP k).eval (τ i) * (legendreP (k + 1)).eval (τ i)
  have htele : ∑ k ∈ Finset.range m,
      ((legendreP (k + 1)).eval (τ i) * (legendreP (k + 2)).eval (τ i) -
        (legendreP k).eval (τ i) * (legendreP (k + 1)).eval (τ i)) = g m - g 0 := by
    exact Finset.sum_range_sub g m
  rw [htele]
  dsimp only [g]
  have hm1 : m + 1 = n := by omega
  rw [hm1, hroots i, mul_zero, legendreP_zero, eval_one, one_mul]
  ring

/-- Explicit formula for the Lagrange basis polynomial at Gauss-Legendre nodes:
`P_n = P_n'(τ_j) * (X - τ_j) * ℓ_j`. -/
lemma gauss_lagBasis_mul_eq {n : ℕ} (_hn : 1 ≤ n) {τ : Fin n → ℝ}
    (hτ : Function.Injective τ) (hroots : ∀ i : Fin n, (legendreP n).eval (τ i) = 0) (j : Fin n) :
    legendreP n = C ((legendreP n).derivative.eval (τ j)) * (X - C (τ j)) * lagBasis τ j := by
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr (hroots j)
  have hQne : Q ≠ 0 := by intro h0; rw [h0, mul_zero] at hQ; exact legendreP_ne_zero n hQ
  have hQdeg : Q.natDegree < n := by
    have hm := natDegree_mul (X_sub_C_ne_zero (τ j)) hQne
    rw [← hQ, legendreP_natDegree, natDegree_X_sub_C] at hm
    omega
  have hQself : Q.eval (τ j) = (legendreP n).derivative.eval (τ j) := by
    have hd := congr_arg Polynomial.derivative hQ
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at hd
    have hev := congr_arg (fun p => p.eval (τ j)) hd
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at hev
    exact hev.symm
  have hQother : ∀ k : Fin n, k ≠ j → Q.eval (τ k) = 0 := by
    intro k hkj
    have hv := congr_arg (fun p => p.eval (τ k)) hQ
    simp only [hroots k, eval_mul, eval_sub, eval_X, eval_C] at hv
    have hne : τ k - τ j ≠ 0 := sub_ne_zero.mpr fun h => hkj (hτ h)
    exact (mul_eq_zero.mp hv.symm).resolve_left hne
  have hQlag := poly_eq_lagrange_sum hτ hQdeg
  rw [Finset.sum_eq_single j] at hQlag
  · rw [hQself] at hQlag
    conv_lhs => rw [hQ, hQlag]
    ring
  · intro k _ hkj; rw [hQother k hkj, C_0, zero_mul]
  · intro hnot; exact absurd (Finset.mem_univ j) hnot

/-- **Legendre ODE Energy Bound:** For all `n` and all `t ∈ [-1, 1]`,
`(1 - t^2) P_n'(t)^2 + n(n+1) P_n(t)^2 ≤ n(n+1)`. -/
theorem legendreP_energy_le (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (1 - t ^ 2) * ((legendreP n).derivative.eval t) ^ 2 +
      (n : ℝ) * ((n : ℝ) + 1) * ((legendreP n).eval t) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by
  let N : ℝ := (n : ℝ) * ((n : ℝ) + 1)
  let E : Polynomial ℝ :=
    (1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative ^ 2 + C N * (legendreP n) ^ 2
  have hEd : E.derivative = C (2 : ℝ) * X * (legendreP n).derivative ^ 2 := by
    have hode := legendreP_ode n
    have hode_exp : (-C (2 : ℝ) * X) * (legendreP n).derivative +
        (1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative.derivative +
        C N * legendreP n = 0 := by
      have hd1 : ((1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative).derivative =
          (-C (2 : ℝ) * X) * (legendreP n).derivative +
            (1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative.derivative := by
        rw [derivative_mul, derivative_sub, derivative_one, derivative_pow, derivative_X]
        simp only [zero_sub, Nat.cast_ofNat, mul_one]
        ring
      rw [← hd1]
      exact hode
    have hmul_ode : (1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative.derivative =
        C (2 : ℝ) * X * (legendreP n).derivative - C N * legendreP n := by
      linear_combination hode_exp
    have hdE : E.derivative =
        (-C (2 : ℝ) * X) * (legendreP n).derivative ^ 2 +
          (1 - X ^ 2 : Polynomial ℝ) * (C (2 : ℝ) * (legendreP n).derivative * (legendreP n).derivative.derivative) +
          C N * (C (2 : ℝ) * legendreP n * (legendreP n).derivative) := by
      dsimp only [E]
      rw [derivative_add, derivative_mul, derivative_C_mul, derivative_sub, derivative_one,
          derivative_pow, derivative_pow, derivative_pow, derivative_X]
      simp only [zero_sub, Nat.cast_ofNat, mul_one]
      ring
    rw [hdE]
    have hC2 : (C (2 : ℝ) : Polynomial ℝ) = 2 := map_ofNat C 2
    calc
      (-C (2 : ℝ) * X) * (legendreP n).derivative ^ 2 +
          (1 - X ^ 2 : Polynomial ℝ) *
            (C (2 : ℝ) * (legendreP n).derivative * (legendreP n).derivative.derivative) +
          C N * (C (2 : ℝ) * legendreP n * (legendreP n).derivative)
        = (-C (2 : ℝ) * X) * (legendreP n).derivative ^ 2 +
            C (2 : ℝ) * (legendreP n).derivative *
              ((1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative.derivative) +
            C N * (C (2 : ℝ) * legendreP n * (legendreP n).derivative) := by ring
      _ = (-C (2 : ℝ) * X) * (legendreP n).derivative ^ 2 +
            C (2 : ℝ) * (legendreP n).derivative *
              (C (2 : ℝ) * X * (legendreP n).derivative - C N * legendreP n) +
            C N * (C (2 : ℝ) * legendreP n * (legendreP n).derivative) := by rw [hmul_ode]
      _ = C (2 : ℝ) * X * (legendreP n).derivative ^ 2 := by rw [hC2]; ring
  have hE1 : E.eval 1 = N := by
    simp [E, legendreP_eval_one]
  have hEm1 : E.eval (-1) = N := by
    simp [E, legendreP_eval_neg_one]
    have : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this, mul_one]
  suffices hE : E.eval t ≤ N by
    simpa [E, N] using hE
  rcases le_total 0 t with ht0 | ht0
  · -- On [0, 1]: E' = 2 x P'^2 ≥ 0, so E(t) ≤ E(1) = N
    have hmono : MonotoneOn (fun x => E.eval x) (Set.Icc (0 : ℝ) 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) E.continuous.continuousOn
        (fun x _ => E.differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [(E.hasDerivAt x).deriv, hEd]
      simp only [eval_mul, eval_C, eval_X, eval_pow]
      have hx0 : 0 ≤ x := (interior_subset hx).1
      positivity
    calc E.eval t ≤ E.eval 1 := hmono ⟨ht0, ht.2⟩ ⟨by norm_num, le_refl 1⟩ ht.2
      _ = N := hE1
  · -- On [-1, 0]: E' = 2 x P'^2 ≤ 0, so E(t) ≤ E(-1) = N
    have hanti : AntitoneOn (fun x => E.eval x) (Set.Icc (-1 : ℝ) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc (-1) 0) E.continuous.continuousOn
        (fun x _ => E.differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [(E.hasDerivAt x).deriv, hEd]
      simp only [eval_mul, eval_C, eval_X, eval_pow]
      have hx0 : x ≤ 0 := (interior_subset hx).2
      have hsq : 0 ≤ ((legendreP n).derivative.eval x) ^ 2 := sq_nonneg _
      nlinarith
    calc E.eval t ≤ E.eval (-1) := hanti ⟨le_refl (-1), by norm_num⟩ ⟨ht.1, ht0⟩ ht.1
      _ = N := hEm1

/-- **Part 3 Main Theorem (Last Row Nonnegativity):** For all `n ≥ 1`, every entry `A_{n,j}` in
the last row (`i = n - 1`) of the Gauss-Legendre integration matrix is nonnegative! -/
theorem gauss_intMatA_last_nonneg {n : ℕ} (hn : 1 ≤ n) {τ : Fin n → ℝ}
    (hmono : StrictMono τ) (hroots : ∀ i : Fin n, (legendreP n).eval (τ i) = 0) :
    ∀ j : Fin n, 0 ≤ intMatA τ ⟨n - 1, by omega⟩ j := by
  let last : Fin n := ⟨n - 1, by omega⟩
  -- Deduce full root properties via roots_of_orthog_weight
  obtain ⟨τ₀, hmono₀, hIoo₀, hroots₀, hall₀, hderiv₀⟩ := roots_of_orthog_weight
    (d := n) (P := legendreP n) (w := fun _ => 1)
    continuous_const (fun _ _ => zero_lt_one) (fun _ _ => zero_le_one)
    (legendreP_ne_zero n) (legendreP_natDegree n)
    (fun q hq => by simpa using legendreP_orthog_lt hq)
  have hτeq : τ = τ₀ := roots_enum_unique hmono hmono₀ hroots hall₀
  have hIoo : ∀ i : Fin n, -1 < τ i ∧ τ i < 1 := by rw [hτeq]; exact hIoo₀
  have hall : ∀ x : ℝ, (legendreP n).eval x = 0 → ∃ i : Fin n, τ i = x := by rw [hτeq]; exact hall₀
  have hderiv_ne : ∀ i : Fin n, (legendreP n).derivative.eval (τ i) ≠ 0 := by
    rw [hτeq]; exact hderiv₀
  have hτ_le_last : ∀ i : Fin n, τ i ≤ τ last := fun i =>
    hmono.monotone (show i ≤ last from Nat.le_sub_one_of_lt i.isLt)
  have hexact : ∀ f : Polynomial ℝ, f.natDegree ≤ 2 * (n - 1) →
      ∫ t in (-1 : ℝ)..1, f.eval t = ∑ j : Fin n, quadWeight τ j * f.eval (τ j) := fun f hf =>
    quad_exact_of_orthog hn hmono.injective (legendreP_natDegree n) hroots
      (fun q hq => legendreP_orthog_lt hq) (by omega)
  -- P_n(t) > 0 on (τ_last, 1] and P_n(t) ≥ 0 on [τ_last, 1]
  have hPn_pos_on : ∀ t ∈ Set.Ioc (τ last) 1, 0 < (legendreP n).eval t := by
    intro t ht
    by_contra hle
    push Not at hle
    have hpos1 : 0 < (legendreP n).eval 1 := by rw [legendreP_eval_one]; norm_num
    have h0mem : (0 : ℝ) ∈ Set.Icc ((legendreP n).eval t) ((legendreP n).eval 1) := ⟨hle, le_of_lt hpos1⟩
    obtain ⟨c, hcI, hc0⟩ := intermediate_value_Icc ht.2 (legendreP n).continuous.continuousOn h0mem
    obtain ⟨k, hk⟩ := hall c hc0
    have := hτ_le_last k
    linarith [ht.1, hcI.1, hk]
  have hPn_nn_on : ∀ t ∈ Set.Icc (τ last) 1, 0 ≤ (legendreP n).eval t := fun t ht => by
    by_cases hteq : t = τ last
    · rw [hteq, hroots last]
    · exact le_of_lt (hPn_pos_on t ⟨lt_of_le_of_ne ht.1 (Ne.symm hteq), ht.2⟩)
  -- Integral of P_n on [τ_last, 1] from Legendre ODE: N * ∫_{τ_last}^1 P_n = (1 - τ_last^2) P_n'(τ_last)
  set N : ℝ := (n : ℝ) * ((n : ℝ) + 1)
  have hNpos : 0 < N := by positivity
  have hint_Pn : N * ∫ t in (τ last)..1, (legendreP n).eval t =
      (1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last) := by
    set F : Polynomial ℝ := (1 - X ^ 2 : Polynomial ℝ) * (legendreP n).derivative
    have hftc : ∫ t in (τ last)..1, F.derivative.eval t = F.eval 1 - F.eval (τ last) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => F.hasDerivAt t)
        (F.derivative.continuous.intervalIntegrable _ _)
    have hFd : ∀ t : ℝ, F.derivative.eval t = -(N * (legendreP n).eval t) := fun t => by
      have h := legendreP_ode_eval n t
      dsimp only [F, N]; linarith
    rw [intervalIntegral.integral_congr (fun t _ => hFd t), intervalIntegral.integral_neg,
        intervalIntegral.integral_const_mul] at hftc
    have hF1 : F.eval 1 = 0 := by simp [F]
    rw [hF1, zero_sub] at hftc
    simp only [F, eval_mul, eval_sub, eval_one, eval_pow, eval_X] at hftc
    linarith
  have hint_Pn_pos : 0 < ∫ t in (τ last)..1, (legendreP n).eval t := by
    have hge : 0 ≤ ∫ t in (τ last)..1, (legendreP n).eval t :=
      intervalIntegral.integral_nonneg (le_of_lt (hIoo last).2) hPn_nn_on
    refine lt_of_le_of_ne hge fun h0 => ?_
    have : (1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last) = 0 := by
      rw [← hint_Pn, ← h0, mul_zero]
    rcases mul_eq_zero.mp this with h1 | h2
    · have : 0 < 1 - (τ last) ^ 2 := by nlinarith [(hIoo last).1, (hIoo last).2]
      linarith
    · exact hderiv_ne last h2
  have hdp_last_pos : 0 < (legendreP n).derivative.eval (τ last) := by
    have h1m : 0 < 1 - (τ last) ^ 2 := by nlinarith [(hIoo last).1, (hIoo last).2]
    have hprod : 0 < (1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last) := by
      rw [← hint_Pn]; exact mul_pos hNpos hint_Pn_pos
    nlinarith
  -- Now prove 0 ≤ intMatA τ last j for every j : Fin n!
  intro j
  by_cases hjl : j = last
  · subst hjl
    rw [gauss_intMatA_diag hn hmono.injective hroots last]
    exact div_nonneg (le_of_lt (quadWeight_pos hn hmono.injective hexact last)) (by norm_num)
  · -- j < last, so n ≥ 2 and τ_j < τ_last!
    have hj_lt_last : j < last := lt_of_le_of_ne (Nat.le_sub_one_of_lt j.isLt) hjl
    have hτj_lt : τ j < τ last := hmono hj_lt_last
    have hwj_pos : 0 < quadWeight τ j := quadWeight_pos hn hmono.injective hexact j
    have hAB : intMatA τ last j = quadWeight τ j - intMatB τ last j := by
      linarith [intMatA_add_intMatB τ last j]
    -- Explicit evaluation of ℓ_j(t) on [τ_last, 1]: ℓ_j(t) = P_n(t) / ((t - τ_j) * P_n'(τ_j))
    have hlag_eval : ∀ t ∈ Set.Icc (τ last) 1,
        (lagBasis τ j).eval t =
          (legendreP n).eval t / ((t - τ j) * (legendreP n).derivative.eval (τ j)) := by
      intro t ht
      have hv := congr_arg (fun p => p.eval t) (gauss_lagBasis_mul_eq hn hmono.injective hroots j)
      simp only [eval_mul, eval_C, eval_sub, eval_X] at hv
      have hden : (t - τ j) * (legendreP n).derivative.eval (τ j) ≠ 0 :=
        mul_ne_zero (by linarith [ht.1]) (hderiv_ne j)
      rw [eq_div_iff hden]
      linarith [hv]
    rcases lt_or_gt_of_ne (hderiv_ne j) with hdp_neg | hdp_pos
    · -- Subcase 2a: P_n'(τ_j) < 0 ⇒ ℓ_j(t) ≤ 0 on [τ_last, 1] ⇒ B_{nj} ≤ 0 ⇒ A_{nj} ≥ w_j > 0!
      have hB_le0 : intMatB τ last j ≤ 0 := by
        unfold intMatB
        rw [← neg_nonneg, ← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_nonneg (le_of_lt (hIoo last).2) fun t ht => ?_
        rw [hlag_eval t ht, neg_nonneg]
        exact div_nonpos_of_nonneg_of_nonpos (hPn_nn_on t ht)
          (mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.1]) (le_of_lt hdp_neg))
      linarith
    · -- Subcase 2b: P_n'(τ_j) > 0 ⇒ B_{nj} < w_j via Legendre energy bound + Part 2 root gap!
      have hB_le : intMatB τ last j ≤
          (1 / ((τ last - τ j) * (legendreP n).derivative.eval (τ j))) *
            ∫ t in (τ last)..1, (legendreP n).eval t := by
        unfold intMatB
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on (le_of_lt (hIoo last).2)
          ((lagBasis τ j).continuous.intervalIntegrable _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _) fun t ht => ?_
        rw [hlag_eval t ht, one_div, inv_mul_eq_div]
        have hden1 : 0 < (τ last - τ j) * (legendreP n).derivative.eval (τ j) :=
          mul_pos (by linarith) hdp_pos
        have hden_le : (τ last - τ j) * (legendreP n).derivative.eval (τ j) ≤
            (t - τ j) * (legendreP n).derivative.eval (τ j) :=
          mul_le_mul_of_nonneg_right (by linarith [ht.1]) (le_of_lt hdp_pos)
        exact div_le_div_of_nonneg_left (hPn_nn_on t ht) hden1 hden_le
      -- Substitute ∫ P_n = (1 - τ_last^2) P_n'(τ_last) / N and w_j = 2 / ((1 - τ_j^2) P_n'(τ_j)^2)
      have hB_le2 : intMatB τ last j * (2 * N * (τ last - τ j)) ≤
          quadWeight τ j *
            (((1 - (τ j) ^ 2) * (legendreP n).derivative.eval (τ j)) *
              ((1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last))) := by
        have hwj_eq := gauss_quadWeight_eq hn hmono.injective hroots j
        have hden_pos : 0 < (τ last - τ j) * (legendreP n).derivative.eval (τ j) :=
          mul_pos (by linarith) hdp_pos
        have h1 : intMatB τ last j * ((τ last - τ j) * (legendreP n).derivative.eval (τ j)) ≤
            ∫ t in (τ last)..1, (legendreP n).eval t := by
          have := mul_le_mul_of_nonneg_right hB_le (le_of_lt hden_pos)
          have hcancel : 1 / ((τ last - τ j) * (legendreP n).derivative.eval (τ j)) *
              (∫ t in (τ last)..1, (legendreP n).eval t) *
              ((τ last - τ j) * (legendreP n).derivative.eval (τ j)) =
              ∫ t in (τ last)..1, (legendreP n).eval t := by
            rw [one_div, inv_mul_eq_div, div_mul_cancel₀ _ (ne_of_gt hden_pos)]
          linarith
        have h2 : intMatB τ last j * (N * (τ last - τ j) * (legendreP n).derivative.eval (τ j)) ≤
            (1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last) := by
          rw [← hint_Pn]
          have := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
          linarith
        have h1mj : 0 < 1 - (τ j) ^ 2 := by nlinarith [(hIoo j).1, (hIoo j).2]
        have hfac_pos : 0 < quadWeight τ j * ((1 - (τ j) ^ 2) * (legendreP n).derivative.eval (τ j)) :=
          mul_pos hwj_pos (mul_pos h1mj hdp_pos)
        have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt hfac_pos)
        -- LHS of h3 = B_{nj} * N * (τ_last - τ_j) * [w_j * (1 - τ_j^2) * P_n'(τ_j)^2] = B_{nj} * 2 * N * (τ_last - τ_j)!
        have hlhs_eq : (quadWeight τ j * ((1 - (τ j) ^ 2) * (legendreP n).derivative.eval (τ j))) *
            (intMatB τ last j * (N * (τ last - τ j) * (legendreP n).derivative.eval (τ j))) =
            intMatB τ last j * (2 * N * (τ last - τ j)) := by
          calc
            _ = intMatB τ last j * (N * (τ last - τ j)) *
                  (quadWeight τ j * ((1 - (τ j) ^ 2) * ((legendreP n).derivative.eval (τ j)) ^ 2)) := by
                ring
            _ = intMatB τ last j * (N * (τ last - τ j)) * 2 := by rw [hwj_eq]
            _ = intMatB τ last j * (2 * N * (τ last - τ j)) := by ring
        have hrhs_eq : (quadWeight τ j * ((1 - (τ j) ^ 2) * (legendreP n).derivative.eval (τ j))) *
            ((1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last)) =
            quadWeight τ j *
              (((1 - (τ j) ^ 2) * (legendreP n).derivative.eval (τ j)) *
                ((1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last))) := by ring
        linarith
      -- Energy bound at τ_j and τ_last + Part 2 root gap:
      have hn2 : 2 ≤ n := by have := j.isLt; have : j.val < n - 1 := hj_lt_last; omega
      have hgap := legendreP_root_gap hn2 hmono hroots
      set sj := 1 - τ j
      set sn := 1 - τ last
      have hsn_pos : 0 < sn := by dsimp only [sn]; linarith [(hIoo last).2]
      have hsj_gt : 3 * sn < sj := by
        have hjle : j ≤ ⟨n - 2, by omega⟩ := by
          change j.val ≤ n - 2
          have : j.val < n - 1 := hj_lt_last
          omega
        have hτle : τ j ≤ τ ⟨n - 2, by omega⟩ := hmono.monotone hjle
        dsimp only [sj, sn]
        linarith
      have hEj : (1 - (τ j) ^ 2) * ((legendreP n).derivative.eval (τ j)) ^ 2 ≤ N := by
        have h := legendreP_energy_le n ⟨le_of_lt (hIoo j).1, le_of_lt (hIoo j).2⟩
        rw [hroots j, zero_pow (by norm_num), mul_zero, add_zero] at h
        exact h
      have hEn : (1 - (τ last) ^ 2) * ((legendreP n).derivative.eval (τ last)) ^ 2 ≤ N := by
        have h := legendreP_energy_le n ⟨le_of_lt (hIoo last).1, le_of_lt (hIoo last).2⟩
        rw [hroots last, zero_pow (by norm_num), mul_zero, add_zero] at h
        exact h
      have h1mj : 0 < 1 - (τ j) ^ 2 := by nlinarith [(hIoo j).1, (hIoo j).2]
      have h1mn : 0 < 1 - (τ last) ^ 2 := by nlinarith [(hIoo last).1, (hIoo last).2]
      have hsq_lt : (((1 - (τ j) ^ 2) * (legendreP n).derivative.eval (τ j)) *
          ((1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last))) ^ 2 <
          (2 * N * (τ last - τ j)) ^ 2 := by
        have hprod1 : (((1 - (τ j) ^ 2) * (legendreP n).derivative.eval (τ j)) *
            ((1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last))) ^ 2 =
            (1 - (τ j) ^ 2) * ((1 - (τ j) ^ 2) * ((legendreP n).derivative.eval (τ j)) ^ 2) *
            ((1 - (τ last) ^ 2) * ((1 - (τ last) ^ 2) * ((legendreP n).derivative.eval (τ last)) ^ 2)) := by
          ring
        have hprod2 : (1 - (τ j) ^ 2) * ((1 - (τ j) ^ 2) * ((legendreP n).derivative.eval (τ j)) ^ 2) *
            ((1 - (τ last) ^ 2) * ((1 - (τ last) ^ 2) * ((legendreP n).derivative.eval (τ last)) ^ 2)) ≤
            N ^ 2 * ((1 - (τ j) ^ 2) * (1 - (τ last) ^ 2)) := by
          have ha : (1 - (τ j) ^ 2) * ((1 - (τ j) ^ 2) * ((legendreP n).derivative.eval (τ j)) ^ 2) ≤
              (1 - (τ j) ^ 2) * N := mul_le_mul_of_nonneg_left hEj (le_of_lt h1mj)
          have hb : (1 - (τ last) ^ 2) * ((1 - (τ last) ^ 2) * ((legendreP n).derivative.eval (τ last)) ^ 2) ≤
              (1 - (τ last) ^ 2) * N := mul_le_mul_of_nonneg_left hEn (le_of_lt h1mn)
          have hnn1 : 0 ≤ (1 - (τ j) ^ 2) * ((1 - (τ j) ^ 2) * ((legendreP n).derivative.eval (τ j)) ^ 2) := by
            positivity
          have hnn2 : 0 ≤ (1 - (τ last) ^ 2) * ((1 - (τ last) ^ 2) * ((legendreP n).derivative.eval (τ last)) ^ 2) := by
            positivity
          have hmul := mul_le_mul ha hb hnn2 (mul_nonneg (le_of_lt h1mj) (le_of_lt hNpos))
          linarith
        have h1m_le : (1 - (τ j) ^ 2) * (1 - (τ last) ^ 2) ≤ 4 * sj * sn := by
          have hfj : 1 - (τ j) ^ 2 = (1 + τ j) * sj := by dsimp only [sj]; ring
          have hfn : 1 - (τ last) ^ 2 = (1 + τ last) * sn := by dsimp only [sn]; ring
          rw [hfj, hfn]
          have h1j : 0 ≤ 1 + τ j := by linarith [(hIoo j).1]
          have h2j : 1 + τ j ≤ 2 := by linarith [(hIoo j).2]
          have h1n : 0 ≤ 1 + τ last := by linarith [(hIoo last).1]
          have h2n : 1 + τ last ≤ 2 := by linarith [(hIoo last).2]
          have hsj_pos : 0 < sj := by linarith
          have h12 : (1 + τ j) * (1 + τ last) ≤ 4 := by nlinarith
          have hss : 0 ≤ sj * sn := mul_nonneg (le_of_lt hsj_pos) (le_of_lt hsn_pos)
          have hmul := mul_le_mul_of_nonneg_right h12 hss
          linarith
        have hgap_sq : sj * sn < (sj - sn) ^ 2 := by
          have : (sj - sn) ^ 2 - sj * sn = sj * (sj - 3 * sn) + sn ^ 2 := by ring
          nlinarith [sq_nonneg sn]
        have hdiff : τ last - τ j = sj - sn := by dsimp only [sj, sn]; ring
        rw [hprod1, hdiff]
        have hN2 : 0 < N ^ 2 := sq_pos_of_pos hNpos
        nlinarith
      have hlin_lt : ((1 - (τ j) ^ 2) * (legendreP n).derivative.eval (τ j)) *
          ((1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last)) <
          2 * N * (τ last - τ j) := by
        have hpos_r : 0 < 2 * N * (τ last - τ j) := by nlinarith
        have hpos_l : 0 ≤ ((1 - (τ j) ^ 2) * (legendreP n).derivative.eval (τ j)) *
            ((1 - (τ last) ^ 2) * (legendreP n).derivative.eval (τ last)) :=
          mul_nonneg (mul_nonneg (le_of_lt h1mj) (le_of_lt hdp_pos))
            (mul_nonneg (le_of_lt h1mn) (le_of_lt hdp_last_pos))
        nlinarith
      have hB_lt_w : intMatB τ last j < quadWeight τ j := by
        have hpos_r : 0 < 2 * N * (τ last - τ j) := by nlinarith
        nlinarith [hB_le2, mul_lt_mul_of_pos_left hlin_lt hwj_pos]
      linarith

/-- **Main Challenge Theorem (Hager's Sharper Gauss-Legendre Reverse-Markov Inequality):**
Let `n ≥ 1`, let `P : Polynomial ℝ` be any degree-`n` polynomial orthogonal on `[-1, 1]` to all
polynomials of degree `< n` (i.e. a nonzero scalar multiple of the Legendre polynomial `P_n`),
and let `τ : Fin n → ℝ` be its `n` strictly increasing roots. Then for every polynomial
`p : Polynomial ℝ` of degree `≤ n` with `p(-1) = 0` and `|p'(τ_j)| ≤ 1` for all `j`:
`|p(τ_i)| ≤ 1 + τ_{n-1}` for all `i : Fin n`.

Stated in pure Mathlib with ZERO custom definitions. -/
theorem hager_gauss_legendre_sharp_challenge
    (n : ℕ) (hn : 1 ≤ n)
    (P : Polynomial ℝ) (hPdeg : P.natDegree = n)
    (hPorth : ∀ q : Polynomial ℝ, q.natDegree < n →
      ∫ t in (-1 : ℝ)..1, P.eval t * q.eval t = 0)
    (τ : Fin n → ℝ) (hτmono : StrictMono τ) (hτroots : ∀ i : Fin n, P.eval (τ i) = 0)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ n) (hp_m1 : p.eval (-1) = 0)
    (hderiv : ∀ i : Fin n, |p.derivative.eval (τ i)| ≤ 1) :
    ∀ i : Fin n, |p.eval (τ i)| ≤ 1 + τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ := by
  -- Show P is a nonzero scalar multiple of legendreP n, so τ are the roots of legendreP n
  have hPeq := eq_smul_legendreP_of_orthog hPdeg hPorth
  have hPne : P ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hPdeg; omega
  have hcne : P.leadingCoeff / (legendreP n).leadingCoeff ≠ 0 :=
    div_ne_zero (leadingCoeff_ne_zero.mpr hPne) (ne_of_gt (legendreP_leadingCoeff_pos n))
  have hleg_roots : ∀ i : Fin n, (legendreP n).eval (τ i) = 0 := by
    intro i
    have hi := hτroots i
    rw [hPeq, eval_mul, eval_C] at hi
    exact (mul_eq_zero.mp hi).resolve_left hcne
  -- Nodes lie in (-1, 1)
  obtain ⟨τ₀, hmono₀, hIoo₀, _, hall₀, _⟩ := roots_of_orthog_weight
    (d := n) (P := legendreP n) (w := fun _ => 1)
    continuous_const (fun _ _ => zero_lt_one) (fun _ _ => zero_le_one)
    (legendreP_ne_zero n) (legendreP_natDegree n)
    (fun q hq => by simpa using legendreP_orthog_lt hq)
  have hτeq : τ = τ₀ := roots_enum_unique hτmono hmono₀ hleg_roots hall₀
  have hIoo : ∀ i : Fin n, -1 < τ i ∧ τ i < 1 := by rw [hτeq]; exact hIoo₀
  have hexact : ∀ f : Polynomial ℝ, f.natDegree ≤ 2 * (n - 1) →
      ∫ t in (-1 : ℝ)..1, f.eval t = ∑ j : Fin n, quadWeight τ j * f.eval (τ j) := fun f hf =>
    quad_exact_of_orthog hn hτmono.injective (legendreP_natDegree n) hleg_roots
      (fun q hq => legendreP_orthog_lt hq) (by omega)
  let last : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩
  intro i
  calc
    |p.eval (τ i)| ≤ ∑ j : Fin n, |intMatA τ i j| :=
      poly_abs_bound_of_sum_abs_intMatA hn hτmono.injective hpdeg hp_m1 hderiv i
    _ ≤ 1 + τ last := by
      by_cases hil : i = last
      · -- Part 3: Last row has all nonnegative entries, so ∑ |A_{nj}| = ∑ A_{nj} = 1 + τ_last!
        subst hil
        have hnn := gauss_intMatA_last_nonneg hn hτmono hleg_roots
        have habs : ∑ j : Fin n, |intMatA τ last j| = ∑ j : Fin n, intMatA τ last j :=
          Finset.sum_congr rfl fun j _ => abs_of_nonneg (hnn j)
        rw [habs, sum_intMatA hn hτmono.injective last]
      · -- Parts 1 & 2: Interior row i < last ⇒ n ≥ 2 and 1 - τ_i ≥ 1 - τ_{n-2} > 3(1 - τ_last) ≥ 2(1 - τ_last)
        have hi_lt : i < last := lt_of_le_of_ne (Nat.le_sub_one_of_lt i.isLt) hil
        have hn2 : 2 ≤ n := by have : i.val < n - 1 := hi_lt; omega
        have hgap := legendreP_root_gap hn2 hτmono hleg_roots
        have hile : i ≤ ⟨n - 2, by omega⟩ := by
          change i.val ≤ n - 2
          have : i.val < n - 1 := hi_lt
          omega
        have hτle : τ i ≤ τ ⟨n - 2, by omega⟩ := hτmono.monotone hile
        have hp1 := sum_abs_intMatA_le_three_add_div_two hn hτmono.injective hexact
          ⟨le_of_lt (hIoo i).1, le_of_lt (hIoo i).2⟩
        have hlast_lt1 : τ last < 1 := (hIoo last).2
        linarith

/-- **Sharpness Witness (`p(X) = X + 1`):** For any `n ≥ 1` and any nodes `τ : Fin n → ℝ` with
`-1 ≤ τ_{n-1}`, the polynomial `p = X + 1` satisfies all hypotheses of
`hager_gauss_legendre_sharp_challenge` and attains `|p(τ_{n-1})| = 1 + τ_{n-1}` identically. -/
theorem hager_gauss_legendre_sharp_attained
    (n : ℕ) (hn : 1 ≤ n) (τ : Fin n → ℝ)
    (hτ_ge : -1 ≤ τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩) :
    ∃ p : Polynomial ℝ,
      p.natDegree ≤ n ∧
      p.eval (-1) = 0 ∧
      (∀ i : Fin n, |p.derivative.eval (τ i)| ≤ 1) ∧
      |p.eval (τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩)| =
        1 + τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ := by
  refine ⟨X + 1, ?_, ?_, ?_, ?_⟩
  · have hdeg : (X + 1 : Polynomial ℝ).natDegree = 1 := by compute_degree!
    omega
  · simp
  · intro i
    simp [derivative_add, derivative_X, derivative_one]
  · simp only [eval_add, eval_X, eval_one]
    rw [abs_of_nonneg (by linarith)]
    ring

end Part3EnergyAndChallenge

end PPL031_HagerGaussSharp
