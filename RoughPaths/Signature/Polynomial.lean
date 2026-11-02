import RoughPaths.Signature.Area
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Polynomial solutions of the chronological word recursion

On a straight path segment each letter has constant velocity. The word
differential recursion therefore gives the deconcatenation formula with
factorial denominators, at every word length.
-/

namespace RoughPaths.Word.PolynomialPath

open Polynomial
open scoped BigOperators

variable {α : Type*} (P : List α → ℝ[X]) (v : α → ℝ)
    (hnil : P [] = 1)
    (hd : ∀ w t, derivative (P (w ++ [t])) = P w * C (v t))

include hnil hd

theorem coeff (w : List α) (n : ℕ) :
    (P w).coeff n = if n ≤ w.length then
      (P (w.take (w.length - n))).eval 0 * (n.factorial : ℝ)⁻¹ *
        ((w.drop (w.length - n)).map v).prod else 0 := by
  induction n generalizing w with
  | zero => simp [Polynomial.coeff_zero_eq_eval_zero]
  | succ n ih =>
      cases w using List.reverseRecOn with
      | nil => simp [hnil, Polynomial.coeff_one]
      | append_singleton w t =>
          have hn : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
          have hc := congrArg (fun q : ℝ[X] => q.coeff n) (hd w t)
          rw [coeff_derivative, coeff_mul_C, ih] at hc
          by_cases h : n ≤ w.length
          · rw [ite_eq_left h] at hc
            have hc' := (eq_div_iff hn).mpr hc
            rw [hc']
            simp only [List.length_append, List.length_singleton, Nat.add_sub_add_right]
            rw [ite_eq_left (by omega), List.take_append_of_le_length (Nat.sub_le _ _),
              List.drop_append_of_le_length (Nat.sub_le _ _)]
            simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
              List.prod_cons, List.prod_nil, mul_one, Nat.factorial_succ, Nat.cast_mul,
              Nat.cast_add, Nat.cast_one, mul_inv_rev]
            field_simp
          · rw [ite_eq_right h, zero_mul] at hc
            have hz := (mul_eq_zero.mp hc).resolve_right hn
            rw [hz, ite_eq_right (by simp; omega)]

theorem natDegree_le (w : List α) : (P w).natDegree ≤ w.length := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff P v hnil hd, ite_eq_right (by omega)]

/-- Multiplication by a chronological exponential, recovered from its
constant-velocity differential equation. -/
theorem eval_one (w : List α) :
    (P w).eval 1 = ∑ j ∈ Finset.range (w.length + 1),
      (P (w.take j)).eval 0 * (((w.drop j).length.factorial : ℝ))⁻¹ *
        ((w.drop j).map v).prod := by
  rw [Polynomial.eval_eq_sum_range' (n := w.length + 1)
    (by have := natDegree_le P v hnil hd w; omega)]
  simp only [one_pow, mul_one]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [coeff P v hnil hd]
  simp only [Nat.add_sub_cancel, List.length_drop]
  rw [ite_eq_left (by omega), Nat.sub_sub_self (by omega)]

end RoughPaths.Word.PolynomialPath

namespace RoughPaths.Signature

open HopfAlgebras.Word.Polynomial
open Polynomial

variable {α : Type*} (S : Signature α ℝ[X])
    (hd : ∀ w a, derivative (S (w ++ [a])) = S w * derivative (S [a]))

include hd

theorem derivative_pairing_append (p : HopfAlgebras.Word.Polynomial α) (a : α) :
    derivative (pairing S (append a p)) = pairing S p * derivative (S [a]) := by
  induction p using HopfAlgebras.Word.Polynomial.induction with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul]
  | smul c p hp => simp [hp]
  | word w => simpa using hd w a

/-- Half-shuffle evaluation is the primitive of `u dv`, including
interior points of a polynomial segment. -/
theorem derivative_pairing_halfShuffle (p q : HopfAlgebras.Word.Polynomial α) :
    derivative (pairing S (halfShuffle p q)) =
      pairing S p * derivative (pairing S q) := by
  induction q using HopfAlgebras.Word.Polynomial.induction with
  | zero => simp
  | add q r hq hr => simp only [map_add, hq, hr, mul_add]
  | smul c q hq => simp [hq]
  | word w =>
    induction w using List.reverseRecOn with
    | nil =>
      have h : S [] = 1 := S.coeff_nil
      simp [h]
    | append_singleton w a _ =>
      rw [← append_word, halfShuffle_append, derivative_pairing_append S hd,
        pairing_shuffle, append_word]
      simp only [pairing_word, hd, mul_assoc]

/-- Signed area has precisely the derivative `u dv − v du`. -/
theorem derivative_pairing_area (p q : HopfAlgebras.Word.Polynomial α) :
    derivative (pairing S (area p q)) =
      pairing S p * derivative (pairing S q) -
        pairing S q * derivative (pairing S p) := by
  simp only [area, map_sub, derivative_pairing_halfShuffle S hd]

end RoughPaths.Signature
