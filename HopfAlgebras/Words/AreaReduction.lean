import HopfAlgebras.Words.Polynomial
import HopfAlgebras.Util.List
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Polynomial reduction for families closed under signed area

The labels are arbitrary. `graft u v - graft v u` represents their area;
no tree structure or numerical method is assumed.
-/

namespace HopfAlgebras.Word.AreaReduction

open HopfAlgebras.Word.Polynomial

/-- Moment polynomials use Mathlib's free rational module on monomials. -/
abbrev Poly := HopfAlgebras.Word.Polynomial

noncomputable section

namespace Poly

abbrev monomial {α : Type*} := word (α := α)

def eval {α R : Type*} [CommRing R] [Algebra ℚ R] (X : α → R) : Poly α →ₗ[ℚ] R :=
  lift (fun ts => (ts.map X).prod)

@[simp] theorem eval_monomial {α R : Type*} [CommRing R] [Algebra ℚ R]
    (X : α → R) (ts : List α) : eval X (monomial ts) = (ts.map X).prod := lift_word _ _

end Poly

variable {α : Type*}

open List (selections selections_length selections_perm selections_rest_length)

/-- Differential of a monomial, by Leibniz's rule. -/
def dmonomial {R : Type*} [CommRing R] (X V : α → R) : List α → R
  | [] => 0
  | t :: ts => V t * (ts.map X).prod + X t * dmonomial X V ts

def Poly.diff {R : Type*} [CommRing R] [Algebra ℚ R] (X V : α → R) : Poly α →ₗ[ℚ] R :=
  lift (dmonomial X V)

@[simp] theorem Poly.diff_monomial {R : Type*} [CommRing R] [Algebra ℚ R]
    (X V : α → R) (ts : List α) : Poly.diff X V (Poly.monomial ts) = dmonomial X V ts :=
  lift_word _ _

theorem selections_diff {R : Type*} [CommRing R] (X V : α → R)
    (ts : List α) :
    ((selections ts).map (fun p => (p.2.map X).prod * V p.1)).sum =
      dmonomial X V ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [selections, List.map_cons, List.sum_cons, List.map_map,
        dmonomial, Function.comp_def, List.prod_cons]
      simp only [mul_assoc]
      rw [List.sum_map_mul_left, ih]
      ring

theorem selections_product {R : Type*} [CommRing R] (X : α → R)
    (ts : List α) :
    ((selections ts).map (fun p => (p.2.map X).prod * X p.1)).sum =
      (ts.length : R) * (ts.map X).prod := by
  have heq : ∀ p ∈ selections ts, (p.2.map X).prod * X p.1 = (ts.map X).prod := by
    intro p hp
    simpa [mul_comm] using ((selections_perm hp).map X).prod_eq
  rw [List.map_congr_left heq]
  simp [selections_length, nsmul_eq_mul]

/-- Primitive of a moment monomial against one elementary column.
The fuel need only exceed the number of factors. -/
def primitive (graft : α → α → α) : ℕ → List α → α → Poly α
  | 0, _, _ => 0
  | n + 1, ts, v =>
      ((ts.length + 1 : ℚ)⁻¹) • (Poly.monomial (v :: ts) +
        ((selections ts).map fun p =>
          primitive graft n p.2 (graft p.1 v) - primitive graft n p.2 (graft v p.1)).sum)

/-- Universal differential identity used for moment reduction. -/
theorem diff_primitive {R : Type*} [CommRing R] [Algebra ℚ R]
    (graft : α → α → α) (X V : α → R)
    (harea : ∀ u v, V (graft u v) - V (graft v u) = X u * V v - X v * V u)
    (n : ℕ) (ts : List α) (v : α) (hn : ts.length < n) :
    (primitive graft n ts v).diff X V = (ts.map X).prod * V v := by
  induction n generalizing ts v with
  | zero => omega
  | succ n ih =>
      have hterms : ∀ p ∈ selections ts,
          (primitive graft n p.2 (graft p.1 v) - primitive graft n p.2 (graft v p.1)).diff X V =
          (p.2.map X).prod * (X p.1 * V v - X v * V p.1) := by
        intro p hp
        have hlen := selections_rest_length hp
        rw [map_sub, ih p.2 _ (by omega), ih p.2 _ (by omega), ← mul_sub, harea]
      rw [primitive, map_smul, map_add, map_list_sum, Poly.diff_monomial]
      simp only [List.map_map, Function.comp_def]
      rw [List.map_congr_left hterms]
      have hs :
          ((selections ts).map (fun p =>
            (p.2.map X).prod * (X p.1 * V v - X v * V p.1))).sum =
          (ts.length : R) * (ts.map X).prod * V v - X v * dmonomial X V ts := by
        simp_rw [mul_sub, ← mul_assoc, mul_right_comm _ (X v)]
        rw [List.sum_hom₂ _ (· - ·) (fun a b c d => (sub_add_sub_comm a c b d).symm) (sub_self 0) _ _, List.sum_map_mul_right, List.sum_map_mul_right,
          selections_product, selections_diff]
        ring
      rw [hs]
      dsimp only [dmonomial]
      rw [Algebra.smul_def]
      have hq : (ts.length + 1 : ℚ)⁻¹ * (ts.length + 1) = 1 :=
        inv_mul_cancel₀ (by positivity)
      have hu : algebraMap ℚ R ((ts.length + 1 : ℚ)⁻¹) * ((ts.length : R) + 1) = 1 := by
        simpa only [map_mul, map_add, map_natCast, map_one] using congrArg (algebraMap ℚ R) hq
      linear_combination hu * (ts.map X).prod * V v

end
end HopfAlgebras.Word.AreaReduction
