import HopfAlgebras.Words.AreaGeneration
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Polynomial reduction for families closed under signed area

The labels are arbitrary. `graft u v - graft v u` represents their area;
no tree structure or numerical method is assumed.
-/

namespace RoughPaths.AreaReduction

/-- A rational linear combination of moment monomials. -/
inductive Poly (α : Type*) where
  | zero
  | monomial (ts : List α)
  | add (p q : Poly α)
  | scale (c : ℚ) (p : Poly α)

namespace Poly

variable {α : Type*}

@[simp] def eval {R : Type*} [CommRing R] [Algebra ℚ R] (X : α → R) : Poly α → R
  | .zero => 0
  | .monomial ts => (ts.map X).prod
  | .add p q => eval X p + eval X q
  | .scale c p => (algebraMap ℚ R c) * eval X p

def sum : List (Poly α) → Poly α := List.foldr .add .zero

@[simp] theorem eval_sum {R : Type*} [CommRing R] [Algebra ℚ R] (X : α → R)
    (ps : List (Poly α)) : eval X (sum ps) = (ps.map (eval X)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [sum, eval] using congrArg (eval X p + ·) ih

end Poly

variable {α : Type*}

export HopfAlgebras.Word.Polynomial (selections selections_length selections_perm)

theorem selections_rest_length {α : Type*} {as : List α} {p : α × List α}
    (h : p ∈ selections as) : p.2.length + 1 = as.length := by
  simpa using (selections_perm h).length_eq

/-- Differential of a monomial, by Leibniz's rule. -/
def dmonomial {R : Type*} [CommRing R] (X V : α → R) : List α → R
  | [] => 0
  | t :: ts => V t * (ts.map X).prod + X t * dmonomial X V ts

@[simp] def Poly.diff {R : Type*} [CommRing R] [Algebra ℚ R] (X V : α → R) : Poly α → R
  | .zero => 0
  | .monomial ts => dmonomial X V ts
  | .add p q => p.diff X V + q.diff X V
  | .scale c p => (algebraMap ℚ R c) * p.diff X V

@[simp] theorem Poly.diff_sum {R : Type*} [CommRing R] [Algebra ℚ R] (X V : α → R)
    (ps : List (Poly α)) : (Poly.sum ps).diff X V = (ps.map (Poly.diff X V)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [Poly.sum, Poly.diff] using congrArg (p.diff X V + ·) ih

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
  | 0, _, _ => .zero
  | n + 1, ts, v =>
      .scale ((ts.length + 1 : ℚ)⁻¹)
        (.add (.monomial (v :: ts)) (Poly.sum ((selections ts).map fun p =>
          .add (primitive graft n p.2 (graft p.1 v))
            (.scale (-1) (primitive graft n p.2 (graft v p.1))))))

private theorem List.sum_map_sub_local {α R : Type*} [AddCommGroup R]
    (xs : List α) (f g : α → R) :
    (xs.map (fun x => f x - g x)).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, sub_add_sub_comm]

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
          (Poly.add (primitive graft n p.2 (graft p.1 v))
            (.scale (-1) (primitive graft n p.2 (graft v p.1)))).diff X V =
          (p.2.map X).prod * (X p.1 * V v - X v * V p.1) := by
        intro p hp
        have hlen := selections_rest_length hp
        simp only [Poly.diff]
        rw [ih p.2 _ (by omega), ih p.2 _ (by omega)]
        simp only [map_neg, map_one, neg_one_mul, ← sub_eq_add_neg]
        rw [← mul_sub, harea]
      rw [primitive, Poly.diff, Poly.diff, Poly.diff_sum]
      simp only [List.map_map, Function.comp_def]
      rw [List.map_congr_left hterms]
      have hs :
          ((selections ts).map (fun p =>
            (p.2.map X).prod * (X p.1 * V v - X v * V p.1))).sum =
          (ts.length : R) * (ts.map X).prod * V v - X v * dmonomial X V ts := by
        simp_rw [mul_sub, ← mul_assoc, mul_right_comm _ (X v)]
        rw [List.sum_map_sub_local, List.sum_map_mul_right, List.sum_map_mul_right,
          selections_product, selections_diff]
        ring
      rw [hs]
      dsimp only [Poly.diff, dmonomial]
      have hq : (ts.length + 1 : ℚ)⁻¹ * (ts.length + 1) = 1 :=
        inv_mul_cancel₀ (by positivity)
      have hu : algebraMap ℚ R ((ts.length + 1 : ℚ)⁻¹) * ((ts.length : R) + 1) = 1 := by
        simpa only [map_mul, map_add, map_natCast, map_one] using congrArg (algebraMap ℚ R) hq
      linear_combination hu * (ts.map X).prod * V v


end RoughPaths.AreaReduction
