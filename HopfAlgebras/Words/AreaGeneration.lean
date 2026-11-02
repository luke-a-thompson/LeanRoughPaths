import HopfAlgebras.Words.Polynomial
import HopfAlgebras.Util.List
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Module
import Mathlib.Data.Multiset.AddSub

/-! # Generation by iterated areas

The half-shuffle product rule gives the reduction of a shuffle monomial
against one area to monomials with fewer factors. This is the integration
by parts form of the induction in Salvi–Diehl–Lyons–Preiß–Reizenstein,
*A structure theorem for streamed information*, §4.
-/

namespace HopfAlgebras.Word

/-- Letters and nested signed areas; shuffle products are kept outside. -/
inductive AreaExpr (α : Type*) where
  | letter (a : α)
  | bracket (u v : AreaExpr α)

def AreaExpr.content {α : Type*} : AreaExpr α → Multiset α
  | .letter a => {a}
  | .bracket u v => u.content + v.content

namespace Polynomial

open List (selections selections_length selections_perm selections_map)

variable {α : Type*}
noncomputable section

def evalArea : AreaExpr α → Polynomial α
  | .letter a => word [a]
  | .bracket u v => area (evalArea u) (evalArea v)

@[simp] theorem constant_evalArea (t : AreaExpr α) : constant (evalArea t) = 0 := by
  cases t <;> simp [evalArea]

/-- A shuffle monomial, including the empty monomial. -/
def prod : List (Polynomial α) → Polynomial α
  | [] => word []
  | p :: ps => shuffle p (prod ps)

theorem prod_perm {ps qs : List (Polynomial α)} (h : ps.Perm qs) : prod ps = prod qs := by
  induction h with
  | nil => rfl
  | cons p h ih => simp [prod, ih]
  | swap p q ps => simp only [prod, ← shuffle_assoc, shuffle_comm p q]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem halfShuffle_prod (y : Polynomial α) (xs : List (Polynomial α)) :
    halfShuffle y (prod xs) =
      ((selections xs).map fun p => halfShuffle (shuffle y (prod p.2)) p.1).sum := by
  induction xs generalizing y with
  | nil => simp [prod, selections]
  | cons x xs ih =>
    simp only [prod, halfShuffle_shuffle, ih, selections, List.map_cons,
      List.map_map, List.sum_cons, Function.comp_def]
    rw [add_comm]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    rw [shuffle_assoc]

/-- The reduction decreases the number of factors, with no division by
path increments or coefficients. -/
theorem halfShuffle_prod_reduction (xs : List (Polynomial α)) (y : Polynomial α)
    (hy : constant y = 0) :
    ((xs.length : ℚ) + 1) • halfShuffle (prod xs) y =
      shuffle (prod xs) y +
        ((selections xs).map fun p => halfShuffle (prod p.2) (area p.1 y)).sum := by
  have ht : ∀ p ∈ selections xs,
      halfShuffle (prod p.2) (area p.1 y) =
        halfShuffle (prod xs) y - halfShuffle (shuffle y (prod p.2)) p.1 := by
    intro p hp
    have he := prod_perm (selections_perm hp)
    dsimp only [prod] at he
    simp only [area, map_sub, halfShuffle_assoc]
    rw [shuffle_comm (prod p.2) p.1, he, shuffle_comm (prod p.2) y]
  rw [List.map_congr_left ht, List.sum_hom₂ _ (· - ·)
    (fun a b c d => (sub_add_sub_comm a c b d).symm) (sub_self 0) _ _]
  simp only [List.sum_replicate, List.map_const', selections_length]
  rw [← halfShuffle_prod]
  have hs := shuffle_eq_halfShuffle (prod xs) y
  rw [hy, mul_zero, zero_smul, add_zero] at hs
  rw [hs]
  simp only [← Nat.cast_smul_eq_nsmul ℚ]
  module

/-- A homogeneous linear combination of shuffle monomials in iterated
areas. The index records every letter occurrence, not just total degree. -/
def areaSpan (m : Multiset α) : Submodule ℚ (Polynomial α) :=
  Submodule.span ℚ {p | ∃ ts : List (AreaExpr α),
    (ts.map AreaExpr.content).sum = m ∧ prod (ts.map evalArea) = p}

theorem prod_evalArea_mem (ts : List (AreaExpr α)) :
    prod (ts.map evalArea) ∈ areaSpan (ts.map AreaExpr.content).sum :=
  Submodule.subset_span ⟨ts, rfl, rfl⟩

private theorem halfShuffle_monomial_mem (xs : List (AreaExpr α)) (y : AreaExpr α) :
    halfShuffle (prod (xs.map evalArea)) (evalArea y) ∈
      areaSpan ((xs.map AreaExpr.content).sum + y.content) := by
  have h := halfShuffle_prod_reduction (xs.map evalArea) (evalArea y) (constant_evalArea y)
  rw [List.length_map, selections_map, List.map_map] at h
  apply (Submodule.smul_mem_iff _ (show (xs.length : ℚ) + 1 ≠ 0 by positivity)).mp
  rw [h]
  apply Submodule.add_mem
  · simpa [prod, add_comm, shuffle_comm] using prod_evalArea_mem (y :: xs)
  · apply list_sum_mem
    intro z hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    have hm := ((selections_perm hp).map AreaExpr.content).sum_eq
    simp only [List.map_cons, List.sum_cons] at hm
    have hi := halfShuffle_monomial_mem p.2 (.bracket p.1 y)
    convert hi using 1
    · simp only [AreaExpr.content]; rw [← hm]; ac_rfl
    · rfl
termination_by xs.length
decreasing_by
  have hlen := List.selections_rest_length hp
  omega

/-- Homogeneous polynomials in areas are closed under integration
against an iterated area. -/
theorem halfShuffle_area_mem {m : Multiset α} {p : Polynomial α}
    (hp : p ∈ areaSpan m) (y : AreaExpr α) :
    halfShuffle p (evalArea y) ∈ areaSpan (m + y.content) := by
  refine (Submodule.span_le
    (p := (areaSpan (m + y.content)).comap (halfShuffle.flip (evalArea y)))).mpr ?_ hp
  rintro _ ⟨xs, rfl, rfl⟩
  exact halfShuffle_monomial_mem xs y

/-- Every word is a rational shuffle polynomial in letters and nested
areas, preserving the multiplicity of each letter (DLPR, Corollary 4.8). -/
theorem word_generated (w : List α) : word w ∈ areaSpan (↑w : Multiset α) := by
  induction w using List.reverseRecOn with
  | nil => exact prod_evalArea_mem []
  | append_singleton w a ih =>
    have he : halfShuffle (word w) (word [a]) = word (w ++ [a]) := by
      simpa using halfShuffle_word_append w [] a
    simpa [evalArea, AreaExpr.content, he, ← Multiset.coe_add] using halfShuffle_area_mem ih (.letter a)

end
end Polynomial
end HopfAlgebras.Word
