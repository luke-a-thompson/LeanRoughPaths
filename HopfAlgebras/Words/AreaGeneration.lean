import HopfAlgebras.Words.Polynomial
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

/-- Choose one occurrence, retaining the other factors, including repeats. -/
def selections {β : Type*} : List β → List (β × List β)
  | [] => []
  | a :: as => (a, as) :: (selections as).map (fun p => (p.1, a :: p.2))

@[simp] theorem selections_length {β : Type*} (xs : List β) :
    (selections xs).length = xs.length := by
  induction xs <;> simp [selections, *]

theorem selections_perm {β : Type*} {xs : List β} {p : β × List β}
    (h : p ∈ selections xs) : (p.1 :: p.2).Perm xs := by
  induction xs generalizing p with
  | nil => simp [selections] at h
  | cons a xs ih =>
    simp only [selections, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩
    · exact .refl _
    · exact (List.Perm.swap _ _ _).trans ((ih hq).cons a)

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
inductive Generated : Multiset α → Polynomial α → Prop
  | monomial (ts : List (AreaExpr α)) :
      Generated (ts.map AreaExpr.content).sum (prod (ts.map evalArea))
  | add {m p q} : Generated m p → Generated m q → Generated m (p + q)
  | smul {m p} (c : ℚ) : Generated m p → Generated m (c • p)
  | zero (m) : Generated m 0

theorem Generated.sum {β : Type*} (xs : List β) (f : β → Polynomial α) (m : Multiset α)
    (h : ∀ x ∈ xs, Generated m (f x)) : Generated m (xs.map f).sum := by
  induction xs with
  | nil => exact .zero m
  | cons x xs ih => exact .add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem selections_map {β γ : Type*} (f : β → γ) (xs : List β) :
    selections (xs.map f) = (selections xs).map (fun p => (f p.1, p.2.map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [selections, ih, List.map_map, Function.comp_def]

private theorem generated_halfShuffle_monomial (xs : List (AreaExpr α)) (y : AreaExpr α) :
    Generated ((xs.map AreaExpr.content).sum + y.content)
      (halfShuffle (prod (xs.map evalArea)) (evalArea y)) := by
  have h := halfShuffle_prod_reduction (xs.map evalArea) (evalArea y) (constant_evalArea y)
  rw [List.length_map, selections_map, List.map_map] at h
  have ht : Generated ((xs.map AreaExpr.content).sum + y.content)
      (shuffle (prod (xs.map evalArea)) (evalArea y) +
        ((selections xs).map fun p =>
          halfShuffle (prod (p.2.map evalArea)) (area (evalArea p.1) (evalArea y))).sum) := by
    apply Generated.add
    · simpa [prod, add_comm, shuffle_comm] using Generated.monomial (y :: xs)
    · apply Generated.sum
      intro p hp
      have hm := ((selections_perm hp).map AreaExpr.content).sum_eq
      simp only [List.map_cons, List.sum_cons] at hm
      have hi := generated_halfShuffle_monomial p.2 (.bracket p.1 y)
      convert hi using 1
      · simp only [AreaExpr.content]; rw [← hm]; ac_rfl
      · rfl
  have hn : (xs.length : ℚ) + 1 ≠ 0 := by positivity
  have he := congrArg (fun z => (((xs.length : ℚ) + 1)⁻¹) • z) h
  rw [smul_smul, inv_mul_cancel₀ hn, one_smul] at he
  rw [he]
  exact .smul _ ht
termination_by xs.length
decreasing_by
  have hlen := (selections_perm hp).length_eq
  simp only [List.length_cons] at hlen
  omega

/-- Homogeneous polynomials in areas are closed under integration
against an iterated area. -/
theorem Generated.halfShuffle_area {m : Multiset α} {p : Polynomial α}
    (hp : Generated m p) (y : AreaExpr α) :
    Generated (m + y.content) (halfShuffle p (evalArea y)) := by
  induction hp with
  | monomial xs => exact generated_halfShuffle_monomial xs y
  | add _ _ hp hq => simpa only [map_add, LinearMap.add_apply] using Generated.add hp hq
  | smul c _ hp => simpa only [map_smul, LinearMap.smul_apply] using Generated.smul c hp
  | zero m => simpa using Generated.zero (m + y.content)

/-- Every word is a rational shuffle polynomial in letters and nested
areas, preserving the multiplicity of each letter (DLPR, Corollary 4.8). -/
theorem word_generated (w : List α) : Generated (↑w : Multiset α) (word w) := by
  induction w using List.reverseRecOn with
  | nil => exact Generated.monomial []
  | append_singleton w a ih =>
    have he : halfShuffle (word w) (word [a]) = word (w ++ [a]) := by
      simpa using halfShuffle_word_append w [] a
    simpa [evalArea, AreaExpr.content, he, ← Multiset.coe_add] using ih.halfShuffle_area (.letter a)

end
end Polynomial
end HopfAlgebras.Word
