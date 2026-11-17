import HopfAlgebras.Words.ShuffleAlgebra
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Algebra.Rat

/-!
# Areas of areas generate the shuffle algebra

Every word is a rational shuffle polynomial in letters and nested signed
areas (Diehl–Lyons–Preiß–Reizenstein, *Areas of areas generate the shuffle
algebra*, Corollary 4.8). The proof is `Derivation.length_succ_nsmul_prod_smul`
for the deletion derivation: integrating a product of areas against one more
area gives the product, plus integrals with one factor fewer against a
deeper area.

The statement is homogeneous for any additive size of the letters
(`AreaExpr.sum`): a weight, or the multiset of letters itself.
-/

namespace HopfAlgebras

/-- Bracket expressions: letters and nested signed areas. -/
inductive AreaExpr (α : Type*) where
  | letter (a : α)
  | bracket (u v : AreaExpr α)

namespace AreaExpr

variable {α : Type*}

/-- The additive size of an expression: the sum of `f` over its letters. -/
def sum {N : Type*} [AddCommMonoid N] (f : α → N) : AreaExpr α → N
  | .letter a => f a
  | .bracket u v => u.sum f + v.sum f

/-- The iterated area that an expression denotes. -/
noncomputable def eval {R : Type*} [CommRing R] : AreaExpr α → ShuffleAlgebra R α
  | .letter a => ShuffleAlgebra.word [a]
  | .bracket u v => ShuffleAlgebra.area u.eval v.eval

@[simp] theorem constant_eval {R : Type*} [CommRing R] (t : AreaExpr α) :
    ShuffleAlgebra.constant (t.eval : ShuffleAlgebra R α) = 0 := by
  cases t <;> simp [eval]

end AreaExpr

namespace ShuffleAlgebra

open List (selections selections_perm selections_rest_length selections_map)

variable {R : Type*} {α : Type*} [CommRing R] {N : Type*} [AddCommMonoid N]

/-- Linear combinations of shuffle products of iterated areas of total
size `n`. -/
noncomputable def areaSpan (f : α → N) (n : N) : Submodule R (ShuffleAlgebra R α) :=
  Submodule.span R {p | ∃ ts : List (AreaExpr α),
    (ts.map (AreaExpr.sum f)).sum = n ∧ (ts.map AreaExpr.eval).prod = p}

theorem prod_eval_mem_areaSpan (f : α → N) (ts : List (AreaExpr α)) :
    (ts.map AreaExpr.eval).prod ∈ areaSpan (R := R) f (ts.map (AreaExpr.sum f)).sum :=
  Submodule.subset_span ⟨ts, rfl, rfl⟩

variable [Algebra ℚ R]

/-- Integrating a product of areas against an area stays in the span. -/
theorem prod_halfShuffle_mem (f : α → N) (ts : List (AreaExpr α)) (y : AreaExpr α) :
    halfShuffle (ts.map AreaExpr.eval).prod (y.eval : ShuffleAlgebra R α) ∈
      areaSpan f ((ts.map (AreaExpr.sum f)).sum + y.sum f) := by
  induction hn : ts.length using Nat.strong_induction_on generalizing ts y with
  | _ n ih =>
    have hred := congrArg integral
      (deletion.length_succ_nsmul_prod_smul (ts.map (AreaExpr.eval (R := R))) y.eval)
    rw [map_nsmul, map_add, integral_deletion, map_list_sum, selections_map, List.map_map,
      List.map_map, List.length_map, constant_mul, AreaExpr.constant_eval, zero_mul, zero_smul,
      sub_zero] at hred
    have hboundary : (y.eval : ShuffleAlgebra R α) * (ts.map AreaExpr.eval).prod ∈
        areaSpan f ((ts.map (AreaExpr.sum f)).sum + y.sum f) := by
      have h := prod_eval_mem_areaSpan (R := R) f (y :: ts)
      simp only [List.map_cons, List.prod_cons, List.sum_cons] at h
      rwa [add_comm] at h
    have hterms : ∀ p ∈ selections ts,
        integral ((p.2.map (AreaExpr.eval (R := R))).prod •
          Derivation.area deletion (p.1.eval : ShuffleAlgebra R α) y.eval) ∈
            areaSpan f ((ts.map (AreaExpr.sum f)).sum + y.sum f) := by
      intro p hp
      have hlen := selections_rest_length hp
      have hsum : (p.2.map (AreaExpr.sum f)).sum + (p.1.sum f + y.sum f) =
          (ts.map (AreaExpr.sum f)).sum + y.sum f := by
        have h := ((selections_perm hp).map (AreaExpr.sum f)).sum_eq
        rw [List.map_cons, List.sum_cons] at h
        rw [← h, ← add_assoc, add_comm _ (p.1.sum f)]
      have h := ih p.2.length (by omega) p.2 (.bracket p.1 y) rfl
      rw [AreaExpr.sum, hsum] at h
      simpa [halfShuffle, AreaExpr.eval] using h
    have hmem : (ts.length + 1) • halfShuffle (ts.map AreaExpr.eval).prod
        (y.eval : ShuffleAlgebra R α) ∈ areaSpan f ((ts.map (AreaExpr.sum f)).sum + y.sum f) := by
      rw [halfShuffle, hred]
      refine add_mem hboundary (list_sum_mem fun x hx => ?_)
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact hterms p hp
    have hc : algebraMap ℚ R ((ts.length + 1 : ℚ)⁻¹) * ((ts.length + 1 : ℕ) : R) = 1 := by
      rw [← map_natCast (algebraMap ℚ R), ← map_mul, Nat.cast_add, Nat.cast_one,
        inv_mul_cancel₀ (by positivity), map_one]
    have hdiv := Submodule.smul_mem _ (algebraMap ℚ R ((ts.length + 1 : ℚ)⁻¹)) hmem
    rwa [← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul] at hdiv

/-- Homogeneous polynomials in areas are closed under integration against
an iterated area. -/
theorem halfShuffle_mem_areaSpan (f : α → N) {n : N} {g : ShuffleAlgebra R α}
    (hg : g ∈ areaSpan f n) (y : AreaExpr α) :
    halfShuffle g y.eval ∈ areaSpan f (n + y.sum f) := by
  have h : (areaSpan (R := R) f n).map (halfShuffleRight y.eval) ≤
      areaSpan f (n + y.sum f) := by
    rw [areaSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨ts, rfl, rfl⟩, rfl⟩
    exact prod_halfShuffle_mem f ts y
  exact h (Submodule.mem_map_of_mem hg)

/-- **Areas of areas generate the shuffle algebra**, homogeneously: every
word is a shuffle polynomial in iterated areas of the same total size. -/
theorem word_mem_areaSpan (f : α → N) (w : List α) :
    (word w : ShuffleAlgebra R α) ∈ areaSpan f (w.map f).sum := by
  induction w using List.reverseRecOn with
  | nil => simpa [one_def] using prod_eval_mem_areaSpan (R := R) f []
  | append_singleton w a ih =>
      rw [← halfShuffle_word_singleton, List.map_append, List.sum_append]
      simpa [AreaExpr.eval, AreaExpr.sum] using halfShuffle_mem_areaSpan f ih (.letter a)

/-- **Areas of areas generate the shuffle algebra.** -/
theorem adjoin_range_eval_eq_top :
    Algebra.adjoin R (Set.range (AreaExpr.eval : AreaExpr α → ShuffleAlgebra R α)) = ⊤ := by
  have hspan : ∀ n : ℕ, areaSpan (R := R) (fun _ : α => (0 : ℕ)) n ≤
      Subalgebra.toSubmodule (Algebra.adjoin R (Set.range AreaExpr.eval)) := by
    intro n
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨ts, -, rfl⟩
    refine Subalgebra.list_prod_mem _ fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact Algebra.subset_adjoin ⟨t, rfl⟩
  refine eq_top_iff.mpr fun p hp => ?_
  clear hp
  induction p using induction with
  | zero => exact zero_mem _
  | word w => exact hspan _ (word_mem_areaSpan _ w)
  | add p q hp hq => exact add_mem hp hq
  | smul c p hp => exact Subalgebra.smul_mem _ hp c

end ShuffleAlgebra
end HopfAlgebras
