/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.Coproduct
import HopfAlgebras.Util.List
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The BCK Antipode

This file defines the recursive antipode on rooted-forest monomials for the
Connes-Kreimer/BCK Hopf algebra.

## Main definitions

* `RootedForest.antipode` - the recursive antipode on rooted forest monomials
* `RootedForest.antipodeProperSum` - the proper-coproduct part of the recursion

## References

* Alain Connes, Dirk Kreimer, *Hopf Algebras, Renormalization and
  Noncommutative Geometry*
* Loic Foissy, *An introduction to Hopf algebras of trees*
-/

namespace HopfAlgebras

universe u

namespace RootedForest

noncomputable section

variable {R : Type u} [CommRing R]

/-- The recursive BCK antipode on rooted-forest monomials. -/
noncomputable def antipode (φ : RootedForest) : ForestAlgebra R := by
  classical
  exact
    if hφ : φ = 0 then
      1
    else
      -ForestAlgebra.ofForest (R := R) φ -
        ((properCoproductTerms φ).attach.map fun term =>
          antipode term.1.1 *
            ForestAlgebra.ofForest (R := R) term.1.2).sum
termination_by order φ
decreasing_by
  exact properCoproductTerms_left_order_lt term.2

/-- The proper-coproduct sum appearing in the recursive antipode formula. -/
noncomputable def antipodeProperSum (φ : RootedForest) : ForestAlgebra R :=
  ((properCoproductTerms φ).attach.map fun term =>
    antipode (R := R) term.1.1 *
      ForestAlgebra.ofForest (R := R) term.1.2).sum

/-- `antipodeProperSum` with the `attach` plumbing removed. -/
theorem antipodeProperSum_eq_map_sum (φ : RootedForest) :
    antipodeProperSum (R := R) φ =
      ((properCoproductTerms φ).map fun term =>
        antipode (R := R) term.1 *
          ForestAlgebra.ofForest (R := R) term.2).sum := by
  rw [antipodeProperSum]
  exact List.sum_attach_map (properCoproductTerms φ) fun term =>
    antipode (R := R) term.1 * ForestAlgebra.ofForest (R := R) term.2

@[simp]
theorem antipode_zero : antipode (R := R) 0 = 1 := by
  rw [antipode]
  simp

@[simp]
theorem antipode_empty : antipode (R := R) RootedForest.empty = 1 := by
  simp [RootedForest.empty]

theorem antipode_eq_of_ne_zero {φ : RootedForest} (hφ : φ ≠ 0) :
    antipode (R := R) φ =
      -ForestAlgebra.ofForest (R := R) φ - antipodeProperSum (R := R) φ := by
  rw [antipode, antipodeProperSum]
  simp [hφ]

theorem antipode_singleton (τ : RootedTree) :
    antipode (R := R) (RootedForest.singleton τ) =
      -ForestAlgebra.ofForest (R := R) (RootedForest.singleton τ) -
        antipodeProperSum (R := R) (RootedForest.singleton τ) :=
  antipode_eq_of_ne_zero (R := R) (RootedForest.singleton_ne_zero τ)

theorem counit_antipode (φ : RootedForest) :
    ForestAlgebra.counit R (antipode (R := R) φ) =
      ForestAlgebra.counitCoeff (R := R) φ := by
  by_cases hφ : φ = 0
  · subst φ
    simp
  · have hsum :
        ForestAlgebra.counit R (antipodeProperSum (R := R) φ) = 0 := by
      rw [antipodeProperSum, map_list_sum]
      apply List.sum_eq_zero
      intro x hx
      rcases List.mem_map.1 hx with ⟨y, hy, rfl⟩
      rcases List.mem_map.1 hy with ⟨term, hterm, rfl⟩
      have hmem : term.1 ∈ properCoproductTerms φ := term.2
      have hproper :
          0 < RootedForest.order term.1.2 :=
        (of_decide_eq_true (List.mem_filter.1 hmem).2).2
      have hright : term.1.2 ≠ 0 :=
        (RootedForest.order_pos_iff_ne_zero term.1.2).1 hproper
      simp [ForestAlgebra.counit_ofForest_ne_zero hright]
    rw [antipode_eq_of_ne_zero hφ, ForestAlgebra.counitCoeff_ne_zero hφ]
    simp [hsum, ForestAlgebra.counit_ofForest_ne_zero hφ]

/-- The symmetric right-recursive BCK antipode on rooted-forest monomials. -/
noncomputable def rightAntipode (φ : RootedForest) : ForestAlgebra R := by
  classical
  exact
    if hφ : φ = 0 then
      1
    else
      -ForestAlgebra.ofForest (R := R) φ -
        ((properCoproductTerms φ).attach.map fun term =>
          ForestAlgebra.ofForest (R := R) term.1.1 *
            rightAntipode term.1.2).sum
termination_by order φ
decreasing_by
  exact properCoproductTerms_right_order_lt term.2

/-- The proper-coproduct sum appearing in the right-recursive antipode formula. -/
noncomputable def rightAntipodeProperSum (φ : RootedForest) : ForestAlgebra R :=
  ((properCoproductTerms φ).attach.map fun term =>
    ForestAlgebra.ofForest (R := R) term.1.1 *
      rightAntipode (R := R) term.1.2).sum

/-- `rightAntipodeProperSum` with the `attach` plumbing removed. -/
theorem rightAntipodeProperSum_eq_map_sum (φ : RootedForest) :
    rightAntipodeProperSum (R := R) φ =
      ((properCoproductTerms φ).map fun term =>
        ForestAlgebra.ofForest (R := R) term.1 *
          rightAntipode (R := R) term.2).sum := by
  rw [rightAntipodeProperSum]
  exact List.sum_attach_map (properCoproductTerms φ) fun term =>
    ForestAlgebra.ofForest (R := R) term.1 * rightAntipode (R := R) term.2

@[simp]
theorem rightAntipode_zero : rightAntipode (R := R) 0 = 1 := by
  rw [rightAntipode]
  simp

@[simp]
theorem rightAntipode_empty : rightAntipode (R := R) RootedForest.empty = 1 := by
  simp [RootedForest.empty]

theorem rightAntipode_eq_of_ne_zero {φ : RootedForest} (hφ : φ ≠ 0) :
    rightAntipode (R := R) φ =
      -ForestAlgebra.ofForest (R := R) φ - rightAntipodeProperSum (R := R) φ := by
  rw [rightAntipode, rightAntipodeProperSum]
  simp [hφ]

theorem rightAntipode_singleton (τ : RootedTree) :
    rightAntipode (R := R) (RootedForest.singleton τ) =
      -ForestAlgebra.ofForest (R := R) (RootedForest.singleton τ) -
        rightAntipodeProperSum (R := R) (RootedForest.singleton τ) :=
  rightAntipode_eq_of_ne_zero (R := R) (RootedForest.singleton_ne_zero τ)

theorem counit_rightAntipode (φ : RootedForest) :
    ForestAlgebra.counit R (rightAntipode (R := R) φ) =
      ForestAlgebra.counitCoeff (R := R) φ := by
  by_cases hφ : φ = 0
  · subst φ
    simp
  · have hsum :
        ForestAlgebra.counit R (rightAntipodeProperSum (R := R) φ) = 0 := by
      rw [rightAntipodeProperSum, map_list_sum]
      apply List.sum_eq_zero
      intro x hx
      rcases List.mem_map.1 hx with ⟨y, hy, rfl⟩
      rcases List.mem_map.1 hy with ⟨term, hterm, rfl⟩
      have hmem : term.1 ∈ properCoproductTerms φ := term.2
      have hproper :
          0 < RootedForest.order term.1.1 :=
        (of_decide_eq_true (List.mem_filter.1 hmem).2).1
      have hleft : term.1.1 ≠ 0 :=
        (RootedForest.order_pos_iff_ne_zero term.1.1).1 hproper
      simp [ForestAlgebra.counit_ofForest_ne_zero hleft]
    rw [rightAntipode_eq_of_ne_zero hφ, ForestAlgebra.counitCoeff_ne_zero hφ]
    simp [hsum, ForestAlgebra.counit_ofForest_ne_zero hφ]

end

end RootedForest

namespace ForestTensorAlgebra

noncomputable section

variable {R : Type u} [CommRing R]

/-- Evaluate a tensor term by applying the recursive antipode to the left factor
and multiplying in the forest algebra. -/
noncomputable def antipodeLeft : ForestTensorAlgebra R →ₗ[R] ForestAlgebra R :=
  (Finsupp.linearCombination R fun term : RootedForest × RootedForest =>
    RootedForest.antipode (R := R) term.1 *
      ForestAlgebra.ofForest (R := R) term.2).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem antipodeLeft_ofPair (term : RootedForest × RootedForest) :
    antipodeLeft (R := R) (ofPair (R := R) term) =
      RootedForest.antipode (R := R) term.1 *
        ForestAlgebra.ofForest (R := R) term.2 := by
  rw [antipodeLeft, ofPair]
  change (Finsupp.linearCombination R fun term : RootedForest × RootedForest =>
      RootedForest.antipode (R := R) term.1 *
        ForestAlgebra.ofForest (R := R) term.2)
      (Finsupp.single term (1 : R)) =
    RootedForest.antipode (R := R) term.1 *
      ForestAlgebra.ofForest (R := R) term.2
  rw [Finsupp.linearCombination_single]
  simp

theorem antipodeLeft_sumTerms (terms : List (RootedForest × RootedForest)) :
    antipodeLeft (R := R) (sumTerms (R := R) terms) =
      (terms.map fun term =>
        RootedForest.antipode (R := R) term.1 *
          ForestAlgebra.ofForest (R := R) term.2).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, antipodeLeft_ofPair, ih]
      rfl

theorem evalCharacter_antipodeLeft_sumTerms (χ : ForestAlgebra.Character R)
    (terms : List (RootedForest × RootedForest)) :
    χ (antipodeLeft (R := R) (sumTerms (R := R) terms)) =
      (terms.map fun term =>
        χ (RootedForest.antipode (R := R) term.1) *
          χ.evalForest term.2).sum := by
  rw [antipodeLeft_sumTerms, map_list_sum]
  simp [Function.comp_def, ForestAlgebra.Character.evalForest]

/-- Evaluate a tensor term by applying the right-recursive antipode to the right factor
and multiplying in the forest algebra. -/
noncomputable def antipodeRight : ForestTensorAlgebra R →ₗ[R] ForestAlgebra R :=
  (Finsupp.linearCombination R fun term : RootedForest × RootedForest =>
    ForestAlgebra.ofForest (R := R) term.1 *
      RootedForest.rightAntipode (R := R) term.2).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem antipodeRight_ofPair (term : RootedForest × RootedForest) :
    antipodeRight (R := R) (ofPair (R := R) term) =
      ForestAlgebra.ofForest (R := R) term.1 *
        RootedForest.rightAntipode (R := R) term.2 := by
  rw [antipodeRight, ofPair]
  change (Finsupp.linearCombination R fun term : RootedForest × RootedForest =>
      ForestAlgebra.ofForest (R := R) term.1 *
        RootedForest.rightAntipode (R := R) term.2)
      (Finsupp.single term (1 : R)) =
    ForestAlgebra.ofForest (R := R) term.1 *
      RootedForest.rightAntipode (R := R) term.2
  rw [Finsupp.linearCombination_single]
  simp

theorem antipodeRight_sumTerms (terms : List (RootedForest × RootedForest)) :
    antipodeRight (R := R) (sumTerms (R := R) terms) =
      (terms.map fun term =>
        ForestAlgebra.ofForest (R := R) term.1 *
          RootedForest.rightAntipode (R := R) term.2).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, antipodeRight_ofPair, ih]
      rfl

theorem evalCharacter_antipodeRight_sumTerms (χ : ForestAlgebra.Character R)
    (terms : List (RootedForest × RootedForest)) :
    χ (antipodeRight (R := R) (sumTerms (R := R) terms)) =
      (terms.map fun term =>
        χ.evalForest term.1 *
          χ (RootedForest.rightAntipode (R := R) term.2)).sum := by
  rw [antipodeRight_sumTerms, map_list_sum]
  simp [Function.comp_def, ForestAlgebra.Character.evalForest]

private theorem antipodeLeft_terms_sum_eq_boundary_add_proper
    {φ : RootedForest} (hφ : φ ≠ 0) :
    ∀ terms : List (RootedForest × RootedForest),
      (∀ term ∈ terms, RootedForest.order term.1 = 0 → term = (0, φ)) →
      (∀ term ∈ terms, RootedForest.order term.2 = 0 → term = (φ, 0)) →
        (terms.map fun term =>
          RootedForest.antipode (R := R) term.1 *
            ForestAlgebra.ofForest (R := R) term.2).sum =
          ((terms.filterMap PTree.leftBoundaryCoproductTerm?).map fun term =>
            RootedForest.antipode (R := R) term.1 *
              ForestAlgebra.ofForest (R := R) term.2).sum +
          ((terms.filterMap PTree.rightBoundaryCoproductTerm?).map fun term =>
            RootedForest.antipode (R := R) term.1 *
              ForestAlgebra.ofForest (R := R) term.2).sum +
          (((terms.filter fun term =>
              0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2).map fun term =>
            RootedForest.antipode (R := R) term.1 *
              ForestAlgebra.ofForest (R := R) term.2).sum)
  | [], _hleft, _hright => by
      simp [PTree.leftBoundaryCoproductTerm?, PTree.rightBoundaryCoproductTerm?]
  | term :: terms, hleft, hright => by
      have hleft_tail :
          ∀ term' ∈ terms, RootedForest.order term'.1 = 0 → term' = (0, φ) := by
        intro term' hmem hzero
        exact hleft term' (by simp [hmem]) hzero
      have hright_tail :
          ∀ term' ∈ terms, RootedForest.order term'.2 = 0 → term' = (φ, 0) := by
        intro term' hmem hzero
        exact hright term' (by simp [hmem]) hzero
      have ih := antipodeLeft_terms_sum_eq_boundary_add_proper hφ
        terms hleft_tail hright_tail
      have hφ_order : RootedForest.order φ ≠ 0 := by
        intro hzero
        exact hφ ((RootedForest.order_eq_zero_iff φ).1 hzero)
      by_cases hterm_left : RootedForest.order term.1 = 0
      · have hterm : term = (0, φ) := hleft term (by simp) hterm_left
        subst term
        simp [PTree.leftBoundaryCoproductTerm?, PTree.rightBoundaryCoproductTerm?,
          hφ_order, ih]
        abel
      · by_cases hterm_right : RootedForest.order term.2 = 0
        · have hterm : term = (φ, 0) := hright term (by simp) hterm_right
          subst term
          simp [PTree.leftBoundaryCoproductTerm?, PTree.rightBoundaryCoproductTerm?,
            hφ_order, ih]
          abel
        · have hproper :
              0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2 := by
            exact ⟨Nat.pos_of_ne_zero hterm_left, Nat.pos_of_ne_zero hterm_right⟩
          simp [PTree.leftBoundaryCoproductTerm?, PTree.rightBoundaryCoproductTerm?,
            hterm_left, hterm_right, hproper, ih]
          abel

private theorem antipodeRight_terms_sum_eq_boundary_add_proper
    {φ : RootedForest} (hφ : φ ≠ 0) :
    ∀ terms : List (RootedForest × RootedForest),
      (∀ term ∈ terms, RootedForest.order term.1 = 0 → term = (0, φ)) →
      (∀ term ∈ terms, RootedForest.order term.2 = 0 → term = (φ, 0)) →
        (terms.map fun term =>
          ForestAlgebra.ofForest (R := R) term.1 *
            RootedForest.rightAntipode (R := R) term.2).sum =
          ((terms.filterMap PTree.leftBoundaryCoproductTerm?).map fun term =>
            ForestAlgebra.ofForest (R := R) term.1 *
              RootedForest.rightAntipode (R := R) term.2).sum +
          ((terms.filterMap PTree.rightBoundaryCoproductTerm?).map fun term =>
            ForestAlgebra.ofForest (R := R) term.1 *
              RootedForest.rightAntipode (R := R) term.2).sum +
          (((terms.filter fun term =>
              0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2).map fun term =>
            ForestAlgebra.ofForest (R := R) term.1 *
              RootedForest.rightAntipode (R := R) term.2).sum)
  | [], _hleft, _hright => by
      simp [PTree.leftBoundaryCoproductTerm?, PTree.rightBoundaryCoproductTerm?]
  | term :: terms, hleft, hright => by
      have hleft_tail :
          ∀ term' ∈ terms, RootedForest.order term'.1 = 0 → term' = (0, φ) := by
        intro term' hmem hzero
        exact hleft term' (by simp [hmem]) hzero
      have hright_tail :
          ∀ term' ∈ terms, RootedForest.order term'.2 = 0 → term' = (φ, 0) := by
        intro term' hmem hzero
        exact hright term' (by simp [hmem]) hzero
      have ih := antipodeRight_terms_sum_eq_boundary_add_proper hφ
        terms hleft_tail hright_tail
      have hφ_order : RootedForest.order φ ≠ 0 := by
        intro hzero
        exact hφ ((RootedForest.order_eq_zero_iff φ).1 hzero)
      by_cases hterm_left : RootedForest.order term.1 = 0
      · have hterm : term = (0, φ) := hleft term (by simp) hterm_left
        subst term
        simp [PTree.leftBoundaryCoproductTerm?, PTree.rightBoundaryCoproductTerm?,
          hφ_order, ih]
        abel
      · by_cases hterm_right : RootedForest.order term.2 = 0
        · have hterm : term = (φ, 0) := hright term (by simp) hterm_right
          subst term
          simp [PTree.leftBoundaryCoproductTerm?, PTree.rightBoundaryCoproductTerm?,
            hφ_order, ih]
          abel
        · have hproper :
              0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2 := by
            exact ⟨Nat.pos_of_ne_zero hterm_left, Nat.pos_of_ne_zero hterm_right⟩
          simp [PTree.leftBoundaryCoproductTerm?, PTree.rightBoundaryCoproductTerm?,
            hterm_left, hterm_right, hproper, ih]
          abel

end

end ForestTensorAlgebra

namespace RootedForest

noncomputable section

variable {R : Type u} [CommRing R]

theorem antipodeLeft_reducedCoproduct (φ : RootedForest) :
    ForestTensorAlgebra.antipodeLeft (R := R)
        (reducedCoproduct (R := R) φ) =
      antipodeProperSum (R := R) φ := by
  rw [reducedCoproduct, ForestTensorAlgebra.antipodeLeft_sumTerms,
    antipodeProperSum_eq_map_sum]

theorem antipodeLeft_reducedCoproduct_eq_neg {φ : RootedForest} (hφ : φ ≠ 0) :
    ForestTensorAlgebra.antipodeLeft (R := R)
        (reducedCoproduct (R := R) φ) =
      -ForestAlgebra.ofForest (R := R) φ - antipode (R := R) φ := by
  rw [antipodeLeft_reducedCoproduct, antipode_eq_of_ne_zero hφ]
  abel

theorem antipode_add_ofForest_add_antipodeLeft_reducedCoproduct
    {φ : RootedForest} (hφ : φ ≠ 0) :
    antipode (R := R) φ + ForestAlgebra.ofForest (R := R) φ +
        ForestTensorAlgebra.antipodeLeft (R := R)
          (reducedCoproduct (R := R) φ) = 0 := by
  rw [antipodeLeft_reducedCoproduct, antipode_eq_of_ne_zero hφ]
  abel

theorem antipodeRight_reducedCoproduct (φ : RootedForest) :
    ForestTensorAlgebra.antipodeRight (R := R)
        (reducedCoproduct (R := R) φ) =
      rightAntipodeProperSum (R := R) φ := by
  rw [reducedCoproduct, ForestTensorAlgebra.antipodeRight_sumTerms,
    rightAntipodeProperSum_eq_map_sum]

theorem antipodeRight_reducedCoproduct_eq_neg {φ : RootedForest} (hφ : φ ≠ 0) :
    ForestTensorAlgebra.antipodeRight (R := R)
        (reducedCoproduct (R := R) φ) =
      -ForestAlgebra.ofForest (R := R) φ - rightAntipode (R := R) φ := by
  rw [antipodeRight_reducedCoproduct, rightAntipode_eq_of_ne_zero hφ]
  abel

theorem rightAntipode_add_ofForest_add_antipodeRight_reducedCoproduct
    {φ : RootedForest} (hφ : φ ≠ 0) :
    rightAntipode (R := R) φ + ForestAlgebra.ofForest (R := R) φ +
        ForestTensorAlgebra.antipodeRight (R := R)
          (reducedCoproduct (R := R) φ) = 0 := by
  rw [antipodeRight_reducedCoproduct, rightAntipode_eq_of_ne_zero hφ]
  abel

/-- Evaluating the full coproduct by the recursive antipode on the left gives the counit. -/
theorem antipodeLeft_coproduct (φ : RootedForest) :
    ForestTensorAlgebra.antipodeLeft (R := R) (coproduct (R := R) φ) =
      ForestAlgebra.counitCoeff (R := R) φ • (1 : ForestAlgebra R) := by
  by_cases hφ : φ = 0
  · subst φ
    rw [coproduct_zero]
    simp only [ForestAlgebra.counitCoeff_zero, one_smul]
    rw [← ForestTensorAlgebra.ofPair_zero (R := R), ForestTensorAlgebra.antipodeLeft_ofPair]
    simp
  · rw [ForestAlgebra.counitCoeff_ne_zero hφ, zero_smul]
    rw [coproduct_eq_sumTerms_coproductTerms, ForestTensorAlgebra.antipodeLeft_sumTerms]
    have hleft :
        ∀ term ∈ coproductTerms φ, RootedForest.order term.1 = 0 → term = (0, φ) := by
      intro term hterm hzero
      have hleft_zero : term.1 = 0 := (RootedForest.order_eq_zero_iff term.1).1 hzero
      have hright := coproductTerms_left_eq_zero hterm hleft_zero
      cases term with
      | mk left right =>
          simp at hleft_zero hright ⊢
          exact ⟨hleft_zero, hright⟩
    have hright :
        ∀ term ∈ coproductTerms φ, RootedForest.order term.2 = 0 → term = (φ, 0) := by
      intro term hterm hzero
      have hright_zero : term.2 = 0 := (RootedForest.order_eq_zero_iff term.2).1 hzero
      have hleft_eq := coproductTerms_right_eq_zero hterm hright_zero
      cases term with
      | mk left right =>
          simp at hright_zero hleft_eq ⊢
          exact ⟨hleft_eq, hright_zero⟩
    rw [ForestTensorAlgebra.antipodeLeft_terms_sum_eq_boundary_add_proper
      (R := R) hφ (coproductTerms φ) hleft hright]
    rw [coproductTerms_leftBoundaryCoproductTerm,
      coproductTerms_rightBoundaryCoproductTerm]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change
      antipode (R := R) 0 * ForestAlgebra.ofForest (R := R) φ +
          antipode (R := R) φ * ForestAlgebra.ofForest (R := R) 0 +
          ((properCoproductTerms φ).map fun term =>
            antipode (R := R) term.1 * ForestAlgebra.ofForest (R := R) term.2).sum =
        0
    rw [← ForestTensorAlgebra.antipodeLeft_sumTerms (R := R) (properCoproductTerms φ)]
    change
      antipode (R := R) 0 * ForestAlgebra.ofForest (R := R) φ +
          antipode (R := R) φ * ForestAlgebra.ofForest (R := R) 0 +
          ForestTensorAlgebra.antipodeLeft (R := R) (reducedCoproduct (R := R) φ) =
        0
    rw [antipode_zero, ForestAlgebra.ofForest_zero, one_mul, mul_one]
    simpa [add_comm, add_left_comm, add_assoc] using
      antipode_add_ofForest_add_antipodeLeft_reducedCoproduct (R := R) hφ

theorem evalCharacter_antipodeLeft_coproductTerms
    (χ : ForestAlgebra.Character R) (φ : RootedForest) :
    ((coproductTerms φ).map fun term =>
      χ (antipode (R := R) term.1) * χ.evalForest term.2).sum =
      ForestAlgebra.counitCoeff (R := R) φ := by
  calc
    ((coproductTerms φ).map fun term =>
      χ (antipode (R := R) term.1) * χ.evalForest term.2).sum =
        χ (ForestTensorAlgebra.antipodeLeft (R := R)
          (ForestTensorAlgebra.sumTerms (R := R) (coproductTerms φ))) := by
          rw [ForestTensorAlgebra.evalCharacter_antipodeLeft_sumTerms]
    _ = χ (ForestTensorAlgebra.antipodeLeft (R := R) (coproduct (R := R) φ)) := by
          rw [coproduct_eq_sumTerms_coproductTerms]
    _ = ForestAlgebra.counitCoeff (R := R) φ := by
          rw [antipodeLeft_coproduct]
          simp

/-- Evaluating the full coproduct by the right-recursive antipode on the right gives the counit. -/
theorem antipodeRight_coproduct (φ : RootedForest) :
    ForestTensorAlgebra.antipodeRight (R := R) (coproduct (R := R) φ) =
      ForestAlgebra.counitCoeff (R := R) φ • (1 : ForestAlgebra R) := by
  by_cases hφ : φ = 0
  · subst φ
    rw [coproduct_zero]
    simp only [ForestAlgebra.counitCoeff_zero, one_smul]
    rw [← ForestTensorAlgebra.ofPair_zero (R := R), ForestTensorAlgebra.antipodeRight_ofPair]
    simp
  · rw [ForestAlgebra.counitCoeff_ne_zero hφ, zero_smul]
    rw [coproduct_eq_sumTerms_coproductTerms, ForestTensorAlgebra.antipodeRight_sumTerms]
    have hleft :
        ∀ term ∈ coproductTerms φ, RootedForest.order term.1 = 0 → term = (0, φ) := by
      intro term hterm hzero
      have hleft_zero : term.1 = 0 := (RootedForest.order_eq_zero_iff term.1).1 hzero
      have hright := coproductTerms_left_eq_zero hterm hleft_zero
      cases term with
      | mk left right =>
          simp at hleft_zero hright ⊢
          exact ⟨hleft_zero, hright⟩
    have hright :
        ∀ term ∈ coproductTerms φ, RootedForest.order term.2 = 0 → term = (φ, 0) := by
      intro term hterm hzero
      have hright_zero : term.2 = 0 := (RootedForest.order_eq_zero_iff term.2).1 hzero
      have hleft_eq := coproductTerms_right_eq_zero hterm hright_zero
      cases term with
      | mk left right =>
          simp at hright_zero hleft_eq ⊢
          exact ⟨hleft_eq, hright_zero⟩
    rw [ForestTensorAlgebra.antipodeRight_terms_sum_eq_boundary_add_proper
      (R := R) hφ (coproductTerms φ) hleft hright]
    rw [coproductTerms_leftBoundaryCoproductTerm,
      coproductTerms_rightBoundaryCoproductTerm]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change
      ForestAlgebra.ofForest (R := R) 0 * rightAntipode (R := R) φ +
          ForestAlgebra.ofForest (R := R) φ * rightAntipode (R := R) 0 +
          ((properCoproductTerms φ).map fun term =>
            ForestAlgebra.ofForest (R := R) term.1 * rightAntipode (R := R) term.2).sum =
        0
    rw [← ForestTensorAlgebra.antipodeRight_sumTerms (R := R) (properCoproductTerms φ)]
    change
      ForestAlgebra.ofForest (R := R) 0 * rightAntipode (R := R) φ +
          ForestAlgebra.ofForest (R := R) φ * rightAntipode (R := R) 0 +
          ForestTensorAlgebra.antipodeRight (R := R) (reducedCoproduct (R := R) φ) =
        0
    rw [rightAntipode_zero, ForestAlgebra.ofForest_zero, one_mul, mul_one]
    simpa [add_comm, add_left_comm, add_assoc] using
      rightAntipode_add_ofForest_add_antipodeRight_reducedCoproduct (R := R) hφ

theorem evalCharacter_antipodeRight_coproductTerms
    (χ : ForestAlgebra.Character R) (φ : RootedForest) :
    ((coproductTerms φ).map fun term =>
      χ.evalForest term.1 * χ (rightAntipode (R := R) term.2)).sum =
      ForestAlgebra.counitCoeff (R := R) φ := by
  calc
    ((coproductTerms φ).map fun term =>
      χ.evalForest term.1 * χ (rightAntipode (R := R) term.2)).sum =
        χ (ForestTensorAlgebra.antipodeRight (R := R)
          (ForestTensorAlgebra.sumTerms (R := R) (coproductTerms φ))) := by
          rw [ForestTensorAlgebra.evalCharacter_antipodeRight_sumTerms]
    _ = χ (ForestTensorAlgebra.antipodeRight (R := R) (coproduct (R := R) φ)) := by
          rw [coproduct_eq_sumTerms_coproductTerms]
    _ = ForestAlgebra.counitCoeff (R := R) φ := by
          rw [antipodeRight_coproduct]
          simp

end

end RootedForest

namespace ForestAlgebra

noncomputable section

variable {R : Type u} [CommRing R]

/-- The linear extension of the recursive antipode to the rooted-forest algebra. -/
noncomputable def antipode : ForestAlgebra R →ₗ[R] ForestAlgebra R :=
  (Finsupp.linearCombination R (RootedForest.antipode (R := R))).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem antipode_ofForest (φ : RootedForest) :
    antipode (R := R) (ofForest (R := R) φ) =
      RootedForest.antipode (R := R) φ := by
  rw [antipode, ofForest]
  change (Finsupp.linearCombination R (RootedForest.antipode (R := R)))
      (Finsupp.single φ (1 : R)) = RootedForest.antipode (R := R) φ
  rw [Finsupp.linearCombination_single]
  simp

@[simp]
theorem antipode_zero : antipode (R := R) (0 : ForestAlgebra R) = 0 :=
  LinearMap.map_zero (antipode (R := R))

theorem antipode_add (x y : ForestAlgebra R) :
    antipode (R := R) (x + y) = antipode x + antipode y :=
  LinearMap.map_add (antipode (R := R)) x y

theorem counit_antipode (x : ForestAlgebra R) :
    ForestAlgebra.counit R (antipode (R := R) x) = ForestAlgebra.counit R x := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestAlgebra R =>
      ForestAlgebra.counit R (antipode (R := R) x) = ForestAlgebra.counit R x) x ?_ ?_ ?_
  · intro φ
    change
      ForestAlgebra.counit R (antipode (R := R) (ofForest (R := R) φ)) =
        ForestAlgebra.counit R (ofForest (R := R) φ)
    rw [antipode_ofForest, ForestAlgebra.counit_ofForest, RootedForest.counit_antipode]
  · intro x y hx hy
    rw [antipode_add, map_add, hx, hy, map_add]
  · intro r x hx
    simp [hx]

/-- The linear extension of the right-recursive antipode to the rooted-forest algebra. -/
noncomputable def rightAntipode : ForestAlgebra R →ₗ[R] ForestAlgebra R :=
  (Finsupp.linearCombination R (RootedForest.rightAntipode (R := R))).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem rightAntipode_ofForest (φ : RootedForest) :
    rightAntipode (R := R) (ofForest (R := R) φ) =
      RootedForest.rightAntipode (R := R) φ := by
  rw [rightAntipode, ofForest]
  change (Finsupp.linearCombination R (RootedForest.rightAntipode (R := R)))
      (Finsupp.single φ (1 : R)) = RootedForest.rightAntipode (R := R) φ
  rw [Finsupp.linearCombination_single]
  simp

@[simp]
theorem rightAntipode_zero : rightAntipode (R := R) (0 : ForestAlgebra R) = 0 :=
  LinearMap.map_zero (rightAntipode (R := R))

theorem rightAntipode_add (x y : ForestAlgebra R) :
    rightAntipode (R := R) (x + y) = rightAntipode x + rightAntipode y :=
  LinearMap.map_add (rightAntipode (R := R)) x y

theorem counit_rightAntipode (x : ForestAlgebra R) :
    ForestAlgebra.counit R (rightAntipode (R := R) x) = ForestAlgebra.counit R x := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestAlgebra R =>
      ForestAlgebra.counit R (rightAntipode (R := R) x) = ForestAlgebra.counit R x) x ?_ ?_ ?_
  · intro φ
    change
      ForestAlgebra.counit R (rightAntipode (R := R) (ofForest (R := R) φ)) =
        ForestAlgebra.counit R (ofForest (R := R) φ)
    rw [rightAntipode_ofForest, ForestAlgebra.counit_ofForest,
      RootedForest.counit_rightAntipode]
  · intro x y hx hy
    rw [rightAntipode_add, map_add, hx, hy, map_add]
  · intro r x hx
    simp [hx]

/-- Applying the recursive antipode on the left factor of the algebra coproduct gives the counit. -/
theorem antipodeLeft_coproduct (x : ForestAlgebra R) :
    ForestTensorAlgebra.antipodeLeft (R := R) (ForestAlgebra.coproduct R x) =
      ForestAlgebra.counit R x • (1 : ForestAlgebra R) := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestAlgebra R =>
      ForestTensorAlgebra.antipodeLeft (R := R) (ForestAlgebra.coproduct R x) =
        ForestAlgebra.counit R x • (1 : ForestAlgebra R)) x ?_ ?_ ?_
  · intro φ
    change
      ForestTensorAlgebra.antipodeLeft (R := R)
          (ForestAlgebra.coproduct R (ofForest (R := R) φ)) =
        ForestAlgebra.counit R (ofForest (R := R) φ) • (1 : ForestAlgebra R)
    rw [ForestAlgebra.coproduct_ofForest, ForestAlgebra.counit_ofForest,
      RootedForest.antipodeLeft_coproduct]
  · intro x y hx hy
    simp [hx, hy, add_smul]
  · intro r x hx
    simp [hx, smul_smul]

/-- Applying the right-recursive antipode on the right factor of the algebra coproduct gives the counit. -/
theorem antipodeRight_coproduct (x : ForestAlgebra R) :
    ForestTensorAlgebra.antipodeRight (R := R) (ForestAlgebra.coproduct R x) =
      ForestAlgebra.counit R x • (1 : ForestAlgebra R) := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestAlgebra R =>
      ForestTensorAlgebra.antipodeRight (R := R) (ForestAlgebra.coproduct R x) =
        ForestAlgebra.counit R x • (1 : ForestAlgebra R)) x ?_ ?_ ?_
  · intro φ
    change
      ForestTensorAlgebra.antipodeRight (R := R)
          (ForestAlgebra.coproduct R (ofForest (R := R) φ)) =
        ForestAlgebra.counit R (ofForest (R := R) φ) • (1 : ForestAlgebra R)
    rw [ForestAlgebra.coproduct_ofForest, ForestAlgebra.counit_ofForest,
      RootedForest.antipodeRight_coproduct]
  · intro x y hx hy
    simp [hx, hy, add_smul]
  · intro r x hx
    simp [hx, smul_smul]

namespace Character

theorem eval_antipodeLeft_coproduct (χ : Character R) (x : ForestAlgebra R) :
    χ (ForestTensorAlgebra.antipodeLeft (R := R) (ForestAlgebra.coproduct R x)) =
      ForestAlgebra.counit R x := by
  rw [ForestAlgebra.antipodeLeft_coproduct]
  simp

theorem eval_antipodeRight_coproduct (χ : Character R) (x : ForestAlgebra R) :
    χ (ForestTensorAlgebra.antipodeRight (R := R) (ForestAlgebra.coproduct R x)) =
      ForestAlgebra.counit R x := by
  rw [ForestAlgebra.antipodeRight_coproduct]
  simp

end Character

end

end ForestAlgebra

end HopfAlgebras
