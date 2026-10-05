/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.Antipode
import HopfAlgebras.Hopf.LabelledCoproduct

/-!
# The Labelled BCK Antipode

This file defines the recursive antipode on labelled rooted-forest monomials.

## Main definitions

* `LRootedForest.antipode` - the recursive antipode on labelled rooted forests
* `LRootedForest.antipodeProperSum` - the proper-coproduct part of the recursion
* `LForestAlgebra.antipode` - the linear extension to the labelled forest algebra

## References

* Alain Connes, Dirk Kreimer, *Hopf Algebras, Renormalization and
  Noncommutative Geometry*
* Loic Foissy, *An introduction to Hopf algebras of trees*
-/

namespace HopfAlgebras

universe u v w

namespace LRootedForest

noncomputable section

variable {α : Type u} {R : Type v} [CommRing R]

/-- The recursive BCK antipode on labelled rooted-forest monomials. -/
noncomputable def antipode (φ : LRootedForest α) : LForestAlgebra α R := by
  classical
  exact
    if hφ : φ = 0 then
      1
    else
      -LForestAlgebra.ofForest (R := R) φ -
        ((properCoproductTerms φ).attach.map fun term =>
          antipode term.1.1 *
            LForestAlgebra.ofForest (R := R) term.1.2).sum
termination_by order φ
decreasing_by
  exact properCoproductTerms_left_order_lt term.2

/-- The proper-coproduct sum appearing in the recursive labelled antipode formula. -/
noncomputable def antipodeProperSum (φ : LRootedForest α) : LForestAlgebra α R :=
  ((properCoproductTerms φ).attach.map fun term =>
    antipode (R := R) term.1.1 *
      LForestAlgebra.ofForest (R := R) term.1.2).sum

/-- `antipodeProperSum` with the `attach` plumbing removed. -/
theorem antipodeProperSum_eq_map_sum (φ : LRootedForest α) :
    antipodeProperSum (R := R) φ =
      ((properCoproductTerms φ).map fun term =>
        antipode (R := R) term.1 *
          LForestAlgebra.ofForest (R := R) term.2).sum := by
  rw [antipodeProperSum]
  exact List.sum_attach_map (properCoproductTerms φ) fun term =>
    antipode (R := R) term.1 * LForestAlgebra.ofForest (R := R) term.2

@[simp]
theorem antipode_zero : antipode (α := α) (R := R) 0 = 1 := by
  rw [antipode]
  simp

@[simp]
theorem antipode_empty : antipode (R := R) (LRootedForest.empty : LRootedForest α) = 1 := by
  simp [LRootedForest.empty]

theorem antipode_eq_of_ne_zero {φ : LRootedForest α} (hφ : φ ≠ 0) :
    antipode (R := R) φ =
      -LForestAlgebra.ofForest (R := R) φ - antipodeProperSum (R := R) φ := by
  rw [antipode, antipodeProperSum]
  simp [hφ]

theorem antipode_singleton (τ : LRootedTree α) :
    antipode (R := R) (LRootedForest.singleton τ) =
      -LForestAlgebra.ofForest (R := R) (LRootedForest.singleton τ) -
        antipodeProperSum (R := R) (LRootedForest.singleton τ) :=
  antipode_eq_of_ne_zero (R := R) (LRootedForest.singleton_ne_zero τ)

/-- The symmetric right-recursive BCK antipode on labelled rooted-forest monomials. -/
noncomputable def rightAntipode (φ : LRootedForest α) : LForestAlgebra α R := by
  classical
  exact
    if hφ : φ = 0 then
      1
    else
      -LForestAlgebra.ofForest (R := R) φ -
        ((properCoproductTerms φ).attach.map fun term =>
          LForestAlgebra.ofForest (R := R) term.1.1 *
            rightAntipode term.1.2).sum
termination_by order φ
decreasing_by
  exact properCoproductTerms_right_order_lt term.2

/-- The proper-coproduct sum appearing in the right-recursive labelled antipode formula. -/
noncomputable def rightAntipodeProperSum (φ : LRootedForest α) : LForestAlgebra α R :=
  ((properCoproductTerms φ).attach.map fun term =>
    LForestAlgebra.ofForest (R := R) term.1.1 *
      rightAntipode (R := R) term.1.2).sum

/-- `rightAntipodeProperSum` with the `attach` plumbing removed. -/
theorem rightAntipodeProperSum_eq_map_sum (φ : LRootedForest α) :
    rightAntipodeProperSum (R := R) φ =
      ((properCoproductTerms φ).map fun term =>
        LForestAlgebra.ofForest (R := R) term.1 *
          rightAntipode (R := R) term.2).sum := by
  rw [rightAntipodeProperSum]
  exact List.sum_attach_map (properCoproductTerms φ) fun term =>
    LForestAlgebra.ofForest (R := R) term.1 * rightAntipode (R := R) term.2

@[simp]
theorem rightAntipode_zero : rightAntipode (α := α) (R := R) 0 = 1 := by
  rw [rightAntipode]
  simp

@[simp]
theorem rightAntipode_empty :
    rightAntipode (R := R) (LRootedForest.empty : LRootedForest α) = 1 := by
  simp [LRootedForest.empty]

theorem rightAntipode_eq_of_ne_zero {φ : LRootedForest α} (hφ : φ ≠ 0) :
    rightAntipode (R := R) φ =
      -LForestAlgebra.ofForest (R := R) φ - rightAntipodeProperSum (R := R) φ := by
  rw [rightAntipode, rightAntipodeProperSum]
  simp [hφ]

theorem rightAntipode_singleton (τ : LRootedTree α) :
    rightAntipode (R := R) (LRootedForest.singleton τ) =
      -LForestAlgebra.ofForest (R := R) (LRootedForest.singleton τ) -
        rightAntipodeProperSum (R := R) (LRootedForest.singleton τ) :=
  rightAntipode_eq_of_ne_zero (R := R) (LRootedForest.singleton_ne_zero τ)

theorem counit_rightAntipode (φ : LRootedForest α) :
    LForestAlgebra.counit α R (rightAntipode (R := R) φ) =
      LForestAlgebra.counitCoeff (R := R) φ := by
  by_cases hφ : φ = 0
  · subst φ
    simp
  · have hsum :
        LForestAlgebra.counit α R (rightAntipodeProperSum (R := R) φ) = 0 := by
      rw [rightAntipodeProperSum, map_list_sum]
      apply List.sum_eq_zero
      intro x hx
      rcases List.mem_map.1 hx with ⟨y, hy, rfl⟩
      rcases List.mem_map.1 hy with ⟨term, hterm, rfl⟩
      have hmem : term.1 ∈ properCoproductTerms φ := term.2
      have hproper :
          0 < LRootedForest.order term.1.1 :=
        (of_decide_eq_true (List.mem_filter.1 hmem).2).1
      have hleft : term.1.1 ≠ 0 :=
        (LRootedForest.order_pos_iff_ne_zero term.1.1).1 hproper
      simp [LForestAlgebra.counit_ofForest_ne_zero hleft]
    rw [rightAntipode_eq_of_ne_zero hφ, LForestAlgebra.counitCoeff_ne_zero hφ]
    simp [hsum, LForestAlgebra.counit_ofForest_ne_zero hφ]

theorem eraseLabels_antipode (φ : LRootedForest α) :
    LForestAlgebra.eraseLabels (α := α) R (antipode (R := R) φ) =
      RootedForest.antipode (R := R) (LRootedForest.erase φ) := by
  classical
  have hmain :
      ∀ n : Nat, ∀ φ : LRootedForest α, LRootedForest.order φ = n →
        LForestAlgebra.eraseLabels (α := α) R (antipode (R := R) φ) =
          RootedForest.antipode (R := R) (LRootedForest.erase φ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro φ hφn
        by_cases hφ : φ = 0
        · subst φ
          rw [show LRootedForest.erase (0 : LRootedForest α) = 0 by rfl]
          simp
        · have hpos : 0 < LRootedForest.order φ :=
            (LRootedForest.order_pos_iff_ne_zero φ).2 hφ
          have herase_pos : 0 < RootedForest.order (LRootedForest.erase φ) := by
            simpa [LRootedForest.order_erase] using hpos
          have herase : LRootedForest.erase φ ≠ 0 :=
            (RootedForest.order_pos_iff_ne_zero _).1 herase_pos
          have hterm :
              ∀ term ∈ LRootedForest.properCoproductTerms φ,
                LForestAlgebra.eraseLabels (α := α) R
                    (antipode (R := R) term.1 *
                      LForestAlgebra.ofForest (R := R) term.2) =
                  RootedForest.antipode (R := R) (LRootedForest.erase term.1) *
                    ForestAlgebra.ofForest (R := R) (LRootedForest.erase term.2) := by
            intro term hmem
            have hlt : LRootedForest.order term.1 < n := by
              rw [← hφn]
              exact LRootedForest.properCoproductTerms_left_order_lt hmem
            have hrec := ih (LRootedForest.order term.1) hlt term.1 rfl
            simp [hrec]
          have hsum :
              LForestAlgebra.eraseLabels (α := α) R
                  (antipodeProperSum (R := R) φ) =
                RootedForest.antipodeProperSum (R := R) (LRootedForest.erase φ) := by
            rw [LRootedForest.antipodeProperSum_eq_map_sum, map_list_sum,
              List.map_map, RootedForest.antipodeProperSum_eq_map_sum,
              ← List.Perm.sum_eq
                ((LRootedForest.properCoproductTerms_erase_perm φ).map
                  fun term => RootedForest.antipode (R := R) term.1 *
                    ForestAlgebra.ofForest (R := R) term.2),
              List.map_map]
            refine congrArg List.sum (List.map_congr_left fun term hmem => ?_)
            simpa [PLTree.eraseCoproductTerm] using hterm term hmem
          rw [LRootedForest.antipode_eq_of_ne_zero hφ,
            RootedForest.antipode_eq_of_ne_zero herase]
          simp [hsum]
  exact hmain (LRootedForest.order φ) φ rfl

theorem counit_antipode (φ : LRootedForest α) :
    LForestAlgebra.counit α R (antipode (R := R) φ) =
      LForestAlgebra.counitCoeff (R := R) φ := by
  calc
    LForestAlgebra.counit α R (antipode (R := R) φ) =
        ForestAlgebra.counit R
          (LForestAlgebra.eraseLabels (α := α) R (antipode (R := R) φ)) := by
          simpa [AlgHom.comp_apply] using
            congrArg (fun f => f (antipode (R := R) φ))
              (LForestAlgebra.counit_comp_eraseLabels (α := α) (R := R)).symm
    _ = ForestAlgebra.counit R (RootedForest.antipode (R := R) (LRootedForest.erase φ)) := by
          rw [eraseLabels_antipode]
    _ = ForestAlgebra.counitCoeff (R := R) (LRootedForest.erase φ) := by
          rw [RootedForest.counit_antipode]
    _ = LForestAlgebra.counitCoeff (R := R) φ :=
          LForestAlgebra.counitCoeff_erase φ

theorem mapLabels_antipode {β : Type w} (f : α → β) (φ : LRootedForest α) :
    LForestAlgebra.mapLabels (R := R) f (antipode (R := R) φ) =
      antipode (R := R) (LRootedForest.mapLabels f φ) := by
  classical
  have hmain :
      ∀ n : Nat, ∀ φ : LRootedForest α, LRootedForest.order φ = n →
        LForestAlgebra.mapLabels (R := R) f (antipode (R := R) φ) =
          antipode (R := R) (LRootedForest.mapLabels f φ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro φ hφn
        by_cases hφ : φ = 0
        · subst φ
          rw [show LRootedForest.mapLabels f (0 : LRootedForest α) = 0 by rfl]
          simp
        · have hpos : 0 < LRootedForest.order φ :=
            (LRootedForest.order_pos_iff_ne_zero φ).2 hφ
          have hmap_pos : 0 < LRootedForest.order (LRootedForest.mapLabels f φ) := by
            simpa [LRootedForest.order_mapLabels] using hpos
          have hmap : LRootedForest.mapLabels f φ ≠ 0 :=
            (LRootedForest.order_pos_iff_ne_zero _).1 hmap_pos
          have hterm :
              ∀ term ∈ LRootedForest.properCoproductTerms φ,
                LForestAlgebra.mapLabels (R := R) f
                    (antipode (R := R) term.1 *
                      LForestAlgebra.ofForest (R := R) term.2) =
                  antipode (R := R) (LRootedForest.mapLabels f term.1) *
                    LForestAlgebra.ofForest (R := R) (LRootedForest.mapLabels f term.2) := by
            intro term hmem
            have hlt : LRootedForest.order term.1 < n := by
              rw [← hφn]
              exact LRootedForest.properCoproductTerms_left_order_lt hmem
            have hrec := ih (LRootedForest.order term.1) hlt term.1 rfl
            simp [hrec]
          have hsum :
              LForestAlgebra.mapLabels (R := R) f (antipodeProperSum (R := R) φ) =
                antipodeProperSum (R := R) (LRootedForest.mapLabels f φ) := by
            rw [LRootedForest.antipodeProperSum_eq_map_sum, map_list_sum,
              List.map_map, LRootedForest.antipodeProperSum_eq_map_sum,
              ← List.Perm.sum_eq
                ((LRootedForest.properCoproductTerms_mapLabels_perm f φ).map
                  fun term => antipode (R := R) term.1 *
                    LForestAlgebra.ofForest (R := R) term.2),
              List.map_map]
            refine congrArg List.sum (List.map_congr_left fun term hmem => ?_)
            simpa [PLTree.mapCoproductTerm] using hterm term hmem
          rw [LRootedForest.antipode_eq_of_ne_zero hφ,
            LRootedForest.antipode_eq_of_ne_zero hmap]
          simp [hsum]
  exact hmain (LRootedForest.order φ) φ rfl

theorem constLabel_antipode (a : α) (φ : RootedForest) :
    LForestAlgebra.constLabel a R (RootedForest.antipode (R := R) φ) =
      antipode (R := R) (LRootedForest.constLabel a φ) := by
  classical
  have hmain :
      ∀ n : Nat, ∀ φ : RootedForest, RootedForest.order φ = n →
        LForestAlgebra.constLabel a R (RootedForest.antipode (R := R) φ) =
          antipode (R := R) (LRootedForest.constLabel a φ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro φ hφn
        by_cases hφ : φ = 0
        · subst φ
          rw [show LRootedForest.constLabel a (0 : RootedForest) = 0 by rfl]
          simp
        · have hpos : 0 < RootedForest.order φ :=
            (RootedForest.order_pos_iff_ne_zero φ).2 hφ
          have hlabel_pos : 0 < LRootedForest.order (LRootedForest.constLabel a φ) := by
            simpa [LRootedForest.order_constLabel] using hpos
          have hlabel : LRootedForest.constLabel a φ ≠ 0 :=
            (LRootedForest.order_pos_iff_ne_zero _).1 hlabel_pos
          have hterm :
              ∀ term ∈ RootedForest.properCoproductTerms φ,
                LForestAlgebra.constLabel a R
                    (RootedForest.antipode (R := R) term.1 *
                      ForestAlgebra.ofForest (R := R) term.2) =
                  antipode (R := R) (LRootedForest.constLabel a term.1) *
                    LForestAlgebra.ofForest (R := R) (LRootedForest.constLabel a term.2) := by
            intro term hmem
            have hlt : RootedForest.order term.1 < n := by
              rw [← hφn]
              exact RootedForest.properCoproductTerms_left_order_lt hmem
            have hrec := ih (RootedForest.order term.1) hlt term.1 rfl
            simp [hrec]
          have hsum :
              LForestAlgebra.constLabel a R (RootedForest.antipodeProperSum (R := R) φ) =
                antipodeProperSum (R := R) (LRootedForest.constLabel a φ) := by
            rw [RootedForest.antipodeProperSum_eq_map_sum, map_list_sum,
              List.map_map, LRootedForest.antipodeProperSum_eq_map_sum,
              ← List.Perm.sum_eq
                ((LRootedForest.properCoproductTerms_constLabel_perm a φ).map
                  fun term => antipode (R := R) term.1 *
                    LForestAlgebra.ofForest (R := R) term.2),
              List.map_map]
            refine congrArg List.sum (List.map_congr_left fun term hmem => ?_)
            simpa [PLTree.constLabelCoproductTerm] using hterm term hmem
          rw [RootedForest.antipode_eq_of_ne_zero hφ,
            LRootedForest.antipode_eq_of_ne_zero hlabel]
          simp [hsum]
  exact hmain (RootedForest.order φ) φ rfl

theorem eraseLabels_rightAntipode (φ : LRootedForest α) :
    LForestAlgebra.eraseLabels (α := α) R (rightAntipode (R := R) φ) =
      RootedForest.rightAntipode (R := R) (LRootedForest.erase φ) := by
  classical
  have hmain :
      ∀ n : Nat, ∀ φ : LRootedForest α, LRootedForest.order φ = n →
        LForestAlgebra.eraseLabels (α := α) R (rightAntipode (R := R) φ) =
          RootedForest.rightAntipode (R := R) (LRootedForest.erase φ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro φ hφn
        by_cases hφ : φ = 0
        · subst φ
          rw [show LRootedForest.erase (0 : LRootedForest α) = 0 by rfl]
          simp
        · have hpos : 0 < LRootedForest.order φ :=
            (LRootedForest.order_pos_iff_ne_zero φ).2 hφ
          have herase_pos : 0 < RootedForest.order (LRootedForest.erase φ) := by
            simpa [LRootedForest.order_erase] using hpos
          have herase : LRootedForest.erase φ ≠ 0 :=
            (RootedForest.order_pos_iff_ne_zero _).1 herase_pos
          have hterm :
              ∀ term ∈ LRootedForest.properCoproductTerms φ,
                LForestAlgebra.eraseLabels (α := α) R
                    (LForestAlgebra.ofForest (R := R) term.1 *
                      rightAntipode (R := R) term.2) =
                  ForestAlgebra.ofForest (R := R) (LRootedForest.erase term.1) *
                    RootedForest.rightAntipode (R := R) (LRootedForest.erase term.2) := by
            intro term hmem
            have hlt : LRootedForest.order term.2 < n := by
              rw [← hφn]
              exact LRootedForest.properCoproductTerms_right_order_lt hmem
            have hrec := ih (LRootedForest.order term.2) hlt term.2 rfl
            simp [hrec]
          have hsum :
              LForestAlgebra.eraseLabels (α := α) R
                  (rightAntipodeProperSum (R := R) φ) =
                RootedForest.rightAntipodeProperSum (R := R) (LRootedForest.erase φ) := by
            rw [LRootedForest.rightAntipodeProperSum_eq_map_sum, map_list_sum,
              List.map_map, RootedForest.rightAntipodeProperSum_eq_map_sum,
              ← List.Perm.sum_eq
                ((LRootedForest.properCoproductTerms_erase_perm φ).map
                  fun term => ForestAlgebra.ofForest (R := R) term.1 *
                    RootedForest.rightAntipode (R := R) term.2),
              List.map_map]
            refine congrArg List.sum (List.map_congr_left fun term hmem => ?_)
            simpa [PLTree.eraseCoproductTerm] using hterm term hmem
          rw [LRootedForest.rightAntipode_eq_of_ne_zero hφ,
            RootedForest.rightAntipode_eq_of_ne_zero herase]
          simp [hsum]
  exact hmain (LRootedForest.order φ) φ rfl

theorem mapLabels_rightAntipode {β : Type w} (f : α → β) (φ : LRootedForest α) :
    LForestAlgebra.mapLabels (R := R) f (rightAntipode (R := R) φ) =
      rightAntipode (R := R) (LRootedForest.mapLabels f φ) := by
  classical
  have hmain :
      ∀ n : Nat, ∀ φ : LRootedForest α, LRootedForest.order φ = n →
        LForestAlgebra.mapLabels (R := R) f (rightAntipode (R := R) φ) =
          rightAntipode (R := R) (LRootedForest.mapLabels f φ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro φ hφn
        by_cases hφ : φ = 0
        · subst φ
          rw [show LRootedForest.mapLabels f (0 : LRootedForest α) = 0 by rfl]
          simp
        · have hpos : 0 < LRootedForest.order φ :=
            (LRootedForest.order_pos_iff_ne_zero φ).2 hφ
          have hmap_pos : 0 < LRootedForest.order (LRootedForest.mapLabels f φ) := by
            simpa [LRootedForest.order_mapLabels] using hpos
          have hmap : LRootedForest.mapLabels f φ ≠ 0 :=
            (LRootedForest.order_pos_iff_ne_zero _).1 hmap_pos
          have hterm :
              ∀ term ∈ LRootedForest.properCoproductTerms φ,
                LForestAlgebra.mapLabels (R := R) f
                    (LForestAlgebra.ofForest (R := R) term.1 *
                      rightAntipode (R := R) term.2) =
                  LForestAlgebra.ofForest (R := R) (LRootedForest.mapLabels f term.1) *
                    rightAntipode (R := R) (LRootedForest.mapLabels f term.2) := by
            intro term hmem
            have hlt : LRootedForest.order term.2 < n := by
              rw [← hφn]
              exact LRootedForest.properCoproductTerms_right_order_lt hmem
            have hrec := ih (LRootedForest.order term.2) hlt term.2 rfl
            simp [hrec]
          have hsum :
              LForestAlgebra.mapLabels (R := R) f (rightAntipodeProperSum (R := R) φ) =
                rightAntipodeProperSum (R := R) (LRootedForest.mapLabels f φ) := by
            rw [LRootedForest.rightAntipodeProperSum_eq_map_sum, map_list_sum,
              List.map_map, LRootedForest.rightAntipodeProperSum_eq_map_sum,
              ← List.Perm.sum_eq
                ((LRootedForest.properCoproductTerms_mapLabels_perm f φ).map
                  fun term => LForestAlgebra.ofForest (R := R) term.1 *
                    rightAntipode (R := R) term.2),
              List.map_map]
            refine congrArg List.sum (List.map_congr_left fun term hmem => ?_)
            simpa [PLTree.mapCoproductTerm] using hterm term hmem
          rw [LRootedForest.rightAntipode_eq_of_ne_zero hφ,
            LRootedForest.rightAntipode_eq_of_ne_zero hmap]
          simp [hsum]
  exact hmain (LRootedForest.order φ) φ rfl

theorem constLabel_rightAntipode (a : α) (φ : RootedForest) :
    LForestAlgebra.constLabel a R (RootedForest.rightAntipode (R := R) φ) =
      rightAntipode (R := R) (LRootedForest.constLabel a φ) := by
  classical
  have hmain :
      ∀ n : Nat, ∀ φ : RootedForest, RootedForest.order φ = n →
        LForestAlgebra.constLabel a R (RootedForest.rightAntipode (R := R) φ) =
          rightAntipode (R := R) (LRootedForest.constLabel a φ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro φ hφn
        by_cases hφ : φ = 0
        · subst φ
          rw [show LRootedForest.constLabel a (0 : RootedForest) = 0 by rfl]
          simp
        · have hpos : 0 < RootedForest.order φ :=
            (RootedForest.order_pos_iff_ne_zero φ).2 hφ
          have hlabel_pos : 0 < LRootedForest.order (LRootedForest.constLabel a φ) := by
            simpa [LRootedForest.order_constLabel] using hpos
          have hlabel : LRootedForest.constLabel a φ ≠ 0 :=
            (LRootedForest.order_pos_iff_ne_zero _).1 hlabel_pos
          have hterm :
              ∀ term ∈ RootedForest.properCoproductTerms φ,
                LForestAlgebra.constLabel a R
                    (ForestAlgebra.ofForest (R := R) term.1 *
                      RootedForest.rightAntipode (R := R) term.2) =
                  LForestAlgebra.ofForest (R := R) (LRootedForest.constLabel a term.1) *
                    rightAntipode (R := R) (LRootedForest.constLabel a term.2) := by
            intro term hmem
            have hlt : RootedForest.order term.2 < n := by
              rw [← hφn]
              exact RootedForest.properCoproductTerms_right_order_lt hmem
            have hrec := ih (RootedForest.order term.2) hlt term.2 rfl
            simp [hrec]
          have hsum :
              LForestAlgebra.constLabel a R
                  (RootedForest.rightAntipodeProperSum (R := R) φ) =
                rightAntipodeProperSum (R := R) (LRootedForest.constLabel a φ) := by
            rw [RootedForest.rightAntipodeProperSum_eq_map_sum, map_list_sum,
              List.map_map, LRootedForest.rightAntipodeProperSum_eq_map_sum,
              ← List.Perm.sum_eq
                ((LRootedForest.properCoproductTerms_constLabel_perm a φ).map
                  fun term => LForestAlgebra.ofForest (R := R) term.1 *
                    rightAntipode (R := R) term.2),
              List.map_map]
            refine congrArg List.sum (List.map_congr_left fun term hmem => ?_)
            simpa [PLTree.constLabelCoproductTerm] using hterm term hmem
          rw [RootedForest.rightAntipode_eq_of_ne_zero hφ,
            LRootedForest.rightAntipode_eq_of_ne_zero hlabel]
          simp [hsum]
  exact hmain (RootedForest.order φ) φ rfl

end

end LRootedForest

namespace LForestTensorAlgebra

noncomputable section

variable {α : Type u} {R : Type v} [CommRing R]

/-- Evaluate a tensor term by applying the labelled antipode to the left factor
and multiplying in the labelled forest algebra. -/
noncomputable def antipodeLeft : LForestTensorAlgebra α R →ₗ[R] LForestAlgebra α R :=
  (Finsupp.linearCombination R fun term : LRootedForest α × LRootedForest α =>
    LRootedForest.antipode (R := R) term.1 *
      LForestAlgebra.ofForest (R := R) term.2).comp
        (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem antipodeLeft_ofPair (term : LRootedForest α × LRootedForest α) :
    antipodeLeft (R := R) (ofPair (R := R) term) =
      LRootedForest.antipode (R := R) term.1 *
        LForestAlgebra.ofForest (R := R) term.2 := by
  rw [antipodeLeft, ofPair]
  change (Finsupp.linearCombination R fun term : LRootedForest α × LRootedForest α =>
      LRootedForest.antipode (R := R) term.1 *
        LForestAlgebra.ofForest (R := R) term.2)
      (Finsupp.single term (1 : R)) =
    LRootedForest.antipode (R := R) term.1 *
      LForestAlgebra.ofForest (R := R) term.2
  rw [Finsupp.linearCombination_single]
  simp

theorem antipodeLeft_sumTerms (terms : List (LRootedForest α × LRootedForest α)) :
    antipodeLeft (R := R) (sumTerms (R := R) terms) =
      (terms.map fun term =>
        LRootedForest.antipode (R := R) term.1 *
          LForestAlgebra.ofForest (R := R) term.2).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, antipodeLeft_ofPair, ih]
      rfl

theorem evalCharacter_antipodeLeft_sumTerms
    (χ : LForestAlgebra.Character α R)
    (terms : List (LRootedForest α × LRootedForest α)) :
    χ (antipodeLeft (R := R) (sumTerms (R := R) terms)) =
      (terms.map fun term =>
        χ (LRootedForest.antipode (R := R) term.1) *
          χ.evalForest term.2).sum := by
  rw [antipodeLeft_sumTerms, map_list_sum]
  simp [Function.comp_def, LForestAlgebra.Character.evalForest]

/-- Evaluate a labelled tensor term by applying the right-recursive antipode to the right factor. -/
noncomputable def antipodeRight : LForestTensorAlgebra α R →ₗ[R] LForestAlgebra α R :=
  (Finsupp.linearCombination R fun term : LRootedForest α × LRootedForest α =>
    LForestAlgebra.ofForest (R := R) term.1 *
      LRootedForest.rightAntipode (R := R) term.2).comp
        (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem antipodeRight_ofPair (term : LRootedForest α × LRootedForest α) :
    antipodeRight (R := R) (ofPair (R := R) term) =
      LForestAlgebra.ofForest (R := R) term.1 *
        LRootedForest.rightAntipode (R := R) term.2 := by
  rw [antipodeRight, ofPair]
  change (Finsupp.linearCombination R fun term : LRootedForest α × LRootedForest α =>
      LForestAlgebra.ofForest (R := R) term.1 *
        LRootedForest.rightAntipode (R := R) term.2)
      (Finsupp.single term (1 : R)) =
    LForestAlgebra.ofForest (R := R) term.1 *
      LRootedForest.rightAntipode (R := R) term.2
  rw [Finsupp.linearCombination_single]
  simp

theorem antipodeRight_sumTerms (terms : List (LRootedForest α × LRootedForest α)) :
    antipodeRight (R := R) (sumTerms (R := R) terms) =
      (terms.map fun term =>
        LForestAlgebra.ofForest (R := R) term.1 *
          LRootedForest.rightAntipode (R := R) term.2).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, antipodeRight_ofPair, ih]
      rfl

theorem evalCharacter_antipodeRight_sumTerms
    (χ : LForestAlgebra.Character α R)
    (terms : List (LRootedForest α × LRootedForest α)) :
    χ (antipodeRight (R := R) (sumTerms (R := R) terms)) =
      (terms.map fun term =>
        χ.evalForest term.1 *
          χ (LRootedForest.rightAntipode (R := R) term.2)).sum := by
  rw [antipodeRight_sumTerms, map_list_sum]
  simp [Function.comp_def, LForestAlgebra.Character.evalForest]

private theorem antipodeLeft_terms_sum_eq_boundary_add_proper
    {φ : LRootedForest α} (hφ : φ ≠ 0) :
    ∀ terms : List (LRootedForest α × LRootedForest α),
      (∀ term ∈ terms, LRootedForest.order term.1 = 0 → term = (0, φ)) →
      (∀ term ∈ terms, LRootedForest.order term.2 = 0 → term = (φ, 0)) →
        (terms.map fun term =>
          LRootedForest.antipode (R := R) term.1 *
            LForestAlgebra.ofForest (R := R) term.2).sum =
          ((terms.filterMap PLTree.leftBoundaryCoproductTerm?).map fun term =>
            LRootedForest.antipode (R := R) term.1 *
              LForestAlgebra.ofForest (R := R) term.2).sum +
          ((terms.filterMap PLTree.rightBoundaryCoproductTerm?).map fun term =>
            LRootedForest.antipode (R := R) term.1 *
              LForestAlgebra.ofForest (R := R) term.2).sum +
          (((terms.filter fun term =>
              0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2).map fun term =>
            LRootedForest.antipode (R := R) term.1 *
              LForestAlgebra.ofForest (R := R) term.2).sum)
  | [], _hleft, _hright => by
      simp [PLTree.leftBoundaryCoproductTerm?, PLTree.rightBoundaryCoproductTerm?]
  | term :: terms, hleft, hright => by
      have hleft_tail :
          ∀ term' ∈ terms, LRootedForest.order term'.1 = 0 → term' = (0, φ) := by
        intro term' hmem hzero
        exact hleft term' (by simp [hmem]) hzero
      have hright_tail :
          ∀ term' ∈ terms, LRootedForest.order term'.2 = 0 → term' = (φ, 0) := by
        intro term' hmem hzero
        exact hright term' (by simp [hmem]) hzero
      have ih := antipodeLeft_terms_sum_eq_boundary_add_proper hφ
        terms hleft_tail hright_tail
      have hφ_order : LRootedForest.order φ ≠ 0 := by
        intro hzero
        exact hφ ((LRootedForest.order_eq_zero_iff φ).1 hzero)
      by_cases hterm_left : LRootedForest.order term.1 = 0
      · have hterm : term = (0, φ) := hleft term (by simp) hterm_left
        subst term
        simp [PLTree.leftBoundaryCoproductTerm?, PLTree.rightBoundaryCoproductTerm?,
          hφ_order, ih]
        abel
      · by_cases hterm_right : LRootedForest.order term.2 = 0
        · have hterm : term = (φ, 0) := hright term (by simp) hterm_right
          subst term
          simp [PLTree.leftBoundaryCoproductTerm?, PLTree.rightBoundaryCoproductTerm?,
            hφ_order, ih]
          abel
        · have hproper :
              0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2 := by
            exact ⟨Nat.pos_of_ne_zero hterm_left, Nat.pos_of_ne_zero hterm_right⟩
          simp [PLTree.leftBoundaryCoproductTerm?, PLTree.rightBoundaryCoproductTerm?,
            hterm_left, hterm_right, hproper, ih]
          abel

private theorem antipodeRight_terms_sum_eq_boundary_add_proper
    {φ : LRootedForest α} (hφ : φ ≠ 0) :
    ∀ terms : List (LRootedForest α × LRootedForest α),
      (∀ term ∈ terms, LRootedForest.order term.1 = 0 → term = (0, φ)) →
      (∀ term ∈ terms, LRootedForest.order term.2 = 0 → term = (φ, 0)) →
        (terms.map fun term =>
          LForestAlgebra.ofForest (R := R) term.1 *
            LRootedForest.rightAntipode (R := R) term.2).sum =
          ((terms.filterMap PLTree.leftBoundaryCoproductTerm?).map fun term =>
            LForestAlgebra.ofForest (R := R) term.1 *
              LRootedForest.rightAntipode (R := R) term.2).sum +
          ((terms.filterMap PLTree.rightBoundaryCoproductTerm?).map fun term =>
            LForestAlgebra.ofForest (R := R) term.1 *
              LRootedForest.rightAntipode (R := R) term.2).sum +
          (((terms.filter fun term =>
              0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2).map fun term =>
            LForestAlgebra.ofForest (R := R) term.1 *
              LRootedForest.rightAntipode (R := R) term.2).sum)
  | [], _hleft, _hright => by
      simp [PLTree.leftBoundaryCoproductTerm?, PLTree.rightBoundaryCoproductTerm?]
  | term :: terms, hleft, hright => by
      have hleft_tail :
          ∀ term' ∈ terms, LRootedForest.order term'.1 = 0 → term' = (0, φ) := by
        intro term' hmem hzero
        exact hleft term' (by simp [hmem]) hzero
      have hright_tail :
          ∀ term' ∈ terms, LRootedForest.order term'.2 = 0 → term' = (φ, 0) := by
        intro term' hmem hzero
        exact hright term' (by simp [hmem]) hzero
      have ih := antipodeRight_terms_sum_eq_boundary_add_proper hφ
        terms hleft_tail hright_tail
      have hφ_order : LRootedForest.order φ ≠ 0 := by
        intro hzero
        exact hφ ((LRootedForest.order_eq_zero_iff φ).1 hzero)
      by_cases hterm_left : LRootedForest.order term.1 = 0
      · have hterm : term = (0, φ) := hleft term (by simp) hterm_left
        subst term
        simp [PLTree.leftBoundaryCoproductTerm?, PLTree.rightBoundaryCoproductTerm?,
          hφ_order, ih]
        abel
      · by_cases hterm_right : LRootedForest.order term.2 = 0
        · have hterm : term = (φ, 0) := hright term (by simp) hterm_right
          subst term
          simp [PLTree.leftBoundaryCoproductTerm?, PLTree.rightBoundaryCoproductTerm?,
            hφ_order, ih]
          abel
        · have hproper :
              0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2 := by
            exact ⟨Nat.pos_of_ne_zero hterm_left, Nat.pos_of_ne_zero hterm_right⟩
          simp [PLTree.leftBoundaryCoproductTerm?, PLTree.rightBoundaryCoproductTerm?,
            hterm_left, hterm_right, hproper, ih]
          abel

end

end LForestTensorAlgebra

namespace LRootedForest

noncomputable section

variable {α : Type u} {R : Type v} [CommRing R]

theorem antipodeLeft_reducedCoproduct (φ : LRootedForest α) :
    LForestTensorAlgebra.antipodeLeft (R := R)
        (reducedCoproduct (R := R) φ) =
      antipodeProperSum (R := R) φ := by
  rw [reducedCoproduct, LForestTensorAlgebra.antipodeLeft_sumTerms,
    LRootedForest.antipodeProperSum_eq_map_sum]

theorem antipodeLeft_reducedCoproduct_eq_neg {φ : LRootedForest α} (hφ : φ ≠ 0) :
    LForestTensorAlgebra.antipodeLeft (R := R)
        (reducedCoproduct (R := R) φ) =
      -LForestAlgebra.ofForest (R := R) φ - antipode (R := R) φ := by
  rw [antipodeLeft_reducedCoproduct, antipode_eq_of_ne_zero hφ]
  abel

theorem antipode_add_ofForest_add_antipodeLeft_reducedCoproduct
    {φ : LRootedForest α} (hφ : φ ≠ 0) :
    antipode (R := R) φ + LForestAlgebra.ofForest (R := R) φ +
        LForestTensorAlgebra.antipodeLeft (R := R)
          (reducedCoproduct (R := R) φ) = 0 := by
  rw [antipodeLeft_reducedCoproduct, antipode_eq_of_ne_zero hφ]
  abel

theorem antipodeRight_reducedCoproduct (φ : LRootedForest α) :
    LForestTensorAlgebra.antipodeRight (R := R)
        (reducedCoproduct (R := R) φ) =
      rightAntipodeProperSum (R := R) φ := by
  rw [reducedCoproduct, LForestTensorAlgebra.antipodeRight_sumTerms,
    LRootedForest.rightAntipodeProperSum_eq_map_sum]

theorem antipodeRight_reducedCoproduct_eq_neg {φ : LRootedForest α} (hφ : φ ≠ 0) :
    LForestTensorAlgebra.antipodeRight (R := R)
        (reducedCoproduct (R := R) φ) =
      -LForestAlgebra.ofForest (R := R) φ - rightAntipode (R := R) φ := by
  rw [antipodeRight_reducedCoproduct, rightAntipode_eq_of_ne_zero hφ]
  abel

theorem rightAntipode_add_ofForest_add_antipodeRight_reducedCoproduct
    {φ : LRootedForest α} (hφ : φ ≠ 0) :
    rightAntipode (R := R) φ + LForestAlgebra.ofForest (R := R) φ +
        LForestTensorAlgebra.antipodeRight (R := R)
          (reducedCoproduct (R := R) φ) = 0 := by
  rw [antipodeRight_reducedCoproduct, rightAntipode_eq_of_ne_zero hφ]
  abel

/-- Evaluating the full labelled coproduct by the labelled antipode on the left gives the counit. -/
theorem antipodeLeft_coproduct (φ : LRootedForest α) :
    LForestTensorAlgebra.antipodeLeft (R := R) (coproduct (R := R) φ) =
      LForestAlgebra.counitCoeff (R := R) φ • (1 : LForestAlgebra α R) := by
  by_cases hφ : φ = 0
  · subst φ
    rw [coproduct_zero]
    simp only [LForestAlgebra.counitCoeff_zero, one_smul]
    rw [← LForestTensorAlgebra.ofPair_zero (R := R),
      LForestTensorAlgebra.antipodeLeft_ofPair]
    simp
  · rw [LForestAlgebra.counitCoeff_ne_zero hφ, zero_smul]
    rw [coproduct_eq_sumTerms_coproductTerms, LForestTensorAlgebra.antipodeLeft_sumTerms]
    have hleft :
        ∀ term ∈ coproductTerms φ, LRootedForest.order term.1 = 0 → term = (0, φ) := by
      intro term hterm hzero
      have hleft_zero : term.1 = 0 := (LRootedForest.order_eq_zero_iff term.1).1 hzero
      have hright := coproductTerms_left_eq_zero hterm hleft_zero
      cases term with
      | mk left right =>
          simp at hleft_zero hright ⊢
          exact ⟨hleft_zero, hright⟩
    have hright :
        ∀ term ∈ coproductTerms φ, LRootedForest.order term.2 = 0 → term = (φ, 0) := by
      intro term hterm hzero
      have hright_zero : term.2 = 0 := (LRootedForest.order_eq_zero_iff term.2).1 hzero
      have hleft_eq := coproductTerms_right_eq_zero hterm hright_zero
      cases term with
      | mk left right =>
          simp at hright_zero hleft_eq ⊢
          exact ⟨hleft_eq, hright_zero⟩
    rw [LForestTensorAlgebra.antipodeLeft_terms_sum_eq_boundary_add_proper
      (R := R) hφ (coproductTerms φ) hleft hright]
    rw [coproductTerms_leftBoundaryCoproductTerm,
      coproductTerms_rightBoundaryCoproductTerm]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change
      antipode (R := R) 0 * LForestAlgebra.ofForest (R := R) φ +
          antipode (R := R) φ * LForestAlgebra.ofForest (R := R) 0 +
          ((properCoproductTerms φ).map fun term =>
            antipode (R := R) term.1 * LForestAlgebra.ofForest (R := R) term.2).sum =
        0
    rw [← LForestTensorAlgebra.antipodeLeft_sumTerms (R := R) (properCoproductTerms φ)]
    change
      antipode (R := R) 0 * LForestAlgebra.ofForest (R := R) φ +
          antipode (R := R) φ * LForestAlgebra.ofForest (R := R) 0 +
          LForestTensorAlgebra.antipodeLeft (R := R) (reducedCoproduct (R := R) φ) =
        0
    rw [antipode_zero, LForestAlgebra.ofForest_zero, one_mul, mul_one]
    simpa [add_comm, add_left_comm, add_assoc] using
      antipode_add_ofForest_add_antipodeLeft_reducedCoproduct (R := R) hφ

theorem evalCharacter_antipodeLeft_coproductTerms
    (χ : LForestAlgebra.Character α R) (φ : LRootedForest α) :
    ((coproductTerms φ).map fun term =>
      χ (antipode (R := R) term.1) * χ.evalForest term.2).sum =
      LForestAlgebra.counitCoeff (R := R) φ := by
  calc
    ((coproductTerms φ).map fun term =>
      χ (antipode (R := R) term.1) * χ.evalForest term.2).sum =
        χ (LForestTensorAlgebra.antipodeLeft (R := R)
          (LForestTensorAlgebra.sumTerms (R := R) (coproductTerms φ))) := by
          rw [LForestTensorAlgebra.evalCharacter_antipodeLeft_sumTerms]
    _ = χ (LForestTensorAlgebra.antipodeLeft (R := R) (coproduct (R := R) φ)) := by
          rw [coproduct_eq_sumTerms_coproductTerms]
    _ = LForestAlgebra.counitCoeff (R := R) φ := by
          rw [antipodeLeft_coproduct]
          simp

/-- Evaluating the full labelled coproduct by the right-recursive antipode gives the counit. -/
theorem antipodeRight_coproduct (φ : LRootedForest α) :
    LForestTensorAlgebra.antipodeRight (R := R) (coproduct (R := R) φ) =
      LForestAlgebra.counitCoeff (R := R) φ • (1 : LForestAlgebra α R) := by
  by_cases hφ : φ = 0
  · subst φ
    rw [coproduct_zero]
    simp only [LForestAlgebra.counitCoeff_zero, one_smul]
    rw [← LForestTensorAlgebra.ofPair_zero (R := R),
      LForestTensorAlgebra.antipodeRight_ofPair]
    simp
  · rw [LForestAlgebra.counitCoeff_ne_zero hφ, zero_smul]
    rw [coproduct_eq_sumTerms_coproductTerms, LForestTensorAlgebra.antipodeRight_sumTerms]
    have hleft :
        ∀ term ∈ coproductTerms φ, LRootedForest.order term.1 = 0 → term = (0, φ) := by
      intro term hterm hzero
      have hleft_zero : term.1 = 0 := (LRootedForest.order_eq_zero_iff term.1).1 hzero
      have hright := coproductTerms_left_eq_zero hterm hleft_zero
      cases term with
      | mk left right =>
          simp at hleft_zero hright ⊢
          exact ⟨hleft_zero, hright⟩
    have hright :
        ∀ term ∈ coproductTerms φ, LRootedForest.order term.2 = 0 → term = (φ, 0) := by
      intro term hterm hzero
      have hright_zero : term.2 = 0 := (LRootedForest.order_eq_zero_iff term.2).1 hzero
      have hleft_eq := coproductTerms_right_eq_zero hterm hright_zero
      cases term with
      | mk left right =>
          simp at hright_zero hleft_eq ⊢
          exact ⟨hleft_eq, hright_zero⟩
    rw [LForestTensorAlgebra.antipodeRight_terms_sum_eq_boundary_add_proper
      (R := R) hφ (coproductTerms φ) hleft hright]
    rw [coproductTerms_leftBoundaryCoproductTerm,
      coproductTerms_rightBoundaryCoproductTerm]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change
      LForestAlgebra.ofForest (R := R) 0 * rightAntipode (R := R) φ +
          LForestAlgebra.ofForest (R := R) φ * rightAntipode (R := R) 0 +
          ((properCoproductTerms φ).map fun term =>
            LForestAlgebra.ofForest (R := R) term.1 * rightAntipode (R := R) term.2).sum =
        0
    rw [← LForestTensorAlgebra.antipodeRight_sumTerms (R := R) (properCoproductTerms φ)]
    change
      LForestAlgebra.ofForest (R := R) 0 * rightAntipode (R := R) φ +
          LForestAlgebra.ofForest (R := R) φ * rightAntipode (R := R) 0 +
          LForestTensorAlgebra.antipodeRight (R := R) (reducedCoproduct (R := R) φ) =
        0
    rw [rightAntipode_zero, LForestAlgebra.ofForest_zero, one_mul, mul_one]
    simpa [add_comm, add_left_comm, add_assoc] using
      rightAntipode_add_ofForest_add_antipodeRight_reducedCoproduct (R := R) hφ

theorem evalCharacter_antipodeRight_coproductTerms
    (χ : LForestAlgebra.Character α R) (φ : LRootedForest α) :
    ((coproductTerms φ).map fun term =>
      χ.evalForest term.1 * χ (rightAntipode (R := R) term.2)).sum =
      LForestAlgebra.counitCoeff (R := R) φ := by
  calc
    ((coproductTerms φ).map fun term =>
      χ.evalForest term.1 * χ (rightAntipode (R := R) term.2)).sum =
        χ (LForestTensorAlgebra.antipodeRight (R := R)
          (LForestTensorAlgebra.sumTerms (R := R) (coproductTerms φ))) := by
          rw [LForestTensorAlgebra.evalCharacter_antipodeRight_sumTerms]
    _ = χ (LForestTensorAlgebra.antipodeRight (R := R) (coproduct (R := R) φ)) := by
          rw [coproduct_eq_sumTerms_coproductTerms]
    _ = LForestAlgebra.counitCoeff (R := R) φ := by
          rw [antipodeRight_coproduct]
          simp

end

end LRootedForest

namespace LForestAlgebra

noncomputable section

variable {α : Type u} {R : Type v} [CommRing R]

/-- The linear extension of the recursive antipode to the labelled forest algebra. -/
noncomputable def antipode : LForestAlgebra α R →ₗ[R] LForestAlgebra α R :=
  (Finsupp.linearCombination R (LRootedForest.antipode (α := α) (R := R))).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem antipode_ofForest (φ : LRootedForest α) :
    antipode (R := R) (ofForest (R := R) φ) =
      LRootedForest.antipode (R := R) φ := by
  rw [antipode, ofForest]
  change (Finsupp.linearCombination R (LRootedForest.antipode (α := α) (R := R)))
      (Finsupp.single φ (1 : R)) = LRootedForest.antipode (R := R) φ
  rw [Finsupp.linearCombination_single]
  simp

@[simp]
theorem antipode_zero : antipode (α := α) (R := R) (0 : LForestAlgebra α R) = 0 :=
  LinearMap.map_zero (antipode (α := α) (R := R))

theorem antipode_add (x y : LForestAlgebra α R) :
    antipode (R := R) (x + y) = antipode x + antipode y :=
  LinearMap.map_add (antipode (α := α) (R := R)) x y

/-- The linear extension of the right-recursive labelled antipode. -/
noncomputable def rightAntipode : LForestAlgebra α R →ₗ[R] LForestAlgebra α R :=
  (Finsupp.linearCombination R (LRootedForest.rightAntipode (α := α) (R := R))).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
theorem rightAntipode_ofForest (φ : LRootedForest α) :
    rightAntipode (R := R) (ofForest (R := R) φ) =
      LRootedForest.rightAntipode (R := R) φ := by
  rw [rightAntipode, ofForest]
  change (Finsupp.linearCombination R (LRootedForest.rightAntipode (α := α) (R := R)))
      (Finsupp.single φ (1 : R)) = LRootedForest.rightAntipode (R := R) φ
  rw [Finsupp.linearCombination_single]
  simp

@[simp]
theorem rightAntipode_zero :
    rightAntipode (α := α) (R := R) (0 : LForestAlgebra α R) = 0 :=
  LinearMap.map_zero (rightAntipode (α := α) (R := R))

theorem rightAntipode_add (x y : LForestAlgebra α R) :
    rightAntipode (R := R) (x + y) = rightAntipode x + rightAntipode y :=
  LinearMap.map_add (rightAntipode (α := α) (R := R)) x y

theorem counit_rightAntipode (x : LForestAlgebra α R) :
    LForestAlgebra.counit α R (rightAntipode (R := R) x) =
      LForestAlgebra.counit α R x := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestAlgebra α R =>
      LForestAlgebra.counit α R (rightAntipode (R := R) x) =
        LForestAlgebra.counit α R x) x ?_ ?_ ?_
  · intro φ
    change
      LForestAlgebra.counit α R (rightAntipode (R := R) (ofForest (R := R) φ)) =
        LForestAlgebra.counit α R (ofForest (R := R) φ)
    rw [rightAntipode_ofForest, LForestAlgebra.counit_ofForest,
      LRootedForest.counit_rightAntipode]
  · intro x y hx hy
    rw [rightAntipode_add, map_add, hx, hy, map_add]
  · intro r x hx
    simp [hx]

/-- Applying the labelled recursive antipode on the left factor of the coproduct gives the counit. -/
theorem antipodeLeft_coproduct (x : LForestAlgebra α R) :
    LForestTensorAlgebra.antipodeLeft (R := R) (LForestAlgebra.coproduct α R x) =
      LForestAlgebra.counit α R x • (1 : LForestAlgebra α R) := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestAlgebra α R =>
      LForestTensorAlgebra.antipodeLeft (R := R) (LForestAlgebra.coproduct α R x) =
        LForestAlgebra.counit α R x • (1 : LForestAlgebra α R)) x ?_ ?_ ?_
  · intro φ
    change
      LForestTensorAlgebra.antipodeLeft (R := R)
          (LForestAlgebra.coproduct α R (ofForest (R := R) φ)) =
        LForestAlgebra.counit α R (ofForest (R := R) φ) •
          (1 : LForestAlgebra α R)
    rw [LForestAlgebra.coproduct_ofForest, LForestAlgebra.counit_ofForest,
      LRootedForest.antipodeLeft_coproduct]
  · intro x y hx hy
    simp [hx, hy, add_smul]
  · intro r x hx
    simp [hx, smul_smul]

/-- Applying the right-recursive labelled antipode on the right factor gives the counit. -/
theorem antipodeRight_coproduct (x : LForestAlgebra α R) :
    LForestTensorAlgebra.antipodeRight (R := R) (LForestAlgebra.coproduct α R x) =
      LForestAlgebra.counit α R x • (1 : LForestAlgebra α R) := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestAlgebra α R =>
      LForestTensorAlgebra.antipodeRight (R := R) (LForestAlgebra.coproduct α R x) =
        LForestAlgebra.counit α R x • (1 : LForestAlgebra α R)) x ?_ ?_ ?_
  · intro φ
    change
      LForestTensorAlgebra.antipodeRight (R := R)
          (LForestAlgebra.coproduct α R (ofForest (R := R) φ)) =
        LForestAlgebra.counit α R (ofForest (R := R) φ) •
          (1 : LForestAlgebra α R)
    rw [LForestAlgebra.coproduct_ofForest, LForestAlgebra.counit_ofForest,
      LRootedForest.antipodeRight_coproduct]
  · intro x y hx hy
    simp [hx, hy, add_smul]
  · intro r x hx
    simp [hx, smul_smul]

namespace Character

theorem eval_antipodeLeft_coproduct
    (χ : Character α R) (x : LForestAlgebra α R) :
    χ (LForestTensorAlgebra.antipodeLeft (R := R) (LForestAlgebra.coproduct α R x)) =
      LForestAlgebra.counit α R x := by
  rw [LForestAlgebra.antipodeLeft_coproduct]
  simp

theorem eval_antipodeRight_coproduct
    (χ : Character α R) (x : LForestAlgebra α R) :
    χ (LForestTensorAlgebra.antipodeRight (R := R) (LForestAlgebra.coproduct α R x)) =
      LForestAlgebra.counit α R x := by
  rw [LForestAlgebra.antipodeRight_coproduct]
  simp

end Character

theorem eraseLabels_antipode (x : LForestAlgebra α R) :
    LForestAlgebra.eraseLabels (α := α) R (antipode (R := R) x) =
      ForestAlgebra.antipode (R := R)
        (LForestAlgebra.eraseLabels (α := α) R x) := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestAlgebra α R =>
      LForestAlgebra.eraseLabels (α := α) R (antipode (R := R) x) =
        ForestAlgebra.antipode (R := R)
          (LForestAlgebra.eraseLabels (α := α) R x)) x ?_ ?_ ?_
  · intro φ
    change
      LForestAlgebra.eraseLabels (α := α) R
          (antipode (R := R) (ofForest (R := R) φ)) =
        ForestAlgebra.antipode (R := R)
          (LForestAlgebra.eraseLabels (α := α) R (ofForest (R := R) φ))
    rw [antipode_ofForest, LForestAlgebra.eraseLabels_ofForest,
      ForestAlgebra.antipode_ofForest, LRootedForest.eraseLabels_antipode]
  · intro x y hx hy
    rw [antipode_add, map_add, hx, hy, map_add, ForestAlgebra.antipode_add]
  · intro r x hx
    simp [hx]

theorem counit_antipode (x : LForestAlgebra α R) :
    LForestAlgebra.counit α R (antipode (R := R) x) = LForestAlgebra.counit α R x := by
  calc
    LForestAlgebra.counit α R (antipode (R := R) x) =
        ForestAlgebra.counit R
          (LForestAlgebra.eraseLabels (α := α) R (antipode (R := R) x)) := by
          simpa [AlgHom.comp_apply] using
            congrArg (fun f => f (antipode (R := R) x))
              (LForestAlgebra.counit_comp_eraseLabels (α := α) (R := R)).symm
    _ = ForestAlgebra.counit R
          (ForestAlgebra.antipode (R := R)
            (LForestAlgebra.eraseLabels (α := α) R x)) := by
          rw [eraseLabels_antipode]
    _ = ForestAlgebra.counit R (LForestAlgebra.eraseLabels (α := α) R x) := by
          rw [ForestAlgebra.counit_antipode]
    _ = LForestAlgebra.counit α R x := by
          simpa [AlgHom.comp_apply] using
            congrArg (fun f => f x)
              (LForestAlgebra.counit_comp_eraseLabels (α := α) (R := R))

theorem mapLabels_antipode {β : Type w} (f : α → β) (x : LForestAlgebra α R) :
    LForestAlgebra.mapLabels (R := R) f (antipode (R := R) x) =
      antipode (R := R) (LForestAlgebra.mapLabels (R := R) f x) := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestAlgebra α R =>
      LForestAlgebra.mapLabels (R := R) f (antipode (R := R) x) =
        antipode (R := R) (LForestAlgebra.mapLabels (R := R) f x)) x ?_ ?_ ?_
  · intro φ
    change
      LForestAlgebra.mapLabels (R := R) f
          (antipode (R := R) (ofForest (R := R) φ)) =
        antipode (R := R)
          (LForestAlgebra.mapLabels (R := R) f (ofForest (R := R) φ))
    rw [antipode_ofForest, LForestAlgebra.mapLabels_ofForest,
      antipode_ofForest, LRootedForest.mapLabels_antipode]
  · intro x y hx hy
    rw [antipode_add, map_add, hx, hy, map_add, antipode_add]
  · intro r x hx
    simp [hx]

theorem constLabel_antipode (a : α) (x : ForestAlgebra R) :
    LForestAlgebra.constLabel a R (ForestAlgebra.antipode (R := R) x) =
      antipode (R := R) (LForestAlgebra.constLabel a R x) := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestAlgebra R =>
      LForestAlgebra.constLabel a R (ForestAlgebra.antipode (R := R) x) =
        antipode (R := R) (LForestAlgebra.constLabel a R x)) x ?_ ?_ ?_
  · intro φ
    change
      LForestAlgebra.constLabel a R
          (ForestAlgebra.antipode (R := R) (ForestAlgebra.ofForest (R := R) φ)) =
        antipode (R := R)
          (LForestAlgebra.constLabel a R (ForestAlgebra.ofForest (R := R) φ))
    rw [ForestAlgebra.antipode_ofForest, LForestAlgebra.constLabel_ofForest,
      antipode_ofForest, LRootedForest.constLabel_antipode]
  · intro x y hx hy
    rw [ForestAlgebra.antipode_add, map_add, hx, hy, map_add, antipode_add]
  · intro r x hx
    simp [hx]

theorem eraseLabels_rightAntipode (x : LForestAlgebra α R) :
    LForestAlgebra.eraseLabels (α := α) R (rightAntipode (R := R) x) =
      ForestAlgebra.rightAntipode (R := R)
        (LForestAlgebra.eraseLabels (α := α) R x) := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestAlgebra α R =>
      LForestAlgebra.eraseLabels (α := α) R (rightAntipode (R := R) x) =
        ForestAlgebra.rightAntipode (R := R)
          (LForestAlgebra.eraseLabels (α := α) R x)) x ?_ ?_ ?_
  · intro φ
    change
      LForestAlgebra.eraseLabels (α := α) R
          (rightAntipode (R := R) (ofForest (R := R) φ)) =
        ForestAlgebra.rightAntipode (R := R)
          (LForestAlgebra.eraseLabels (α := α) R (ofForest (R := R) φ))
    rw [rightAntipode_ofForest, LForestAlgebra.eraseLabels_ofForest,
      ForestAlgebra.rightAntipode_ofForest, LRootedForest.eraseLabels_rightAntipode]
  · intro x y hx hy
    rw [rightAntipode_add, map_add, hx, hy, map_add, ForestAlgebra.rightAntipode_add]
  · intro r x hx
    simp [hx]

theorem mapLabels_rightAntipode {β : Type w} (f : α → β) (x : LForestAlgebra α R) :
    LForestAlgebra.mapLabels (R := R) f (rightAntipode (R := R) x) =
      rightAntipode (R := R) (LForestAlgebra.mapLabels (R := R) f x) := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestAlgebra α R =>
      LForestAlgebra.mapLabels (R := R) f (rightAntipode (R := R) x) =
        rightAntipode (R := R) (LForestAlgebra.mapLabels (R := R) f x)) x ?_ ?_ ?_
  · intro φ
    change
      LForestAlgebra.mapLabels (R := R) f
          (rightAntipode (R := R) (ofForest (R := R) φ)) =
        rightAntipode (R := R)
          (LForestAlgebra.mapLabels (R := R) f (ofForest (R := R) φ))
    rw [rightAntipode_ofForest, LForestAlgebra.mapLabels_ofForest,
      rightAntipode_ofForest, LRootedForest.mapLabels_rightAntipode]
  · intro x y hx hy
    rw [rightAntipode_add, map_add, hx, hy, map_add, rightAntipode_add]
  · intro r x hx
    simp [hx]

theorem constLabel_rightAntipode (a : α) (x : ForestAlgebra R) :
    LForestAlgebra.constLabel a R (ForestAlgebra.rightAntipode (R := R) x) =
      rightAntipode (R := R) (LForestAlgebra.constLabel a R x) := by
  classical
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestAlgebra R =>
      LForestAlgebra.constLabel a R (ForestAlgebra.rightAntipode (R := R) x) =
        rightAntipode (R := R) (LForestAlgebra.constLabel a R x)) x ?_ ?_ ?_
  · intro φ
    change
      LForestAlgebra.constLabel a R
          (ForestAlgebra.rightAntipode (R := R) (ForestAlgebra.ofForest (R := R) φ)) =
        rightAntipode (R := R)
          (LForestAlgebra.constLabel a R (ForestAlgebra.ofForest (R := R) φ))
    rw [ForestAlgebra.rightAntipode_ofForest, LForestAlgebra.constLabel_ofForest,
      rightAntipode_ofForest, LRootedForest.constLabel_rightAntipode]
  · intro x y hx hy
    rw [ForestAlgebra.rightAntipode_add, map_add, hx, hy, map_add, rightAntipode_add]
  · intro r x hx
    simp [hx]

end

end LForestAlgebra

end HopfAlgebras
