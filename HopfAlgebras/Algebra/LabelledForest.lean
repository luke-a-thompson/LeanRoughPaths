/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Algebra.Forest
import HopfAlgebras.Forests.Labelled
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The Algebra of Labelled Rooted Forests

This file defines the commutative algebra freely spanned by labelled rooted
forests. It is the labelled analogue of `HopfAlgebras.Algebra.Forest`.

## Main definitions

* `LForestAlgebra` - monoid algebra of labelled rooted forests
* `LForestAlgebra.ofForest` - the monomial associated to a labelled forest
* `LForestAlgebra.eraseLabels` - forget labels as an algebra morphism
* `LForestAlgebra.constLabel` - label every vertex by a fixed label as an algebra morphism
* `LForestAlgebra.mapLabels` - relabel forests as an algebra morphism
* `LForestAlgebra.counit` - algebra counit sending the empty forest to `1`
* `LForestAlgebra.Character` - algebra characters on labelled forest algebra
-/

namespace HopfAlgebras

universe u v w x

/-- The algebra freely spanned by labelled rooted forests over a coefficient semiring. -/
abbrev LForestAlgebra (α : Type u) (R : Type v) [Semiring R] : Type (max u v) :=
  AddMonoidAlgebra R (LRootedForest α)

namespace LForestAlgebra

noncomputable section

variable {α : Type u} {β : Type w} {γ : Type x} {R : Type v}

/-- The monomial associated to a labelled rooted forest. -/
def ofForest [Semiring R] (φ : LRootedForest α) : LForestAlgebra α R :=
  AddMonoidAlgebra.single φ 1

@[simp]
theorem ofForest_zero [Semiring R] : ofForest (R := R) (α := α) 0 = 1 := by
  simp [ofForest, AddMonoidAlgebra.one_def]

@[simp]
theorem ofForest_empty [Semiring R] :
    ofForest (R := R) (α := α) LRootedForest.empty = 1 := by
  simp [LRootedForest.empty]

@[simp]
theorem ofForest_add [Semiring R] (φ ψ : LRootedForest α) :
    ofForest (R := R) (φ + ψ) = ofForest φ * ofForest ψ := by
  simp [ofForest, AddMonoidAlgebra.single_mul_single]

private def eraseLabelsMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    Multiplicative (LRootedForest α) →* ForestAlgebra R where
  toFun φ :=
    ForestAlgebra.ofForest (R := R) (LRootedForest.erase (Multiplicative.toAdd φ))
  map_one' := by
    change
      ForestAlgebra.ofForest (R := R) (LRootedForest.erase (0 : LRootedForest α)) = 1
    rw [show LRootedForest.erase (0 : LRootedForest α) = 0 by rfl]
    simp
  map_mul' φ ψ := by
    change
      ForestAlgebra.ofForest (R := R)
          (LRootedForest.erase (Multiplicative.toAdd φ + Multiplicative.toAdd ψ)) =
        ForestAlgebra.ofForest (R := R) (LRootedForest.erase (Multiplicative.toAdd φ)) *
          ForestAlgebra.ofForest (R := R) (LRootedForest.erase (Multiplicative.toAdd ψ))
    simp [LRootedForest.erase_add, ForestAlgebra.ofForest_add]

/-- Forget labels as an algebra morphism from labelled to unlabelled forest algebra. -/
def eraseLabels (R : Type v) [CommSemiring R] :
    LForestAlgebra α R →ₐ[R] ForestAlgebra R :=
  (AddMonoidAlgebra.lift R (ForestAlgebra R) (LRootedForest α))
    (eraseLabelsMonoidHom α R)

@[simp]
theorem eraseLabels_ofForest [CommSemiring R] (φ : LRootedForest α) :
    eraseLabels (α := α) R (ofForest (R := R) φ) =
      ForestAlgebra.ofForest (R := R) (LRootedForest.erase φ) := by
  simp [eraseLabels, ofForest, eraseLabelsMonoidHom]

@[simp]
theorem eraseLabels_ofForest_zero [CommSemiring R] :
    eraseLabels (α := α) R (ofForest (R := R) 0) = 1 := by
  simp

private def constLabelMonoidHom (a : α) (R : Type v) [CommSemiring R] :
    Multiplicative RootedForest →* LForestAlgebra α R where
  toFun φ :=
    ofForest (R := R) (LRootedForest.constLabel a (Multiplicative.toAdd φ))
  map_one' := by
    change ofForest (R := R) (LRootedForest.constLabel a (0 : RootedForest)) = 1
    simp
  map_mul' φ ψ := by
    change
      ofForest (R := R)
          (LRootedForest.constLabel a (Multiplicative.toAdd φ + Multiplicative.toAdd ψ)) =
        ofForest (R := R) (LRootedForest.constLabel a (Multiplicative.toAdd φ)) *
          ofForest (R := R) (LRootedForest.constLabel a (Multiplicative.toAdd ψ))
    simp [LRootedForest.constLabel_add, ofForest_add]

/-- Label every vertex as an algebra morphism from unlabelled to labelled forests. -/
def constLabel (a : α) (R : Type v) [CommSemiring R] :
    ForestAlgebra R →ₐ[R] LForestAlgebra α R :=
  (AddMonoidAlgebra.lift R (LForestAlgebra α R) RootedForest)
    (constLabelMonoidHom a R)

@[simp]
theorem constLabel_ofForest [CommSemiring R] (a : α) (φ : RootedForest) :
    constLabel a R (ForestAlgebra.ofForest (R := R) φ) =
      ofForest (R := R) (LRootedForest.constLabel a φ) := by
  simp [constLabel, ForestAlgebra.ofForest, constLabelMonoidHom]

@[simp]
theorem constLabel_ofForest_zero [CommSemiring R] (a : α) :
    constLabel a R (ForestAlgebra.ofForest (R := R) 0) = 1 := by
  simp

private def mapLabelsMonoidHom (f : α → β) (R : Type v) [CommSemiring R] :
    Multiplicative (LRootedForest α) →* LForestAlgebra β R where
  toFun φ :=
    ofForest (R := R) (LRootedForest.mapLabels f (Multiplicative.toAdd φ))
  map_one' := by
    change ofForest (R := R) (LRootedForest.mapLabels f (0 : LRootedForest α)) = 1
    rw [show LRootedForest.mapLabels f (0 : LRootedForest α) = 0 by rfl]
    simp
  map_mul' φ ψ := by
    change
      ofForest (R := R)
          (LRootedForest.mapLabels f (Multiplicative.toAdd φ + Multiplicative.toAdd ψ)) =
        ofForest (R := R) (LRootedForest.mapLabels f (Multiplicative.toAdd φ)) *
          ofForest (R := R) (LRootedForest.mapLabels f (Multiplicative.toAdd ψ))
    simp [LRootedForest.mapLabels_add, ofForest_add]

/-- Relabel labelled forests as an algebra morphism. -/
def mapLabels (R : Type v) [CommSemiring R] (f : α → β) :
    LForestAlgebra α R →ₐ[R] LForestAlgebra β R :=
  (AddMonoidAlgebra.lift R (LForestAlgebra β R) (LRootedForest α))
    (mapLabelsMonoidHom f R)

@[simp]
theorem mapLabels_ofForest [CommSemiring R] (f : α → β) (φ : LRootedForest α) :
    mapLabels (R := R) f (ofForest (R := R) φ) =
      ofForest (R := R) (LRootedForest.mapLabels f φ) := by
  simp [mapLabels, ofForest, mapLabelsMonoidHom]

@[simp]
theorem mapLabels_ofForest_zero [CommSemiring R] (f : α → β) :
    mapLabels (R := R) f (ofForest (R := R) 0) = 1 := by
  simp

@[simp]
theorem mapLabels_id [CommSemiring R] :
    mapLabels (R := R) (fun a : α => a) = AlgHom.id R (LForestAlgebra α R) := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext x)
  apply MonoidHom.ext
  intro φ
  change
    mapLabels (R := R) (fun a : α => a) (ofForest (R := R) (Multiplicative.toAdd φ)) =
      ofForest (R := R) (Multiplicative.toAdd φ)
  rw [mapLabels_ofForest]
  exact congrArg (fun ψ => ofForest (R := R) ψ)
    (LRootedForest.mapLabels_id (Multiplicative.toAdd φ))

theorem mapLabels_comp [CommSemiring R] (g : β → γ) (f : α → β) :
    (mapLabels (R := R) g).comp (mapLabels (R := R) f) =
      mapLabels (R := R) (g ∘ f) := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext x)
  apply MonoidHom.ext
  intro φ
  change
    mapLabels (R := R) g
        (mapLabels (R := R) f (ofForest (R := R) (Multiplicative.toAdd φ))) =
      mapLabels (R := R) (g ∘ f) (ofForest (R := R) (Multiplicative.toAdd φ))
  rw [mapLabels_ofForest, mapLabels_ofForest, mapLabels_ofForest]
  simp

theorem eraseLabels_comp_mapLabels [CommSemiring R] (f : α → β) :
    (eraseLabels (α := β) R).comp (mapLabels (R := R) f) =
      eraseLabels (α := α) R := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext x)
  apply MonoidHom.ext
  intro φ
  change
    eraseLabels (α := β) R
        (mapLabels (R := R) f (ofForest (R := R) (Multiplicative.toAdd φ))) =
      eraseLabels (α := α) R (ofForest (R := R) (Multiplicative.toAdd φ))
  rw [mapLabels_ofForest, eraseLabels_ofForest, eraseLabels_ofForest]
  simp

theorem eraseLabels_comp_constLabel [CommSemiring R] (a : α) :
    (eraseLabels (α := α) R).comp (constLabel a R) =
      AlgHom.id R (ForestAlgebra R) := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext x)
  apply MonoidHom.ext
  intro φ
  change
    eraseLabels (α := α) R
        (constLabel a R (ForestAlgebra.ofForest (R := R) (Multiplicative.toAdd φ))) =
      ForestAlgebra.ofForest (R := R) (Multiplicative.toAdd φ)
  rw [constLabel_ofForest, eraseLabels_ofForest]
  simp

theorem constLabel_injective [CommSemiring R] (a : α) :
    Function.Injective (constLabel a R : ForestAlgebra R → LForestAlgebra α R) := by
  intro x y h
  have hErase := congrArg (eraseLabels (α := α) R) h
  simpa [← AlgHom.comp_apply, eraseLabels_comp_constLabel] using hErase

theorem constLabel_eq_constLabel_iff [CommSemiring R] (a : α) {x y : ForestAlgebra R} :
    constLabel a R x = constLabel a R y ↔ x = y := by
  constructor
  · intro h
    exact constLabel_injective a h
  · intro h
    rw [h]

theorem mapLabels_comp_constLabel [CommSemiring R] (f : α → β) (a : α) :
    (mapLabels (R := R) f).comp (constLabel a R) =
      constLabel (f a) R := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext x)
  apply MonoidHom.ext
  intro φ
  change
    mapLabels (R := R) f
        (constLabel a R (ForestAlgebra.ofForest (R := R) (Multiplicative.toAdd φ))) =
      constLabel (f a) R (ForestAlgebra.ofForest (R := R) (Multiplicative.toAdd φ))
  rw [constLabel_ofForest, mapLabels_ofForest, constLabel_ofForest]
  simp

/-- The counit value on a labelled forest monomial. -/
def counitCoeff [Zero R] [One R] (φ : LRootedForest α) : R :=
  by
    classical
    exact if φ = 0 then 1 else 0

@[simp]
theorem counitCoeff_zero [Zero R] [One R] :
    counitCoeff (R := R) (α := α) 0 = 1 := by
  classical
  simp [counitCoeff]

@[simp]
theorem counitCoeff_empty [Zero R] [One R] :
    counitCoeff (R := R) (α := α) LRootedForest.empty = 1 := by
  classical
  simp [LRootedForest.empty]

theorem counitCoeff_ne_zero [Zero R] [One R] {φ : LRootedForest α} (hφ : φ ≠ 0) :
    counitCoeff (R := R) φ = 0 := by
  classical
  simp [counitCoeff, hφ]

theorem counitCoeff_add [Semiring R] (φ ψ : LRootedForest α) :
    counitCoeff (R := R) (φ + ψ) = counitCoeff φ * counitCoeff ψ := by
  classical
  by_cases hφ : φ = 0
  · subst φ
    simp [counitCoeff]
  · by_cases hψ : ψ = 0
    · subst ψ
      simp [counitCoeff, hφ]
    · have hφpos := (LRootedForest.order_pos_iff_ne_zero φ).2 hφ
      have hψpos := (LRootedForest.order_pos_iff_ne_zero ψ).2 hψ
      have hsumpos : 0 < LRootedForest.order (φ + ψ) := by
        rw [LRootedForest.order_add]
        omega
      have hsum : φ + ψ ≠ 0 :=
        (LRootedForest.order_pos_iff_ne_zero (φ + ψ)).1 hsumpos
      simp [counitCoeff, hφ, hψ, hsum]

theorem counitCoeff_mapLabels [Zero R] [One R] (f : α → β) (φ : LRootedForest α) :
    counitCoeff (R := R) (LRootedForest.mapLabels f φ) = counitCoeff (R := R) φ := by
  classical
  by_cases hφ : φ = 0
  · subst φ
    rw [show LRootedForest.mapLabels f (0 : LRootedForest α) = 0 by rfl]
    simp
  · have hpos := (LRootedForest.order_pos_iff_ne_zero φ).2 hφ
    have hmap_pos : 0 < LRootedForest.order (LRootedForest.mapLabels f φ) := by
      simpa [LRootedForest.order_mapLabels] using hpos
    have hmap : LRootedForest.mapLabels f φ ≠ 0 :=
      (LRootedForest.order_pos_iff_ne_zero _).1 hmap_pos
    simp [counitCoeff, hφ, hmap]

theorem counitCoeff_erase [Zero R] [One R] (φ : LRootedForest α) :
    ForestAlgebra.counitCoeff (R := R) (LRootedForest.erase φ) =
      counitCoeff (R := R) φ := by
  classical
  by_cases hφ : φ = 0
  · subst φ
    rw [show LRootedForest.erase (0 : LRootedForest α) = 0 by rfl]
    simp
  · have hpos := (LRootedForest.order_pos_iff_ne_zero φ).2 hφ
    have herase_pos : 0 < RootedForest.order (LRootedForest.erase φ) := by
      simpa [LRootedForest.order_erase] using hpos
    have herase : LRootedForest.erase φ ≠ 0 :=
      (RootedForest.order_pos_iff_ne_zero _).1 herase_pos
    simp [ForestAlgebra.counitCoeff, counitCoeff, hφ, herase]

private def counitMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    Multiplicative (LRootedForest α) →* R where
  toFun φ := counitCoeff (R := R) (Multiplicative.toAdd φ)
  map_one' := by
    simp [counitCoeff]
  map_mul' φ ψ := by
    exact counitCoeff_add (R := R) (Multiplicative.toAdd φ) (Multiplicative.toAdd ψ)

/-- The counit algebra homomorphism, sending the empty labelled forest to `1`. -/
def counit (α : Type u) (R : Type v) [CommSemiring R] :
    LForestAlgebra α R →ₐ[R] R :=
  (AddMonoidAlgebra.lift R R (LRootedForest α)) (counitMonoidHom α R)

@[simp]
theorem counit_ofForest [CommSemiring R] (φ : LRootedForest α) :
    counit α R (ofForest φ) = counitCoeff (R := R) φ := by
  simp [counit, ofForest, counitMonoidHom, counitCoeff]

@[simp]
theorem counit_ofForest_zero [CommSemiring R] :
    counit α R (ofForest (R := R) 0) = 1 := by
  simp

@[simp]
theorem counit_ofForest_ne_zero [CommSemiring R] {φ : LRootedForest α} (hφ : φ ≠ 0) :
    counit α R (ofForest (R := R) φ) = 0 := by
  rw [counit_ofForest]
  exact counitCoeff_ne_zero hφ

theorem counit_comp_mapLabels [CommSemiring R] (f : α → β) :
    (counit β R).comp (mapLabels (R := R) f) = counit α R := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext x)
  apply MonoidHom.ext
  intro φ
  change
    counit β R ((mapLabels (R := R) f) (ofForest (R := R) (Multiplicative.toAdd φ))) =
      counit α R (ofForest (R := R) (Multiplicative.toAdd φ))
  rw [mapLabels_ofForest, counit_ofForest, counit_ofForest, counitCoeff_mapLabels]

theorem counit_comp_eraseLabels [CommSemiring R] :
    (ForestAlgebra.counit R).comp (eraseLabels (α := α) R) = counit α R := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext x)
  apply MonoidHom.ext
  intro φ
  change
    ForestAlgebra.counit R
        ((eraseLabels (α := α) R) (ofForest (R := R) (Multiplicative.toAdd φ))) =
      counit α R (ofForest (R := R) (Multiplicative.toAdd φ))
  rw [eraseLabels_ofForest, ForestAlgebra.counit_ofForest, counit_ofForest, counitCoeff_erase]

/-- Algebra characters on the labelled rooted-forest algebra. -/
abbrev Character (α : Type u) (R : Type v) [CommSemiring R] : Type (max u v) :=
  LForestAlgebra α R →ₐ[R] R

namespace Character

variable [CommSemiring R]

/-- Evaluate a labelled-forest character on one forest monomial. -/
def evalForest (χ : Character α R) (φ : LRootedForest α) : R :=
  χ (ofForest (R := R) φ)

@[simp]
theorem evalForest_zero (χ : Character α R) :
    χ.evalForest 0 = 1 := by
  simp [evalForest]

@[simp]
theorem evalForest_empty (χ : Character α R) :
    χ.evalForest LRootedForest.empty = 1 := by
  simp [evalForest]

@[simp]
theorem evalForest_add (χ : Character α R) (φ ψ : LRootedForest α) :
    χ.evalForest (φ + ψ) = χ.evalForest φ * χ.evalForest ψ := by
  simp [evalForest, ofForest_add]

theorem evalForest_ofPLTree_list_perm (χ : Character α R) {ts us : List (PLTree α)}
    (h : ts.Perm us) :
    χ.evalForest (ts.map LRootedTree.ofPLTree : LRootedForest α) =
      χ.evalForest (us.map LRootedTree.ofPLTree : LRootedForest α) :=
  congrArg χ.evalForest (Quotient.sound (h.map LRootedTree.ofPLTree))

theorem evalForest_ofPLTree_list_forall₂_perm (χ : Character α R)
    {ts us : List (PLTree α)} (h : List.Forall₂ PLTree.Perm ts us) :
    χ.evalForest (ts.map LRootedTree.ofPLTree : LRootedForest α) =
      χ.evalForest (us.map LRootedTree.ofPLTree : LRootedForest α) :=
  congrArg χ.evalForest <|
    congrArg (fun vs : List (LRootedTree α) => (vs : LRootedForest α))
      (LRootedTree.map_ofPLTree_eq_of_forall₂_perm h)

@[ext]
theorem ext {χ ψ : Character α R} (h : ∀ φ, χ.evalForest φ = ψ.evalForest φ) :
    χ = ψ := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext x)
  apply MonoidHom.ext
  intro φ
  change
    χ (ofForest (R := R) (Multiplicative.toAdd φ)) =
      ψ (ofForest (R := R) (Multiplicative.toAdd φ))
  exact h (Multiplicative.toAdd φ)

theorem ext_tree {χ ψ : Character α R}
    (h : ∀ τ : LRootedTree α,
      χ.evalForest (LRootedForest.singleton τ) = ψ.evalForest (LRootedForest.singleton τ)) :
    χ = ψ := by
  apply ext
  intro φ
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp [evalForest]
  | cons τ ts ih =>
      change
        χ.evalForest (LRootedForest.singleton τ + (ts : LRootedForest α)) =
          ψ.evalForest (LRootedForest.singleton τ + (ts : LRootedForest α))
      rw [evalForest_add, evalForest_add, h τ]
      exact congrArg (fun x => ψ.evalForest (LRootedForest.singleton τ) * x)
        (by simpa using ih)

@[simp]
theorem map_ofForest_zero (χ : Character α R) :
    χ (ofForest (R := R) 0) = 1 := by
  simp

@[simp]
theorem map_ofForest_empty (χ : Character α R) :
    χ (ofForest (R := R) LRootedForest.empty) = 1 := by
  simp

theorem map_ofForest_add (χ : Character α R) (φ ψ : LRootedForest α) :
    χ (ofForest (R := R) (φ + ψ)) = χ (ofForest φ) * χ (ofForest ψ) := by
  rw [ofForest_add, map_mul]

/-- Pull a labelled-forest character back along a relabelling map. -/
def comapMapLabels (f : α → β) (χ : Character β R) : Character α R :=
  χ.comp (LForestAlgebra.mapLabels (R := R) f)

/-- Pull an unlabelled forest character back by forgetting labels. -/
def comapEraseLabels (χ : ForestAlgebra.Character R) : Character α R :=
  χ.comp (eraseLabels (α := α) R)

/-- Pull a labelled-forest character back along constant labelling. -/
def comapConstLabel (a : α) (χ : Character α R) : ForestAlgebra.Character R :=
  χ.comp (LForestAlgebra.constLabel a R)

@[simp]
theorem comapMapLabels_evalForest (f : α → β) (χ : Character β R)
    (φ : LRootedForest α) :
    (comapMapLabels f χ).evalForest φ =
      χ.evalForest (LRootedForest.mapLabels f φ) := by
  simp [comapMapLabels, evalForest]

@[simp]
theorem comapEraseLabels_evalForest (χ : ForestAlgebra.Character R)
    (φ : LRootedForest α) :
    (comapEraseLabels (α := α) χ).evalForest φ =
      χ (ForestAlgebra.ofForest (R := R) (LRootedForest.erase φ)) := by
  simp [comapEraseLabels, evalForest]

@[simp]
theorem comapConstLabel_evalForest (a : α) (χ : Character α R) (φ : RootedForest) :
    (comapConstLabel a χ).evalForest φ =
      χ.evalForest (LRootedForest.constLabel a φ) := by
  simp [comapConstLabel, ForestAlgebra.Character.evalForest, evalForest]

@[simp]
theorem comapMapLabels_id (χ : Character α R) :
    comapMapLabels (fun a : α => a) χ = χ := by
  simp [comapMapLabels]

theorem comapMapLabels_comp (g : β → γ) (f : α → β) (χ : Character γ R) :
    comapMapLabels f (comapMapLabels g χ) = comapMapLabels (g ∘ f) χ := by
  simp [comapMapLabels, AlgHom.comp_assoc, LForestAlgebra.mapLabels_comp]

theorem comapEraseLabels_comapMapLabels (f : α → β) (χ : ForestAlgebra.Character R) :
    comapMapLabels f (comapEraseLabels (α := β) χ) =
      comapEraseLabels (α := α) χ := by
  simp [comapMapLabels, comapEraseLabels, AlgHom.comp_assoc,
    LForestAlgebra.eraseLabels_comp_mapLabels]

theorem comapConstLabel_comapMapLabels (f : α → β) (a : α) (χ : Character β R) :
    comapConstLabel a (comapMapLabels f χ) = comapConstLabel (f a) χ := by
  simp [comapConstLabel, comapMapLabels, AlgHom.comp_assoc,
    LForestAlgebra.mapLabels_comp_constLabel]

theorem comapConstLabel_comapEraseLabels (a : α) (χ : ForestAlgebra.Character R) :
    comapConstLabel a (comapEraseLabels (α := α) χ) = χ := by
  apply ForestAlgebra.Character.ext
  intro φ
  change
    χ ((eraseLabels (α := α) R)
        (constLabel a R (ForestAlgebra.ofForest (R := R) φ))) =
      χ (ForestAlgebra.ofForest (R := R) φ)
  rw [constLabel_ofForest, eraseLabels_ofForest]
  simp

theorem comapMapLabels_counit (f : α → β) :
    comapMapLabels f (counit β R) = counit α R := by
  simpa [comapMapLabels] using LForestAlgebra.counit_comp_mapLabels (R := R) f

theorem comapEraseLabels_counit :
    comapEraseLabels (α := α) (ForestAlgebra.counit R) = counit α R := by
  simpa [comapEraseLabels] using LForestAlgebra.counit_comp_eraseLabels (α := α) (R := R)

theorem comapConstLabel_counit (a : α) :
    comapConstLabel a (counit α R) = ForestAlgebra.counit R := by
  rw [← comapEraseLabels_counit (α := α) (R := R)]
  exact comapConstLabel_comapEraseLabels a (ForestAlgebra.counit R)

/-- A labelled forest character whose values only depend on the unlabelled forest. -/
def LabelInvariant (χ : Character α R) : Prop :=
  ∀ φ ψ, LRootedForest.erase φ = LRootedForest.erase ψ →
    χ.evalForest φ = χ.evalForest ψ

theorem LabelInvariant.evalForest_eq {χ : Character α R} (h : LabelInvariant χ)
    {φ ψ : LRootedForest α} (hφψ : LRootedForest.erase φ = LRootedForest.erase ψ) :
    χ.evalForest φ = χ.evalForest ψ :=
  h φ ψ hφψ

theorem labelInvariant_comapEraseLabels (χ : ForestAlgebra.Character R) :
    LabelInvariant (comapEraseLabels (α := α) χ) := by
  intro φ ψ hφψ
  simpa [comapEraseLabels_evalForest] using
    congrArg (fun ξ => χ (ForestAlgebra.ofForest (R := R) ξ)) hφψ

theorem labelInvariant_counit : LabelInvariant (counit α R) := by
  rw [← comapEraseLabels_counit (α := α) (R := R)]
  exact labelInvariant_comapEraseLabels (α := α) (ForestAlgebra.counit R)

theorem LabelInvariant.comapMapLabels {χ : Character β R} (h : LabelInvariant χ)
    (f : α → β) : LabelInvariant (comapMapLabels f χ) := by
  intro φ ψ hφψ
  simpa [comapMapLabels_evalForest] using
    h (LRootedForest.mapLabels f φ) (LRootedForest.mapLabels f ψ) (by simpa using hφψ)

theorem LabelInvariant.comapConstLabel_eq {χ : Character α R} (h : LabelInvariant χ)
    (x y : α) : comapConstLabel x χ = comapConstLabel y χ := by
  apply ForestAlgebra.Character.ext
  intro φ
  simpa [comapConstLabel_evalForest] using
    h (LRootedForest.constLabel x φ) (LRootedForest.constLabel y φ) (by simp)

theorem LabelInvariant.comapEraseLabels_comapConstLabel {χ : Character α R}
    (h : LabelInvariant χ) (x : α) :
    comapEraseLabels (α := α) (comapConstLabel x χ) = χ := by
  apply ext
  intro φ
  calc
    (comapEraseLabels (α := α) (comapConstLabel x χ)).evalForest φ =
        (comapConstLabel x χ).evalForest (LRootedForest.erase φ) := by
          rw [comapEraseLabels_evalForest]
          rfl
    _ = χ.evalForest (LRootedForest.constLabel x (LRootedForest.erase φ)) := by
          rw [comapConstLabel_evalForest]
    _ = χ.evalForest φ := by
          exact h (LRootedForest.constLabel x (LRootedForest.erase φ)) φ (by simp)

/-- Unlabelled forest characters are equivalent to label-invariant labelled characters. -/
noncomputable def labelInvariantEquiv [Nonempty α] :
    ForestAlgebra.Character R ≃ {χ : Character α R // LabelInvariant χ} where
  toFun χ := ⟨comapEraseLabels (α := α) χ, labelInvariant_comapEraseLabels χ⟩
  invFun χ := comapConstLabel (Classical.choice (inferInstance : Nonempty α)) χ.1
  left_inv χ := by
    exact comapConstLabel_comapEraseLabels (Classical.choice (inferInstance : Nonempty α)) χ
  right_inv χ := by
    cases χ with
    | mk χ hχ =>
        apply Subtype.ext
        exact hχ.comapEraseLabels_comapConstLabel
          (Classical.choice (inferInstance : Nonempty α))

@[simp]
theorem labelInvariantEquiv_apply [Nonempty α] (χ : ForestAlgebra.Character R) :
    (labelInvariantEquiv (α := α) χ).1 = comapEraseLabels (α := α) χ :=
  rfl

@[simp]
theorem labelInvariantEquiv_symm_apply [Nonempty α]
    (χ : {χ : Character α R // LabelInvariant χ}) :
    (labelInvariantEquiv (α := α) (R := R)).symm χ =
      comapConstLabel (Classical.choice (inferInstance : Nonempty α)) χ.1 :=
  rfl

theorem labelInvariantEquiv_counit [Nonempty α] :
    labelInvariantEquiv (α := α) (R := R) (ForestAlgebra.counit R) =
      ⟨counit α R, labelInvariant_counit⟩ := by
  apply Subtype.ext
  exact comapEraseLabels_counit (α := α) (R := R)

theorem labelInvariantEquiv_symm_counit [Nonempty α] :
    (labelInvariantEquiv (α := α) (R := R)).symm
        ⟨counit α R, labelInvariant_counit⟩ =
      ForestAlgebra.counit R := by
  exact comapConstLabel_counit (Classical.choice (inferInstance : Nonempty α))

theorem labelInvariant_iff_exists_comapEraseLabels [Nonempty α] (χ : Character α R) :
    LabelInvariant χ ↔ ∃ ψ : ForestAlgebra.Character R, comapEraseLabels (α := α) ψ = χ := by
  constructor
  · intro hχ
    let x := Classical.choice (inferInstance : Nonempty α)
    exact ⟨comapConstLabel x χ, hχ.comapEraseLabels_comapConstLabel x⟩
  · rintro ⟨ψ, rfl⟩
    exact labelInvariant_comapEraseLabels (α := α) ψ

end Character

end

end LForestAlgebra

end HopfAlgebras
