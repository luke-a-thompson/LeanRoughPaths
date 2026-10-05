/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.Coproduct
import HopfAlgebras.Cuts.Labelled
import HopfAlgebras.Algebra.LabelledForest

/-!
# Labelled Coproduct Terms in the Forest Algebra

This file turns the finite labelled cut-term lists from `HopfAlgebras.Cuts.Labelled`
into elements of the monoid algebra on pairs of labelled rooted forests. A pair
`(φ, ψ)` represents the basis tensor `φ ⊗ ψ`.

Planar labelled cut terms are extended to non-planar labelled forests through
the forest quotient.
-/

namespace HopfAlgebras

universe u v w

/-- Tensor-coded labelled forest algebra: `(φ, ψ)` represents the basis tensor `φ ⊗ ψ`. -/
abbrev LForestTensorAlgebra (α : Type u) (R : Type v) [Semiring R] : Type (max u v) :=
  AddMonoidAlgebra R (LRootedForest α × LRootedForest α)

namespace LForestTensorAlgebra

noncomputable section

variable {α : Type u} {R : Type v}

/-- The basis tensor represented by a pair of labelled rooted forests. -/
def ofPair [Semiring R] (term : LRootedForest α × LRootedForest α) :
    LForestTensorAlgebra α R :=
  AddMonoidAlgebra.single term 1

/-- The basis tensor `φ ⊗ ψ`. -/
def ofForests [Semiring R] (φ ψ : LRootedForest α) : LForestTensorAlgebra α R :=
  ofPair (R := R) (φ, ψ)

@[simp]
theorem ofPair_zero [Semiring R] :
    ofPair (R := R) (0 : LRootedForest α × LRootedForest α) = 1 := by
  simp [ofPair, AddMonoidAlgebra.one_def]

@[simp]
theorem ofForests_zero_zero [Semiring R] :
    ofForests (R := R) (α := α) 0 0 = 1 := by
  change ofPair (R := R) (0 : LRootedForest α × LRootedForest α) = 1
  simp

@[simp]
theorem ofPair_add [Semiring R] (x y : LRootedForest α × LRootedForest α) :
    ofPair (R := R) (x + y) = ofPair x * ofPair y := by
  simp [ofPair, AddMonoidAlgebra.single_mul_single]

@[simp]
theorem ofForests_add [Semiring R]
    (φ₁ φ₂ ψ₁ ψ₂ : LRootedForest α) :
    ofForests (R := R) (φ₁ + φ₂) (ψ₁ + ψ₂) =
      ofForests φ₁ ψ₁ * ofForests φ₂ ψ₂ := by
  simp [ofForests, ofPair, AddMonoidAlgebra.single_mul_single]

/-- Sum a finite list of labelled basis tensors. Duplicates contribute multiplicity. -/
def sumTerms [Semiring R] (terms : List (LRootedForest α × LRootedForest α)) :
    LForestTensorAlgebra α R :=
  (terms.map (ofPair (R := R))).sum

@[simp]
theorem sumTerms_nil [Semiring R] : sumTerms (R := R) (α := α) [] = 0 :=
  rfl

@[simp]
theorem sumTerms_cons [Semiring R] (term : LRootedForest α × LRootedForest α)
    (terms : List (LRootedForest α × LRootedForest α)) :
    sumTerms (R := R) (term :: terms) = ofPair term + sumTerms terms :=
  rfl

@[simp]
theorem sumTerms_singleton [Semiring R] (term : LRootedForest α × LRootedForest α) :
    sumTerms (R := R) [term] = ofPair term := by
  simp [sumTerms]

theorem sumTerms_append [Semiring R]
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    sumTerms (R := R) (xs ++ ys) = sumTerms xs + sumTerms ys := by
  simp [sumTerms, List.map_append]

theorem sumTerms_perm [Semiring R]
    {xs ys : List (LRootedForest α × LRootedForest α)} (h : xs.Perm ys) :
    sumTerms (R := R) xs = sumTerms ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem sumTerms_cut_forall₂_perm [Semiring R] :
    ∀ {cs ds : List (PLTree.Cut α)}, List.Forall₂ PLTree.Cut.Perm cs ds →
      sumTerms (R := R) (cs.map fun c => (c.prunedForest, c.trunkForest)) =
        sumTerms (R := R) (ds.map fun d => (d.prunedForest, d.trunkForest))
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      simp [PLTree.Cut.Perm.coproductTerm_eq h, sumTerms_cut_forall₂_perm hs]

theorem sumTerms_cut_listRelPerm [Semiring R] {cs ds : List (PLTree.Cut α)}
    (h : PTree.ListRelPerm PLTree.Cut.Perm cs ds) :
    sumTerms (R := R) (cs.map fun c => (c.prunedForest, c.trunkForest)) =
      sumTerms (R := R) (ds.map fun d => (d.prunedForest, d.trunkForest)) := by
  rcases h with ⟨cs', hp, hrel⟩
  rw [sumTerms_perm (R := R) (hp.map _)]
  exact sumTerms_cut_forall₂_perm hrel

theorem sumTerms_map_add_left [Semiring R]
    (x : LRootedForest α × LRootedForest α) :
    ∀ ys : List (LRootedForest α × LRootedForest α),
      sumTerms (R := R) (ys.map fun y => x + y) = ofPair x * sumTerms ys
  | [] => by
      simp [sumTerms]
  | y :: ys => by
      rw [List.map_cons, sumTerms_cons, sumTerms_cons, sumTerms_map_add_left x ys]
      rw [ofPair_add, mul_add]

theorem sumTerms_multiply [Semiring R]
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    sumTerms (R := R) (PLTree.multiplyCoproductTerms xs ys) =
      sumTerms xs * sumTerms ys := by
  induction xs with
  | nil =>
      simp [PLTree.multiplyCoproductTerms, sumTerms]
  | cons x xs ih =>
      rw [PLTree.multiplyCoproductTerms]
      rw [PLTree.multiplyCoproductTerms] at ih
      simp only [List.flatMap_cons]
      rw [sumTerms_append, ih, sumTerms_cons]
      change
        sumTerms (R := R) (ys.map fun y => x + y) + sumTerms xs * sumTerms ys =
          (ofPair x + sumTerms xs) * sumTerms ys
      rw [sumTerms_map_add_left, add_mul]

/-- Forget labels in a coproduct basis term, as an additive homomorphism. -/
def eraseTermAddHom : (LRootedForest α × LRootedForest α) →+ RootedForest × RootedForest where
  toFun := PLTree.eraseCoproductTerm
  map_zero' := by
    simp [PLTree.eraseCoproductTerm, LRootedForest.erase]
  map_add' x y := by
    cases x
    cases y
    simp [PLTree.eraseCoproductTerm]

/-- Forget labels in the tensor-coded labelled forest algebra. -/
def erase [Semiring R] (x : LForestTensorAlgebra α R) : ForestTensorAlgebra R :=
  AddMonoidAlgebra.mapDomain (eraseTermAddHom (α := α)) x

@[simp]
theorem erase_zero [Semiring R] :
    erase (α := α) (R := R) 0 = 0 := by
  simpa [erase] using
    (AddMonoidAlgebra.mapDomain_zero (R := R) (eraseTermAddHom (α := α)))

@[simp]
theorem erase_add [Semiring R] (x y : LForestTensorAlgebra α R) :
    erase (x + y) = erase x + erase y := by
  simp [erase, AddMonoidAlgebra.mapDomain_add]

@[simp]
theorem erase_one [Semiring R] :
    erase (α := α) (R := R) 1 = 1 := by
  simp [erase]

@[simp]
theorem erase_mul [Semiring R] (x y : LForestTensorAlgebra α R) :
    erase (x * y) = erase x * erase y := by
  simpa [erase] using
    (AddMonoidAlgebra.mapDomain_mul (R := R) (f := eraseTermAddHom (α := α)) x y)

@[simp]
theorem erase_ofPair [Semiring R] (term : LRootedForest α × LRootedForest α) :
    erase (R := R) (ofPair (R := R) term) =
      ForestTensorAlgebra.ofPair (R := R) (PLTree.eraseCoproductTerm term) := by
  simp [erase, ofPair, ForestTensorAlgebra.ofPair, eraseTermAddHom]
  rfl

/-- Erasing labels commutes with summing finite tensor basis terms. -/
theorem erase_sumTerms [Semiring R] :
    ∀ terms : List (LRootedForest α × LRootedForest α),
      erase (R := R) (sumTerms (R := R) terms) =
        ForestTensorAlgebra.sumTerms (R := R) (terms.map PLTree.eraseCoproductTerm)
  | [] => by
      simp [sumTerms, ForestTensorAlgebra.sumTerms]
  | term :: terms => by
      rw [sumTerms_cons]
      simp only [List.map_cons]
      rw [ForestTensorAlgebra.sumTerms_cons, erase_add, erase_ofPair, erase_sumTerms terms]

/-- Constantly label tensor basis terms as an additive homomorphism. -/
def constLabelTermAddHom (a : α) :
    (RootedForest × RootedForest) →+ (LRootedForest α × LRootedForest α) where
  toFun := PLTree.constLabelCoproductTerm a
  map_zero' := by
    simp [PLTree.constLabelCoproductTerm, LRootedForest.constLabel]
  map_add' x y := by
    cases x
    cases y
    simp [PLTree.constLabelCoproductTerm, LRootedForest.constLabel_add]

/-- Label every vertex in tensor-coded unlabelled forest algebra terms by the same label. -/
def constLabel [Semiring R] (a : α) (x : ForestTensorAlgebra R) :
    LForestTensorAlgebra α R :=
  AddMonoidAlgebra.mapDomain (constLabelTermAddHom a) x

@[simp]
theorem constLabel_zero [Semiring R] (a : α) :
    constLabel (R := R) a 0 = 0 := by
  simpa [constLabel] using
    (AddMonoidAlgebra.mapDomain_zero (R := R) (constLabelTermAddHom a))

@[simp]
theorem constLabel_add [Semiring R] (a : α) (x y : ForestTensorAlgebra R) :
    constLabel a (x + y) = constLabel a x + constLabel a y := by
  simp [constLabel, AddMonoidAlgebra.mapDomain_add]

@[simp]
theorem constLabel_one [Semiring R] (a : α) :
    constLabel (R := R) a 1 = 1 := by
  simp [constLabel]

@[simp]
theorem constLabel_mul [Semiring R] (a : α) (x y : ForestTensorAlgebra R) :
    constLabel a (x * y) = constLabel a x * constLabel a y := by
  simpa [constLabel] using
    (AddMonoidAlgebra.mapDomain_mul (R := R) (f := constLabelTermAddHom a) x y)

@[simp]
theorem constLabel_ofPair [Semiring R] (a : α) (term : RootedForest × RootedForest) :
    constLabel (R := R) a (ForestTensorAlgebra.ofPair (R := R) term) =
      ofPair (R := R) (PLTree.constLabelCoproductTerm a term) := by
  simp [constLabel, ofPair, ForestTensorAlgebra.ofPair, constLabelTermAddHom]
  rfl

/-- Constant labelling commutes with summing finite tensor basis terms. -/
theorem constLabel_sumTerms [Semiring R] (a : α) :
    ∀ terms : List (RootedForest × RootedForest),
      constLabel (R := R) a (ForestTensorAlgebra.sumTerms (R := R) terms) =
        sumTerms (R := R) (terms.map (PLTree.constLabelCoproductTerm a))
  | [] => by
      simp [sumTerms, ForestTensorAlgebra.sumTerms]
  | term :: terms => by
      rw [ForestTensorAlgebra.sumTerms_cons]
      simp only [List.map_cons]
      rw [sumTerms_cons, constLabel_add, constLabel_ofPair, constLabel_sumTerms a terms]

/-- Relabel tensor basis terms as an additive homomorphism. -/
def mapLabelsTermAddHom {β : Type w} (f : α → β) :
    (LRootedForest α × LRootedForest α) →+ (LRootedForest β × LRootedForest β) where
  toFun := PLTree.mapCoproductTerm f
  map_zero' := by
    simp [PLTree.mapCoproductTerm, LRootedForest.mapLabels]
  map_add' x y := by
    cases x
    cases y
    simp [PLTree.mapCoproductTerm, LRootedForest.mapLabels_add]

/-- Relabel tensor-coded labelled forest algebra terms. -/
def mapLabels [Semiring R] {β : Type w} (f : α → β)
    (x : LForestTensorAlgebra α R) : LForestTensorAlgebra β R :=
  AddMonoidAlgebra.mapDomain (mapLabelsTermAddHom (α := α) f) x

@[simp]
theorem mapLabels_zero [Semiring R] {β : Type w} (f : α → β) :
    mapLabels (R := R) f 0 = 0 := by
  simpa [mapLabels] using
    (AddMonoidAlgebra.mapDomain_zero (R := R) (mapLabelsTermAddHom (α := α) f))

@[simp]
theorem mapLabels_add [Semiring R] {β : Type w} (f : α → β)
    (x y : LForestTensorAlgebra α R) :
    mapLabels f (x + y) = mapLabels f x + mapLabels f y := by
  simp [mapLabels, AddMonoidAlgebra.mapDomain_add]

@[simp]
theorem mapLabels_one [Semiring R] {β : Type w} (f : α → β) :
    mapLabels (R := R) f 1 = 1 := by
  simp [mapLabels]

@[simp]
theorem mapLabels_mul [Semiring R] {β : Type w} (f : α → β)
    (x y : LForestTensorAlgebra α R) :
    mapLabels f (x * y) = mapLabels f x * mapLabels f y := by
  simpa [mapLabels] using
    (AddMonoidAlgebra.mapDomain_mul
      (R := R) (f := mapLabelsTermAddHom (α := α) f) x y)

@[simp]
theorem mapLabels_ofPair [Semiring R] {β : Type w} (f : α → β)
    (term : LRootedForest α × LRootedForest α) :
    mapLabels (R := R) f (ofPair (R := R) term) =
      ofPair (R := R) (PLTree.mapCoproductTerm f term) := by
  simp [mapLabels, ofPair, mapLabelsTermAddHom]
  rfl

/-- Relabelling commutes with summing finite tensor basis terms. -/
theorem mapLabels_sumTerms [Semiring R] {β : Type w} (f : α → β) :
    ∀ terms : List (LRootedForest α × LRootedForest α),
      mapLabels (R := R) f (sumTerms (R := R) terms) =
        sumTerms (R := R) (terms.map (PLTree.mapCoproductTerm f))
  | [] => by
      simp [sumTerms]
  | term :: terms => by
      rw [sumTerms_cons]
      simp only [List.map_cons]
      rw [sumTerms_cons, mapLabels_add, mapLabels_ofPair, mapLabels_sumTerms f terms]

private def counitLeftMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    Multiplicative (LRootedForest α × LRootedForest α) →* LForestAlgebra α R where
  toFun term :=
    LForestAlgebra.counitCoeff (R := R) (Multiplicative.toAdd term).1 •
      LForestAlgebra.ofForest (R := R) (Multiplicative.toAdd term).2
  map_one' := by
    change LForestAlgebra.counitCoeff (R := R) (0 : LRootedForest α) •
      LForestAlgebra.ofForest (R := R) (0 : LRootedForest α) = 1
    simp
  map_mul' x y := by
    cases x
    cases y
    simp [LForestAlgebra.counitCoeff_add, LForestAlgebra.ofForest_add,
      mul_smul]
    rw [smul_comm]

private def counitRightMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    Multiplicative (LRootedForest α × LRootedForest α) →* LForestAlgebra α R where
  toFun term :=
    LForestAlgebra.counitCoeff (R := R) (Multiplicative.toAdd term).2 •
      LForestAlgebra.ofForest (R := R) (Multiplicative.toAdd term).1
  map_one' := by
    change LForestAlgebra.counitCoeff (R := R) (0 : LRootedForest α) •
      LForestAlgebra.ofForest (R := R) (0 : LRootedForest α) = 1
    simp
  map_mul' x y := by
    cases x
    cases y
    simp [LForestAlgebra.counitCoeff_add, LForestAlgebra.ofForest_add,
      mul_smul]
    rw [smul_comm]

/-- Apply the labelled counit to the left tensor factor. -/
def counitLeft [CommSemiring R] :
    LForestTensorAlgebra α R →ₐ[R] LForestAlgebra α R :=
  (AddMonoidAlgebra.lift R (LForestAlgebra α R) (LRootedForest α × LRootedForest α))
    (counitLeftMonoidHom α R)

/-- Apply the labelled counit to the right tensor factor. -/
def counitRight [CommSemiring R] :
    LForestTensorAlgebra α R →ₐ[R] LForestAlgebra α R :=
  (AddMonoidAlgebra.lift R (LForestAlgebra α R) (LRootedForest α × LRootedForest α))
    (counitRightMonoidHom α R)

theorem counitLeft_ofPair [CommSemiring R] (term : LRootedForest α × LRootedForest α) :
    counitLeft (R := R) (ofPair (R := R) term) =
      LForestAlgebra.counitCoeff (R := R) term.1 •
        LForestAlgebra.ofForest (R := R) term.2 := by
  simp [counitLeft, ofPair, counitLeftMonoidHom]

theorem counitRight_ofPair [CommSemiring R] (term : LRootedForest α × LRootedForest α) :
    counitRight (R := R) (ofPair (R := R) term) =
      LForestAlgebra.counitCoeff (R := R) term.2 •
        LForestAlgebra.ofForest (R := R) term.1 := by
  simp [counitRight, ofPair, counitRightMonoidHom]

theorem counitLeft_sumTerms [CommSemiring R]
    (terms : List (LRootedForest α × LRootedForest α)) :
    counitLeft (R := R) (sumTerms (R := R) terms) =
      (terms.map fun term =>
        LForestAlgebra.counitCoeff (R := R) term.1 •
          LForestAlgebra.ofForest (R := R) term.2).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, counitLeft_ofPair, ih]
      simp

theorem counitRight_sumTerms [CommSemiring R]
    (terms : List (LRootedForest α × LRootedForest α)) :
    counitRight (R := R) (sumTerms (R := R) terms) =
      (terms.map fun term =>
        LForestAlgebra.counitCoeff (R := R) term.2 •
          LForestAlgebra.ofForest (R := R) term.1).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, counitRight_ofPair, ih]
      simp

end

end LForestTensorAlgebra

/-- Triple tensor-coded labelled forest algebra:
`(φ, ψ, η)` represents the basis tensor `φ ⊗ ψ ⊗ η`. -/
abbrev LForestTripleTensorAlgebra
    (α : Type u) (R : Type v) [Semiring R] : Type (max u v) :=
  AddMonoidAlgebra R (LRootedForest α × LRootedForest α × LRootedForest α)

namespace LForestTripleTensorAlgebra

noncomputable section

variable {α : Type u} {R : Type v}

/-- The basis triple tensor represented by a triple of labelled rooted forests. -/
def ofTriple [Semiring R]
    (term : LRootedForest α × LRootedForest α × LRootedForest α) :
    LForestTripleTensorAlgebra α R :=
  AddMonoidAlgebra.single term 1

/-- The basis tensor `φ ⊗ ψ ⊗ η`. -/
def ofForests [Semiring R] (φ ψ η : LRootedForest α) :
    LForestTripleTensorAlgebra α R :=
  ofTriple (R := R) (φ, ψ, η)

@[simp]
theorem ofTriple_zero [Semiring R] :
    ofTriple (R := R) (0 : LRootedForest α × LRootedForest α × LRootedForest α) = 1 := by
  simp [ofTriple, AddMonoidAlgebra.one_def]

@[simp]
theorem ofForests_zero_zero_zero [Semiring R] :
    ofForests (R := R) (α := α) 0 0 0 = 1 := by
  change
    ofTriple (R := R)
      (0 : LRootedForest α × LRootedForest α × LRootedForest α) = 1
  simp

@[simp]
theorem ofTriple_add [Semiring R]
    (x y : LRootedForest α × LRootedForest α × LRootedForest α) :
    ofTriple (R := R) (x + y) = ofTriple x * ofTriple y := by
  simp [ofTriple, AddMonoidAlgebra.single_mul_single]

@[simp]
theorem ofForests_add [Semiring R]
    (φ₁ φ₂ ψ₁ ψ₂ η₁ η₂ : LRootedForest α) :
    ofForests (R := R) (φ₁ + φ₂) (ψ₁ + ψ₂) (η₁ + η₂) =
      ofForests φ₁ ψ₁ η₁ * ofForests φ₂ ψ₂ η₂ := by
  simp [ofForests, ofTriple, AddMonoidAlgebra.single_mul_single]

/-- Sum a finite list of labelled basis triple tensors. Duplicates contribute multiplicity. -/
def sumTerms [Semiring R]
    (terms : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    LForestTripleTensorAlgebra α R :=
  (terms.map (ofTriple (R := R))).sum

@[simp]
theorem sumTerms_nil [Semiring R] : sumTerms (R := R) (α := α) [] = 0 :=
  rfl

@[simp]
theorem sumTerms_cons [Semiring R]
    (term : LRootedForest α × LRootedForest α × LRootedForest α)
    (terms : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    sumTerms (R := R) (term :: terms) = ofTriple term + sumTerms terms :=
  rfl

@[simp]
theorem sumTerms_singleton [Semiring R]
    (term : LRootedForest α × LRootedForest α × LRootedForest α) :
    sumTerms (R := R) [term] = ofTriple term := by
  simp [sumTerms]

theorem sumTerms_append [Semiring R]
    (xs ys : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    sumTerms (R := R) (xs ++ ys) = sumTerms xs + sumTerms ys := by
  simp [sumTerms, List.map_append]

theorem sumTerms_perm [Semiring R]
    {xs ys : List (LRootedForest α × LRootedForest α × LRootedForest α)}
    (h : xs.Perm ys) :
    sumTerms (R := R) xs = sumTerms ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Multiply two finite lists of labelled triple tensor basis terms. -/
def multiplyTerms
    (xs ys : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    List (LRootedForest α × LRootedForest α × LRootedForest α) :=
  xs.flatMap fun x =>
    ys.map fun y => x + y

theorem sumTerms_map_add_left [Semiring R]
    (x : LRootedForest α × LRootedForest α × LRootedForest α) :
    ∀ ys : List (LRootedForest α × LRootedForest α × LRootedForest α),
      sumTerms (R := R) (ys.map fun y => x + y) = ofTriple x * sumTerms ys
  | [] => by
      simp [sumTerms]
  | y :: ys => by
      rw [List.map_cons, sumTerms_cons, sumTerms_cons, sumTerms_map_add_left x ys]
      rw [ofTriple_add, mul_add]

theorem sumTerms_multiply [Semiring R]
    (xs ys : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    sumTerms (R := R) (multiplyTerms xs ys) =
      sumTerms xs * sumTerms ys := by
  induction xs with
  | nil =>
      simp [multiplyTerms, sumTerms]
  | cons x xs ih =>
      rw [multiplyTerms]
      rw [multiplyTerms] at ih
      simp only [List.flatMap_cons]
      rw [sumTerms_append, ih, sumTerms_cons]
      rw [sumTerms_map_add_left, add_mul]

/-- Forget labels in a triple tensor basis term, as an additive homomorphism. -/
def eraseTripleTermAddHom :
    (LRootedForest α × LRootedForest α × LRootedForest α) →+
      RootedForest × RootedForest × RootedForest where
  toFun term :=
    (LRootedForest.erase term.1,
      LRootedForest.erase term.2.1,
      LRootedForest.erase term.2.2)
  map_zero' := by
    simp [LRootedForest.erase]
  map_add' x y := by
    rcases x with ⟨φ₁, ψ₁, η₁⟩
    rcases y with ⟨φ₂, ψ₂, η₂⟩
    simp [LRootedForest.erase_add]

/-- Forget labels in the triple tensor-coded labelled forest algebra. -/
def erase [Semiring R] (x : LForestTripleTensorAlgebra α R) :
    ForestTripleTensorAlgebra R :=
  AddMonoidAlgebra.mapDomain (eraseTripleTermAddHom (α := α)) x

@[simp]
theorem erase_zero [Semiring R] :
    erase (α := α) (R := R) 0 = 0 := by
  simpa [erase] using
    (AddMonoidAlgebra.mapDomain_zero (R := R) (eraseTripleTermAddHom (α := α)))

@[simp]
theorem erase_add [Semiring R] (x y : LForestTripleTensorAlgebra α R) :
    erase (x + y) = erase x + erase y := by
  simp [erase, AddMonoidAlgebra.mapDomain_add]

@[simp]
theorem erase_one [Semiring R] :
    erase (α := α) (R := R) 1 = 1 := by
  simp [erase]

@[simp]
theorem erase_mul [Semiring R] (x y : LForestTripleTensorAlgebra α R) :
    erase (x * y) = erase x * erase y := by
  simpa [erase] using
    (AddMonoidAlgebra.mapDomain_mul
      (R := R) (f := eraseTripleTermAddHom (α := α)) x y)

@[simp]
theorem erase_ofTriple [Semiring R]
    (term : LRootedForest α × LRootedForest α × LRootedForest α) :
    erase (R := R) (ofTriple (R := R) term) =
      ForestTripleTensorAlgebra.ofTriple (R := R)
        (eraseTripleTermAddHom (α := α) term) := by
  simp [erase, ofTriple, ForestTripleTensorAlgebra.ofTriple, eraseTripleTermAddHom]

/-- Erasing labels commutes with summing finite triple tensor basis terms. -/
theorem erase_sumTerms [Semiring R] :
    ∀ terms : List (LRootedForest α × LRootedForest α × LRootedForest α),
      erase (R := R) (sumTerms (R := R) terms) =
        ForestTripleTensorAlgebra.sumTerms (R := R)
          (terms.map (eraseTripleTermAddHom (α := α)))
  | [] => by
      simp [sumTerms, ForestTripleTensorAlgebra.sumTerms]
  | term :: terms => by
      rw [sumTerms_cons]
      simp only [List.map_cons]
      rw [ForestTripleTensorAlgebra.sumTerms_cons, erase_add, erase_ofTriple,
        erase_sumTerms terms]

/-- Constantly label triple tensor basis terms as an additive homomorphism. -/
def constLabelTripleTermAddHom (a : α) :
    (RootedForest × RootedForest × RootedForest) →+
      (LRootedForest α × LRootedForest α × LRootedForest α) where
  toFun term :=
    (LRootedForest.constLabel a term.1,
      LRootedForest.constLabel a term.2.1,
      LRootedForest.constLabel a term.2.2)
  map_zero' := by
    simp [LRootedForest.constLabel]
  map_add' x y := by
    rcases x with ⟨φ₁, ψ₁, η₁⟩
    rcases y with ⟨φ₂, ψ₂, η₂⟩
    simp [LRootedForest.constLabel_add]

/-- Label every vertex in triple tensor-coded unlabelled forest algebra terms by one label. -/
def constLabel [Semiring R] (a : α) (x : ForestTripleTensorAlgebra R) :
    LForestTripleTensorAlgebra α R :=
  AddMonoidAlgebra.mapDomain (constLabelTripleTermAddHom a) x

@[simp]
theorem constLabel_zero [Semiring R] (a : α) :
    constLabel (R := R) a 0 = 0 := by
  simpa [constLabel] using
    (AddMonoidAlgebra.mapDomain_zero (R := R) (constLabelTripleTermAddHom a))

@[simp]
theorem constLabel_add [Semiring R] (a : α) (x y : ForestTripleTensorAlgebra R) :
    constLabel a (x + y) = constLabel a x + constLabel a y := by
  simp [constLabel, AddMonoidAlgebra.mapDomain_add]

@[simp]
theorem constLabel_one [Semiring R] (a : α) :
    constLabel (R := R) a 1 = 1 := by
  simp [constLabel]

@[simp]
theorem constLabel_mul [Semiring R] (a : α) (x y : ForestTripleTensorAlgebra R) :
    constLabel a (x * y) = constLabel a x * constLabel a y := by
  simpa [constLabel] using
    (AddMonoidAlgebra.mapDomain_mul
      (R := R) (f := constLabelTripleTermAddHom a) x y)

@[simp]
theorem constLabel_ofTriple [Semiring R] (a : α)
    (term : RootedForest × RootedForest × RootedForest) :
    constLabel (R := R) a (ForestTripleTensorAlgebra.ofTriple (R := R) term) =
      ofTriple (R := R) (constLabelTripleTermAddHom a term) := by
  simp [constLabel, ofTriple, ForestTripleTensorAlgebra.ofTriple, constLabelTripleTermAddHom]

/-- Constant labelling commutes with summing finite triple tensor basis terms. -/
theorem constLabel_sumTerms [Semiring R] (a : α) :
    ∀ terms : List (RootedForest × RootedForest × RootedForest),
      constLabel (R := R) a (ForestTripleTensorAlgebra.sumTerms (R := R) terms) =
        sumTerms (R := R) (terms.map (constLabelTripleTermAddHom a))
  | [] => by
      simp [sumTerms, ForestTripleTensorAlgebra.sumTerms]
  | term :: terms => by
      rw [ForestTripleTensorAlgebra.sumTerms_cons]
      simp only [List.map_cons]
      rw [sumTerms_cons, constLabel_add, constLabel_ofTriple,
        constLabel_sumTerms a terms]

/-- Relabel triple tensor basis terms as an additive homomorphism. -/
def mapLabelsTripleTermAddHom {β : Type w} (f : α → β) :
    (LRootedForest α × LRootedForest α × LRootedForest α) →+
      (LRootedForest β × LRootedForest β × LRootedForest β) where
  toFun term :=
    (LRootedForest.mapLabels f term.1,
      LRootedForest.mapLabels f term.2.1,
      LRootedForest.mapLabels f term.2.2)
  map_zero' := by
    simp [LRootedForest.mapLabels]
  map_add' x y := by
    rcases x with ⟨φ₁, ψ₁, η₁⟩
    rcases y with ⟨φ₂, ψ₂, η₂⟩
    simp [LRootedForest.mapLabels_add]

/-- Relabel triple tensor-coded labelled forest algebra terms. -/
def mapLabels [Semiring R] {β : Type w} (f : α → β)
    (x : LForestTripleTensorAlgebra α R) : LForestTripleTensorAlgebra β R :=
  AddMonoidAlgebra.mapDomain (mapLabelsTripleTermAddHom (α := α) f) x

@[simp]
theorem mapLabels_zero [Semiring R] {β : Type w} (f : α → β) :
    mapLabels (R := R) f 0 = 0 := by
  simpa [mapLabels] using
    (AddMonoidAlgebra.mapDomain_zero (R := R)
      (mapLabelsTripleTermAddHom (α := α) f))

@[simp]
theorem mapLabels_add [Semiring R] {β : Type w} (f : α → β)
    (x y : LForestTripleTensorAlgebra α R) :
    mapLabels f (x + y) = mapLabels f x + mapLabels f y := by
  simp [mapLabels, AddMonoidAlgebra.mapDomain_add]

@[simp]
theorem mapLabels_one [Semiring R] {β : Type w} (f : α → β) :
    mapLabels (R := R) f 1 = 1 := by
  simp [mapLabels]

@[simp]
theorem mapLabels_mul [Semiring R] {β : Type w} (f : α → β)
    (x y : LForestTripleTensorAlgebra α R) :
    mapLabels f (x * y) = mapLabels f x * mapLabels f y := by
  simpa [mapLabels] using
    (AddMonoidAlgebra.mapDomain_mul
      (R := R) (f := mapLabelsTripleTermAddHom (α := α) f) x y)

@[simp]
theorem mapLabels_ofTriple [Semiring R] {β : Type w} (f : α → β)
    (term : LRootedForest α × LRootedForest α × LRootedForest α) :
    mapLabels (R := R) f (ofTriple (R := R) term) =
      ofTriple (R := R) (mapLabelsTripleTermAddHom f term) := by
  simp [mapLabels, ofTriple, mapLabelsTripleTermAddHom]

/-- Relabelling commutes with summing finite triple tensor basis terms. -/
theorem mapLabels_sumTerms [Semiring R] {β : Type w} (f : α → β) :
    ∀ terms : List (LRootedForest α × LRootedForest α × LRootedForest α),
      mapLabels (R := R) f (sumTerms (R := R) terms) =
        sumTerms (R := R) (terms.map (mapLabelsTripleTermAddHom f))
  | [] => by
      simp [sumTerms]
  | term :: terms => by
      rw [sumTerms_cons]
      simp only [List.map_cons]
      rw [sumTerms_cons, mapLabels_add, mapLabels_ofTriple,
        mapLabels_sumTerms f terms]

private def includeLeftPairMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    Multiplicative (LRootedForest α × LRootedForest α) →*
      LForestTripleTensorAlgebra α R where
  toFun term :=
    ofTriple (R := R)
      ((Multiplicative.toAdd term).1, (Multiplicative.toAdd term).2, 0)
  map_one' := by
    change
      ofTriple (R := R)
        (0 : LRootedForest α × LRootedForest α × LRootedForest α) = 1
    simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rcases Multiplicative.toAdd x with ⟨φ₁, ψ₁⟩
    rcases Multiplicative.toAdd y with ⟨φ₂, ψ₂⟩
    simpa using
      (ofTriple_add (R := R) (φ₁, ψ₁, 0) (φ₂, ψ₂, 0))

/-- Embed a labelled pair tensor as the first two factors of a triple tensor. -/
def includeLeftPair [CommSemiring R] : LForestTensorAlgebra α R →ₐ[R]
    LForestTripleTensorAlgebra α R :=
  (AddMonoidAlgebra.lift R
      (LForestTripleTensorAlgebra α R) (LRootedForest α × LRootedForest α))
    (includeLeftPairMonoidHom α R)

@[simp]
theorem includeLeftPair_ofPair [CommSemiring R]
    (term : LRootedForest α × LRootedForest α) :
    includeLeftPair (R := R) (LForestTensorAlgebra.ofPair (R := R) term) =
      ofTriple (R := R) (term.1, term.2, 0) := by
  simp [includeLeftPair, LForestTensorAlgebra.ofPair, includeLeftPairMonoidHom]

@[simp]
theorem includeLeftPair_ofForests [CommSemiring R] (φ ψ : LRootedForest α) :
    includeLeftPair (R := R) (LForestTensorAlgebra.ofForests (R := R) φ ψ) =
      ofForests (R := R) φ ψ 0 := by
  simp [LForestTensorAlgebra.ofForests, ofForests]

private def includeRightPairMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    Multiplicative (LRootedForest α × LRootedForest α) →*
      LForestTripleTensorAlgebra α R where
  toFun term :=
    ofTriple (R := R)
      (0, (Multiplicative.toAdd term).1, (Multiplicative.toAdd term).2)
  map_one' := by
    change
      ofTriple (R := R)
        (0 : LRootedForest α × LRootedForest α × LRootedForest α) = 1
    simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rcases Multiplicative.toAdd x with ⟨φ₁, ψ₁⟩
    rcases Multiplicative.toAdd y with ⟨φ₂, ψ₂⟩
    simpa using
      (ofTriple_add (R := R) (0, φ₁, ψ₁) (0, φ₂, ψ₂))

/-- Embed a labelled pair tensor as the last two factors of a triple tensor. -/
def includeRightPair [CommSemiring R] : LForestTensorAlgebra α R →ₐ[R]
    LForestTripleTensorAlgebra α R :=
  (AddMonoidAlgebra.lift R
      (LForestTripleTensorAlgebra α R) (LRootedForest α × LRootedForest α))
    (includeRightPairMonoidHom α R)

@[simp]
theorem includeRightPair_ofPair [CommSemiring R]
    (term : LRootedForest α × LRootedForest α) :
    includeRightPair (R := R) (LForestTensorAlgebra.ofPair (R := R) term) =
      ofTriple (R := R) (0, term.1, term.2) := by
  simp [includeRightPair, LForestTensorAlgebra.ofPair, includeRightPairMonoidHom]

@[simp]
theorem includeRightPair_ofForests [CommSemiring R] (φ ψ : LRootedForest α) :
    includeRightPair (R := R) (LForestTensorAlgebra.ofForests (R := R) φ ψ) =
      ofForests (R := R) 0 φ ψ := by
  simp [LForestTensorAlgebra.ofForests, ofForests]

theorem erase_includeLeftPair [CommSemiring R] (x : LForestTensorAlgebra α R) :
    erase (R := R) (includeLeftPair (R := R) x) =
      ForestTripleTensorAlgebra.includeLeftPair (R := R)
        (LForestTensorAlgebra.erase (R := R) x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R (eraseTripleTermAddHom (α := α))).comp
        (includeLeftPair (α := α) (R := R))) x =
      (ForestTripleTensorAlgebra.includeLeftPair (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.eraseTermAddHom (α := α))) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    LRootedForest α × LRootedForest α) (by
      intro term
      change
        erase (R := R)
            (includeLeftPair (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
          ForestTripleTensorAlgebra.includeLeftPair (R := R)
            (LForestTensorAlgebra.erase (R := R)
              (LForestTensorAlgebra.ofPair (R := R) term))
      simp [eraseTripleTermAddHom, PLTree.eraseCoproductTerm, LRootedForest.erase]) (by ext)) x

theorem erase_includeRightPair [CommSemiring R] (x : LForestTensorAlgebra α R) :
    erase (R := R) (includeRightPair (R := R) x) =
      ForestTripleTensorAlgebra.includeRightPair (R := R)
        (LForestTensorAlgebra.erase (R := R) x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R (eraseTripleTermAddHom (α := α))).comp
        (includeRightPair (α := α) (R := R))) x =
      (ForestTripleTensorAlgebra.includeRightPair (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.eraseTermAddHom (α := α))) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    LRootedForest α × LRootedForest α) (by
      intro term
      change
        erase (R := R)
            (includeRightPair (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
          ForestTripleTensorAlgebra.includeRightPair (R := R)
            (LForestTensorAlgebra.erase (R := R)
              (LForestTensorAlgebra.ofPair (R := R) term))
      simp [eraseTripleTermAddHom, PLTree.eraseCoproductTerm, LRootedForest.erase]) (by ext)) x

theorem constLabel_includeLeftPair [CommSemiring R] (a : α) (x : ForestTensorAlgebra R) :
    constLabel (R := R) a (ForestTripleTensorAlgebra.includeLeftPair (R := R) x) =
      includeLeftPair (R := R) (LForestTensorAlgebra.constLabel (R := R) a x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R (constLabelTripleTermAddHom a)).comp
        (ForestTripleTensorAlgebra.includeLeftPair (R := R))) x =
      (includeLeftPair (α := α) (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.constLabelTermAddHom a)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    RootedForest × RootedForest) (by
      intro term
      change
        constLabel (R := R) a
            (ForestTripleTensorAlgebra.includeLeftPair (R := R)
              (ForestTensorAlgebra.ofPair (R := R) term)) =
          includeLeftPair (R := R)
            (LForestTensorAlgebra.constLabel (R := R) a
              (ForestTensorAlgebra.ofPair (R := R) term))
      simp [constLabelTripleTermAddHom, PLTree.constLabelCoproductTerm,
        LRootedForest.constLabel]) (by ext)) x

theorem constLabel_includeRightPair [CommSemiring R] (a : α) (x : ForestTensorAlgebra R) :
    constLabel (R := R) a (ForestTripleTensorAlgebra.includeRightPair (R := R) x) =
      includeRightPair (R := R) (LForestTensorAlgebra.constLabel (R := R) a x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R (constLabelTripleTermAddHom a)).comp
        (ForestTripleTensorAlgebra.includeRightPair (R := R))) x =
      (includeRightPair (α := α) (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.constLabelTermAddHom a)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    RootedForest × RootedForest) (by
      intro term
      change
        constLabel (R := R) a
            (ForestTripleTensorAlgebra.includeRightPair (R := R)
              (ForestTensorAlgebra.ofPair (R := R) term)) =
          includeRightPair (R := R)
            (LForestTensorAlgebra.constLabel (R := R) a
              (ForestTensorAlgebra.ofPair (R := R) term))
      simp [constLabelTripleTermAddHom, PLTree.constLabelCoproductTerm,
        LRootedForest.constLabel]) (by ext)) x

theorem mapLabels_includeLeftPair [CommSemiring R] {β : Type w} (f : α → β)
    (x : LForestTensorAlgebra α R) :
    mapLabels (R := R) f (includeLeftPair (R := R) x) =
      includeLeftPair (R := R) (LForestTensorAlgebra.mapLabels (R := R) f x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (mapLabelsTripleTermAddHom (α := α) f)).comp
        (includeLeftPair (α := α) (R := R))) x =
      (includeLeftPair (α := β) (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.mapLabelsTermAddHom (α := α) f)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    LRootedForest α × LRootedForest α) (by
      intro term
      change
        mapLabels (R := R) f
            (includeLeftPair (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
          includeLeftPair (R := R)
            (LForestTensorAlgebra.mapLabels (R := R) f
              (LForestTensorAlgebra.ofPair (R := R) term))
      simp [mapLabelsTripleTermAddHom, PLTree.mapCoproductTerm,
        LRootedForest.mapLabels]) (by ext)) x

theorem mapLabels_includeRightPair [CommSemiring R] {β : Type w} (f : α → β)
    (x : LForestTensorAlgebra α R) :
    mapLabels (R := R) f (includeRightPair (R := R) x) =
      includeRightPair (R := R) (LForestTensorAlgebra.mapLabels (R := R) f x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (mapLabelsTripleTermAddHom (α := α) f)).comp
        (includeRightPair (α := α) (R := R))) x =
      (includeRightPair (α := β) (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.mapLabelsTermAddHom (α := α) f)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    LRootedForest α × LRootedForest α) (by
      intro term
      change
        mapLabels (R := R) f
            (includeRightPair (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
          includeRightPair (R := R)
            (LForestTensorAlgebra.mapLabels (R := R) f
              (LForestTensorAlgebra.ofPair (R := R) term))
      simp [mapLabelsTripleTermAddHom, PLTree.mapCoproductTerm,
        LRootedForest.mapLabels]) (by ext)) x

end

end LForestTripleTensorAlgebra

namespace PLTree

noncomputable section

variable {α : Type u} {R : Type v}

/-- The planar labelled BCK coproduct, represented in the tensor-coded algebra. -/
def labelledCoproduct [Semiring R] (t : PLTree α) : LForestTensorAlgebra α R :=
  LForestTensorAlgebra.sumTerms (R := R) (coproductTerms t)

/-- The reduced planar labelled BCK coproduct, summing only proper cut terms. -/
def labelledReducedCoproduct [Semiring R] (t : PLTree α) :
    LForestTensorAlgebra α R :=
  LForestTensorAlgebra.sumTerms (R := R) (properCoproductTerms t)

theorem labelledReducedCoproduct_perm [Semiring R] {t u : PLTree α}
    (h : PLTree.Perm t u) :
    labelledReducedCoproduct (R := R) t = labelledReducedCoproduct (R := R) u := by
  rw [labelledReducedCoproduct, labelledReducedCoproduct]
  exact LForestTensorAlgebra.sumTerms_perm (R := R) (PLTree.properCoproductTerms_perm h)

theorem labelledCoproduct_eq_of_cuts_listRelPerm [Semiring R] {t u : PLTree α}
    (h : PTree.ListRelPerm Cut.Perm (cuts t) (cuts u)) :
    labelledCoproduct (R := R) t = labelledCoproduct (R := R) u := by
  rw [labelledCoproduct, labelledCoproduct, coproductTerms, coproductTerms]
  exact LForestTensorAlgebra.sumTerms_cut_listRelPerm h

theorem labelledCoproduct_perm [Semiring R] {t u : PLTree α} (h : PLTree.Perm t u) :
    labelledCoproduct (R := R) t = labelledCoproduct (R := R) u :=
  labelledCoproduct_eq_of_cuts_listRelPerm (cuts_listRelPerm_of_perm h)

theorem labelledCoproduct_node [Semiring R] (a : α) (ts : List (PLTree α)) :
    labelledCoproduct (R := R) (.node a ts) =
      LForestTensorAlgebra.sumTerms (R := R)
        ((coproductTermsList ts).map fun term =>
          (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))) +
        LForestTensorAlgebra.ofPair (R := R)
          (LRootedForest.singleton (LRootedTree.ofPLTree (.node a ts)), 0) := by
  rw [labelledCoproduct]
  rw [LForestTensorAlgebra.sumTerms_perm (R := R) (PLTree.coproductTerms_node_perm a ts)]
  rw [LForestTensorAlgebra.sumTerms_append]
  simp

/-- Multiplicative extension of the planar labelled coproduct to labelled forests. -/
def labelledCoproductList [Semiring R] (ts : List (PLTree α)) :
    LForestTensorAlgebra α R :=
  LForestTensorAlgebra.sumTerms (R := R) (coproductTermsList ts)

/-- The reduced planar labelled BCK coproduct of a planar labelled forest. -/
def labelledReducedCoproductList [Semiring R] (ts : List (PLTree α)) :
    LForestTensorAlgebra α R :=
  LForestTensorAlgebra.sumTerms (R := R) (properCoproductTermsList ts)

/-- Erasing labels sends the labelled planar coproduct to the unlabelled coproduct. -/
theorem erase_labelledCoproduct [Semiring R] (t : PLTree α) :
    LForestTensorAlgebra.erase (R := R) (labelledCoproduct (R := R) t) =
      PTree.coproduct (R := R) (PLTree.erase t) := by
  rw [labelledCoproduct, PTree.coproduct, LForestTensorAlgebra.erase_sumTerms]
  rw [coproductTerms_erase]

theorem erase_labelledReducedCoproduct [Semiring R] (t : PLTree α) :
    LForestTensorAlgebra.erase (R := R) (labelledReducedCoproduct (R := R) t) =
      PTree.reducedCoproduct (R := R) (PLTree.erase t) := by
  rw [labelledReducedCoproduct, PTree.reducedCoproduct, LForestTensorAlgebra.erase_sumTerms]
  rw [properCoproductTerms_erase]

/-- Erasing labels sends the labelled planar forest coproduct to the unlabelled coproduct. -/
theorem erase_labelledCoproductList [Semiring R] (ts : List (PLTree α)) :
    LForestTensorAlgebra.erase (R := R) (labelledCoproductList (R := R) ts) =
      PTree.coproductList (R := R) (ts.map PLTree.erase) := by
  rw [labelledCoproductList, PTree.coproductList, LForestTensorAlgebra.erase_sumTerms]
  rw [coproductTermsList_erase]

theorem erase_labelledReducedCoproductList [Semiring R] (ts : List (PLTree α)) :
    LForestTensorAlgebra.erase (R := R) (labelledReducedCoproductList (R := R) ts) =
      PTree.reducedCoproductList (R := R) (ts.map PLTree.erase) := by
  rw [labelledReducedCoproductList, PTree.reducedCoproductList,
    LForestTensorAlgebra.erase_sumTerms]
  rw [properCoproductTermsList_erase]

theorem mapLabels_labelledCoproduct [Semiring R] {β : Type w}
    (f : α → β) (t : PLTree α) :
    LForestTensorAlgebra.mapLabels (R := R) f (labelledCoproduct (R := R) t) =
      labelledCoproduct (R := R) (PLTree.map f t) := by
  rw [labelledCoproduct, labelledCoproduct, LForestTensorAlgebra.mapLabels_sumTerms,
    coproductTerms_map]

theorem mapLabels_labelledReducedCoproduct [Semiring R] {β : Type w}
    (f : α → β) (t : PLTree α) :
    LForestTensorAlgebra.mapLabels (R := R) f (labelledReducedCoproduct (R := R) t) =
      labelledReducedCoproduct (R := R) (PLTree.map f t) := by
  rw [labelledReducedCoproduct, labelledReducedCoproduct,
    LForestTensorAlgebra.mapLabels_sumTerms, properCoproductTerms_map]

theorem mapLabels_labelledCoproductList [Semiring R] {β : Type w}
    (f : α → β) (ts : List (PLTree α)) :
    LForestTensorAlgebra.mapLabels (R := R) f (labelledCoproductList (R := R) ts) =
      labelledCoproductList (R := R) (ts.map (PLTree.map f)) := by
  rw [labelledCoproductList, labelledCoproductList, LForestTensorAlgebra.mapLabels_sumTerms,
    coproductTermsList_map]

theorem mapLabels_labelledReducedCoproductList [Semiring R] {β : Type w}
    (f : α → β) (ts : List (PLTree α)) :
    LForestTensorAlgebra.mapLabels (R := R) f
        (labelledReducedCoproductList (R := R) ts) =
      labelledReducedCoproductList (R := R) (ts.map (PLTree.map f)) := by
  rw [labelledReducedCoproductList, labelledReducedCoproductList,
    LForestTensorAlgebra.mapLabels_sumTerms, properCoproductTermsList_map]

theorem constLabel_labelledCoproduct [Semiring R] (a : α) (t : PTree) :
    LForestTensorAlgebra.constLabel (R := R) a (PTree.coproduct (R := R) t) =
      labelledCoproduct (R := R) (PLTree.constLabel a t) := by
  rw [PTree.coproduct, labelledCoproduct, LForestTensorAlgebra.constLabel_sumTerms,
    coproductTerms_constLabel]

theorem constLabel_labelledReducedCoproduct [Semiring R] (a : α) (t : PTree) :
    LForestTensorAlgebra.constLabel (R := R) a (PTree.reducedCoproduct (R := R) t) =
      labelledReducedCoproduct (R := R) (PLTree.constLabel a t) := by
  rw [PTree.reducedCoproduct, labelledReducedCoproduct,
    LForestTensorAlgebra.constLabel_sumTerms, properCoproductTerms_constLabel]

theorem constLabel_labelledCoproductList [Semiring R] (a : α) (ts : List PTree) :
    LForestTensorAlgebra.constLabel (R := R) a (PTree.coproductList (R := R) ts) =
      labelledCoproductList (R := R) (ts.map (PLTree.constLabel a)) := by
  rw [PTree.coproductList, labelledCoproductList, LForestTensorAlgebra.constLabel_sumTerms,
    coproductTermsList_constLabel]

theorem constLabel_labelledReducedCoproductList [Semiring R] (a : α) (ts : List PTree) :
    LForestTensorAlgebra.constLabel (R := R) a (PTree.reducedCoproductList (R := R) ts) =
      labelledReducedCoproductList (R := R) (ts.map (PLTree.constLabel a)) := by
  rw [PTree.reducedCoproductList, labelledReducedCoproductList,
    LForestTensorAlgebra.constLabel_sumTerms, properCoproductTermsList_constLabel]

@[simp]
theorem labelledCoproductList_nil [Semiring R] :
    labelledCoproductList (R := R) ([] : List (PLTree α)) = 1 := by
  change
    LForestTensorAlgebra.sumTerms (R := R)
      ([(0 : LRootedForest α × LRootedForest α)] :
        List (LRootedForest α × LRootedForest α)) = 1
  simp [LForestTensorAlgebra.sumTerms, LForestTensorAlgebra.ofPair, AddMonoidAlgebra.one_def]

@[simp]
theorem labelledReducedCoproductList_nil [Semiring R] :
    labelledReducedCoproductList (R := R) ([] : List (PLTree α)) = 0 := by
  simp [labelledReducedCoproductList, properCoproductTermsList, coproductTermsList,
    LForestTensorAlgebra.sumTerms]

theorem labelledReducedCoproductList_forall₂_perm [Semiring R]
    {ts us : List (PLTree α)} (h : List.Forall₂ PLTree.Perm ts us) :
    labelledReducedCoproductList (R := R) ts = labelledReducedCoproductList us := by
  rw [labelledReducedCoproductList, labelledReducedCoproductList]
  exact LForestTensorAlgebra.sumTerms_perm (R := R)
    (PLTree.properCoproductTermsList_forall₂_perm h)

@[simp]
theorem labelledCoproductList_cons [Semiring R] (t : PLTree α) (ts : List (PLTree α)) :
    labelledCoproductList (R := R) (t :: ts) =
      labelledCoproduct t * labelledCoproductList ts := by
  simp [
    labelledCoproductList,
    labelledCoproduct,
    coproductTermsList,
    LForestTensorAlgebra.sumTerms_multiply
  ]

@[simp]
theorem labelledCoproductList_singleton [Semiring R] (t : PLTree α) :
    labelledCoproductList (R := R) [t] = labelledCoproduct t := by
  simp

theorem labelledCoproductList_append [Semiring R] (ts us : List (PLTree α)) :
    labelledCoproductList (R := R) (ts ++ us) =
      labelledCoproductList ts * labelledCoproductList us := by
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      simp [ih, mul_assoc]

theorem labelledCoproductList_perm [CommSemiring R] {ts us : List (PLTree α)}
    (h : ts.Perm us) :
    labelledCoproductList (R := R) ts = labelledCoproductList us := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ =>
      simp
      ac_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem labelledCoproductList_forall₂_perm [CommSemiring R] :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ PLTree.Perm ts us →
      labelledCoproductList (R := R) ts = labelledCoproductList us
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
      rw [labelledCoproductList_cons, labelledCoproductList_cons,
        labelledCoproduct_perm h, labelledCoproductList_forall₂_perm hs]

private theorem counitLeft_rootCutTerms [CommSemiring R] :
    ∀ cuts : List (RootCut α),
      (cuts.map fun c =>
          LForestAlgebra.counitCoeff (R := R)
              (c.pruned.map LRootedTree.ofPLTree : LRootedForest α) •
            LForestAlgebra.ofForest (R := R)
              (LRootedForest.singleton (LRootedTree.ofPLTree c.trunk))).sum =
        ((cuts.filterMap RootCut.noPrunedTrunk?).map fun trunk =>
          LForestAlgebra.ofForest (R := R)
            (LRootedForest.singleton (LRootedTree.ofPLTree trunk))).sum
  | [] => by
      simp
  | c :: cuts => by
      cases hpruned : c.pruned with
      | nil =>
          simp [RootCut.noPrunedTrunk?, hpruned, counitLeft_rootCutTerms cuts]
      | cons p ps =>
          have hne :
              (((LRootedTree.ofPLTree p :: ps.map LRootedTree.ofPLTree) :
                  List (LRootedTree α)) : LRootedForest α) ≠ 0 := by
            exact (LRootedForest.order_pos_iff_ne_zero _).1
              (LRootedForest.order_coe_cons_pos (LRootedTree.ofPLTree p)
                (ps.map LRootedTree.ofPLTree))
          simp [RootCut.noPrunedTrunk?, hpruned, counitLeft_rootCutTerms cuts,
            LForestAlgebra.counitCoeff_ne_zero hne]

private theorem counitRight_rootCutTerms [CommSemiring R] :
    ∀ cuts : List (RootCut α),
      (cuts.map fun c =>
          LForestAlgebra.counitCoeff (R := R)
              (LRootedForest.singleton (LRootedTree.ofPLTree c.trunk)) •
            LForestAlgebra.ofForest (R := R)
              (c.pruned.map LRootedTree.ofPLTree : LRootedForest α)).sum = 0
  | [] => by
      simp
  | c :: cuts => by
      have hne :
          LRootedForest.singleton (LRootedTree.ofPLTree c.trunk) ≠ 0 :=
        (LRootedForest.order_pos_iff_ne_zero _).1 (by
          simpa using LRootedTree.order_pos (LRootedTree.ofPLTree c.trunk))
      simp [counitRight_rootCutTerms cuts, LForestAlgebra.counitCoeff_ne_zero hne]

theorem counitLeft_labelledCoproduct [CommSemiring R] (t : PLTree α) :
    LForestTensorAlgebra.counitLeft (R := R) (labelledCoproduct (R := R) t) =
      LForestAlgebra.ofForest (R := R)
        (LRootedForest.singleton (LRootedTree.ofPLTree t)) := by
  rw [labelledCoproduct, LForestTensorAlgebra.counitLeft_sumTerms, coproductTerms, cuts]
  simp only [List.map_append, List.map_map, List.sum_append]
  change
    ((rootCuts t).map
          (fun c =>
            LForestAlgebra.counitCoeff (R := R)
                (c.pruned.map LRootedTree.ofPLTree : LRootedForest α) •
              LForestAlgebra.ofForest (R := R)
                (LRootedForest.singleton (LRootedTree.ofPLTree c.trunk)))).sum +
        (List.map
            (fun c : Cut α =>
              LForestAlgebra.counitCoeff (R := R) c.prunedForest •
                LForestAlgebra.ofForest (R := R) c.trunkForest)
            ([{ pruned := [t], trunk? := none }] : List (Cut α))).sum =
      LForestAlgebra.ofForest (R := R)
        (LRootedForest.singleton (LRootedTree.ofPLTree t))
  rw [counitLeft_rootCutTerms, rootCuts_noPrunedTrunks]
  have hne :
      LRootedForest.singleton (LRootedTree.ofPLTree t) ≠ 0 :=
    (LRootedForest.order_pos_iff_ne_zero _).1 (by
      simpa using LRootedTree.order_pos (LRootedTree.ofPLTree t))
  have hne' : ({LRootedTree.ofPLTree t} : LRootedForest α) ≠ 0 := by
    exact hne
  simp [Cut.prunedForest, Cut.trunkForest, LRootedForest.singleton]
  rw [LForestAlgebra.counitCoeff_ne_zero hne']
  simp

theorem counitRight_labelledCoproduct [CommSemiring R] (t : PLTree α) :
    LForestTensorAlgebra.counitRight (R := R) (labelledCoproduct (R := R) t) =
      LForestAlgebra.ofForest (R := R)
        (LRootedForest.singleton (LRootedTree.ofPLTree t)) := by
  rw [labelledCoproduct, LForestTensorAlgebra.counitRight_sumTerms, coproductTerms, cuts]
  simp only [List.map_append, List.map_map, List.sum_append]
  change
    ((rootCuts t).map
          (fun c =>
            LForestAlgebra.counitCoeff (R := R)
                (LRootedForest.singleton (LRootedTree.ofPLTree c.trunk)) •
              LForestAlgebra.ofForest (R := R)
                (c.pruned.map LRootedTree.ofPLTree : LRootedForest α))).sum +
        (List.map
            (fun c : Cut α =>
              LForestAlgebra.counitCoeff (R := R) c.trunkForest •
                LForestAlgebra.ofForest (R := R) c.prunedForest)
            ([{ pruned := [t], trunk? := none }] : List (Cut α))).sum =
      LForestAlgebra.ofForest (R := R)
        (LRootedForest.singleton (LRootedTree.ofPLTree t))
  rw [counitRight_rootCutTerms]
  simp [Cut.prunedForest, Cut.trunkForest, LRootedForest.singleton]

end

end PLTree

namespace LRootedForest

noncomputable section

variable {α : Type u} {R : Type v}

private theorem order_out (τ : LRootedTree α) :
    PLTree.order (Quotient.out τ) = LRootedTree.order τ := by
  rw [← LRootedTree.order_ofPLTree (Quotient.out τ)]
  rw [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ]

private theorem orderList_out :
    ∀ ts : List (LRootedTree α),
      PLTree.orderList (ts.map Quotient.out) = LRootedForest.order (ts : LRootedForest α)
  | [] => rfl
  | τ :: ts => by
      simp [LRootedForest.order, order_out τ, orderList_out ts]

theorem coproductTermsList_out_order
    {ts : List (LRootedTree α)} {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ PLTree.coproductTermsList (ts.map Quotient.out)) :
    LRootedForest.order term.1 + LRootedForest.order term.2 =
      LRootedForest.order (ts : LRootedForest α) := by
  rw [← orderList_out ts]
  exact PLTree.coproductTermsList_order hterm

/-- A finite representative list for the labelled forest coproduct, using `Quotient.out`. -/
def coproductTerms (φ : LRootedForest α) : List (LRootedForest α × LRootedForest α) :=
  PLTree.coproductTermsList ((Quotient.out φ).map Quotient.out)

theorem coproductTerms_order {φ : LRootedForest α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ coproductTerms φ) :
    LRootedForest.order term.1 + LRootedForest.order term.2 =
      LRootedForest.order φ := by
  conv_rhs =>
    rw [(show ((Quotient.out φ : List (LRootedTree α)) : LRootedForest α) = φ from
      Quotient.out_eq φ).symm]
  exact coproductTermsList_out_order (ts := Quotient.out φ) hterm

private theorem out_map_out_ofPLTree_coe (φ : LRootedForest α) :
    ((((Quotient.out φ).map Quotient.out).map LRootedTree.ofPLTree :
        List (LRootedTree α)) : LRootedForest α) = φ := by
  have hmap :
      (((Quotient.out φ).map Quotient.out).map LRootedTree.ofPLTree) =
        (Quotient.out φ : List (LRootedTree α)) := by
    induction Quotient.out φ with
    | nil => rfl
    | cons τ ts ih =>
        simp [LRootedTree.ofPLTree_out τ, ih]
  calc
    ((((Quotient.out φ).map Quotient.out).map LRootedTree.ofPLTree :
        List (LRootedTree α)) : LRootedForest α) =
        ((Quotient.out φ : List (LRootedTree α)) : LRootedForest α) := by
          rw [hmap]
    _ = φ := Quotient.out_eq φ

/-- The only labelled forest coproduct terms with empty left factor are `1 ⊗ φ`. -/
theorem coproductTerms_left_eq_zero {φ : LRootedForest α}
    {term : LRootedForest α × LRootedForest α} (hterm : term ∈ coproductTerms φ)
    (hleft : term.1 = 0) :
    term.2 = φ := by
  rw [coproductTerms] at hterm
  calc
    term.2 =
        ((((Quotient.out φ).map Quotient.out).map LRootedTree.ofPLTree :
          List (LRootedTree α)) : LRootedForest α) := by
      exact PLTree.coproductTermsList_left_eq_zero hterm hleft
    _ = φ := out_map_out_ofPLTree_coe φ

/-- The only labelled forest coproduct terms with empty right factor are `φ ⊗ 1`. -/
theorem coproductTerms_right_eq_zero {φ : LRootedForest α}
    {term : LRootedForest α × LRootedForest α} (hterm : term ∈ coproductTerms φ)
    (hright : term.2 = 0) :
    term.1 = φ := by
  rw [coproductTerms] at hterm
  calc
    term.1 =
        ((((Quotient.out φ).map Quotient.out).map LRootedTree.ofPLTree :
          List (LRootedTree α)) : LRootedForest α) := by
      exact PLTree.coproductTermsList_right_eq_zero hterm hright
    _ = φ := out_map_out_ofPLTree_coe φ

/-- The labelled forest coproduct has exactly one term with empty left factor. -/
theorem coproductTerms_leftBoundaryCoproductTerm (φ : LRootedForest α) :
    (coproductTerms φ).filterMap PLTree.leftBoundaryCoproductTerm? =
      [((0 : LRootedForest α), φ)] := by
  rw [coproductTerms]
  calc
    (PLTree.coproductTermsList ((Quotient.out φ).map Quotient.out)).filterMap
        PLTree.leftBoundaryCoproductTerm? =
      [((0 : LRootedForest α),
        ((((Quotient.out φ).map Quotient.out).map LRootedTree.ofPLTree :
          List (LRootedTree α)) : LRootedForest α))] :=
        PLTree.coproductTermsList_leftBoundaryCoproductTerm
          ((Quotient.out φ).map Quotient.out)
    _ = [((0 : LRootedForest α), φ)] := by
      rw [out_map_out_ofPLTree_coe φ]

/-- The labelled forest coproduct has exactly one term with empty right factor. -/
theorem coproductTerms_rightBoundaryCoproductTerm (φ : LRootedForest α) :
    (coproductTerms φ).filterMap PLTree.rightBoundaryCoproductTerm? =
      [(φ, (0 : LRootedForest α))] := by
  rw [coproductTerms]
  calc
    (PLTree.coproductTermsList ((Quotient.out φ).map Quotient.out)).filterMap
        PLTree.rightBoundaryCoproductTerm? =
      [(((((Quotient.out φ).map Quotient.out).map LRootedTree.ofPLTree :
          List (LRootedTree α)) : LRootedForest α), (0 : LRootedForest α))] :=
        PLTree.coproductTermsList_rightBoundaryCoproductTerm
          ((Quotient.out φ).map Quotient.out)
    _ = [(φ, (0 : LRootedForest α))] := by
      rw [out_map_out_ofPLTree_coe φ]

theorem coproductTerms_ofPLTree_list_perm (ts : List (PLTree α)) :
    (coproductTerms ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) :
      LRootedForest α)).Perm (PLTree.coproductTermsList ts) := by
  rw [coproductTerms]
  apply PLTree.coproductTermsList_forestPerm
  let φ : LRootedForest α :=
    ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α)
  change PLTree.ForestPerm ((Quotient.out φ).map Quotient.out) ts
  dsimp [PLTree.ForestPerm]
  have hmap :
      (((Quotient.out φ).map Quotient.out).map LRootedTree.ofPLTree) =
        (Quotient.out φ : List (LRootedTree α)) := by
    induction Quotient.out φ with
    | nil => rfl
    | cons τ ts ih =>
        simp [LRootedTree.ofPLTree_out τ, ih]
  calc
    ((((Quotient.out φ).map Quotient.out).map LRootedTree.ofPLTree :
        List (LRootedTree α)) : LRootedForest α) =
        ((Quotient.out φ : List (LRootedTree α)) : LRootedForest α) := by
          rw [hmap]
    _ = ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) :=
        Quotient.out_eq φ

theorem coproductTerms_singleton_ofPLTree_perm (t : PLTree α) :
    (coproductTerms (LRootedForest.singleton (LRootedTree.ofPLTree t))).Perm
      (PLTree.coproductTerms t) := by
  have hsingleton :
      (PLTree.coproductTermsList [t]).Perm (PLTree.coproductTerms t) := by
    simp [PLTree.coproductTermsList, PLTree.multiplyCoproductTerms]
  simpa [LRootedForest.singleton] using
    (coproductTerms_ofPLTree_list_perm [t]).trans hsingleton

theorem coproductTerms_singleton_graft_perm (a : α) (φ : LRootedForest α) :
    (coproductTerms (LRootedForest.singleton (LRootedForest.graft a φ))).Perm
      (((coproductTerms φ).map fun term =>
          (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))) ++
        [(LRootedForest.singleton (LRootedForest.graft a φ), 0)]) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  have hts :
      ((((ts.map Quotient.out).map LRootedTree.ofPLTree : List (LRootedTree α)) :
          LRootedForest α) = (ts : LRootedForest α)) := by
    have hmap : (ts.map Quotient.out).map LRootedTree.ofPLTree = ts := by
      induction ts with
      | nil => rfl
      | cons τ ts ih =>
          simp [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ,
            ih]
    rw [hmap]
  have hforest :
      (coproductTerms (ts : LRootedForest α)).Perm
        (PLTree.coproductTermsList (ts.map Quotient.out)) := by
    have h := coproductTerms_ofPLTree_list_perm (ts.map Quotient.out)
    rw [hts] at h
    exact h
  have hnode :
      (coproductTerms (LRootedForest.singleton
          (LRootedTree.ofPLTree (PLTree.node a (ts.map Quotient.out))))).Perm
        (((PLTree.coproductTermsList (ts.map Quotient.out)).map fun term =>
            (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))) ++
          [(LRootedForest.singleton
              (LRootedTree.ofPLTree (PLTree.node a (ts.map Quotient.out))), 0)]) :=
    (coproductTerms_singleton_ofPLTree_perm (PLTree.node a (ts.map Quotient.out))).trans
      (PLTree.coproductTerms_node_perm a (ts.map Quotient.out))
  simpa [LRootedForest.graft_coe] using
    hnode.trans ((hforest.symm.map fun term =>
      (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))).append_right _)

theorem coproductTerms_add_perm (φ ψ : LRootedForest α) :
    (coproductTerms (φ + ψ)).Perm
      (PLTree.multiplyCoproductTerms (coproductTerms φ) (coproductTerms ψ)) := by
  let ts := (Quotient.out φ).map Quotient.out
  let us := (Quotient.out ψ).map Quotient.out
  have hφ :
      ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) = φ := by
    simpa [ts] using out_map_out_ofPLTree_coe φ
  have hψ :
      ((us.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) = ψ := by
    simpa [us] using out_map_out_ofPLTree_coe ψ
  have hsum :
      (((ts ++ us).map LRootedTree.ofPLTree : List (LRootedTree α)) :
          LRootedForest α) = φ + ψ := by
    rw [List.map_append]
    change
      ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) +
          ((us.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) =
        φ + ψ
    rw [hφ, hψ]
  have hleft :
      (coproductTerms (φ + ψ)).Perm (PLTree.coproductTermsList (ts ++ us)) := by
    rw [← hsum]
    exact coproductTerms_ofPLTree_list_perm (ts ++ us)
  have hφterms : (PLTree.coproductTermsList ts).Perm (coproductTerms φ) := by
    rw [← hφ]
    exact (coproductTerms_ofPLTree_list_perm ts).symm
  have hψterms : (PLTree.coproductTermsList us).Perm (coproductTerms ψ) := by
    rw [← hψ]
    exact (coproductTerms_ofPLTree_list_perm us).symm
  exact hleft.trans
    ((PLTree.coproductTermsList_append_perm ts us).trans
      (PLTree.multiplyCoproductTerms_perm hφterms hψterms))

/-- A finite representative list for the reduced labelled forest coproduct. -/
def properCoproductTerms (φ : LRootedForest α) :
    List (LRootedForest α × LRootedForest α) :=
  (coproductTerms φ).filter fun term =>
    0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2

theorem properCoproductTerms_mem_coproductTerms {φ : LRootedForest α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTerms φ) :
    term ∈ coproductTerms φ :=
  (List.mem_filter.1 hterm).1

theorem properCoproductTerms_order {φ : LRootedForest α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTerms φ) :
    LRootedForest.order term.1 + LRootedForest.order term.2 =
      LRootedForest.order φ :=
  coproductTerms_order (properCoproductTerms_mem_coproductTerms hterm)

theorem properCoproductTerms_left_order_lt {φ : LRootedForest α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTerms φ) :
    LRootedForest.order term.1 < LRootedForest.order φ := by
  have hproper :
      0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hright_pos : 0 < LRootedForest.order term.2 := hproper.2
  have horder := properCoproductTerms_order hterm
  omega

theorem properCoproductTerms_right_order_lt {φ : LRootedForest α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTerms φ) :
    LRootedForest.order term.2 < LRootedForest.order φ := by
  have hproper :
      0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hleft_pos : 0 < LRootedForest.order term.1 := hproper.1
  have horder := properCoproductTerms_order hterm
  omega

theorem coproductTerms_erase_perm (φ : LRootedForest α) :
    ((coproductTerms φ).map PLTree.eraseCoproductTerm).Perm
      (RootedForest.coproductTerms (LRootedForest.erase φ)) := by
  rw [coproductTerms, PLTree.coproductTermsList_erase]
  have hforall :
      List.Forall₂ PTree.Perm
        (((Quotient.out φ).map Quotient.out).map PLTree.erase)
        (((Quotient.out φ).map LRootedTree.erase).map Quotient.out) := by
    induction Quotient.out φ with
    | nil => exact List.Forall₂.nil
    | cons τ ts ih =>
        exact List.Forall₂.cons (LRootedTree.erase_out_perm τ) ih
  refine (PTree.coproductTermsList_forall₂_perm hforall).trans ?_
  change
      (PTree.coproductTermsList (((Quotient.out φ).map LRootedTree.erase).map Quotient.out)).Perm
        (PTree.coproductTermsList
          ((Quotient.out (LRootedForest.erase φ)).map Quotient.out))
  exact PTree.coproductTermsList_forestPerm
    (PTree.ForestPerm.of_list_perm ((LRootedForest.erase_out_perm φ).map Quotient.out))

theorem properCoproductTerms_erase_perm (φ : LRootedForest α) :
    ((properCoproductTerms φ).map PLTree.eraseCoproductTerm).Perm
      (RootedForest.properCoproductTerms (LRootedForest.erase φ)) := by
  change
    ((PLTree.properCoproductTermsList ((Quotient.out φ).map Quotient.out)).map
        PLTree.eraseCoproductTerm).Perm
      (RootedForest.properCoproductTerms (LRootedForest.erase φ))
  rw [PLTree.properCoproductTermsList_erase]
  have hforall :
      List.Forall₂ PTree.Perm
        (((Quotient.out φ).map Quotient.out).map PLTree.erase)
        (((Quotient.out φ).map LRootedTree.erase).map Quotient.out) := by
    induction Quotient.out φ with
    | nil => exact List.Forall₂.nil
    | cons τ ts ih =>
        exact List.Forall₂.cons (LRootedTree.erase_out_perm τ) ih
  refine (PTree.properCoproductTermsList_forall₂_perm hforall).trans ?_
  change
      (PTree.properCoproductTermsList (((Quotient.out φ).map LRootedTree.erase).map Quotient.out)).Perm
        (PTree.properCoproductTermsList
          ((Quotient.out (LRootedForest.erase φ)).map Quotient.out))
  apply List.Perm.filter
  exact PTree.coproductTermsList_forestPerm
    (PTree.ForestPerm.of_list_perm ((LRootedForest.erase_out_perm φ).map Quotient.out))

theorem properCoproductTerms_mapLabels_perm {β : Type w} (f : α → β)
    (φ : LRootedForest α) :
    ((properCoproductTerms φ).map (PLTree.mapCoproductTerm f)).Perm
      (properCoproductTerms (LRootedForest.mapLabels f φ)) := by
  change
    ((PLTree.properCoproductTermsList ((Quotient.out φ).map Quotient.out)).map
        (PLTree.mapCoproductTerm f)).Perm
      (PLTree.properCoproductTermsList
        ((Quotient.out (LRootedForest.mapLabels f φ)).map Quotient.out))
  rw [← PLTree.properCoproductTermsList_map f ((Quotient.out φ).map Quotient.out)]
  have hlist :
      ((Quotient.out (LRootedForest.mapLabels f φ)).map Quotient.out).Perm
        (((Quotient.out φ).map (LRootedTree.map f)).map Quotient.out) :=
    ((LRootedForest.mapLabels_out_perm f φ).map Quotient.out).symm
  have hpermList :
      (PLTree.properCoproductTermsList
          ((Quotient.out (LRootedForest.mapLabels f φ)).map Quotient.out)).Perm
        (PLTree.properCoproductTermsList
          (((Quotient.out φ).map (LRootedTree.map f)).map Quotient.out)) :=
    List.Perm.filter _ (PLTree.coproductTermsList_perm_of_list_perm hlist)
  have hforall :
      List.Forall₂ PLTree.Perm
        (((Quotient.out φ).map (LRootedTree.map f)).map Quotient.out)
        (((Quotient.out φ).map Quotient.out).map (PLTree.map f)) := by
    induction Quotient.out φ with
    | nil => exact List.Forall₂.nil
    | cons τ ts ih =>
        exact List.Forall₂.cons (LRootedTree.map_out_perm f τ).symm ih
  exact (PLTree.properCoproductTermsList_forall₂_perm hforall).symm.trans
    hpermList.symm

theorem properCoproductTerms_constLabel_perm (a : α) (φ : RootedForest) :
    ((RootedForest.properCoproductTerms φ).map (PLTree.constLabelCoproductTerm a)).Perm
      (properCoproductTerms (LRootedForest.constLabel a φ)) := by
  change
    ((PTree.properCoproductTermsList ((Quotient.out φ).map Quotient.out)).map
        (PLTree.constLabelCoproductTerm a)).Perm
      (PLTree.properCoproductTermsList
        ((Quotient.out (LRootedForest.constLabel a φ)).map Quotient.out))
  rw [← PLTree.properCoproductTermsList_constLabel a ((Quotient.out φ).map Quotient.out)]
  have hlist :
      ((Quotient.out (LRootedForest.constLabel a φ)).map Quotient.out).Perm
        (((Quotient.out φ).map (LRootedTree.constLabel a)).map Quotient.out) :=
    ((LRootedForest.constLabel_out_perm a φ).map Quotient.out).symm
  have hpermList :
      (PLTree.properCoproductTermsList
          ((Quotient.out (LRootedForest.constLabel a φ)).map Quotient.out)).Perm
        (PLTree.properCoproductTermsList
          (((Quotient.out φ).map (LRootedTree.constLabel a)).map Quotient.out)) :=
    List.Perm.filter _ (PLTree.coproductTermsList_perm_of_list_perm hlist)
  have hforall :
      List.Forall₂ PLTree.Perm
        (((Quotient.out φ).map (LRootedTree.constLabel a)).map Quotient.out)
        (((Quotient.out φ).map Quotient.out).map (PLTree.constLabel a)) := by
    induction Quotient.out φ with
    | nil => exact List.Forall₂.nil
    | cons τ ts ih =>
        exact List.Forall₂.cons (LRootedTree.constLabel_out_perm a τ).symm ih
  exact (PLTree.properCoproductTermsList_forall₂_perm hforall).symm.trans
    hpermList.symm

/-- The multiplicative labelled coproduct of a non-planar labelled forest. -/
def coproduct [CommSemiring R] (φ : LRootedForest α) : LForestTensorAlgebra α R :=
  Quotient.lift
    (fun ts : List (LRootedTree α) =>
      PLTree.labelledCoproductList (R := R) (ts.map Quotient.out))
    (fun (ts us : List (LRootedTree α)) (h : ts.Perm us) =>
      PLTree.labelledCoproductList_perm (R := R) (List.Perm.map Quotient.out h))
    φ

@[simp]
theorem coproduct_coe [CommSemiring R] (ts : List (LRootedTree α)) :
    coproduct (R := R) (ts : LRootedForest α) =
      PLTree.labelledCoproductList (R := R) (ts.map Quotient.out) :=
  rfl

theorem coproduct_ofPLTree_list [CommSemiring R] (ts : List (PLTree α)) :
    coproduct (R := R) ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) :
        LRootedForest α) =
      PLTree.labelledCoproductList (R := R) ts := by
  change
    PLTree.labelledCoproductList (R := R)
        ((ts.map LRootedTree.ofPLTree).map Quotient.out) =
      PLTree.labelledCoproductList (R := R) ts
  exact PLTree.labelledCoproductList_forall₂_perm (R := R) (by
    induction ts with
    | nil => exact List.Forall₂.nil
    | cons t ts ih =>
        exact List.Forall₂.cons (LRootedTree.out_perm_ofPLTree t) ih)

theorem coproduct_eq_sumTerms_coproductTerms [CommSemiring R] (φ : LRootedForest α) :
    coproduct (R := R) φ =
      LForestTensorAlgebra.sumTerms (R := R) (coproductTerms φ) := by
  change
    coproduct (R := R) φ =
      PLTree.labelledCoproductList (R := R) ((Quotient.out φ).map Quotient.out)
  conv_lhs =>
    rw [(show ((Quotient.out φ : List (LRootedTree α)) : LRootedForest α) = φ from
      Quotient.out_eq φ).symm]
  rfl

/-- The reduced BCK coproduct of a non-planar labelled forest. -/
def reducedCoproduct [Semiring R] (φ : LRootedForest α) :
    LForestTensorAlgebra α R :=
  LForestTensorAlgebra.sumTerms (R := R) (properCoproductTerms φ)

@[simp]
theorem reducedCoproduct_zero [Semiring R] :
    reducedCoproduct (R := R) (0 : LRootedForest α) = 0 := by
  cases hterms : properCoproductTerms (0 : LRootedForest α) with
  | nil =>
      simp [reducedCoproduct, hterms]
  | cons term terms =>
      have hmem : term ∈ properCoproductTerms (0 : LRootedForest α) := by
        rw [hterms]
        simp
      have hproper :
          0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2 :=
        of_decide_eq_true (List.mem_filter.1 hmem).2
      have horder := properCoproductTerms_order hmem
      rw [LRootedForest.order_zero] at horder
      omega

@[simp]
theorem reducedCoproduct_empty [Semiring R] :
    reducedCoproduct (R := R) (LRootedForest.empty : LRootedForest α) = 0 := by
  simp [LRootedForest.empty]

@[simp]
theorem coproduct_zero [CommSemiring R] :
    coproduct (R := R) (0 : LRootedForest α) = 1 := by
  change
    PLTree.labelledCoproductList (R := R)
      (([] : List (LRootedTree α)).map Quotient.out) = 1
  simp

@[simp]
theorem coproduct_empty [CommSemiring R] :
    coproduct (R := R) (LRootedForest.empty : LRootedForest α) = 1 := by
  simp [LRootedForest.empty]

@[simp]
theorem coproduct_singleton [CommSemiring R] (τ : LRootedTree α) :
    coproduct (R := R) (LRootedForest.singleton τ) =
      PLTree.labelledCoproduct (R := R) (Quotient.out τ) := by
  change
    PLTree.labelledCoproductList (R := R) ([τ].map Quotient.out) =
      PLTree.labelledCoproduct (R := R) (Quotient.out τ)
  simp

theorem coproduct_singleton_ofPLTree [CommSemiring R] (t : PLTree α) :
    coproduct (R := R) (LRootedForest.singleton (LRootedTree.ofPLTree t)) =
      PLTree.labelledCoproduct (R := R) t := by
  rw [coproduct_singleton]
  exact PLTree.labelledCoproduct_perm (LRootedTree.out_perm_ofPLTree t)

@[simp]
theorem coproduct_add [CommSemiring R] (φ ψ : LRootedForest α) :
    coproduct (R := R) (φ + ψ) = coproduct φ * coproduct ψ := by
  refine Quotient.inductionOn₂ φ ψ ?_
  intro ts us
  change
    PLTree.labelledCoproductList (R := R) ((ts ++ us).map Quotient.out) =
      PLTree.labelledCoproductList (R := R) (ts.map Quotient.out) *
        PLTree.labelledCoproductList (R := R) (us.map Quotient.out)
  rw [List.map_append, PLTree.labelledCoproductList_append]

theorem counitLeft_coproduct [CommSemiring R] (φ : LRootedForest α) :
    LForestTensorAlgebra.counitLeft (R := R) (coproduct (R := R) φ) =
      LForestAlgebra.ofForest (R := R) φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp
  | cons τ ts ih =>
      change
        LForestTensorAlgebra.counitLeft (R := R)
            (PLTree.labelledCoproductList (R := R) ((τ :: ts).map Quotient.out)) =
          LForestAlgebra.ofForest (R := R)
            (((τ :: ts) : List (LRootedTree α)) : LRootedForest α)
      simp only [List.map_cons, PLTree.labelledCoproductList_cons, map_mul]
      rw [PLTree.counitLeft_labelledCoproduct]
      have ih' :
          LForestTensorAlgebra.counitLeft (R := R)
              (PLTree.labelledCoproductList (R := R) (ts.map Quotient.out)) =
            LForestAlgebra.ofForest (R := R) (ts : LRootedForest α) := by
        simpa using ih
      rw [ih']
      rw [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ]
      rw [← LForestAlgebra.ofForest_add]
      simp [LRootedForest.singleton]

theorem counitRight_coproduct [CommSemiring R] (φ : LRootedForest α) :
    LForestTensorAlgebra.counitRight (R := R) (coproduct (R := R) φ) =
      LForestAlgebra.ofForest (R := R) φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp
  | cons τ ts ih =>
      change
        LForestTensorAlgebra.counitRight (R := R)
            (PLTree.labelledCoproductList (R := R) ((τ :: ts).map Quotient.out)) =
          LForestAlgebra.ofForest (R := R)
            (((τ :: ts) : List (LRootedTree α)) : LRootedForest α)
      simp only [List.map_cons, PLTree.labelledCoproductList_cons, map_mul]
      rw [PLTree.counitRight_labelledCoproduct]
      have ih' :
          LForestTensorAlgebra.counitRight (R := R)
              (PLTree.labelledCoproductList (R := R) (ts.map Quotient.out)) =
            LForestAlgebra.ofForest (R := R) (ts : LRootedForest α) := by
        simpa using ih
      rw [ih']
      rw [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ]
      rw [← LForestAlgebra.ofForest_add]
      simp [LRootedForest.singleton]

theorem erase_coproduct [CommSemiring R] (φ : LRootedForest α) :
    LForestTensorAlgebra.erase (R := R) (coproduct (R := R) φ) =
      RootedForest.coproduct (R := R) (LRootedForest.erase φ) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change
    LForestTensorAlgebra.erase (R := R)
        (PLTree.labelledCoproductList (R := R) (ts.map Quotient.out)) =
      RootedForest.coproduct (R := R)
        (LRootedForest.erase ((ts : List (LRootedTree α)) : LRootedForest α))
  rw [PLTree.erase_labelledCoproductList]
  change
    PTree.coproductList (R := R) ((ts.map Quotient.out).map PLTree.erase) =
      PTree.coproductList (R := R) ((ts.map LRootedTree.erase).map Quotient.out)
  exact PTree.coproductList_forall₂_perm (R := R) (by
    induction ts with
    | nil => exact List.Forall₂.nil
    | cons τ ts ih =>
        exact List.Forall₂.cons (LRootedTree.erase_out_perm τ) ih)

theorem mapLabels_coproduct [CommSemiring R] {β : Type w}
    (f : α → β) (φ : LRootedForest α) :
    LForestTensorAlgebra.mapLabels (R := R) f (coproduct (R := R) φ) =
      coproduct (R := R) (LRootedForest.mapLabels f φ) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change
    LForestTensorAlgebra.mapLabels (R := R) f
        (PLTree.labelledCoproductList (R := R) (ts.map Quotient.out)) =
      coproduct (R := R)
        (LRootedForest.mapLabels f ((ts : List (LRootedTree α)) : LRootedForest α))
  rw [PLTree.mapLabels_labelledCoproductList]
  change
    PLTree.labelledCoproductList (R := R) ((ts.map Quotient.out).map (PLTree.map f)) =
      PLTree.labelledCoproductList (R := R) ((ts.map (LRootedTree.map f)).map Quotient.out)
  exact PLTree.labelledCoproductList_forall₂_perm (R := R) (by
    induction ts with
    | nil =>
        exact List.Forall₂.nil
    | cons τ ts ih =>
        exact List.Forall₂.cons (LRootedTree.map_out_perm f τ) ih)

theorem constLabel_coproduct [CommSemiring R] (a : α) (φ : RootedForest) :
    LForestTensorAlgebra.constLabel (R := R) a (RootedForest.coproduct (R := R) φ) =
      coproduct (R := R) (LRootedForest.constLabel a φ) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change
    LForestTensorAlgebra.constLabel (R := R) a
        (PTree.coproductList (R := R) (ts.map Quotient.out)) =
      coproduct (R := R)
        (LRootedForest.constLabel a ((ts : List RootedTree) : RootedForest))
  rw [PLTree.constLabel_labelledCoproductList]
  change
    PLTree.labelledCoproductList (R := R)
        ((ts.map Quotient.out).map (PLTree.constLabel a)) =
      PLTree.labelledCoproductList (R := R)
        ((ts.map (LRootedTree.constLabel a)).map Quotient.out)
  exact PLTree.labelledCoproductList_forall₂_perm (R := R) (by
    induction ts with
    | nil =>
        exact List.Forall₂.nil
    | cons τ ts ih =>
        exact List.Forall₂.cons (LRootedTree.constLabel_out_perm a τ) ih)

end

end LRootedForest

namespace LForestTripleTensorAlgebra

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

private def coproductLeftMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    Multiplicative (LRootedForest α × LRootedForest α) →*
      LForestTripleTensorAlgebra α R where
  toFun term :=
    let term := Multiplicative.toAdd term
    includeLeftPair (R := R) (LRootedForest.coproduct (R := R) term.1) *
      ofForests (R := R) 0 0 term.2
  map_one' := by
    simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rcases Multiplicative.toAdd x with ⟨φ₁, ψ₁⟩
    rcases Multiplicative.toAdd y with ⟨φ₂, ψ₂⟩
    change
      includeLeftPair (R := R) (LRootedForest.coproduct (R := R) (φ₁ + φ₂)) *
          ofForests (R := R) 0 0 (ψ₁ + ψ₂) =
        includeLeftPair (R := R) (LRootedForest.coproduct (R := R) φ₁) *
            ofForests (R := R) 0 0 ψ₁ *
          (includeLeftPair (R := R) (LRootedForest.coproduct (R := R) φ₂) *
            ofForests (R := R) 0 0 ψ₂)
    rw [LRootedForest.coproduct_add, map_mul]
    have hψ :
        ofForests (R := R) 0 0 (ψ₁ + ψ₂) =
          ofForests (R := R) 0 0 ψ₁ * ofForests (R := R) 0 0 ψ₂ := by
      simpa using
        (ofForests_add (R := R) (0 : LRootedForest α) 0 0 0 ψ₁ ψ₂)
    rw [hψ]
    ac_rfl

/-- Apply the labelled coproduct to the first tensor factor, the map `Δ ⊗ id`. -/
def coproductLeft : LForestTensorAlgebra α R →ₐ[R] LForestTripleTensorAlgebra α R :=
  (AddMonoidAlgebra.lift R
      (LForestTripleTensorAlgebra α R) (LRootedForest α × LRootedForest α))
    (coproductLeftMonoidHom α R)

@[simp]
theorem coproductLeft_ofPair (term : LRootedForest α × LRootedForest α) :
    coproductLeft (R := R) (LForestTensorAlgebra.ofPair (R := R) term) =
      includeLeftPair (R := R) (LRootedForest.coproduct (R := R) term.1) *
        ofForests (R := R) 0 0 term.2 := by
  simp [coproductLeft, LForestTensorAlgebra.ofPair, coproductLeftMonoidHom]

@[simp]
theorem coproductLeft_ofForests (φ ψ : LRootedForest α) :
    coproductLeft (R := R) (LForestTensorAlgebra.ofForests (R := R) φ ψ) =
      includeLeftPair (R := R) (LRootedForest.coproduct (R := R) φ) *
        ofForests (R := R) 0 0 ψ := by
  simp [LForestTensorAlgebra.ofForests]

private def coproductRightMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    Multiplicative (LRootedForest α × LRootedForest α) →*
      LForestTripleTensorAlgebra α R where
  toFun term :=
    let term := Multiplicative.toAdd term
    ofForests (R := R) term.1 0 0 *
      includeRightPair (R := R) (LRootedForest.coproduct (R := R) term.2)
  map_one' := by
    simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rcases Multiplicative.toAdd x with ⟨φ₁, ψ₁⟩
    rcases Multiplicative.toAdd y with ⟨φ₂, ψ₂⟩
    change
      ofForests (R := R) (φ₁ + φ₂) 0 0 *
          includeRightPair (R := R) (LRootedForest.coproduct (R := R) (ψ₁ + ψ₂)) =
        ofForests (R := R) φ₁ 0 0 *
            includeRightPair (R := R) (LRootedForest.coproduct (R := R) ψ₁) *
          (ofForests (R := R) φ₂ 0 0 *
            includeRightPair (R := R) (LRootedForest.coproduct (R := R) ψ₂))
    rw [LRootedForest.coproduct_add, map_mul]
    have hφ :
        ofForests (R := R) (φ₁ + φ₂) 0 0 =
          ofForests (R := R) φ₁ 0 0 * ofForests (R := R) φ₂ 0 0 := by
      simpa using
        (ofForests_add (R := R) φ₁ φ₂ 0 0 (0 : LRootedForest α) 0)
    rw [hφ]
    ac_rfl

/-- Apply the labelled coproduct to the second tensor factor, the map `id ⊗ Δ`. -/
def coproductRight : LForestTensorAlgebra α R →ₐ[R] LForestTripleTensorAlgebra α R :=
  (AddMonoidAlgebra.lift R
      (LForestTripleTensorAlgebra α R) (LRootedForest α × LRootedForest α))
    (coproductRightMonoidHom α R)

@[simp]
theorem coproductRight_ofPair (term : LRootedForest α × LRootedForest α) :
    coproductRight (R := R) (LForestTensorAlgebra.ofPair (R := R) term) =
      ofForests (R := R) term.1 0 0 *
        includeRightPair (R := R) (LRootedForest.coproduct (R := R) term.2) := by
  simp [coproductRight, LForestTensorAlgebra.ofPair, coproductRightMonoidHom]

@[simp]
theorem coproductRight_ofForests (φ ψ : LRootedForest α) :
    coproductRight (R := R) (LForestTensorAlgebra.ofForests (R := R) φ ψ) =
      ofForests (R := R) φ 0 0 *
        includeRightPair (R := R) (LRootedForest.coproduct (R := R) ψ) := by
  simp [LForestTensorAlgebra.ofForests]

theorem includeLeftPair_sumTerms (terms : List (LRootedForest α × LRootedForest α)) :
    includeLeftPair (R := R) (LForestTensorAlgebra.sumTerms (R := R) terms) =
      sumTerms (R := R) (terms.map fun term => (term.1, term.2, 0)) := by
  induction terms with
  | nil =>
      simp [LForestTensorAlgebra.sumTerms, sumTerms]
  | cons term terms ih =>
      rw [LForestTensorAlgebra.sumTerms_cons, List.map_cons, sumTerms_cons, map_add,
        includeLeftPair_ofPair, ih]

theorem includeRightPair_sumTerms (terms : List (LRootedForest α × LRootedForest α)) :
    includeRightPair (R := R) (LForestTensorAlgebra.sumTerms (R := R) terms) =
      sumTerms (R := R) (terms.map fun term => (0, term.1, term.2)) := by
  induction terms with
  | nil =>
      simp [LForestTensorAlgebra.sumTerms, sumTerms]
  | cons term terms ih =>
      rw [LForestTensorAlgebra.sumTerms_cons, List.map_cons, sumTerms_cons, map_add,
        includeRightPair_ofPair, ih]

theorem sumTerms_liftLeft_mul_ofForests
    (terms : List (LRootedForest α × LRootedForest α)) (ψ : LRootedForest α) :
    sumTerms (R := R) (terms.map fun term => (term.1, term.2, 0)) *
        ofForests (R := R) 0 0 ψ =
      sumTerms (R := R) (terms.map fun term => (term.1, term.2, ψ)) := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      have hterm :
          ofTriple (R := R) (term.1, term.2, 0) * ofForests (R := R) 0 0 ψ =
            ofTriple (R := R) (term.1, term.2, ψ) := by
        change
          ofTriple (R := R) (term.1, term.2, 0) *
              ofTriple (R := R) (0, 0, ψ) =
            ofTriple (R := R) (term.1, term.2, ψ)
        rw [← ofTriple_add (R := R) (term.1, term.2, 0) (0, 0, ψ)]
        simp
      rw [List.map_cons, List.map_cons, sumTerms_cons, sumTerms_cons, add_mul,
        hterm, ih]

theorem ofForests_mul_sumTerms_liftRight
    (φ : LRootedForest α) (terms : List (LRootedForest α × LRootedForest α)) :
    ofForests (R := R) φ 0 0 *
        sumTerms (R := R) (terms.map fun term => (0, term.1, term.2)) =
      sumTerms (R := R) (terms.map fun term => (φ, term.1, term.2)) := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      have hterm :
          ofForests (R := R) φ 0 0 * ofTriple (R := R) (0, term.1, term.2) =
            ofTriple (R := R) (φ, term.1, term.2) := by
        rcases term with ⟨ψ, η⟩
        change
          ofTriple (R := R) (φ, 0, 0) *
              ofTriple (R := R) (0, ψ, η) =
            ofTriple (R := R) (φ, ψ, η)
        rw [← ofTriple_add (R := R) (φ, 0, 0) (0, ψ, η)]
        simp
      rw [List.map_cons, List.map_cons, sumTerms_cons, sumTerms_cons, mul_add,
        hterm, ih]

theorem multiplyTerms_append_left
    (xs ys zs : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    multiplyTerms (xs ++ ys) zs = multiplyTerms xs zs ++ multiplyTerms ys zs := by
  simp [multiplyTerms, List.flatMap_append]

theorem multiplyTerms_perm_left
    {xs ys zs : List (LRootedForest α × LRootedForest α × LRootedForest α)}
    (h : xs.Perm ys) :
    (multiplyTerms xs zs).Perm (multiplyTerms ys zs) := by
  rw [multiplyTerms, multiplyTerms]
  exact List.Perm.flatMap h (fun _ _ => List.Perm.refl _)

theorem multiplyTerms_perm_right
    {xs ys zs : List (LRootedForest α × LRootedForest α × LRootedForest α)}
    (h : ys.Perm zs) :
    (multiplyTerms xs ys).Perm (multiplyTerms xs zs) := by
  rw [multiplyTerms, multiplyTerms]
  exact List.Perm.flatMap (List.Perm.refl xs)
    (fun x _ => List.Perm.map (fun y => x + y) h)

theorem multiplyTerms_perm
    {xs xs' ys ys' : List (LRootedForest α × LRootedForest α × LRootedForest α)}
    (hxs : xs.Perm xs') (hys : ys.Perm ys') :
    (multiplyTerms xs ys).Perm (multiplyTerms xs' ys') :=
  (multiplyTerms_perm_left (zs := ys) hxs).trans
    (multiplyTerms_perm_right (xs := xs') hys)

private theorem flatMap_append_fun_perm {β γ : Type*} (xs : List β) (f g : β → List γ) :
    (xs.flatMap fun x => f x ++ g x).Perm (xs.flatMap f ++ xs.flatMap g) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have htail :
          ((f x ++ g x) ++ xs.flatMap (fun x => f x ++ g x)).Perm
            ((f x ++ g x) ++ (xs.flatMap f ++ xs.flatMap g)) :=
        List.Perm.append_left (f x ++ g x) ih
      have hswap :
          ((f x ++ g x) ++ (xs.flatMap f ++ xs.flatMap g)).Perm
            ((f x ++ xs.flatMap f) ++ (g x ++ xs.flatMap g)) := by
        simpa [List.append_assoc] using
          List.Perm.append_left (f x)
            (List.Perm.append
              (List.perm_append_comm : (g x ++ xs.flatMap f).Perm
                (xs.flatMap f ++ g x))
              (List.Perm.refl (xs.flatMap g)))
      exact htail.trans hswap

theorem flatMap_multiplyTerms_right_perm {β : Type*}
    (xs : List (LRootedForest α × LRootedForest α × LRootedForest α)) (ys : List β)
    (f : β → List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    (ys.flatMap fun y => multiplyTerms xs (f y)).Perm
      (multiplyTerms xs (ys.flatMap f)) := by
  induction xs with
  | nil =>
      simp [multiplyTerms]
  | cons x xs ih =>
      have hhead :
          (ys.flatMap fun y => (f y).map fun z => x + z) =
            (ys.flatMap f).map fun z => x + z := by
        simpa using
          (List.map_flatMap (f := fun z => x + z) (g := f) (l := ys)).symm
      rw [multiplyTerms]
      simp only [List.flatMap_cons]
      exact
        (flatMap_append_fun_perm ys (fun y => (f y).map fun z => x + z)
          (fun y => multiplyTerms xs (f y))).trans
          (List.Perm.append (by rw [hhead]) ih)

def coproductLeftTerm (term : LRootedForest α × LRootedForest α) :
    List (LRootedForest α × LRootedForest α × LRootedForest α) :=
  (LRootedForest.coproductTerms term.1).map fun left => (left.1, left.2, term.2)

def coproductRightTerm (term : LRootedForest α × LRootedForest α) :
    List (LRootedForest α × LRootedForest α × LRootedForest α) :=
  (LRootedForest.coproductTerms term.2).map fun right => (term.1, right.1, right.2)

def coproductLeftTerms (terms : List (LRootedForest α × LRootedForest α)) :
    List (LRootedForest α × LRootedForest α × LRootedForest α) :=
  terms.flatMap coproductLeftTerm

def coproductRightTerms (terms : List (LRootedForest α × LRootedForest α)) :
    List (LRootedForest α × LRootedForest α × LRootedForest α) :=
  terms.flatMap coproductRightTerm

theorem coproductLeftTerm_add_perm (x y : LRootedForest α × LRootedForest α) :
    (coproductLeftTerm (x + y)).Perm (multiplyTerms (coproductLeftTerm x)
      (coproductLeftTerm y)) := by
  rcases x with ⟨φ₁, ψ₁⟩
  rcases y with ⟨φ₂, ψ₂⟩
  have h := (LRootedForest.coproductTerms_add_perm φ₁ φ₂).map
    (fun term => (term.1, term.2, ψ₁ + ψ₂))
  simpa [coproductLeftTerm, multiplyTerms, PLTree.multiplyCoproductTerms,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def] using h

theorem coproductRightTerm_add_perm (x y : LRootedForest α × LRootedForest α) :
    (coproductRightTerm (x + y)).Perm (multiplyTerms (coproductRightTerm x)
      (coproductRightTerm y)) := by
  rcases x with ⟨φ₁, ψ₁⟩
  rcases y with ⟨φ₂, ψ₂⟩
  have h := (LRootedForest.coproductTerms_add_perm ψ₁ ψ₂).map
    (fun term => (φ₁ + φ₂, term.1, term.2))
  have hmap :
      (List.flatMap
          (fun a : LRootedForest α × LRootedForest α =>
            List.map (fun x => (φ₁ + φ₂, a.1 + x.1, a.2 + x.2))
              (LRootedForest.coproductTerms ψ₂)) (LRootedForest.coproductTerms ψ₁)) =
        (List.flatMap
          (fun a : LRootedForest α × LRootedForest α =>
            List.map (fun x => (φ₁ + φ₂, a + x))
              (LRootedForest.coproductTerms ψ₂)) (LRootedForest.coproductTerms ψ₁)) := by
    apply List.flatMap_congr
    intro a _ha
    apply List.map_congr_left
    intro x _hx
    cases a
    cases x
    rfl
  simpa [coproductRightTerm, multiplyTerms, PLTree.multiplyCoproductTerms,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def, hmap] using h

theorem coproductLeftTerm_singleton_graft_zero_perm (a : α) (φ : LRootedForest α) :
    (coproductLeftTerm (LRootedForest.singleton (LRootedForest.graft a φ), 0)).Perm
      (((LRootedForest.coproductTerms φ).map fun term =>
          (term.1, LRootedForest.singleton (LRootedForest.graft a term.2), 0)) ++
        [(LRootedForest.singleton (LRootedForest.graft a φ), 0, 0)]) := by
  have h :
      (coproductLeftTerm (LRootedForest.singleton (LRootedForest.graft a φ), 0)).Perm
        (((LRootedForest.coproductTerms φ).map fun term =>
            (term.1, (LRootedForest.singleton (LRootedForest.graft a term.2),
              (0 : LRootedForest α)))) ++
          [(LRootedForest.singleton (LRootedForest.graft a φ),
            ((0 : LRootedForest α), 0))]) := by
    simpa [coproductLeftTerm, Function.comp_def] using
      (LRootedForest.coproductTerms_singleton_graft_perm a φ).map
        (fun left => (left.1, left.2, (0 : LRootedForest α)))
  simpa using h

theorem coproductRightTerm_singleton_graft_perm
    (a : α) (φ ψ : LRootedForest α) :
    (coproductRightTerm (φ, LRootedForest.singleton (LRootedForest.graft a ψ))).Perm
      (((LRootedForest.coproductTerms ψ).map fun term =>
          (φ, term.1, LRootedForest.singleton (LRootedForest.graft a term.2))) ++
        [(φ, LRootedForest.singleton (LRootedForest.graft a ψ), 0)]) := by
  have h :
      (coproductRightTerm (φ, LRootedForest.singleton (LRootedForest.graft a ψ))).Perm
        (((LRootedForest.coproductTerms ψ).map fun term =>
            (φ, (term.1, LRootedForest.singleton (LRootedForest.graft a term.2)))) ++
          [(φ, (LRootedForest.singleton (LRootedForest.graft a ψ), 0))]) := by
    simpa [coproductRightTerm, Function.comp_def] using
      (LRootedForest.coproductTerms_singleton_graft_perm a ψ).map
        (fun right => (φ, right.1, right.2))
  simpa using h

private theorem append_singleton_middle_perm {α : Type _} (xs ys zs : List α) (x : α) :
    ((xs ++ [x]) ++ (ys ++ zs)).Perm ((xs ++ ys) ++ (x :: zs)) := by
  simpa [List.append_assoc] using
    List.Perm.append_right zs
      (List.Perm.append_left xs
        (show ([x] ++ ys).Perm (ys ++ [x]) from List.perm_append_comm))

theorem coproductLeftTerms_append
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    coproductLeftTerms (xs ++ ys) = coproductLeftTerms xs ++ coproductLeftTerms ys := by
  simp [coproductLeftTerms]

theorem coproductRightTerms_append
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    coproductRightTerms (xs ++ ys) = coproductRightTerms xs ++ coproductRightTerms ys := by
  simp [coproductRightTerms]

theorem coproductLeftTerms_map_singleton_graft
    (a : α) (terms : List (LRootedForest α × LRootedForest α)) :
    coproductLeftTerms (terms.map fun term =>
        (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))) =
      (coproductLeftTerms terms).map fun triple =>
        (triple.1, triple.2.1, LRootedForest.singleton (LRootedForest.graft a triple.2.2)) := by
  induction terms with
  | nil => simp [coproductLeftTerms]
  | cons term terms ih =>
      change
        coproductLeftTerm (term.1, LRootedForest.singleton (LRootedForest.graft a term.2)) ++
          coproductLeftTerms (terms.map fun term =>
            (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))) =
        (coproductLeftTerm term ++ coproductLeftTerms terms).map fun triple =>
          (triple.1, triple.2.1, LRootedForest.singleton (LRootedForest.graft a triple.2.2))
      rw [List.map_append, ih]
      cases term
      simp [coproductLeftTerm, List.map_map, Function.comp_def]

theorem coproductRightTerms_map_singleton_graft_perm
    (a : α) (terms : List (LRootedForest α × LRootedForest α)) :
    (coproductRightTerms (terms.map fun term =>
        (term.1, LRootedForest.singleton (LRootedForest.graft a term.2)))).Perm
      (((coproductRightTerms terms).map fun triple =>
        (triple.1, triple.2.1, LRootedForest.singleton (LRootedForest.graft a triple.2.2))) ++
        (terms.map fun term =>
          (term.1, LRootedForest.singleton (LRootedForest.graft a term.2), 0))) := by
  induction terms with
  | nil => simp [coproductRightTerms]
  | cons term terms ih =>
      let boundary := (term.1, LRootedForest.singleton (LRootedForest.graft a term.2),
        (0 : LRootedForest α))
      let headTerms :=
        (LRootedForest.coproductTerms term.2).map fun right =>
          (term.1, right.1, LRootedForest.singleton (LRootedForest.graft a right.2))
      let tailTerms :=
        (coproductRightTerms terms).map fun triple =>
          (triple.1, triple.2.1, LRootedForest.singleton (LRootedForest.graft a triple.2.2))
      let tailBoundary :=
        terms.map fun term =>
          (term.1, LRootedForest.singleton (LRootedForest.graft a term.2),
            (0 : LRootedForest α))
      have hhead :
          (coproductRightTerm
              (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))).Perm
            (headTerms ++ [boundary]) := by
        simpa [headTerms, boundary] using
          coproductRightTerm_singleton_graft_perm a term.1 term.2
      have htail :
          (coproductRightTerms (terms.map fun term =>
            (term.1, LRootedForest.singleton (LRootedForest.graft a term.2)))).Perm
            (tailTerms ++ tailBoundary) := by
        simpa [tailTerms, tailBoundary] using ih
      change
        ((coproductRightTerm
            (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))) ++
          coproductRightTerms (terms.map fun term =>
            (term.1, LRootedForest.singleton (LRootedForest.graft a term.2)))).Perm
        (((coproductRightTerm term ++ coproductRightTerms terms).map fun triple =>
            (triple.1, triple.2.1, LRootedForest.singleton (LRootedForest.graft a triple.2.2))) ++
          (boundary :: tailBoundary))
      rw [List.map_append]
      have hcombined := List.Perm.append hhead htail
      refine hcombined.trans ?_
      simpa [headTerms, tailTerms, tailBoundary, boundary, coproductRightTerm,
        List.map_map, Function.comp_def] using
        append_singleton_middle_perm headTerms tailTerms tailBoundary boundary

theorem coproductRightTerm_zero_perm (φ : LRootedForest α) :
    (coproductRightTerm (φ, 0)).Perm [(φ, 0, 0)] := by
  have hzero : (LRootedForest.coproductTerms (0 : LRootedForest α)).Perm [(0, 0)] := by
    have h := LRootedForest.coproductTerms_ofPLTree_list_perm ([] : List (PLTree α))
    exact h.trans (by simp [PLTree.coproductTermsList])
  simpa [coproductRightTerm] using hzero.map (fun right => (φ, right.1, right.2))

theorem coproductTerms_node_left_right_perm_of_coproductTermsList_perm
    (a : α) (ts : List (PLTree α))
    (h : (coproductLeftTerms (PLTree.coproductTermsList ts)).Perm
          (coproductRightTerms (PLTree.coproductTermsList ts))) :
    (coproductLeftTerms (PLTree.coproductTerms (.node a ts))).Perm
      (coproductRightTerms (PLTree.coproductTerms (.node a ts))) := by
  let terms := PLTree.coproductTermsList ts
  let forest : LRootedForest α := (ts.map LRootedTree.ofPLTree : List (LRootedTree α))
  let graftTerms : List (LRootedForest α × LRootedForest α) :=
    terms.map fun term => (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))
  let fullTerm : LRootedForest α × LRootedForest α :=
    (LRootedForest.singleton (LRootedTree.ofPLTree (.node a ts)), 0)
  let mapG := fun triple : LRootedForest α × LRootedForest α × LRootedForest α =>
    (triple.1, triple.2.1, LRootedForest.singleton (LRootedForest.graft a triple.2.2))
  let boundaryTerms := terms.map fun term =>
    (term.1, LRootedForest.singleton (LRootedForest.graft a term.2),
      (0 : LRootedForest α))
  let top := (LRootedForest.singleton (LRootedTree.ofPLTree (.node a ts)),
    (0 : LRootedForest α), (0 : LRootedForest α))
  have hforest_graft : LRootedForest.graft a forest = LRootedTree.ofPLTree (.node a ts) := by
    simpa [forest] using LRootedForest.graft_ofPLTree_list a ts
  have hforestTerms : (LRootedForest.coproductTerms forest).Perm terms := by
    simpa [forest, terms] using LRootedForest.coproductTerms_ofPLTree_list_perm ts
  have hcop : (PLTree.coproductTerms (.node a ts)).Perm (graftTerms ++ [fullTerm]) := by
    simpa [graftTerms, fullTerm, terms] using PLTree.coproductTerms_node_perm a ts
  have hleftStart :
      (coproductLeftTerms (PLTree.coproductTerms (.node a ts))).Perm
        (coproductLeftTerms (graftTerms ++ [fullTerm])) := by
    rw [coproductLeftTerms, coproductLeftTerms]
    exact List.Perm.flatMap hcop (fun _ _ => List.Perm.refl _)
  have hrightStart :
      (coproductRightTerms (PLTree.coproductTerms (.node a ts))).Perm
        (coproductRightTerms (graftTerms ++ [fullTerm])) := by
    rw [coproductRightTerms, coproductRightTerms]
    exact List.Perm.flatMap hcop (fun _ _ => List.Perm.refl _)
  have hmap : ((coproductLeftTerms terms).map mapG).Perm
      ((coproductRightTerms terms).map mapG) :=
    h.map mapG
  have hleftNormal :
      (coproductLeftTerms (graftTerms ++ [fullTerm])).Perm
        (((coproductLeftTerms terms).map mapG ++ boundaryTerms) ++ [top]) := by
    rw [coproductLeftTerms_append]
    rw [show coproductLeftTerms [fullTerm] = coproductLeftTerm fullTerm by
      simp [coproductLeftTerms]]
    have hfull : (coproductLeftTerm fullTerm).Perm (boundaryTerms ++ [top]) := by
      have hraw := coproductLeftTerm_singleton_graft_zero_perm a forest
      have hboundary :
          ((LRootedForest.coproductTerms forest).map fun term =>
            (term.1, LRootedForest.singleton (LRootedForest.graft a term.2),
              (0 : LRootedForest α))).Perm
          boundaryTerms := by
        simpa [boundaryTerms, terms] using hforestTerms.map
          (fun term => (term.1, LRootedForest.singleton (LRootedForest.graft a term.2),
            (0 : LRootedForest α)))
      simpa [fullTerm, top, hforest_graft] using hraw.trans (hboundary.append_right _)
    have hgraft : coproductLeftTerms graftTerms = (coproductLeftTerms terms).map mapG := by
      simpa [graftTerms, mapG, terms] using coproductLeftTerms_map_singleton_graft a terms
    rw [hgraft]
    simpa [List.append_assoc] using
      List.Perm.append (List.Perm.refl ((coproductLeftTerms terms).map mapG)) hfull
  have hrightNormal :
      (coproductRightTerms (graftTerms ++ [fullTerm])).Perm
        (((coproductRightTerms terms).map mapG ++ boundaryTerms) ++ [top]) := by
    rw [coproductRightTerms_append]
    rw [show coproductRightTerms [fullTerm] = coproductRightTerm fullTerm by
      simp [coproductRightTerms]]
    have hgraft :
        (coproductRightTerms graftTerms).Perm
          ((coproductRightTerms terms).map mapG ++ boundaryTerms) := by
      simpa [graftTerms, mapG, boundaryTerms, terms] using
        coproductRightTerms_map_singleton_graft_perm a terms
    have hfull : (coproductRightTerm fullTerm).Perm [top] := by
      simpa [fullTerm, top] using
        coproductRightTerm_zero_perm (LRootedForest.singleton (LRootedTree.ofPLTree (.node a ts)))
    simpa [List.append_assoc] using List.Perm.append hgraft hfull
  have hnormal :
      (((coproductLeftTerms terms).map mapG ++ boundaryTerms) ++ [top]).Perm
        (((coproductRightTerms terms).map mapG ++ boundaryTerms) ++ [top]) :=
    List.Perm.append_right [top]
      (List.Perm.append hmap (List.Perm.refl boundaryTerms))
  exact hleftStart.trans
    (hleftNormal.trans (hnormal.trans (hrightNormal.symm.trans hrightStart.symm)))

theorem coproductLeftTerms_multiplyCoproductTerms_perm
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    (coproductLeftTerms (PLTree.multiplyCoproductTerms xs ys)).Perm
      (multiplyTerms (coproductLeftTerms xs) (coproductLeftTerms ys)) := by
  induction xs with
  | nil =>
      simp [PLTree.multiplyCoproductTerms, coproductLeftTerms, multiplyTerms]
  | cons x xs ih =>
      have hhead :
          (ys.flatMap fun y =>
              coproductLeftTerm (x.1 + y.1, x.2 + y.2)).Perm
            (multiplyTerms (coproductLeftTerm x) (coproductLeftTerms ys)) := by
        have hterm :
            (ys.flatMap fun y =>
                coproductLeftTerm (x.1 + y.1, x.2 + y.2)).Perm
              (ys.flatMap fun y => multiplyTerms (coproductLeftTerm x)
                (coproductLeftTerm y)) := by
          apply List.Perm.flatMap (List.Perm.refl ys)
          intro y _hy
          have hxy : (x.1 + y.1, x.2 + y.2) = x + y := by
            cases x
            cases y
            rfl
          rw [hxy]
          exact coproductLeftTerm_add_perm x y
        exact hterm.trans
          (flatMap_multiplyTerms_right_perm (coproductLeftTerm x) ys
            coproductLeftTerm)
      have ih' :
          (List.flatMap coproductLeftTerm
              (List.flatMap (fun x => List.map
                (fun y => (x.1 + y.1, x.2 + y.2)) ys) xs)).Perm
            (multiplyTerms (coproductLeftTerms xs) (coproductLeftTerms ys)) := by
        simpa [coproductLeftTerms, PLTree.multiplyCoproductTerms] using ih
      rw [PLTree.multiplyCoproductTerms, coproductLeftTerms]
      simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_map]
      rw [show coproductLeftTerms (x :: xs) =
        coproductLeftTerm x ++ coproductLeftTerms xs by rfl]
      rw [multiplyTerms_append_left]
      exact List.Perm.append hhead ih'

theorem coproductRightTerms_multiplyCoproductTerms_perm
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    (coproductRightTerms (PLTree.multiplyCoproductTerms xs ys)).Perm
      (multiplyTerms (coproductRightTerms xs) (coproductRightTerms ys)) := by
  induction xs with
  | nil =>
      simp [PLTree.multiplyCoproductTerms, coproductRightTerms, multiplyTerms]
  | cons x xs ih =>
      have hhead :
          (ys.flatMap fun y =>
              coproductRightTerm (x.1 + y.1, x.2 + y.2)).Perm
            (multiplyTerms (coproductRightTerm x) (coproductRightTerms ys)) := by
        have hterm :
            (ys.flatMap fun y =>
                coproductRightTerm (x.1 + y.1, x.2 + y.2)).Perm
              (ys.flatMap fun y => multiplyTerms (coproductRightTerm x)
                (coproductRightTerm y)) := by
          apply List.Perm.flatMap (List.Perm.refl ys)
          intro y _hy
          have hxy : (x.1 + y.1, x.2 + y.2) = x + y := by
            cases x
            cases y
            rfl
          rw [hxy]
          exact coproductRightTerm_add_perm x y
        exact hterm.trans
          (flatMap_multiplyTerms_right_perm (coproductRightTerm x) ys
            coproductRightTerm)
      have ih' :
          (List.flatMap coproductRightTerm
              (List.flatMap (fun x => List.map
                (fun y => (x.1 + y.1, x.2 + y.2)) ys) xs)).Perm
            (multiplyTerms (coproductRightTerms xs) (coproductRightTerms ys)) := by
        simpa [coproductRightTerms, PLTree.multiplyCoproductTerms] using ih
      rw [PLTree.multiplyCoproductTerms, coproductRightTerms]
      simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_map]
      rw [show coproductRightTerms (x :: xs) =
        coproductRightTerm x ++ coproductRightTerms xs by rfl]
      rw [multiplyTerms_append_left]
      exact List.Perm.append hhead ih'

theorem coproductLeftTerms_perm
    {xs ys : List (LRootedForest α × LRootedForest α)} (h : xs.Perm ys) :
    (coproductLeftTerms xs).Perm (coproductLeftTerms ys) := by
  rw [coproductLeftTerms, coproductLeftTerms]
  exact List.Perm.flatMap h (fun _ _ => List.Perm.refl _)

theorem coproductRightTerms_perm
    {xs ys : List (LRootedForest α × LRootedForest α)} (h : xs.Perm ys) :
    (coproductRightTerms xs).Perm (coproductRightTerms ys) := by
  rw [coproductRightTerms, coproductRightTerms]
  exact List.Perm.flatMap h (fun _ _ => List.Perm.refl _)

theorem coproductLeftTerms_lrootedForest_add_perm (φ ψ : LRootedForest α) :
    (coproductLeftTerms (LRootedForest.coproductTerms (φ + ψ))).Perm
      (multiplyTerms (coproductLeftTerms (LRootedForest.coproductTerms φ))
        (coproductLeftTerms (LRootedForest.coproductTerms ψ))) :=
  (coproductLeftTerms_perm (LRootedForest.coproductTerms_add_perm φ ψ)).trans
    (coproductLeftTerms_multiplyCoproductTerms_perm _ _)

theorem coproductRightTerms_lrootedForest_add_perm (φ ψ : LRootedForest α) :
    (coproductRightTerms (LRootedForest.coproductTerms (φ + ψ))).Perm
      (multiplyTerms (coproductRightTerms (LRootedForest.coproductTerms φ))
        (coproductRightTerms (LRootedForest.coproductTerms ψ))) :=
  (coproductRightTerms_perm (LRootedForest.coproductTerms_add_perm φ ψ)).trans
    (coproductRightTerms_multiplyCoproductTerms_perm _ _)

theorem coproductTermsList_left_right_perm_of_coproductTerms_perm
    (h : ∀ t : PLTree α,
      (coproductLeftTerms (PLTree.coproductTerms t)).Perm
        (coproductRightTerms (PLTree.coproductTerms t))) :
    ∀ ts : List (PLTree α),
      (coproductLeftTerms (PLTree.coproductTermsList ts)).Perm
        (coproductRightTerms (PLTree.coproductTermsList ts)) := by
  intro ts
  induction ts with
  | nil =>
      have hzero : (LRootedForest.coproductTerms (0 : LRootedForest α)).Perm [(0, 0)] := by
        simpa [PLTree.coproductTermsList] using
          (LRootedForest.coproductTerms_ofPLTree_list_perm ([] : List (PLTree α)))
      have hleft :
          (coproductLeftTerm ((0 : LRootedForest α), (0 : LRootedForest α))).Perm
            [((0 : LRootedForest α), (0 : LRootedForest α), (0 : LRootedForest α))] := by
        simpa [coproductLeftTerm] using
          hzero.map (fun left => (left.1, left.2, (0 : LRootedForest α)))
      have hright :
          (coproductRightTerm ((0 : LRootedForest α), (0 : LRootedForest α))).Perm
            [((0 : LRootedForest α), (0 : LRootedForest α), (0 : LRootedForest α))] := by
        simpa [coproductRightTerm] using
          hzero.map (fun right => ((0 : LRootedForest α), right.1, right.2))
      simpa [PLTree.coproductTermsList, coproductLeftTerms, coproductRightTerms] using
        hleft.trans hright.symm
  | cons t ts ih =>
      rw [PLTree.coproductTermsList]
      exact (coproductLeftTerms_multiplyCoproductTerms_perm
          (PLTree.coproductTerms t) (PLTree.coproductTermsList ts)).trans
        ((multiplyTerms_perm (h t) ih).trans
          (coproductRightTerms_multiplyCoproductTerms_perm
            (PLTree.coproductTerms t) (PLTree.coproductTermsList ts)).symm)

mutual

theorem coproductTerms_left_right_perm :
    ∀ t : PLTree α,
      (coproductLeftTerms (PLTree.coproductTerms t)).Perm
        (coproductRightTerms (PLTree.coproductTerms t))
  | .node a ts =>
      coproductTerms_node_left_right_perm_of_coproductTermsList_perm a ts
        (coproductTermsList_left_right_perm ts)

theorem coproductTermsList_left_right_perm :
    ∀ ts : List (PLTree α),
      (coproductLeftTerms (PLTree.coproductTermsList ts)).Perm
        (coproductRightTerms (PLTree.coproductTermsList ts))
  | [] => by
      have hzero : (LRootedForest.coproductTerms (0 : LRootedForest α)).Perm [(0, 0)] := by
        have h := LRootedForest.coproductTerms_ofPLTree_list_perm ([] : List (PLTree α))
        exact h.trans (by simp [PLTree.coproductTermsList])
      have hleft :
          (coproductLeftTerm ((0 : LRootedForest α), (0 : LRootedForest α))).Perm
            [((0 : LRootedForest α), (0 : LRootedForest α), (0 : LRootedForest α))] := by
        simpa [coproductLeftTerm] using
          hzero.map (fun left => (left.1, left.2, (0 : LRootedForest α)))
      have hright :
          (coproductRightTerm ((0 : LRootedForest α), (0 : LRootedForest α))).Perm
            [((0 : LRootedForest α), (0 : LRootedForest α), (0 : LRootedForest α))] := by
        simpa [coproductRightTerm] using
          hzero.map (fun right => ((0 : LRootedForest α), right.1, right.2))
      simpa [PLTree.coproductTermsList, coproductLeftTerms, coproductRightTerms] using
        hleft.trans hright.symm
  | t :: ts => by
      rw [PLTree.coproductTermsList]
      exact (coproductLeftTerms_multiplyCoproductTerms_perm
          (PLTree.coproductTerms t) (PLTree.coproductTermsList ts)).trans
        ((multiplyTerms_perm (coproductTerms_left_right_perm t)
            (coproductTermsList_left_right_perm ts)).trans
          (coproductRightTerms_multiplyCoproductTerms_perm
            (PLTree.coproductTerms t) (PLTree.coproductTermsList ts)).symm)

end

theorem coproductTerms_lrootedForest_left_right_perm_of_coproductTerms_perm
    (h : ∀ t : PLTree α,
      (coproductLeftTerms (PLTree.coproductTerms t)).Perm
        (coproductRightTerms (PLTree.coproductTerms t)))
    (φ : LRootedForest α) :
    (coproductLeftTerms (LRootedForest.coproductTerms φ)).Perm
      (coproductRightTerms (LRootedForest.coproductTerms φ)) := by
  rw [LRootedForest.coproductTerms]
  exact coproductTermsList_left_right_perm_of_coproductTerms_perm h
    ((Quotient.out φ).map Quotient.out)

theorem coproductLeftTerm_order
    {term : LRootedForest α × LRootedForest α}
    {triple : LRootedForest α × LRootedForest α × LRootedForest α}
    (htriple : triple ∈ coproductLeftTerm term) :
    LRootedForest.order triple.1 + LRootedForest.order triple.2.1 +
        LRootedForest.order triple.2.2 =
      LRootedForest.order term.1 + LRootedForest.order term.2 := by
  simp [coproductLeftTerm] at htriple
  obtain ⟨left₁, left₂, hleft, htriple⟩ := htriple
  subst triple
  have hleft_order := LRootedForest.coproductTerms_order hleft
  change
    LRootedForest.order left₁ + LRootedForest.order left₂ =
      LRootedForest.order term.1 at hleft_order
  change
    LRootedForest.order left₁ + LRootedForest.order left₂ +
        LRootedForest.order term.2 =
      LRootedForest.order term.1 + LRootedForest.order term.2
  omega

theorem coproductRightTerm_order
    {term : LRootedForest α × LRootedForest α}
    {triple : LRootedForest α × LRootedForest α × LRootedForest α}
    (htriple : triple ∈ coproductRightTerm term) :
    LRootedForest.order triple.1 + LRootedForest.order triple.2.1 +
        LRootedForest.order triple.2.2 =
      LRootedForest.order term.1 + LRootedForest.order term.2 := by
  simp [coproductRightTerm] at htriple
  obtain ⟨right₁, right₂, hright, htriple⟩ := htriple
  subst triple
  have hright_order := LRootedForest.coproductTerms_order hright
  change
    LRootedForest.order right₁ + LRootedForest.order right₂ =
      LRootedForest.order term.2 at hright_order
  change
    LRootedForest.order term.1 + LRootedForest.order right₁ +
        LRootedForest.order right₂ =
      LRootedForest.order term.1 + LRootedForest.order term.2
  omega

theorem coproductLeftTerms_order
    {terms : List (LRootedForest α × LRootedForest α)} {m : Nat}
    (hterms :
      ∀ term ∈ terms, LRootedForest.order term.1 + LRootedForest.order term.2 = m)
    {triple : LRootedForest α × LRootedForest α × LRootedForest α}
    (htriple : triple ∈ coproductLeftTerms terms) :
    LRootedForest.order triple.1 + LRootedForest.order triple.2.1 +
        LRootedForest.order triple.2.2 = m := by
  simp [coproductLeftTerms] at htriple
  obtain ⟨φ, ψ, hterm, htriple⟩ := htriple
  rw [← hterms (φ, ψ) hterm]
  exact coproductLeftTerm_order htriple

theorem coproductRightTerms_order
    {terms : List (LRootedForest α × LRootedForest α)} {m : Nat}
    (hterms :
      ∀ term ∈ terms, LRootedForest.order term.1 + LRootedForest.order term.2 = m)
    {triple : LRootedForest α × LRootedForest α × LRootedForest α}
    (htriple : triple ∈ coproductRightTerms terms) :
    LRootedForest.order triple.1 + LRootedForest.order triple.2.1 +
        LRootedForest.order triple.2.2 = m := by
  simp [coproductRightTerms] at htriple
  obtain ⟨φ, ψ, hterm, htriple⟩ := htriple
  rw [← hterms (φ, ψ) hterm]
  exact coproductRightTerm_order htriple

theorem coproductLeftTerms_rootedForest_order
    {φ : LRootedForest α}
    {triple : LRootedForest α × LRootedForest α × LRootedForest α}
    (htriple : triple ∈ coproductLeftTerms (LRootedForest.coproductTerms φ)) :
    LRootedForest.order triple.1 + LRootedForest.order triple.2.1 +
        LRootedForest.order triple.2.2 = LRootedForest.order φ :=
  coproductLeftTerms_order (fun _ hterm => LRootedForest.coproductTerms_order hterm)
    htriple

theorem coproductRightTerms_rootedForest_order
    {φ : LRootedForest α}
    {triple : LRootedForest α × LRootedForest α × LRootedForest α}
    (htriple : triple ∈ coproductRightTerms (LRootedForest.coproductTerms φ)) :
    LRootedForest.order triple.1 + LRootedForest.order triple.2.1 +
        LRootedForest.order triple.2.2 = LRootedForest.order φ :=
  coproductRightTerms_order (fun _ hterm => LRootedForest.coproductTerms_order hterm)
    htriple

theorem coproductLeftTerms_pltree_order
    {t : PLTree α} {triple : LRootedForest α × LRootedForest α × LRootedForest α}
    (htriple : triple ∈ coproductLeftTerms (PLTree.coproductTerms t)) :
    LRootedForest.order triple.1 + LRootedForest.order triple.2.1 +
        LRootedForest.order triple.2.2 = PLTree.order t :=
  coproductLeftTerms_order (fun _ hterm => PLTree.coproductTerms_order hterm)
    htriple

theorem coproductRightTerms_pltree_order
    {t : PLTree α} {triple : LRootedForest α × LRootedForest α × LRootedForest α}
    (htriple : triple ∈ coproductRightTerms (PLTree.coproductTerms t)) :
    LRootedForest.order triple.1 + LRootedForest.order triple.2.1 +
        LRootedForest.order triple.2.2 = PLTree.order t :=
  coproductRightTerms_order (fun _ hterm => PLTree.coproductTerms_order hterm)
    htriple

theorem sumTerms_coproductLeftTerm (term : LRootedForest α × LRootedForest α) :
    sumTerms (R := R) (coproductLeftTerm term) =
      coproductLeft (R := R) (LForestTensorAlgebra.ofPair (R := R) term) := by
  rw [coproductLeftTerm, coproductLeft_ofPair,
    LRootedForest.coproduct_eq_sumTerms_coproductTerms, includeLeftPair_sumTerms,
    sumTerms_liftLeft_mul_ofForests]

theorem sumTerms_coproductRightTerm (term : LRootedForest α × LRootedForest α) :
    sumTerms (R := R) (coproductRightTerm term) =
      coproductRight (R := R) (LForestTensorAlgebra.ofPair (R := R) term) := by
  rw [coproductRightTerm, coproductRight_ofPair,
    LRootedForest.coproduct_eq_sumTerms_coproductTerms, includeRightPair_sumTerms,
    ofForests_mul_sumTerms_liftRight]

theorem sumTerms_coproductLeftTerms
    (terms : List (LRootedForest α × LRootedForest α)) :
    sumTerms (R := R) (coproductLeftTerms terms) =
      coproductLeft (R := R) (LForestTensorAlgebra.sumTerms (R := R) terms) := by
  induction terms with
  | nil =>
      simp [coproductLeftTerms, LForestTensorAlgebra.sumTerms]
  | cons term terms ih =>
      have ih' :
          sumTerms (R := R) (List.flatMap coproductLeftTerm terms) =
            coproductLeft (R := R) (LForestTensorAlgebra.sumTerms (R := R) terms) := by
        simpa [coproductLeftTerms] using ih
      rw [coproductLeftTerms, List.flatMap_cons, sumTerms_append,
        sumTerms_coproductLeftTerm, ih', LForestTensorAlgebra.sumTerms_cons, map_add]

theorem sumTerms_coproductRightTerms
    (terms : List (LRootedForest α × LRootedForest α)) :
    sumTerms (R := R) (coproductRightTerms terms) =
      coproductRight (R := R) (LForestTensorAlgebra.sumTerms (R := R) terms) := by
  induction terms with
  | nil =>
      simp [coproductRightTerms, LForestTensorAlgebra.sumTerms]
  | cons term terms ih =>
      have ih' :
          sumTerms (R := R) (List.flatMap coproductRightTerm terms) =
            coproductRight (R := R) (LForestTensorAlgebra.sumTerms (R := R) terms) := by
        simpa [coproductRightTerms] using ih
      rw [coproductRightTerms, List.flatMap_cons, sumTerms_append,
        sumTerms_coproductRightTerm, ih', LForestTensorAlgebra.sumTerms_cons, map_add]

theorem coproductLeft_coproduct_eq_sumTerms (φ : LRootedForest α) :
    coproductLeft (R := R) (LRootedForest.coproduct (R := R) φ) =
      sumTerms (R := R) (coproductLeftTerms (LRootedForest.coproductTerms φ)) := by
  rw [LRootedForest.coproduct_eq_sumTerms_coproductTerms]
  exact (sumTerms_coproductLeftTerms (R := R) (LRootedForest.coproductTerms φ)).symm

theorem coproductRight_coproduct_eq_sumTerms (φ : LRootedForest α) :
    coproductRight (R := R) (LRootedForest.coproduct (R := R) φ) =
      sumTerms (R := R) (coproductRightTerms (LRootedForest.coproductTerms φ)) := by
  rw [LRootedForest.coproduct_eq_sumTerms_coproductTerms]
  exact (sumTerms_coproductRightTerms (R := R) (LRootedForest.coproductTerms φ)).symm

theorem coproductLeft_pltree_coproduct_eq_sumTerms (t : PLTree α) :
    coproductLeft (R := R) (PLTree.labelledCoproduct (R := R) t) =
      sumTerms (R := R) (coproductLeftTerms (PLTree.coproductTerms t)) := by
  rw [PLTree.labelledCoproduct]
  exact (sumTerms_coproductLeftTerms (R := R) (PLTree.coproductTerms t)).symm

theorem coproductRight_pltree_coproduct_eq_sumTerms (t : PLTree α) :
    coproductRight (R := R) (PLTree.labelledCoproduct (R := R) t) =
      sumTerms (R := R) (coproductRightTerms (PLTree.coproductTerms t)) := by
  rw [PLTree.labelledCoproduct]
  exact (sumTerms_coproductRightTerms (R := R) (PLTree.coproductTerms t)).symm

theorem nestedCoproductLeftCut_perm_coproductLeftTerm (c : PLTree.Cut α) :
    ((PLTree.coproductTermsList c.pruned).map
        fun left => (left.1, left.2, c.trunkForest)).Perm
      (coproductLeftTerm (c.prunedForest, c.trunkForest)) := by
  simpa [coproductLeftTerm, PLTree.Cut.prunedForest] using
    ((LRootedForest.coproductTerms_ofPLTree_list_perm c.pruned).symm.map
      (fun left => (left.1, left.2, c.trunkForest)))

theorem nestedCoproductRightCut_perm_coproductRightTerm (c : PLTree.Cut α) :
    (c.trunkCoproductTerms.map
        fun right => (c.prunedForest, right.1, right.2)).Perm
      (coproductRightTerm (c.prunedForest, c.trunkForest)) := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? with
      | none =>
          change
            (List.map
                (fun right =>
                  (((pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) :
                    LRootedForest α), right.1, right.2))
                (PLTree.coproductTermsList ([] : List (PLTree α)))).Perm
              (List.map
                (fun right =>
                  (((pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) :
                    LRootedForest α), right.1, right.2))
                (LRootedForest.coproductTerms (0 : LRootedForest α)))
          exact
            ((LRootedForest.coproductTerms_ofPLTree_list_perm ([] : List (PLTree α))).symm.map
              (fun right =>
                (((pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) :
                  LRootedForest α), right.1, right.2)))
      | some trunk =>
          change
            (List.map
                (fun right =>
                  (((pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) :
                    LRootedForest α), right.1, right.2))
                (PLTree.coproductTerms trunk)).Perm
              (List.map
                (fun right =>
                  (((pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) :
                    LRootedForest α), right.1, right.2))
                (LRootedForest.coproductTerms
                  (LRootedForest.singleton (LRootedTree.ofPLTree trunk))))
          exact
            ((LRootedForest.coproductTerms_singleton_ofPLTree_perm trunk).symm.map
              (fun right =>
                (((pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) :
                  LRootedForest α), right.1, right.2)))

theorem nestedCoproductLeftCuts_perm_coproductLeftTerms :
    ∀ cuts : List (PLTree.Cut α),
      (cuts.flatMap fun c =>
        (PLTree.coproductTermsList c.pruned).map
          fun left => (left.1, left.2, c.trunkForest)).Perm
        (coproductLeftTerms
          (cuts.map fun c => (c.prunedForest, c.trunkForest)))
  | [] => by
      simp [coproductLeftTerms]
  | c :: cuts => by
      simpa [coproductLeftTerms] using
        (nestedCoproductLeftCut_perm_coproductLeftTerm c).append
          (nestedCoproductLeftCuts_perm_coproductLeftTerms cuts)

theorem nestedCoproductRightCuts_perm_coproductRightTerms :
    ∀ cuts : List (PLTree.Cut α),
      (cuts.flatMap fun c =>
        c.trunkCoproductTerms.map
          fun right => (c.prunedForest, right.1, right.2)).Perm
        (coproductRightTerms
          (cuts.map fun c => (c.prunedForest, c.trunkForest)))
  | [] => by
      simp [coproductRightTerms]
  | c :: cuts => by
      simpa [coproductRightTerms] using
        (nestedCoproductRightCut_perm_coproductRightTerm c).append
          (nestedCoproductRightCuts_perm_coproductRightTerms cuts)

theorem nestedCoproductLeftTerms_perm_coproductLeftTerms (t : PLTree α) :
    (PLTree.nestedCoproductLeftTerms t).Perm
      (coproductLeftTerms (PLTree.coproductTerms t)) := by
  simpa [PLTree.nestedCoproductLeftTerms, PLTree.coproductTerms] using
    nestedCoproductLeftCuts_perm_coproductLeftTerms (PLTree.cuts t)

theorem nestedCoproductRightTerms_perm_coproductRightTerms (t : PLTree α) :
    (PLTree.nestedCoproductRightTerms t).Perm
      (coproductRightTerms (PLTree.coproductTerms t)) := by
  simpa [PLTree.nestedCoproductRightTerms, PLTree.coproductTerms] using
    nestedCoproductRightCuts_perm_coproductRightTerms (PLTree.cuts t)

theorem nestedCoproductTerms_perm_iff_coproductTerms_perm (t : PLTree α) :
    (PLTree.nestedCoproductLeftTerms t).Perm (PLTree.nestedCoproductRightTerms t) ↔
      (coproductLeftTerms (PLTree.coproductTerms t)).Perm
        (coproductRightTerms (PLTree.coproductTerms t)) := by
  constructor
  · intro h
    exact (nestedCoproductLeftTerms_perm_coproductLeftTerms t).symm.trans
      (h.trans (nestedCoproductRightTerms_perm_coproductRightTerms t))
  · intro h
    exact (nestedCoproductLeftTerms_perm_coproductLeftTerms t).trans
      (h.trans (nestedCoproductRightTerms_perm_coproductRightTerms t).symm)

theorem nestedCoproductTerms_left_right_perm (t : PLTree α) :
    (PLTree.nestedCoproductLeftTerms t).Perm (PLTree.nestedCoproductRightTerms t) :=
  (nestedCoproductTerms_perm_iff_coproductTerms_perm t).2
    (coproductTerms_left_right_perm t)

theorem coproductTerms_lrootedForest_left_right_perm_of_nestedCoproductTerms_perm
    (h : ∀ t : PLTree α,
      (PLTree.nestedCoproductLeftTerms t).Perm (PLTree.nestedCoproductRightTerms t))
    (φ : LRootedForest α) :
    (coproductLeftTerms (LRootedForest.coproductTerms φ)).Perm
      (coproductRightTerms (LRootedForest.coproductTerms φ)) :=
  coproductTerms_lrootedForest_left_right_perm_of_coproductTerms_perm
    (fun t => (nestedCoproductTerms_perm_iff_coproductTerms_perm t).1 (h t)) φ

theorem sumTerms_nestedCoproductLeftCut (c : PLTree.Cut α) :
    sumTerms (R := R)
        ((PLTree.coproductTermsList c.pruned).map
          fun left => (left.1, left.2, c.trunkForest)) =
      coproductLeft (R := R)
        (LForestTensorAlgebra.ofPair (R := R) (c.prunedForest, c.trunkForest)) := by
  rw [coproductLeft_ofPair]
  have hcop :
      LRootedForest.coproduct (R := R) c.prunedForest =
        PLTree.labelledCoproductList (R := R) c.pruned := by
    simpa [PLTree.Cut.prunedForest] using
      LRootedForest.coproduct_ofPLTree_list (R := R) c.pruned
  rw [hcop, PLTree.labelledCoproductList, includeLeftPair_sumTerms,
    sumTerms_liftLeft_mul_ofForests]

theorem sumTerms_trunkCoproductTerms (c : PLTree.Cut α) :
    LRootedForest.coproduct (R := R) c.trunkForest =
      LForestTensorAlgebra.sumTerms (R := R) c.trunkCoproductTerms := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? with
      | none =>
          simp [PLTree.Cut.trunkForest, PLTree.Cut.trunkCoproductTerms,
            LForestTensorAlgebra.sumTerms]
          change 1 = LForestTensorAlgebra.ofPair (R := R)
            (0 : LRootedForest α × LRootedForest α)
          rw [LForestTensorAlgebra.ofPair_zero]
      | some trunk =>
          rw [PLTree.Cut.trunkForest, PLTree.Cut.trunkCoproductTerms,
            LRootedForest.coproduct_singleton_ofPLTree, PLTree.labelledCoproduct]

theorem sumTerms_nestedCoproductRightCut (c : PLTree.Cut α) :
    sumTerms (R := R)
        (c.trunkCoproductTerms.map
          fun right => (c.prunedForest, right.1, right.2)) =
      coproductRight (R := R)
        (LForestTensorAlgebra.ofPair (R := R) (c.prunedForest, c.trunkForest)) := by
  rw [coproductRight_ofPair, sumTerms_trunkCoproductTerms,
    includeRightPair_sumTerms, ofForests_mul_sumTerms_liftRight]

theorem sumTerms_nestedCoproductLeftCut_perm {c d : PLTree.Cut α}
    (h : PLTree.Cut.Perm c d) :
    sumTerms (R := R)
        ((PLTree.coproductTermsList c.pruned).map
          fun left => (left.1, left.2, c.trunkForest)) =
      sumTerms (R := R)
        ((PLTree.coproductTermsList d.pruned).map
          fun left => (left.1, left.2, d.trunkForest)) := by
  rw [sumTerms_nestedCoproductLeftCut, sumTerms_nestedCoproductLeftCut,
    PLTree.Cut.Perm.coproductTerm_eq h]

theorem sumTerms_nestedCoproductRightCut_perm {c d : PLTree.Cut α}
    (h : PLTree.Cut.Perm c d) :
    sumTerms (R := R)
        (c.trunkCoproductTerms.map
          fun right => (c.prunedForest, right.1, right.2)) =
      sumTerms (R := R)
        (d.trunkCoproductTerms.map
          fun right => (d.prunedForest, right.1, right.2)) := by
  rw [sumTerms_nestedCoproductRightCut, sumTerms_nestedCoproductRightCut,
    PLTree.Cut.Perm.coproductTerm_eq h]

theorem sumTerms_nestedCoproductLeftCuts :
    ∀ cuts : List (PLTree.Cut α),
      sumTerms (R := R)
          (cuts.flatMap fun c =>
            (PLTree.coproductTermsList c.pruned).map
              fun left => (left.1, left.2, c.trunkForest)) =
        coproductLeft (R := R)
          (LForestTensorAlgebra.sumTerms (R := R)
            (cuts.map fun c => (c.prunedForest, c.trunkForest)))
  | [] => by
      simp [LForestTensorAlgebra.sumTerms]
  | c :: cuts => by
      rw [List.flatMap_cons, sumTerms_append, List.map_cons,
        LForestTensorAlgebra.sumTerms_cons, map_add, sumTerms_nestedCoproductLeftCut,
        sumTerms_nestedCoproductLeftCuts cuts]

theorem sumTerms_nestedCoproductRightCuts :
    ∀ cuts : List (PLTree.Cut α),
      sumTerms (R := R)
          (cuts.flatMap fun c =>
            c.trunkCoproductTerms.map
              fun right => (c.prunedForest, right.1, right.2)) =
        coproductRight (R := R)
          (LForestTensorAlgebra.sumTerms (R := R)
            (cuts.map fun c => (c.prunedForest, c.trunkForest)))
  | [] => by
      simp [LForestTensorAlgebra.sumTerms]
  | c :: cuts => by
      rw [List.flatMap_cons, sumTerms_append, List.map_cons,
        LForestTensorAlgebra.sumTerms_cons, map_add, sumTerms_nestedCoproductRightCut,
        sumTerms_nestedCoproductRightCuts cuts]

theorem sumTerms_nestedCoproductLeftCuts_listRelPerm
    {cs ds : List (PLTree.Cut α)}
    (h : PTree.ListRelPerm PLTree.Cut.Perm cs ds) :
    sumTerms (R := R)
        (cs.flatMap fun c =>
          (PLTree.coproductTermsList c.pruned).map
            fun left => (left.1, left.2, c.trunkForest)) =
      sumTerms (R := R)
        (ds.flatMap fun d =>
          (PLTree.coproductTermsList d.pruned).map
            fun left => (left.1, left.2, d.trunkForest)) := by
  rw [sumTerms_nestedCoproductLeftCuts, sumTerms_nestedCoproductLeftCuts,
    LForestTensorAlgebra.sumTerms_cut_listRelPerm (R := R) h]

theorem sumTerms_nestedCoproductRightCuts_listRelPerm
    {cs ds : List (PLTree.Cut α)}
    (h : PTree.ListRelPerm PLTree.Cut.Perm cs ds) :
    sumTerms (R := R)
        (cs.flatMap fun c =>
          c.trunkCoproductTerms.map
            fun right => (c.prunedForest, right.1, right.2)) =
      sumTerms (R := R)
        (ds.flatMap fun d =>
          d.trunkCoproductTerms.map
            fun right => (d.prunedForest, right.1, right.2)) := by
  rw [sumTerms_nestedCoproductRightCuts, sumTerms_nestedCoproductRightCuts,
    LForestTensorAlgebra.sumTerms_cut_listRelPerm (R := R) h]

theorem sumTerms_nestedCoproductLeftCuts_forall₂_perm
    {cs ds : List (PLTree.Cut α)} (h : List.Forall₂ PLTree.Cut.Perm cs ds) :
    sumTerms (R := R)
        (cs.flatMap fun c =>
          (PLTree.coproductTermsList c.pruned).map
            fun left => (left.1, left.2, c.trunkForest)) =
      sumTerms (R := R)
        (ds.flatMap fun d =>
          (PLTree.coproductTermsList d.pruned).map
            fun left => (left.1, left.2, d.trunkForest)) :=
  sumTerms_nestedCoproductLeftCuts_listRelPerm (R := R)
    (PTree.ListRelPerm.of_forall₂ h)

theorem sumTerms_nestedCoproductRightCuts_forall₂_perm
    {cs ds : List (PLTree.Cut α)} (h : List.Forall₂ PLTree.Cut.Perm cs ds) :
    sumTerms (R := R)
        (cs.flatMap fun c =>
          c.trunkCoproductTerms.map
            fun right => (c.prunedForest, right.1, right.2)) =
      sumTerms (R := R)
        (ds.flatMap fun d =>
          d.trunkCoproductTerms.map
            fun right => (d.prunedForest, right.1, right.2)) :=
  sumTerms_nestedCoproductRightCuts_listRelPerm (R := R)
    (PTree.ListRelPerm.of_forall₂ h)

theorem sumTerms_nestedCoproductLeftTerms (t : PLTree α) :
    sumTerms (R := R) (PLTree.nestedCoproductLeftTerms t) =
      sumTerms (R := R) (coproductLeftTerms (PLTree.coproductTerms t)) := by
  rw [← coproductLeft_pltree_coproduct_eq_sumTerms]
  simpa [PLTree.nestedCoproductLeftTerms, PLTree.labelledCoproduct, PLTree.coproductTerms] using
    sumTerms_nestedCoproductLeftCuts (R := R) (PLTree.cuts t)

theorem sumTerms_nestedCoproductRightTerms (t : PLTree α) :
    sumTerms (R := R) (PLTree.nestedCoproductRightTerms t) =
      sumTerms (R := R) (coproductRightTerms (PLTree.coproductTerms t)) := by
  rw [← coproductRight_pltree_coproduct_eq_sumTerms]
  simpa [PLTree.nestedCoproductRightTerms, PLTree.labelledCoproduct, PLTree.coproductTerms] using
    sumTerms_nestedCoproductRightCuts (R := R) (PLTree.cuts t)

theorem sumTerms_nestedCoproductLeftTerms_listRelPerm
    {t u : PLTree α}
    (h : PTree.ListRelPerm PLTree.Cut.Perm (PLTree.cuts t) (PLTree.cuts u)) :
    sumTerms (R := R) (PLTree.nestedCoproductLeftTerms t) =
      sumTerms (R := R) (PLTree.nestedCoproductLeftTerms u) := by
  simpa [PLTree.nestedCoproductLeftTerms] using
    sumTerms_nestedCoproductLeftCuts_listRelPerm (R := R) h

theorem sumTerms_nestedCoproductRightTerms_listRelPerm
    {t u : PLTree α}
    (h : PTree.ListRelPerm PLTree.Cut.Perm (PLTree.cuts t) (PLTree.cuts u)) :
    sumTerms (R := R) (PLTree.nestedCoproductRightTerms t) =
      sumTerms (R := R) (PLTree.nestedCoproductRightTerms u) := by
  simpa [PLTree.nestedCoproductRightTerms] using
    sumTerms_nestedCoproductRightCuts_listRelPerm (R := R) h

theorem sumTerms_nestedCoproductLeftTerms_perm {t u : PLTree α} (h : PLTree.Perm t u) :
    sumTerms (R := R) (PLTree.nestedCoproductLeftTerms t) =
      sumTerms (R := R) (PLTree.nestedCoproductLeftTerms u) :=
  sumTerms_nestedCoproductLeftTerms_listRelPerm (R := R)
    (PLTree.cuts_listRelPerm_of_perm h)

theorem sumTerms_nestedCoproductRightTerms_perm {t u : PLTree α} (h : PLTree.Perm t u) :
    sumTerms (R := R) (PLTree.nestedCoproductRightTerms t) =
      sumTerms (R := R) (PLTree.nestedCoproductRightTerms u) :=
  sumTerms_nestedCoproductRightTerms_listRelPerm (R := R)
    (PLTree.cuts_listRelPerm_of_perm h)

theorem erase_coproductLeft (x : LForestTensorAlgebra α R) :
    erase (R := R) (coproductLeft (R := R) x) =
      ForestTripleTensorAlgebra.coproductLeft (R := R)
        (LForestTensorAlgebra.erase (R := R) x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R (eraseTripleTermAddHom (α := α))).comp
        (coproductLeft (α := α) (R := R))) x =
      (ForestTripleTensorAlgebra.coproductLeft (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.eraseTermAddHom (α := α))) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    LRootedForest α × LRootedForest α) (by
      intro term
      change
        erase (R := R)
            (coproductLeft (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
          ForestTripleTensorAlgebra.coproductLeft (R := R)
            (LForestTensorAlgebra.erase (R := R)
              (LForestTensorAlgebra.ofPair (R := R) term))
      simp [erase_includeLeftPair, LRootedForest.erase_coproduct,
        eraseTripleTermAddHom, PLTree.eraseCoproductTerm, LRootedForest.erase, ofForests,
        ForestTripleTensorAlgebra.ofForests]) (by ext)) x

theorem erase_coproductRight (x : LForestTensorAlgebra α R) :
    erase (R := R) (coproductRight (R := R) x) =
      ForestTripleTensorAlgebra.coproductRight (R := R)
        (LForestTensorAlgebra.erase (R := R) x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R (eraseTripleTermAddHom (α := α))).comp
        (coproductRight (α := α) (R := R))) x =
      (ForestTripleTensorAlgebra.coproductRight (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.eraseTermAddHom (α := α))) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    LRootedForest α × LRootedForest α) (by
      intro term
      change
        erase (R := R)
            (coproductRight (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
          ForestTripleTensorAlgebra.coproductRight (R := R)
            (LForestTensorAlgebra.erase (R := R)
              (LForestTensorAlgebra.ofPair (R := R) term))
      simp [erase_includeRightPair, LRootedForest.erase_coproduct,
        eraseTripleTermAddHom, PLTree.eraseCoproductTerm, LRootedForest.erase, ofForests,
        ForestTripleTensorAlgebra.ofForests]) (by ext)) x

theorem constLabel_coproductLeft (a : α) (x : ForestTensorAlgebra R) :
    constLabel (R := R) a (ForestTripleTensorAlgebra.coproductLeft (R := R) x) =
      coproductLeft (R := R) (LForestTensorAlgebra.constLabel (R := R) a x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R (constLabelTripleTermAddHom a)).comp
        (ForestTripleTensorAlgebra.coproductLeft (R := R))) x =
      (coproductLeft (α := α) (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.constLabelTermAddHom a)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    RootedForest × RootedForest) (by
      intro term
      change
        constLabel (R := R) a
            (ForestTripleTensorAlgebra.coproductLeft (R := R)
              (ForestTensorAlgebra.ofPair (R := R) term)) =
          coproductLeft (R := R)
            (LForestTensorAlgebra.constLabel (R := R) a
              (ForestTensorAlgebra.ofPair (R := R) term))
      simp [constLabel_includeLeftPair, LRootedForest.constLabel_coproduct,
        constLabelTripleTermAddHom, PLTree.constLabelCoproductTerm,
        LRootedForest.constLabel, ofForests, ForestTripleTensorAlgebra.ofForests]) (by ext)) x

theorem constLabel_coproductRight (a : α) (x : ForestTensorAlgebra R) :
    constLabel (R := R) a (ForestTripleTensorAlgebra.coproductRight (R := R) x) =
      coproductRight (R := R) (LForestTensorAlgebra.constLabel (R := R) a x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R (constLabelTripleTermAddHom a)).comp
        (ForestTripleTensorAlgebra.coproductRight (R := R))) x =
      (coproductRight (α := α) (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.constLabelTermAddHom a)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    RootedForest × RootedForest) (by
      intro term
      change
        constLabel (R := R) a
            (ForestTripleTensorAlgebra.coproductRight (R := R)
              (ForestTensorAlgebra.ofPair (R := R) term)) =
          coproductRight (R := R)
            (LForestTensorAlgebra.constLabel (R := R) a
              (ForestTensorAlgebra.ofPair (R := R) term))
      simp [constLabel_includeRightPair, LRootedForest.constLabel_coproduct,
        constLabelTripleTermAddHom, PLTree.constLabelCoproductTerm,
        LRootedForest.constLabel, ofForests, ForestTripleTensorAlgebra.ofForests]) (by ext)) x

theorem mapLabels_coproductLeft {β : Type w} (f : α → β)
    (x : LForestTensorAlgebra α R) :
    mapLabels (R := R) f (coproductLeft (R := R) x) =
      coproductLeft (R := R) (LForestTensorAlgebra.mapLabels (R := R) f x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (mapLabelsTripleTermAddHom (α := α) f)).comp
        (coproductLeft (α := α) (R := R))) x =
      (coproductLeft (α := β) (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.mapLabelsTermAddHom (α := α) f)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    LRootedForest α × LRootedForest α) (by
      intro term
      change
        mapLabels (R := R) f
            (coproductLeft (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
          coproductLeft (R := R)
            (LForestTensorAlgebra.mapLabels (R := R) f
              (LForestTensorAlgebra.ofPair (R := R) term))
      simp [mapLabels_includeLeftPair, LRootedForest.mapLabels_coproduct,
        mapLabelsTripleTermAddHom, PLTree.mapCoproductTerm, LRootedForest.mapLabels,
        ofForests]) (by ext)) x

theorem mapLabels_coproductRight {β : Type w} (f : α → β)
    (x : LForestTensorAlgebra α R) :
    mapLabels (R := R) f (coproductRight (R := R) x) =
      coproductRight (R := R) (LForestTensorAlgebra.mapLabels (R := R) f x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (mapLabelsTripleTermAddHom (α := α) f)).comp
        (coproductRight (α := α) (R := R))) x =
      (coproductRight (α := β) (R := R)).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (LForestTensorAlgebra.mapLabelsTermAddHom (α := α) f)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M :=
    LRootedForest α × LRootedForest α) (by
      intro term
      change
        mapLabels (R := R) f
            (coproductRight (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
          coproductRight (R := R)
            (LForestTensorAlgebra.mapLabels (R := R) f
              (LForestTensorAlgebra.ofPair (R := R) term))
      simp [mapLabels_includeRightPair, LRootedForest.mapLabels_coproduct,
        mapLabelsTripleTermAddHom, PLTree.mapCoproductTerm, LRootedForest.mapLabels,
        ofForests]) (by ext)) x

theorem erase_sumTerms_coproductLeftTerms_pltree (t : PLTree α) :
    erase (R := R)
        (sumTerms (R := R) (coproductLeftTerms (PLTree.coproductTerms t))) =
      ForestTripleTensorAlgebra.sumTerms (R := R)
        (ForestTripleTensorAlgebra.coproductLeftTerms
          (PTree.coproductTerms (PLTree.erase t))) := by
  rw [← coproductLeft_pltree_coproduct_eq_sumTerms, erase_coproductLeft,
    PLTree.erase_labelledCoproduct,
    ForestTripleTensorAlgebra.coproductLeft_ptree_coproduct_eq_sumTerms]

theorem erase_sumTerms_coproductRightTerms_pltree (t : PLTree α) :
    erase (R := R)
        (sumTerms (R := R) (coproductRightTerms (PLTree.coproductTerms t))) =
      ForestTripleTensorAlgebra.sumTerms (R := R)
        (ForestTripleTensorAlgebra.coproductRightTerms
          (PTree.coproductTerms (PLTree.erase t))) := by
  rw [← coproductRight_pltree_coproduct_eq_sumTerms, erase_coproductRight,
    PLTree.erase_labelledCoproduct,
    ForestTripleTensorAlgebra.coproductRight_ptree_coproduct_eq_sumTerms]

theorem erase_sumTerms_nestedCoproductLeftTerms_pltree (t : PLTree α) :
    erase (R := R) (sumTerms (R := R) (PLTree.nestedCoproductLeftTerms t)) =
      ForestTripleTensorAlgebra.sumTerms (R := R)
        (PTree.nestedCoproductLeftTerms (PLTree.erase t)) := by
  rw [erase_sumTerms]
  rw [show (PLTree.nestedCoproductLeftTerms t).map
      (eraseTripleTermAddHom (α := α)) =
        (PLTree.nestedCoproductLeftTerms t).map PLTree.eraseTripleCoproductTerm by
    apply List.map_congr_left
    intro term _hterm
    rfl]
  rw [PLTree.nestedCoproductLeftTerms_erase]

theorem erase_sumTerms_nestedCoproductRightTerms_pltree (t : PLTree α) :
    erase (R := R) (sumTerms (R := R) (PLTree.nestedCoproductRightTerms t)) =
      ForestTripleTensorAlgebra.sumTerms (R := R)
        (PTree.nestedCoproductRightTerms (PLTree.erase t)) := by
  rw [erase_sumTerms]
  rw [show (PLTree.nestedCoproductRightTerms t).map
      (eraseTripleTermAddHom (α := α)) =
        (PLTree.nestedCoproductRightTerms t).map PLTree.eraseTripleCoproductTerm by
    apply List.map_congr_left
    intro term _hterm
    rfl]
  rw [PLTree.nestedCoproductRightTerms_erase]

theorem constLabel_sumTerms_coproductLeftTerms_ptree (a : α) (t : PTree) :
    constLabel (R := R) a
        (ForestTripleTensorAlgebra.sumTerms (R := R)
          (ForestTripleTensorAlgebra.coproductLeftTerms (PTree.coproductTerms t))) =
      sumTerms (R := R)
        (coproductLeftTerms (PLTree.coproductTerms (PLTree.constLabel a t))) := by
  rw [← ForestTripleTensorAlgebra.coproductLeft_ptree_coproduct_eq_sumTerms,
    constLabel_coproductLeft, PLTree.constLabel_labelledCoproduct,
    coproductLeft_pltree_coproduct_eq_sumTerms]

theorem constLabel_sumTerms_coproductRightTerms_ptree (a : α) (t : PTree) :
    constLabel (R := R) a
        (ForestTripleTensorAlgebra.sumTerms (R := R)
          (ForestTripleTensorAlgebra.coproductRightTerms (PTree.coproductTerms t))) =
      sumTerms (R := R)
        (coproductRightTerms (PLTree.coproductTerms (PLTree.constLabel a t))) := by
  rw [← ForestTripleTensorAlgebra.coproductRight_ptree_coproduct_eq_sumTerms,
    constLabel_coproductRight, PLTree.constLabel_labelledCoproduct,
    coproductRight_pltree_coproduct_eq_sumTerms]

theorem mapLabels_sumTerms_coproductLeftTerms_pltree {β : Type w}
    (f : α → β) (t : PLTree α) :
    mapLabels (R := R) f
        (sumTerms (R := R) (coproductLeftTerms (PLTree.coproductTerms t))) =
      sumTerms (R := R)
        (coproductLeftTerms (PLTree.coproductTerms (PLTree.map f t))) := by
  rw [← coproductLeft_pltree_coproduct_eq_sumTerms, mapLabels_coproductLeft,
    PLTree.mapLabels_labelledCoproduct, coproductLeft_pltree_coproduct_eq_sumTerms]

theorem mapLabels_sumTerms_coproductRightTerms_pltree {β : Type w}
    (f : α → β) (t : PLTree α) :
    mapLabels (R := R) f
        (sumTerms (R := R) (coproductRightTerms (PLTree.coproductTerms t))) =
      sumTerms (R := R)
        (coproductRightTerms (PLTree.coproductTerms (PLTree.map f t))) := by
  rw [← coproductRight_pltree_coproduct_eq_sumTerms, mapLabels_coproductRight,
    PLTree.mapLabels_labelledCoproduct, coproductRight_pltree_coproduct_eq_sumTerms]

end

end LForestTripleTensorAlgebra

namespace LRootedTree

noncomputable section

variable {α : Type u} {R : Type v}

/-- The BCK coproduct of a non-planar labelled rooted tree. -/
def coproduct [Semiring R] (τ : LRootedTree α) : LForestTensorAlgebra α R :=
  Quotient.lift (PLTree.labelledCoproduct (R := R))
    (fun _ _ h => PLTree.labelledCoproduct_perm (R := R) h) τ

@[simp]
theorem coproduct_ofPLTree [Semiring R] (t : PLTree α) :
    coproduct (R := R) (LRootedTree.ofPLTree t) =
      PLTree.labelledCoproduct (R := R) t :=
  rfl

theorem coproduct_out [Semiring R] (τ : LRootedTree α) :
    coproduct (R := R) τ =
      PLTree.labelledCoproduct (R := R) (Quotient.out τ) := by
  refine Quotient.inductionOn τ ?_
  intro t
  exact (PLTree.labelledCoproduct_perm (R := R) (LRootedTree.out_perm_ofPLTree t)).symm

theorem coproduct_graft_coe [Semiring R] (a : α) (ts : List (LRootedTree α)) :
    coproduct (R := R) (LRootedForest.graft a (ts : LRootedForest α)) =
      LForestTensorAlgebra.sumTerms (R := R)
        ((PLTree.coproductTermsList (ts.map Quotient.out)).map fun term =>
          (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))) +
        LForestTensorAlgebra.ofPair (R := R)
          (LRootedForest.singleton (LRootedForest.graft a (ts : LRootedForest α)), 0) := by
  rw [LRootedForest.graft_coe, coproduct_ofPLTree, PLTree.labelledCoproduct_node]

/-- The reduced BCK coproduct of a non-planar labelled rooted tree. -/
def reducedCoproduct [Semiring R] (τ : LRootedTree α) : LForestTensorAlgebra α R :=
  Quotient.lift (PLTree.labelledReducedCoproduct (R := R))
    (fun _ _ h => PLTree.labelledReducedCoproduct_perm (R := R) h) τ

@[simp]
theorem reducedCoproduct_ofPLTree [Semiring R] (t : PLTree α) :
    reducedCoproduct (R := R) (LRootedTree.ofPLTree t) =
      PLTree.labelledReducedCoproduct (R := R) t :=
  rfl

theorem reducedCoproduct_out [Semiring R] (τ : LRootedTree α) :
    reducedCoproduct (R := R) τ =
      PLTree.labelledReducedCoproduct (R := R) (Quotient.out τ) := by
  refine Quotient.inductionOn τ ?_
  intro t
  exact (PLTree.labelledReducedCoproduct_perm (R := R) (LRootedTree.out_perm_ofPLTree t)).symm

theorem erase_reducedCoproduct [CommSemiring R] (τ : LRootedTree α) :
    LForestTensorAlgebra.erase (R := R) (reducedCoproduct (R := R) τ) =
      RootedTree.reducedCoproduct (R := R) (LRootedTree.erase τ) := by
  rw [reducedCoproduct_out, PLTree.erase_labelledReducedCoproduct,
    RootedTree.reducedCoproduct_out]
  exact PTree.reducedCoproduct_perm (LRootedTree.erase_out_perm τ)

theorem coproduct_eq_forest_singleton [CommSemiring R] (τ : LRootedTree α) :
    coproduct (R := R) τ =
      LRootedForest.coproduct (R := R) (LRootedForest.singleton τ) := by
  rw [coproduct_out, LRootedForest.coproduct_singleton]

theorem erase_coproduct [CommSemiring R] (τ : LRootedTree α) :
    LForestTensorAlgebra.erase (R := R) (coproduct (R := R) τ) =
      RootedTree.coproduct (R := R) (LRootedTree.erase τ) := by
  rw [coproduct_out, PLTree.erase_labelledCoproduct, RootedTree.coproduct_out]
  exact PTree.coproduct_perm (LRootedTree.erase_out_perm τ)

theorem mapLabels_coproduct [CommSemiring R] {β : Type w}
    (f : α → β) (τ : LRootedTree α) :
    LForestTensorAlgebra.mapLabels (R := R) f (coproduct (R := R) τ) =
      coproduct (R := R) (LRootedTree.map f τ) := by
  rw [coproduct_out, PLTree.mapLabels_labelledCoproduct, coproduct_out]
  exact PLTree.labelledCoproduct_perm (LRootedTree.map_out_perm f τ)

theorem constLabel_coproduct [CommSemiring R] (a : α) (τ : RootedTree) :
    LForestTensorAlgebra.constLabel (R := R) a (RootedTree.coproduct (R := R) τ) =
      coproduct (R := R) (LRootedTree.constLabel a τ) := by
  rw [RootedTree.coproduct_out, coproduct_out, PLTree.constLabel_labelledCoproduct]
  exact PLTree.labelledCoproduct_perm (LRootedTree.constLabel_out_perm a τ)

end

end LRootedTree

namespace LForestAlgebra

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

private def coproductMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    Multiplicative (LRootedForest α) →* LForestTensorAlgebra α R where
  toFun φ := LRootedForest.coproduct (R := R) (Multiplicative.toAdd φ)
  map_one' := by
    change LRootedForest.coproduct (R := R) (0 : LRootedForest α) = 1
    simp
  map_mul' φ ψ := by
    change
      LRootedForest.coproduct (R := R) (Multiplicative.toAdd (φ * ψ)) =
        LRootedForest.coproduct (R := R) (Multiplicative.toAdd φ) *
          LRootedForest.coproduct (R := R) (Multiplicative.toAdd ψ)
    change
      LRootedForest.coproduct (R := R)
          (Multiplicative.toAdd φ + Multiplicative.toAdd ψ) =
        LRootedForest.coproduct (R := R) (Multiplicative.toAdd φ) *
          LRootedForest.coproduct (R := R) (Multiplicative.toAdd ψ)
    simp

/-- The labelled BCK coproduct as an algebra morphism on the labelled forest algebra. -/
def coproduct (α : Type u) (R : Type v) [CommSemiring R] :
    LForestAlgebra α R →ₐ[R] LForestTensorAlgebra α R :=
  (AddMonoidAlgebra.lift R (LForestTensorAlgebra α R) (LRootedForest α))
    (coproductMonoidHom α R)

/-- The iterated labelled coproduct `(Δ ⊗ id) ∘ Δ`. -/
def coproductLeft (α : Type u) (R : Type v) [CommSemiring R] :
    LForestAlgebra α R →ₐ[R] LForestTripleTensorAlgebra α R :=
  LForestTripleTensorAlgebra.coproductLeft.comp (coproduct α R)

/-- The iterated labelled coproduct `(id ⊗ Δ) ∘ Δ`. -/
def coproductRight (α : Type u) (R : Type v) [CommSemiring R] :
    LForestAlgebra α R →ₐ[R] LForestTripleTensorAlgebra α R :=
  LForestTripleTensorAlgebra.coproductRight.comp (coproduct α R)

@[simp]
theorem coproduct_ofForest (φ : LRootedForest α) :
    coproduct α R (ofForest (R := R) φ) = LRootedForest.coproduct (R := R) φ := by
  simp [coproduct, ofForest, coproductMonoidHom]

@[simp]
theorem coproductLeft_ofForest (φ : LRootedForest α) :
    coproductLeft α R (ofForest (R := R) φ) =
      LForestTripleTensorAlgebra.coproductLeft (LRootedForest.coproduct (R := R) φ) := by
  simp [coproductLeft]

@[simp]
theorem coproductRight_ofForest (φ : LRootedForest α) :
    coproductRight α R (ofForest (R := R) φ) =
      LForestTripleTensorAlgebra.coproductRight (LRootedForest.coproduct (R := R) φ) := by
  simp [coproductRight]

@[simp]
theorem coproduct_ofForest_zero :
    coproduct α R (ofForest (R := R) (0 : LRootedForest α)) = 1 := by
  simp

@[simp]
theorem coproduct_ofForest_empty :
    coproduct α R (ofForest (R := R) LRootedForest.empty) = 1 := by
  simp

@[simp]
theorem coproduct_ofForest_singleton (τ : LRootedTree α) :
    coproduct α R (ofForest (R := R) (LRootedForest.singleton τ)) =
      PLTree.labelledCoproduct (R := R) (Quotient.out τ) := by
  simp

theorem coproduct_ofForest_singleton_tree (τ : LRootedTree α) :
    coproduct α R (ofForest (R := R) (LRootedForest.singleton τ)) =
      LRootedTree.coproduct (R := R) τ := by
  rw [coproduct_ofForest]
  exact (LRootedTree.coproduct_eq_forest_singleton (R := R) τ).symm

theorem coproductLeft_ofForest_singleton_ofPLTree_eq_sumTerms (t : PLTree α) :
    coproductLeft α R
        (ofForest (R := R) (LRootedForest.singleton (LRootedTree.ofPLTree t))) =
      LForestTripleTensorAlgebra.sumTerms (R := R)
        (LForestTripleTensorAlgebra.coproductLeftTerms (PLTree.coproductTerms t)) := by
  rw [coproductLeft_ofForest, LRootedForest.coproduct_singleton_ofPLTree,
    LForestTripleTensorAlgebra.coproductLeft_pltree_coproduct_eq_sumTerms]

theorem coproductRight_ofForest_singleton_ofPLTree_eq_sumTerms (t : PLTree α) :
    coproductRight α R
        (ofForest (R := R) (LRootedForest.singleton (LRootedTree.ofPLTree t))) =
      LForestTripleTensorAlgebra.sumTerms (R := R)
        (LForestTripleTensorAlgebra.coproductRightTerms (PLTree.coproductTerms t)) := by
  rw [coproductRight_ofForest, LRootedForest.coproduct_singleton_ofPLTree,
    LForestTripleTensorAlgebra.coproductRight_pltree_coproduct_eq_sumTerms]

theorem erase_coproduct_ofForest (φ : LRootedForest α) :
    LForestTensorAlgebra.erase (R := R)
        (coproduct α R (ofForest (R := R) φ)) =
      ForestAlgebra.coproduct R
        (ForestAlgebra.ofForest (R := R) (LRootedForest.erase φ)) := by
  rw [coproduct_ofForest, ForestAlgebra.coproduct_ofForest,
    LRootedForest.erase_coproduct]

theorem constLabel_coproduct_ofForest (a : α) (φ : RootedForest) :
    LForestTensorAlgebra.constLabel (R := R) a
        (ForestAlgebra.coproduct R (ForestAlgebra.ofForest (R := R) φ)) =
      coproduct α R (constLabel a R (ForestAlgebra.ofForest (R := R) φ)) := by
  rw [ForestAlgebra.coproduct_ofForest, constLabel_ofForest, coproduct_ofForest,
    LRootedForest.constLabel_coproduct]

theorem eraseLabels_coproduct (x : LForestAlgebra α R) :
    LForestTensorAlgebra.erase (R := R) (coproduct α R x) =
      ForestAlgebra.coproduct R (eraseLabels (α := α) R x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (LForestTensorAlgebra.eraseTermAddHom (α := α))).comp
        (coproduct α R)) x =
      ((ForestAlgebra.coproduct R).comp (eraseLabels (α := α) R)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := LRootedForest α) (by
    intro φ
    change
      LForestTensorAlgebra.erase (R := R)
          (coproduct α R (ofForest (R := R) (Multiplicative.toAdd φ))) =
        ForestAlgebra.coproduct R
          (eraseLabels (α := α) R (ofForest (R := R) (Multiplicative.toAdd φ)))
    simp [LRootedForest.erase_coproduct]) (by ext)) x

theorem constLabel_coproduct (a : α) (x : ForestAlgebra R) :
    LForestTensorAlgebra.constLabel (R := R) a (ForestAlgebra.coproduct R x) =
      coproduct α R (constLabel a R x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (LForestTensorAlgebra.constLabelTermAddHom a)).comp
        (ForestAlgebra.coproduct R)) x =
      ((coproduct α R).comp (constLabel a R)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := RootedForest) (by
    intro φ
    change
      LForestTensorAlgebra.constLabel (R := R) a
          (ForestAlgebra.coproduct R (ForestAlgebra.ofForest (R := R) (Multiplicative.toAdd φ))) =
        coproduct α R
          (constLabel a R (ForestAlgebra.ofForest (R := R) (Multiplicative.toAdd φ)))
    simp [LRootedForest.constLabel_coproduct]) (by ext)) x

theorem mapLabels_coproduct {β : Type w} (f : α → β) (x : LForestAlgebra α R) :
    LForestTensorAlgebra.mapLabels (R := R) f (coproduct α R x) =
      coproduct β R (mapLabels (R := R) f x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (LForestTensorAlgebra.mapLabelsTermAddHom (α := α) f)).comp
        (coproduct α R)) x =
      ((coproduct β R).comp (mapLabels (R := R) f)) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := LRootedForest α) (by
    intro φ
    change
      LForestTensorAlgebra.mapLabels (R := R) f
          (coproduct α R (ofForest (R := R) (Multiplicative.toAdd φ))) =
        coproduct β R
          (mapLabels (R := R) f (ofForest (R := R) (Multiplicative.toAdd φ)))
    simp [LRootedForest.mapLabels_coproduct]) (by ext)) x

theorem eraseLabels_coproductLeft (x : LForestAlgebra α R) :
    LForestTripleTensorAlgebra.erase (R := R) (coproductLeft α R x) =
      ForestAlgebra.coproductLeft R (eraseLabels (α := α) R x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (LForestTripleTensorAlgebra.eraseTripleTermAddHom (α := α))).comp
        (coproductLeft α R)) x =
      (ForestAlgebra.coproductLeft R).comp (eraseLabels (α := α) R) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := LRootedForest α) (by
    intro φ
    change
      LForestTripleTensorAlgebra.erase (R := R)
          (coproductLeft α R (ofForest (R := R) φ)) =
        ForestAlgebra.coproductLeft R
          (eraseLabels (α := α) R (ofForest (R := R) φ))
    simp [LForestTripleTensorAlgebra.erase_coproductLeft,
      LRootedForest.erase_coproduct]) (by ext)) x

theorem eraseLabels_coproductRight (x : LForestAlgebra α R) :
    LForestTripleTensorAlgebra.erase (R := R) (coproductRight α R x) =
      ForestAlgebra.coproductRight R (eraseLabels (α := α) R x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (LForestTripleTensorAlgebra.eraseTripleTermAddHom (α := α))).comp
        (coproductRight α R)) x =
      (ForestAlgebra.coproductRight R).comp (eraseLabels (α := α) R) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := LRootedForest α) (by
    intro φ
    change
      LForestTripleTensorAlgebra.erase (R := R)
          (coproductRight α R (ofForest (R := R) φ)) =
        ForestAlgebra.coproductRight R
          (eraseLabels (α := α) R (ofForest (R := R) φ))
    simp [LForestTripleTensorAlgebra.erase_coproductRight,
      LRootedForest.erase_coproduct]) (by ext)) x

theorem constLabel_coproductLeft (a : α) (x : ForestAlgebra R) :
    LForestTripleTensorAlgebra.constLabel (R := R) a (ForestAlgebra.coproductLeft R x) =
      coproductLeft α R (constLabel a R x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (LForestTripleTensorAlgebra.constLabelTripleTermAddHom a)).comp
        (ForestAlgebra.coproductLeft R)) x =
      (coproductLeft α R).comp (constLabel a R) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := RootedForest) (by
    intro φ
    change
      LForestTripleTensorAlgebra.constLabel (R := R) a
          (ForestAlgebra.coproductLeft R (ForestAlgebra.ofForest (R := R) φ)) =
        coproductLeft α R (constLabel a R (ForestAlgebra.ofForest (R := R) φ))
    simp [LForestTripleTensorAlgebra.constLabel_coproductLeft,
      LRootedForest.constLabel_coproduct]) (by ext)) x

theorem constLabel_coproductRight (a : α) (x : ForestAlgebra R) :
    LForestTripleTensorAlgebra.constLabel (R := R) a (ForestAlgebra.coproductRight R x) =
      coproductRight α R (constLabel a R x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (LForestTripleTensorAlgebra.constLabelTripleTermAddHom a)).comp
        (ForestAlgebra.coproductRight R)) x =
      (coproductRight α R).comp (constLabel a R) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := RootedForest) (by
    intro φ
    change
      LForestTripleTensorAlgebra.constLabel (R := R) a
          (ForestAlgebra.coproductRight R (ForestAlgebra.ofForest (R := R) φ)) =
        coproductRight α R (constLabel a R (ForestAlgebra.ofForest (R := R) φ))
    simp [LForestTripleTensorAlgebra.constLabel_coproductRight,
      LRootedForest.constLabel_coproduct]) (by ext)) x

theorem mapLabels_coproductLeft {β : Type w} (f : α → β)
    (x : LForestAlgebra α R) :
    LForestTripleTensorAlgebra.mapLabels (R := R) f (coproductLeft α R x) =
      coproductLeft β R (mapLabels (R := R) f x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (LForestTripleTensorAlgebra.mapLabelsTripleTermAddHom (α := α) f)).comp
        (coproductLeft α R)) x =
      (coproductLeft β R).comp (mapLabels (R := R) f) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := LRootedForest α) (by
    intro φ
    change
      LForestTripleTensorAlgebra.mapLabels (R := R) f
          (coproductLeft α R (ofForest (R := R) φ)) =
        coproductLeft β R (mapLabels (R := R) f (ofForest (R := R) φ))
    simp [LForestTripleTensorAlgebra.mapLabels_coproductLeft,
      LRootedForest.mapLabels_coproduct]) (by ext)) x

theorem mapLabels_coproductRight {β : Type w} (f : α → β)
    (x : LForestAlgebra α R) :
    LForestTripleTensorAlgebra.mapLabels (R := R) f (coproductRight α R x) =
      coproductRight β R (mapLabels (R := R) f x) := by
  change
    ((AddMonoidAlgebra.mapDomainAlgHom R R
        (LForestTripleTensorAlgebra.mapLabelsTripleTermAddHom (α := α) f)).comp
        (coproductRight α R)) x =
      (coproductRight β R).comp (mapLabels (R := R) f) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := LRootedForest α) (by
    intro φ
    change
      LForestTripleTensorAlgebra.mapLabels (R := R) f
          (coproductRight α R (ofForest (R := R) φ)) =
        coproductRight β R (mapLabels (R := R) f (ofForest (R := R) φ))
    simp [LForestTripleTensorAlgebra.mapLabels_coproductRight,
      LRootedForest.mapLabels_coproduct]) (by ext)) x

theorem coproductLeft_eq_coproductRight_of_singletons
    (h : ∀ τ : LRootedTree α,
      coproductLeft α R (ofForest (R := R) (LRootedForest.singleton τ)) =
        coproductRight α R (ofForest (R := R) (LRootedForest.singleton τ))) :
    coproductLeft α R = coproductRight α R := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext)
  apply MonoidHom.ext
  intro φ
  change
    coproductLeft α R (ofForest (R := R) (Multiplicative.toAdd φ)) =
      coproductRight α R (ofForest (R := R) (Multiplicative.toAdd φ))
  refine Quotient.inductionOn (Multiplicative.toAdd φ) ?_
  intro ts
  induction ts with
  | nil =>
      simp
  | cons τ ts ih =>
      change
        coproductLeft α R (ofForest (R := R)
            (LRootedForest.singleton τ + (ts : LRootedForest α))) =
          coproductRight α R (ofForest (R := R)
            (LRootedForest.singleton τ + (ts : LRootedForest α)))
      have ih' :
          coproductLeft α R (ofForest (R := R) (ts : LRootedForest α)) =
            coproductRight α R (ofForest (R := R) (ts : LRootedForest α)) := by
        simpa using ih
      rw [ofForest_add, map_mul, map_mul, h τ, ih']

theorem coproductLeft_eq_coproductRight_iff_singletons :
    coproductLeft α R = coproductRight α R ↔
      ∀ τ : LRootedTree α,
        coproductLeft α R (ofForest (R := R) (LRootedForest.singleton τ)) =
          coproductRight α R (ofForest (R := R) (LRootedForest.singleton τ)) := by
  constructor
  · intro h τ
    rw [h]
  · exact coproductLeft_eq_coproductRight_of_singletons (α := α) (R := R)

theorem coproductLeft_eq_coproductRight_of_pltree_singletons
    (h : ∀ t : PLTree α,
      coproductLeft α R
          (ofForest (R := R) (LRootedForest.singleton (LRootedTree.ofPLTree t))) =
        coproductRight α R
          (ofForest (R := R) (LRootedForest.singleton (LRootedTree.ofPLTree t)))) :
    coproductLeft α R = coproductRight α R := by
  apply coproductLeft_eq_coproductRight_of_singletons (α := α) (R := R)
  intro τ
  have hτ : LRootedTree.ofPLTree (Quotient.out τ) = τ := Quotient.out_eq τ
  simpa [hτ] using h (Quotient.out τ)

theorem coproductLeft_eq_coproductRight_iff_pltree_singletons :
    coproductLeft α R = coproductRight α R ↔
      ∀ t : PLTree α,
        coproductLeft α R
            (ofForest (R := R) (LRootedForest.singleton (LRootedTree.ofPLTree t))) =
          coproductRight α R
            (ofForest (R := R) (LRootedForest.singleton (LRootedTree.ofPLTree t))) := by
  constructor
  · intro h t
    rw [h]
  · exact coproductLeft_eq_coproductRight_of_pltree_singletons (α := α) (R := R)

theorem coproductLeft_eq_coproductRight_of_pltree_coproductTerms
    (h : ∀ t : PLTree α,
      LForestTripleTensorAlgebra.sumTerms (R := R)
          (LForestTripleTensorAlgebra.coproductLeftTerms (PLTree.coproductTerms t)) =
        LForestTripleTensorAlgebra.sumTerms (R := R)
          (LForestTripleTensorAlgebra.coproductRightTerms (PLTree.coproductTerms t))) :
    coproductLeft α R = coproductRight α R := by
  apply coproductLeft_eq_coproductRight_of_pltree_singletons (α := α) (R := R)
  intro t
  rw [coproductLeft_ofForest_singleton_ofPLTree_eq_sumTerms,
    coproductRight_ofForest_singleton_ofPLTree_eq_sumTerms]
  exact h t

theorem coproductLeft_eq_coproductRight_iff_pltree_coproductTerms :
    coproductLeft α R = coproductRight α R ↔
      ∀ t : PLTree α,
        LForestTripleTensorAlgebra.sumTerms (R := R)
            (LForestTripleTensorAlgebra.coproductLeftTerms (PLTree.coproductTerms t)) =
          LForestTripleTensorAlgebra.sumTerms (R := R)
            (LForestTripleTensorAlgebra.coproductRightTerms (PLTree.coproductTerms t)) := by
  constructor
  · intro h t
    have hsingle :=
      (coproductLeft_eq_coproductRight_iff_pltree_singletons (α := α) (R := R)).1 h t
    rw [coproductLeft_ofForest_singleton_ofPLTree_eq_sumTerms,
      coproductRight_ofForest_singleton_ofPLTree_eq_sumTerms] at hsingle
    exact hsingle
  · exact coproductLeft_eq_coproductRight_of_pltree_coproductTerms (α := α) (R := R)

theorem coproductLeft_eq_coproductRight_of_nestedCoproductTerms
    (h : ∀ t : PLTree α,
      LForestTripleTensorAlgebra.sumTerms (R := R) (PLTree.nestedCoproductLeftTerms t) =
        LForestTripleTensorAlgebra.sumTerms (R := R) (PLTree.nestedCoproductRightTerms t)) :
    coproductLeft α R = coproductRight α R := by
  apply coproductLeft_eq_coproductRight_of_pltree_coproductTerms (α := α) (R := R)
  intro t
  rw [← LForestTripleTensorAlgebra.sumTerms_nestedCoproductLeftTerms (R := R) t,
    ← LForestTripleTensorAlgebra.sumTerms_nestedCoproductRightTerms (R := R) t]
  exact h t

theorem coproductLeft_eq_coproductRight_iff_nestedCoproductTerms :
    coproductLeft α R = coproductRight α R ↔
      ∀ t : PLTree α,
        LForestTripleTensorAlgebra.sumTerms (R := R) (PLTree.nestedCoproductLeftTerms t) =
          LForestTripleTensorAlgebra.sumTerms (R := R)
            (PLTree.nestedCoproductRightTerms t) := by
  constructor
  · intro h t
    have hterms :=
      (coproductLeft_eq_coproductRight_iff_pltree_coproductTerms
        (α := α) (R := R)).1 h t
    rw [LForestTripleTensorAlgebra.sumTerms_nestedCoproductLeftTerms,
      LForestTripleTensorAlgebra.sumTerms_nestedCoproductRightTerms]
    exact hterms
  · exact coproductLeft_eq_coproductRight_of_nestedCoproductTerms (α := α) (R := R)

theorem coproductLeft_eq_coproductRight_of_nestedCoproductTerms_perm
    (h : ∀ t : PLTree α,
      (PLTree.nestedCoproductLeftTerms t).Perm (PLTree.nestedCoproductRightTerms t)) :
    coproductLeft α R = coproductRight α R :=
  coproductLeft_eq_coproductRight_of_nestedCoproductTerms (α := α) (R := R) fun t =>
    LForestTripleTensorAlgebra.sumTerms_perm (R := R) (h t)

theorem coproductLeft_eq_coproductRight_of_pltree_coproductTerms_perm
    (h : ∀ t : PLTree α,
      (LForestTripleTensorAlgebra.coproductLeftTerms (PLTree.coproductTerms t)).Perm
        (LForestTripleTensorAlgebra.coproductRightTerms (PLTree.coproductTerms t))) :
    coproductLeft α R = coproductRight α R :=
  coproductLeft_eq_coproductRight_of_nestedCoproductTerms_perm (α := α) (R := R) fun t =>
    (LForestTripleTensorAlgebra.nestedCoproductTerms_perm_iff_coproductTerms_perm t).2
      (h t)

theorem coproductLeft_eq_coproductRight_of_lrootedForest_coproductTerms_perm
    (h : ∀ φ : LRootedForest α,
      (LForestTripleTensorAlgebra.coproductLeftTerms (LRootedForest.coproductTerms φ)).Perm
        (LForestTripleTensorAlgebra.coproductRightTerms (LRootedForest.coproductTerms φ))) :
    coproductLeft α R = coproductRight α R := by
  apply coproductLeft_eq_coproductRight_of_pltree_coproductTerms_perm (α := α) (R := R)
  intro t
  have hsingle := h (LRootedForest.singleton (LRootedTree.ofPLTree t))
  have hterms := LRootedForest.coproductTerms_singleton_ofPLTree_perm t
  exact (LForestTripleTensorAlgebra.coproductLeftTerms_perm hterms).symm.trans
    (hsingle.trans (LForestTripleTensorAlgebra.coproductRightTerms_perm hterms))

theorem coproductLeft_eq_coproductRight :
    coproductLeft α R = coproductRight α R :=
  coproductLeft_eq_coproductRight_of_nestedCoproductTerms_perm (α := α) (R := R)
    LForestTripleTensorAlgebra.nestedCoproductTerms_left_right_perm

theorem counitLeft_coproduct :
    (LForestTensorAlgebra.counitLeft (R := R)).comp (coproduct α R) =
      AlgHom.id R (LForestAlgebra α R) := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext)
  apply MonoidHom.ext
  intro φ
  simpa [coproduct, coproductMonoidHom, ofForest] using
    LRootedForest.counitLeft_coproduct (R := R) (Multiplicative.toAdd φ)

theorem counitRight_coproduct :
    (LForestTensorAlgebra.counitRight (R := R)).comp (coproduct α R) =
      AlgHom.id R (LForestAlgebra α R) := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext)
  apply MonoidHom.ext
  intro φ
  simpa [coproduct, coproductMonoidHom, ofForest] using
    LRootedForest.counitRight_coproduct (R := R) (Multiplicative.toAdd φ)

end

end LForestAlgebra

end HopfAlgebras
