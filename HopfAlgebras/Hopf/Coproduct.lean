/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Cuts.Rooted
import HopfAlgebras.Algebra.Forest

/-!
# Coproduct Terms in the Forest Algebra

This file turns the finite cut-term lists from `HopfAlgebras.Cuts.Rooted` into elements of
the monoid algebra on pairs of rooted forests. This is a tensor-coded target
for the BCK coproduct: a pair `(φ, ψ)` represents the basis tensor
`φ ⊗ ψ`.

The tree coproduct is first defined for planar representatives, then quotiented
to non-planar rooted trees and forests.

## Main definitions

* `ForestTensorAlgebra` - monoid algebra on pairs of rooted forests
* `ForestTensorAlgebra.ofForests` - basis tensor represented by a pair
* `ForestTensorAlgebra.sumTerms` - finite sum of basis tensors
* `PTree.coproduct` - planar tree coproduct as a finite algebra element
* `PTree.coproductList` - multiplicative extension to planar forests
* `RootedTree.coproduct` - non-planar tree coproduct
* `RootedForest.coproduct` - multiplicative extension to non-planar forests

## References

* Alain Connes, Dirk Kreimer, *Hopf Algebras, Renormalization and
  Noncommutative Geometry*
* Loic Foissy, *An introduction to Hopf algebras of trees*
-/

namespace HopfAlgebras

universe u

/-- Tensor-coded forest algebra: `(φ, ψ)` represents the basis tensor `φ ⊗ ψ`. -/
abbrev ForestTensorAlgebra (R : Type u) [Semiring R] : Type u :=
  AddMonoidAlgebra R (RootedForest × RootedForest)

namespace ForestTensorAlgebra

noncomputable section

variable {R : Type u}

/-- The basis tensor represented by a pair of rooted forests. -/
def ofPair [Semiring R] (term : RootedForest × RootedForest) : ForestTensorAlgebra R :=
  AddMonoidAlgebra.single term 1

/-- The basis tensor `φ ⊗ ψ`. -/
def ofForests [Semiring R] (φ ψ : RootedForest) : ForestTensorAlgebra R :=
  ofPair (R := R) (φ, ψ)

@[simp]
theorem ofPair_zero [Semiring R] : ofPair (R := R) 0 = 1 := by
  simp [ofPair, AddMonoidAlgebra.one_def]

@[simp]
theorem ofForests_zero_zero [Semiring R] : ofForests (R := R) 0 0 = 1 := by
  change ofPair (R := R) (0 : RootedForest × RootedForest) = 1
  simp

@[simp]
theorem ofPair_add [Semiring R] (x y : RootedForest × RootedForest) :
    ofPair (R := R) (x + y) = ofPair x * ofPair y := by
  simp [ofPair, AddMonoidAlgebra.single_mul_single]

@[simp]
theorem ofForests_add [Semiring R]
    (φ₁ φ₂ ψ₁ ψ₂ : RootedForest) :
    ofForests (R := R) (φ₁ + φ₂) (ψ₁ + ψ₂) =
      ofForests φ₁ ψ₁ * ofForests φ₂ ψ₂ := by
  simp [ofForests, ofPair, AddMonoidAlgebra.single_mul_single]

/-- Sum a finite list of basis tensors. Duplicates contribute multiplicity. -/
def sumTerms [Semiring R] (terms : List (RootedForest × RootedForest)) :
    ForestTensorAlgebra R :=
  (terms.map (ofPair (R := R))).sum

@[simp]
theorem sumTerms_nil [Semiring R] : sumTerms (R := R) [] = 0 :=
  rfl

@[simp]
theorem sumTerms_cons [Semiring R] (term : RootedForest × RootedForest)
    (terms : List (RootedForest × RootedForest)) :
    sumTerms (R := R) (term :: terms) = ofPair term + sumTerms terms :=
  rfl

@[simp]
theorem sumTerms_singleton [Semiring R] (term : RootedForest × RootedForest) :
    sumTerms (R := R) [term] = ofPair term := by
  simp [sumTerms]

theorem sumTerms_append [Semiring R]
    (xs ys : List (RootedForest × RootedForest)) :
    sumTerms (R := R) (xs ++ ys) = sumTerms xs + sumTerms ys := by
  simp [sumTerms, List.map_append]

theorem sumTerms_perm [Semiring R] {xs ys : List (RootedForest × RootedForest)}
    (h : xs.Perm ys) :
    sumTerms (R := R) xs = sumTerms ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem sumTerms_eq_of_forall₂_eq [Semiring R] :
    ∀ {xs ys : List (RootedForest × RootedForest)},
      List.Forall₂ (fun x y => x = y) xs ys →
        sumTerms (R := R) xs = sumTerms ys
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      simp [h, sumTerms_eq_of_forall₂_eq hs]

theorem sumTerms_cut_forall₂_perm [Semiring R] :
    ∀ {cs ds : List PTree.Cut}, List.Forall₂ PTree.Cut.Perm cs ds →
      sumTerms (R := R) (cs.map fun c => (c.prunedForest, c.trunkForest)) =
        sumTerms (R := R) (ds.map fun d => (d.prunedForest, d.trunkForest))
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      simp [PTree.Cut.Perm.coproductTerm_eq h, sumTerms_cut_forall₂_perm hs]

theorem sumTerms_cut_listRelPerm [Semiring R] {cs ds : List PTree.Cut}
    (h : PTree.ListRelPerm PTree.Cut.Perm cs ds) :
    sumTerms (R := R) (cs.map fun c => (c.prunedForest, c.trunkForest)) =
      sumTerms (R := R) (ds.map fun d => (d.prunedForest, d.trunkForest)) := by
  rcases h with ⟨cs', hp, hrel⟩
  rw [sumTerms_perm (R := R) (hp.map _)]
  exact sumTerms_cut_forall₂_perm hrel

theorem sumTerms_map_add_left [Semiring R]
    (x : RootedForest × RootedForest) :
    ∀ ys : List (RootedForest × RootedForest),
      sumTerms (R := R) (ys.map fun y => x + y) = ofPair x * sumTerms ys
  | [] => by
      simp [sumTerms]
  | y :: ys => by
      rw [List.map_cons, sumTerms_cons, sumTerms_cons, sumTerms_map_add_left x ys]
      rw [ofPair_add, mul_add]

theorem sumTerms_multiply [Semiring R]
    (xs ys : List (RootedForest × RootedForest)) :
    sumTerms (R := R) (PTree.multiplyCoproductTerms xs ys) =
      sumTerms xs * sumTerms ys := by
  induction xs with
  | nil =>
      simp [PTree.multiplyCoproductTerms, sumTerms]
  | cons x xs ih =>
      rw [PTree.multiplyCoproductTerms]
      rw [PTree.multiplyCoproductTerms] at ih
      simp only [List.flatMap_cons]
      rw [sumTerms_append, ih, sumTerms_cons]
      change
        sumTerms (R := R) (ys.map fun y => x + y) + sumTerms xs * sumTerms ys =
          (ofPair x + sumTerms xs) * sumTerms ys
      rw [sumTerms_map_add_left, add_mul]

private def counitLeftMonoidHom (R : Type u) [CommSemiring R] :
    Multiplicative (RootedForest × RootedForest) →* ForestAlgebra R where
  toFun term :=
    ForestAlgebra.counitCoeff (R := R) (Multiplicative.toAdd term).1 •
      ForestAlgebra.ofForest (R := R) (Multiplicative.toAdd term).2
  map_one' := by
    change ForestAlgebra.counitCoeff (R := R) 0 •
        ForestAlgebra.ofForest (R := R) 0 = 1
    simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rcases Multiplicative.toAdd x with ⟨φ₁, ψ₁⟩
    rcases Multiplicative.toAdd y with ⟨φ₂, ψ₂⟩
    change
      ForestAlgebra.counitCoeff (R := R) (φ₁ + φ₂) •
          ForestAlgebra.ofForest (R := R) (ψ₁ + ψ₂) =
        (ForestAlgebra.counitCoeff (R := R) φ₁ • ForestAlgebra.ofForest (R := R) ψ₁) *
          (ForestAlgebra.counitCoeff (R := R) φ₂ • ForestAlgebra.ofForest (R := R) ψ₂)
    rw [ForestAlgebra.counitCoeff_add, ForestAlgebra.ofForest_add]
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

private def counitRightMonoidHom (R : Type u) [CommSemiring R] :
    Multiplicative (RootedForest × RootedForest) →* ForestAlgebra R where
  toFun term :=
    ForestAlgebra.counitCoeff (R := R) (Multiplicative.toAdd term).2 •
      ForestAlgebra.ofForest (R := R) (Multiplicative.toAdd term).1
  map_one' := by
    change ForestAlgebra.counitCoeff (R := R) 0 •
        ForestAlgebra.ofForest (R := R) 0 = 1
    simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rcases Multiplicative.toAdd x with ⟨φ₁, ψ₁⟩
    rcases Multiplicative.toAdd y with ⟨φ₂, ψ₂⟩
    change
      ForestAlgebra.counitCoeff (R := R) (ψ₁ + ψ₂) •
          ForestAlgebra.ofForest (R := R) (φ₁ + φ₂) =
        (ForestAlgebra.counitCoeff (R := R) ψ₁ • ForestAlgebra.ofForest (R := R) φ₁) *
          (ForestAlgebra.counitCoeff (R := R) ψ₂ • ForestAlgebra.ofForest (R := R) φ₂)
    rw [ForestAlgebra.counitCoeff_add, ForestAlgebra.ofForest_add]
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-- Apply the counit to the left tensor factor. -/
def counitLeft [CommSemiring R] : ForestTensorAlgebra R →ₐ[R] ForestAlgebra R :=
  (AddMonoidAlgebra.lift R (ForestAlgebra R) (RootedForest × RootedForest))
    (counitLeftMonoidHom R)

/-- Apply the counit to the right tensor factor. -/
def counitRight [CommSemiring R] : ForestTensorAlgebra R →ₐ[R] ForestAlgebra R :=
  (AddMonoidAlgebra.lift R (ForestAlgebra R) (RootedForest × RootedForest))
    (counitRightMonoidHom R)

@[simp]
theorem counitLeft_ofPair [CommSemiring R] (term : RootedForest × RootedForest) :
    counitLeft (R := R) (ofPair (R := R) term) =
      ForestAlgebra.counitCoeff (R := R) term.1 • ForestAlgebra.ofForest (R := R) term.2 := by
  simp [counitLeft, ofPair, counitLeftMonoidHom]

@[simp]
theorem counitRight_ofPair [CommSemiring R] (term : RootedForest × RootedForest) :
    counitRight (R := R) (ofPair (R := R) term) =
      ForestAlgebra.counitCoeff (R := R) term.2 • ForestAlgebra.ofForest (R := R) term.1 := by
  simp [counitRight, ofPair, counitRightMonoidHom]

theorem counitLeft_sumTerms [CommSemiring R] (terms : List (RootedForest × RootedForest)) :
    counitLeft (R := R) (sumTerms (R := R) terms) =
      (terms.map fun term =>
        ForestAlgebra.counitCoeff (R := R) term.1 •
          ForestAlgebra.ofForest (R := R) term.2).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, ih]
      simp

theorem counitRight_sumTerms [CommSemiring R] (terms : List (RootedForest × RootedForest)) :
    counitRight (R := R) (sumTerms (R := R) terms) =
      (terms.map fun term =>
        ForestAlgebra.counitCoeff (R := R) term.2 •
          ForestAlgebra.ofForest (R := R) term.1).sum := by
  induction terms with
  | nil =>
      simp [sumTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, ih]
      simp

end

end ForestTensorAlgebra

/-- Triple tensor-coded forest algebra:
`(φ, ψ, η)` represents the basis tensor `φ ⊗ ψ ⊗ η`. -/
abbrev ForestTripleTensorAlgebra (R : Type u) [Semiring R] : Type u :=
  AddMonoidAlgebra R (RootedForest × RootedForest × RootedForest)

namespace ForestTripleTensorAlgebra

noncomputable section

variable {R : Type u}

/-- The basis triple tensor represented by a triple of rooted forests. -/
def ofTriple [Semiring R] (term : RootedForest × RootedForest × RootedForest) :
    ForestTripleTensorAlgebra R :=
  AddMonoidAlgebra.single term 1

/-- The basis tensor `φ ⊗ ψ ⊗ η`. -/
def ofForests [Semiring R] (φ ψ η : RootedForest) : ForestTripleTensorAlgebra R :=
  ofTriple (R := R) (φ, ψ, η)

@[simp]
theorem ofTriple_zero [Semiring R] : ofTriple (R := R) 0 = 1 := by
  simp [ofTriple, AddMonoidAlgebra.one_def]

@[simp]
theorem ofForests_zero_zero_zero [Semiring R] :
    ofForests (R := R) 0 0 0 = 1 := by
  change ofTriple (R := R) (0 : RootedForest × RootedForest × RootedForest) = 1
  simp

@[simp]
theorem ofTriple_add [Semiring R]
    (x y : RootedForest × RootedForest × RootedForest) :
    ofTriple (R := R) (x + y) = ofTriple x * ofTriple y := by
  simp [ofTriple, AddMonoidAlgebra.single_mul_single]

@[simp]
theorem ofForests_add [Semiring R]
    (φ₁ φ₂ ψ₁ ψ₂ η₁ η₂ : RootedForest) :
    ofForests (R := R) (φ₁ + φ₂) (ψ₁ + ψ₂) (η₁ + η₂) =
      ofForests φ₁ ψ₁ η₁ * ofForests φ₂ ψ₂ η₂ := by
  simp [ofForests, ofTriple, AddMonoidAlgebra.single_mul_single]

/-- Sum a finite list of basis triple tensors. Duplicates contribute multiplicity. -/
def sumTerms [Semiring R]
    (terms : List (RootedForest × RootedForest × RootedForest)) :
    ForestTripleTensorAlgebra R :=
  (terms.map (ofTriple (R := R))).sum

@[simp]
theorem sumTerms_nil [Semiring R] : sumTerms (R := R) [] = 0 :=
  rfl

@[simp]
theorem sumTerms_cons [Semiring R]
    (term : RootedForest × RootedForest × RootedForest)
    (terms : List (RootedForest × RootedForest × RootedForest)) :
    sumTerms (R := R) (term :: terms) = ofTriple term + sumTerms terms :=
  rfl

@[simp]
theorem sumTerms_singleton [Semiring R]
    (term : RootedForest × RootedForest × RootedForest) :
    sumTerms (R := R) [term] = ofTriple term := by
  simp [sumTerms]

theorem sumTerms_append [Semiring R]
    (xs ys : List (RootedForest × RootedForest × RootedForest)) :
    sumTerms (R := R) (xs ++ ys) = sumTerms xs + sumTerms ys := by
  simp [sumTerms, List.map_append]

theorem sumTerms_perm [Semiring R]
    {xs ys : List (RootedForest × RootedForest × RootedForest)}
    (h : xs.Perm ys) :
    sumTerms (R := R) xs = sumTerms ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Multiply two finite lists of triple tensor basis terms. -/
def multiplyTerms
    (xs ys : List (RootedForest × RootedForest × RootedForest)) :
    List (RootedForest × RootedForest × RootedForest) :=
  xs.flatMap fun x =>
    ys.map fun y => x + y

theorem sumTerms_map_add_left [Semiring R]
    (x : RootedForest × RootedForest × RootedForest) :
    ∀ ys : List (RootedForest × RootedForest × RootedForest),
      sumTerms (R := R) (ys.map fun y => x + y) = ofTriple x * sumTerms ys
  | [] => by
      simp [sumTerms]
  | y :: ys => by
      rw [List.map_cons, sumTerms_cons, sumTerms_cons, sumTerms_map_add_left x ys]
      rw [ofTriple_add, mul_add]

theorem sumTerms_multiply [Semiring R]
    (xs ys : List (RootedForest × RootedForest × RootedForest)) :
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

theorem multiplyTerms_append_left
    (xs ys zs : List (RootedForest × RootedForest × RootedForest)) :
    multiplyTerms (xs ++ ys) zs = multiplyTerms xs zs ++ multiplyTerms ys zs := by
  simp [multiplyTerms, List.flatMap_append]

theorem multiplyTerms_perm_left
    {xs ys zs : List (RootedForest × RootedForest × RootedForest)} (h : xs.Perm ys) :
    (multiplyTerms xs zs).Perm (multiplyTerms ys zs) := by
  rw [multiplyTerms, multiplyTerms]
  exact List.Perm.flatMap h (fun _ _ => List.Perm.refl _)

theorem multiplyTerms_perm_right
    {xs ys zs : List (RootedForest × RootedForest × RootedForest)} (h : ys.Perm zs) :
    (multiplyTerms xs ys).Perm (multiplyTerms xs zs) := by
  rw [multiplyTerms, multiplyTerms]
  exact List.Perm.flatMap (List.Perm.refl xs)
    (fun x _ => List.Perm.map (fun y => x + y) h)

theorem multiplyTerms_perm
    {xs xs' ys ys' : List (RootedForest × RootedForest × RootedForest)}
    (hxs : xs.Perm xs') (hys : ys.Perm ys') :
    (multiplyTerms xs ys).Perm (multiplyTerms xs' ys') :=
  (multiplyTerms_perm_left (zs := ys) hxs).trans
    (multiplyTerms_perm_right (xs := xs') hys)

private theorem flatMap_append_fun_perm {α β : Type*} (xs : List α) (f g : α → List β) :
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

theorem flatMap_multiplyTerms_right_perm {α : Type*}
    (xs : List (RootedForest × RootedForest × RootedForest)) (ys : List α)
    (f : α → List (RootedForest × RootedForest × RootedForest)) :
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

private def includeLeftPairMonoidHom (R : Type u) [CommSemiring R] :
    Multiplicative (RootedForest × RootedForest) →* ForestTripleTensorAlgebra R where
  toFun term :=
    ofTriple (R := R)
      ((Multiplicative.toAdd term).1, (Multiplicative.toAdd term).2, 0)
  map_one' := by
    change ofTriple (R := R) (0 : RootedForest × RootedForest × RootedForest) = 1
    simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rcases Multiplicative.toAdd x with ⟨φ₁, ψ₁⟩
    rcases Multiplicative.toAdd y with ⟨φ₂, ψ₂⟩
    simpa using
      (ofTriple_add (R := R) (φ₁, ψ₁, 0) (φ₂, ψ₂, 0))

/-- Embed a pair tensor as the first two factors of a triple tensor. -/
def includeLeftPair [CommSemiring R] : ForestTensorAlgebra R →ₐ[R]
    ForestTripleTensorAlgebra R :=
  (AddMonoidAlgebra.lift R (ForestTripleTensorAlgebra R) (RootedForest × RootedForest))
    (includeLeftPairMonoidHom R)

@[simp]
theorem includeLeftPair_ofPair [CommSemiring R] (term : RootedForest × RootedForest) :
    includeLeftPair (R := R) (ForestTensorAlgebra.ofPair (R := R) term) =
      ofTriple (R := R) (term.1, term.2, 0) := by
  simp [includeLeftPair, ForestTensorAlgebra.ofPair, includeLeftPairMonoidHom]

@[simp]
theorem includeLeftPair_ofForests [CommSemiring R] (φ ψ : RootedForest) :
    includeLeftPair (R := R) (ForestTensorAlgebra.ofForests (R := R) φ ψ) =
      ofForests (R := R) φ ψ 0 := by
  simp [ForestTensorAlgebra.ofForests, ofForests]

private def includeRightPairMonoidHom (R : Type u) [CommSemiring R] :
    Multiplicative (RootedForest × RootedForest) →* ForestTripleTensorAlgebra R where
  toFun term :=
    ofTriple (R := R)
      (0, (Multiplicative.toAdd term).1, (Multiplicative.toAdd term).2)
  map_one' := by
    change ofTriple (R := R) (0 : RootedForest × RootedForest × RootedForest) = 1
    simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rcases Multiplicative.toAdd x with ⟨φ₁, ψ₁⟩
    rcases Multiplicative.toAdd y with ⟨φ₂, ψ₂⟩
    simpa using
      (ofTriple_add (R := R) (0, φ₁, ψ₁) (0, φ₂, ψ₂))

/-- Embed a pair tensor as the last two factors of a triple tensor. -/
def includeRightPair [CommSemiring R] : ForestTensorAlgebra R →ₐ[R]
    ForestTripleTensorAlgebra R :=
  (AddMonoidAlgebra.lift R (ForestTripleTensorAlgebra R) (RootedForest × RootedForest))
    (includeRightPairMonoidHom R)

@[simp]
theorem includeRightPair_ofPair [CommSemiring R] (term : RootedForest × RootedForest) :
    includeRightPair (R := R) (ForestTensorAlgebra.ofPair (R := R) term) =
      ofTriple (R := R) (0, term.1, term.2) := by
  simp [includeRightPair, ForestTensorAlgebra.ofPair, includeRightPairMonoidHom]

@[simp]
theorem includeRightPair_ofForests [CommSemiring R] (φ ψ : RootedForest) :
    includeRightPair (R := R) (ForestTensorAlgebra.ofForests (R := R) φ ψ) =
      ofForests (R := R) 0 φ ψ := by
  simp [ForestTensorAlgebra.ofForests, ofForests]

end

end ForestTripleTensorAlgebra

namespace PTree

noncomputable section

variable {R : Type u}

/-- The planar BCK coproduct of a tree, represented in the tensor-coded algebra. -/
def coproduct [Semiring R] (t : PTree) : ForestTensorAlgebra R :=
  ForestTensorAlgebra.sumTerms (R := R) (coproductTerms t)

/-- The reduced planar BCK coproduct, summing only proper cut terms. -/
def reducedCoproduct [Semiring R] (t : PTree) : ForestTensorAlgebra R :=
  ForestTensorAlgebra.sumTerms (R := R) (properCoproductTerms t)

@[simp]
theorem reducedCoproduct_bullet [Semiring R] :
    reducedCoproduct (R := R) PTree.bullet = 0 := by
  simp [reducedCoproduct, properCoproductTerms, coproductTerms, cuts,
    PTree.Cut.prunedForest, PTree.Cut.trunkForest, ForestTensorAlgebra.sumTerms]

theorem reducedCoproduct_perm [Semiring R] {t u : PTree} (h : PTree.Perm t u) :
    reducedCoproduct (R := R) t = reducedCoproduct (R := R) u := by
  rw [reducedCoproduct, reducedCoproduct]
  exact ForestTensorAlgebra.sumTerms_perm (R := R) (PTree.properCoproductTerms_perm h)

theorem coproduct_eq_of_cuts_listRelPerm [Semiring R] {t u : PTree}
    (h : ListRelPerm Cut.Perm (cuts t) (cuts u)) :
    coproduct (R := R) t = coproduct (R := R) u := by
  rw [coproduct, coproduct, coproductTerms, coproductTerms]
  exact ForestTensorAlgebra.sumTerms_cut_listRelPerm h

theorem coproduct_perm [Semiring R] {t u : PTree} (h : PTree.Perm t u) :
    coproduct (R := R) t = coproduct (R := R) u :=
  coproduct_eq_of_cuts_listRelPerm (cuts_listRelPerm_of_perm h)

theorem coproduct_node [Semiring R] (ts : List PTree) :
    coproduct (R := R) (.node ts) =
      ForestTensorAlgebra.sumTerms (R := R)
        ((coproductTermsList ts).map fun term =>
          (term.1, RootedForest.singleton (RootedForest.graft term.2))) +
        ForestTensorAlgebra.ofPair (R := R)
          (RootedForest.singleton (RootedTree.ofPTree (.node ts)), 0) := by
  rw [coproduct]
  rw [ForestTensorAlgebra.sumTerms_perm (R := R) (PTree.coproductTerms_node_perm ts)]
  rw [ForestTensorAlgebra.sumTerms_append]
  simp

/-- Multiplicative extension of the planar coproduct to planar forests. -/
def coproductList [Semiring R] (ts : List PTree) : ForestTensorAlgebra R :=
  ForestTensorAlgebra.sumTerms (R := R) (coproductTermsList ts)

/-- The reduced planar BCK coproduct of a planar forest. -/
def reducedCoproductList [Semiring R] (ts : List PTree) : ForestTensorAlgebra R :=
  ForestTensorAlgebra.sumTerms (R := R) (properCoproductTermsList ts)

@[simp]
theorem reducedCoproductList_nil [Semiring R] :
    reducedCoproductList (R := R) [] = 0 := by
  simp [reducedCoproductList, properCoproductTermsList, coproductTermsList,
    ForestTensorAlgebra.sumTerms]

theorem reducedCoproductList_forall₂_perm [Semiring R]
    {ts us : List PTree} (h : List.Forall₂ PTree.Perm ts us) :
    reducedCoproductList (R := R) ts = reducedCoproductList us := by
  rw [reducedCoproductList, reducedCoproductList]
  exact ForestTensorAlgebra.sumTerms_perm (R := R)
    (PTree.properCoproductTermsList_forall₂_perm h)

@[simp]
theorem coproductList_nil [Semiring R] : coproductList (R := R) [] = 1 := by
  change ForestTensorAlgebra.sumTerms (R := R) [(0 : RootedForest × RootedForest)] = 1
  simp

@[simp]
theorem coproductList_cons [Semiring R] (t : PTree) (ts : List PTree) :
    coproductList (R := R) (t :: ts) = coproduct t * coproductList ts := by
  simp [
    coproductList,
    coproduct,
    coproductTermsList,
    ForestTensorAlgebra.sumTerms_multiply
  ]

@[simp]
theorem coproductList_singleton [Semiring R] (t : PTree) :
    coproductList (R := R) [t] = coproduct t := by
  simp

theorem coproductList_forall₂_perm [Semiring R] :
    ∀ {ts us : List PTree}, List.Forall₂ PTree.Perm ts us →
      coproductList (R := R) ts = coproductList (R := R) us
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
      rw [coproductList_cons, coproductList_cons, coproduct_perm h,
        coproductList_forall₂_perm hs]

theorem coproductList_append [Semiring R] (ts us : List PTree) :
    coproductList (R := R) (ts ++ us) = coproductList ts * coproductList us := by
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      simp [ih, mul_assoc]

theorem coproductList_perm [CommSemiring R] {ts us : List PTree} (h : ts.Perm us) :
    coproductList (R := R) ts = coproductList us := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ =>
      simp
      ac_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem counitLeft_rootCutTerms [CommSemiring R] :
    ∀ cuts : List RootCut,
      (cuts.map fun c =>
          ForestAlgebra.counitCoeff (R := R)
              (c.pruned.map RootedTree.ofPTree : RootedForest) •
            ForestAlgebra.ofForest (R := R)
              (RootedForest.singleton (RootedTree.ofPTree c.trunk))).sum =
        ((cuts.filterMap RootCut.noPrunedTrunk?).map fun trunk =>
          ForestAlgebra.ofForest (R := R)
            (RootedForest.singleton (RootedTree.ofPTree trunk))).sum
  | [] => by
      simp
  | c :: cuts => by
      cases hpruned : c.pruned with
      | nil =>
          simp [RootCut.noPrunedTrunk?, hpruned, counitLeft_rootCutTerms cuts]
      | cons p ps =>
          have hne :
              (((RootedTree.ofPTree p :: ps.map RootedTree.ofPTree) : List RootedTree) :
                RootedForest) ≠ 0 := by
            exact (RootedForest.order_pos_iff_ne_zero _).1
              (RootedForest.order_coe_cons_pos (RootedTree.ofPTree p)
                (ps.map RootedTree.ofPTree))
          simp [RootCut.noPrunedTrunk?, hpruned, counitLeft_rootCutTerms cuts,
            ForestAlgebra.counitCoeff_ne_zero hne]

private theorem counitRight_rootCutTerms [CommSemiring R] :
    ∀ cuts : List RootCut,
      (cuts.map fun c =>
          ForestAlgebra.counitCoeff (R := R)
              (RootedForest.singleton (RootedTree.ofPTree c.trunk)) •
            ForestAlgebra.ofForest (R := R)
              (c.pruned.map RootedTree.ofPTree : RootedForest)).sum = 0
  | [] => by
      simp
  | c :: cuts => by
      have hne :
          RootedForest.singleton (RootedTree.ofPTree c.trunk) ≠ 0 :=
        RootedForest.singleton_ne_zero (RootedTree.ofPTree c.trunk)
      simp [counitRight_rootCutTerms cuts, ForestAlgebra.counitCoeff_ne_zero hne]

theorem counitLeft_coproduct [CommSemiring R] (t : PTree) :
    ForestTensorAlgebra.counitLeft (R := R) (coproduct (R := R) t) =
      ForestAlgebra.ofForest (R := R)
        (RootedForest.singleton (RootedTree.ofPTree t)) := by
  rw [coproduct, ForestTensorAlgebra.counitLeft_sumTerms, coproductTerms, cuts]
  simp only [List.map_append, List.map_map, List.sum_append]
  change
    ((rootCuts t).map
          (fun c =>
            ForestAlgebra.counitCoeff (R := R)
                (c.pruned.map RootedTree.ofPTree : RootedForest) •
              ForestAlgebra.ofForest (R := R)
                (RootedForest.singleton (RootedTree.ofPTree c.trunk)))).sum +
        (List.map
            (fun c : Cut =>
              ForestAlgebra.counitCoeff (R := R) c.prunedForest •
                ForestAlgebra.ofForest (R := R) c.trunkForest)
            ([{ pruned := [t], trunk? := none }] : List Cut)).sum =
      ForestAlgebra.ofForest (R := R)
        (RootedForest.singleton (RootedTree.ofPTree t))
  rw [counitLeft_rootCutTerms, rootCuts_noPrunedTrunks]
  have hne :
      RootedForest.singleton (RootedTree.ofPTree t) ≠ 0 :=
    RootedForest.singleton_ne_zero (RootedTree.ofPTree t)
  have hne' : ({RootedTree.ofPTree t} : RootedForest) ≠ 0 := by
    exact hne
  simp [Cut.prunedForest, Cut.trunkForest, RootedForest.singleton]
  rw [ForestAlgebra.counitCoeff_ne_zero hne']
  simp

theorem counitRight_coproduct [CommSemiring R] (t : PTree) :
    ForestTensorAlgebra.counitRight (R := R) (coproduct (R := R) t) =
      ForestAlgebra.ofForest (R := R)
        (RootedForest.singleton (RootedTree.ofPTree t)) := by
  rw [coproduct, ForestTensorAlgebra.counitRight_sumTerms, coproductTerms, cuts]
  simp only [List.map_append, List.map_map, List.sum_append]
  change
    ((rootCuts t).map
          (fun c =>
            ForestAlgebra.counitCoeff (R := R)
                (RootedForest.singleton (RootedTree.ofPTree c.trunk)) •
              ForestAlgebra.ofForest (R := R)
                (c.pruned.map RootedTree.ofPTree : RootedForest))).sum +
        (List.map
            (fun c : Cut =>
              ForestAlgebra.counitCoeff (R := R) c.trunkForest •
                ForestAlgebra.ofForest (R := R) c.prunedForest)
            ([{ pruned := [t], trunk? := none }] : List Cut)).sum =
      ForestAlgebra.ofForest (R := R)
        (RootedForest.singleton (RootedTree.ofPTree t))
  rw [counitRight_rootCutTerms]
  simp [Cut.prunedForest, Cut.trunkForest, RootedForest.singleton]

end

end PTree

namespace RootedTree

noncomputable section

variable {R : Type u}

/-- The BCK coproduct of a non-planar rooted tree. -/
def coproduct [Semiring R] (τ : RootedTree) : ForestTensorAlgebra R :=
  Quotient.lift (PTree.coproduct (R := R))
    (fun _ _ h => PTree.coproduct_perm (R := R) h) τ

@[simp]
theorem coproduct_ofPTree [Semiring R] (t : PTree) :
    coproduct (R := R) (RootedTree.ofPTree t) = PTree.coproduct (R := R) t :=
  rfl

theorem coproduct_out [Semiring R] (τ : RootedTree) :
    coproduct (R := R) τ = PTree.coproduct (R := R) (Quotient.out τ) := by
  refine Quotient.inductionOn τ ?_
  intro t
  exact (PTree.coproduct_perm (R := R) (RootedTree.out_perm_ofPTree t)).symm

theorem coproduct_graft_coe [Semiring R] (ts : List RootedTree) :
    coproduct (R := R) (RootedForest.graft (ts : RootedForest)) =
      ForestTensorAlgebra.sumTerms (R := R)
        ((PTree.coproductTermsList (ts.map Quotient.out)).map fun term =>
          (term.1, RootedForest.singleton (RootedForest.graft term.2))) +
        ForestTensorAlgebra.ofPair (R := R)
          (RootedForest.singleton (RootedForest.graft (ts : RootedForest)), 0) := by
  rw [RootedForest.graft_coe, coproduct_ofPTree, PTree.coproduct_node]

/-- The reduced BCK coproduct of a non-planar rooted tree. -/
def reducedCoproduct [Semiring R] (τ : RootedTree) : ForestTensorAlgebra R :=
  Quotient.lift (PTree.reducedCoproduct (R := R))
    (fun _ _ h => PTree.reducedCoproduct_perm (R := R) h) τ

@[simp]
theorem reducedCoproduct_ofPTree [Semiring R] (t : PTree) :
    reducedCoproduct (R := R) (RootedTree.ofPTree t) =
      PTree.reducedCoproduct (R := R) t :=
  rfl

theorem reducedCoproduct_out [Semiring R] (τ : RootedTree) :
    reducedCoproduct (R := R) τ =
      PTree.reducedCoproduct (R := R) (Quotient.out τ) := by
  refine Quotient.inductionOn τ ?_
  intro t
  exact (PTree.reducedCoproduct_perm (R := R) (RootedTree.out_perm_ofPTree t)).symm

@[simp]
theorem reducedCoproduct_bullet [Semiring R] :
    reducedCoproduct (R := R) RootedTree.bullet = 0 := by
  rw [RootedTree.bullet, reducedCoproduct_ofPTree, PTree.reducedCoproduct_bullet]

end

end RootedTree

namespace RootedForest

noncomputable section

variable {R : Type u}

private theorem order_out (τ : RootedTree) :
    PTree.order (Quotient.out τ) = RootedTree.order τ := by
  rw [← RootedTree.order_ofPTree (Quotient.out τ)]
  rw [show RootedTree.ofPTree (Quotient.out τ) = τ from Quotient.out_eq τ]

private theorem orderList_out :
    ∀ ts : List RootedTree,
      PTree.orderList (ts.map Quotient.out) = RootedForest.order (ts : RootedForest)
  | [] => rfl
  | τ :: ts => by
      simp [RootedForest.order, order_out τ, orderList_out ts]

theorem coproductTermsList_out_order
    {ts : List RootedTree} {term : RootedForest × RootedForest}
    (hterm : term ∈ PTree.coproductTermsList (ts.map Quotient.out)) :
    RootedForest.order term.1 + RootedForest.order term.2 =
      RootedForest.order (ts : RootedForest) := by
  rw [← orderList_out ts]
  exact PTree.coproductTermsList_order hterm

/-- A finite representative list for the forest coproduct, using `Quotient.out`. -/
def coproductTerms (φ : RootedForest) : List (RootedForest × RootedForest) :=
  PTree.coproductTermsList ((Quotient.out φ).map Quotient.out)

theorem coproductTerms_order {φ : RootedForest} {term : RootedForest × RootedForest}
    (hterm : term ∈ coproductTerms φ) :
    RootedForest.order term.1 + RootedForest.order term.2 = RootedForest.order φ := by
  conv_rhs =>
    rw [(show ((Quotient.out φ : List RootedTree) : RootedForest) = φ from
      Quotient.out_eq φ).symm]
  exact coproductTermsList_out_order (ts := Quotient.out φ) hterm

private theorem out_map_out_ofPTree_coe (φ : RootedForest) :
    ((((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree : List RootedTree) :
        RootedForest) = φ := by
  have hmap :
      (((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree) =
        (Quotient.out φ : List RootedTree) := by
    induction Quotient.out φ with
    | nil => rfl
    | cons τ ts ih =>
        simp [RootedTree.ofPTree_out τ, ih]
  calc
    ((((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree : List RootedTree) :
        RootedForest) = ((Quotient.out φ : List RootedTree) : RootedForest) := by
          rw [hmap]
    _ = φ := Quotient.out_eq φ

/-- The only forest coproduct terms with empty left factor are `1 ⊗ φ`. -/
theorem coproductTerms_left_eq_zero {φ : RootedForest}
    {term : RootedForest × RootedForest} (hterm : term ∈ coproductTerms φ)
    (hleft : term.1 = 0) :
    term.2 = φ := by
  rw [coproductTerms] at hterm
  calc
    term.2 =
        ((((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree : List RootedTree) :
          RootedForest) := by
      exact PTree.coproductTermsList_left_eq_zero hterm hleft
    _ = φ := out_map_out_ofPTree_coe φ

/-- The only forest coproduct terms with empty right factor are `φ ⊗ 1`. -/
theorem coproductTerms_right_eq_zero {φ : RootedForest}
    {term : RootedForest × RootedForest} (hterm : term ∈ coproductTerms φ)
    (hright : term.2 = 0) :
    term.1 = φ := by
  rw [coproductTerms] at hterm
  calc
    term.1 =
        ((((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree : List RootedTree) :
          RootedForest) := by
      exact PTree.coproductTermsList_right_eq_zero hterm hright
    _ = φ := out_map_out_ofPTree_coe φ

/-- The forest coproduct has exactly one term with empty left factor. -/
theorem coproductTerms_leftBoundaryCoproductTerm (φ : RootedForest) :
    (coproductTerms φ).filterMap PTree.leftBoundaryCoproductTerm? =
      [((0 : RootedForest), φ)] := by
  rw [coproductTerms]
  calc
    (PTree.coproductTermsList ((Quotient.out φ).map Quotient.out)).filterMap
        PTree.leftBoundaryCoproductTerm? =
      [((0 : RootedForest),
        ((((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree :
          List RootedTree) : RootedForest))] :=
        PTree.coproductTermsList_leftBoundaryCoproductTerm
          ((Quotient.out φ).map Quotient.out)
    _ = [((0 : RootedForest), φ)] := by
      rw [out_map_out_ofPTree_coe φ]

/-- The forest coproduct has exactly one term with empty right factor. -/
theorem coproductTerms_rightBoundaryCoproductTerm (φ : RootedForest) :
    (coproductTerms φ).filterMap PTree.rightBoundaryCoproductTerm? =
      [(φ, (0 : RootedForest))] := by
  rw [coproductTerms]
  calc
    (PTree.coproductTermsList ((Quotient.out φ).map Quotient.out)).filterMap
        PTree.rightBoundaryCoproductTerm? =
      [(((((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree :
          List RootedTree) : RootedForest), (0 : RootedForest))] :=
        PTree.coproductTermsList_rightBoundaryCoproductTerm
          ((Quotient.out φ).map Quotient.out)
    _ = [(φ, (0 : RootedForest))] := by
      rw [out_map_out_ofPTree_coe φ]

theorem coproductTerms_ofPTree_list_perm (ts : List PTree) :
    (coproductTerms ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest)).Perm
      (PTree.coproductTermsList ts) := by
  rw [coproductTerms]
  apply PTree.coproductTermsList_forestPerm
  let φ : RootedForest := ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest)
  change PTree.ForestPerm ((Quotient.out φ).map Quotient.out) ts
  dsimp [PTree.ForestPerm]
  have hmap :
      (((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree) =
        (Quotient.out φ : List RootedTree) := by
    induction Quotient.out φ with
    | nil => rfl
    | cons τ ts ih =>
        simp [RootedTree.ofPTree_out τ, ih]
  calc
    ((((Quotient.out φ).map Quotient.out).map RootedTree.ofPTree : List RootedTree) :
        RootedForest) = ((Quotient.out φ : List RootedTree) : RootedForest) := by
          rw [hmap]
    _ = ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) :=
        Quotient.out_eq φ

theorem coproductTerms_singleton_ofPTree_perm (t : PTree) :
    (coproductTerms (RootedForest.singleton (RootedTree.ofPTree t))).Perm
      (PTree.coproductTerms t) := by
  have hsingleton :
      (PTree.coproductTermsList [t]).Perm (PTree.coproductTerms t) := by
    simp [PTree.coproductTermsList, PTree.multiplyCoproductTerms]
  simpa [RootedForest.singleton] using
    (coproductTerms_ofPTree_list_perm [t]).trans hsingleton

theorem coproductTerms_singleton_graft_perm (φ : RootedForest) :
    (coproductTerms (RootedForest.singleton (RootedForest.graft φ))).Perm
      (((coproductTerms φ).map fun term =>
          (term.1, RootedForest.singleton (RootedForest.graft term.2))) ++
        [(RootedForest.singleton (RootedForest.graft φ), 0)]) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  have hts :
      ((((ts.map Quotient.out).map RootedTree.ofPTree : List RootedTree) : RootedForest) =
        (ts : RootedForest)) := by
    have hmap : (ts.map Quotient.out).map RootedTree.ofPTree = ts := by
      induction ts with
      | nil => rfl
      | cons τ ts ih =>
          simp [RootedTree.ofPTree_out τ, ih]
    rw [hmap]
  have hforest :
      (coproductTerms (ts : RootedForest)).Perm
        (PTree.coproductTermsList (ts.map Quotient.out)) := by
    have h := coproductTerms_ofPTree_list_perm (ts.map Quotient.out)
    rw [hts] at h
    exact h
  have hnode :
      (coproductTerms (RootedForest.singleton
          (RootedTree.ofPTree (PTree.node (ts.map Quotient.out))))).Perm
        (((PTree.coproductTermsList (ts.map Quotient.out)).map fun term =>
            (term.1, RootedForest.singleton (RootedForest.graft term.2))) ++
          [(RootedForest.singleton
              (RootedTree.ofPTree (PTree.node (ts.map Quotient.out))), 0)]) :=
    (coproductTerms_singleton_ofPTree_perm (PTree.node (ts.map Quotient.out))).trans
      (PTree.coproductTerms_node_perm (ts.map Quotient.out))
  simpa [RootedForest.graft_coe] using
    hnode.trans ((hforest.symm.map fun term =>
      (term.1, RootedForest.singleton (RootedForest.graft term.2))).append_right _)

theorem coproductTerms_add_perm (φ ψ : RootedForest) :
    (coproductTerms (φ + ψ)).Perm
      (PTree.multiplyCoproductTerms (coproductTerms φ) (coproductTerms ψ)) := by
  let ts := (Quotient.out φ).map Quotient.out
  let us := (Quotient.out ψ).map Quotient.out
  have hφ :
      ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) = φ := by
    simpa [ts] using out_map_out_ofPTree_coe φ
  have hψ :
      ((us.map RootedTree.ofPTree : List RootedTree) : RootedForest) = ψ := by
    simpa [us] using out_map_out_ofPTree_coe ψ
  have hsum :
      (((ts ++ us).map RootedTree.ofPTree : List RootedTree) : RootedForest) =
        φ + ψ := by
    rw [List.map_append]
    change
      ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) +
          ((us.map RootedTree.ofPTree : List RootedTree) : RootedForest) =
        φ + ψ
    rw [hφ, hψ]
  have hleft :
      (coproductTerms (φ + ψ)).Perm (PTree.coproductTermsList (ts ++ us)) := by
    rw [← hsum]
    exact coproductTerms_ofPTree_list_perm (ts ++ us)
  have hφterms : (PTree.coproductTermsList ts).Perm (coproductTerms φ) := by
    rw [← hφ]
    exact (coproductTerms_ofPTree_list_perm ts).symm
  have hψterms : (PTree.coproductTermsList us).Perm (coproductTerms ψ) := by
    rw [← hψ]
    exact (coproductTerms_ofPTree_list_perm us).symm
  exact hleft.trans
    ((PTree.coproductTermsList_append_perm ts us).trans
      (PTree.multiplyCoproductTerms_perm hφterms hψterms))

/-- A finite representative list for the reduced forest coproduct. -/
def properCoproductTerms (φ : RootedForest) : List (RootedForest × RootedForest) :=
  (coproductTerms φ).filter fun term =>
    0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2

theorem properCoproductTerms_mem_coproductTerms {φ : RootedForest}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTerms φ) :
    term ∈ coproductTerms φ :=
  (List.mem_filter.1 hterm).1

theorem properCoproductTerms_order {φ : RootedForest}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTerms φ) :
    RootedForest.order term.1 + RootedForest.order term.2 = RootedForest.order φ :=
  coproductTerms_order (properCoproductTerms_mem_coproductTerms hterm)

theorem properCoproductTerms_left_order_lt {φ : RootedForest}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTerms φ) :
    RootedForest.order term.1 < RootedForest.order φ := by
  have hproper :
      0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hright_pos : 0 < RootedForest.order term.2 := hproper.2
  have horder := properCoproductTerms_order hterm
  omega

theorem properCoproductTerms_right_order_lt {φ : RootedForest}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTerms φ) :
    RootedForest.order term.2 < RootedForest.order φ := by
  have hproper :
      0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hleft_pos : 0 < RootedForest.order term.1 := hproper.1
  have horder := properCoproductTerms_order hterm
  omega

/-- The multiplicative coproduct of a non-planar rooted forest. -/
def coproduct [CommSemiring R] (φ : RootedForest) : ForestTensorAlgebra R :=
  Quotient.lift
    (fun ts : List RootedTree => PTree.coproductList (R := R) (ts.map Quotient.out))
    (fun (ts us : List RootedTree) (h : ts.Perm us) =>
      PTree.coproductList_perm (R := R) (List.Perm.map Quotient.out h))
    φ

@[simp]
theorem coproduct_coe [CommSemiring R] (ts : List RootedTree) :
    coproduct (R := R) (ts : RootedForest) =
      PTree.coproductList (R := R) (ts.map Quotient.out) :=
  rfl

theorem coproduct_ofPTree_list [CommSemiring R] (ts : List PTree) :
    coproduct (R := R) ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) =
      PTree.coproductList (R := R) ts := by
  change
    PTree.coproductList (R := R) ((ts.map RootedTree.ofPTree).map Quotient.out) =
      PTree.coproductList (R := R) ts
  exact PTree.coproductList_forall₂_perm (R := R) (by
    induction ts with
    | nil => exact List.Forall₂.nil
    | cons t ts ih =>
        exact List.Forall₂.cons (RootedTree.out_perm_ofPTree t) ih)

theorem coproduct_eq_sumTerms_coproductTerms [CommSemiring R] (φ : RootedForest) :
    coproduct (R := R) φ =
      ForestTensorAlgebra.sumTerms (R := R) (coproductTerms φ) := by
  change
    coproduct (R := R) φ =
      PTree.coproductList (R := R) ((Quotient.out φ).map Quotient.out)
  conv_lhs =>
    rw [(show ((Quotient.out φ : List RootedTree) : RootedForest) = φ from
      Quotient.out_eq φ).symm]
  rfl

/-- The reduced BCK coproduct of a non-planar rooted forest. -/
def reducedCoproduct [Semiring R] (φ : RootedForest) : ForestTensorAlgebra R :=
  ForestTensorAlgebra.sumTerms (R := R) (properCoproductTerms φ)

@[simp]
theorem reducedCoproduct_zero [Semiring R] :
    reducedCoproduct (R := R) (0 : RootedForest) = 0 := by
  cases hterms : properCoproductTerms (0 : RootedForest) with
  | nil =>
      simp [reducedCoproduct, hterms]
  | cons term terms =>
      have hmem : term ∈ properCoproductTerms (0 : RootedForest) := by
        rw [hterms]
        simp
      have hproper :
          0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2 :=
        of_decide_eq_true (List.mem_filter.1 hmem).2
      have horder := properCoproductTerms_order hmem
      rw [RootedForest.order_zero] at horder
      omega

@[simp]
theorem reducedCoproduct_empty [Semiring R] :
    reducedCoproduct (R := R) RootedForest.empty = 0 := by
  simp [RootedForest.empty]

@[simp]
theorem coproduct_zero [CommSemiring R] :
    coproduct (R := R) (0 : RootedForest) = 1 := by
  change PTree.coproductList (R := R) (([] : List RootedTree).map Quotient.out) = 1
  simp

@[simp]
theorem coproduct_empty [CommSemiring R] :
    coproduct (R := R) RootedForest.empty = 1 := by
  simp [RootedForest.empty]

@[simp]
theorem coproduct_singleton [CommSemiring R] (τ : RootedTree) :
    coproduct (R := R) (RootedForest.singleton τ) =
      PTree.coproduct (R := R) (Quotient.out τ) := by
  change PTree.coproductList (R := R) ([τ].map Quotient.out) =
    PTree.coproduct (R := R) (Quotient.out τ)
  simp

theorem coproduct_singleton_tree [CommSemiring R] (τ : RootedTree) :
    coproduct (R := R) (RootedForest.singleton τ) =
      RootedTree.coproduct (R := R) τ := by
  rw [coproduct_singleton, RootedTree.coproduct_out]

theorem coproduct_singleton_ofPTree [CommSemiring R] (t : PTree) :
    coproduct (R := R) (RootedForest.singleton (RootedTree.ofPTree t)) =
      PTree.coproduct (R := R) t := by
  rw [coproduct_singleton]
  exact PTree.coproduct_perm (RootedTree.out_perm_ofPTree t)

@[simp]
theorem coproduct_add [CommSemiring R] (φ ψ : RootedForest) :
    coproduct (R := R) (φ + ψ) = coproduct φ * coproduct ψ := by
  refine Quotient.inductionOn₂ φ ψ ?_
  intro ts us
  change
    PTree.coproductList (R := R) ((ts ++ us).map Quotient.out) =
      PTree.coproductList (R := R) (ts.map Quotient.out) *
        PTree.coproductList (R := R) (us.map Quotient.out)
  rw [List.map_append, PTree.coproductList_append]

theorem counitLeft_coproduct [CommSemiring R] (φ : RootedForest) :
    ForestTensorAlgebra.counitLeft (R := R) (coproduct (R := R) φ) =
      ForestAlgebra.ofForest (R := R) φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp
  | cons τ ts ih =>
      change
        ForestTensorAlgebra.counitLeft (R := R)
            (PTree.coproductList (R := R) ((τ :: ts).map Quotient.out)) =
          ForestAlgebra.ofForest (R := R) (((τ :: ts) : List RootedTree) : RootedForest)
      simp only [List.map_cons, PTree.coproductList_cons, map_mul]
      rw [PTree.counitLeft_coproduct]
      have ih' :
          ForestTensorAlgebra.counitLeft (R := R)
              (PTree.coproductList (R := R) (ts.map Quotient.out)) =
            ForestAlgebra.ofForest (R := R) (ts : RootedForest) := by
        simpa using ih
      rw [ih']
      rw [show RootedTree.ofPTree (Quotient.out τ) = τ from Quotient.out_eq τ]
      rw [← ForestAlgebra.ofForest_add]
      simp [RootedForest.singleton]

theorem counitRight_coproduct [CommSemiring R] (φ : RootedForest) :
    ForestTensorAlgebra.counitRight (R := R) (coproduct (R := R) φ) =
      ForestAlgebra.ofForest (R := R) φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp
  | cons τ ts ih =>
      change
        ForestTensorAlgebra.counitRight (R := R)
            (PTree.coproductList (R := R) ((τ :: ts).map Quotient.out)) =
          ForestAlgebra.ofForest (R := R) (((τ :: ts) : List RootedTree) : RootedForest)
      simp only [List.map_cons, PTree.coproductList_cons, map_mul]
      rw [PTree.counitRight_coproduct]
      have ih' :
          ForestTensorAlgebra.counitRight (R := R)
              (PTree.coproductList (R := R) (ts.map Quotient.out)) =
            ForestAlgebra.ofForest (R := R) (ts : RootedForest) := by
        simpa using ih
      rw [ih']
      rw [show RootedTree.ofPTree (Quotient.out τ) = τ from Quotient.out_eq τ]
      rw [← ForestAlgebra.ofForest_add]
      simp [RootedForest.singleton]

end

end RootedForest

namespace ForestTripleTensorAlgebra

noncomputable section

variable {R : Type u} [CommSemiring R]

private def coproductLeftMonoidHom (R : Type u) [CommSemiring R] :
    Multiplicative (RootedForest × RootedForest) →* ForestTripleTensorAlgebra R where
  toFun term :=
    let term := Multiplicative.toAdd term
    includeLeftPair (R := R) (RootedForest.coproduct (R := R) term.1) *
      ofForests (R := R) 0 0 term.2
  map_one' := by
    simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rcases Multiplicative.toAdd x with ⟨φ₁, ψ₁⟩
    rcases Multiplicative.toAdd y with ⟨φ₂, ψ₂⟩
    change
      includeLeftPair (R := R) (RootedForest.coproduct (R := R) (φ₁ + φ₂)) *
          ofForests (R := R) 0 0 (ψ₁ + ψ₂) =
        includeLeftPair (R := R) (RootedForest.coproduct (R := R) φ₁) *
            ofForests (R := R) 0 0 ψ₁ *
          (includeLeftPair (R := R) (RootedForest.coproduct (R := R) φ₂) *
            ofForests (R := R) 0 0 ψ₂)
    rw [RootedForest.coproduct_add, map_mul]
    have hψ :
        ofForests (R := R) 0 0 (ψ₁ + ψ₂) =
          ofForests (R := R) 0 0 ψ₁ * ofForests (R := R) 0 0 ψ₂ := by
      simpa using
        (ofForests_add (R := R) (0 : RootedForest) 0 0 0 ψ₁ ψ₂)
    rw [hψ]
    ac_rfl

/-- Apply the coproduct to the first tensor factor, the map `Δ ⊗ id`. -/
def coproductLeft : ForestTensorAlgebra R →ₐ[R] ForestTripleTensorAlgebra R :=
  (AddMonoidAlgebra.lift R (ForestTripleTensorAlgebra R) (RootedForest × RootedForest))
    (coproductLeftMonoidHom R)

@[simp]
theorem coproductLeft_ofPair (term : RootedForest × RootedForest) :
    coproductLeft (R := R) (ForestTensorAlgebra.ofPair (R := R) term) =
      includeLeftPair (R := R) (RootedForest.coproduct (R := R) term.1) *
        ofForests (R := R) 0 0 term.2 := by
  simp [coproductLeft, ForestTensorAlgebra.ofPair, coproductLeftMonoidHom]

@[simp]
theorem coproductLeft_ofForests (φ ψ : RootedForest) :
    coproductLeft (R := R) (ForestTensorAlgebra.ofForests (R := R) φ ψ) =
      includeLeftPair (R := R) (RootedForest.coproduct (R := R) φ) *
        ofForests (R := R) 0 0 ψ := by
  simp [ForestTensorAlgebra.ofForests]

private def coproductRightMonoidHom (R : Type u) [CommSemiring R] :
    Multiplicative (RootedForest × RootedForest) →* ForestTripleTensorAlgebra R where
  toFun term :=
    let term := Multiplicative.toAdd term
    ofForests (R := R) term.1 0 0 *
      includeRightPair (R := R) (RootedForest.coproduct (R := R) term.2)
  map_one' := by
    simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rcases Multiplicative.toAdd x with ⟨φ₁, ψ₁⟩
    rcases Multiplicative.toAdd y with ⟨φ₂, ψ₂⟩
    change
      ofForests (R := R) (φ₁ + φ₂) 0 0 *
          includeRightPair (R := R) (RootedForest.coproduct (R := R) (ψ₁ + ψ₂)) =
        ofForests (R := R) φ₁ 0 0 *
            includeRightPair (R := R) (RootedForest.coproduct (R := R) ψ₁) *
          (ofForests (R := R) φ₂ 0 0 *
            includeRightPair (R := R) (RootedForest.coproduct (R := R) ψ₂))
    rw [RootedForest.coproduct_add, map_mul]
    have hφ :
        ofForests (R := R) (φ₁ + φ₂) 0 0 =
          ofForests (R := R) φ₁ 0 0 * ofForests (R := R) φ₂ 0 0 := by
      simpa using
        (ofForests_add (R := R) φ₁ φ₂ 0 0 (0 : RootedForest) 0)
    rw [hφ]
    ac_rfl

/-- Apply the coproduct to the second tensor factor, the map `id ⊗ Δ`. -/
def coproductRight : ForestTensorAlgebra R →ₐ[R] ForestTripleTensorAlgebra R :=
  (AddMonoidAlgebra.lift R (ForestTripleTensorAlgebra R) (RootedForest × RootedForest))
    (coproductRightMonoidHom R)

@[simp]
theorem coproductRight_ofPair (term : RootedForest × RootedForest) :
    coproductRight (R := R) (ForestTensorAlgebra.ofPair (R := R) term) =
      ofForests (R := R) term.1 0 0 *
        includeRightPair (R := R) (RootedForest.coproduct (R := R) term.2) := by
  simp [coproductRight, ForestTensorAlgebra.ofPair, coproductRightMonoidHom]

@[simp]
theorem coproductRight_ofForests (φ ψ : RootedForest) :
    coproductRight (R := R) (ForestTensorAlgebra.ofForests (R := R) φ ψ) =
      ofForests (R := R) φ 0 0 *
        includeRightPair (R := R) (RootedForest.coproduct (R := R) ψ) := by
  simp [ForestTensorAlgebra.ofForests]

theorem includeLeftPair_sumTerms (terms : List (RootedForest × RootedForest)) :
    includeLeftPair (R := R) (ForestTensorAlgebra.sumTerms (R := R) terms) =
      sumTerms (R := R) (terms.map fun term => (term.1, term.2, 0)) := by
  induction terms with
  | nil =>
      simp [ForestTensorAlgebra.sumTerms, sumTerms]
  | cons term terms ih =>
      rw [ForestTensorAlgebra.sumTerms_cons, List.map_cons, sumTerms_cons, map_add,
        includeLeftPair_ofPair, ih]

theorem includeRightPair_sumTerms (terms : List (RootedForest × RootedForest)) :
    includeRightPair (R := R) (ForestTensorAlgebra.sumTerms (R := R) terms) =
      sumTerms (R := R) (terms.map fun term => (0, term.1, term.2)) := by
  induction terms with
  | nil =>
      simp [ForestTensorAlgebra.sumTerms, sumTerms]
  | cons term terms ih =>
      rw [ForestTensorAlgebra.sumTerms_cons, List.map_cons, sumTerms_cons, map_add,
        includeRightPair_ofPair, ih]

theorem sumTerms_liftLeft_mul_ofForests
    (terms : List (RootedForest × RootedForest)) (ψ : RootedForest) :
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
    (φ : RootedForest) (terms : List (RootedForest × RootedForest)) :
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

def coproductLeftTerm (term : RootedForest × RootedForest) :
    List (RootedForest × RootedForest × RootedForest) :=
  (RootedForest.coproductTerms term.1).map fun left => (left.1, left.2, term.2)

def coproductRightTerm (term : RootedForest × RootedForest) :
    List (RootedForest × RootedForest × RootedForest) :=
  (RootedForest.coproductTerms term.2).map fun right => (term.1, right.1, right.2)

def coproductLeftTerms (terms : List (RootedForest × RootedForest)) :
    List (RootedForest × RootedForest × RootedForest) :=
  terms.flatMap coproductLeftTerm

def coproductRightTerms (terms : List (RootedForest × RootedForest)) :
    List (RootedForest × RootedForest × RootedForest) :=
  terms.flatMap coproductRightTerm

theorem coproductLeftTerm_add_perm (x y : RootedForest × RootedForest) :
    (coproductLeftTerm (x + y)).Perm (multiplyTerms (coproductLeftTerm x)
      (coproductLeftTerm y)) := by
  rcases x with ⟨φ₁, ψ₁⟩
  rcases y with ⟨φ₂, ψ₂⟩
  have h := (RootedForest.coproductTerms_add_perm φ₁ φ₂).map
    (fun term => (term.1, term.2, ψ₁ + ψ₂))
  simpa [coproductLeftTerm, multiplyTerms, PTree.multiplyCoproductTerms,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def] using h

theorem coproductRightTerm_add_perm (x y : RootedForest × RootedForest) :
    (coproductRightTerm (x + y)).Perm (multiplyTerms (coproductRightTerm x)
      (coproductRightTerm y)) := by
  rcases x with ⟨φ₁, ψ₁⟩
  rcases y with ⟨φ₂, ψ₂⟩
  have h := (RootedForest.coproductTerms_add_perm ψ₁ ψ₂).map
    (fun term => (φ₁ + φ₂, term.1, term.2))
  have hmap :
      (List.flatMap
          (fun a : RootedForest × RootedForest =>
            List.map (fun x => (φ₁ + φ₂, a.1 + x.1, a.2 + x.2))
              (RootedForest.coproductTerms ψ₂)) (RootedForest.coproductTerms ψ₁)) =
        (List.flatMap
          (fun a : RootedForest × RootedForest =>
            List.map (fun x => (φ₁ + φ₂, a + x))
              (RootedForest.coproductTerms ψ₂)) (RootedForest.coproductTerms ψ₁)) := by
    apply List.flatMap_congr
    intro a _ha
    apply List.map_congr_left
    intro x _hx
    cases a
    cases x
    rfl
  simpa [coproductRightTerm, multiplyTerms, PTree.multiplyCoproductTerms,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def, hmap] using h

theorem coproductLeftTerm_singleton_graft_zero_perm (φ : RootedForest) :
    (coproductLeftTerm (RootedForest.singleton (RootedForest.graft φ), 0)).Perm
      (((RootedForest.coproductTerms φ).map fun term =>
          (term.1, RootedForest.singleton (RootedForest.graft term.2), 0)) ++
        [(RootedForest.singleton (RootedForest.graft φ), 0, 0)]) := by
  have h :
      (coproductLeftTerm (RootedForest.singleton (RootedForest.graft φ), 0)).Perm
        (((RootedForest.coproductTerms φ).map fun term =>
            (term.1, (RootedForest.singleton (RootedForest.graft term.2),
              (0 : RootedForest)))) ++
          [(RootedForest.singleton (RootedForest.graft φ), ((0 : RootedForest), 0))]) := by
    simpa [coproductLeftTerm, Function.comp_def] using
      (RootedForest.coproductTerms_singleton_graft_perm φ).map
        (fun left => (left.1, left.2, (0 : RootedForest)))
  simpa using h

theorem coproductRightTerm_singleton_graft_perm (φ ψ : RootedForest) :
    (coproductRightTerm (φ, RootedForest.singleton (RootedForest.graft ψ))).Perm
      (((RootedForest.coproductTerms ψ).map fun term =>
          (φ, term.1, RootedForest.singleton (RootedForest.graft term.2))) ++
        [(φ, RootedForest.singleton (RootedForest.graft ψ), 0)]) := by
  have h :
      (coproductRightTerm (φ, RootedForest.singleton (RootedForest.graft ψ))).Perm
        (((RootedForest.coproductTerms ψ).map fun term =>
            (φ, (term.1, RootedForest.singleton (RootedForest.graft term.2)))) ++
          [(φ, (RootedForest.singleton (RootedForest.graft ψ), 0))]) := by
    simpa [coproductRightTerm, Function.comp_def] using
      (RootedForest.coproductTerms_singleton_graft_perm ψ).map
        (fun right => (φ, right.1, right.2))
  simpa using h

private theorem append_singleton_middle_perm {α : Type _} (xs ys zs : List α) (x : α) :
    ((xs ++ [x]) ++ (ys ++ zs)).Perm ((xs ++ ys) ++ (x :: zs)) := by
  simpa [List.append_assoc] using
    List.Perm.append_right zs
      (List.Perm.append_left xs
        (show ([x] ++ ys).Perm (ys ++ [x]) from List.perm_append_comm))

theorem coproductLeftTerms_append
    (xs ys : List (RootedForest × RootedForest)) :
    coproductLeftTerms (xs ++ ys) = coproductLeftTerms xs ++ coproductLeftTerms ys := by
  simp [coproductLeftTerms]

theorem coproductRightTerms_append
    (xs ys : List (RootedForest × RootedForest)) :
    coproductRightTerms (xs ++ ys) = coproductRightTerms xs ++ coproductRightTerms ys := by
  simp [coproductRightTerms]

theorem coproductLeftTerms_map_singleton_graft
    (terms : List (RootedForest × RootedForest)) :
    coproductLeftTerms (terms.map fun term =>
        (term.1, RootedForest.singleton (RootedForest.graft term.2))) =
      (coproductLeftTerms terms).map fun triple =>
        (triple.1, triple.2.1, RootedForest.singleton (RootedForest.graft triple.2.2)) := by
  induction terms with
  | nil => simp [coproductLeftTerms]
  | cons term terms ih =>
      change
        coproductLeftTerm (term.1, RootedForest.singleton (RootedForest.graft term.2)) ++
          coproductLeftTerms (terms.map fun term =>
            (term.1, RootedForest.singleton (RootedForest.graft term.2))) =
        (coproductLeftTerm term ++ coproductLeftTerms terms).map fun triple =>
          (triple.1, triple.2.1, RootedForest.singleton (RootedForest.graft triple.2.2))
      rw [List.map_append, ih]
      cases term
      simp [coproductLeftTerm, List.map_map, Function.comp_def]

theorem coproductRightTerms_map_singleton_graft_perm
    (terms : List (RootedForest × RootedForest)) :
    (coproductRightTerms (terms.map fun term =>
        (term.1, RootedForest.singleton (RootedForest.graft term.2)))).Perm
      (((coproductRightTerms terms).map fun triple =>
        (triple.1, triple.2.1, RootedForest.singleton (RootedForest.graft triple.2.2))) ++
        (terms.map fun term =>
          (term.1, RootedForest.singleton (RootedForest.graft term.2), 0))) := by
  induction terms with
  | nil => simp [coproductRightTerms]
  | cons term terms ih =>
      let boundary := (term.1, RootedForest.singleton (RootedForest.graft term.2),
        (0 : RootedForest))
      let headTerms :=
        (RootedForest.coproductTerms term.2).map fun right =>
          (term.1, right.1, RootedForest.singleton (RootedForest.graft right.2))
      let tailTerms :=
        (coproductRightTerms terms).map fun triple =>
          (triple.1, triple.2.1, RootedForest.singleton (RootedForest.graft triple.2.2))
      let tailBoundary :=
        terms.map fun term =>
          (term.1, RootedForest.singleton (RootedForest.graft term.2), (0 : RootedForest))
      have hhead :
          (coproductRightTerm
              (term.1, RootedForest.singleton (RootedForest.graft term.2))).Perm
            (headTerms ++ [boundary]) := by
        simpa [headTerms, boundary] using coproductRightTerm_singleton_graft_perm term.1 term.2
      have htail :
          (coproductRightTerms (terms.map fun term =>
            (term.1, RootedForest.singleton (RootedForest.graft term.2)))).Perm
            (tailTerms ++ tailBoundary) := by
        simpa [tailTerms, tailBoundary] using ih
      change
        ((coproductRightTerm
            (term.1, RootedForest.singleton (RootedForest.graft term.2))) ++
          coproductRightTerms (terms.map fun term =>
            (term.1, RootedForest.singleton (RootedForest.graft term.2)))).Perm
        (((coproductRightTerm term ++ coproductRightTerms terms).map fun triple =>
            (triple.1, triple.2.1, RootedForest.singleton (RootedForest.graft triple.2.2))) ++
          (boundary :: tailBoundary))
      rw [List.map_append]
      have hcombined := List.Perm.append hhead htail
      refine hcombined.trans ?_
      simpa [headTerms, tailTerms, tailBoundary, boundary, coproductRightTerm,
        List.map_map, Function.comp_def] using
        append_singleton_middle_perm headTerms tailTerms tailBoundary boundary

theorem coproductRightTerm_zero_perm (φ : RootedForest) :
    (coproductRightTerm (φ, 0)).Perm [(φ, 0, 0)] := by
  have hzero : (RootedForest.coproductTerms (0 : RootedForest)).Perm [(0, 0)] := by
    have h := RootedForest.coproductTerms_ofPTree_list_perm ([] : List PTree)
    exact h.trans (by simp [PTree.coproductTermsList])
  simpa [coproductRightTerm] using hzero.map (fun right => (φ, right.1, right.2))

theorem coproductTerms_node_left_right_perm_of_coproductTermsList_perm
    (ts : List PTree)
    (h : (coproductLeftTerms (PTree.coproductTermsList ts)).Perm
          (coproductRightTerms (PTree.coproductTermsList ts))) :
    (coproductLeftTerms (PTree.coproductTerms (.node ts))).Perm
      (coproductRightTerms (PTree.coproductTerms (.node ts))) := by
  let terms := PTree.coproductTermsList ts
  let forest : RootedForest := (ts.map RootedTree.ofPTree : List RootedTree)
  let graftTerms : List (RootedForest × RootedForest) :=
    terms.map fun term => (term.1, RootedForest.singleton (RootedForest.graft term.2))
  let fullTerm : RootedForest × RootedForest :=
    (RootedForest.singleton (RootedTree.ofPTree (.node ts)), 0)
  let mapG := fun triple : RootedForest × RootedForest × RootedForest =>
    (triple.1, triple.2.1, RootedForest.singleton (RootedForest.graft triple.2.2))
  let boundaryTerms := terms.map fun term =>
    (term.1, RootedForest.singleton (RootedForest.graft term.2), (0 : RootedForest))
  let top := (RootedForest.singleton (RootedTree.ofPTree (.node ts)),
    (0 : RootedForest), (0 : RootedForest))
  have hforest_graft : RootedForest.graft forest = RootedTree.ofPTree (.node ts) := by
    simpa [forest] using RootedForest.graft_ofPTree_list ts
  have hforestTerms : (RootedForest.coproductTerms forest).Perm terms := by
    simpa [forest, terms] using RootedForest.coproductTerms_ofPTree_list_perm ts
  have hcop : (PTree.coproductTerms (.node ts)).Perm (graftTerms ++ [fullTerm]) := by
    simpa [graftTerms, fullTerm, terms] using PTree.coproductTerms_node_perm ts
  have hleftStart :
      (coproductLeftTerms (PTree.coproductTerms (.node ts))).Perm
        (coproductLeftTerms (graftTerms ++ [fullTerm])) := by
    rw [coproductLeftTerms, coproductLeftTerms]
    exact List.Perm.flatMap hcop (fun _ _ => List.Perm.refl _)
  have hrightStart :
      (coproductRightTerms (PTree.coproductTerms (.node ts))).Perm
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
      have hraw := coproductLeftTerm_singleton_graft_zero_perm forest
      have hboundary :
          ((RootedForest.coproductTerms forest).map fun term =>
            (term.1, RootedForest.singleton (RootedForest.graft term.2),
              (0 : RootedForest))).Perm
          boundaryTerms := by
        simpa [boundaryTerms, terms] using hforestTerms.map
          (fun term => (term.1, RootedForest.singleton (RootedForest.graft term.2),
            (0 : RootedForest)))
      simpa [fullTerm, top, hforest_graft] using hraw.trans (hboundary.append_right _)
    have hgraft : coproductLeftTerms graftTerms = (coproductLeftTerms terms).map mapG := by
      simpa [graftTerms, mapG, terms] using coproductLeftTerms_map_singleton_graft terms
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
        coproductRightTerms_map_singleton_graft_perm terms
    have hfull : (coproductRightTerm fullTerm).Perm [top] := by
      simpa [fullTerm, top] using
        coproductRightTerm_zero_perm (RootedForest.singleton (RootedTree.ofPTree (.node ts)))
    simpa [List.append_assoc] using List.Perm.append hgraft hfull
  have hnormal :
      (((coproductLeftTerms terms).map mapG ++ boundaryTerms) ++ [top]).Perm
        (((coproductRightTerms terms).map mapG ++ boundaryTerms) ++ [top]) :=
    List.Perm.append_right [top]
      (List.Perm.append hmap (List.Perm.refl boundaryTerms))
  exact hleftStart.trans
    (hleftNormal.trans (hnormal.trans (hrightNormal.symm.trans hrightStart.symm)))

theorem coproductLeftTerms_multiplyCoproductTerms_perm
    (xs ys : List (RootedForest × RootedForest)) :
    (coproductLeftTerms (PTree.multiplyCoproductTerms xs ys)).Perm
      (multiplyTerms (coproductLeftTerms xs) (coproductLeftTerms ys)) := by
  induction xs with
  | nil =>
      simp [PTree.multiplyCoproductTerms, coproductLeftTerms, multiplyTerms]
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
        simpa [coproductLeftTerms, PTree.multiplyCoproductTerms] using ih
      rw [PTree.multiplyCoproductTerms, coproductLeftTerms]
      simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_map]
      rw [show coproductLeftTerms (x :: xs) =
        coproductLeftTerm x ++ coproductLeftTerms xs by rfl]
      rw [multiplyTerms_append_left]
      exact List.Perm.append hhead ih'

theorem coproductRightTerms_multiplyCoproductTerms_perm
    (xs ys : List (RootedForest × RootedForest)) :
    (coproductRightTerms (PTree.multiplyCoproductTerms xs ys)).Perm
      (multiplyTerms (coproductRightTerms xs) (coproductRightTerms ys)) := by
  induction xs with
  | nil =>
      simp [PTree.multiplyCoproductTerms, coproductRightTerms, multiplyTerms]
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
        simpa [coproductRightTerms, PTree.multiplyCoproductTerms] using ih
      rw [PTree.multiplyCoproductTerms, coproductRightTerms]
      simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_map]
      rw [show coproductRightTerms (x :: xs) =
        coproductRightTerm x ++ coproductRightTerms xs by rfl]
      rw [multiplyTerms_append_left]
      exact List.Perm.append hhead ih'

theorem coproductLeftTerms_perm {xs ys : List (RootedForest × RootedForest)}
    (h : xs.Perm ys) :
    (coproductLeftTerms xs).Perm (coproductLeftTerms ys) := by
  rw [coproductLeftTerms, coproductLeftTerms]
  exact List.Perm.flatMap h (fun _ _ => List.Perm.refl _)

theorem coproductRightTerms_perm {xs ys : List (RootedForest × RootedForest)}
    (h : xs.Perm ys) :
    (coproductRightTerms xs).Perm (coproductRightTerms ys) := by
  rw [coproductRightTerms, coproductRightTerms]
  exact List.Perm.flatMap h (fun _ _ => List.Perm.refl _)

theorem coproductLeftTerms_rootedForest_add_perm (φ ψ : RootedForest) :
    (coproductLeftTerms (RootedForest.coproductTerms (φ + ψ))).Perm
      (multiplyTerms (coproductLeftTerms (RootedForest.coproductTerms φ))
        (coproductLeftTerms (RootedForest.coproductTerms ψ))) :=
  (coproductLeftTerms_perm (RootedForest.coproductTerms_add_perm φ ψ)).trans
    (coproductLeftTerms_multiplyCoproductTerms_perm _ _)

theorem coproductRightTerms_rootedForest_add_perm (φ ψ : RootedForest) :
    (coproductRightTerms (RootedForest.coproductTerms (φ + ψ))).Perm
      (multiplyTerms (coproductRightTerms (RootedForest.coproductTerms φ))
        (coproductRightTerms (RootedForest.coproductTerms ψ))) :=
  (coproductRightTerms_perm (RootedForest.coproductTerms_add_perm φ ψ)).trans
    (coproductRightTerms_multiplyCoproductTerms_perm _ _)

theorem coproductTermsList_left_right_perm_of_coproductTerms_perm
    (h : ∀ t : PTree,
      (coproductLeftTerms (PTree.coproductTerms t)).Perm
        (coproductRightTerms (PTree.coproductTerms t))) :
    ∀ ts : List PTree,
      (coproductLeftTerms (PTree.coproductTermsList ts)).Perm
        (coproductRightTerms (PTree.coproductTermsList ts)) := by
  intro ts
  induction ts with
  | nil =>
      have hzero : (RootedForest.coproductTerms (0 : RootedForest)).Perm [(0, 0)] := by
        simpa [PTree.coproductTermsList] using
          (RootedForest.coproductTerms_ofPTree_list_perm ([] : List PTree))
      have hleft :
          (coproductLeftTerm ((0 : RootedForest), (0 : RootedForest))).Perm
            [((0 : RootedForest), (0 : RootedForest), (0 : RootedForest))] := by
        simpa [coproductLeftTerm] using
          hzero.map (fun left => (left.1, left.2, (0 : RootedForest)))
      have hright :
          (coproductRightTerm ((0 : RootedForest), (0 : RootedForest))).Perm
            [((0 : RootedForest), (0 : RootedForest), (0 : RootedForest))] := by
        simpa [coproductRightTerm] using
          hzero.map (fun right => ((0 : RootedForest), right.1, right.2))
      simpa [PTree.coproductTermsList, coproductLeftTerms, coproductRightTerms] using
        hleft.trans hright.symm
  | cons t ts ih =>
      rw [PTree.coproductTermsList]
      exact (coproductLeftTerms_multiplyCoproductTerms_perm
          (PTree.coproductTerms t) (PTree.coproductTermsList ts)).trans
        ((multiplyTerms_perm (h t) ih).trans
          (coproductRightTerms_multiplyCoproductTerms_perm
            (PTree.coproductTerms t) (PTree.coproductTermsList ts)).symm)

mutual

theorem coproductTerms_left_right_perm :
    ∀ t : PTree,
      (coproductLeftTerms (PTree.coproductTerms t)).Perm
        (coproductRightTerms (PTree.coproductTerms t))
  | .node ts =>
      coproductTerms_node_left_right_perm_of_coproductTermsList_perm ts
        (coproductTermsList_left_right_perm ts)

theorem coproductTermsList_left_right_perm :
    ∀ ts : List PTree,
      (coproductLeftTerms (PTree.coproductTermsList ts)).Perm
        (coproductRightTerms (PTree.coproductTermsList ts))
  | [] => by
      have hzero : (RootedForest.coproductTerms (0 : RootedForest)).Perm [(0, 0)] := by
        have h := RootedForest.coproductTerms_ofPTree_list_perm ([] : List PTree)
        exact h.trans (by simp [PTree.coproductTermsList])
      have hleft :
          (coproductLeftTerm ((0 : RootedForest), (0 : RootedForest))).Perm
            [((0 : RootedForest), (0 : RootedForest), (0 : RootedForest))] := by
        simpa [coproductLeftTerm] using
          hzero.map (fun left => (left.1, left.2, (0 : RootedForest)))
      have hright :
          (coproductRightTerm ((0 : RootedForest), (0 : RootedForest))).Perm
            [((0 : RootedForest), (0 : RootedForest), (0 : RootedForest))] := by
        simpa [coproductRightTerm] using
          hzero.map (fun right => ((0 : RootedForest), right.1, right.2))
      simpa [PTree.coproductTermsList, coproductLeftTerms, coproductRightTerms] using
        hleft.trans hright.symm
  | t :: ts => by
      rw [PTree.coproductTermsList]
      exact (coproductLeftTerms_multiplyCoproductTerms_perm
          (PTree.coproductTerms t) (PTree.coproductTermsList ts)).trans
        ((multiplyTerms_perm (coproductTerms_left_right_perm t)
            (coproductTermsList_left_right_perm ts)).trans
          (coproductRightTerms_multiplyCoproductTerms_perm
            (PTree.coproductTerms t) (PTree.coproductTermsList ts)).symm)

end

theorem coproductTerms_rootedForest_left_right_perm_of_coproductTerms_perm
    (h : ∀ t : PTree,
      (coproductLeftTerms (PTree.coproductTerms t)).Perm
        (coproductRightTerms (PTree.coproductTerms t)))
    (φ : RootedForest) :
    (coproductLeftTerms (RootedForest.coproductTerms φ)).Perm
      (coproductRightTerms (RootedForest.coproductTerms φ)) := by
  rw [RootedForest.coproductTerms]
  exact coproductTermsList_left_right_perm_of_coproductTerms_perm h
    ((Quotient.out φ).map Quotient.out)

theorem coproductLeftTerm_order
    {term : RootedForest × RootedForest}
    {triple : RootedForest × RootedForest × RootedForest}
    (htriple : triple ∈ coproductLeftTerm term) :
    RootedForest.order triple.1 + RootedForest.order triple.2.1 +
        RootedForest.order triple.2.2 =
      RootedForest.order term.1 + RootedForest.order term.2 := by
  simp [coproductLeftTerm] at htriple
  obtain ⟨left₁, left₂, hleft, htriple⟩ := htriple
  subst triple
  have hleft_order := RootedForest.coproductTerms_order hleft
  change
    RootedForest.order left₁ + RootedForest.order left₂ =
      RootedForest.order term.1 at hleft_order
  change
    RootedForest.order left₁ + RootedForest.order left₂ + RootedForest.order term.2 =
      RootedForest.order term.1 + RootedForest.order term.2
  omega

theorem coproductRightTerm_order
    {term : RootedForest × RootedForest}
    {triple : RootedForest × RootedForest × RootedForest}
    (htriple : triple ∈ coproductRightTerm term) :
    RootedForest.order triple.1 + RootedForest.order triple.2.1 +
        RootedForest.order triple.2.2 =
      RootedForest.order term.1 + RootedForest.order term.2 := by
  simp [coproductRightTerm] at htriple
  obtain ⟨right₁, right₂, hright, htriple⟩ := htriple
  subst triple
  have hright_order := RootedForest.coproductTerms_order hright
  change
    RootedForest.order right₁ + RootedForest.order right₂ =
      RootedForest.order term.2 at hright_order
  change
    RootedForest.order term.1 + RootedForest.order right₁ + RootedForest.order right₂ =
      RootedForest.order term.1 + RootedForest.order term.2
  omega

theorem coproductLeftTerms_order
    {terms : List (RootedForest × RootedForest)} {m : Nat}
    (hterms : ∀ term ∈ terms, RootedForest.order term.1 + RootedForest.order term.2 = m)
    {triple : RootedForest × RootedForest × RootedForest}
    (htriple : triple ∈ coproductLeftTerms terms) :
    RootedForest.order triple.1 + RootedForest.order triple.2.1 +
        RootedForest.order triple.2.2 = m := by
  simp [coproductLeftTerms] at htriple
  obtain ⟨φ, ψ, hterm, htriple⟩ := htriple
  rw [← hterms (φ, ψ) hterm]
  exact coproductLeftTerm_order htriple

theorem coproductRightTerms_order
    {terms : List (RootedForest × RootedForest)} {m : Nat}
    (hterms : ∀ term ∈ terms, RootedForest.order term.1 + RootedForest.order term.2 = m)
    {triple : RootedForest × RootedForest × RootedForest}
    (htriple : triple ∈ coproductRightTerms terms) :
    RootedForest.order triple.1 + RootedForest.order triple.2.1 +
        RootedForest.order triple.2.2 = m := by
  simp [coproductRightTerms] at htriple
  obtain ⟨φ, ψ, hterm, htriple⟩ := htriple
  rw [← hterms (φ, ψ) hterm]
  exact coproductRightTerm_order htriple

theorem coproductLeftTerms_rootedForest_order
    {φ : RootedForest} {triple : RootedForest × RootedForest × RootedForest}
    (htriple : triple ∈ coproductLeftTerms (RootedForest.coproductTerms φ)) :
    RootedForest.order triple.1 + RootedForest.order triple.2.1 +
        RootedForest.order triple.2.2 = RootedForest.order φ :=
  coproductLeftTerms_order (fun _ hterm => RootedForest.coproductTerms_order hterm)
    htriple

theorem coproductRightTerms_rootedForest_order
    {φ : RootedForest} {triple : RootedForest × RootedForest × RootedForest}
    (htriple : triple ∈ coproductRightTerms (RootedForest.coproductTerms φ)) :
    RootedForest.order triple.1 + RootedForest.order triple.2.1 +
        RootedForest.order triple.2.2 = RootedForest.order φ :=
  coproductRightTerms_order (fun _ hterm => RootedForest.coproductTerms_order hterm)
    htriple

theorem coproductLeftTerms_ptree_order
    {t : PTree} {triple : RootedForest × RootedForest × RootedForest}
    (htriple : triple ∈ coproductLeftTerms (PTree.coproductTerms t)) :
    RootedForest.order triple.1 + RootedForest.order triple.2.1 +
        RootedForest.order triple.2.2 = PTree.order t :=
  coproductLeftTerms_order (fun _ hterm => PTree.coproductTerms_order hterm)
    htriple

theorem coproductRightTerms_ptree_order
    {t : PTree} {triple : RootedForest × RootedForest × RootedForest}
    (htriple : triple ∈ coproductRightTerms (PTree.coproductTerms t)) :
    RootedForest.order triple.1 + RootedForest.order triple.2.1 +
        RootedForest.order triple.2.2 = PTree.order t :=
  coproductRightTerms_order (fun _ hterm => PTree.coproductTerms_order hterm)
    htriple

theorem sumTerms_coproductLeftTerm (term : RootedForest × RootedForest) :
    sumTerms (R := R) (coproductLeftTerm term) =
      coproductLeft (R := R) (ForestTensorAlgebra.ofPair (R := R) term) := by
  rw [coproductLeftTerm, coproductLeft_ofPair,
    RootedForest.coproduct_eq_sumTerms_coproductTerms, includeLeftPair_sumTerms,
    sumTerms_liftLeft_mul_ofForests]

theorem sumTerms_coproductRightTerm (term : RootedForest × RootedForest) :
    sumTerms (R := R) (coproductRightTerm term) =
      coproductRight (R := R) (ForestTensorAlgebra.ofPair (R := R) term) := by
  rw [coproductRightTerm, coproductRight_ofPair,
    RootedForest.coproduct_eq_sumTerms_coproductTerms, includeRightPair_sumTerms,
    ofForests_mul_sumTerms_liftRight]

theorem sumTerms_coproductLeftTerms (terms : List (RootedForest × RootedForest)) :
    sumTerms (R := R) (coproductLeftTerms terms) =
      coproductLeft (R := R) (ForestTensorAlgebra.sumTerms (R := R) terms) := by
  induction terms with
  | nil =>
      simp [coproductLeftTerms, ForestTensorAlgebra.sumTerms]
  | cons term terms ih =>
      have ih' :
          sumTerms (R := R) (List.flatMap coproductLeftTerm terms) =
            coproductLeft (R := R) (ForestTensorAlgebra.sumTerms (R := R) terms) := by
        simpa [coproductLeftTerms] using ih
      rw [coproductLeftTerms, List.flatMap_cons, sumTerms_append,
        sumTerms_coproductLeftTerm, ih', ForestTensorAlgebra.sumTerms_cons, map_add]

theorem sumTerms_coproductRightTerms (terms : List (RootedForest × RootedForest)) :
    sumTerms (R := R) (coproductRightTerms terms) =
      coproductRight (R := R) (ForestTensorAlgebra.sumTerms (R := R) terms) := by
  induction terms with
  | nil =>
      simp [coproductRightTerms, ForestTensorAlgebra.sumTerms]
  | cons term terms ih =>
      have ih' :
          sumTerms (R := R) (List.flatMap coproductRightTerm terms) =
            coproductRight (R := R) (ForestTensorAlgebra.sumTerms (R := R) terms) := by
        simpa [coproductRightTerms] using ih
      rw [coproductRightTerms, List.flatMap_cons, sumTerms_append,
        sumTerms_coproductRightTerm, ih', ForestTensorAlgebra.sumTerms_cons, map_add]

theorem coproductLeft_coproduct_eq_sumTerms (φ : RootedForest) :
    coproductLeft (R := R) (RootedForest.coproduct (R := R) φ) =
      sumTerms (R := R) (coproductLeftTerms (RootedForest.coproductTerms φ)) := by
  rw [RootedForest.coproduct_eq_sumTerms_coproductTerms]
  exact (sumTerms_coproductLeftTerms (R := R) (RootedForest.coproductTerms φ)).symm

theorem coproductRight_coproduct_eq_sumTerms (φ : RootedForest) :
    coproductRight (R := R) (RootedForest.coproduct (R := R) φ) =
      sumTerms (R := R) (coproductRightTerms (RootedForest.coproductTerms φ)) := by
  rw [RootedForest.coproduct_eq_sumTerms_coproductTerms]
  exact (sumTerms_coproductRightTerms (R := R) (RootedForest.coproductTerms φ)).symm

theorem coproductLeft_ptree_coproduct_eq_sumTerms (t : PTree) :
    coproductLeft (R := R) (PTree.coproduct (R := R) t) =
      sumTerms (R := R) (coproductLeftTerms (PTree.coproductTerms t)) := by
  rw [PTree.coproduct]
  exact (sumTerms_coproductLeftTerms (R := R) (PTree.coproductTerms t)).symm

theorem coproductRight_ptree_coproduct_eq_sumTerms (t : PTree) :
    coproductRight (R := R) (PTree.coproduct (R := R) t) =
      sumTerms (R := R) (coproductRightTerms (PTree.coproductTerms t)) := by
  rw [PTree.coproduct]
  exact (sumTerms_coproductRightTerms (R := R) (PTree.coproductTerms t)).symm

theorem nestedCoproductLeftCut_perm_coproductLeftTerm (c : PTree.Cut) :
    ((PTree.coproductTermsList c.pruned).map
        fun left => (left.1, left.2, c.trunkForest)).Perm
      (coproductLeftTerm (c.prunedForest, c.trunkForest)) := by
  simpa [coproductLeftTerm, PTree.Cut.prunedForest] using
    ((RootedForest.coproductTerms_ofPTree_list_perm c.pruned).symm.map
      (fun left => (left.1, left.2, c.trunkForest)))

theorem nestedCoproductRightCut_perm_coproductRightTerm (c : PTree.Cut) :
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
                  (((pruned.map RootedTree.ofPTree : List RootedTree) : RootedForest),
                    right.1, right.2))
                (PTree.coproductTermsList ([] : List PTree))).Perm
              (List.map
                (fun right =>
                  (((pruned.map RootedTree.ofPTree : List RootedTree) : RootedForest),
                    right.1, right.2))
                (RootedForest.coproductTerms (0 : RootedForest)))
          exact
            ((RootedForest.coproductTerms_ofPTree_list_perm ([] : List PTree)).symm.map
              (fun right =>
                (((pruned.map RootedTree.ofPTree : List RootedTree) : RootedForest),
                  right.1, right.2)))
      | some trunk =>
          change
            (List.map
                (fun right =>
                  (((pruned.map RootedTree.ofPTree : List RootedTree) : RootedForest),
                    right.1, right.2))
                (PTree.coproductTerms trunk)).Perm
              (List.map
                (fun right =>
                  (((pruned.map RootedTree.ofPTree : List RootedTree) : RootedForest),
                    right.1, right.2))
                (RootedForest.coproductTerms
                  (RootedForest.singleton (RootedTree.ofPTree trunk))))
          exact
            ((RootedForest.coproductTerms_singleton_ofPTree_perm trunk).symm.map
              (fun right =>
                (((pruned.map RootedTree.ofPTree : List RootedTree) : RootedForest),
                  right.1, right.2)))

theorem nestedCoproductLeftCuts_perm_coproductLeftTerms :
    ∀ cuts : List PTree.Cut,
      (cuts.flatMap fun c =>
        (PTree.coproductTermsList c.pruned).map
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
    ∀ cuts : List PTree.Cut,
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

theorem nestedCoproductLeftTerms_perm_coproductLeftTerms (t : PTree) :
    (PTree.nestedCoproductLeftTerms t).Perm
      (coproductLeftTerms (PTree.coproductTerms t)) := by
  simpa [PTree.nestedCoproductLeftTerms, PTree.coproductTerms] using
    nestedCoproductLeftCuts_perm_coproductLeftTerms (PTree.cuts t)

theorem nestedCoproductRightTerms_perm_coproductRightTerms (t : PTree) :
    (PTree.nestedCoproductRightTerms t).Perm
      (coproductRightTerms (PTree.coproductTerms t)) := by
  simpa [PTree.nestedCoproductRightTerms, PTree.coproductTerms] using
    nestedCoproductRightCuts_perm_coproductRightTerms (PTree.cuts t)

theorem nestedCoproductTerms_perm_iff_coproductTerms_perm (t : PTree) :
    (PTree.nestedCoproductLeftTerms t).Perm (PTree.nestedCoproductRightTerms t) ↔
      (coproductLeftTerms (PTree.coproductTerms t)).Perm
        (coproductRightTerms (PTree.coproductTerms t)) := by
  constructor
  · intro h
    exact (nestedCoproductLeftTerms_perm_coproductLeftTerms t).symm.trans
      (h.trans (nestedCoproductRightTerms_perm_coproductRightTerms t))
  · intro h
    exact (nestedCoproductLeftTerms_perm_coproductLeftTerms t).trans
      (h.trans (nestedCoproductRightTerms_perm_coproductRightTerms t).symm)

theorem nestedCoproductTerms_left_right_perm (t : PTree) :
    (PTree.nestedCoproductLeftTerms t).Perm (PTree.nestedCoproductRightTerms t) :=
  (nestedCoproductTerms_perm_iff_coproductTerms_perm t).2
    (coproductTerms_left_right_perm t)

theorem coproductTerms_rootedForest_left_right_perm_of_nestedCoproductTerms_perm
    (h : ∀ t : PTree,
      (PTree.nestedCoproductLeftTerms t).Perm (PTree.nestedCoproductRightTerms t))
    (φ : RootedForest) :
    (coproductLeftTerms (RootedForest.coproductTerms φ)).Perm
      (coproductRightTerms (RootedForest.coproductTerms φ)) :=
  coproductTerms_rootedForest_left_right_perm_of_coproductTerms_perm
    (fun t => (nestedCoproductTerms_perm_iff_coproductTerms_perm t).1 (h t)) φ

theorem sumTerms_nestedCoproductLeftCut (c : PTree.Cut) :
    sumTerms (R := R)
        ((PTree.coproductTermsList c.pruned).map
          fun left => (left.1, left.2, c.trunkForest)) =
      coproductLeft (R := R)
        (ForestTensorAlgebra.ofPair (R := R) (c.prunedForest, c.trunkForest)) := by
  rw [coproductLeft_ofPair]
  have hcop :
      RootedForest.coproduct (R := R) c.prunedForest =
        PTree.coproductList (R := R) c.pruned := by
    simpa [PTree.Cut.prunedForest] using
      RootedForest.coproduct_ofPTree_list (R := R) c.pruned
  rw [hcop, PTree.coproductList, includeLeftPair_sumTerms,
    sumTerms_liftLeft_mul_ofForests]

theorem sumTerms_trunkCoproductTerms (c : PTree.Cut) :
    RootedForest.coproduct (R := R) c.trunkForest =
      ForestTensorAlgebra.sumTerms (R := R) c.trunkCoproductTerms := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? with
      | none =>
          simp [PTree.Cut.trunkForest, PTree.Cut.trunkCoproductTerms,
            ForestTensorAlgebra.sumTerms]
          change 1 = ForestTensorAlgebra.ofPair (R := R)
            (0 : RootedForest × RootedForest)
          rw [ForestTensorAlgebra.ofPair_zero]
      | some trunk =>
          rw [PTree.Cut.trunkForest, PTree.Cut.trunkCoproductTerms,
            RootedForest.coproduct_singleton_ofPTree, PTree.coproduct]

theorem sumTerms_nestedCoproductRightCut (c : PTree.Cut) :
    sumTerms (R := R)
        (c.trunkCoproductTerms.map
          fun right => (c.prunedForest, right.1, right.2)) =
      coproductRight (R := R)
        (ForestTensorAlgebra.ofPair (R := R) (c.prunedForest, c.trunkForest)) := by
  rw [coproductRight_ofPair, sumTerms_trunkCoproductTerms,
    includeRightPair_sumTerms, ofForests_mul_sumTerms_liftRight]

theorem sumTerms_nestedCoproductLeftCut_perm {c d : PTree.Cut}
    (h : PTree.Cut.Perm c d) :
    sumTerms (R := R)
        ((PTree.coproductTermsList c.pruned).map
          fun left => (left.1, left.2, c.trunkForest)) =
      sumTerms (R := R)
        ((PTree.coproductTermsList d.pruned).map
          fun left => (left.1, left.2, d.trunkForest)) := by
  rw [sumTerms_nestedCoproductLeftCut, sumTerms_nestedCoproductLeftCut,
    PTree.Cut.Perm.coproductTerm_eq h]

theorem sumTerms_nestedCoproductRightCut_perm {c d : PTree.Cut}
    (h : PTree.Cut.Perm c d) :
    sumTerms (R := R)
        (c.trunkCoproductTerms.map
          fun right => (c.prunedForest, right.1, right.2)) =
      sumTerms (R := R)
        (d.trunkCoproductTerms.map
          fun right => (d.prunedForest, right.1, right.2)) := by
  rw [sumTerms_nestedCoproductRightCut, sumTerms_nestedCoproductRightCut,
    PTree.Cut.Perm.coproductTerm_eq h]

theorem sumTerms_nestedCoproductLeftCuts :
    ∀ cuts : List PTree.Cut,
      sumTerms (R := R)
          (cuts.flatMap fun c =>
            (PTree.coproductTermsList c.pruned).map
              fun left => (left.1, left.2, c.trunkForest)) =
        coproductLeft (R := R)
          (ForestTensorAlgebra.sumTerms (R := R)
            (cuts.map fun c => (c.prunedForest, c.trunkForest)))
  | [] => by
      simp [ForestTensorAlgebra.sumTerms]
  | c :: cuts => by
      rw [List.flatMap_cons, sumTerms_append, List.map_cons,
        ForestTensorAlgebra.sumTerms_cons, map_add, sumTerms_nestedCoproductLeftCut,
        sumTerms_nestedCoproductLeftCuts cuts]

theorem sumTerms_nestedCoproductRightCuts :
    ∀ cuts : List PTree.Cut,
      sumTerms (R := R)
          (cuts.flatMap fun c =>
            c.trunkCoproductTerms.map
              fun right => (c.prunedForest, right.1, right.2)) =
        coproductRight (R := R)
          (ForestTensorAlgebra.sumTerms (R := R)
            (cuts.map fun c => (c.prunedForest, c.trunkForest)))
  | [] => by
      simp [ForestTensorAlgebra.sumTerms]
  | c :: cuts => by
      rw [List.flatMap_cons, sumTerms_append, List.map_cons,
        ForestTensorAlgebra.sumTerms_cons, map_add, sumTerms_nestedCoproductRightCut,
        sumTerms_nestedCoproductRightCuts cuts]

theorem sumTerms_nestedCoproductLeftCuts_listRelPerm
    {cs ds : List PTree.Cut} (h : PTree.ListRelPerm PTree.Cut.Perm cs ds) :
    sumTerms (R := R)
        (cs.flatMap fun c =>
          (PTree.coproductTermsList c.pruned).map
            fun left => (left.1, left.2, c.trunkForest)) =
      sumTerms (R := R)
        (ds.flatMap fun d =>
          (PTree.coproductTermsList d.pruned).map
            fun left => (left.1, left.2, d.trunkForest)) := by
  rw [sumTerms_nestedCoproductLeftCuts, sumTerms_nestedCoproductLeftCuts,
    ForestTensorAlgebra.sumTerms_cut_listRelPerm (R := R) h]

theorem sumTerms_nestedCoproductRightCuts_listRelPerm
    {cs ds : List PTree.Cut} (h : PTree.ListRelPerm PTree.Cut.Perm cs ds) :
    sumTerms (R := R)
        (cs.flatMap fun c =>
          c.trunkCoproductTerms.map
            fun right => (c.prunedForest, right.1, right.2)) =
      sumTerms (R := R)
        (ds.flatMap fun d =>
          d.trunkCoproductTerms.map
            fun right => (d.prunedForest, right.1, right.2)) := by
  rw [sumTerms_nestedCoproductRightCuts, sumTerms_nestedCoproductRightCuts,
    ForestTensorAlgebra.sumTerms_cut_listRelPerm (R := R) h]

theorem sumTerms_nestedCoproductLeftCuts_forall₂_perm
    {cs ds : List PTree.Cut} (h : List.Forall₂ PTree.Cut.Perm cs ds) :
    sumTerms (R := R)
        (cs.flatMap fun c =>
          (PTree.coproductTermsList c.pruned).map
            fun left => (left.1, left.2, c.trunkForest)) =
      sumTerms (R := R)
        (ds.flatMap fun d =>
          (PTree.coproductTermsList d.pruned).map
            fun left => (left.1, left.2, d.trunkForest)) :=
  sumTerms_nestedCoproductLeftCuts_listRelPerm (R := R)
    (PTree.ListRelPerm.of_forall₂ h)

theorem sumTerms_nestedCoproductRightCuts_forall₂_perm
    {cs ds : List PTree.Cut} (h : List.Forall₂ PTree.Cut.Perm cs ds) :
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

theorem sumTerms_nestedCoproductLeftTerms (t : PTree) :
    sumTerms (R := R) (PTree.nestedCoproductLeftTerms t) =
      sumTerms (R := R) (coproductLeftTerms (PTree.coproductTerms t)) := by
  rw [← coproductLeft_ptree_coproduct_eq_sumTerms]
  simpa [PTree.nestedCoproductLeftTerms, PTree.coproduct, PTree.coproductTerms] using
    sumTerms_nestedCoproductLeftCuts (R := R) (PTree.cuts t)

theorem sumTerms_nestedCoproductRightTerms (t : PTree) :
    sumTerms (R := R) (PTree.nestedCoproductRightTerms t) =
      sumTerms (R := R) (coproductRightTerms (PTree.coproductTerms t)) := by
  rw [← coproductRight_ptree_coproduct_eq_sumTerms]
  simpa [PTree.nestedCoproductRightTerms, PTree.coproduct, PTree.coproductTerms] using
    sumTerms_nestedCoproductRightCuts (R := R) (PTree.cuts t)

theorem sumTerms_nestedCoproductLeftTerms_listRelPerm
    {t u : PTree} (h : PTree.ListRelPerm PTree.Cut.Perm (PTree.cuts t) (PTree.cuts u)) :
    sumTerms (R := R) (PTree.nestedCoproductLeftTerms t) =
      sumTerms (R := R) (PTree.nestedCoproductLeftTerms u) := by
  simpa [PTree.nestedCoproductLeftTerms] using
    sumTerms_nestedCoproductLeftCuts_listRelPerm (R := R) h

theorem sumTerms_nestedCoproductRightTerms_listRelPerm
    {t u : PTree} (h : PTree.ListRelPerm PTree.Cut.Perm (PTree.cuts t) (PTree.cuts u)) :
    sumTerms (R := R) (PTree.nestedCoproductRightTerms t) =
      sumTerms (R := R) (PTree.nestedCoproductRightTerms u) := by
  simpa [PTree.nestedCoproductRightTerms] using
    sumTerms_nestedCoproductRightCuts_listRelPerm (R := R) h

theorem sumTerms_nestedCoproductLeftTerms_perm {t u : PTree} (h : PTree.Perm t u) :
    sumTerms (R := R) (PTree.nestedCoproductLeftTerms t) =
      sumTerms (R := R) (PTree.nestedCoproductLeftTerms u) :=
  sumTerms_nestedCoproductLeftTerms_listRelPerm (R := R)
    (PTree.cuts_listRelPerm_of_perm h)

theorem sumTerms_nestedCoproductRightTerms_perm {t u : PTree} (h : PTree.Perm t u) :
    sumTerms (R := R) (PTree.nestedCoproductRightTerms t) =
      sumTerms (R := R) (PTree.nestedCoproductRightTerms u) :=
  sumTerms_nestedCoproductRightTerms_listRelPerm (R := R)
    (PTree.cuts_listRelPerm_of_perm h)

end

end ForestTripleTensorAlgebra

namespace ForestAlgebra

noncomputable section

variable {R : Type u} [CommSemiring R]

private def coproductMonoidHom (R : Type u) [CommSemiring R] :
    Multiplicative RootedForest →* ForestTensorAlgebra R where
  toFun φ := RootedForest.coproduct (R := R) (Multiplicative.toAdd φ)
  map_one' := by
    change RootedForest.coproduct (R := R) (0 : RootedForest) = 1
    simp
  map_mul' φ ψ := by
    change
      RootedForest.coproduct (R := R) (Multiplicative.toAdd (φ * ψ)) =
        RootedForest.coproduct (R := R) (Multiplicative.toAdd φ) *
          RootedForest.coproduct (R := R) (Multiplicative.toAdd ψ)
    change
      RootedForest.coproduct (R := R) (Multiplicative.toAdd φ + Multiplicative.toAdd ψ) =
        RootedForest.coproduct (R := R) (Multiplicative.toAdd φ) *
          RootedForest.coproduct (R := R) (Multiplicative.toAdd ψ)
    simp

/-- The BCK coproduct as an algebra morphism on the rooted-forest algebra. -/
def coproduct (R : Type u) [CommSemiring R] :
    ForestAlgebra R →ₐ[R] ForestTensorAlgebra R :=
  (AddMonoidAlgebra.lift R (ForestTensorAlgebra R) RootedForest)
    (coproductMonoidHom R)

/-- The iterated coproduct `(Δ ⊗ id) ∘ Δ`. -/
def coproductLeft (R : Type u) [CommSemiring R] :
    ForestAlgebra R →ₐ[R] ForestTripleTensorAlgebra R :=
  ForestTripleTensorAlgebra.coproductLeft.comp (coproduct R)

/-- The iterated coproduct `(id ⊗ Δ) ∘ Δ`. -/
def coproductRight (R : Type u) [CommSemiring R] :
    ForestAlgebra R →ₐ[R] ForestTripleTensorAlgebra R :=
  ForestTripleTensorAlgebra.coproductRight.comp (coproduct R)

@[simp]
theorem coproduct_ofForest (φ : RootedForest) :
    coproduct R (ofForest (R := R) φ) = RootedForest.coproduct (R := R) φ := by
  simp [coproduct, ofForest, coproductMonoidHom]

@[simp]
theorem coproductLeft_ofForest (φ : RootedForest) :
    coproductLeft R (ofForest (R := R) φ) =
      ForestTripleTensorAlgebra.coproductLeft (RootedForest.coproduct (R := R) φ) := by
  simp [coproductLeft]

@[simp]
theorem coproductRight_ofForest (φ : RootedForest) :
    coproductRight R (ofForest (R := R) φ) =
      ForestTripleTensorAlgebra.coproductRight (RootedForest.coproduct (R := R) φ) := by
  simp [coproductRight]

@[simp]
theorem coproduct_ofForest_zero :
    coproduct R (ofForest (R := R) 0) = 1 := by
  simp

@[simp]
theorem coproduct_ofForest_empty :
    coproduct R (ofForest (R := R) RootedForest.empty) = 1 := by
  simp

@[simp]
theorem coproduct_ofForest_singleton (τ : RootedTree) :
    coproduct R (ofForest (R := R) (RootedForest.singleton τ)) =
      PTree.coproduct (R := R) (Quotient.out τ) := by
  simp

theorem coproduct_ofForest_singleton_tree (τ : RootedTree) :
    coproduct R (ofForest (R := R) (RootedForest.singleton τ)) =
      RootedTree.coproduct (R := R) τ := by
  rw [coproduct_ofForest, RootedForest.coproduct_singleton_tree]

theorem coproduct_ofForest_singleton_ofPTree (t : PTree) :
    coproduct R (ofForest (R := R) (RootedForest.singleton (RootedTree.ofPTree t))) =
      PTree.coproduct (R := R) t := by
  rw [coproduct_ofForest, RootedForest.coproduct_singleton_ofPTree]

theorem coproductLeft_ofForest_singleton_ofPTree_eq_sumTerms (t : PTree) :
    coproductLeft R
        (ofForest (R := R) (RootedForest.singleton (RootedTree.ofPTree t))) =
      ForestTripleTensorAlgebra.sumTerms (R := R)
        (ForestTripleTensorAlgebra.coproductLeftTerms (PTree.coproductTerms t)) := by
  rw [coproductLeft_ofForest, RootedForest.coproduct_singleton_ofPTree,
    ForestTripleTensorAlgebra.coproductLeft_ptree_coproduct_eq_sumTerms]

theorem coproductRight_ofForest_singleton_ofPTree_eq_sumTerms (t : PTree) :
    coproductRight R
        (ofForest (R := R) (RootedForest.singleton (RootedTree.ofPTree t))) =
      ForestTripleTensorAlgebra.sumTerms (R := R)
        (ForestTripleTensorAlgebra.coproductRightTerms (PTree.coproductTerms t)) := by
  rw [coproductRight_ofForest, RootedForest.coproduct_singleton_ofPTree,
    ForestTripleTensorAlgebra.coproductRight_ptree_coproduct_eq_sumTerms]

theorem coproductLeft_eq_coproductRight_of_singletons
    (h : ∀ τ : RootedTree,
      coproductLeft R (ofForest (R := R) (RootedForest.singleton τ)) =
        coproductRight R (ofForest (R := R) (RootedForest.singleton τ))) :
    coproductLeft R = coproductRight R := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext)
  apply MonoidHom.ext
  intro φ
  change
    coproductLeft R (ofForest (R := R) (Multiplicative.toAdd φ)) =
      coproductRight R (ofForest (R := R) (Multiplicative.toAdd φ))
  refine Quotient.inductionOn (Multiplicative.toAdd φ) ?_
  intro ts
  induction ts with
  | nil =>
      simp
  | cons τ ts ih =>
      change
        coproductLeft R (ofForest (R := R)
            (RootedForest.singleton τ + (ts : RootedForest))) =
          coproductRight R (ofForest (R := R)
            (RootedForest.singleton τ + (ts : RootedForest)))
      have ih' :
          coproductLeft R (ofForest (R := R) (ts : RootedForest)) =
            coproductRight R (ofForest (R := R) (ts : RootedForest)) := by
        simpa using ih
      rw [ofForest_add, map_mul, map_mul, h τ, ih']

theorem coproductLeft_eq_coproductRight_iff_singletons :
    coproductLeft R = coproductRight R ↔
      ∀ τ : RootedTree,
        coproductLeft R (ofForest (R := R) (RootedForest.singleton τ)) =
          coproductRight R (ofForest (R := R) (RootedForest.singleton τ)) := by
  constructor
  · intro h τ
    rw [h]
  · exact coproductLeft_eq_coproductRight_of_singletons (R := R)

theorem coproductLeft_eq_coproductRight_of_ptree_singletons
    (h : ∀ t : PTree,
      coproductLeft R
          (ofForest (R := R) (RootedForest.singleton (RootedTree.ofPTree t))) =
        coproductRight R
          (ofForest (R := R) (RootedForest.singleton (RootedTree.ofPTree t)))) :
    coproductLeft R = coproductRight R := by
  apply coproductLeft_eq_coproductRight_of_singletons (R := R)
  intro τ
  have hτ : RootedTree.ofPTree (Quotient.out τ) = τ := Quotient.out_eq τ
  simpa [hτ] using h (Quotient.out τ)

theorem coproductLeft_eq_coproductRight_iff_ptree_singletons :
    coproductLeft R = coproductRight R ↔
      ∀ t : PTree,
        coproductLeft R
            (ofForest (R := R) (RootedForest.singleton (RootedTree.ofPTree t))) =
          coproductRight R
            (ofForest (R := R) (RootedForest.singleton (RootedTree.ofPTree t))) := by
  constructor
  · intro h t
    rw [h]
  · exact coproductLeft_eq_coproductRight_of_ptree_singletons (R := R)

theorem coproductLeft_eq_coproductRight_of_ptree_coproductTerms
    (h : ∀ t : PTree,
      ForestTripleTensorAlgebra.sumTerms (R := R)
          (ForestTripleTensorAlgebra.coproductLeftTerms (PTree.coproductTerms t)) =
        ForestTripleTensorAlgebra.sumTerms (R := R)
          (ForestTripleTensorAlgebra.coproductRightTerms (PTree.coproductTerms t))) :
    coproductLeft R = coproductRight R := by
  apply coproductLeft_eq_coproductRight_of_ptree_singletons (R := R)
  intro t
  rw [coproductLeft_ofForest_singleton_ofPTree_eq_sumTerms,
    coproductRight_ofForest_singleton_ofPTree_eq_sumTerms]
  exact h t

theorem coproductLeft_eq_coproductRight_iff_ptree_coproductTerms :
    coproductLeft R = coproductRight R ↔
      ∀ t : PTree,
        ForestTripleTensorAlgebra.sumTerms (R := R)
            (ForestTripleTensorAlgebra.coproductLeftTerms (PTree.coproductTerms t)) =
          ForestTripleTensorAlgebra.sumTerms (R := R)
            (ForestTripleTensorAlgebra.coproductRightTerms (PTree.coproductTerms t)) := by
  constructor
  · intro h t
    have hsingle :=
      (coproductLeft_eq_coproductRight_iff_ptree_singletons (R := R)).1 h t
    rw [coproductLeft_ofForest_singleton_ofPTree_eq_sumTerms,
      coproductRight_ofForest_singleton_ofPTree_eq_sumTerms] at hsingle
    exact hsingle
  · exact coproductLeft_eq_coproductRight_of_ptree_coproductTerms (R := R)

theorem coproductLeft_eq_coproductRight_of_nestedCoproductTerms
    (h : ∀ t : PTree,
      ForestTripleTensorAlgebra.sumTerms (R := R) (PTree.nestedCoproductLeftTerms t) =
        ForestTripleTensorAlgebra.sumTerms (R := R) (PTree.nestedCoproductRightTerms t)) :
    coproductLeft R = coproductRight R := by
  apply coproductLeft_eq_coproductRight_of_ptree_coproductTerms (R := R)
  intro t
  rw [← ForestTripleTensorAlgebra.sumTerms_nestedCoproductLeftTerms (R := R) t,
    ← ForestTripleTensorAlgebra.sumTerms_nestedCoproductRightTerms (R := R) t]
  exact h t

theorem coproductLeft_eq_coproductRight_iff_nestedCoproductTerms :
    coproductLeft R = coproductRight R ↔
      ∀ t : PTree,
        ForestTripleTensorAlgebra.sumTerms (R := R) (PTree.nestedCoproductLeftTerms t) =
          ForestTripleTensorAlgebra.sumTerms (R := R)
            (PTree.nestedCoproductRightTerms t) := by
  constructor
  · intro h t
    have hterms :=
      (coproductLeft_eq_coproductRight_iff_ptree_coproductTerms (R := R)).1 h t
    rw [ForestTripleTensorAlgebra.sumTerms_nestedCoproductLeftTerms,
      ForestTripleTensorAlgebra.sumTerms_nestedCoproductRightTerms]
    exact hterms
  · exact coproductLeft_eq_coproductRight_of_nestedCoproductTerms (R := R)

theorem coproductLeft_eq_coproductRight_of_nestedCoproductTerms_perm
    (h : ∀ t : PTree,
      (PTree.nestedCoproductLeftTerms t).Perm (PTree.nestedCoproductRightTerms t)) :
    coproductLeft R = coproductRight R :=
  coproductLeft_eq_coproductRight_of_nestedCoproductTerms (R := R) fun t =>
    ForestTripleTensorAlgebra.sumTerms_perm (R := R) (h t)

theorem coproductLeft_eq_coproductRight_of_ptree_coproductTerms_perm
    (h : ∀ t : PTree,
      (ForestTripleTensorAlgebra.coproductLeftTerms (PTree.coproductTerms t)).Perm
        (ForestTripleTensorAlgebra.coproductRightTerms (PTree.coproductTerms t))) :
    coproductLeft R = coproductRight R :=
  coproductLeft_eq_coproductRight_of_nestedCoproductTerms_perm (R := R) fun t =>
    (ForestTripleTensorAlgebra.nestedCoproductTerms_perm_iff_coproductTerms_perm t).2 (h t)

theorem coproductLeft_eq_coproductRight_of_rootedForest_coproductTerms_perm
    (h : ∀ φ : RootedForest,
      (ForestTripleTensorAlgebra.coproductLeftTerms (RootedForest.coproductTerms φ)).Perm
        (ForestTripleTensorAlgebra.coproductRightTerms (RootedForest.coproductTerms φ))) :
    coproductLeft R = coproductRight R := by
  apply coproductLeft_eq_coproductRight_of_ptree_coproductTerms_perm (R := R)
  intro t
  have hsingle := h (RootedForest.singleton (RootedTree.ofPTree t))
  have hterms := RootedForest.coproductTerms_singleton_ofPTree_perm t
  exact (ForestTripleTensorAlgebra.coproductLeftTerms_perm hterms).symm.trans
    (hsingle.trans (ForestTripleTensorAlgebra.coproductRightTerms_perm hterms))

theorem coproductLeft_eq_coproductRight :
    coproductLeft R = coproductRight R :=
  coproductLeft_eq_coproductRight_of_nestedCoproductTerms_perm (R := R)
    ForestTripleTensorAlgebra.nestedCoproductTerms_left_right_perm

theorem counitLeft_coproduct :
    (ForestTensorAlgebra.counitLeft (R := R)).comp (coproduct R) =
      AlgHom.id R (ForestAlgebra R) := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext)
  apply MonoidHom.ext
  intro φ
  simpa [coproduct, coproductMonoidHom, ofForest] using
    RootedForest.counitLeft_coproduct (R := R) (Multiplicative.toAdd φ)

theorem counitRight_coproduct :
    (ForestTensorAlgebra.counitRight (R := R)).comp (coproduct R) =
      AlgHom.id R (ForestAlgebra R) := by
  refine AddMonoidAlgebra.algHom_ext' ?_ (by ext)
  apply MonoidHom.ext
  intro φ
  simpa [coproduct, coproductMonoidHom, ofForest] using
    RootedForest.counitRight_coproduct (R := R) (Multiplicative.toAdd φ)

end

end ForestAlgebra

end HopfAlgebras
