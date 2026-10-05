/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.CharacterConvolution
import HopfAlgebras.Hopf.LabelledCoproduct

/-!
# Labelled Character Convolution

The convolution of labelled forest-algebra characters induced by the
labelled BCK coproduct, with unit (the counit), associativity, the
coefficient functions on labelled trees and forests, and the erase-labels
bridges to the unlabelled character convolution.
-/

namespace HopfAlgebras

universe u v w

namespace PLTree

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- Evaluate one labelled tensor-coded coproduct term against two characters. -/
def evalCoproductTerm (χ ψ : LForestAlgebra.Character α R)
    (term : LRootedForest α × LRootedForest α) : R :=
  χ.evalForest term.1 * ψ.evalForest term.2

@[simp]
theorem evalCoproductTerm_zero (χ ψ : LForestAlgebra.Character α R) :
    evalCoproductTerm χ ψ (0 : LRootedForest α × LRootedForest α) = 1 := by
  simp [evalCoproductTerm]

@[simp]
theorem evalCoproductTerm_add (χ ψ : LForestAlgebra.Character α R)
    (x y : LRootedForest α × LRootedForest α) :
    evalCoproductTerm χ ψ (x + y) =
      evalCoproductTerm χ ψ x * evalCoproductTerm χ ψ y := by
  rcases x with ⟨φ₁, ψ₁⟩
  rcases y with ⟨φ₂, ψ₂⟩
  simp [evalCoproductTerm]
  ac_rfl

/-- Evaluate a finite list of labelled tensor-coded coproduct terms. -/
def evalCoproductTerms (χ ψ : LForestAlgebra.Character α R)
    (terms : List (LRootedForest α × LRootedForest α)) : R :=
  (terms.map (evalCoproductTerm χ ψ)).sum

@[simp]
theorem evalCoproductTerms_nil (χ ψ : LForestAlgebra.Character α R) :
    evalCoproductTerms χ ψ [] = 0 :=
  rfl

@[simp]
theorem evalCoproductTerms_cons (χ ψ : LForestAlgebra.Character α R)
    (term : LRootedForest α × LRootedForest α)
    (terms : List (LRootedForest α × LRootedForest α)) :
    evalCoproductTerms χ ψ (term :: terms) =
      evalCoproductTerm χ ψ term + evalCoproductTerms χ ψ terms :=
  rfl

theorem evalCoproductTerms_append (χ ψ : LForestAlgebra.Character α R)
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    evalCoproductTerms χ ψ (xs ++ ys) =
      evalCoproductTerms χ ψ xs + evalCoproductTerms χ ψ ys := by
  simp [evalCoproductTerms, List.map_append]

theorem evalCoproductTerms_perm (χ ψ : LForestAlgebra.Character α R)
    {xs ys : List (LRootedForest α × LRootedForest α)} (h : xs.Perm ys) :
    evalCoproductTerms χ ψ xs = evalCoproductTerms χ ψ ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem evalCoproductTerms_map_add_left (χ ψ : LForestAlgebra.Character α R)
    (x : LRootedForest α × LRootedForest α) :
    ∀ ys : List (LRootedForest α × LRootedForest α),
      evalCoproductTerms χ ψ (ys.map fun y => x + y) =
        evalCoproductTerm χ ψ x * evalCoproductTerms χ ψ ys
  | [] => by
      simp [evalCoproductTerms]
  | y :: ys => by
      rw [
        List.map_cons,
        evalCoproductTerms_cons,
        evalCoproductTerms_cons,
        evalCoproductTerms_map_add_left χ ψ x ys,
        evalCoproductTerm_add,
        ← mul_add
      ]

theorem evalCoproductTerms_multiply (χ ψ : LForestAlgebra.Character α R)
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    evalCoproductTerms χ ψ (multiplyCoproductTerms xs ys) =
      evalCoproductTerms χ ψ xs * evalCoproductTerms χ ψ ys := by
  induction xs with
  | nil =>
      simp [multiplyCoproductTerms, evalCoproductTerms]
  | cons x xs ih =>
      rw [multiplyCoproductTerms]
      rw [multiplyCoproductTerms] at ih
      simp only [List.flatMap_cons]
      rw [evalCoproductTerms_append, ih, evalCoproductTerms_cons]
      change
        evalCoproductTerms χ ψ (ys.map fun y => x + y) +
            evalCoproductTerms χ ψ xs * evalCoproductTerms χ ψ ys =
          (evalCoproductTerm χ ψ x + evalCoproductTerms χ ψ xs) *
            evalCoproductTerms χ ψ ys
      rw [evalCoproductTerms_map_add_left, add_mul]

/-- Evaluate one labelled triple tensor-coded term against three characters. -/
def evalTripleCoproductTerm (χ ψ η : LForestAlgebra.Character α R)
    (term : LRootedForest α × LRootedForest α × LRootedForest α) : R :=
  χ.evalForest term.1 * ψ.evalForest term.2.1 * η.evalForest term.2.2

@[simp]
theorem evalTripleCoproductTerm_zero (χ ψ η : LForestAlgebra.Character α R) :
    evalTripleCoproductTerm χ ψ η
        (0 : LRootedForest α × LRootedForest α × LRootedForest α) = 1 := by
  simp [evalTripleCoproductTerm]

@[simp]
theorem evalTripleCoproductTerm_add
    (χ ψ η : LForestAlgebra.Character α R)
    (x y : LRootedForest α × LRootedForest α × LRootedForest α) :
    evalTripleCoproductTerm χ ψ η (x + y) =
      evalTripleCoproductTerm χ ψ η x *
        evalTripleCoproductTerm χ ψ η y := by
  rcases x with ⟨φ₁, ψ₁, η₁⟩
  rcases y with ⟨φ₂, ψ₂, η₂⟩
  simp [evalTripleCoproductTerm]
  ac_rfl

/-- Evaluate a finite list of labelled triple tensor-coded terms. -/
def evalTripleCoproductTerms (χ ψ η : LForestAlgebra.Character α R)
    (terms : List (LRootedForest α × LRootedForest α × LRootedForest α)) : R :=
  (terms.map (evalTripleCoproductTerm χ ψ η)).sum

@[simp]
theorem evalTripleCoproductTerms_nil
    (χ ψ η : LForestAlgebra.Character α R) :
    evalTripleCoproductTerms χ ψ η [] = 0 :=
  rfl

@[simp]
theorem evalTripleCoproductTerms_cons
    (χ ψ η : LForestAlgebra.Character α R)
    (term : LRootedForest α × LRootedForest α × LRootedForest α)
    (terms : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    evalTripleCoproductTerms χ ψ η (term :: terms) =
      evalTripleCoproductTerm χ ψ η term +
        evalTripleCoproductTerms χ ψ η terms :=
  rfl

theorem evalTripleCoproductTerms_append
    (χ ψ η : LForestAlgebra.Character α R)
    (xs ys : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    evalTripleCoproductTerms χ ψ η (xs ++ ys) =
      evalTripleCoproductTerms χ ψ η xs +
        evalTripleCoproductTerms χ ψ η ys := by
  simp [evalTripleCoproductTerms, List.map_append]

theorem evalTripleCoproductTerms_perm
    (χ ψ η : LForestAlgebra.Character α R)
    {xs ys : List (LRootedForest α × LRootedForest α × LRootedForest α)}
    (h : xs.Perm ys) :
    evalTripleCoproductTerms χ ψ η xs =
      evalTripleCoproductTerms χ ψ η ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem evalTripleCoproductTerms_map_add_left
    (χ ψ η : LForestAlgebra.Character α R)
    (x : LRootedForest α × LRootedForest α × LRootedForest α) :
    ∀ ys : List (LRootedForest α × LRootedForest α × LRootedForest α),
      evalTripleCoproductTerms χ ψ η (ys.map fun y => x + y) =
        evalTripleCoproductTerm χ ψ η x *
          evalTripleCoproductTerms χ ψ η ys
  | [] => by
      simp [evalTripleCoproductTerms]
  | y :: ys => by
      rw [
        List.map_cons,
        evalTripleCoproductTerms_cons,
        evalTripleCoproductTerms_cons,
        evalTripleCoproductTerms_map_add_left χ ψ η x ys,
        evalTripleCoproductTerm_add,
        ← mul_add
      ]

theorem evalTripleCoproductTerms_multiply
    (χ ψ η : LForestAlgebra.Character α R)
    (xs ys : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    evalTripleCoproductTerms χ ψ η
        (LForestTripleTensorAlgebra.multiplyTerms xs ys) =
      evalTripleCoproductTerms χ ψ η xs *
        evalTripleCoproductTerms χ ψ η ys := by
  induction xs with
  | nil =>
      simp [LForestTripleTensorAlgebra.multiplyTerms, evalTripleCoproductTerms]
  | cons x xs ih =>
      rw [LForestTripleTensorAlgebra.multiplyTerms]
      rw [LForestTripleTensorAlgebra.multiplyTerms] at ih
      simp only [List.flatMap_cons]
      rw [evalTripleCoproductTerms_append, ih, evalTripleCoproductTerms_cons]
      rw [evalTripleCoproductTerms_map_add_left, add_mul]

theorem evalCoproductTerms_cut_forall₂_perm
    (χ ψ : LForestAlgebra.Character α R) :
    ∀ {cs ds : List (Cut α)}, List.Forall₂ Cut.Perm cs ds →
      evalCoproductTerms χ ψ (cs.map fun c => (c.prunedForest, c.trunkForest)) =
        evalCoproductTerms χ ψ (ds.map fun d => (d.prunedForest, d.trunkForest))
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      simp [Cut.Perm.coproductTerm_eq h, evalCoproductTerms_cut_forall₂_perm χ ψ hs]

theorem evalCoproductTerms_cut_listRelPerm
    (χ ψ : LForestAlgebra.Character α R) {cs ds : List (Cut α)}
    (h : PTree.ListRelPerm Cut.Perm cs ds) :
    evalCoproductTerms χ ψ (cs.map fun c => (c.prunedForest, c.trunkForest)) =
      evalCoproductTerms χ ψ (ds.map fun d => (d.prunedForest, d.trunkForest)) := by
  rcases h with ⟨cs', hp, hrel⟩
  rw [evalCoproductTerms_perm χ ψ (hp.map _)]
  exact evalCoproductTerms_cut_forall₂_perm χ ψ hrel

/-- Pulling characters back along label erasure commutes with one coproduct-term evaluation. -/
theorem evalCoproductTerm_comapEraseLabels
    (χ ψ : ForestAlgebra.Character R) (term : LRootedForest α × LRootedForest α) :
    evalCoproductTerm
        (LForestAlgebra.Character.comapEraseLabels (α := α) χ)
        (LForestAlgebra.Character.comapEraseLabels (α := α) ψ) term =
      PTree.evalCoproductTerm χ ψ (eraseCoproductTerm term) := by
  simp [evalCoproductTerm, PTree.evalCoproductTerm, eraseCoproductTerm,
    ForestAlgebra.Character.evalForest]

/-- Pulling characters back along label erasure commutes with finite coproduct evaluation. -/
theorem evalCoproductTerms_comapEraseLabels
    (χ ψ : ForestAlgebra.Character R) :
    ∀ terms : List (LRootedForest α × LRootedForest α),
      evalCoproductTerms
          (LForestAlgebra.Character.comapEraseLabels (α := α) χ)
          (LForestAlgebra.Character.comapEraseLabels (α := α) ψ) terms =
        PTree.evalCoproductTerms χ ψ (terms.map eraseCoproductTerm)
  | [] => by
      simp [evalCoproductTerms, PTree.evalCoproductTerms]
  | term :: terms => by
      rw [evalCoproductTerms_cons]
      simp only [List.map_cons]
      rw [PTree.evalCoproductTerms_cons, evalCoproductTerm_comapEraseLabels,
        evalCoproductTerms_comapEraseLabels χ ψ terms]

/-- Pulling characters back along relabelling commutes with one coproduct-term evaluation. -/
theorem evalCoproductTerm_comapMapLabels {β : Type w}
    (f : α → β) (χ ψ : LForestAlgebra.Character β R)
    (term : LRootedForest α × LRootedForest α) :
    evalCoproductTerm
        (LForestAlgebra.Character.comapMapLabels f χ)
        (LForestAlgebra.Character.comapMapLabels f ψ) term =
      evalCoproductTerm χ ψ (mapCoproductTerm f term) := by
  simp [evalCoproductTerm, mapCoproductTerm]

/-- Pulling characters back along relabelling commutes with finite coproduct evaluation. -/
theorem evalCoproductTerms_comapMapLabels {β : Type w}
    (f : α → β) (χ ψ : LForestAlgebra.Character β R) :
    ∀ terms : List (LRootedForest α × LRootedForest α),
      evalCoproductTerms
          (LForestAlgebra.Character.comapMapLabels f χ)
          (LForestAlgebra.Character.comapMapLabels f ψ) terms =
        evalCoproductTerms χ ψ (terms.map (mapCoproductTerm f))
  | [] => by
      simp [evalCoproductTerms]
  | term :: terms => by
      rw [evalCoproductTerms_cons]
      simp only [List.map_cons]
      rw [evalCoproductTerms_cons, evalCoproductTerm_comapMapLabels,
        evalCoproductTerms_comapMapLabels f χ ψ terms]

/-- Pulling characters back along constant labelling commutes with one coproduct-term evaluation. -/
theorem evalCoproductTerm_comapConstLabel
    (x : α) (χ ψ : LForestAlgebra.Character α R)
    (term : RootedForest × RootedForest) :
    PTree.evalCoproductTerm
        (LForestAlgebra.Character.comapConstLabel x χ)
        (LForestAlgebra.Character.comapConstLabel x ψ) term =
      evalCoproductTerm χ ψ (constLabelCoproductTerm x term) := by
  simp [PTree.evalCoproductTerm, evalCoproductTerm, constLabelCoproductTerm,
    ForestAlgebra.Character.evalForest, LForestAlgebra.Character.evalForest,
    LForestAlgebra.Character.comapConstLabel]

/-- Pulling characters back along constant labelling commutes with finite coproduct evaluation. -/
theorem evalCoproductTerms_comapConstLabel
    (x : α) (χ ψ : LForestAlgebra.Character α R) :
    ∀ terms : List (RootedForest × RootedForest),
      PTree.evalCoproductTerms
          (LForestAlgebra.Character.comapConstLabel x χ)
          (LForestAlgebra.Character.comapConstLabel x ψ) terms =
        evalCoproductTerms χ ψ (terms.map (constLabelCoproductTerm x))
  | [] => by
      simp [PTree.evalCoproductTerms, evalCoproductTerms]
  | term :: terms => by
      rw [PTree.evalCoproductTerms_cons]
      simp only [List.map_cons]
      rw [evalCoproductTerms_cons, evalCoproductTerm_comapConstLabel,
        evalCoproductTerms_comapConstLabel x χ ψ terms]

/-- The convolution coefficient of two characters on a planar labelled rooted tree. -/
def convolutionCoeff (χ ψ : LForestAlgebra.Character α R) (t : PLTree α) : R :=
  evalCoproductTerms χ ψ (coproductTerms t)

theorem convolutionCoeff_eq_of_cuts_listRelPerm
    (χ ψ : LForestAlgebra.Character α R) {t u : PLTree α}
    (h : PTree.ListRelPerm Cut.Perm (cuts t) (cuts u)) :
    convolutionCoeff χ ψ t = convolutionCoeff χ ψ u := by
  rw [convolutionCoeff, convolutionCoeff, coproductTerms, coproductTerms]
  exact evalCoproductTerms_cut_listRelPerm χ ψ h

theorem convolutionCoeff_eq_of_rootCuts_listRelPerm
    (χ ψ : LForestAlgebra.Character α R) {t u : PLTree α} (htu : PLTree.Perm t u)
    (hroot : PTree.ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) :
    convolutionCoeff χ ψ t = convolutionCoeff χ ψ u :=
  convolutionCoeff_eq_of_cuts_listRelPerm χ ψ
    (cuts_listRelPerm_of_rootCuts htu hroot)

theorem convolutionCoeff_perm (χ ψ : LForestAlgebra.Character α R)
    {t u : PLTree α} (h : PLTree.Perm t u) :
    convolutionCoeff χ ψ t = convolutionCoeff χ ψ u :=
  convolutionCoeff_eq_of_cuts_listRelPerm χ ψ (cuts_listRelPerm_of_perm h)

/-- Multiplicative extension of labelled convolution coefficients to planar labelled forests. -/
def convolutionForestCoeff (χ ψ : LForestAlgebra.Character α R) (ts : List (PLTree α)) : R :=
  evalCoproductTerms χ ψ (coproductTermsList ts)

/-- Labelled convolution with characters pulled back by erasure is unlabelled convolution. -/
theorem convolutionCoeff_comapEraseLabels
    (χ ψ : ForestAlgebra.Character R) (t : PLTree α) :
    convolutionCoeff
        (LForestAlgebra.Character.comapEraseLabels (α := α) χ)
        (LForestAlgebra.Character.comapEraseLabels (α := α) ψ) t =
      PTree.convolutionCoeff χ ψ (PLTree.erase t) := by
  rw [convolutionCoeff, PTree.convolutionCoeff]
  rw [evalCoproductTerms_comapEraseLabels]
  rw [coproductTerms_erase]

/-- Labelled forest convolution pulled back by erasure is unlabelled forest convolution. -/
theorem convolutionForestCoeff_comapEraseLabels
    (χ ψ : ForestAlgebra.Character R) (ts : List (PLTree α)) :
    convolutionForestCoeff
        (LForestAlgebra.Character.comapEraseLabels (α := α) χ)
        (LForestAlgebra.Character.comapEraseLabels (α := α) ψ) ts =
      PTree.convolutionForestCoeff χ ψ (ts.map PLTree.erase) := by
  rw [convolutionForestCoeff, PTree.convolutionForestCoeff]
  rw [evalCoproductTerms_comapEraseLabels]
  rw [coproductTermsList_erase]

theorem convolutionCoeff_comapMapLabels {β : Type w}
    (f : α → β) (χ ψ : LForestAlgebra.Character β R) (t : PLTree α) :
    convolutionCoeff
        (LForestAlgebra.Character.comapMapLabels f χ)
        (LForestAlgebra.Character.comapMapLabels f ψ) t =
      convolutionCoeff χ ψ (PLTree.map f t) := by
  rw [convolutionCoeff, convolutionCoeff]
  rw [evalCoproductTerms_comapMapLabels]
  rw [coproductTerms_map]

theorem convolutionForestCoeff_comapMapLabels {β : Type w}
    (f : α → β) (χ ψ : LForestAlgebra.Character β R)
    (ts : List (PLTree α)) :
    convolutionForestCoeff
        (LForestAlgebra.Character.comapMapLabels f χ)
        (LForestAlgebra.Character.comapMapLabels f ψ) ts =
      convolutionForestCoeff χ ψ (ts.map (PLTree.map f)) := by
  rw [convolutionForestCoeff, convolutionForestCoeff]
  rw [evalCoproductTerms_comapMapLabels]
  rw [coproductTermsList_map]

theorem convolutionCoeff_comapConstLabel
    (x : α) (χ ψ : LForestAlgebra.Character α R) (t : PTree) :
    PTree.convolutionCoeff
        (LForestAlgebra.Character.comapConstLabel x χ)
        (LForestAlgebra.Character.comapConstLabel x ψ) t =
      convolutionCoeff χ ψ (PLTree.constLabel x t) := by
  rw [PTree.convolutionCoeff, convolutionCoeff]
  rw [evalCoproductTerms_comapConstLabel]
  rw [coproductTerms_constLabel]

theorem convolutionForestCoeff_comapConstLabel
    (x : α) (χ ψ : LForestAlgebra.Character α R)
    (ts : List PTree) :
    PTree.convolutionForestCoeff
        (LForestAlgebra.Character.comapConstLabel x χ)
        (LForestAlgebra.Character.comapConstLabel x ψ) ts =
      convolutionForestCoeff χ ψ (ts.map (PLTree.constLabel x)) := by
  rw [PTree.convolutionForestCoeff, convolutionForestCoeff]
  rw [evalCoproductTerms_comapConstLabel]
  rw [coproductTermsList_constLabel]

/-- If two labelled characters ignore labels, their planar convolution does too. -/
theorem convolutionCoeff_labelInvariant_eq [Nonempty α]
    {χ ψ : LForestAlgebra.Character α R}
    (hχ : LForestAlgebra.Character.LabelInvariant χ)
    (hψ : LForestAlgebra.Character.LabelInvariant ψ)
    {t u : PLTree α} (htu : PLTree.erase t = PLTree.erase u) :
    convolutionCoeff χ ψ t = convolutionCoeff χ ψ u := by
  let x := Classical.choice (inferInstance : Nonempty α)
  have hχ' := hχ.comapEraseLabels_comapConstLabel x
  have hψ' := hψ.comapEraseLabels_comapConstLabel x
  rw [← hχ', ← hψ']
  rw [convolutionCoeff_comapEraseLabels, convolutionCoeff_comapEraseLabels, htu]

/-- If two labelled characters ignore labels, their planar forest convolution does too. -/
theorem convolutionForestCoeff_labelInvariant_eq [Nonempty α]
    {χ ψ : LForestAlgebra.Character α R}
    (hχ : LForestAlgebra.Character.LabelInvariant χ)
    (hψ : LForestAlgebra.Character.LabelInvariant ψ)
    {ts us : List (PLTree α)} (hts : ts.map PLTree.erase = us.map PLTree.erase) :
    convolutionForestCoeff χ ψ ts = convolutionForestCoeff χ ψ us := by
  let x := Classical.choice (inferInstance : Nonempty α)
  have hχ' := hχ.comapEraseLabels_comapConstLabel x
  have hψ' := hψ.comapEraseLabels_comapConstLabel x
  rw [← hχ', ← hψ']
  rw [convolutionForestCoeff_comapEraseLabels, convolutionForestCoeff_comapEraseLabels, hts]

@[simp]
theorem convolutionForestCoeff_nil (χ ψ : LForestAlgebra.Character α R) :
    convolutionForestCoeff χ ψ [] = 1 := by
  simp [convolutionForestCoeff, coproductTermsList, evalCoproductTerms, evalCoproductTerm]

@[simp]
theorem convolutionForestCoeff_cons (χ ψ : LForestAlgebra.Character α R)
    (t : PLTree α) (ts : List (PLTree α)) :
    convolutionForestCoeff χ ψ (t :: ts) =
      convolutionCoeff χ ψ t * convolutionForestCoeff χ ψ ts := by
  simp [
    convolutionForestCoeff,
    convolutionCoeff,
    coproductTermsList,
    evalCoproductTerms_multiply
  ]

theorem convolutionForestCoeff_perm (χ ψ : LForestAlgebra.Character α R)
    {ts us : List (PLTree α)} (h : ts.Perm us) :
    convolutionForestCoeff χ ψ ts = convolutionForestCoeff χ ψ us := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ =>
      simp
      ac_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem convolutionForestCoeff_forall₂_perm (χ ψ : LForestAlgebra.Character α R) :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ PLTree.Perm ts us →
      convolutionForestCoeff χ ψ ts = convolutionForestCoeff χ ψ us
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
      rw [convolutionForestCoeff_cons, convolutionForestCoeff_cons,
        convolutionCoeff_perm χ ψ h, convolutionForestCoeff_forall₂_perm χ ψ hs]

private theorem evalRootCuts_unit_right (χ : LForestAlgebra.Character α R)
    (cuts : List (RootCut α)) :
    evalCoproductTerms χ (LForestAlgebra.counit α R)
      (cuts.map fun c =>
        ((c.pruned.map LRootedTree.ofPLTree : LRootedForest α),
          LRootedForest.singleton (LRootedTree.ofPLTree c.trunk))) = 0 := by
  induction cuts with
  | nil =>
      simp
  | cons c cuts ih =>
      simp [evalCoproductTerm, LForestAlgebra.Character.evalForest,
        LForestAlgebra.counit_ofForest,
        LForestAlgebra.counitCoeff_ne_zero (LRootedForest.singleton_ne_zero _), ih]

private theorem evalRootCuts_unit_right_tree
    (χ : LForestAlgebra.Character α R) (t : PLTree α) :
    evalCoproductTerms χ (LForestAlgebra.counit α R)
      ((rootCuts t).map fun c =>
        ((c.pruned.map LRootedTree.ofPLTree : LRootedForest α),
          LRootedForest.singleton (LRootedTree.ofPLTree c.trunk))) = 0 :=
  evalRootCuts_unit_right χ (rootCuts t)

theorem convolutionCoeff_unit_right (χ : LForestAlgebra.Character α R) (t : PLTree α) :
    convolutionCoeff χ (LForestAlgebra.counit α R) t =
      χ.evalForest (LRootedForest.singleton (LRootedTree.ofPLTree t)) := by
  rw [convolutionCoeff, coproductTerms, cuts]
  simp only [List.map_append, List.map_map]
  rw [evalCoproductTerms_append]
  change
    evalCoproductTerms χ (LForestAlgebra.counit α R)
        ((rootCuts t).map fun c =>
          ((c.pruned.map LRootedTree.ofPLTree : LRootedForest α),
            LRootedForest.singleton (LRootedTree.ofPLTree c.trunk))) +
      evalCoproductTerms χ (LForestAlgebra.counit α R)
        (List.map (fun c : Cut α => (c.prunedForest, c.trunkForest))
          ([{ pruned := [t], trunk? := none }] : List (Cut α))) =
    χ.evalForest (LRootedForest.singleton (LRootedTree.ofPLTree t))
  rw [evalRootCuts_unit_right_tree]
  simp [evalCoproductTerms, evalCoproductTerm, Cut.prunedForest, Cut.trunkForest,
    LForestAlgebra.Character.evalForest, LRootedForest.singleton]

private theorem evalRootCuts_unit_left (χ : LForestAlgebra.Character α R)
    (cuts : List (RootCut α)) :
    evalCoproductTerms (LForestAlgebra.counit α R) χ
      (cuts.map fun c =>
        ((c.pruned.map LRootedTree.ofPLTree : LRootedForest α),
          LRootedForest.singleton (LRootedTree.ofPLTree c.trunk))) =
      ((cuts.filterMap RootCut.noPrunedTrunk?).map fun trunk =>
        χ.evalForest (LRootedForest.singleton (LRootedTree.ofPLTree trunk))).sum := by
  induction cuts with
  | nil =>
      simp
  | cons c cuts ih =>
      cases hpruned : c.pruned with
      | nil =>
          simp [evalCoproductTerm, LForestAlgebra.Character.evalForest,
            RootCut.noPrunedTrunk?, hpruned, ih]
      | cons p ps =>
          have hne :
              (((LRootedTree.ofPLTree p :: ps.map LRootedTree.ofPLTree) :
                  List (LRootedTree α)) : LRootedForest α) ≠ 0 := by
            exact (LRootedForest.order_pos_iff_ne_zero _).1
              (LRootedForest.order_coe_cons_pos (LRootedTree.ofPLTree p)
                (ps.map LRootedTree.ofPLTree))
          simp [evalCoproductTerm, LForestAlgebra.Character.evalForest,
            RootCut.noPrunedTrunk?, hpruned, ih, LForestAlgebra.counit_ofForest,
            LForestAlgebra.counitCoeff_ne_zero hne]

private theorem evalRootCuts_unit_left_tree
    (χ : LForestAlgebra.Character α R) (t : PLTree α) :
    evalCoproductTerms (LForestAlgebra.counit α R) χ
      ((rootCuts t).map fun c =>
        ((c.pruned.map LRootedTree.ofPLTree : LRootedForest α),
          LRootedForest.singleton (LRootedTree.ofPLTree c.trunk))) =
      χ.evalForest (LRootedForest.singleton (LRootedTree.ofPLTree t)) := by
  rw [evalRootCuts_unit_left, rootCuts_noPrunedTrunks]
  simp

theorem convolutionCoeff_unit_left (χ : LForestAlgebra.Character α R) (t : PLTree α) :
    convolutionCoeff (LForestAlgebra.counit α R) χ t =
      χ.evalForest (LRootedForest.singleton (LRootedTree.ofPLTree t)) := by
  rw [convolutionCoeff, coproductTerms, cuts]
  simp only [List.map_append, List.map_map]
  rw [evalCoproductTerms_append]
  change
    evalCoproductTerms (LForestAlgebra.counit α R) χ
        ((rootCuts t).map fun c =>
          ((c.pruned.map LRootedTree.ofPLTree : LRootedForest α),
            LRootedForest.singleton (LRootedTree.ofPLTree c.trunk))) +
      evalCoproductTerms (LForestAlgebra.counit α R) χ
        (List.map (fun c : Cut α => (c.prunedForest, c.trunkForest))
          ([{ pruned := [t], trunk? := none }] : List (Cut α))) =
    χ.evalForest (LRootedForest.singleton (LRootedTree.ofPLTree t))
  rw [evalRootCuts_unit_left_tree]
  simp [evalCoproductTerms, evalCoproductTerm, Cut.prunedForest, Cut.trunkForest,
    LForestAlgebra.Character.evalForest,
    LForestAlgebra.counit_ofForest,
    LForestAlgebra.counitCoeff_ne_zero
      (show ({LRootedTree.ofPLTree t} : LRootedForest α) ≠ 0 by simp)]

theorem convolutionForestCoeff_unit_right (χ : LForestAlgebra.Character α R)
    (ts : List (PLTree α)) :
    convolutionForestCoeff χ (LForestAlgebra.counit α R) ts =
      χ.evalForest (ts.map LRootedTree.ofPLTree : LRootedForest α) := by
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      rw [convolutionForestCoeff_cons, convolutionCoeff_unit_right, ih]
      rw [← LForestAlgebra.Character.evalForest_add]
      simp [LRootedForest.singleton]

theorem convolutionForestCoeff_unit_left (χ : LForestAlgebra.Character α R)
    (ts : List (PLTree α)) :
    convolutionForestCoeff (LForestAlgebra.counit α R) χ ts =
      χ.evalForest (ts.map LRootedTree.ofPLTree : LRootedForest α) := by
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      rw [convolutionForestCoeff_cons, convolutionCoeff_unit_left, ih]
      rw [← LForestAlgebra.Character.evalForest_add]
      simp [LRootedForest.singleton]

end

end PLTree

namespace LForestTensorAlgebra

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

private def evalByCharactersMonoidHom
    (χ ψ : LForestAlgebra.Character α R) :
    Multiplicative (LRootedForest α × LRootedForest α) →* R where
  toFun term := PLTree.evalCoproductTerm χ ψ (Multiplicative.toAdd term)
  map_one' := by
    change PLTree.evalCoproductTerm χ ψ (0 : LRootedForest α × LRootedForest α) = 1
    simp
  map_mul' x y := by
    change
      PLTree.evalCoproductTerm χ ψ
          (Multiplicative.toAdd (x * y)) =
        PLTree.evalCoproductTerm χ ψ (Multiplicative.toAdd x) *
          PLTree.evalCoproductTerm χ ψ (Multiplicative.toAdd y)
    simp

/-- Evaluate tensor-coded labelled forest algebra terms by a pair of characters. -/
def evalByCharacters (χ ψ : LForestAlgebra.Character α R) :
    LForestTensorAlgebra α R →ₐ[R] R :=
  (AddMonoidAlgebra.lift R R (LRootedForest α × LRootedForest α))
    (evalByCharactersMonoidHom χ ψ)

@[simp]
theorem evalByCharacters_ofPair (χ ψ : LForestAlgebra.Character α R)
    (term : LRootedForest α × LRootedForest α) :
    evalByCharacters χ ψ (ofPair (R := R) term) =
      PLTree.evalCoproductTerm χ ψ term := by
  simp [evalByCharacters, ofPair, evalByCharactersMonoidHom]

theorem evalByCharacters_sumTerms (χ ψ : LForestAlgebra.Character α R)
    (terms : List (LRootedForest α × LRootedForest α)) :
    evalByCharacters χ ψ (sumTerms (R := R) terms) =
      PLTree.evalCoproductTerms χ ψ terms := by
  induction terms with
  | nil =>
      simp [sumTerms, PLTree.evalCoproductTerms]
  | cons term terms ih =>
      rw [sumTerms_cons, map_add, ih]
      simp [PLTree.evalCoproductTerms]

theorem evalByLinearMaps_ofCharacter (χ ψ : LForestAlgebra.Character α R) :
    evalByLinearMaps
        (LForestAlgebra.LinearFunctional.ofCharacter χ)
        (LForestAlgebra.LinearFunctional.ofCharacter ψ) =
      (evalByCharacters χ ψ).toLinearMap := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : LForestTensorAlgebra α R =>
      evalByLinearMaps
          (LForestAlgebra.LinearFunctional.ofCharacter χ)
          (LForestAlgebra.LinearFunctional.ofCharacter ψ) x =
        (evalByCharacters χ ψ).toLinearMap x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps
          (LForestAlgebra.LinearFunctional.ofCharacter χ)
          (LForestAlgebra.LinearFunctional.ofCharacter ψ)
          (ofPair (R := R) term) =
        evalByCharacters χ ψ (ofPair (R := R) term)
    simp [LForestAlgebra.LinearFunctional.ofCharacter, PLTree.evalCoproductTerm,
      LForestAlgebra.Character.evalForest]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

@[simp]
theorem evalByCharacters_labelledCoproduct (χ ψ : LForestAlgebra.Character α R)
    (t : PLTree α) :
    evalByCharacters χ ψ (PLTree.labelledCoproduct (R := R) t) =
      PLTree.convolutionCoeff χ ψ t := by
  rw [PLTree.labelledCoproduct, evalByCharacters_sumTerms]
  rfl

@[simp]
theorem evalByCharacters_labelledCoproductList (χ ψ : LForestAlgebra.Character α R)
    (ts : List (PLTree α)) :
    evalByCharacters χ ψ (PLTree.labelledCoproductList (R := R) ts) =
      PLTree.convolutionForestCoeff χ ψ ts := by
  rw [PLTree.labelledCoproductList, evalByCharacters_sumTerms]
  rfl

end

end LForestTensorAlgebra

namespace LForestTripleTensorAlgebra

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

private def evalByCharactersMonoidHom
    (χ ψ η : LForestAlgebra.Character α R) :
    Multiplicative (LRootedForest α × LRootedForest α × LRootedForest α) →* R where
  toFun term := PLTree.evalTripleCoproductTerm χ ψ η (Multiplicative.toAdd term)
  map_one' := by
    change
      PLTree.evalTripleCoproductTerm χ ψ η
        (0 : LRootedForest α × LRootedForest α × LRootedForest α) = 1
    simp
  map_mul' x y := by
    change
      PLTree.evalTripleCoproductTerm χ ψ η
          (Multiplicative.toAdd (x * y)) =
        PLTree.evalTripleCoproductTerm χ ψ η (Multiplicative.toAdd x) *
          PLTree.evalTripleCoproductTerm χ ψ η (Multiplicative.toAdd y)
    change
      PLTree.evalTripleCoproductTerm χ ψ η
          (Multiplicative.toAdd x + Multiplicative.toAdd y) =
        PLTree.evalTripleCoproductTerm χ ψ η (Multiplicative.toAdd x) *
          PLTree.evalTripleCoproductTerm χ ψ η (Multiplicative.toAdd y)
    simp

/-- Evaluate the labelled triple tensor-coded forest algebra using three characters. -/
def evalByCharacters (χ ψ η : LForestAlgebra.Character α R) :
    LForestTripleTensorAlgebra α R →ₐ[R] R :=
  (AddMonoidAlgebra.lift R R
      (LRootedForest α × LRootedForest α × LRootedForest α))
    (evalByCharactersMonoidHom χ ψ η)

@[simp]
theorem evalByCharacters_ofTriple (χ ψ η : LForestAlgebra.Character α R)
    (term : LRootedForest α × LRootedForest α × LRootedForest α) :
    evalByCharacters χ ψ η (ofTriple (R := R) term) =
      PLTree.evalTripleCoproductTerm χ ψ η term := by
  simp [evalByCharacters, ofTriple, evalByCharactersMonoidHom]

theorem evalByCharacters_sumTerms (χ ψ η : LForestAlgebra.Character α R)
    (terms : List (LRootedForest α × LRootedForest α × LRootedForest α)) :
    evalByCharacters χ ψ η (sumTerms (R := R) terms) =
      PLTree.evalTripleCoproductTerms χ ψ η terms := by
  induction terms with
  | nil =>
      simp [sumTerms, PLTree.evalTripleCoproductTerms]
  | cons term terms ih =>
      rw [
        sumTerms_cons,
        PLTree.evalTripleCoproductTerms_cons,
        map_add,
        evalByCharacters_ofTriple,
        ih
      ]

@[simp]
theorem evalByCharacters_includeLeftPair
    (χ ψ η : LForestAlgebra.Character α R) (x : LForestTensorAlgebra α R) :
    evalByCharacters χ ψ η (includeLeftPair (R := R) x) =
      LForestTensorAlgebra.evalByCharacters χ ψ x := by
  change
    ((evalByCharacters χ ψ η).comp (includeLeftPair (R := R))) x =
      LForestTensorAlgebra.evalByCharacters χ ψ x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext
    (M := LRootedForest α × LRootedForest α) (by
      intro term
      change
        evalByCharacters χ ψ η
            (includeLeftPair (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
          LForestTensorAlgebra.evalByCharacters χ ψ
            (LForestTensorAlgebra.ofPair (R := R) term)
      simp [PLTree.evalTripleCoproductTerm, PLTree.evalCoproductTerm]) (by ext)) x

@[simp]
theorem evalByCharacters_includeRightPair
    (χ ψ η : LForestAlgebra.Character α R) (x : LForestTensorAlgebra α R) :
    evalByCharacters χ ψ η (includeRightPair (R := R) x) =
      LForestTensorAlgebra.evalByCharacters ψ η x := by
  change
    ((evalByCharacters χ ψ η).comp (includeRightPair (R := R))) x =
      LForestTensorAlgebra.evalByCharacters ψ η x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext
    (M := LRootedForest α × LRootedForest α) (by
      intro term
      change
        evalByCharacters χ ψ η
            (includeRightPair (R := R) (LForestTensorAlgebra.ofPair (R := R) term)) =
          LForestTensorAlgebra.evalByCharacters ψ η
            (LForestTensorAlgebra.ofPair (R := R) term)
      simp [PLTree.evalTripleCoproductTerm, PLTree.evalCoproductTerm]) (by ext)) x

end

end LForestTripleTensorAlgebra

namespace LRootedForest

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

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

/-- Character convolution evaluated on a non-planar labelled rooted forest. -/
def convolutionCoeff (χ ψ : LForestAlgebra.Character α R) (φ : LRootedForest α) : R :=
  LForestTensorAlgebra.evalByCharacters χ ψ (LRootedForest.coproduct (R := R) φ)

@[simp]
theorem convolutionCoeff_zero (χ ψ : LForestAlgebra.Character α R) :
    convolutionCoeff χ ψ 0 = 1 := by
  simp [convolutionCoeff]

@[simp]
theorem convolutionCoeff_empty (χ ψ : LForestAlgebra.Character α R) :
    convolutionCoeff χ ψ LRootedForest.empty = 1 := by
  simp [convolutionCoeff, LRootedForest.empty]

@[simp]
theorem convolutionCoeff_singleton (χ ψ : LForestAlgebra.Character α R)
    (τ : LRootedTree α) :
    convolutionCoeff χ ψ (LRootedForest.singleton τ) =
      PLTree.convolutionCoeff χ ψ (Quotient.out τ) := by
  simp [convolutionCoeff]

@[simp]
theorem convolutionCoeff_add (χ ψ : LForestAlgebra.Character α R)
    (φ η : LRootedForest α) :
    convolutionCoeff χ ψ (φ + η) =
      convolutionCoeff χ ψ φ * convolutionCoeff χ ψ η := by
  simp [convolutionCoeff]

theorem convolutionCoeff_comapEraseLabels
    (χ ψ : ForestAlgebra.Character R) (φ : LRootedForest α) :
    convolutionCoeff
        (LForestAlgebra.Character.comapEraseLabels (α := α) χ)
        (LForestAlgebra.Character.comapEraseLabels (α := α) ψ) φ =
      RootedForest.convolutionCoeff χ ψ (LRootedForest.erase φ) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change convolutionCoeff
      (LForestAlgebra.Character.comapEraseLabels (α := α) χ)
      (LForestAlgebra.Character.comapEraseLabels (α := α) ψ) (ts : LRootedForest α) =
    RootedForest.convolutionCoeff χ ψ (LRootedForest.erase (ts : LRootedForest α))
  rw [convolutionCoeff, RootedForest.convolutionCoeff]
  change
    LForestTensorAlgebra.evalByCharacters
        (LForestAlgebra.Character.comapEraseLabels (α := α) χ)
        (LForestAlgebra.Character.comapEraseLabels (α := α) ψ)
        (PLTree.labelledCoproductList (R := R) (ts.map Quotient.out)) =
      ForestTensorAlgebra.evalByCharacters χ ψ
        (PTree.coproductList (R := R) ((ts.map LRootedTree.erase).map Quotient.out))
  rw [LForestTensorAlgebra.evalByCharacters_labelledCoproductList,
    ForestTensorAlgebra.evalByCharacters_coproductList,
    PLTree.convolutionForestCoeff_comapEraseLabels]
  exact PTree.convolutionForestCoeff_forall₂_perm χ ψ (by
    induction ts with
    | nil =>
        exact List.Forall₂.nil
    | cons τ ts ih =>
        exact List.Forall₂.cons (LRootedTree.erase_out_perm τ) ih)

theorem convolutionCoeff_comapMapLabels {β : Type w}
    (f : α → β) (χ ψ : LForestAlgebra.Character β R)
    (φ : LRootedForest α) :
    convolutionCoeff
        (LForestAlgebra.Character.comapMapLabels f χ)
        (LForestAlgebra.Character.comapMapLabels f ψ) φ =
      LRootedForest.convolutionCoeff χ ψ (LRootedForest.mapLabels f φ) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change convolutionCoeff (LForestAlgebra.Character.comapMapLabels f χ)
      (LForestAlgebra.Character.comapMapLabels f ψ) (ts : LRootedForest α) =
    convolutionCoeff χ ψ (LRootedForest.mapLabels f (ts : LRootedForest α))
  rw [convolutionCoeff, convolutionCoeff]
  change
    LForestTensorAlgebra.evalByCharacters
        (LForestAlgebra.Character.comapMapLabels f χ)
        (LForestAlgebra.Character.comapMapLabels f ψ)
        (PLTree.labelledCoproductList (R := R) (ts.map Quotient.out)) =
      LForestTensorAlgebra.evalByCharacters χ ψ
        (PLTree.labelledCoproductList (R := R)
          ((ts.map (LRootedTree.map f)).map Quotient.out))
  rw [LForestTensorAlgebra.evalByCharacters_labelledCoproductList,
    LForestTensorAlgebra.evalByCharacters_labelledCoproductList,
    PLTree.convolutionForestCoeff_comapMapLabels]
  exact PLTree.convolutionForestCoeff_forall₂_perm χ ψ (by
    induction ts with
    | nil =>
        exact List.Forall₂.nil
    | cons τ ts ih =>
        exact List.Forall₂.cons (LRootedTree.map_out_perm f τ) ih)

theorem convolutionCoeff_unit_right (χ : LForestAlgebra.Character α R)
    (φ : LRootedForest α) :
    convolutionCoeff χ (LForestAlgebra.counit α R) φ = χ.evalForest φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change convolutionCoeff χ (LForestAlgebra.counit α R) (ts : LRootedForest α) =
    χ.evalForest (ts : LRootedForest α)
  rw [convolutionCoeff]
  change
    LForestTensorAlgebra.evalByCharacters χ (LForestAlgebra.counit α R)
        (PLTree.labelledCoproductList (R := R) (ts.map Quotient.out)) =
      χ.evalForest (ts : LRootedForest α)
  rw [LForestTensorAlgebra.evalByCharacters_labelledCoproductList]
  rw [PLTree.convolutionForestCoeff_unit_right]
  have h : (ts.map Quotient.out).map LRootedTree.ofPLTree = ts := by
    induction ts with
    | nil => rfl
    | cons τ ts ih =>
        simp only [List.map_cons]
        rw [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ, ih]
  rw [h]

theorem convolutionCoeff_unit_left (χ : LForestAlgebra.Character α R)
    (φ : LRootedForest α) :
    convolutionCoeff (LForestAlgebra.counit α R) χ φ = χ.evalForest φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change convolutionCoeff (LForestAlgebra.counit α R) χ (ts : LRootedForest α) =
    χ.evalForest (ts : LRootedForest α)
  rw [convolutionCoeff]
  change
    LForestTensorAlgebra.evalByCharacters (LForestAlgebra.counit α R) χ
        (PLTree.labelledCoproductList (R := R) (ts.map Quotient.out)) =
      χ.evalForest (ts : LRootedForest α)
  rw [LForestTensorAlgebra.evalByCharacters_labelledCoproductList]
  rw [PLTree.convolutionForestCoeff_unit_left]
  have h : (ts.map Quotient.out).map LRootedTree.ofPLTree = ts := by
    induction ts with
    | nil => rfl
    | cons τ ts ih =>
        simp only [List.map_cons]
        rw [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ, ih]
  rw [h]

end

end LRootedForest

namespace RootedForest

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

theorem convolutionCoeff_comapConstLabel
    (x : α) (χ ψ : LForestAlgebra.Character α R) (φ : RootedForest) :
    convolutionCoeff
        (LForestAlgebra.Character.comapConstLabel x χ)
        (LForestAlgebra.Character.comapConstLabel x ψ) φ =
      LRootedForest.convolutionCoeff χ ψ (LRootedForest.constLabel x φ) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change convolutionCoeff (LForestAlgebra.Character.comapConstLabel x χ)
      (LForestAlgebra.Character.comapConstLabel x ψ) (ts : RootedForest) =
    LRootedForest.convolutionCoeff χ ψ (LRootedForest.constLabel x (ts : RootedForest))
  rw [convolutionCoeff, LRootedForest.convolutionCoeff]
  change
    ForestTensorAlgebra.evalByCharacters
        (LForestAlgebra.Character.comapConstLabel x χ)
        (LForestAlgebra.Character.comapConstLabel x ψ)
        (PTree.coproductList (R := R) (ts.map Quotient.out)) =
      LForestTensorAlgebra.evalByCharacters χ ψ
        (PLTree.labelledCoproductList (R := R)
          ((ts.map (LRootedTree.constLabel x)).map Quotient.out))
  rw [ForestTensorAlgebra.evalByCharacters_coproductList,
    LForestTensorAlgebra.evalByCharacters_labelledCoproductList,
    PLTree.convolutionForestCoeff_comapConstLabel]
  exact PLTree.convolutionForestCoeff_forall₂_perm χ ψ (by
    induction ts with
    | nil =>
        exact List.Forall₂.nil
    | cons τ ts ih =>
        exact List.Forall₂.cons (LRootedTree.constLabel_out_perm x τ) ih)

end

end RootedForest

namespace LRootedTree

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- Character convolution coefficient on a non-planar labelled rooted tree. -/
def convolutionCoeff
    (χ ψ : LForestAlgebra.Character α R) (τ : LRootedTree α) : R :=
  LForestTensorAlgebra.evalByCharacters χ ψ (LRootedTree.coproduct (R := R) τ)

theorem convolutionCoeff_eq_singleton
    (χ ψ : LForestAlgebra.Character α R) (τ : LRootedTree α) :
    convolutionCoeff χ ψ τ =
      LRootedForest.convolutionCoeff χ ψ (LRootedForest.singleton τ) :=
  by
    rw [convolutionCoeff, LRootedForest.convolutionCoeff,
      LRootedTree.coproduct_eq_forest_singleton]

theorem convolutionCoeff_out
    (χ ψ : LForestAlgebra.Character α R) (τ : LRootedTree α) :
    convolutionCoeff χ ψ τ =
      PLTree.convolutionCoeff χ ψ (Quotient.out τ) := by
  rw [convolutionCoeff_eq_singleton, LRootedForest.convolutionCoeff_singleton]

theorem convolutionCoeff_ofPLTree
    (χ ψ : LForestAlgebra.Character α R) (t : PLTree α) :
    convolutionCoeff χ ψ (LRootedTree.ofPLTree t) =
      PLTree.convolutionCoeff χ ψ t := by
  rw [convolutionCoeff_out]
  exact PLTree.convolutionCoeff_perm χ ψ (LRootedTree.out_perm_ofPLTree t)

theorem convolutionCoeff_comapEraseLabels
    (χ ψ : ForestAlgebra.Character R) (τ : LRootedTree α) :
    convolutionCoeff
        (LForestAlgebra.Character.comapEraseLabels (α := α) χ)
        (LForestAlgebra.Character.comapEraseLabels (α := α) ψ) τ =
      RootedTree.convolutionCoeff χ ψ (LRootedTree.erase τ) := by
  rw [convolutionCoeff_eq_singleton, LRootedForest.convolutionCoeff_comapEraseLabels,
    LRootedForest.erase_singleton, RootedTree.convolutionCoeff_eq_singleton]

theorem convolutionCoeff_comapMapLabels {β : Type w}
    (f : α → β) (χ ψ : LForestAlgebra.Character β R)
    (τ : LRootedTree α) :
    convolutionCoeff
        (LForestAlgebra.Character.comapMapLabels f χ)
        (LForestAlgebra.Character.comapMapLabels f ψ) τ =
      LRootedTree.convolutionCoeff χ ψ (LRootedTree.map f τ) := by
  rw [convolutionCoeff_eq_singleton, LRootedForest.convolutionCoeff_comapMapLabels,
    LRootedTree.convolutionCoeff_eq_singleton]
  exact congrArg (fun φ => LRootedForest.convolutionCoeff χ ψ φ)
    (LRootedForest.mapLabels_singleton f τ)

theorem convolutionCoeff_unit_right
    (χ : LForestAlgebra.Character α R) (τ : LRootedTree α) :
    convolutionCoeff χ (LForestAlgebra.counit α R) τ =
      χ.evalForest (LRootedForest.singleton τ) := by
  rw [convolutionCoeff_eq_singleton]
  exact LRootedForest.convolutionCoeff_unit_right χ (LRootedForest.singleton τ)

theorem convolutionCoeff_unit_left
    (χ : LForestAlgebra.Character α R) (τ : LRootedTree α) :
    convolutionCoeff (LForestAlgebra.counit α R) χ τ =
      χ.evalForest (LRootedForest.singleton τ) := by
  rw [convolutionCoeff_eq_singleton]
  exact LRootedForest.convolutionCoeff_unit_left χ (LRootedForest.singleton τ)

end

end LRootedTree

namespace RootedTree

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

theorem convolutionCoeff_comapConstLabel
    (x : α) (χ ψ : LForestAlgebra.Character α R) (τ : RootedTree) :
    convolutionCoeff
        (LForestAlgebra.Character.comapConstLabel x χ)
        (LForestAlgebra.Character.comapConstLabel x ψ) τ =
      LRootedTree.convolutionCoeff χ ψ (LRootedTree.constLabel x τ) := by
  rw [convolutionCoeff_eq_singleton, RootedForest.convolutionCoeff_comapConstLabel,
    LRootedForest.constLabel_singleton, LRootedTree.convolutionCoeff_eq_singleton]

end

end RootedTree

namespace LForestAlgebra
namespace Character

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- The identity labelled character for convolution. -/
def unit (α : Type u) (R : Type v) [CommSemiring R] : Character α R :=
  LForestAlgebra.counit α R

@[simp]
theorem unit_evalForest (φ : LRootedForest α) :
    (unit α R).evalForest φ = LForestAlgebra.counitCoeff (R := R) φ := by
  simp [unit, LForestAlgebra.Character.evalForest, LForestAlgebra.counit_ofForest]

theorem unit_eq_counit : unit α R = LForestAlgebra.counit α R := rfl

@[simp]
theorem linearFunctional_ofCharacter_unit :
    LinearFunctional.ofCharacter (unit α R) = LinearFunctional.counit α R :=
  rfl

/-- Labelled character convolution induced by the labelled BCK coproduct. -/
def convolution (χ ψ : Character α R) : Character α R :=
  (LForestTensorAlgebra.evalByCharacters χ ψ).comp (LForestAlgebra.coproduct α R)

@[simp]
theorem convolution_evalForest (χ ψ : Character α R) (φ : LRootedForest α) :
    (convolution χ ψ).evalForest φ = LRootedForest.convolutionCoeff χ ψ φ := by
  simp [LForestAlgebra.Character.evalForest, convolution, LRootedForest.convolutionCoeff]

@[simp]
theorem convolution_ofForest (χ ψ : Character α R) (φ : LRootedForest α) :
    convolution χ ψ (ofForest (R := R) φ) = LRootedForest.convolutionCoeff χ ψ φ := by
  simpa [LForestAlgebra.Character.evalForest] using convolution_evalForest χ ψ φ

theorem linearFunctional_ofCharacter_convolution (χ ψ : Character α R) :
    LinearFunctional.ofCharacter (convolution χ ψ) =
      LinearFunctional.convolution
        (LinearFunctional.ofCharacter χ)
        (LinearFunctional.ofCharacter ψ) := by
  rw [convolution, LinearFunctional.ofCharacter, LinearFunctional.convolution,
    LForestTensorAlgebra.evalByLinearMaps_ofCharacter]
  rfl

theorem linearFunctional_ofCharacter_injective :
    Function.Injective
      (LinearFunctional.ofCharacter : Character α R → LinearFunctional α R) := by
  intro χ ψ h
  apply LForestAlgebra.Character.ext
  intro φ
  have hφ :=
    congrArg (fun f : LinearFunctional α R => f (ofForest (R := R) φ)) h
  simpa [LinearFunctional.ofCharacter, LForestAlgebra.Character.evalForest] using hφ

theorem convolution_comapEraseLabels
    (χ ψ : ForestAlgebra.Character R) :
    convolution
        (comapEraseLabels (α := α) χ)
        (comapEraseLabels (α := α) ψ) =
      comapEraseLabels (α := α) (ForestAlgebra.Character.convolution χ ψ) := by
  apply LForestAlgebra.Character.ext
  intro φ
  rw [convolution_evalForest, comapEraseLabels_evalForest,
    ForestAlgebra.Character.convolution_ofForest,
    LRootedForest.convolutionCoeff_comapEraseLabels]

theorem convolution_comapMapLabels {β : Type w}
    (f : α → β) (χ ψ : Character β R) :
    convolution (comapMapLabels f χ) (comapMapLabels f ψ) =
      comapMapLabels f (convolution χ ψ) := by
  apply LForestAlgebra.Character.ext
  intro φ
  rw [convolution_evalForest, comapMapLabels_evalForest, convolution_evalForest,
    LRootedForest.convolutionCoeff_comapMapLabels]

theorem convolution_comapConstLabel
    (x : α) (χ ψ : Character α R) :
    ForestAlgebra.Character.convolution (comapConstLabel x χ) (comapConstLabel x ψ) =
      comapConstLabel x (convolution χ ψ) := by
  apply ForestAlgebra.Character.ext
  intro φ
  rw [ForestAlgebra.Character.convolution_evalForest, comapConstLabel_evalForest,
    convolution_evalForest]
  exact RootedForest.convolutionCoeff_comapConstLabel x χ ψ φ

theorem LabelInvariant.convolution [Nonempty α]
    {χ ψ : Character α R} (hχ : LabelInvariant χ) (hψ : LabelInvariant ψ) :
    LabelInvariant (convolution χ ψ) := by
  rcases (labelInvariant_iff_exists_comapEraseLabels (α := α) χ).1 hχ with ⟨χ₀, hχ₀⟩
  rcases (labelInvariant_iff_exists_comapEraseLabels (α := α) ψ).1 hψ with ⟨ψ₀, hψ₀⟩
  rw [← hχ₀, ← hψ₀, convolution_comapEraseLabels]
  exact labelInvariant_comapEraseLabels (α := α)
    (ForestAlgebra.Character.convolution χ₀ ψ₀)

theorem labelInvariantEquiv_convolution [Nonempty α]
    (χ ψ : ForestAlgebra.Character R) :
    labelInvariantEquiv (α := α) (R := R)
        (ForestAlgebra.Character.convolution χ ψ) =
      ⟨convolution
          (labelInvariantEquiv (α := α) (R := R) χ).1
          (labelInvariantEquiv (α := α) (R := R) ψ).1,
        (labelInvariantEquiv (α := α) (R := R) χ).2.convolution
          (labelInvariantEquiv (α := α) (R := R) ψ).2⟩ := by
  apply Subtype.ext
  exact (convolution_comapEraseLabels (α := α) χ ψ).symm

theorem labelInvariantEquiv_symm_convolution [Nonempty α]
    (χ ψ : {χ : Character α R // LabelInvariant χ}) :
    (labelInvariantEquiv (α := α) (R := R)).symm
        ⟨LForestAlgebra.Character.convolution χ.1 ψ.1, χ.2.convolution ψ.2⟩ =
      ForestAlgebra.Character.convolution
        ((labelInvariantEquiv (α := α) (R := R)).symm χ)
        ((labelInvariantEquiv (α := α) (R := R)).symm ψ) := by
  change
    comapConstLabel (Classical.choice (inferInstance : Nonempty α))
        (LForestAlgebra.Character.convolution χ.1 ψ.1) =
      ForestAlgebra.Character.convolution
        (comapConstLabel (Classical.choice (inferInstance : Nonempty α)) χ.1)
        (comapConstLabel (Classical.choice (inferInstance : Nonempty α)) ψ.1)
  exact (LForestAlgebra.Character.convolution_comapConstLabel
    (Classical.choice (inferInstance : Nonempty α)) χ.1 ψ.1).symm

theorem convolution_unit_right (χ : Character α R) :
    convolution χ (unit α R) = χ := by
  change convolution χ (LForestAlgebra.counit α R) = χ
  apply LForestAlgebra.Character.ext
  intro φ
  rw [convolution_evalForest, LRootedForest.convolutionCoeff_unit_right]

theorem convolution_unit_left (χ : Character α R) :
    convolution (unit α R) χ = χ := by
  change convolution (LForestAlgebra.counit α R) χ = χ
  apply LForestAlgebra.Character.ext
  intro φ
  rw [convolution_evalForest, LRootedForest.convolutionCoeff_unit_left]

theorem linearFunctional_convolution_compAntipode_ofCharacter_left
    {α : Type u} {R : Type v} [CommRing R] (χ : Character α R) :
    LinearFunctional.convolution
        (LinearFunctional.compAntipode (LinearFunctional.ofCharacter χ))
        (LinearFunctional.ofCharacter χ) =
      LinearFunctional.ofCharacter (unit α R) := by
  rw [LinearFunctional.convolution_compAntipode_ofCharacter_left,
    linearFunctional_ofCharacter_unit]

theorem linearFunctional_convolution_compAntipode_ofCharacter_right
    {α : Type u} {R : Type v} [CommRing R] (χ : Character α R) :
    LinearFunctional.convolution
        (LinearFunctional.ofCharacter χ)
        (LinearFunctional.compAntipode (LinearFunctional.ofCharacter χ)) =
      LinearFunctional.ofCharacter (unit α R) := by
  rw [LinearFunctional.compAntipode_ofCharacter_eq_compRightAntipode χ]
  rw [LinearFunctional.convolution_compRightAntipode_ofCharacter_right,
    linearFunctional_ofCharacter_unit]

theorem convolution_left_cancel
    {α : Type u} {R : Type v} [CommRing R] {χ ψ η : Character α R}
    (h : convolution χ ψ = convolution χ η) : ψ = η := by
  have hlin := congrArg LinearFunctional.ofCharacter h
  rw [linearFunctional_ofCharacter_convolution,
    linearFunctional_ofCharacter_convolution] at hlin
  have hcancel :=
    congrArg
      (fun f : LinearFunctional α R =>
        LinearFunctional.convolution (inverseLinearFunctional χ) f) hlin
  rw [← LinearFunctional.convolution_assoc,
    convolution_inverseLinearFunctional_left,
    LinearFunctional.convolution_counit_left,
    ← LinearFunctional.convolution_assoc,
    convolution_inverseLinearFunctional_left,
    LinearFunctional.convolution_counit_left] at hcancel
  exact linearFunctional_ofCharacter_injective hcancel

theorem convolution_right_cancel
    {α : Type u} {R : Type v} [CommRing R] {χ ψ η : Character α R}
    (h : convolution ψ χ = convolution η χ) : ψ = η := by
  have hlin := congrArg LinearFunctional.ofCharacter h
  rw [linearFunctional_ofCharacter_convolution,
    linearFunctional_ofCharacter_convolution] at hlin
  have hcancel :=
    congrArg
      (fun f : LinearFunctional α R =>
        LinearFunctional.convolution f (inverseLinearFunctional χ)) hlin
  rw [LinearFunctional.convolution_assoc,
    convolution_inverseLinearFunctional_right,
    LinearFunctional.convolution_counit_right,
    LinearFunctional.convolution_assoc,
    convolution_inverseLinearFunctional_right,
    LinearFunctional.convolution_counit_right] at hcancel
  exact linearFunctional_ofCharacter_injective hcancel

theorem evalByCharacters_coproductLeft
    (χ ψ η : Character α R) (x : LForestTensorAlgebra α R) :
    LForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (LForestTripleTensorAlgebra.coproductLeft (R := R) x) =
      LForestTensorAlgebra.evalByCharacters (convolution χ ψ) η x := by
  change
    ((LForestTripleTensorAlgebra.evalByCharacters χ ψ η).comp
        (LForestTripleTensorAlgebra.coproductLeft (R := R))) x =
      LForestTensorAlgebra.evalByCharacters (convolution χ ψ) η x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext
    (M := LRootedForest α × LRootedForest α) (by
      intro term
      change
        LForestTripleTensorAlgebra.evalByCharacters χ ψ η
            (LForestTripleTensorAlgebra.coproductLeft (R := R)
              (LForestTensorAlgebra.ofPair (R := R) term)) =
          LForestTensorAlgebra.evalByCharacters (convolution χ ψ) η
            (LForestTensorAlgebra.ofPair (R := R) term)
      simp [LForestTripleTensorAlgebra.ofForests, PLTree.evalTripleCoproductTerm,
        PLTree.evalCoproductTerm, convolution, LForestAlgebra.Character.evalForest]) (by ext)) x

theorem evalByCharacters_coproductRight
    (χ ψ η : Character α R) (x : LForestTensorAlgebra α R) :
    LForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (LForestTripleTensorAlgebra.coproductRight (R := R) x) =
      LForestTensorAlgebra.evalByCharacters χ (convolution ψ η) x := by
  change
    ((LForestTripleTensorAlgebra.evalByCharacters χ ψ η).comp
        (LForestTripleTensorAlgebra.coproductRight (R := R))) x =
      LForestTensorAlgebra.evalByCharacters χ (convolution ψ η) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext
    (M := LRootedForest α × LRootedForest α) (by
      intro term
      change
        LForestTripleTensorAlgebra.evalByCharacters χ ψ η
            (LForestTripleTensorAlgebra.coproductRight (R := R)
              (LForestTensorAlgebra.ofPair (R := R) term)) =
          LForestTensorAlgebra.evalByCharacters χ (convolution ψ η)
            (LForestTensorAlgebra.ofPair (R := R) term)
      simp [LForestTripleTensorAlgebra.ofForests, PLTree.evalTripleCoproductTerm,
        PLTree.evalCoproductTerm, convolution, LForestAlgebra.Character.evalForest]) (by ext)) x

theorem evalByCharacters_forestCoproductLeft
    (χ ψ η : Character α R) (x : LForestAlgebra α R) :
    LForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (LForestAlgebra.coproductLeft α R x) =
      convolution (convolution χ ψ) η x := by
  rw [LForestAlgebra.coproductLeft]
  change
    LForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (LForestTripleTensorAlgebra.coproductLeft
          (LForestAlgebra.coproduct α R x)) =
      LForestTensorAlgebra.evalByCharacters (convolution χ ψ) η
        (LForestAlgebra.coproduct α R x)
  rw [evalByCharacters_coproductLeft]

theorem evalByCharacters_forestCoproductRight
    (χ ψ η : Character α R) (x : LForestAlgebra α R) :
    LForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (LForestAlgebra.coproductRight α R x) =
      convolution χ (convolution ψ η) x := by
  rw [LForestAlgebra.coproductRight]
  change
    LForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (LForestTripleTensorAlgebra.coproductRight
          (LForestAlgebra.coproduct α R x)) =
      LForestTensorAlgebra.evalByCharacters χ (convolution ψ η)
        (LForestAlgebra.coproduct α R x)
  rw [evalByCharacters_coproductRight]

theorem evalTripleCoproductTerms_coproductLeftTerms
    (χ ψ η : Character α R) (terms : List (LRootedForest α × LRootedForest α)) :
    PLTree.evalTripleCoproductTerms χ ψ η
        (LForestTripleTensorAlgebra.coproductLeftTerms terms) =
      PLTree.evalCoproductTerms (convolution χ ψ) η terms := by
  rw [← LForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    LForestTripleTensorAlgebra.sumTerms_coproductLeftTerms,
    evalByCharacters_coproductLeft,
    LForestTensorAlgebra.evalByCharacters_sumTerms]

theorem evalTripleCoproductTerms_coproductRightTerms
    (χ ψ η : Character α R) (terms : List (LRootedForest α × LRootedForest α)) :
    PLTree.evalTripleCoproductTerms χ ψ η
        (LForestTripleTensorAlgebra.coproductRightTerms terms) =
      PLTree.evalCoproductTerms χ (convolution ψ η) terms := by
  rw [← LForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    LForestTripleTensorAlgebra.sumTerms_coproductRightTerms,
    evalByCharacters_coproductRight,
    LForestTensorAlgebra.evalByCharacters_sumTerms]

theorem evalTripleCoproductTerms_coproductLeftTerms_pltree
    (χ ψ η : Character α R) (t : PLTree α) :
    PLTree.evalTripleCoproductTerms χ ψ η
        (LForestTripleTensorAlgebra.coproductLeftTerms (PLTree.coproductTerms t)) =
      PLTree.convolutionCoeff (convolution χ ψ) η t := by
  rw [evalTripleCoproductTerms_coproductLeftTerms, PLTree.convolutionCoeff]

theorem evalTripleCoproductTerms_coproductRightTerms_pltree
    (χ ψ η : Character α R) (t : PLTree α) :
    PLTree.evalTripleCoproductTerms χ ψ η
        (LForestTripleTensorAlgebra.coproductRightTerms (PLTree.coproductTerms t)) =
      PLTree.convolutionCoeff χ (convolution ψ η) t := by
  rw [evalTripleCoproductTerms_coproductRightTerms, PLTree.convolutionCoeff]

theorem evalTripleCoproductTerms_nestedCoproductLeftTerms
    (χ ψ η : Character α R) (t : PLTree α) :
    PLTree.evalTripleCoproductTerms χ ψ η (PLTree.nestedCoproductLeftTerms t) =
      PLTree.convolutionCoeff (convolution χ ψ) η t := by
  rw [← LForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    LForestTripleTensorAlgebra.sumTerms_nestedCoproductLeftTerms,
    LForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    evalTripleCoproductTerms_coproductLeftTerms_pltree]

theorem evalTripleCoproductTerms_nestedCoproductRightTerms
    (χ ψ η : Character α R) (t : PLTree α) :
    PLTree.evalTripleCoproductTerms χ ψ η (PLTree.nestedCoproductRightTerms t) =
      PLTree.convolutionCoeff χ (convolution ψ η) t := by
  rw [← LForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    LForestTripleTensorAlgebra.sumTerms_nestedCoproductRightTerms,
    LForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    evalTripleCoproductTerms_coproductRightTerms_pltree]

theorem evalTripleCoproductTerms_nestedCoproductLeftTerms_listRelPerm
    (χ ψ η : Character α R) {t u : PLTree α}
    (h : PTree.ListRelPerm PLTree.Cut.Perm (PLTree.cuts t) (PLTree.cuts u)) :
    PLTree.evalTripleCoproductTerms χ ψ η (PLTree.nestedCoproductLeftTerms t) =
      PLTree.evalTripleCoproductTerms χ ψ η (PLTree.nestedCoproductLeftTerms u) := by
  rw [← LForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    LForestTripleTensorAlgebra.sumTerms_nestedCoproductLeftTerms_listRelPerm (R := R) h,
    LForestTripleTensorAlgebra.evalByCharacters_sumTerms]

theorem evalTripleCoproductTerms_nestedCoproductRightTerms_listRelPerm
    (χ ψ η : Character α R) {t u : PLTree α}
    (h : PTree.ListRelPerm PLTree.Cut.Perm (PLTree.cuts t) (PLTree.cuts u)) :
    PLTree.evalTripleCoproductTerms χ ψ η (PLTree.nestedCoproductRightTerms t) =
      PLTree.evalTripleCoproductTerms χ ψ η (PLTree.nestedCoproductRightTerms u) := by
  rw [← LForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    LForestTripleTensorAlgebra.sumTerms_nestedCoproductRightTerms_listRelPerm (R := R) h,
    LForestTripleTensorAlgebra.evalByCharacters_sumTerms]

theorem evalTripleCoproductTerms_nestedCoproductLeftTerms_perm
    (χ ψ η : Character α R) {t u : PLTree α} (h : PLTree.Perm t u) :
    PLTree.evalTripleCoproductTerms χ ψ η (PLTree.nestedCoproductLeftTerms t) =
      PLTree.evalTripleCoproductTerms χ ψ η (PLTree.nestedCoproductLeftTerms u) :=
  evalTripleCoproductTerms_nestedCoproductLeftTerms_listRelPerm χ ψ η
    (PLTree.cuts_listRelPerm_of_perm h)

theorem evalTripleCoproductTerms_nestedCoproductRightTerms_perm
    (χ ψ η : Character α R) {t u : PLTree α} (h : PLTree.Perm t u) :
    PLTree.evalTripleCoproductTerms χ ψ η (PLTree.nestedCoproductRightTerms t) =
      PLTree.evalTripleCoproductTerms χ ψ η (PLTree.nestedCoproductRightTerms u) :=
  evalTripleCoproductTerms_nestedCoproductRightTerms_listRelPerm χ ψ η
    (PLTree.cuts_listRelPerm_of_perm h)

theorem convolution_assoc_of_coproduct_eq
    (hcoassoc : ∀ x : LForestAlgebra α R,
      LForestAlgebra.coproductLeft α R x = LForestAlgebra.coproductRight α R x)
    (χ ψ η : Character α R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) := by
  apply LForestAlgebra.Character.ext
  intro φ
  have h :=
    congrArg (LForestTripleTensorAlgebra.evalByCharacters χ ψ η)
      (hcoassoc (ofForest (R := R) φ))
  change
    convolution (convolution χ ψ) η (ofForest (R := R) φ) =
      convolution χ (convolution ψ η) (ofForest (R := R) φ)
  rw [← evalByCharacters_forestCoproductLeft χ ψ η (ofForest (R := R) φ),
    ← evalByCharacters_forestCoproductRight χ ψ η (ofForest (R := R) φ)]
  exact h

theorem convolution_assoc_of_coproductLeft_eq_coproductRight
    (hcoassoc :
      LForestAlgebra.coproductLeft α R = LForestAlgebra.coproductRight α R)
    (χ ψ η : Character α R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) :=
  convolution_assoc_of_coproduct_eq (fun x => by rw [hcoassoc]) χ ψ η

theorem convolution_assoc_of_coproduct_eq_singletons
    (hcoassoc : ∀ τ : LRootedTree α,
      LForestAlgebra.coproductLeft α R
          (ofForest (R := R) (LRootedForest.singleton τ)) =
        LForestAlgebra.coproductRight α R
          (ofForest (R := R) (LRootedForest.singleton τ)))
    (χ ψ η : Character α R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) := by
  exact convolution_assoc_of_coproduct_eq
    (fun x => by
      rw [LForestAlgebra.coproductLeft_eq_coproductRight_of_singletons
        (α := α) (R := R) hcoassoc])
    χ ψ η

theorem convolution_assoc_of_coproduct_eq_pltree_singletons
    (hcoassoc : ∀ t : PLTree α,
      LForestAlgebra.coproductLeft α R
          (ofForest (R := R) (LRootedForest.singleton (LRootedTree.ofPLTree t))) =
        LForestAlgebra.coproductRight α R
          (ofForest (R := R) (LRootedForest.singleton (LRootedTree.ofPLTree t))))
    (χ ψ η : Character α R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) := by
  exact convolution_assoc_of_coproduct_eq
    (fun x => by
      rw [LForestAlgebra.coproductLeft_eq_coproductRight_of_pltree_singletons
        (α := α) (R := R) hcoassoc])
    χ ψ η

theorem convolution_assoc_of_coproduct_eq_pltree_coproductTerms
    (hcoassoc : ∀ t : PLTree α,
      LForestTripleTensorAlgebra.sumTerms (R := R)
          (LForestTripleTensorAlgebra.coproductLeftTerms (PLTree.coproductTerms t)) =
        LForestTripleTensorAlgebra.sumTerms (R := R)
          (LForestTripleTensorAlgebra.coproductRightTerms (PLTree.coproductTerms t)))
    (χ ψ η : Character α R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) := by
  exact convolution_assoc_of_coproduct_eq
    (fun x => by
      rw [LForestAlgebra.coproductLeft_eq_coproductRight_of_pltree_coproductTerms
        (α := α) (R := R) hcoassoc])
    χ ψ η

theorem convolution_assoc_of_nestedCoproductTerms
    (hcoassoc : ∀ t : PLTree α,
      LForestTripleTensorAlgebra.sumTerms (R := R) (PLTree.nestedCoproductLeftTerms t) =
        LForestTripleTensorAlgebra.sumTerms (R := R) (PLTree.nestedCoproductRightTerms t))
    (χ ψ η : Character α R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) := by
  exact convolution_assoc_of_coproduct_eq
    (fun x => by
      rw [LForestAlgebra.coproductLeft_eq_coproductRight_of_nestedCoproductTerms
        (α := α) (R := R) hcoassoc])
    χ ψ η

theorem convolution_assoc_of_nestedCoproductTerms_perm
    (hcoassoc : ∀ t : PLTree α,
      (PLTree.nestedCoproductLeftTerms t).Perm (PLTree.nestedCoproductRightTerms t))
    (χ ψ η : Character α R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) :=
  convolution_assoc_of_nestedCoproductTerms
    (fun t => LForestTripleTensorAlgebra.sumTerms_perm (R := R) (hcoassoc t)) χ ψ η

theorem convolution_assoc (χ ψ η : Character α R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) :=
  convolution_assoc_of_coproductLeft_eq_coproductRight
    (LForestAlgebra.coproductLeft_eq_coproductRight (α := α) (R := R)) χ ψ η

noncomputable instance instMonoid : Monoid (Character α R) where
  one := unit α R
  mul := convolution
  mul_assoc := convolution_assoc
  one_mul := convolution_unit_left
  mul_one := convolution_unit_right

noncomputable instance instLabelInvariantMonoid [Nonempty α] :
    Monoid {χ : Character α R // LabelInvariant χ} where
  one := ⟨unit α R, by rw [unit_eq_counit]; exact labelInvariant_counit⟩
  mul χ ψ := ⟨convolution χ.1 ψ.1, χ.2.convolution ψ.2⟩
  mul_assoc χ ψ η := by
    apply Subtype.ext
    exact convolution_assoc χ.1 ψ.1 η.1
  one_mul χ := by
    apply Subtype.ext
    exact convolution_unit_left χ.1
  mul_one χ := by
    apply Subtype.ext
    exact convolution_unit_right χ.1

noncomputable def labelInvariantMulEquiv [Nonempty α] :
    ForestAlgebra.Character R ≃* {χ : Character α R // LabelInvariant χ} where
  toEquiv := labelInvariantEquiv
  map_mul' χ ψ := by
    change labelInvariantEquiv (ForestAlgebra.Character.convolution χ ψ) =
      ⟨convolution (labelInvariantEquiv (α := α) χ).1
          (labelInvariantEquiv (α := α) ψ).1,
        (labelInvariantEquiv (α := α) χ).2.convolution
          (labelInvariantEquiv (α := α) ψ).2⟩
    exact labelInvariantEquiv_convolution χ ψ

end

end Character
end LForestAlgebra

end HopfAlgebras
