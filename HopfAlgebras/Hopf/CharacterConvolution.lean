/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.Coproduct
import HopfAlgebras.Hopf.Dual

/-!
# Character Convolution on the BCK Hopf Algebra

The convolution product of forest-algebra characters induced by the BCK
coproduct, with its unit (the counit), associativity, and the coefficient
functions on planar trees, rooted trees and forests.
-/

namespace HopfAlgebras

universe u

namespace PTree

noncomputable section

variable {R : Type u} [CommSemiring R]

/-- Evaluate one tensor-coded coproduct term against two characters. -/
def evalCoproductTerm (χ ψ : ForestAlgebra.Character R)
    (term : RootedForest × RootedForest) : R :=
  χ.evalForest term.1 * ψ.evalForest term.2

@[simp]
theorem evalCoproductTerm_zero (χ ψ : ForestAlgebra.Character R) :
    evalCoproductTerm χ ψ (0 : RootedForest × RootedForest) = 1 := by
  simp [evalCoproductTerm]

@[simp]
theorem evalCoproductTerm_add (χ ψ : ForestAlgebra.Character R)
    (x y : RootedForest × RootedForest) :
    evalCoproductTerm χ ψ (x + y) =
      evalCoproductTerm χ ψ x * evalCoproductTerm χ ψ y := by
  rcases x with ⟨φ₁, ψ₁⟩
  rcases y with ⟨φ₂, ψ₂⟩
  simp [evalCoproductTerm]
  ac_rfl

theorem evalCoproductTerm_ofPTree_list_forall₂_perm_singleton
    (χ ψ : ForestAlgebra.Character R)
    {ps qs : List PTree} (hps : List.Forall₂ PTree.Perm ps qs)
    {t u : PTree} (htu : PTree.Perm t u) :
    evalCoproductTerm χ ψ
        ((ps.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree t)) =
      evalCoproductTerm χ ψ
        ((qs.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree u)) := by
  have ht : RootedTree.ofPTree t = RootedTree.ofPTree u :=
    Quotient.sound (show t ≈ u from htu)
  simp [evalCoproductTerm, ForestAlgebra.Character.evalForest_ofPTree_list_forall₂_perm χ hps,
    ht]

theorem evalCoproductTerm_ofPTree_list_forestPerm_singleton
    (χ ψ : ForestAlgebra.Character R)
    {ps qs : List PTree} (hps : PTree.ForestPerm ps qs)
    {t u : PTree} (htu : RootedTree.ofPTree t = RootedTree.ofPTree u) :
    evalCoproductTerm χ ψ
        ((ps.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree t)) =
      evalCoproductTerm χ ψ
        ((qs.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree u)) := by
  simp [evalCoproductTerm, ForestAlgebra.Character.evalForest_ofPTree_list_forestPerm χ hps,
    htu]

theorem evalCoproductTerm_ofPTree_list_forall₂_perm_zero
    (χ ψ : ForestAlgebra.Character R)
    {ps qs : List PTree} (hps : List.Forall₂ PTree.Perm ps qs) :
    evalCoproductTerm χ ψ ((ps.map RootedTree.ofPTree : RootedForest), 0) =
      evalCoproductTerm χ ψ ((qs.map RootedTree.ofPTree : RootedForest), 0) := by
  simp [evalCoproductTerm, ForestAlgebra.Character.evalForest_ofPTree_list_forall₂_perm χ hps]

theorem evalCoproductTerm_ofPTree_list_forestPerm_zero
    (χ ψ : ForestAlgebra.Character R)
    {ps qs : List PTree} (hps : PTree.ForestPerm ps qs) :
    evalCoproductTerm χ ψ ((ps.map RootedTree.ofPTree : RootedForest), 0) =
      evalCoproductTerm χ ψ ((qs.map RootedTree.ofPTree : RootedForest), 0) := by
  simp [evalCoproductTerm, ForestAlgebra.Character.evalForest_ofPTree_list_forestPerm χ hps]

theorem evalCoproductTerm_rootCut_perm (χ ψ : ForestAlgebra.Character R)
    {c d : RootCut} (h : RootCut.Perm c d) :
    evalCoproductTerm χ ψ
        ((c.pruned.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree c.trunk)) =
      evalCoproductTerm χ ψ
        ((d.pruned.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree d.trunk)) := by
  exact evalCoproductTerm_ofPTree_list_forestPerm_singleton χ ψ h.1 h.2

theorem evalCoproductTerm_rootCutList_perm (χ ψ : ForestAlgebra.Character R)
    {c d : RootCutList} (h : RootCutList.Perm c d) :
    evalCoproductTerm χ ψ
        ((c.pruned.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree (.node c.trunks))) =
      evalCoproductTerm χ ψ
        ((d.pruned.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree (.node d.trunks))) := by
  exact evalCoproductTerm_ofPTree_list_forestPerm_singleton χ ψ h.1
    (RootedForest.ofPTree_node_eq_of_forestPerm h.2)

theorem evalCoproductTerm_cut_perm (χ ψ : ForestAlgebra.Character R)
    {c d : Cut} (h : Cut.Perm c d) :
    evalCoproductTerm χ ψ (c.prunedForest, c.trunkForest) =
      evalCoproductTerm χ ψ (d.prunedForest, d.trunkForest) := by
  rcases c with ⟨ps, t?⟩
  rcases d with ⟨qs, u?⟩
  rcases h with ⟨hps, htrunk⟩
  cases t? with
  | none =>
      cases u? with
      | none =>
          simpa [Cut.prunedForest, Cut.trunkForest] using
            evalCoproductTerm_ofPTree_list_forestPerm_zero χ ψ hps
      | some u =>
          simp [OptionPerm] at htrunk
  | some t =>
      cases u? with
      | none =>
          simp [OptionPerm] at htrunk
      | some u =>
          simpa [Cut.prunedForest, Cut.trunkForest] using
            evalCoproductTerm_ofPTree_list_forestPerm_singleton χ ψ hps htrunk

/-- Evaluate a finite list of tensor-coded coproduct terms. -/
def evalCoproductTerms (χ ψ : ForestAlgebra.Character R)
    (terms : List (RootedForest × RootedForest)) : R :=
  (terms.map (evalCoproductTerm χ ψ)).sum

@[simp]
theorem evalCoproductTerms_nil (χ ψ : ForestAlgebra.Character R) :
    evalCoproductTerms χ ψ [] = 0 :=
  rfl

@[simp]
theorem evalCoproductTerms_cons (χ ψ : ForestAlgebra.Character R)
    (term : RootedForest × RootedForest)
    (terms : List (RootedForest × RootedForest)) :
    evalCoproductTerms χ ψ (term :: terms) =
      evalCoproductTerm χ ψ term + evalCoproductTerms χ ψ terms :=
  rfl

theorem evalCoproductTerms_append (χ ψ : ForestAlgebra.Character R)
    (xs ys : List (RootedForest × RootedForest)) :
    evalCoproductTerms χ ψ (xs ++ ys) =
      evalCoproductTerms χ ψ xs + evalCoproductTerms χ ψ ys := by
  simp [evalCoproductTerms, List.map_append]

theorem evalCoproductTerms_perm (χ ψ : ForestAlgebra.Character R)
    {xs ys : List (RootedForest × RootedForest)} (h : xs.Perm ys) :
    evalCoproductTerms χ ψ xs = evalCoproductTerms χ ψ ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem evalCoproductTerms_eq_of_forall₂_eval_eq (χ ψ : ForestAlgebra.Character R) :
    ∀ {xs ys : List (RootedForest × RootedForest)},
      List.Forall₂
        (fun x y => evalCoproductTerm χ ψ x = evalCoproductTerm χ ψ y) xs ys →
        evalCoproductTerms χ ψ xs = evalCoproductTerms χ ψ ys
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      simp [h, evalCoproductTerms_eq_of_forall₂_eval_eq χ ψ hs]

theorem evalCoproductTerms_rootCut_forall₂_perm (χ ψ : ForestAlgebra.Character R) :
    ∀ {cs ds : List RootCut}, List.Forall₂ RootCut.Perm cs ds →
      evalCoproductTerms χ ψ
          (cs.map fun c =>
            ((c.pruned.map RootedTree.ofPTree : RootedForest),
              RootedForest.singleton (RootedTree.ofPTree c.trunk))) =
        evalCoproductTerms χ ψ
          (ds.map fun d =>
            ((d.pruned.map RootedTree.ofPTree : RootedForest),
              RootedForest.singleton (RootedTree.ofPTree d.trunk)))
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      simp [evalCoproductTerm_rootCut_perm χ ψ h,
        evalCoproductTerms_rootCut_forall₂_perm χ ψ hs]

theorem evalCoproductTerms_rootCut_listRelPerm (χ ψ : ForestAlgebra.Character R)
    {cs ds : List RootCut} (h : ListRelPerm RootCut.Perm cs ds) :
    evalCoproductTerms χ ψ
        (cs.map fun c =>
          ((c.pruned.map RootedTree.ofPTree : RootedForest),
            RootedForest.singleton (RootedTree.ofPTree c.trunk))) =
      evalCoproductTerms χ ψ
        (ds.map fun d =>
          ((d.pruned.map RootedTree.ofPTree : RootedForest),
            RootedForest.singleton (RootedTree.ofPTree d.trunk))) := by
  rcases h with ⟨cs', hp, hrel⟩
  rw [evalCoproductTerms_perm χ ψ (hp.map _)]
  exact evalCoproductTerms_rootCut_forall₂_perm χ ψ hrel

theorem evalCoproductTerms_rootCutList_forall₂_perm
    (χ ψ : ForestAlgebra.Character R) :
    ∀ {cs ds : List RootCutList}, List.Forall₂ RootCutList.Perm cs ds →
      evalCoproductTerms χ ψ
          (cs.map fun c =>
            ((c.pruned.map RootedTree.ofPTree : RootedForest),
              RootedForest.singleton (RootedTree.ofPTree (.node c.trunks)))) =
        evalCoproductTerms χ ψ
          (ds.map fun d =>
            ((d.pruned.map RootedTree.ofPTree : RootedForest),
              RootedForest.singleton (RootedTree.ofPTree (.node d.trunks))))
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      simp [evalCoproductTerm_rootCutList_perm χ ψ h,
        evalCoproductTerms_rootCutList_forall₂_perm χ ψ hs]

theorem evalCoproductTerms_rootCutList_listRelPerm
    (χ ψ : ForestAlgebra.Character R)
    {cs ds : List RootCutList} (h : ListRelPerm RootCutList.Perm cs ds) :
    evalCoproductTerms χ ψ
        (cs.map fun c =>
          ((c.pruned.map RootedTree.ofPTree : RootedForest),
            RootedForest.singleton (RootedTree.ofPTree (.node c.trunks)))) =
      evalCoproductTerms χ ψ
        (ds.map fun d =>
          ((d.pruned.map RootedTree.ofPTree : RootedForest),
            RootedForest.singleton (RootedTree.ofPTree (.node d.trunks)))) := by
  rcases h with ⟨cs', hp, hrel⟩
  rw [evalCoproductTerms_perm χ ψ (hp.map _)]
  exact evalCoproductTerms_rootCutList_forall₂_perm χ ψ hrel

theorem evalCoproductTerms_cut_forall₂_perm (χ ψ : ForestAlgebra.Character R) :
    ∀ {cs ds : List Cut}, List.Forall₂ Cut.Perm cs ds →
      evalCoproductTerms χ ψ (cs.map fun c => (c.prunedForest, c.trunkForest)) =
        evalCoproductTerms χ ψ (ds.map fun d => (d.prunedForest, d.trunkForest))
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      simp [evalCoproductTerm_cut_perm χ ψ h,
        evalCoproductTerms_cut_forall₂_perm χ ψ hs]

theorem evalCoproductTerms_cut_listRelPerm (χ ψ : ForestAlgebra.Character R)
    {cs ds : List Cut} (h : ListRelPerm Cut.Perm cs ds) :
    evalCoproductTerms χ ψ (cs.map fun c => (c.prunedForest, c.trunkForest)) =
      evalCoproductTerms χ ψ (ds.map fun d => (d.prunedForest, d.trunkForest)) := by
  rcases h with ⟨cs', hp, hrel⟩
  rw [evalCoproductTerms_perm χ ψ (hp.map _)]
  exact evalCoproductTerms_cut_forall₂_perm χ ψ hrel

theorem evalCoproductTerms_map_add_left (χ ψ : ForestAlgebra.Character R)
    (x : RootedForest × RootedForest) :
    ∀ ys : List (RootedForest × RootedForest),
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

theorem evalCoproductTerms_multiply (χ ψ : ForestAlgebra.Character R)
    (xs ys : List (RootedForest × RootedForest)) :
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

/-- Evaluate one triple tensor-coded term against three characters. -/
def evalTripleCoproductTerm (χ ψ η : ForestAlgebra.Character R)
    (term : RootedForest × RootedForest × RootedForest) : R :=
  χ.evalForest term.1 * ψ.evalForest term.2.1 * η.evalForest term.2.2

@[simp]
theorem evalTripleCoproductTerm_zero (χ ψ η : ForestAlgebra.Character R) :
    evalTripleCoproductTerm χ ψ η
        (0 : RootedForest × RootedForest × RootedForest) = 1 := by
  simp [evalTripleCoproductTerm]

@[simp]
theorem evalTripleCoproductTerm_add (χ ψ η : ForestAlgebra.Character R)
    (x y : RootedForest × RootedForest × RootedForest) :
    evalTripleCoproductTerm χ ψ η (x + y) =
      evalTripleCoproductTerm χ ψ η x *
        evalTripleCoproductTerm χ ψ η y := by
  rcases x with ⟨φ₁, ψ₁, η₁⟩
  rcases y with ⟨φ₂, ψ₂, η₂⟩
  simp [evalTripleCoproductTerm]
  ac_rfl

/-- Evaluate a finite list of triple tensor-coded terms. -/
def evalTripleCoproductTerms (χ ψ η : ForestAlgebra.Character R)
    (terms : List (RootedForest × RootedForest × RootedForest)) : R :=
  (terms.map (evalTripleCoproductTerm χ ψ η)).sum

@[simp]
theorem evalTripleCoproductTerms_nil (χ ψ η : ForestAlgebra.Character R) :
    evalTripleCoproductTerms χ ψ η [] = 0 :=
  rfl

@[simp]
theorem evalTripleCoproductTerms_cons (χ ψ η : ForestAlgebra.Character R)
    (term : RootedForest × RootedForest × RootedForest)
    (terms : List (RootedForest × RootedForest × RootedForest)) :
    evalTripleCoproductTerms χ ψ η (term :: terms) =
      evalTripleCoproductTerm χ ψ η term +
        evalTripleCoproductTerms χ ψ η terms :=
  rfl

theorem evalTripleCoproductTerms_append (χ ψ η : ForestAlgebra.Character R)
    (xs ys : List (RootedForest × RootedForest × RootedForest)) :
    evalTripleCoproductTerms χ ψ η (xs ++ ys) =
      evalTripleCoproductTerms χ ψ η xs +
        evalTripleCoproductTerms χ ψ η ys := by
  simp [evalTripleCoproductTerms, List.map_append]

theorem evalTripleCoproductTerms_perm (χ ψ η : ForestAlgebra.Character R)
    {xs ys : List (RootedForest × RootedForest × RootedForest)}
    (h : xs.Perm ys) :
    evalTripleCoproductTerms χ ψ η xs =
      evalTripleCoproductTerms χ ψ η ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem evalTripleCoproductTerms_map_add_left
    (χ ψ η : ForestAlgebra.Character R)
    (x : RootedForest × RootedForest × RootedForest) :
    ∀ ys : List (RootedForest × RootedForest × RootedForest),
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
    (χ ψ η : ForestAlgebra.Character R)
    (xs ys : List (RootedForest × RootedForest × RootedForest)) :
    evalTripleCoproductTerms χ ψ η
        (ForestTripleTensorAlgebra.multiplyTerms xs ys) =
      evalTripleCoproductTerms χ ψ η xs *
        evalTripleCoproductTerms χ ψ η ys := by
  induction xs with
  | nil =>
      simp [ForestTripleTensorAlgebra.multiplyTerms, evalTripleCoproductTerms]
  | cons x xs ih =>
      rw [ForestTripleTensorAlgebra.multiplyTerms]
      rw [ForestTripleTensorAlgebra.multiplyTerms] at ih
      simp only [List.flatMap_cons]
      rw [evalTripleCoproductTerms_append, ih, evalTripleCoproductTerms_cons]
      rw [evalTripleCoproductTerms_map_add_left, add_mul]

/-- The convolution coefficient of two characters on a planar rooted tree. -/
def convolutionCoeff (χ ψ : ForestAlgebra.Character R) (t : PTree) : R :=
  evalCoproductTerms χ ψ (coproductTerms t)

theorem convolutionCoeff_eq_of_cuts_listRelPerm
    (χ ψ : ForestAlgebra.Character R) {t u : PTree}
    (h : ListRelPerm Cut.Perm (cuts t) (cuts u)) :
    convolutionCoeff χ ψ t = convolutionCoeff χ ψ u := by
  rw [convolutionCoeff, convolutionCoeff, coproductTerms, coproductTerms]
  exact evalCoproductTerms_cut_listRelPerm χ ψ h

theorem convolutionCoeff_eq_of_rootCuts_listRelPerm
    (χ ψ : ForestAlgebra.Character R) {t u : PTree} (htu : PTree.Perm t u)
    (hroot : ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) :
    convolutionCoeff χ ψ t = convolutionCoeff χ ψ u :=
  convolutionCoeff_eq_of_cuts_listRelPerm χ ψ
    (cuts_listRelPerm_of_rootCuts htu hroot)

theorem convolutionCoeff_perm (χ ψ : ForestAlgebra.Character R)
    {t u : PTree} (h : PTree.Perm t u) :
    convolutionCoeff χ ψ t = convolutionCoeff χ ψ u :=
  convolutionCoeff_eq_of_cuts_listRelPerm χ ψ (cuts_listRelPerm_of_perm h)

private theorem forall₂_perm_of_forall₂_perm_rootCuts :
    ∀ {ts us : List PTree},
      List.Forall₂
          (fun t u =>
            PTree.Perm t u ∧ ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) ts us →
        List.Forall₂ PTree.Perm ts us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h htail =>
      .cons h.1 (forall₂_perm_of_forall₂_perm_rootCuts htail)

theorem convolutionCoeff_node_eq_of_forall₂_perm_rootCuts
    (χ ψ : ForestAlgebra.Character R) {ts us : List PTree}
    (h :
      List.Forall₂
        (fun t u =>
          PTree.Perm t u ∧ ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) ts us) :
    convolutionCoeff χ ψ (.node ts) = convolutionCoeff χ ψ (.node us) :=
  convolutionCoeff_eq_of_rootCuts_listRelPerm χ ψ
    (PTree.perm_node_of_forall2 (forall₂_perm_of_forall₂_perm_rootCuts h))
    (rootCuts_node_listRelPerm_of_forall₂_perm_rootCuts h)

/-- Multiplicative extension of convolution coefficients to planar forests. -/
def convolutionForestCoeff (χ ψ : ForestAlgebra.Character R) (ts : List PTree) : R :=
  evalCoproductTerms χ ψ (coproductTermsList ts)

@[simp]
theorem convolutionForestCoeff_nil (χ ψ : ForestAlgebra.Character R) :
    convolutionForestCoeff χ ψ [] = 1 := by
  simp [convolutionForestCoeff, coproductTermsList, evalCoproductTerms, evalCoproductTerm]

@[simp]
theorem convolutionForestCoeff_cons (χ ψ : ForestAlgebra.Character R)
    (t : PTree) (ts : List PTree) :
    convolutionForestCoeff χ ψ (t :: ts) =
      convolutionCoeff χ ψ t * convolutionForestCoeff χ ψ ts := by
  simp [
    convolutionForestCoeff,
    convolutionCoeff,
    coproductTermsList,
    evalCoproductTerms_multiply
  ]

theorem convolutionForestCoeff_perm (χ ψ : ForestAlgebra.Character R)
    {ts us : List PTree} (h : ts.Perm us) :
    convolutionForestCoeff χ ψ ts = convolutionForestCoeff χ ψ us := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ =>
      simp
      ac_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem convolutionForestCoeff_forall₂_perm (χ ψ : ForestAlgebra.Character R) :
    ∀ {ts us : List PTree}, List.Forall₂ PTree.Perm ts us →
      convolutionForestCoeff χ ψ ts = convolutionForestCoeff χ ψ us
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
      rw [convolutionForestCoeff_cons, convolutionForestCoeff_cons,
        convolutionCoeff_perm χ ψ h, convolutionForestCoeff_forall₂_perm χ ψ hs]

private theorem evalRootCuts_unit_right (χ : ForestAlgebra.Character R)
    (cuts : List RootCut) :
    evalCoproductTerms χ (ForestAlgebra.counit R)
      (cuts.map fun c =>
        ((c.pruned.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree c.trunk))) = 0 := by
  induction cuts with
  | nil =>
      simp
  | cons c cuts ih =>
      simp [evalCoproductTerm, ForestAlgebra.Character.evalForest,
        ForestAlgebra.counit_ofForest,
        ForestAlgebra.counitCoeff_ne_zero (RootedForest.singleton_ne_zero _), ih]

private theorem evalRootCuts_unit_right_tree (χ : ForestAlgebra.Character R) (t : PTree) :
    evalCoproductTerms χ (ForestAlgebra.counit R)
      ((rootCuts t).map fun c =>
        ((c.pruned.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree c.trunk))) = 0 :=
  evalRootCuts_unit_right χ (rootCuts t)

theorem convolutionCoeff_unit_right (χ : ForestAlgebra.Character R) (t : PTree) :
    convolutionCoeff χ (ForestAlgebra.counit R) t =
      χ.evalForest (RootedForest.singleton (RootedTree.ofPTree t)) := by
  rw [convolutionCoeff, coproductTerms, cuts]
  simp only [List.map_append, List.map_map]
  rw [evalCoproductTerms_append]
  change
    evalCoproductTerms χ (ForestAlgebra.counit R)
        ((rootCuts t).map fun c =>
          ((c.pruned.map RootedTree.ofPTree : RootedForest),
            RootedForest.singleton (RootedTree.ofPTree c.trunk))) +
      evalCoproductTerms χ (ForestAlgebra.counit R)
        (List.map (fun c : Cut => (c.prunedForest, c.trunkForest))
          ([{ pruned := [t], trunk? := none }] : List Cut)) =
    χ.evalForest (RootedForest.singleton (RootedTree.ofPTree t))
  rw [evalRootCuts_unit_right_tree]
  simp [evalCoproductTerms, evalCoproductTerm, Cut.prunedForest, Cut.trunkForest,
    ForestAlgebra.Character.evalForest, RootedForest.singleton]

private theorem evalRootCuts_unit_left (χ : ForestAlgebra.Character R)
    (cuts : List RootCut) :
    evalCoproductTerms (ForestAlgebra.counit R) χ
      (cuts.map fun c =>
        ((c.pruned.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree c.trunk))) =
      ((cuts.filterMap RootCut.noPrunedTrunk?).map fun trunk =>
        χ.evalForest (RootedForest.singleton (RootedTree.ofPTree trunk))).sum := by
  induction cuts with
  | nil =>
      simp
  | cons c cuts ih =>
      cases hpruned : c.pruned with
      | nil =>
          simp [evalCoproductTerm, ForestAlgebra.Character.evalForest,
            RootCut.noPrunedTrunk?, hpruned, ih]
      | cons p ps =>
          have hne :
              (((RootedTree.ofPTree p :: ps.map RootedTree.ofPTree) : List RootedTree) :
                RootedForest) ≠ 0 := by
            exact (RootedForest.order_pos_iff_ne_zero _).1
              (RootedForest.order_coe_cons_pos (RootedTree.ofPTree p)
                (ps.map RootedTree.ofPTree))
          simp [evalCoproductTerm, ForestAlgebra.Character.evalForest,
            RootCut.noPrunedTrunk?, hpruned, ih, ForestAlgebra.counit_ofForest,
            ForestAlgebra.counitCoeff_ne_zero hne]

private theorem evalRootCuts_unit_left_tree (χ : ForestAlgebra.Character R) (t : PTree) :
    evalCoproductTerms (ForestAlgebra.counit R) χ
      ((rootCuts t).map fun c =>
        ((c.pruned.map RootedTree.ofPTree : RootedForest),
          RootedForest.singleton (RootedTree.ofPTree c.trunk))) =
      χ.evalForest (RootedForest.singleton (RootedTree.ofPTree t)) := by
  rw [evalRootCuts_unit_left, rootCuts_noPrunedTrunks]
  simp

theorem convolutionCoeff_unit_left (χ : ForestAlgebra.Character R) (t : PTree) :
    convolutionCoeff (ForestAlgebra.counit R) χ t =
      χ.evalForest (RootedForest.singleton (RootedTree.ofPTree t)) := by
  rw [convolutionCoeff, coproductTerms, cuts]
  simp only [List.map_append, List.map_map]
  rw [evalCoproductTerms_append]
  change
    evalCoproductTerms (ForestAlgebra.counit R) χ
        ((rootCuts t).map fun c =>
          ((c.pruned.map RootedTree.ofPTree : RootedForest),
            RootedForest.singleton (RootedTree.ofPTree c.trunk))) +
      evalCoproductTerms (ForestAlgebra.counit R) χ
        (List.map (fun c : Cut => (c.prunedForest, c.trunkForest))
          ([{ pruned := [t], trunk? := none }] : List Cut)) =
    χ.evalForest (RootedForest.singleton (RootedTree.ofPTree t))
  rw [evalRootCuts_unit_left_tree]
  simp [evalCoproductTerms, evalCoproductTerm, Cut.prunedForest, Cut.trunkForest,
    ForestAlgebra.Character.evalForest,
    ForestAlgebra.counit_ofForest,
    ForestAlgebra.counitCoeff_ne_zero
      (show ({RootedTree.ofPTree t} : RootedForest) ≠ 0 by simp)]

theorem convolutionForestCoeff_unit_right (χ : ForestAlgebra.Character R) (ts : List PTree) :
    convolutionForestCoeff χ (ForestAlgebra.counit R) ts =
      χ.evalForest (ts.map RootedTree.ofPTree : RootedForest) := by
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      rw [convolutionForestCoeff_cons, convolutionCoeff_unit_right, ih]
      rw [← ForestAlgebra.Character.evalForest_add]
      simp [RootedForest.singleton]

theorem convolutionForestCoeff_unit_left (χ : ForestAlgebra.Character R) (ts : List PTree) :
    convolutionForestCoeff (ForestAlgebra.counit R) χ ts =
      χ.evalForest (ts.map RootedTree.ofPTree : RootedForest) := by
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      rw [convolutionForestCoeff_cons, convolutionCoeff_unit_left, ih]
      rw [← ForestAlgebra.Character.evalForest_add]
      simp [RootedForest.singleton]

end

end PTree

namespace ForestTensorAlgebra

noncomputable section

variable {R : Type u} [CommSemiring R]

private def characterPairMonoidHom (χ ψ : ForestAlgebra.Character R) :
    Multiplicative (RootedForest × RootedForest) →* R where
  toFun term := PTree.evalCoproductTerm χ ψ (Multiplicative.toAdd term)
  map_one' := by
    change PTree.evalCoproductTerm χ ψ (0 : RootedForest × RootedForest) = 1
    simp
  map_mul' x y := by
    change
      PTree.evalCoproductTerm χ ψ (Multiplicative.toAdd (x * y)) =
        PTree.evalCoproductTerm χ ψ (Multiplicative.toAdd x) *
          PTree.evalCoproductTerm χ ψ (Multiplicative.toAdd y)
    change
      PTree.evalCoproductTerm χ ψ
          (Multiplicative.toAdd x + Multiplicative.toAdd y) =
        PTree.evalCoproductTerm χ ψ (Multiplicative.toAdd x) *
          PTree.evalCoproductTerm χ ψ (Multiplicative.toAdd y)
    simp

/-- Evaluate the tensor-coded forest algebra using two characters. -/
def evalByCharacters (χ ψ : ForestAlgebra.Character R) :
    ForestTensorAlgebra R →ₐ[R] R :=
  (AddMonoidAlgebra.lift R R (RootedForest × RootedForest))
    (characterPairMonoidHom χ ψ)

@[simp]
theorem evalByCharacters_ofPair (χ ψ : ForestAlgebra.Character R)
    (term : RootedForest × RootedForest) :
    evalByCharacters χ ψ (ofPair (R := R) term) =
      PTree.evalCoproductTerm χ ψ term := by
  simp [evalByCharacters, ofPair, characterPairMonoidHom]

theorem evalByCharacters_sumTerms (χ ψ : ForestAlgebra.Character R)
    (terms : List (RootedForest × RootedForest)) :
    evalByCharacters χ ψ (sumTerms (R := R) terms) =
      PTree.evalCoproductTerms χ ψ terms := by
  induction terms with
  | nil =>
      simp [sumTerms, PTree.evalCoproductTerms]
  | cons term terms ih =>
      rw [
        sumTerms_cons,
        PTree.evalCoproductTerms_cons,
        map_add,
        evalByCharacters_ofPair,
        ih
      ]

theorem evalByLinearMaps_ofCharacter (χ ψ : ForestAlgebra.Character R) :
    evalByLinearMaps
        (ForestAlgebra.LinearFunctional.ofCharacter χ)
        (ForestAlgebra.LinearFunctional.ofCharacter ψ) =
      (evalByCharacters χ ψ).toLinearMap := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on
    (motive := fun x : ForestTensorAlgebra R =>
      evalByLinearMaps
          (ForestAlgebra.LinearFunctional.ofCharacter χ)
          (ForestAlgebra.LinearFunctional.ofCharacter ψ) x =
        (evalByCharacters χ ψ).toLinearMap x) x ?_ ?_ ?_
  · intro term
    change
      evalByLinearMaps
          (ForestAlgebra.LinearFunctional.ofCharacter χ)
          (ForestAlgebra.LinearFunctional.ofCharacter ψ)
          (ofPair (R := R) term) =
        evalByCharacters χ ψ (ofPair (R := R) term)
    simp [ForestAlgebra.LinearFunctional.ofCharacter, PTree.evalCoproductTerm,
      ForestAlgebra.Character.evalForest]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

@[simp]
theorem evalByCharacters_coproduct (χ ψ : ForestAlgebra.Character R)
    (t : PTree) :
    evalByCharacters χ ψ (PTree.coproduct (R := R) t) =
      PTree.convolutionCoeff χ ψ t := by
  simp [
    PTree.coproduct,
    PTree.convolutionCoeff,
    evalByCharacters_sumTerms
  ]

@[simp]
theorem evalByCharacters_coproductList (χ ψ : ForestAlgebra.Character R)
    (ts : List PTree) :
    evalByCharacters χ ψ (PTree.coproductList (R := R) ts) =
      PTree.convolutionForestCoeff χ ψ ts := by
  simp [
    PTree.coproductList,
    PTree.convolutionForestCoeff,
    evalByCharacters_sumTerms
  ]

end

end ForestTensorAlgebra

namespace ForestTripleTensorAlgebra

noncomputable section

variable {R : Type u} [CommSemiring R]

private def characterTripleMonoidHom
    (χ ψ η : ForestAlgebra.Character R) :
    Multiplicative (RootedForest × RootedForest × RootedForest) →* R where
  toFun term := PTree.evalTripleCoproductTerm χ ψ η (Multiplicative.toAdd term)
  map_one' := by
    change
      PTree.evalTripleCoproductTerm χ ψ η
        (0 : RootedForest × RootedForest × RootedForest) = 1
    simp
  map_mul' x y := by
    change
      PTree.evalTripleCoproductTerm χ ψ η
          (Multiplicative.toAdd (x * y)) =
        PTree.evalTripleCoproductTerm χ ψ η (Multiplicative.toAdd x) *
          PTree.evalTripleCoproductTerm χ ψ η (Multiplicative.toAdd y)
    change
      PTree.evalTripleCoproductTerm χ ψ η
          (Multiplicative.toAdd x + Multiplicative.toAdd y) =
        PTree.evalTripleCoproductTerm χ ψ η (Multiplicative.toAdd x) *
          PTree.evalTripleCoproductTerm χ ψ η (Multiplicative.toAdd y)
    simp

/-- Evaluate the triple tensor-coded forest algebra using three characters. -/
def evalByCharacters (χ ψ η : ForestAlgebra.Character R) :
    ForestTripleTensorAlgebra R →ₐ[R] R :=
  (AddMonoidAlgebra.lift R R (RootedForest × RootedForest × RootedForest))
    (characterTripleMonoidHom χ ψ η)

@[simp]
theorem evalByCharacters_ofTriple (χ ψ η : ForestAlgebra.Character R)
    (term : RootedForest × RootedForest × RootedForest) :
    evalByCharacters χ ψ η (ofTriple (R := R) term) =
      PTree.evalTripleCoproductTerm χ ψ η term := by
  simp [evalByCharacters, ofTriple, characterTripleMonoidHom]

theorem evalByCharacters_sumTerms (χ ψ η : ForestAlgebra.Character R)
    (terms : List (RootedForest × RootedForest × RootedForest)) :
    evalByCharacters χ ψ η (sumTerms (R := R) terms) =
      PTree.evalTripleCoproductTerms χ ψ η terms := by
  induction terms with
  | nil =>
      simp [sumTerms, PTree.evalTripleCoproductTerms]
  | cons term terms ih =>
      rw [
        sumTerms_cons,
        PTree.evalTripleCoproductTerms_cons,
        map_add,
        evalByCharacters_ofTriple,
        ih
      ]

@[simp]
theorem evalByCharacters_includeLeftPair
    (χ ψ η : ForestAlgebra.Character R) (x : ForestTensorAlgebra R) :
    evalByCharacters χ ψ η (includeLeftPair (R := R) x) =
      ForestTensorAlgebra.evalByCharacters χ ψ x := by
  change
    ((evalByCharacters χ ψ η).comp (includeLeftPair (R := R))) x =
      ForestTensorAlgebra.evalByCharacters χ ψ x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := RootedForest × RootedForest) (by
    intro term
    change
      evalByCharacters χ ψ η
          (includeLeftPair (R := R) (ForestTensorAlgebra.ofPair (R := R) term)) =
        ForestTensorAlgebra.evalByCharacters χ ψ
          (ForestTensorAlgebra.ofPair (R := R) term)
    simp [PTree.evalTripleCoproductTerm, PTree.evalCoproductTerm]) (by ext)) x

@[simp]
theorem evalByCharacters_includeRightPair
    (χ ψ η : ForestAlgebra.Character R) (x : ForestTensorAlgebra R) :
    evalByCharacters χ ψ η (includeRightPair (R := R) x) =
      ForestTensorAlgebra.evalByCharacters ψ η x := by
  change
    ((evalByCharacters χ ψ η).comp (includeRightPair (R := R))) x =
      ForestTensorAlgebra.evalByCharacters ψ η x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := RootedForest × RootedForest) (by
    intro term
    change
      evalByCharacters χ ψ η
          (includeRightPair (R := R) (ForestTensorAlgebra.ofPair (R := R) term)) =
        ForestTensorAlgebra.evalByCharacters ψ η
          (ForestTensorAlgebra.ofPair (R := R) term)
    simp [PTree.evalTripleCoproductTerm, PTree.evalCoproductTerm]) (by ext)) x

end

end ForestTripleTensorAlgebra

namespace RootedForest

noncomputable section

variable {R : Type u} [CommSemiring R]

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

/-- Character convolution evaluated on a non-planar rooted forest. -/
def convolutionCoeff (χ ψ : ForestAlgebra.Character R) (φ : RootedForest) : R :=
  ForestTensorAlgebra.evalByCharacters χ ψ (RootedForest.coproduct (R := R) φ)

@[simp]
theorem convolutionCoeff_zero (χ ψ : ForestAlgebra.Character R) :
    convolutionCoeff χ ψ 0 = 1 := by
  simp [convolutionCoeff]

@[simp]
theorem convolutionCoeff_empty (χ ψ : ForestAlgebra.Character R) :
    convolutionCoeff χ ψ RootedForest.empty = 1 := by
  simp [convolutionCoeff, RootedForest.empty]

@[simp]
theorem convolutionCoeff_singleton (χ ψ : ForestAlgebra.Character R) (τ : RootedTree) :
    convolutionCoeff χ ψ (RootedForest.singleton τ) =
      PTree.convolutionCoeff χ ψ (Quotient.out τ) := by
  simp [convolutionCoeff]

theorem convolutionCoeff_singleton_ofPTree
    (χ ψ : ForestAlgebra.Character R) (t : PTree) :
    convolutionCoeff χ ψ (RootedForest.singleton (RootedTree.ofPTree t)) =
      PTree.convolutionCoeff χ ψ t := by
  rw [convolutionCoeff_singleton]
  exact PTree.convolutionCoeff_perm χ ψ (RootedTree.out_perm_ofPTree t)

@[simp]
theorem convolutionCoeff_add (χ ψ : ForestAlgebra.Character R) (φ η : RootedForest) :
    convolutionCoeff χ ψ (φ + η) =
      convolutionCoeff χ ψ φ * convolutionCoeff χ ψ η := by
  simp [convolutionCoeff]

theorem convolutionCoeff_unit_right (χ : ForestAlgebra.Character R) (φ : RootedForest) :
    convolutionCoeff χ (ForestAlgebra.counit R) φ = χ.evalForest φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change convolutionCoeff χ (ForestAlgebra.counit R) (ts : RootedForest) =
    χ.evalForest (ts : RootedForest)
  rw [convolutionCoeff]
  change
    ForestTensorAlgebra.evalByCharacters χ (ForestAlgebra.counit R)
        (PTree.coproductList (R := R) (ts.map Quotient.out)) =
      χ.evalForest (ts : RootedForest)
  rw [ForestTensorAlgebra.evalByCharacters_coproductList]
  rw [PTree.convolutionForestCoeff_unit_right]
  have h : (ts.map Quotient.out).map RootedTree.ofPTree = ts := by
    induction ts with
    | nil => rfl
    | cons τ ts ih =>
        simp only [List.map_cons]
        rw [show RootedTree.ofPTree (Quotient.out τ) = τ from Quotient.out_eq τ, ih]
  rw [h]

theorem convolutionCoeff_unit_left (χ : ForestAlgebra.Character R) (φ : RootedForest) :
    convolutionCoeff (ForestAlgebra.counit R) χ φ = χ.evalForest φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change convolutionCoeff (ForestAlgebra.counit R) χ (ts : RootedForest) =
    χ.evalForest (ts : RootedForest)
  rw [convolutionCoeff]
  change
    ForestTensorAlgebra.evalByCharacters (ForestAlgebra.counit R) χ
        (PTree.coproductList (R := R) (ts.map Quotient.out)) =
      χ.evalForest (ts : RootedForest)
  rw [ForestTensorAlgebra.evalByCharacters_coproductList]
  rw [PTree.convolutionForestCoeff_unit_left]
  have h : (ts.map Quotient.out).map RootedTree.ofPTree = ts := by
    induction ts with
    | nil => rfl
    | cons τ ts ih =>
        simp only [List.map_cons]
        rw [show RootedTree.ofPTree (Quotient.out τ) = τ from Quotient.out_eq τ, ih]
  rw [h]

end

end RootedForest

namespace RootedTree

noncomputable section

variable {R : Type u} [CommSemiring R]

/-- Character convolution coefficient on a non-planar rooted tree. -/
def convolutionCoeff (χ ψ : ForestAlgebra.Character R) (τ : RootedTree) : R :=
  ForestTensorAlgebra.evalByCharacters χ ψ (RootedTree.coproduct (R := R) τ)

theorem convolutionCoeff_eq_singleton
    (χ ψ : ForestAlgebra.Character R) (τ : RootedTree) :
    convolutionCoeff χ ψ τ =
      RootedForest.convolutionCoeff χ ψ (RootedForest.singleton τ) := by
  rw [convolutionCoeff, RootedForest.convolutionCoeff,
    RootedForest.coproduct_singleton_tree]

theorem convolutionCoeff_out
    (χ ψ : ForestAlgebra.Character R) (τ : RootedTree) :
    convolutionCoeff χ ψ τ =
      PTree.convolutionCoeff χ ψ (Quotient.out τ) := by
  rw [convolutionCoeff_eq_singleton, RootedForest.convolutionCoeff_singleton]

theorem convolutionCoeff_ofPTree
    (χ ψ : ForestAlgebra.Character R) (t : PTree) :
    convolutionCoeff χ ψ (RootedTree.ofPTree t) =
      PTree.convolutionCoeff χ ψ t := by
  rw [convolutionCoeff_out]
  exact PTree.convolutionCoeff_perm χ ψ (RootedTree.out_perm_ofPTree t)

theorem convolutionCoeff_unit_right
    (χ : ForestAlgebra.Character R) (τ : RootedTree) :
    convolutionCoeff χ (ForestAlgebra.counit R) τ =
      χ.evalForest (RootedForest.singleton τ) := by
  rw [convolutionCoeff_eq_singleton]
  exact RootedForest.convolutionCoeff_unit_right χ (RootedForest.singleton τ)

theorem convolutionCoeff_unit_left
    (χ : ForestAlgebra.Character R) (τ : RootedTree) :
    convolutionCoeff (ForestAlgebra.counit R) χ τ =
      χ.evalForest (RootedForest.singleton τ) := by
  rw [convolutionCoeff_eq_singleton]
  exact RootedForest.convolutionCoeff_unit_left χ (RootedForest.singleton τ)

end

end RootedTree

namespace ForestAlgebra
namespace Character

noncomputable section

variable {R : Type u} [CommSemiring R]

/-- The identity character for convolution. -/
def unit (R : Type u) [CommSemiring R] : Character R :=
  ForestAlgebra.counit R

@[simp]
theorem unit_evalForest (φ : RootedForest) :
    (unit R).evalForest φ = ForestAlgebra.counitCoeff (R := R) φ := by
  simp [unit, ForestAlgebra.Character.evalForest, ForestAlgebra.counit_ofForest]

theorem unit_eq_counit : unit R = ForestAlgebra.counit R := rfl

@[simp]
theorem linearFunctional_ofCharacter_unit :
    LinearFunctional.ofCharacter (unit R) = LinearFunctional.counit R :=
  rfl

/-- Character convolution induced by the BCK coproduct. -/
def convolution (χ ψ : Character R) : Character R :=
  (ForestTensorAlgebra.evalByCharacters χ ψ).comp (ForestAlgebra.coproduct R)

@[simp]
theorem convolution_evalForest (χ ψ : Character R) (φ : RootedForest) :
    (convolution χ ψ).evalForest φ = RootedForest.convolutionCoeff χ ψ φ := by
  simp [ForestAlgebra.Character.evalForest, convolution, RootedForest.convolutionCoeff]

@[simp]
theorem convolution_ofForest (χ ψ : Character R) (φ : RootedForest) :
    convolution χ ψ (ofForest (R := R) φ) = RootedForest.convolutionCoeff χ ψ φ := by
  simpa [ForestAlgebra.Character.evalForest] using convolution_evalForest χ ψ φ

theorem linearFunctional_ofCharacter_convolution (χ ψ : Character R) :
    LinearFunctional.ofCharacter (convolution χ ψ) =
      LinearFunctional.convolution
        (LinearFunctional.ofCharacter χ)
        (LinearFunctional.ofCharacter ψ) := by
  rw [convolution, LinearFunctional.ofCharacter, LinearFunctional.convolution,
    ForestTensorAlgebra.evalByLinearMaps_ofCharacter]
  rfl

theorem linearFunctional_ofCharacter_injective :
    Function.Injective
      (LinearFunctional.ofCharacter : Character R → LinearFunctional R) := by
  intro χ ψ h
  apply ForestAlgebra.Character.ext
  intro φ
  have hφ :=
    congrArg (fun f : LinearFunctional R => f (ofForest (R := R) φ)) h
  simpa [LinearFunctional.ofCharacter, ForestAlgebra.Character.evalForest] using hφ

theorem convolution_unit_right (χ : Character R) :
    convolution χ (unit R) = χ := by
  change convolution χ (ForestAlgebra.counit R) = χ
  apply ForestAlgebra.Character.ext
  intro φ
  change
    (convolution χ (ForestAlgebra.counit R)).evalForest
        φ = χ.evalForest φ
  rw [convolution_evalForest, RootedForest.convolutionCoeff_unit_right]

theorem convolution_unit_left (χ : Character R) :
    convolution (unit R) χ = χ := by
  change convolution (ForestAlgebra.counit R) χ = χ
  apply ForestAlgebra.Character.ext
  intro φ
  change
    (convolution (ForestAlgebra.counit R) χ).evalForest
        φ = χ.evalForest φ
  rw [convolution_evalForest, RootedForest.convolutionCoeff_unit_left]

theorem linearFunctional_convolution_compAntipode_ofCharacter_left
    {R : Type u} [CommRing R] (χ : Character R) :
    LinearFunctional.convolution
        (LinearFunctional.compAntipode (LinearFunctional.ofCharacter χ))
        (LinearFunctional.ofCharacter χ) =
      LinearFunctional.ofCharacter (unit R) := by
  rw [LinearFunctional.convolution_compAntipode_ofCharacter_left,
    linearFunctional_ofCharacter_unit]

theorem linearFunctional_convolution_compAntipode_ofCharacter_right
    {R : Type u} [CommRing R] (χ : Character R) :
    LinearFunctional.convolution
        (LinearFunctional.ofCharacter χ)
        (LinearFunctional.compAntipode (LinearFunctional.ofCharacter χ)) =
      LinearFunctional.ofCharacter (unit R) := by
  rw [LinearFunctional.compAntipode_ofCharacter_eq_compRightAntipode χ]
  rw [LinearFunctional.convolution_compRightAntipode_ofCharacter_right,
    linearFunctional_ofCharacter_unit]

theorem convolution_left_cancel
    {R : Type u} [CommRing R] {χ ψ η : Character R}
    (h : convolution χ ψ = convolution χ η) : ψ = η := by
  have hlin := congrArg LinearFunctional.ofCharacter h
  rw [linearFunctional_ofCharacter_convolution,
    linearFunctional_ofCharacter_convolution] at hlin
  have hcancel :=
    congrArg
      (fun f : LinearFunctional R =>
        LinearFunctional.convolution (inverseLinearFunctional χ) f) hlin
  rw [← LinearFunctional.convolution_assoc,
    convolution_inverseLinearFunctional_left,
    LinearFunctional.convolution_counit_left,
    ← LinearFunctional.convolution_assoc,
    convolution_inverseLinearFunctional_left,
    LinearFunctional.convolution_counit_left] at hcancel
  exact linearFunctional_ofCharacter_injective hcancel

theorem convolution_right_cancel
    {R : Type u} [CommRing R] {χ ψ η : Character R}
    (h : convolution ψ χ = convolution η χ) : ψ = η := by
  have hlin := congrArg LinearFunctional.ofCharacter h
  rw [linearFunctional_ofCharacter_convolution,
    linearFunctional_ofCharacter_convolution] at hlin
  have hcancel :=
    congrArg
      (fun f : LinearFunctional R =>
        LinearFunctional.convolution f (inverseLinearFunctional χ)) hlin
  rw [LinearFunctional.convolution_assoc,
    convolution_inverseLinearFunctional_right,
    LinearFunctional.convolution_counit_right,
    LinearFunctional.convolution_assoc,
    convolution_inverseLinearFunctional_right,
    LinearFunctional.convolution_counit_right] at hcancel
  exact linearFunctional_ofCharacter_injective hcancel

theorem evalByCharacters_coproductLeft
    (χ ψ η : Character R) (x : ForestTensorAlgebra R) :
    ForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (ForestTripleTensorAlgebra.coproductLeft (R := R) x) =
      ForestTensorAlgebra.evalByCharacters (convolution χ ψ) η x := by
  change
    ((ForestTripleTensorAlgebra.evalByCharacters χ ψ η).comp
        (ForestTripleTensorAlgebra.coproductLeft (R := R))) x =
      ForestTensorAlgebra.evalByCharacters (convolution χ ψ) η x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := RootedForest × RootedForest) (by
    intro term
    change
      ForestTripleTensorAlgebra.evalByCharacters χ ψ η
          (ForestTripleTensorAlgebra.coproductLeft (R := R)
            (ForestTensorAlgebra.ofPair (R := R) term)) =
        ForestTensorAlgebra.evalByCharacters (convolution χ ψ) η
          (ForestTensorAlgebra.ofPair (R := R) term)
    simp [ForestTripleTensorAlgebra.ofForests, PTree.evalTripleCoproductTerm,
      PTree.evalCoproductTerm, convolution, ForestAlgebra.Character.evalForest]) (by ext)) x

theorem evalByCharacters_coproductRight
    (χ ψ η : Character R) (x : ForestTensorAlgebra R) :
    ForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (ForestTripleTensorAlgebra.coproductRight (R := R) x) =
      ForestTensorAlgebra.evalByCharacters χ (convolution ψ η) x := by
  change
    ((ForestTripleTensorAlgebra.evalByCharacters χ ψ η).comp
        (ForestTripleTensorAlgebra.coproductRight (R := R))) x =
      ForestTensorAlgebra.evalByCharacters χ (convolution ψ η) x
  exact DFunLike.congr_fun (AddMonoidAlgebra.algHom_ext (M := RootedForest × RootedForest) (by
    intro term
    change
      ForestTripleTensorAlgebra.evalByCharacters χ ψ η
          (ForestTripleTensorAlgebra.coproductRight (R := R)
            (ForestTensorAlgebra.ofPair (R := R) term)) =
        ForestTensorAlgebra.evalByCharacters χ (convolution ψ η)
          (ForestTensorAlgebra.ofPair (R := R) term)
    simp [ForestTripleTensorAlgebra.ofForests, PTree.evalTripleCoproductTerm,
      PTree.evalCoproductTerm, convolution, ForestAlgebra.Character.evalForest]) (by ext)) x

theorem evalByCharacters_forestCoproductLeft
    (χ ψ η : Character R) (x : ForestAlgebra R) :
    ForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (ForestAlgebra.coproductLeft R x) =
      convolution (convolution χ ψ) η x := by
  rw [ForestAlgebra.coproductLeft]
  change
    ForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (ForestTripleTensorAlgebra.coproductLeft
          (ForestAlgebra.coproduct R x)) =
      ForestTensorAlgebra.evalByCharacters (convolution χ ψ) η
        (ForestAlgebra.coproduct R x)
  rw [evalByCharacters_coproductLeft]

theorem evalByCharacters_forestCoproductRight
    (χ ψ η : Character R) (x : ForestAlgebra R) :
    ForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (ForestAlgebra.coproductRight R x) =
      convolution χ (convolution ψ η) x := by
  rw [ForestAlgebra.coproductRight]
  change
    ForestTripleTensorAlgebra.evalByCharacters χ ψ η
        (ForestTripleTensorAlgebra.coproductRight
          (ForestAlgebra.coproduct R x)) =
      ForestTensorAlgebra.evalByCharacters χ (convolution ψ η)
        (ForestAlgebra.coproduct R x)
  rw [evalByCharacters_coproductRight]

theorem evalTripleCoproductTerms_coproductLeftTerms
    (χ ψ η : Character R) (terms : List (RootedForest × RootedForest)) :
    PTree.evalTripleCoproductTerms χ ψ η
        (ForestTripleTensorAlgebra.coproductLeftTerms terms) =
      PTree.evalCoproductTerms (convolution χ ψ) η terms := by
  rw [← ForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    ForestTripleTensorAlgebra.sumTerms_coproductLeftTerms,
    evalByCharacters_coproductLeft,
    ForestTensorAlgebra.evalByCharacters_sumTerms]

theorem evalTripleCoproductTerms_coproductRightTerms
    (χ ψ η : Character R) (terms : List (RootedForest × RootedForest)) :
    PTree.evalTripleCoproductTerms χ ψ η
        (ForestTripleTensorAlgebra.coproductRightTerms terms) =
      PTree.evalCoproductTerms χ (convolution ψ η) terms := by
  rw [← ForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    ForestTripleTensorAlgebra.sumTerms_coproductRightTerms,
    evalByCharacters_coproductRight,
    ForestTensorAlgebra.evalByCharacters_sumTerms]

theorem evalTripleCoproductTerms_coproductLeftTerms_ptree
    (χ ψ η : Character R) (t : PTree) :
    PTree.evalTripleCoproductTerms χ ψ η
        (ForestTripleTensorAlgebra.coproductLeftTerms (PTree.coproductTerms t)) =
      PTree.convolutionCoeff (convolution χ ψ) η t := by
  rw [evalTripleCoproductTerms_coproductLeftTerms, PTree.convolutionCoeff]

theorem evalTripleCoproductTerms_coproductRightTerms_ptree
    (χ ψ η : Character R) (t : PTree) :
    PTree.evalTripleCoproductTerms χ ψ η
        (ForestTripleTensorAlgebra.coproductRightTerms (PTree.coproductTerms t)) =
      PTree.convolutionCoeff χ (convolution ψ η) t := by
  rw [evalTripleCoproductTerms_coproductRightTerms, PTree.convolutionCoeff]

theorem evalTripleCoproductTerms_nestedCoproductLeftTerms
    (χ ψ η : Character R) (t : PTree) :
    PTree.evalTripleCoproductTerms χ ψ η (PTree.nestedCoproductLeftTerms t) =
      PTree.convolutionCoeff (convolution χ ψ) η t := by
  rw [← ForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    ForestTripleTensorAlgebra.sumTerms_nestedCoproductLeftTerms,
    ForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    evalTripleCoproductTerms_coproductLeftTerms_ptree]

theorem evalTripleCoproductTerms_nestedCoproductRightTerms
    (χ ψ η : Character R) (t : PTree) :
    PTree.evalTripleCoproductTerms χ ψ η (PTree.nestedCoproductRightTerms t) =
      PTree.convolutionCoeff χ (convolution ψ η) t := by
  rw [← ForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    ForestTripleTensorAlgebra.sumTerms_nestedCoproductRightTerms,
    ForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    evalTripleCoproductTerms_coproductRightTerms_ptree]

theorem evalTripleCoproductTerms_nestedCoproductLeftTerms_listRelPerm
    (χ ψ η : Character R) {t u : PTree}
    (h : PTree.ListRelPerm PTree.Cut.Perm (PTree.cuts t) (PTree.cuts u)) :
    PTree.evalTripleCoproductTerms χ ψ η (PTree.nestedCoproductLeftTerms t) =
      PTree.evalTripleCoproductTerms χ ψ η (PTree.nestedCoproductLeftTerms u) := by
  rw [← ForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    ForestTripleTensorAlgebra.sumTerms_nestedCoproductLeftTerms_listRelPerm (R := R) h,
    ForestTripleTensorAlgebra.evalByCharacters_sumTerms]

theorem evalTripleCoproductTerms_nestedCoproductRightTerms_listRelPerm
    (χ ψ η : Character R) {t u : PTree}
    (h : PTree.ListRelPerm PTree.Cut.Perm (PTree.cuts t) (PTree.cuts u)) :
    PTree.evalTripleCoproductTerms χ ψ η (PTree.nestedCoproductRightTerms t) =
      PTree.evalTripleCoproductTerms χ ψ η (PTree.nestedCoproductRightTerms u) := by
  rw [← ForestTripleTensorAlgebra.evalByCharacters_sumTerms,
    ForestTripleTensorAlgebra.sumTerms_nestedCoproductRightTerms_listRelPerm (R := R) h,
    ForestTripleTensorAlgebra.evalByCharacters_sumTerms]

theorem evalTripleCoproductTerms_nestedCoproductLeftTerms_perm
    (χ ψ η : Character R) {t u : PTree} (h : PTree.Perm t u) :
    PTree.evalTripleCoproductTerms χ ψ η (PTree.nestedCoproductLeftTerms t) =
      PTree.evalTripleCoproductTerms χ ψ η (PTree.nestedCoproductLeftTerms u) :=
  evalTripleCoproductTerms_nestedCoproductLeftTerms_listRelPerm χ ψ η
    (PTree.cuts_listRelPerm_of_perm h)

theorem evalTripleCoproductTerms_nestedCoproductRightTerms_perm
    (χ ψ η : Character R) {t u : PTree} (h : PTree.Perm t u) :
    PTree.evalTripleCoproductTerms χ ψ η (PTree.nestedCoproductRightTerms t) =
      PTree.evalTripleCoproductTerms χ ψ η (PTree.nestedCoproductRightTerms u) :=
  evalTripleCoproductTerms_nestedCoproductRightTerms_listRelPerm χ ψ η
    (PTree.cuts_listRelPerm_of_perm h)

theorem convolution_assoc_of_coproduct_eq
    (hcoassoc : ∀ x : ForestAlgebra R,
      ForestAlgebra.coproductLeft R x = ForestAlgebra.coproductRight R x)
    (χ ψ η : Character R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) := by
  apply ForestAlgebra.Character.ext
  intro φ
  have h :=
    congrArg (ForestTripleTensorAlgebra.evalByCharacters χ ψ η)
      (hcoassoc (ofForest (R := R) φ))
  change
    convolution (convolution χ ψ) η (ofForest (R := R) φ) =
      convolution χ (convolution ψ η) (ofForest (R := R) φ)
  rw [← evalByCharacters_forestCoproductLeft χ ψ η (ofForest (R := R) φ),
    ← evalByCharacters_forestCoproductRight χ ψ η (ofForest (R := R) φ)]
  exact h

theorem convolution_assoc_of_coproductLeft_eq_coproductRight
    (hcoassoc : ForestAlgebra.coproductLeft R = ForestAlgebra.coproductRight R)
    (χ ψ η : Character R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) :=
  convolution_assoc_of_coproduct_eq (fun x => by rw [hcoassoc]) χ ψ η

theorem convolution_assoc_of_coproduct_eq_singletons
    (hcoassoc : ∀ τ : RootedTree,
      ForestAlgebra.coproductLeft R
          (ofForest (R := R) (RootedForest.singleton τ)) =
        ForestAlgebra.coproductRight R
          (ofForest (R := R) (RootedForest.singleton τ)))
    (χ ψ η : Character R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) := by
  exact convolution_assoc_of_coproduct_eq
    (fun x => by
      rw [ForestAlgebra.coproductLeft_eq_coproductRight_of_singletons
        (R := R) hcoassoc])
    χ ψ η

theorem convolution_assoc_of_coproduct_eq_ptree_singletons
    (hcoassoc : ∀ t : PTree,
      ForestAlgebra.coproductLeft R
          (ofForest (R := R) (RootedForest.singleton (RootedTree.ofPTree t))) =
        ForestAlgebra.coproductRight R
          (ofForest (R := R) (RootedForest.singleton (RootedTree.ofPTree t))))
    (χ ψ η : Character R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) := by
  exact convolution_assoc_of_coproduct_eq
    (fun x => by
      rw [ForestAlgebra.coproductLeft_eq_coproductRight_of_ptree_singletons
        (R := R) hcoassoc])
    χ ψ η

theorem convolution_assoc_of_coproduct_eq_ptree_coproductTerms
    (hcoassoc : ∀ t : PTree,
      ForestTripleTensorAlgebra.sumTerms (R := R)
          (ForestTripleTensorAlgebra.coproductLeftTerms (PTree.coproductTerms t)) =
        ForestTripleTensorAlgebra.sumTerms (R := R)
          (ForestTripleTensorAlgebra.coproductRightTerms (PTree.coproductTerms t)))
    (χ ψ η : Character R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) := by
  exact convolution_assoc_of_coproduct_eq
    (fun x => by
      rw [ForestAlgebra.coproductLeft_eq_coproductRight_of_ptree_coproductTerms
        (R := R) hcoassoc])
    χ ψ η

theorem convolution_assoc_of_nestedCoproductTerms
    (hcoassoc : ∀ t : PTree,
      ForestTripleTensorAlgebra.sumTerms (R := R) (PTree.nestedCoproductLeftTerms t) =
        ForestTripleTensorAlgebra.sumTerms (R := R) (PTree.nestedCoproductRightTerms t))
    (χ ψ η : Character R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) := by
  exact convolution_assoc_of_coproduct_eq
    (fun x => by
      rw [ForestAlgebra.coproductLeft_eq_coproductRight_of_nestedCoproductTerms
        (R := R) hcoassoc])
    χ ψ η

theorem convolution_assoc_of_nestedCoproductTerms_perm
    (hcoassoc : ∀ t : PTree,
      (PTree.nestedCoproductLeftTerms t).Perm (PTree.nestedCoproductRightTerms t))
    (χ ψ η : Character R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) :=
  convolution_assoc_of_nestedCoproductTerms
    (fun t => ForestTripleTensorAlgebra.sumTerms_perm (R := R) (hcoassoc t)) χ ψ η

theorem convolution_assoc (χ ψ η : Character R) :
    convolution (convolution χ ψ) η = convolution χ (convolution ψ η) :=
  convolution_assoc_of_coproductLeft_eq_coproductRight
    (ForestAlgebra.coproductLeft_eq_coproductRight (R := R)) χ ψ η

noncomputable instance instMonoid : Monoid (Character R) where
  one := unit R
  mul := convolution
  mul_assoc := convolution_assoc
  one_mul := convolution_unit_left
  mul_one := convolution_unit_right

end

end Character
end ForestAlgebra

end HopfAlgebras
