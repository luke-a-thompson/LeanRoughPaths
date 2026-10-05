/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Trees.Labelled
import HopfAlgebras.Forests.Rooted

/-!
# Labelled Rooted Forests

This file defines labelled rooted forests as multisets of non-planar labelled
rooted trees. It also defines labelled branches and labelled grafting, the
analogue of the `B_+` operator where the new root receives a specified label.

## Main definitions

* `LRootedForest α` - non-planar labelled rooted forests
* `LRootedTree.branches` - the forest below the root of a labelled tree
* `LRootedForest.graft` - labelled grafting onto a new root
* `LRootedForest.butcherProduct` - grafting a labelled forest onto a labelled tree root
* `LRootedForest.treeFactorial` - product of labelled tree factorials
* `LRootedForest.erase` - forget labels in a labelled forest
* `LRootedForest.mapLabels` - change labels in a labelled forest
-/

namespace HopfAlgebras

universe u v w

/-- Non-planar labelled rooted forests. -/
abbrev LRootedForest (α : Type u) : Type u :=
  Multiset (LRootedTree α)

namespace PLTree

variable {α : Type u}

/-- Two labelled planar tree lists represent the same non-planar labelled forest. -/
def ForestPerm (ts us : List (PLTree α)) : Prop :=
  ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) =
    ((us.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α)

theorem ForestPerm.refl (ts : List (PLTree α)) : ForestPerm ts ts :=
  rfl

theorem ForestPerm.symm {ts us : List (PLTree α)} (h : ForestPerm ts us) :
    ForestPerm us ts :=
  Eq.symm h

theorem ForestPerm.trans {ts us vs : List (PLTree α)}
    (h₁ : ForestPerm ts us) (h₂ : ForestPerm us vs) :
    ForestPerm ts vs :=
  Eq.trans h₁ h₂

theorem ForestPerm.of_list_perm {ts us : List (PLTree α)} (h : ts.Perm us) :
    ForestPerm ts us :=
  Quotient.sound (h.map LRootedTree.ofPLTree)

theorem ForestPerm.of_forall₂_perm {ts us : List (PLTree α)}
    (h : List.Forall₂ PLTree.Perm ts us) :
    ForestPerm ts us :=
  congrArg (fun vs : List (LRootedTree α) => (vs : LRootedForest α))
    (LRootedTree.map_ofPLTree_eq_of_forall₂_perm h)

theorem ForestPerm.cons_eq {t u : PLTree α} {ts us : List (PLTree α)}
    (ht : LRootedTree.ofPLTree t = LRootedTree.ofPLTree u) (h : ForestPerm ts us) :
    ForestPerm (t :: ts) (u :: us) := by
  dsimp [ForestPerm] at h ⊢
  simp only [List.map_cons]
  rw [ht]
  simpa using
    congrArg (fun φ : LRootedForest α => ({LRootedTree.ofPLTree u} : LRootedForest α) + φ)
      h

theorem ForestPerm.cons {t u : PLTree α} {ts us : List (PLTree α)}
    (ht : PLTree.Perm t u) (h : ForestPerm ts us) :
    ForestPerm (t :: ts) (u :: us) :=
  ForestPerm.cons_eq (Quotient.sound (show t ≈ u from ht)) h

theorem ForestPerm.append {ts us vs ws : List (PLTree α)}
    (h₁ : ForestPerm ts us) (h₂ : ForestPerm vs ws) :
    ForestPerm (ts ++ vs) (us ++ ws) := by
  dsimp [ForestPerm] at h₁ h₂ ⊢
  simpa [List.map_append] using congrArg₂ HAdd.hAdd h₁ h₂

end PLTree

namespace LRootedTree

variable {α : Type u}

private def branchesAux : PLTree α → LRootedForest α
  | .node _ ts => (ts.map LRootedTree.ofPLTree : LRootedForest α)

private theorem branchesAux_sound :
    ∀ {t u : PLTree α}, PLTree.Perm t u → branchesAux t = branchesAux u
  | _, _, .node hp hf => by
      have hp' :=
        @Quotient.sound (List (LRootedTree α)) (List.isSetoid (LRootedTree α)) _ _
          (hp.map LRootedTree.ofPLTree)
      have hf' :=
        congrArg (fun ts : List (LRootedTree α) => (ts : LRootedForest α))
          (LRootedTree.map_ofPLTree_eq_of_forall₂_perm hf)
      exact hp'.trans hf'

/-- The forest immediately below the root of a non-planar labelled tree. -/
def branches : LRootedTree α → LRootedForest α :=
  Quotient.lift branchesAux (fun _ _ h => branchesAux_sound h)

@[simp]
theorem branches_ofPLTree_node (a : α) (ts : List (PLTree α)) :
    branches (ofPLTree (.node a ts)) = (ts.map ofPLTree : LRootedForest α) :=
  rfl

end LRootedTree

namespace LRootedForest

noncomputable section

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The empty labelled rooted forest. -/
def empty : LRootedForest α :=
  0

/-- The one-tree labelled forest. -/
def singleton (τ : LRootedTree α) : LRootedForest α :=
  {τ}

/-- Forget all labels in a labelled rooted forest. -/
def erase (φ : LRootedForest α) : RootedForest :=
  Multiset.map LRootedTree.erase φ

/-- Label every vertex of a rooted forest by the same label. -/
def constLabel (a : α) (φ : RootedForest) : LRootedForest α :=
  Multiset.map (LRootedTree.constLabel a) φ

/-- Change all labels in a labelled rooted forest. -/
def mapLabels (f : α → β) (φ : LRootedForest α) : LRootedForest β :=
  Multiset.map (LRootedTree.map f) φ

/-- The total number of vertices in a labelled rooted forest. -/
def order (φ : LRootedForest α) : Nat :=
  (Multiset.map LRootedTree.order φ).sum

/-- Predicate for labelled rooted forests of a fixed order. -/
def IsOfOrder (φ : LRootedForest α) (n : Nat) : Prop :=
  order φ = n

/-- The product of the tree factorials in a labelled rooted forest. -/
def treeFactorial (φ : LRootedForest α) : Nat :=
  (Multiset.map LRootedTree.treeFactorial φ).prod

@[simp]
theorem erase_empty : erase (empty : LRootedForest α) = RootedForest.empty := by
  simp [erase, empty, RootedForest.empty]

@[simp]
theorem constLabel_empty (a : α) :
    constLabel a RootedForest.empty = (empty : LRootedForest α) := by
  simp [constLabel, empty, RootedForest.empty]

@[simp]
theorem constLabel_zero (a : α) : constLabel a (0 : RootedForest) = 0 := by
  simp [constLabel]

@[simp]
theorem mapLabels_empty (f : α → β) : mapLabels f (empty : LRootedForest α) = empty := by
  simp [mapLabels, empty]

@[simp]
theorem order_empty : order (empty : LRootedForest α) = 0 := by
  simp [order, empty]

@[simp]
theorem order_zero : order (0 : LRootedForest α) = 0 := by
  simp [order]

@[simp]
theorem treeFactorial_empty : treeFactorial (empty : LRootedForest α) = 1 := by
  simp [treeFactorial, empty]

@[simp]
theorem treeFactorial_zero : treeFactorial (0 : LRootedForest α) = 1 := by
  simp [treeFactorial]

@[simp]
theorem erase_singleton (τ : LRootedTree α) :
    erase (singleton τ) = RootedForest.singleton (LRootedTree.erase τ) := by
  simp [erase, singleton, RootedForest.singleton]

theorem erase_out_perm (φ : LRootedForest α) :
    List.Perm ((Quotient.out φ).map LRootedTree.erase) (Quotient.out (erase φ)) := by
  exact Quotient.exact <| by
    calc
      (((Quotient.out φ).map LRootedTree.erase : List RootedTree) : RootedForest)
          = erase (((Quotient.out φ : List (LRootedTree α)) : LRootedForest α)) := rfl
      _ = erase φ := congrArg erase (Quotient.out_eq φ)
      _ = ((Quotient.out (erase φ) : List RootedTree) : RootedForest) :=
          (Quotient.out_eq (erase φ)).symm

theorem constLabel_out_perm (a : α) (φ : RootedForest) :
    List.Perm ((Quotient.out φ).map (LRootedTree.constLabel a))
      (Quotient.out (constLabel a φ)) := by
  exact Quotient.exact <| by
    calc
      (((Quotient.out φ).map (LRootedTree.constLabel a) :
          List (LRootedTree α)) : LRootedForest α)
          = constLabel a (((Quotient.out φ : List RootedTree) : RootedForest)) := rfl
      _ = constLabel a φ := congrArg (constLabel a) (Quotient.out_eq φ)
      _ = ((Quotient.out (constLabel a φ) : List (LRootedTree α)) :
          LRootedForest α) := (Quotient.out_eq (constLabel a φ)).symm

theorem mapLabels_out_perm (f : α → β) (φ : LRootedForest α) :
    List.Perm ((Quotient.out φ).map (LRootedTree.map f))
      (Quotient.out (mapLabels f φ)) := by
  exact Quotient.exact <| by
    calc
      (((Quotient.out φ).map (LRootedTree.map f) :
          List (LRootedTree β)) : LRootedForest β)
          = mapLabels f (((Quotient.out φ : List (LRootedTree α)) :
              LRootedForest α)) := rfl
      _ = mapLabels f φ := congrArg (mapLabels f) (Quotient.out_eq φ)
      _ = ((Quotient.out (mapLabels f φ) : List (LRootedTree β)) :
          LRootedForest β) := (Quotient.out_eq (mapLabels f φ)).symm

@[simp]
theorem constLabel_singleton (a : α) (τ : RootedTree) :
    constLabel a (RootedForest.singleton τ) = singleton (LRootedTree.constLabel a τ) := by
  simp [constLabel, singleton, RootedForest.singleton]

@[simp]
theorem mapLabels_singleton (f : α → β) (τ : LRootedTree α) :
    mapLabels f (singleton τ) = singleton (LRootedTree.map f τ) := by
  simp [mapLabels, singleton]

@[simp]
theorem order_singleton (τ : LRootedTree α) :
    order (singleton τ) = LRootedTree.order τ := by
  simp [order, singleton]

theorem singleton_ne_zero (τ : LRootedTree α) : singleton τ ≠ 0 := by
  intro h
  have horder : order (singleton τ) = 0 := by
    rw [h]
    simp
  rw [order_singleton] at horder
  exact (Nat.ne_of_gt (LRootedTree.order_pos τ)) horder

@[simp]
theorem treeFactorial_singleton (τ : LRootedTree α) :
    treeFactorial (singleton τ) = LRootedTree.treeFactorial τ := by
  simp [treeFactorial, singleton]

@[simp]
theorem erase_add (φ ψ : LRootedForest α) :
    erase (φ + ψ) = erase φ + erase ψ := by
  simp [erase, Multiset.map_add]

@[simp]
theorem constLabel_add (a : α) (φ ψ : RootedForest) :
    constLabel a (φ + ψ) = constLabel a φ + constLabel a ψ := by
  simp [constLabel, Multiset.map_add]

@[simp]
theorem mapLabels_add (f : α → β) (φ ψ : LRootedForest α) :
    mapLabels f (φ + ψ) = mapLabels f φ + mapLabels f ψ := by
  simp [mapLabels, Multiset.map_add]

@[simp]
theorem mapLabels_id (φ : LRootedForest α) : mapLabels id φ = φ := by
  simp [mapLabels]

@[simp]
theorem mapLabels_comp (g : β → γ) (f : α → β) (φ : LRootedForest α) :
    mapLabels g (mapLabels f φ) = mapLabels (g ∘ f) φ := by
  simp [mapLabels, Multiset.map_map]

@[simp]
theorem erase_mapLabels (f : α → β) (φ : LRootedForest α) :
    erase (mapLabels f φ) = erase φ := by
  simp [erase, mapLabels, Multiset.map_map]

@[simp]
theorem erase_constLabel (a : α) (φ : RootedForest) :
    erase (constLabel a φ) = φ := by
  simp [erase, constLabel, Multiset.map_map]

theorem constLabel_injective (a : α) : Function.Injective (constLabel a) := by
  intro φ ψ h
  have hErase := congrArg erase h
  simpa using hErase

@[simp]
theorem constLabel_eq_constLabel_iff (a : α) {φ ψ : RootedForest} :
    constLabel a φ = constLabel a ψ ↔ φ = ψ := by
  constructor
  · intro h
    exact constLabel_injective a h
  · intro h
    rw [h]

@[simp]
theorem mapLabels_constLabel (f : α → β) (a : α) (φ : RootedForest) :
    mapLabels f (constLabel a φ) = constLabel (f a) φ := by
  simp [mapLabels, constLabel, Multiset.map_map]

theorem mapLabels_injective (f : α → β) (hf : Function.Injective f) :
    Function.Injective (mapLabels f : LRootedForest α → LRootedForest β) := by
  intro φ ψ h
  exact (Multiset.map_eq_map (LRootedTree.map_injective f hf)).1 (by
    simpa [mapLabels] using h)

theorem mapLabels_eq_mapLabels_iff_of_injective (f : α → β) (hf : Function.Injective f)
    {φ ψ : LRootedForest α} :
    mapLabels f φ = mapLabels f ψ ↔ φ = ψ := by
  constructor
  · intro h
    exact mapLabels_injective f hf h
  · intro h
    rw [h]

@[simp]
theorem order_add (φ ψ : LRootedForest α) :
    order (φ + ψ) = order φ + order ψ := by
  simp [order, Multiset.map_add]

@[simp]
theorem treeFactorial_add (φ ψ : LRootedForest α) :
    treeFactorial (φ + ψ) = treeFactorial φ * treeFactorial ψ := by
  simp [treeFactorial, Multiset.map_add]

@[simp]
theorem order_erase (φ : LRootedForest α) :
    RootedForest.order (erase φ) = order φ := by
  simp [erase, RootedForest.order, order, Multiset.map_map]

@[simp]
theorem treeFactorial_erase (φ : LRootedForest α) :
    RootedForest.treeFactorial (erase φ) = treeFactorial φ := by
  simp [erase, RootedForest.treeFactorial, treeFactorial, Multiset.map_map]

@[simp]
theorem order_ofPLTree_list :
    ∀ ts : List (PLTree α),
      order ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) =
        PLTree.orderList ts
  | [] => rfl
  | _ :: ts => by
      have ih := order_ofPLTree_list ts
      simp [order] at ih
      simp [order, PLTree.orderList, ih]

@[simp]
theorem treeFactorial_ofPLTree_list :
    ∀ ts : List (PLTree α),
      treeFactorial
          ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) =
        PLTree.treeFactorialList ts
  | [] => rfl
  | _ :: ts => by
      have ih := treeFactorial_ofPLTree_list ts
      simp [treeFactorial] at ih
      simp [treeFactorial, PLTree.treeFactorialList, ih]

@[simp]
theorem order_constLabel (a : α) (φ : RootedForest) :
    order (constLabel a φ) = RootedForest.order φ := by
  simp [constLabel, order, RootedForest.order, Multiset.map_map]

@[simp]
theorem treeFactorial_constLabel (a : α) (φ : RootedForest) :
    treeFactorial (constLabel a φ) = RootedForest.treeFactorial φ := by
  simp [constLabel, treeFactorial, RootedForest.treeFactorial, Multiset.map_map]

@[simp]
theorem order_mapLabels (f : α → β) (φ : LRootedForest α) :
    order (mapLabels f φ) = order φ := by
  simp [mapLabels, order, Multiset.map_map]

@[simp]
theorem treeFactorial_mapLabels (f : α → β) (φ : LRootedForest α) :
    treeFactorial (mapLabels f φ) = treeFactorial φ := by
  simp [mapLabels, treeFactorial, Multiset.map_map]

theorem treeFactorial_pos (φ : LRootedForest α) : 0 < treeFactorial φ := by
  have h := RootedForest.treeFactorial_pos (erase φ)
  rwa [treeFactorial_erase] at h

theorem treeFactorial_ne_zero (φ : LRootedForest α) : treeFactorial φ ≠ 0 :=
  Nat.ne_of_gt (treeFactorial_pos φ)

theorem order_coe_cons_pos (τ : LRootedTree α) (ts : List (LRootedTree α)) :
    0 < order (((τ :: ts) : List (LRootedTree α)) : LRootedForest α) := by
  have hτ := LRootedTree.order_pos τ
  simp [order]
  omega

@[simp]
theorem order_eq_zero_iff (φ : LRootedForest α) : order φ = 0 ↔ φ = 0 := by
  constructor
  · refine Quotient.inductionOn φ ?_
    intro ts h
    cases ts with
    | nil => rfl
    | cons τ ts =>
        have hpos := order_coe_cons_pos τ ts
        exact False.elim ((Nat.ne_of_gt hpos) h)
  · intro h
    rw [h]
    simp

theorem order_pos_iff_ne_zero (φ : LRootedForest α) :
    0 < order φ ↔ φ ≠ 0 := by
  constructor
  · intro h hzero
    rw [hzero] at h
    simp at h
  · intro h
    have horder : order φ ≠ 0 := fun hzero => h ((order_eq_zero_iff φ).1 hzero)
    omega

private theorem order_out (τ : LRootedTree α) :
    PLTree.order (Quotient.out τ) = LRootedTree.order τ := by
  rw [← LRootedTree.order_ofPLTree (Quotient.out τ)]
  rw [LRootedTree.ofPLTree_out τ]

private theorem orderList_out :
    ∀ ts : List (LRootedTree α),
      PLTree.orderList (ts.map Quotient.out) = (ts.map LRootedTree.order).sum
  | [] => rfl
  | τ :: ts => by
      simp [order_out τ, orderList_out ts]

private theorem forall₂_out_perm_ofPLTree :
    ∀ ts : List (PLTree α),
      List.Forall₂ PLTree.Perm ((ts.map LRootedTree.ofPLTree).map Quotient.out) ts
  | [] => .nil
  | t :: ts => .cons (LRootedTree.out_perm_ofPLTree t) (forall₂_out_perm_ofPLTree ts)

/-- Graft all roots in a labelled forest onto a new root with label `a`. -/
def graft (a : α) : LRootedForest α → LRootedTree α :=
  Quotient.lift
    (fun ts : List (LRootedTree α) =>
      LRootedTree.ofPLTree (.node a (ts.map Quotient.out)))
    (fun ts us h => by
      exact Quotient.sound <|
        PLTree.Perm.node (h.map Quotient.out) (PLTree.permForall₂_refl _))

@[simp]
theorem graft_coe (a : α) (ts : List (LRootedTree α)) :
    graft a (ts : LRootedForest α) =
      LRootedTree.ofPLTree (.node a (ts.map Quotient.out)) :=
  rfl

@[simp]
theorem graft_empty (a : α) :
    graft a (empty : LRootedForest α) = LRootedTree.ofPLTree (.node a []) :=
  rfl

@[simp]
theorem branches_graft (a : α) (φ : LRootedForest α) :
    LRootedTree.branches (graft a φ) = φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change (((ts.map Quotient.out).map LRootedTree.ofPLTree : List (LRootedTree α)) :
    LRootedForest α) = (ts : LRootedForest α)
  have h : (ts.map Quotient.out).map LRootedTree.ofPLTree = ts := by
    induction ts with
    | nil => rfl
    | cons τ ts ih =>
        simp [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ, ih]
  rw [h]

@[simp]
theorem rootLabel_graft (a : α) (φ : LRootedForest α) :
    LRootedTree.rootLabel (graft a φ) = a := by
  refine Quotient.inductionOn φ ?_
  intro ts
  rfl

theorem graft_injective (a : α) : Function.Injective (graft a) := by
  intro φ ψ h
  have hbranches := congrArg LRootedTree.branches h
  simpa using hbranches

@[simp]
theorem graft_eq_graft_iff (a : α) (φ ψ : LRootedForest α) :
    graft a φ = graft a ψ ↔ φ = ψ := by
  constructor
  · intro h
    exact graft_injective a h
  · intro h
    rw [h]

@[simp]
theorem graft_eq_graft_iff_rootLabel_branches
    (a b : α) (φ ψ : LRootedForest α) :
    graft a φ = graft b ψ ↔ a = b ∧ φ = ψ := by
  constructor
  · intro h
    constructor
    · have hroot := congrArg LRootedTree.rootLabel h
      simpa using hroot
    · have hbranches := congrArg LRootedTree.branches h
      simpa using hbranches
  · rintro ⟨rfl, rfl⟩
    rfl

theorem graft_ofPLTree_list (a : α) (ts : List (PLTree α)) :
    graft a ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) =
      LRootedTree.ofPLTree (.node a ts) := by
  change
    LRootedTree.ofPLTree (.node a ((ts.map LRootedTree.ofPLTree).map Quotient.out)) =
      LRootedTree.ofPLTree (.node a ts)
  exact Quotient.sound (PLTree.Perm.node (List.Perm.refl _)
    (forall₂_out_perm_ofPLTree ts))

theorem ofPLTree_node_eq_of_forestPerm (a : α) {ts us : List (PLTree α)}
    (h : PLTree.ForestPerm ts us) :
    LRootedTree.ofPLTree (.node a ts) = LRootedTree.ofPLTree (.node a us) := by
  rw [← graft_ofPLTree_list a ts, ← graft_ofPLTree_list a us, h]

@[simp]
theorem graft_branches_ofPLTree_node (a : α) (ts : List (PLTree α)) :
    graft a (LRootedTree.branches (LRootedTree.ofPLTree (.node a ts))) =
      LRootedTree.ofPLTree (.node a ts) := by
  rw [LRootedTree.branches_ofPLTree_node]
  exact graft_ofPLTree_list a ts

@[simp]
theorem graft_branches (τ : LRootedTree α) :
    graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ) = τ := by
  refine Quotient.inductionOn τ ?_
  intro t
  cases t with
  | node a ts =>
      exact graft_branches_ofPLTree_node a ts

@[simp]
theorem order_graft (a : α) (φ : LRootedForest α) :
    LRootedTree.order (graft a φ) = 1 + order φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change LRootedTree.order (graft a (ts : LRootedForest α)) = 1 + order (ts : LRootedForest α)
  rw [graft_coe]
  simp [order, orderList_out]

@[simp]
theorem mapLabels_graft (f : α → β) (a : α) (φ : LRootedForest α) :
    LRootedTree.map f (graft a φ) = graft (f a) (mapLabels f φ) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change
    LRootedTree.ofPLTree (PLTree.map f (.node a (ts.map Quotient.out))) =
      graft (f a) (mapLabels f ((ts : List (LRootedTree α)) : LRootedForest α))
  rw [PLTree.map_node]
  have hmap :
      mapLabels f ((ts : List (LRootedTree α)) : LRootedForest α) =
        ((ts.map (LRootedTree.map f) : List (LRootedTree β)) : LRootedForest β) := rfl
  rw [hmap, graft_coe]
  clear hmap
  exact Quotient.sound <|
    PLTree.Perm.node (List.Perm.refl _) <| by
      induction ts with
      | nil => exact .nil
      | cons τ ts ih =>
          have hτ :
              PLTree.Perm (PLTree.map f (Quotient.out τ))
                (Quotient.out (LRootedTree.map f τ)) := by
            exact Quotient.exact <|
              calc
                LRootedTree.ofPLTree (PLTree.map f (Quotient.out τ)) =
                    LRootedTree.map f (LRootedTree.ofPLTree (Quotient.out τ)) := rfl
                _ = LRootedTree.map f τ := by
                    rw [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ]
                _ = LRootedTree.ofPLTree (Quotient.out (LRootedTree.map f τ)) := by
                    rw [show LRootedTree.ofPLTree (Quotient.out (LRootedTree.map f τ)) =
                      LRootedTree.map f τ from Quotient.out_eq (LRootedTree.map f τ)]
          exact .cons hτ ih

@[simp]
theorem erase_graft (a : α) (φ : LRootedForest α) :
    LRootedTree.erase (graft a φ) = RootedForest.graft (erase φ) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change
    LRootedTree.erase (LRootedTree.ofPLTree (.node a (ts.map Quotient.out))) =
      RootedForest.graft (erase ((ts : List (LRootedTree α)) : LRootedForest α))
  rw [LRootedTree.erase_ofPLTree]
  simp [erase]
  exact Quotient.sound <|
    PTree.perm_node_of_forall2 <| by
      induction ts with
      | nil => exact .nil
      | cons τ ts ih =>
          have hτ :
              RootedTree.ofPTree (PLTree.erase (Quotient.out τ)) =
                RootedTree.ofPTree (Quotient.out (LRootedTree.erase τ)) := by
            calc
              RootedTree.ofPTree (PLTree.erase (Quotient.out τ)) =
                  LRootedTree.erase (LRootedTree.ofPLTree (Quotient.out τ)) := rfl
              _ = LRootedTree.erase τ := by
                  rw [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ]
              _ = RootedTree.ofPTree (Quotient.out (LRootedTree.erase τ)) := by
                  rw [show RootedTree.ofPTree (Quotient.out (LRootedTree.erase τ)) =
                    LRootedTree.erase τ from Quotient.out_eq (LRootedTree.erase τ)]
          exact .cons (Quotient.exact hτ) ih

@[simp]
theorem treeFactorial_graft (a : α) (φ : LRootedForest α) :
    LRootedTree.treeFactorial (graft a φ) = (1 + order φ) * treeFactorial φ := by
  calc
    LRootedTree.treeFactorial (graft a φ) =
        RootedTree.treeFactorial (LRootedTree.erase (graft a φ)) := by
          rw [LRootedTree.treeFactorial_erase]
    _ = (1 + order φ) * treeFactorial φ := by
          simp [RootedForest.treeFactorial_graft]

theorem treeFactorial_branches (τ : LRootedTree α) :
    LRootedTree.order τ * treeFactorial (LRootedTree.branches τ) =
      LRootedTree.treeFactorial τ := by
  have h := congrArg LRootedTree.treeFactorial (graft_branches τ)
  change
    LRootedTree.treeFactorial
        (graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ)) =
      LRootedTree.treeFactorial τ at h
  rw [treeFactorial_graft] at h
  have horder := congrArg LRootedTree.order (graft_branches τ)
  change
    LRootedTree.order
        (graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ)) =
      LRootedTree.order τ at horder
  rw [order_graft] at horder
  rw [← horder]
  exact h

@[simp]
theorem erase_branches (τ : LRootedTree α) :
    erase (LRootedTree.branches τ) = RootedTree.branches (LRootedTree.erase τ) := by
  have h := erase_graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ)
  rw [graft_branches] at h
  have hbranches := congrArg RootedTree.branches h
  rw [RootedForest.branches_graft] at hbranches
  exact hbranches.symm

@[simp]
theorem mapLabels_branches (f : α → β) (τ : LRootedTree α) :
    mapLabels f (LRootedTree.branches τ) = LRootedTree.branches (LRootedTree.map f τ) := by
  have h := mapLabels_graft f (LRootedTree.rootLabel τ) (LRootedTree.branches τ)
  rw [graft_branches] at h
  have hbranches := congrArg LRootedTree.branches h
  rw [branches_graft] at hbranches
  exact hbranches.symm

@[simp]
theorem order_branches (τ : LRootedTree α) :
    1 + order (LRootedTree.branches τ) = LRootedTree.order τ := by
  have h := congrArg LRootedTree.order (graft_branches τ)
  change
    LRootedTree.order
        (graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ)) =
      LRootedTree.order τ at h
  rw [order_graft] at h
  exact h

theorem order_branches_lt (τ : LRootedTree α) :
    order (LRootedTree.branches τ) < LRootedTree.order τ := by
  rw [← order_branches τ]
  omega

theorem branches_eq_zero_of_order_eq_one (τ : LRootedTree α)
    (h : LRootedTree.order τ = 1) : LRootedTree.branches τ = 0 := by
  have hbranches := order_branches τ
  rw [h] at hbranches
  have hzero : order (LRootedTree.branches τ) = 0 := by omega
  exact (order_eq_zero_iff _).1 hzero

theorem order_eq_one_iff_branches_eq_zero (τ : LRootedTree α) :
    LRootedTree.order τ = 1 ↔ LRootedTree.branches τ = 0 := by
  constructor
  · exact branches_eq_zero_of_order_eq_one τ
  · intro h
    rw [← order_branches τ, h]
    simp

theorem order_eq_one_iff_eq_graft_root_zero (τ : LRootedTree α) :
    LRootedTree.order τ = 1 ↔ τ = graft (LRootedTree.rootLabel τ) 0 := by
  constructor
  · intro h
    calc
      τ = graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ) := (graft_branches τ).symm
      _ = graft (LRootedTree.rootLabel τ) 0 := by
          rw [branches_eq_zero_of_order_eq_one τ h]
  · intro h
    rw [h]
    simp

/-- Graft a labelled rooted forest onto the root of a labelled rooted tree. -/
def butcherProduct (φ : LRootedForest α) (τ : LRootedTree α) : LRootedTree α :=
  graft (LRootedTree.rootLabel τ) (φ + LRootedTree.branches τ)

@[simp]
theorem butcherProduct_zero_left (τ : LRootedTree α) :
    butcherProduct 0 τ = τ := by
  simp [butcherProduct]

@[simp]
theorem butcherProduct_empty_left (τ : LRootedTree α) :
    butcherProduct empty τ = τ := by
  simp [empty, butcherProduct]

@[simp]
theorem butcherProduct_assoc (φ ψ : LRootedForest α) (τ : LRootedTree α) :
    butcherProduct φ (butcherProduct ψ τ) = butcherProduct (φ + ψ) τ := by
  simp [butcherProduct, add_assoc]

@[simp]
theorem rootLabel_butcherProduct (φ : LRootedForest α) (τ : LRootedTree α) :
    LRootedTree.rootLabel (butcherProduct φ τ) = LRootedTree.rootLabel τ := by
  simp [butcherProduct]

@[simp]
theorem branches_butcherProduct (φ : LRootedForest α) (τ : LRootedTree α) :
    LRootedTree.branches (butcherProduct φ τ) = φ + LRootedTree.branches τ := by
  simp [butcherProduct]

theorem butcherProduct_ofPLTree_list (ts : List (PLTree α)) (t : PLTree α) :
    LRootedTree.ofPLTree (PLTree.butcherProduct ts t) =
      butcherProduct ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α)
        (LRootedTree.ofPLTree t) := by
  cases t with
  | node a us =>
      change LRootedTree.ofPLTree (PLTree.node a (ts ++ us)) =
        butcherProduct
          ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α)
          (LRootedTree.ofPLTree (PLTree.node a us))
      rw [← graft_ofPLTree_list a (ts ++ us)]
      simp [butcherProduct, List.map_append]

theorem butcherProduct_eq_iff_rootLabel_branches
    (φ ψ : LRootedForest α) (τ σ : LRootedTree α) :
    butcherProduct φ τ = butcherProduct ψ σ ↔
      LRootedTree.rootLabel τ = LRootedTree.rootLabel σ ∧
        φ + LRootedTree.branches τ = ψ + LRootedTree.branches σ := by
  simp [butcherProduct, graft_eq_graft_iff_rootLabel_branches]

theorem butcherProduct_injective_left (τ : LRootedTree α) :
    Function.Injective (fun φ : LRootedForest α => butcherProduct φ τ) := by
  intro φ ψ h
  have hbranches := (butcherProduct_eq_iff_rootLabel_branches φ ψ τ τ).1 h
  exact add_right_cancel hbranches.2

theorem butcherProduct_injective_right (φ : LRootedForest α) :
    Function.Injective (butcherProduct φ) := by
  intro τ σ h
  have hdata := (butcherProduct_eq_iff_rootLabel_branches φ φ τ σ).1 h
  have hbranches : LRootedTree.branches τ = LRootedTree.branches σ :=
    add_left_cancel hdata.2
  calc
    τ = graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ) :=
      (graft_branches τ).symm
    _ = graft (LRootedTree.rootLabel σ) (LRootedTree.branches σ) := by
        rw [hdata.1, hbranches]
    _ = σ := graft_branches σ

@[simp]
theorem butcherProduct_left_eq_left_iff
    (φ ψ : LRootedForest α) (τ : LRootedTree α) :
    butcherProduct φ τ = butcherProduct ψ τ ↔ φ = ψ := by
  constructor
  · intro h
    exact butcherProduct_injective_left τ h
  · intro h
    rw [h]

@[simp]
theorem butcherProduct_right_eq_right_iff
    (φ : LRootedForest α) (τ σ : LRootedTree α) :
    butcherProduct φ τ = butcherProduct φ σ ↔ τ = σ := by
  constructor
  · intro h
    exact butcherProduct_injective_right φ h
  · intro h
    rw [h]

@[simp]
theorem order_butcherProduct (φ : LRootedForest α) (τ : LRootedTree α) :
    LRootedTree.order (butcherProduct φ τ) = order φ + LRootedTree.order τ := by
  calc
    LRootedTree.order (butcherProduct φ τ) =
        1 + order (φ + LRootedTree.branches τ) := by
          simp [butcherProduct]
    _ = 1 + (order φ + order (LRootedTree.branches τ)) := by
          rw [order_add]
    _ = order φ + (1 + order (LRootedTree.branches τ)) := by
          omega
    _ = order φ + LRootedTree.order τ := by
          rw [order_branches]

@[simp]
theorem erase_butcherProduct (φ : LRootedForest α) (τ : LRootedTree α) :
    LRootedTree.erase (butcherProduct φ τ) =
      RootedForest.butcherProduct (erase φ) (LRootedTree.erase τ) := by
  simp [butcherProduct, RootedForest.butcherProduct]

@[simp]
theorem mapLabels_butcherProduct (f : α → β) (φ : LRootedForest α) (τ : LRootedTree α) :
    LRootedTree.map f (butcherProduct φ τ) =
      butcherProduct (mapLabels f φ) (LRootedTree.map f τ) := by
  simp [butcherProduct]

@[simp]
theorem treeFactorial_butcherProduct (φ : LRootedForest α) (τ : LRootedTree α) :
    LRootedTree.treeFactorial (butcherProduct φ τ) =
      (order φ + LRootedTree.order τ) * treeFactorial (φ + LRootedTree.branches τ) := by
  calc
    LRootedTree.treeFactorial (butcherProduct φ τ) =
        (1 + order (φ + LRootedTree.branches τ)) *
          treeFactorial (φ + LRootedTree.branches τ) := by
          simp [butcherProduct]
    _ = (1 + (order φ + order (LRootedTree.branches τ))) *
          treeFactorial (φ + LRootedTree.branches τ) := by
          rw [order_add]
    _ = (order φ + LRootedTree.order τ) *
          treeFactorial (φ + LRootedTree.branches τ) := by
          rw [← order_branches τ]
          congr 1
          omega

end

end LRootedForest

end HopfAlgebras
