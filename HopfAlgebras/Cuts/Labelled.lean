/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Cuts.Rooted
import HopfAlgebras.Forests.Labelled

/-!
# Admissible Cuts of Labelled Rooted Trees

This file defines finite admissible-cut data for planar labelled rooted trees.
It is the labelled analogue of `HopfAlgebras.Cuts.Rooted`, and provides the combinatorial
input for labelled BCK-type coproducts.

## Main definitions

* `PLTree.RootCut` - a labelled admissible cut which keeps the root component
* `PLTree.Cut` - a labelled admissible cut, allowing the full cut
* `PLTree.cuts` - finite list of labelled admissible cuts
* `PLTree.coproductTerms` - labelled cuts as forest-pair coproduct terms
-/

namespace HopfAlgebras

universe u v

namespace PLTree

variable {α : Type u}

/-- A cut below the root, so the trunk remains a non-empty labelled tree. -/
structure RootCut (α : Type u) where
  pruned : List (PLTree α)
  trunk : PLTree α
deriving Repr

/-- A child-level labelled cut choice. `none` means the edge above the child is cut. -/
structure ChildCut (α : Type u) where
  pruned : List (PLTree α)
  trunk? : Option (PLTree α)
deriving Repr

/-- A root-preserving labelled cut list accumulated across a list of children. -/
structure RootCutList (α : Type u) where
  pruned : List (PLTree α)
  trunks : List (PLTree α)
deriving Repr

/-- An admissible cut of a planar labelled rooted tree. `none` is the full cut. -/
structure Cut (α : Type u) where
  pruned : List (PLTree α)
  trunk? : Option (PLTree α)
deriving Repr

namespace RootCut

/-- Forget labels in a root-preserving labelled cut. -/
def erase (c : RootCut α) : PTree.RootCut :=
  { pruned := c.pruned.map PLTree.erase, trunk := PLTree.erase c.trunk }

/-- Relabel a root-preserving labelled cut. -/
def map {β : Type v} (f : α → β) (c : RootCut α) : RootCut β :=
  { pruned := c.pruned.map (PLTree.map f), trunk := PLTree.map f c.trunk }

/-- Label every vertex in an unlabelled root-preserving cut by the same label. -/
def constLabel (a : α) (c : PTree.RootCut) : RootCut α :=
  { pruned := c.pruned.map (PLTree.constLabel a), trunk := PLTree.constLabel a c.trunk }

@[simp]
theorem erase_constLabel (a : α) (c : PTree.RootCut) :
    erase (constLabel a c) = c := by
  cases c
  simp [erase, constLabel, List.map_map, Function.comp_def]

@[simp]
theorem map_constLabel {β : Type v} (f : α → β) (a : α) (c : PTree.RootCut) :
    map f (constLabel a c) = constLabel (f a) c := by
  cases c
  simp [map, constLabel, List.map_map, Function.comp_def]

/-- The trunk of a root cut, only when the cut prunes no labelled trees. -/
def noPrunedTrunk? (c : RootCut α) : Option (PLTree α) :=
  match c.pruned with
  | [] => some c.trunk
  | _ :: _ => none

end RootCut

namespace ChildCut

/-- Forget labels in a labelled child cut choice. -/
def erase (c : ChildCut α) : PTree.ChildCut :=
  { pruned := c.pruned.map PLTree.erase, trunk? := c.trunk?.map PLTree.erase }

/-- Relabel a labelled child cut choice. -/
def map {β : Type v} (f : α → β) (c : ChildCut α) : ChildCut β :=
  { pruned := c.pruned.map (PLTree.map f), trunk? := c.trunk?.map (PLTree.map f) }

/-- Label every vertex in an unlabelled child cut by the same label. -/
def constLabel (a : α) (c : PTree.ChildCut) : ChildCut α :=
  { pruned := c.pruned.map (PLTree.constLabel a),
    trunk? := c.trunk?.map (PLTree.constLabel a) }

@[simp]
theorem erase_constLabel (a : α) (c : PTree.ChildCut) :
    erase (constLabel a c) = c := by
  cases c
  simp [erase, constLabel, List.map_map, Function.comp_def]

@[simp]
theorem map_constLabel {β : Type v} (f : α → β) (a : α) (c : PTree.ChildCut) :
    map f (constLabel a c) = constLabel (f a) c := by
  cases c
  simp [map, constLabel, List.map_map, Function.comp_def]

/-- The trunk of a child cut choice, only when the choice prunes no labelled trees. -/
def noPrunedTrunk? (c : ChildCut α) : Option (PLTree α) :=
  match c.pruned with
  | [] => c.trunk?
  | _ :: _ => none

/-- The pruned forest of a labelled child cut choice. -/
def prunedForest (c : ChildCut α) : LRootedForest α :=
  (c.pruned.map LRootedTree.ofPLTree : LRootedForest α)

/-- The trunk forest of a labelled child cut choice. Cutting the edge gives the empty trunk. -/
def trunkForest (c : ChildCut α) : LRootedForest α :=
  match c.trunk? with
  | none => 0
  | some trunk => LRootedForest.singleton (LRootedTree.ofPLTree trunk)

/-- The labelled coproduct term encoded by a child cut choice. -/
def coproductTerm (c : ChildCut α) : LRootedForest α × LRootedForest α :=
  (c.prunedForest, c.trunkForest)

end ChildCut

namespace RootCutList

/-- Forget labels in a root-preserving labelled cut list. -/
def erase (c : RootCutList α) : PTree.RootCutList :=
  { pruned := c.pruned.map PLTree.erase, trunks := c.trunks.map PLTree.erase }

/-- Relabel a root-preserving labelled cut list. -/
def map {β : Type v} (f : α → β) (c : RootCutList α) : RootCutList β :=
  { pruned := c.pruned.map (PLTree.map f), trunks := c.trunks.map (PLTree.map f) }

/-- Label every vertex in an unlabelled root-preserving cut list by the same label. -/
def constLabel (a : α) (c : PTree.RootCutList) : RootCutList α :=
  { pruned := c.pruned.map (PLTree.constLabel a),
    trunks := c.trunks.map (PLTree.constLabel a) }

@[simp]
theorem erase_constLabel (a : α) (c : PTree.RootCutList) :
    erase (constLabel a c) = c := by
  cases c
  simp [erase, constLabel, List.map_map, Function.comp_def]

@[simp]
theorem map_constLabel {β : Type v} (f : α → β) (a : α) (c : PTree.RootCutList) :
    map f (constLabel a c) = constLabel (f a) c := by
  cases c
  simp [map, constLabel, List.map_map, Function.comp_def]

/-- The trunks of a root-preserving cut list, only when the cut prunes no labelled trees. -/
def noPrunedTrunks? (c : RootCutList α) : Option (List (PLTree α)) :=
  match c.pruned with
  | [] => some c.trunks
  | _ :: _ => none

/-- The pruned forest of a labelled root-preserving cut list. -/
def prunedForest (c : RootCutList α) : LRootedForest α :=
  (c.pruned.map LRootedTree.ofPLTree : LRootedForest α)

/-- The trunk forest of a labelled root-preserving cut list. -/
def trunkForest (c : RootCutList α) : LRootedForest α :=
  (c.trunks.map LRootedTree.ofPLTree : LRootedForest α)

/-- The labelled coproduct term encoded by a root-preserving cut list. -/
def coproductTerm (c : RootCutList α) : LRootedForest α × LRootedForest α :=
  (c.prunedForest, c.trunkForest)

end RootCutList

namespace Cut

/-- Forget labels in a labelled admissible cut. -/
def erase (c : Cut α) : PTree.Cut :=
  { pruned := c.pruned.map PLTree.erase, trunk? := c.trunk?.map PLTree.erase }

/-- Relabel a labelled admissible cut. -/
def map {β : Type v} (f : α → β) (c : Cut α) : Cut β :=
  { pruned := c.pruned.map (PLTree.map f), trunk? := c.trunk?.map (PLTree.map f) }

/-- Label every vertex in an unlabelled admissible cut by the same label. -/
def constLabel (a : α) (c : PTree.Cut) : Cut α :=
  { pruned := c.pruned.map (PLTree.constLabel a),
    trunk? := c.trunk?.map (PLTree.constLabel a) }

@[simp]
theorem erase_constLabel (a : α) (c : PTree.Cut) :
    erase (constLabel a c) = c := by
  cases c
  simp [erase, constLabel, List.map_map, Function.comp_def]

@[simp]
theorem map_constLabel {β : Type v} (f : α → β) (a : α) (c : PTree.Cut) :
    map f (constLabel a c) = constLabel (f a) c := by
  cases c
  simp [map, constLabel, List.map_map, Function.comp_def]

end Cut

namespace RootCut

def Perm (c d : RootCut α) : Prop :=
  PLTree.ForestPerm c.pruned d.pruned ∧
    LRootedTree.ofPLTree c.trunk = LRootedTree.ofPLTree d.trunk

theorem Perm.refl (c : RootCut α) : Perm c c :=
  ⟨PLTree.ForestPerm.refl c.pruned, rfl⟩

theorem Perm.trans {c d e : RootCut α} (hcd : Perm c d) (hde : Perm d e) :
    Perm c e :=
  ⟨PLTree.ForestPerm.trans hcd.1 hde.1, hcd.2.trans hde.2⟩

end RootCut

def OptionPerm : Option (PLTree α) → Option (PLTree α) → Prop
  | none, none => True
  | some t, some u => LRootedTree.ofPLTree t = LRootedTree.ofPLTree u
  | _, _ => False

theorem OptionPerm.refl : ∀ t : Option (PLTree α), OptionPerm t t
  | none => trivial
  | some _ => rfl

theorem OptionPerm.trans {t u v : Option (PLTree α)}
    (htu : OptionPerm t u) (huv : OptionPerm u v) : OptionPerm t v := by
  cases t <;> cases u <;> cases v <;> simp [OptionPerm] at htu huv ⊢
  exact htu.trans huv

namespace ChildCut

def Perm (c d : ChildCut α) : Prop :=
  PLTree.ForestPerm c.pruned d.pruned ∧ OptionPerm c.trunk? d.trunk?

theorem Perm.refl (c : ChildCut α) : Perm c c :=
  ⟨PLTree.ForestPerm.refl c.pruned, OptionPerm.refl c.trunk?⟩

theorem Perm.trans {c d e : ChildCut α} (hcd : Perm c d) (hde : Perm d e) :
    Perm c e :=
  ⟨PLTree.ForestPerm.trans hcd.1 hde.1, OptionPerm.trans hcd.2 hde.2⟩

theorem Perm.cutEdge {t u : PLTree α} (h : PLTree.Perm t u) :
    Perm { pruned := [t], trunk? := none } { pruned := [u], trunk? := none } :=
  ⟨PLTree.ForestPerm.cons h (PLTree.ForestPerm.refl []), trivial⟩

theorem Perm.of_rootCut {c d : RootCut α} (h : RootCut.Perm c d) :
    Perm { pruned := c.pruned, trunk? := some c.trunk }
      { pruned := d.pruned, trunk? := some d.trunk } :=
  h

end ChildCut

namespace RootCutList

def Perm (c d : RootCutList α) : Prop :=
  PLTree.ForestPerm c.pruned d.pruned ∧ PLTree.ForestPerm c.trunks d.trunks

theorem Perm.refl (c : RootCutList α) : Perm c c :=
  ⟨PLTree.ForestPerm.refl c.pruned, PLTree.ForestPerm.refl c.trunks⟩

theorem Perm.trans {c d e : RootCutList α} (hcd : Perm c d) (hde : Perm d e) :
    Perm c e :=
  ⟨PLTree.ForestPerm.trans hcd.1 hde.1, PLTree.ForestPerm.trans hcd.2 hde.2⟩

def consChild (c : ChildCut α) (r : RootCutList α) : RootCutList α :=
  { pruned := c.pruned ++ r.pruned
    trunks :=
      match c.trunk? with
      | none => r.trunks
      | some trunk => trunk :: r.trunks }

@[simp]
theorem prunedForest_consChild (c : ChildCut α) (r : RootCutList α) :
    (consChild c r).prunedForest = c.prunedForest + r.prunedForest := by
  cases c
  cases r
  simp [prunedForest, ChildCut.prunedForest, consChild, List.map_append]

@[simp]
theorem trunkForest_consChild (c : ChildCut α) (r : RootCutList α) :
    (consChild c r).trunkForest = c.trunkForest + r.trunkForest := by
  cases c with
  | mk pruned trunk? =>
      cases r
      cases trunk? <;> simp [trunkForest, ChildCut.trunkForest, consChild,
        LRootedForest.singleton]

@[simp]
theorem coproductTerm_consChild (c : ChildCut α) (r : RootCutList α) :
    (consChild c r).coproductTerm =
      c.coproductTerm + r.coproductTerm := by
  simp [coproductTerm, ChildCut.coproductTerm]

@[simp]
theorem coproductTerm_mk_consChild (c : ChildCut α) (r : RootCutList α) :
    ({ pruned := c.pruned ++ r.pruned
       trunks :=
        match c.trunk? with
        | none => r.trunks
        | some trunk => trunk :: r.trunks } : RootCutList α).coproductTerm =
      c.coproductTerm + r.coproductTerm := by
  change (consChild c r).coproductTerm = c.coproductTerm + r.coproductTerm
  simp

@[simp]
theorem map_consChild {β : Type v} (f : α → β)
    (c : ChildCut α) (r : RootCutList α) :
    map f (consChild c r) = consChild (ChildCut.map f c) (map f r) := by
  rcases c with ⟨pruned, trunk?⟩
  rcases r with ⟨restPruned, restTrunks⟩
  cases trunk? <;> simp [map, consChild, ChildCut.map, List.map_append]

@[simp]
theorem constLabel_consChild (a : α) (c : PTree.ChildCut) (r : PTree.RootCutList) :
    constLabel a (PTree.RootCutList.consChild c r) =
      consChild (ChildCut.constLabel a c) (constLabel a r) := by
  rcases c with ⟨pruned, trunk?⟩
  rcases r with ⟨restPruned, restTrunks⟩
  cases trunk? <;>
    simp [constLabel, consChild, ChildCut.constLabel, PTree.RootCutList.consChild,
      List.map_append]

theorem Perm.consChild {c d : ChildCut α} {r s : RootCutList α}
    (hc : ChildCut.Perm c d) (hr : Perm r s) :
    Perm (consChild c r) (consChild d s) := by
  rcases c with ⟨cp, ct⟩
  rcases d with ⟨dp, dt⟩
  rcases r with ⟨rp, rt⟩
  rcases s with ⟨sp, st⟩
  rcases hc with ⟨hp, ht⟩
  rcases hr with ⟨hrp, hrt⟩
  cases ct with
  | none =>
      cases dt with
      | none =>
          exact ⟨PLTree.ForestPerm.append hp hrp, hrt⟩
      | some u =>
          simp [OptionPerm] at ht
  | some t =>
      cases dt with
      | none =>
          simp [OptionPerm] at ht
      | some u =>
          exact ⟨PLTree.ForestPerm.append hp hrp, PLTree.ForestPerm.cons_eq ht hrt⟩

theorem Perm.consChild_swap (c d : ChildCut α) (r : RootCutList α) :
    Perm (RootCutList.consChild c (RootCutList.consChild d r))
      (RootCutList.consChild d (RootCutList.consChild c r)) := by
  rcases c with ⟨cp, ct⟩
  rcases d with ⟨dp, dt⟩
  rcases r with ⟨rp, rt⟩
  have hp : PLTree.ForestPerm (cp ++ (dp ++ rp)) (dp ++ (cp ++ rp)) := by
    apply PLTree.ForestPerm.of_list_perm
    simpa [List.append_assoc] using
      List.Perm.append_right rp
        (show (cp ++ dp).Perm (dp ++ cp) from List.perm_append_comm)
  cases ct with
  | none =>
      cases dt with
      | none =>
          exact ⟨hp, PLTree.ForestPerm.refl rt⟩
      | some u =>
          exact ⟨hp, PLTree.ForestPerm.refl (u :: rt)⟩
  | some t =>
      cases dt with
      | none =>
          exact ⟨hp, PLTree.ForestPerm.refl (t :: rt)⟩
      | some u =>
          exact ⟨hp, PLTree.ForestPerm.of_list_perm (List.Perm.swap t u rt).symm⟩

theorem Perm.combine {c d : ChildCut α} {r s : RootCutList α}
    (hc : ChildCut.Perm c d) (hr : Perm r s) :
    Perm
      { pruned := c.pruned ++ r.pruned
        trunks :=
          match c.trunk? with
          | none => r.trunks
          | some trunk => trunk :: r.trunks }
      { pruned := d.pruned ++ s.pruned
        trunks :=
          match d.trunk? with
          | none => s.trunks
          | some trunk => trunk :: s.trunks } := by
  change Perm (RootCutList.consChild c r) (RootCutList.consChild d s)
  exact Perm.consChild hc hr

end RootCutList

theorem rootCut_perm_of_rootCutList_perm (a : α) {c d : RootCutList α}
    (h : RootCutList.Perm c d) :
    RootCut.Perm { pruned := c.pruned, trunk := .node a c.trunks }
      { pruned := d.pruned, trunk := .node a d.trunks } :=
  ⟨h.1, LRootedForest.ofPLTree_node_eq_of_forestPerm a h.2⟩

namespace Cut

def Perm (c d : Cut α) : Prop :=
  PLTree.ForestPerm c.pruned d.pruned ∧ OptionPerm c.trunk? d.trunk?

theorem Perm.refl (c : Cut α) : Perm c c :=
  ⟨PLTree.ForestPerm.refl c.pruned, OptionPerm.refl c.trunk?⟩

theorem Perm.trans {c d e : Cut α} (hcd : Perm c d) (hde : Perm d e) :
    Perm c e :=
  ⟨PLTree.ForestPerm.trans hcd.1 hde.1, OptionPerm.trans hcd.2 hde.2⟩

theorem Perm.full {t u : PLTree α} (h : PLTree.Perm t u) :
    Perm { pruned := [t], trunk? := none } { pruned := [u], trunk? := none } :=
  ⟨PLTree.ForestPerm.cons h (PLTree.ForestPerm.refl []), trivial⟩

theorem Perm.of_rootCut {c d : RootCut α} (h : RootCut.Perm c d) :
    Perm { pruned := c.pruned, trunk? := some c.trunk }
      { pruned := d.pruned, trunk? := some d.trunk } :=
  h

end Cut

private theorem forall₂_ofPLTree_eq_map :
    ∀ ts : List (PLTree α),
      List.Forall₂ (fun t τ => LRootedTree.ofPLTree t = τ) ts (ts.map LRootedTree.ofPLTree)
  | [] => .nil
  | _ :: ts => .cons rfl (forall₂_ofPLTree_eq_map ts)

private theorem forall₂_perm_of_forall₂_ofPLTree_eq :
    ∀ {ts us : List (PLTree α)},
      List.Forall₂ (fun t τ => LRootedTree.ofPLTree t = τ) ts
          (us.map LRootedTree.ofPLTree) →
        List.Forall₂ PLTree.Perm ts us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs =>
      .cons (LRootedTree.ofPLTree_eq_iff.1 h) (forall₂_perm_of_forall₂_ofPLTree_eq hs)

theorem listRelPerm_of_forestPerm {ts us : List (PLTree α)} (h : PLTree.ForestPerm ts us) :
    PTree.ListRelPerm PLTree.Perm ts us := by
  have hp : (ts.map LRootedTree.ofPLTree).Perm (us.map LRootedTree.ofPLTree) :=
    Quotient.exact h
  obtain ⟨ts', hts', hrel⟩ :=
    PTree.forall2_perm_right (R := fun t τ => LRootedTree.ofPLTree t = τ) hp
      (forall₂_ofPLTree_eq_map ts)
  exact ⟨ts', hts', forall₂_perm_of_forall₂_ofPLTree_eq hrel⟩

mutual

/-- Labelled admissible cuts which keep the root component. -/
def rootCuts : PLTree α → List (RootCut α)
  | .node a ts => (rootCutsList ts).map fun c =>
      { pruned := c.pruned, trunk := .node a c.trunks }

/-- Choices for a labelled child: cut the edge above it, or keep it with a root-preserving cut. -/
def childCuts (t : PLTree α) : List (ChildCut α) :=
  { pruned := [t], trunk? := none } ::
    (rootCuts t).map fun c => { pruned := c.pruned, trunk? := some c.trunk }

/-- Combine labelled child cut choices into root-preserving cuts. -/
def rootCutsList : List (PLTree α) → List (RootCutList α)
  | [] => [{ pruned := [], trunks := [] }]
  | t :: ts =>
      (childCuts t).flatMap fun c =>
        (rootCutsList ts).map fun rest =>
          { pruned := c.pruned ++ rest.pruned
            trunks :=
              match c.trunk? with
              | none => rest.trunks
              | some trunk => trunk :: rest.trunks }

end

mutual

/-- Labelled root-preserving cuts erase to the corresponding unlabelled cuts. -/
theorem rootCuts_erase :
    ∀ t : PLTree α, (rootCuts t).map RootCut.erase = PTree.rootCuts (PLTree.erase t)
  | .node a ts => by
      rw [rootCuts, PTree.rootCuts.eq_def]
      simp only [PLTree.erase]
      rw [← rootCutsList_erase ts]
      simp [RootCut.erase, RootCutList.erase, List.map_map]

/-- Labelled child cut choices erase to the corresponding unlabelled choices. -/
theorem childCuts_erase (t : PLTree α) :
    (childCuts t).map ChildCut.erase = PTree.childCuts (PLTree.erase t) := by
  rw [childCuts, PTree.childCuts]
  rw [← rootCuts_erase t]
  simp [ChildCut.erase, RootCut.erase, List.map_map]

/-- Labelled root-preserving cut lists erase to the corresponding unlabelled cut lists. -/
theorem rootCutsList_erase :
    ∀ ts : List (PLTree α),
      (rootCutsList ts).map RootCutList.erase = PTree.rootCutsList (ts.map PLTree.erase)
  | [] => by
      simp [rootCutsList, RootCutList.erase]
  | t :: ts => by
      rw [rootCutsList, PTree.rootCutsList.eq_def]
      simp only [List.map_cons]
      rw [← childCuts_erase t, ← rootCutsList_erase ts]
      rw [List.map_flatMap, List.flatMap_map]
      apply List.flatMap_congr
      intro c _hc
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro rest _hrest
      cases c with
      | mk pruned trunk? =>
          cases trunk? <;>
            simp [ChildCut.erase, RootCutList.erase, PTree.RootCutList.consChild,
              List.map_append]

end

mutual

/-- Root-preserving cuts commute with relabelling. -/
theorem rootCuts_map {β : Type v} (f : α → β) :
    ∀ t : PLTree α, rootCuts (PLTree.map f t) = (rootCuts t).map (RootCut.map f)
  | .node a ts => by
      rw [PLTree.map_node, rootCuts, rootCuts, rootCutsList_map f ts]
      simp [RootCut.map, RootCutList.map, List.map_map]

/-- Child cut choices commute with relabelling. -/
theorem childCuts_map {β : Type v} (f : α → β) (t : PLTree α) :
    childCuts (PLTree.map f t) = (childCuts t).map (ChildCut.map f) := by
  rw [childCuts, childCuts, rootCuts_map f t]
  simp [ChildCut.map, RootCut.map, List.map_map]

/-- Root-preserving cut lists commute with relabelling. -/
theorem rootCutsList_map {β : Type v} (f : α → β) :
    ∀ ts : List (PLTree α),
      rootCutsList (ts.map (PLTree.map f)) =
        (rootCutsList ts).map (RootCutList.map f)
  | [] => by
      simp [rootCutsList, RootCutList.map]
  | t :: ts => by
      rw [List.map_cons, rootCutsList, rootCutsList, childCuts_map f t,
        rootCutsList_map f ts]
      rw [List.map_flatMap, List.flatMap_map]
      apply List.flatMap_congr
      intro c _hc
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro rest _hrest
      exact (RootCutList.map_consChild f c rest).symm

end

mutual

/-- Root-preserving cuts of a constantly labelled tree are constantly labelled cuts. -/
theorem rootCuts_constLabel (a : α) :
    ∀ t : PTree, rootCuts (PLTree.constLabel a t) =
      (PTree.rootCuts t).map (RootCut.constLabel a)
  | .node ts => by
      rw [PLTree.constLabel_node, rootCuts, PTree.rootCuts.eq_def,
        rootCutsList_constLabel a ts]
      simp [RootCut.constLabel, RootCutList.constLabel, List.map_map]

/-- Child cuts of a constantly labelled tree are constantly labelled cuts. -/
theorem childCuts_constLabel (a : α) (t : PTree) :
    childCuts (PLTree.constLabel a t) =
      (PTree.childCuts t).map (ChildCut.constLabel a) := by
  rw [childCuts, PTree.childCuts, rootCuts_constLabel a t]
  simp [ChildCut.constLabel, RootCut.constLabel, List.map_map]

/-- Root-preserving cut lists of constantly labelled trees are constantly labelled cut lists. -/
theorem rootCutsList_constLabel (a : α) :
    ∀ ts : List PTree,
      rootCutsList (ts.map (PLTree.constLabel a)) =
        (PTree.rootCutsList ts).map (RootCutList.constLabel a)
  | [] => by
      simp [rootCutsList, RootCutList.constLabel]
  | t :: ts => by
      rw [List.map_cons, rootCutsList, PTree.rootCutsList.eq_def,
        childCuts_constLabel a t, rootCutsList_constLabel a ts]
      rw [List.map_flatMap, List.flatMap_map]
      apply List.flatMap_congr
      intro c _hc
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro rest _hrest
      exact (RootCutList.constLabel_consChild a c rest).symm

end

private theorem flatMap₂_perm {α β γ : Type _} (xs : List α) (ys : List β)
    (f : α → β → List γ) :
    (xs.flatMap fun x => ys.flatMap fun y => f x y).Perm
      (ys.flatMap fun y => xs.flatMap fun x => f x y) := by
  induction xs with
  | nil =>
      induction ys with
      | nil => rfl
      | cons y ys ih => simp [List.flatMap_cons]
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      exact (List.Perm.append_left (ys.flatMap fun y => f x y) ih).trans
        (List.flatMap_append_perm ys (fun y => f x y)
          (fun y => xs.flatMap fun x' => f x' y))

private theorem flatMap_map_swap {α β γ : Type _} (f : α → β → γ) (g : β → α → γ)
    (hfg : ∀ x y, f x y = g y x) :
    ∀ (xs : List α) (ys : List β),
      (xs.flatMap fun x => ys.map (f x)).Perm
        (ys.flatMap fun y => xs.map (g y))
  | xs, ys => by
      have hswap :
          (xs.flatMap fun x => ys.map (f x)).Perm
            (ys.flatMap fun y => xs.map fun x => f x y) := by
        simpa only [← List.map_eq_flatMap] using flatMap₂_perm xs ys (fun x y => [f x y])
      refine hswap.trans ?_
      exact List.Perm.flatMap (List.Perm.refl ys) fun y _ => by
        have hrow : xs.map (fun x => f x y) = xs.map (g y) := by
          exact List.map_congr_left fun x _ => hfg x y
        rw [hrow]

theorem rootCuts_node_listRelPerm_of_rootCutsList
    {a : α} {ts us : List (PLTree α)}
    (h : PTree.ListRelPerm RootCutList.Perm (rootCutsList ts) (rootCutsList us)) :
    PTree.ListRelPerm RootCut.Perm (rootCuts (.node a ts)) (rootCuts (.node a us)) := by
  simpa [rootCuts] using
    PTree.ListRelPerm.map (fun h => rootCut_perm_of_rootCutList_perm a h) h

theorem childCuts_listRelPerm_of_perm {t u : PLTree α} (htu : PLTree.Perm t u)
    (hroot : PTree.ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) :
    PTree.ListRelPerm ChildCut.Perm (childCuts t) (childCuts u) := by
  rw [childCuts, childCuts]
  exact PTree.ListRelPerm.cons (ChildCut.Perm.cutEdge htu)
    (PTree.ListRelPerm.map (fun h => ChildCut.Perm.of_rootCut h) hroot)

theorem rootCutsList_cons_listRelPerm {t u : PLTree α}
    {ts us : List (PLTree α)}
    (hchild : PTree.ListRelPerm ChildCut.Perm (childCuts t) (childCuts u))
    (htail : PTree.ListRelPerm RootCutList.Perm (rootCutsList ts) (rootCutsList us)) :
    PTree.ListRelPerm RootCutList.Perm (rootCutsList (t :: ts)) (rootCutsList (u :: us)) := by
  rw [rootCutsList, rootCutsList]
  change PTree.ListRelPerm RootCutList.Perm
    ((childCuts t).flatMap fun c =>
      (rootCutsList ts).map fun rest => RootCutList.consChild c rest)
    ((childCuts u).flatMap fun c =>
      (rootCutsList us).map fun rest => RootCutList.consChild c rest)
  exact PTree.ListRelPerm.flatMap
    (fun hcut =>
      PTree.ListRelPerm.map (fun hrest => RootCutList.Perm.consChild hcut hrest) htail)
    hchild

theorem rootCutsList_cons_cons_listRelPerm_swap
    (t u : PLTree α) (ts : List (PLTree α)) :
    PTree.ListRelPerm RootCutList.Perm (rootCutsList (t :: u :: ts))
      (rootCutsList (u :: t :: ts)) := by
  rw [rootCutsList, rootCutsList, rootCutsList, rootCutsList]
  simp only [List.map_flatMap, List.map_map]
  change PTree.ListRelPerm RootCutList.Perm
    ((childCuts t).flatMap fun c =>
      (childCuts u).flatMap fun d =>
        (rootCutsList ts).map fun r =>
          RootCutList.consChild c (RootCutList.consChild d r))
    ((childCuts u).flatMap fun d =>
      (childCuts t).flatMap fun c =>
        (rootCutsList ts).map fun r =>
          RootCutList.consChild d (RootCutList.consChild c r))
  refine PTree.ListRelPerm.perm_left
    (flatMap₂_perm (childCuts t) (childCuts u)
      (fun c d =>
        (rootCutsList ts).map fun r =>
          RootCutList.consChild c (RootCutList.consChild d r))) ?_
  exact PTree.ListRelPerm.flatMap
    (fun {d d'} hd =>
      PTree.ListRelPerm.flatMap
        (fun {c c'} hc =>
          PTree.ListRelPerm.map
            (fun {r s} hr =>
              RootCutList.Perm.trans (RootCutList.Perm.consChild_swap c d r)
                (RootCutList.Perm.consChild hd (RootCutList.Perm.consChild hc hr)))
            (PTree.ListRelPerm.refl RootCutList.Perm.refl (rootCutsList ts)))
        (PTree.ListRelPerm.refl ChildCut.Perm.refl (childCuts t)))
    (PTree.ListRelPerm.refl ChildCut.Perm.refl (childCuts u))

theorem rootCutsList_listRelPerm_of_perm {ts us : List (PLTree α)} (h : ts.Perm us) :
    PTree.ListRelPerm RootCutList.Perm (rootCutsList ts) (rootCutsList us) := by
  induction h with
  | nil =>
      exact PTree.ListRelPerm.refl RootCutList.Perm.refl (rootCutsList [])
  | cons t _ ih =>
      exact rootCutsList_cons_listRelPerm
        (PTree.ListRelPerm.refl ChildCut.Perm.refl (childCuts t)) ih
  | swap t u ts =>
      exact rootCutsList_cons_cons_listRelPerm_swap u t ts
  | trans _ _ ih₁ ih₂ =>
      exact PTree.ListRelPerm.trans (R := RootCutList.Perm)
        (fun {x y z} => RootCutList.Perm.trans) ih₁ ih₂

theorem rootCutsList_listRelPerm_of_forall₂_childCuts :
    ∀ {ts us : List (PLTree α)},
      List.Forall₂
          (fun t u => PTree.ListRelPerm ChildCut.Perm (childCuts t) (childCuts u)) ts us →
        PTree.ListRelPerm RootCutList.Perm (rootCutsList ts) (rootCutsList us)
  | [], [], .nil => by
      rw [rootCutsList.eq_def]
      exact PTree.ListRelPerm.of_forall₂ (.cons (RootCutList.Perm.refl _) .nil)
  | _ :: _, _ :: _, .cons hchild htail =>
      rootCutsList_cons_listRelPerm hchild
        (rootCutsList_listRelPerm_of_forall₂_childCuts htail)

theorem rootCutsList_listRelPerm_of_forall₂_perm_rootCuts :
    ∀ {ts us : List (PLTree α)},
      List.Forall₂
          (fun t u =>
            PLTree.Perm t u ∧ PTree.ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u))
          ts us →
        PTree.ListRelPerm RootCutList.Perm (rootCutsList ts) (rootCutsList us)
  | [], [], .nil => by
      rw [rootCutsList.eq_def]
      exact PTree.ListRelPerm.of_forall₂ (.cons (RootCutList.Perm.refl _) .nil)
  | _ :: _, _ :: _, .cons h htail =>
      rootCutsList_cons_listRelPerm (childCuts_listRelPerm_of_perm h.1 h.2)
        (rootCutsList_listRelPerm_of_forall₂_perm_rootCuts htail)

theorem rootCuts_node_listRelPerm_of_forall₂_perm_rootCuts
    {a : α} {ts us : List (PLTree α)}
    (h :
      List.Forall₂
        (fun t u =>
          PLTree.Perm t u ∧ PTree.ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u))
        ts us) :
    PTree.ListRelPerm RootCut.Perm (rootCuts (.node a ts)) (rootCuts (.node a us)) :=
  rootCuts_node_listRelPerm_of_rootCutsList
    (rootCutsList_listRelPerm_of_forall₂_perm_rootCuts h)

mutual

theorem rootCuts_listRelPerm_of_perm :
    ∀ {t u : PLTree α}, PLTree.Perm t u →
      PTree.ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)
  | .node a ts, .node _ us, PLTree.Perm.node (ts' := ts') hp hf => by
      have hleft :
          PTree.ListRelPerm RootCut.Perm (rootCuts (.node a ts)) (rootCuts (.node a ts')) :=
        rootCuts_node_listRelPerm_of_rootCutsList (rootCutsList_listRelPerm_of_perm hp)
      have hright :
          PTree.ListRelPerm RootCut.Perm (rootCuts (.node a ts')) (rootCuts (.node a us)) :=
        rootCuts_node_listRelPerm_of_forall₂_perm_rootCuts
          (forall₂_perm_rootCuts_of_forall₂_perm hf)
      exact PTree.ListRelPerm.trans (R := RootCut.Perm)
        (fun {x y z} => RootCut.Perm.trans) hleft hright

theorem forall₂_perm_rootCuts_of_forall₂_perm :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ PLTree.Perm ts us →
      List.Forall₂
        (fun t u =>
          PLTree.Perm t u ∧ PTree.ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u))
        ts us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h htail =>
      .cons ⟨h, rootCuts_listRelPerm_of_perm h⟩
        (forall₂_perm_rootCuts_of_forall₂_perm htail)

end

private theorem filterMap_rootCutList_noPrunedTrunks_map {β : Type u}
    (f : List (PLTree α) → β) :
    ∀ cuts : List (RootCutList α),
      cuts.filterMap
          (fun c =>
            match c.pruned with
            | [] => some (f c.trunks)
            | _ :: _ => none) =
        (cuts.filterMap RootCutList.noPrunedTrunks?).map f
  | [] => rfl
  | c :: cuts => by
      cases c with
      | mk pruned trunks =>
          cases pruned <;> simp [List.filterMap_cons, RootCutList.noPrunedTrunks?,
            filterMap_rootCutList_noPrunedTrunks_map f cuts]

private theorem flatMap_rootCut_noPrunedTrunk_singleton {β : Type u}
    (f : PLTree α → β) :
    ∀ cuts : List (RootCut α),
      cuts.flatMap
          (fun c =>
            match c.noPrunedTrunk? with
            | none => []
            | some trunk => [f trunk]) =
        (cuts.filterMap RootCut.noPrunedTrunk?).map f
  | [] => rfl
  | c :: cuts => by
      cases h : RootCut.noPrunedTrunk? c <;>
        simp [h, flatMap_rootCut_noPrunedTrunk_singleton f cuts]

mutual

/-- Exactly one root-preserving labelled cut of a tree prunes no trees: the no-cut cut. -/
theorem rootCuts_noPrunedTrunks :
    ∀ t : PLTree α, (rootCuts t).filterMap RootCut.noPrunedTrunk? = [t]
  | .node a ts => by
      rw [rootCuts]
      simp only [List.filterMap_map]
      have h := filterMap_rootCutList_noPrunedTrunks_map (fun trunks => PLTree.node a trunks)
        (rootCutsList ts)
      rw [rootCutsList_noPrunedTrunks] at h
      simpa [Function.comp_def, RootCut.noPrunedTrunk?, RootCutList.noPrunedTrunks?] using h

/-- Exactly one labelled child cut choice prunes no trees: the choice keeping the whole child. -/
theorem childCuts_noPrunedTrunks (t : PLTree α) :
    (childCuts t).filterMap ChildCut.noPrunedTrunk? = [t] := by
  rw [childCuts]
  simp only [List.filterMap_cons, ChildCut.noPrunedTrunk?, List.filterMap_map]
  change (rootCuts t).filterMap RootCut.noPrunedTrunk? = [t]
  exact rootCuts_noPrunedTrunks t

/-- Exactly one root-preserving labelled cut list prunes no trees: the no-cut list. -/
theorem rootCutsList_noPrunedTrunks :
    ∀ ts : List (PLTree α), (rootCutsList ts).filterMap RootCutList.noPrunedTrunks? = [ts]
  | [] => by
      simp [rootCutsList, RootCutList.noPrunedTrunks?]
  | t :: ts => by
      rw [rootCutsList]
      rw [childCuts]
      simp only [List.flatMap_cons, List.flatMap_map]
      have hinner :
          ∀ c : RootCut α,
            (List.map
                (fun rest : RootCutList α =>
                  { pruned := c.pruned ++ rest.pruned,
                    trunks :=
                      c.trunk :: rest.trunks })
                (rootCutsList ts)).filterMap RootCutList.noPrunedTrunks? =
              match RootCut.noPrunedTrunk? c with
              | none => []
              | some trunk => [trunk :: ts] := by
        intro c
        cases hcpruned : c.pruned with
        | nil =>
            have h :=
              filterMap_rootCutList_noPrunedTrunks_map (fun trunks => c.trunk :: trunks)
                (rootCutsList ts)
            rw [rootCutsList_noPrunedTrunks] at h
            simpa [Function.comp_def, RootCutList.noPrunedTrunks?, RootCut.noPrunedTrunk?, hcpruned] using h
        | cons p ps =>
            simp [RootCutList.noPrunedTrunks?, RootCut.noPrunedTrunk?, hcpruned]
      rw [List.filterMap_append, List.filterMap_flatMap]
      change
        (List.map
            (fun rest : RootCutList α =>
              { pruned := [t] ++ rest.pruned,
                trunks := rest.trunks })
            (rootCutsList ts)).filterMap RootCutList.noPrunedTrunks? ++
          List.flatMap
            (fun c : RootCut α =>
              (List.map
                (fun rest : RootCutList α =>
                  { pruned := c.pruned ++ rest.pruned,
                    trunks := c.trunk :: rest.trunks })
                (rootCutsList ts)).filterMap RootCutList.noPrunedTrunks?)
            (rootCuts t) = [t :: ts]
      rw [show
          (List.map
              (fun rest : RootCutList α =>
                { pruned := [t] ++ rest.pruned,
                  trunks := rest.trunks })
              (rootCutsList ts)).filterMap RootCutList.noPrunedTrunks? = [] by
            simp [RootCutList.noPrunedTrunks?]]
      simp [hinner]
      rw [flatMap_rootCut_noPrunedTrunk_singleton (fun trunk => trunk :: ts),
        rootCuts_noPrunedTrunks]
      rfl

end

mutual

/-- Root-preserving labelled cuts conserve the order of a tree. -/
theorem rootCuts_order :
    ∀ {t : PLTree α} {c : RootCut α}, c ∈ rootCuts t →
      orderList c.pruned + order c.trunk = order t
  | .node a ts, c, hc => by
      simp [rootCuts] at hc
      obtain ⟨cl, hcl, rfl⟩ := hc
      have hcl_order := rootCutsList_order hcl
      simp
      omega

/-- Labelled child cut choices conserve the order of the child tree. -/
theorem childCuts_order :
    ∀ {t : PLTree α} {c : ChildCut α}, c ∈ childCuts t →
      orderList c.pruned +
        (match c.trunk? with
        | none => 0
        | some trunk => order trunk) = order t
  | t, c, hc => by
      simp [childCuts] at hc
      rcases hc with hc | hc
      · subst c
        simp
      · obtain ⟨rc, hrc, rfl⟩ := hc
        simpa using rootCuts_order hrc

/-- Combined labelled child cuts conserve the total order of a list of children. -/
theorem rootCutsList_order :
    ∀ {ts : List (PLTree α)} {c : RootCutList α}, c ∈ rootCutsList ts →
      orderList c.pruned + orderList c.trunks = orderList ts
  | [], c, hc => by
      simp [rootCutsList] at hc
      subst c
      simp
  | t :: ts, c, hc => by
      rw [rootCutsList] at hc
      simp only [List.mem_flatMap, List.mem_map] at hc
      obtain ⟨cc, hcc, rest, hrest, hcr⟩ := hc
      subst c
      have hcc_order := childCuts_order hcc
      have hrest_order := rootCutsList_order hrest
      cases hcct : cc.trunk? with
      | none =>
          simp [hcct] at hcc_order
          simp
          omega
      | some trunk =>
          simp [hcct] at hcc_order
          simp
          omega

end

mutual

/-- A labelled root-preserving cut with no pruned trees is the no-cut root cut. -/
theorem rootCuts_pruned_eq_nil :
    ∀ {t : PLTree α} {c : RootCut α}, c ∈ rootCuts t → c.pruned = [] → c.trunk = t
  | .node a ts, c, hc, hpruned => by
      simp [rootCuts] at hc
      obtain ⟨cl, hcl, rfl⟩ := hc
      have htrunks := rootCutsList_pruned_eq_nil hcl hpruned
      simp [htrunks]

/-- A labelled child cut choice with no pruned trees keeps the whole child tree. -/
theorem childCuts_pruned_eq_nil :
    ∀ {t : PLTree α} {c : ChildCut α}, c ∈ childCuts t → c.pruned = [] →
      c.trunk? = some t
  | t, c, hc, hpruned => by
      simp [childCuts] at hc
      rcases hc with hc | hc
      · subst c
        simp at hpruned
      · obtain ⟨rc, hrc, rfl⟩ := hc
        exact congrArg some (rootCuts_pruned_eq_nil hrc hpruned)

/-- A labelled root-preserving cut list with no pruned trees keeps every child tree. -/
theorem rootCutsList_pruned_eq_nil :
    ∀ {ts : List (PLTree α)} {c : RootCutList α}, c ∈ rootCutsList ts →
      c.pruned = [] → c.trunks = ts
  | [], c, hc, _ => by
      simp [rootCutsList] at hc
      subst c
      rfl
  | t :: ts, c, hc, hpruned => by
      rw [rootCutsList] at hc
      simp only [List.mem_flatMap, List.mem_map] at hc
      obtain ⟨cc, hcc, rest, hrest, hcr⟩ := hc
      subst c
      have hparts : cc.pruned = [] ∧ rest.pruned = [] := by
        cases hccp : cc.pruned with
        | nil =>
            cases hrp : rest.pruned with
            | nil => simp
            | cons p ps =>
                simp [hccp, hrp] at hpruned
        | cons p ps =>
            simp [hccp] at hpruned
      have hcc_trunk := childCuts_pruned_eq_nil hcc hparts.1
      have hrest_trunks := rootCutsList_pruned_eq_nil hrest hparts.2
      simp [hcc_trunk, hrest_trunks]

end

/-- All labelled admissible cuts, including the full cut. -/
def cuts (t : PLTree α) : List (Cut α) :=
  (rootCuts t).map (fun c => { pruned := c.pruned, trunk? := some c.trunk }) ++
    [{ pruned := [t], trunk? := none }]

theorem cuts_listRelPerm_of_rootCuts {t u : PLTree α} (htu : PLTree.Perm t u)
    (hroot : PTree.ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) :
    PTree.ListRelPerm Cut.Perm (cuts t) (cuts u) := by
  rw [cuts, cuts]
  exact PTree.ListRelPerm.append
    (PTree.ListRelPerm.map (fun h => Cut.Perm.of_rootCut h) hroot)
    (PTree.ListRelPerm.of_forall₂ (.cons (Cut.Perm.full htu) .nil))

theorem cuts_listRelPerm_of_perm {t u : PLTree α} (h : PLTree.Perm t u) :
    PTree.ListRelPerm Cut.Perm (cuts t) (cuts u) :=
  cuts_listRelPerm_of_rootCuts h (rootCuts_listRelPerm_of_perm h)

/-- Labelled admissible cuts erase to the corresponding unlabelled cuts. -/
theorem cuts_erase (t : PLTree α) :
    (cuts t).map Cut.erase = PTree.cuts (PLTree.erase t) := by
  rw [cuts, PTree.cuts]
  rw [← rootCuts_erase t]
  simp [Cut.erase, RootCut.erase, List.map_map]

theorem cuts_map {β : Type v} (f : α → β) (t : PLTree α) :
    cuts (PLTree.map f t) = (cuts t).map (Cut.map f) := by
  rw [cuts, cuts, rootCuts_map f t]
  simp [Cut.map, RootCut.map, List.map_map]

theorem cuts_constLabel (a : α) (t : PTree) :
    cuts (PLTree.constLabel a t) = (PTree.cuts t).map (Cut.constLabel a) := by
  rw [cuts, PTree.cuts, rootCuts_constLabel a t]
  simp [Cut.constLabel, RootCut.constLabel, List.map_map]

private theorem order_ofPLTree_list :
    ∀ ts : List (PLTree α),
      LRootedForest.order
          ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) =
        orderList ts
  | [] => by
      simp [LRootedForest.order]
  | t :: ts => by
      change
        LRootedTree.order (LRootedTree.ofPLTree t) +
            LRootedForest.order
              ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) =
          order t + orderList ts
      rw [LRootedTree.order_ofPLTree, order_ofPLTree_list ts]

namespace Cut

/-- The pruned branches of a labelled cut, as a non-planar labelled rooted forest. -/
def prunedForest (c : Cut α) : LRootedForest α :=
  (c.pruned.map LRootedTree.ofPLTree : LRootedForest α)

/-- The trunk of a labelled cut. The full cut has empty trunk forest. -/
def trunkForest (c : Cut α) : LRootedForest α :=
  match c.trunk? with
  | none => 0
  | some t => LRootedForest.singleton (LRootedTree.ofPLTree t)

@[simp]
theorem map_prunedForest {β : Type v} (f : α → β) (c : Cut α) :
    LRootedForest.mapLabels f c.prunedForest = (Cut.map f c).prunedForest := by
  cases c with
  | mk pruned trunk? =>
      simp [prunedForest, Cut.map, LRootedForest.mapLabels, List.map_map, Function.comp_def]

@[simp]
theorem map_trunkForest {β : Type v} (f : α → β) (c : Cut α) :
    LRootedForest.mapLabels f c.trunkForest = (Cut.map f c).trunkForest := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? <;> simp [trunkForest, Cut.map, LRootedForest.mapLabels,
        LRootedForest.singleton]

theorem Perm.prunedForest_eq {c d : Cut α} (h : Perm c d) :
    c.prunedForest = d.prunedForest :=
  h.1

theorem Perm.trunkForest_eq {c d : Cut α} (h : Perm c d) :
    c.trunkForest = d.trunkForest := by
  rcases c with ⟨cp, ct⟩
  rcases d with ⟨dp, dt⟩
  rcases h with ⟨_, ht⟩
  cases ct with
  | none =>
      cases dt with
      | none => rfl
      | some u => simp [OptionPerm] at ht
  | some t =>
      cases dt with
      | none => simp [OptionPerm] at ht
      | some u =>
          simp [OptionPerm] at ht
          simpa [trunkForest] using congrArg LRootedForest.singleton ht

theorem Perm.coproductTerm_eq {c d : Cut α} (h : Perm c d) :
    (c.prunedForest, c.trunkForest) = (d.prunedForest, d.trunkForest) := by
  simp [h.prunedForest_eq, h.trunkForest_eq]

@[simp]
theorem constLabel_prunedForest (a : α) (c : PTree.Cut) :
    (Cut.constLabel a c).prunedForest =
      LRootedForest.constLabel a (PTree.Cut.prunedForest c) := by
  cases c with
  | mk pruned trunk? =>
      simp [prunedForest, PTree.Cut.prunedForest, Cut.constLabel,
        LRootedForest.constLabel, List.map_map, Function.comp_def]

@[simp]
theorem constLabel_trunkForest (a : α) (c : PTree.Cut) :
    (Cut.constLabel a c).trunkForest =
      LRootedForest.constLabel a (PTree.Cut.trunkForest c) := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? <;>
        simp [trunkForest, PTree.Cut.trunkForest, Cut.constLabel,
          LRootedForest.constLabel, LRootedForest.singleton, RootedForest.singleton]

@[simp]
theorem erase_prunedForest (c : Cut α) :
    LRootedForest.erase c.prunedForest = PTree.Cut.prunedForest (Cut.erase c) := by
  cases c with
  | mk pruned trunk? =>
      simp [prunedForest, PTree.Cut.prunedForest, Cut.erase, LRootedForest.erase,
        List.map_map, Function.comp_def]

@[simp]
theorem erase_trunkForest (c : Cut α) :
    LRootedForest.erase c.trunkForest = PTree.Cut.trunkForest (Cut.erase c) := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? with
      | none =>
          simp [trunkForest, PTree.Cut.trunkForest, Cut.erase, LRootedForest.erase]
      | some t =>
          simp [trunkForest, PTree.Cut.trunkForest, Cut.erase]

@[simp]
theorem order_trunkForest (c : Cut α) :
    LRootedForest.order c.trunkForest =
      match c.trunk? with
      | none => 0
      | some trunk => order trunk := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? <;> simp [trunkForest]

end Cut

/-- Every labelled admissible cut conserves total order between pruned forest and trunk. -/
theorem cuts_order {t : PLTree α} {c : Cut α} (hc : c ∈ cuts t) :
    LRootedForest.order c.prunedForest + LRootedForest.order c.trunkForest = order t := by
  simp [cuts] at hc
  rcases hc with hc | hc
  · obtain ⟨rc, hrc, rfl⟩ := hc
    simpa [Cut.prunedForest, Cut.trunkForest, order_ofPLTree_list] using rootCuts_order hrc
  · subst c
    simp [Cut.prunedForest, Cut.trunkForest, LRootedForest.order]

/-- The terms `P^c(t) ⊗ R^c(t)` appearing in the labelled BCK coproduct. -/
def coproductTerms (t : PLTree α) : List (LRootedForest α × LRootedForest α) :=
  (cuts t).map fun c => (c.prunedForest, c.trunkForest)

/-- Keep exactly the labelled coproduct terms whose left tensor factor is empty. -/
def leftBoundaryCoproductTerm? (term : LRootedForest α × LRootedForest α) :
    Option (LRootedForest α × LRootedForest α) :=
  if LRootedForest.order term.1 = 0 then some term else none

/-- Keep exactly the labelled coproduct terms whose right tensor factor is empty. -/
def rightBoundaryCoproductTerm? (term : LRootedForest α × LRootedForest α) :
    Option (LRootedForest α × LRootedForest α) :=
  if LRootedForest.order term.2 = 0 then some term else none

/-- Forget labels in a labelled coproduct basis term. -/
def eraseCoproductTerm (term : LRootedForest α × LRootedForest α) :
    RootedForest × RootedForest :=
  (LRootedForest.erase term.1, LRootedForest.erase term.2)

/-- Relabel a labelled coproduct basis term. -/
def mapCoproductTerm {β : Type v} (f : α → β)
    (term : LRootedForest α × LRootedForest α) :
    LRootedForest β × LRootedForest β :=
  (LRootedForest.mapLabels f term.1, LRootedForest.mapLabels f term.2)

/-- Label every vertex in an unlabelled coproduct basis term by the same label. -/
def constLabelCoproductTerm (a : α) (term : RootedForest × RootedForest) :
    LRootedForest α × LRootedForest α :=
  (LRootedForest.constLabel a term.1, LRootedForest.constLabel a term.2)

@[simp]
theorem eraseCoproductTerm_constLabel (a : α) (term : RootedForest × RootedForest) :
    eraseCoproductTerm (constLabelCoproductTerm a term) = term := by
  cases term
  simp [eraseCoproductTerm, constLabelCoproductTerm]

@[simp]
theorem mapCoproductTerm_constLabel {β : Type v} (f : α → β) (a : α)
    (term : RootedForest × RootedForest) :
    mapCoproductTerm f (constLabelCoproductTerm a term) =
      constLabelCoproductTerm (f a) term := by
  cases term
  simp [mapCoproductTerm, constLabelCoproductTerm]

@[simp]
theorem mapCoproductTerm_add {β : Type v} (f : α → β)
    (x y : LRootedForest α × LRootedForest α) :
    mapCoproductTerm f (x + y) = mapCoproductTerm f x + mapCoproductTerm f y := by
  cases x
  cases y
  simp [mapCoproductTerm, LRootedForest.mapLabels_add]

@[simp]
theorem constLabelCoproductTerm_add (a : α) (x y : RootedForest × RootedForest) :
    constLabelCoproductTerm a (x + y) =
      constLabelCoproductTerm a x + constLabelCoproductTerm a y := by
  cases x
  cases y
  simp [constLabelCoproductTerm, LRootedForest.constLabel_add]

/-- Forget labels in a labelled triple coproduct term. -/
def eraseTripleCoproductTerm
    (term : LRootedForest α × LRootedForest α × LRootedForest α) :
    RootedForest × RootedForest × RootedForest :=
  (LRootedForest.erase term.1, LRootedForest.erase term.2.1,
    LRootedForest.erase term.2.2)

/-- Relabel a labelled triple coproduct term. -/
def mapTripleCoproductTerm {β : Type v} (f : α → β)
    (term : LRootedForest α × LRootedForest α × LRootedForest α) :
    LRootedForest β × LRootedForest β × LRootedForest β :=
  (LRootedForest.mapLabels f term.1, LRootedForest.mapLabels f term.2.1,
    LRootedForest.mapLabels f term.2.2)

/-- Label every vertex in an unlabelled triple coproduct term by the same label. -/
def constLabelTripleCoproductTerm (a : α)
    (term : RootedForest × RootedForest × RootedForest) :
    LRootedForest α × LRootedForest α × LRootedForest α :=
  (LRootedForest.constLabel a term.1, LRootedForest.constLabel a term.2.1,
    LRootedForest.constLabel a term.2.2)

@[simp]
theorem eraseTripleCoproductTerm_constLabel (a : α)
    (term : RootedForest × RootedForest × RootedForest) :
    eraseTripleCoproductTerm (constLabelTripleCoproductTerm a term) = term := by
  cases term
  simp [eraseTripleCoproductTerm, constLabelTripleCoproductTerm]

@[simp]
theorem mapTripleCoproductTerm_constLabel {β : Type v} (f : α → β) (a : α)
    (term : RootedForest × RootedForest × RootedForest) :
    mapTripleCoproductTerm f (constLabelTripleCoproductTerm a term) =
      constLabelTripleCoproductTerm (f a) term := by
  cases term
  simp [mapTripleCoproductTerm, constLabelTripleCoproductTerm]

/-- Labelled tree coproduct terms erase to the corresponding unlabelled terms. -/
theorem coproductTerms_erase (t : PLTree α) :
    (coproductTerms t).map eraseCoproductTerm =
      PTree.coproductTerms (PLTree.erase t) := by
  rw [coproductTerms, PTree.coproductTerms]
  rw [← cuts_erase t]
  simp [eraseCoproductTerm, List.map_map]

theorem coproductTerms_map {β : Type v} (f : α → β) (t : PLTree α) :
    coproductTerms (PLTree.map f t) =
      (coproductTerms t).map (mapCoproductTerm f) := by
  rw [coproductTerms, coproductTerms, cuts_map f t]
  simp [mapCoproductTerm, List.map_map]

theorem coproductTerms_constLabel (a : α) (t : PTree) :
    coproductTerms (PLTree.constLabel a t) =
      (PTree.coproductTerms t).map (constLabelCoproductTerm a) := by
  rw [coproductTerms, PTree.coproductTerms, cuts_constLabel a t]
  simp [constLabelCoproductTerm, List.map_map]

/-- Every labelled coproduct term conserves total order between tensor factors. -/
theorem coproductTerms_order {t : PLTree α} {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ coproductTerms t) :
    LRootedForest.order term.1 + LRootedForest.order term.2 = order t := by
  simp [coproductTerms] at hterm
  obtain ⟨c, hc, hterm⟩ := hterm
  subst term
  exact cuts_order hc

private theorem orderList_eq_zero_iff :
    ∀ ts : List (PLTree α), orderList ts = 0 ↔ ts = []
  | [] => by simp
  | t :: ts => by
      constructor
      · intro h
        have ht := order_pos t
        simp [orderList] at h
        omega
      · intro h
        cases h

private theorem ofPLTree_list_eq_zero_iff (ts : List (PLTree α)) :
    ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) = 0 ↔
      ts = [] := by
  constructor
  · intro h
    have horder :
        orderList ts = 0 := by
      have horder' := congrArg LRootedForest.order h
      simpa [order_ofPLTree_list] using horder'
    exact (orderList_eq_zero_iff ts).1 horder
  · intro h
    subst ts
    simp

private theorem lrootedForest_add_eq_zero_left {φ ψ : LRootedForest α} (h : φ + ψ = 0) :
    φ = 0 := by
  have horder : LRootedForest.order (φ + ψ) = 0 := by
    rw [h]
    simp
  rw [LRootedForest.order_add] at horder
  have hφ : LRootedForest.order φ = 0 := by omega
  exact (LRootedForest.order_eq_zero_iff φ).1 hφ

private theorem lrootedForest_add_eq_zero_right {φ ψ : LRootedForest α} (h : φ + ψ = 0) :
    ψ = 0 := by
  have horder : LRootedForest.order (φ + ψ) = 0 := by
    rw [h]
    simp
  rw [LRootedForest.order_add] at horder
  have hψ : LRootedForest.order ψ = 0 := by omega
  exact (LRootedForest.order_eq_zero_iff ψ).1 hψ

/-- The only labelled tree coproduct term with empty left factor is `1 ⊗ t`. -/
theorem coproductTerms_left_eq_zero {t : PLTree α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ coproductTerms t) (hleft : term.1 = 0) :
    term.2 = LRootedForest.singleton (LRootedTree.ofPLTree t) := by
  simp [coproductTerms] at hterm
  obtain ⟨c, hc, hterm⟩ := hterm
  subst term
  simp [cuts] at hc
  rcases hc with hc | hc
  · obtain ⟨rc, hrc, hcut⟩ := hc
    subst c
    have hpruned : rc.pruned = [] :=
      (ofPLTree_list_eq_zero_iff rc.pruned).1 hleft
    have htrunk := rootCuts_pruned_eq_nil hrc hpruned
    simp [Cut.trunkForest, htrunk]
  · subst c
    exact False.elim
      (LRootedForest.singleton_ne_zero (LRootedTree.ofPLTree t) hleft)

/-- The only labelled tree coproduct term with empty right factor is `t ⊗ 1`. -/
theorem coproductTerms_right_eq_zero {t : PLTree α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ coproductTerms t) (hright : term.2 = 0) :
    term.1 = LRootedForest.singleton (LRootedTree.ofPLTree t) := by
  simp [coproductTerms] at hterm
  obtain ⟨c, hc, hterm⟩ := hterm
  subst term
  simp [cuts] at hc
  rcases hc with hc | hc
  · obtain ⟨rc, hrc, hcut⟩ := hc
    subst c
    have hright' : LRootedForest.singleton (LRootedTree.ofPLTree rc.trunk) = 0 := by
      simpa [Cut.trunkForest] using hright
    exact False.elim
      (LRootedForest.singleton_ne_zero (LRootedTree.ofPLTree rc.trunk) hright')
  · subst c
    simp [Cut.prunedForest, LRootedForest.singleton]

private theorem filterMap_rootCut_noPrunedBoundary (t : PLTree α) :
    (rootCuts t).filterMap
        (fun c => (RootCut.noPrunedTrunk? c).map fun u =>
          ((0 : LRootedForest α), LRootedForest.singleton (LRootedTree.ofPLTree u))) =
      [((0 : LRootedForest α), LRootedForest.singleton (LRootedTree.ofPLTree t))] := by
  rw [show (rootCuts t).filterMap
        (fun c => (RootCut.noPrunedTrunk? c).map fun u =>
          ((0 : LRootedForest α), LRootedForest.singleton (LRootedTree.ofPLTree u))) =
      ((rootCuts t).filterMap RootCut.noPrunedTrunk?).map fun u =>
        ((0 : LRootedForest α), LRootedForest.singleton (LRootedTree.ofPLTree u)) by
    induction rootCuts t with
    | nil => rfl
    | cons c cs ih =>
        cases h : RootCut.noPrunedTrunk? c <;> simp [List.filterMap, h, ih]]
  rw [rootCuts_noPrunedTrunks]
  rfl

/-- A labelled tree coproduct has exactly one term with empty left factor. -/
theorem coproductTerms_leftBoundaryCoproductTerm (t : PLTree α) :
    (coproductTerms t).filterMap leftBoundaryCoproductTerm? =
      [((0 : LRootedForest α), LRootedForest.singleton (LRootedTree.ofPLTree t))] := by
  rw [coproductTerms, cuts]
  simp only [List.map_append, List.map_map, List.filterMap_append, Function.comp_def]
  rw [show ((rootCuts t).map fun c =>
        (({ pruned := c.pruned, trunk? := some c.trunk } : Cut α).prunedForest,
          ({ pruned := c.pruned, trunk? := some c.trunk } : Cut α).trunkForest)).filterMap
        leftBoundaryCoproductTerm? =
      (rootCuts t).filterMap
        (fun c => (RootCut.noPrunedTrunk? c).map fun u =>
          ((0 : LRootedForest α), LRootedForest.singleton (LRootedTree.ofPLTree u))) by
    induction rootCuts t with
    | nil => rfl
    | cons c cs ih =>
        rw [List.map_cons, List.filterMap_cons, ih]
        cases hc : c.pruned with
        | nil =>
            simp [leftBoundaryCoproductTerm?, RootCut.noPrunedTrunk?,
              Cut.prunedForest, Cut.trunkForest, hc]
        | cons p ps =>
            have horder : LRootedForest.order
                ((c.pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) :
                  LRootedForest α) ≠ 0 := by
              intro hzero
              have hnil : c.pruned = [] := by
                exact (ofPLTree_list_eq_zero_iff c.pruned).1
                  ((LRootedForest.order_eq_zero_iff _).1 hzero)
              simp [hc] at hnil
            simp [leftBoundaryCoproductTerm?, RootCut.noPrunedTrunk?,
              Cut.prunedForest, hc]]
  calc
    ((rootCuts t).filterMap
        (fun c => (RootCut.noPrunedTrunk? c).map fun u =>
          ((0 : LRootedForest α), LRootedForest.singleton (LRootedTree.ofPLTree u)))) ++
        (List.map (fun c : Cut α => (c.prunedForest, c.trunkForest))
          ([{ pruned := [t], trunk? := none }] : List (Cut α))).filterMap
            leftBoundaryCoproductTerm? =
      [((0 : LRootedForest α), LRootedForest.singleton (LRootedTree.ofPLTree t))] ++
        (List.map (fun c : Cut α => (c.prunedForest, c.trunkForest))
          ([{ pruned := [t], trunk? := none }] : List (Cut α))).filterMap
            leftBoundaryCoproductTerm? := by
        exact congrArg
          (fun xs => xs ++
            (List.map (fun c : Cut α => (c.prunedForest, c.trunkForest))
              ([{ pruned := [t], trunk? := none }] : List (Cut α))).filterMap
                leftBoundaryCoproductTerm?)
          (filterMap_rootCut_noPrunedBoundary t)
    _ = [((0 : LRootedForest α), LRootedForest.singleton (LRootedTree.ofPLTree t))] := by
      have htorder : PLTree.order t ≠ 0 :=
        Nat.ne_of_gt (PLTree.order_pos t)
      simp [leftBoundaryCoproductTerm?, Cut.prunedForest, Cut.trunkForest, htorder]

/-- A labelled tree coproduct has exactly one term with empty right factor. -/
theorem coproductTerms_rightBoundaryCoproductTerm (t : PLTree α) :
    (coproductTerms t).filterMap rightBoundaryCoproductTerm? =
      [(LRootedForest.singleton (LRootedTree.ofPLTree t), (0 : LRootedForest α))] := by
  rw [coproductTerms, cuts]
  simp only [List.map_append, List.map_map, List.filterMap_append, Function.comp_def]
  have hroot :
      ((rootCuts t).map fun c =>
        (({ pruned := c.pruned, trunk? := some c.trunk } : Cut α).prunedForest,
          ({ pruned := c.pruned, trunk? := some c.trunk } : Cut α).trunkForest)).filterMap
          rightBoundaryCoproductTerm? = [] := by
    induction rootCuts t with
    | nil => rfl
    | cons c cs ih =>
        rw [List.map_cons, List.filterMap_cons, ih]
        have horder : PLTree.order c.trunk ≠ 0 :=
          Nat.ne_of_gt (PLTree.order_pos c.trunk)
        simp [rightBoundaryCoproductTerm?, Cut.trunkForest, horder]
  rw [hroot]
  simp [rightBoundaryCoproductTerm?, Cut.prunedForest, Cut.trunkForest,
    LRootedForest.singleton]

theorem coproductTerms_perm_of_cuts_listRelPerm {t u : PLTree α}
    (h : PTree.ListRelPerm Cut.Perm (cuts t) (cuts u)) :
    (coproductTerms t).Perm (coproductTerms u) := by
  rw [coproductTerms, coproductTerms]
  exact PTree.ListRelPerm.perm_of_eq
    (PTree.ListRelPerm.map (fun hcut => Cut.Perm.coproductTerm_eq hcut) h)

theorem coproductTerms_perm {t u : PLTree α} (h : PLTree.Perm t u) :
    (coproductTerms t).Perm (coproductTerms u) :=
  coproductTerms_perm_of_cuts_listRelPerm (cuts_listRelPerm_of_perm h)

private theorem cons_perm_append_singleton {β : Type _} (x : β) :
    ∀ xs : List β, (x :: xs).Perm (xs ++ [x])
  | [] => by simp
  | y :: ys => by
      exact (List.Perm.swap x y ys).symm.trans
        ((cons_perm_append_singleton x ys).cons y)

theorem childCuts_coproductTerms_perm (t : PLTree α) :
    ((childCuts t).map ChildCut.coproductTerm).Perm (coproductTerms t) := by
  rw [childCuts, coproductTerms, cuts]
  simp only [List.map_cons, List.map_append, List.map_map, Function.comp_def,
    ChildCut.coproductTerm, ChildCut.prunedForest, ChildCut.trunkForest,
    Cut.prunedForest, Cut.trunkForest]
  exact cons_perm_append_singleton
    ((([t].map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α), 0)
    ((rootCuts t).map fun c =>
      (((c.pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α),
        LRootedForest.singleton (LRootedTree.ofPLTree c.trunk)))

/-- The proper labelled BCK coproduct terms, excluding the two counit terms. -/
def properCoproductTerms (t : PLTree α) :
    List (LRootedForest α × LRootedForest α) :=
  (coproductTerms t).filter fun term =>
    0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2

theorem properCoproductTerms_perm {t u : PLTree α} (h : PLTree.Perm t u) :
    (properCoproductTerms t).Perm (properCoproductTerms u) :=
  List.Perm.filter _ (coproductTerms_perm h)

private theorem map_filter_eraseCoproductTerm :
    ∀ terms : List (LRootedForest α × LRootedForest α),
      ((terms.filter fun term =>
            0 < LRootedForest.order term.1 ∧
              0 < LRootedForest.order term.2).map eraseCoproductTerm) =
        (terms.map eraseCoproductTerm).filter fun term =>
          0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2
  | [] => rfl
  | term :: terms => by
      by_cases hproper :
          0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2
      · have hproperErase :
            0 < RootedForest.order (eraseCoproductTerm term).1 ∧
              0 < RootedForest.order (eraseCoproductTerm term).2 := by
          simpa [eraseCoproductTerm] using hproper
        simpa [hproper, hproperErase, eraseCoproductTerm] using
          map_filter_eraseCoproductTerm terms
      · have hproperErase :
            ¬ (0 < RootedForest.order (eraseCoproductTerm term).1 ∧
              0 < RootedForest.order (eraseCoproductTerm term).2) := by
          simpa [eraseCoproductTerm] using hproper
        simpa [hproper, hproperErase, eraseCoproductTerm] using
          map_filter_eraseCoproductTerm terms

theorem properCoproductTerms_erase (t : PLTree α) :
    (properCoproductTerms t).map eraseCoproductTerm =
      PTree.properCoproductTerms (PLTree.erase t) := by
  rw [properCoproductTerms, PTree.properCoproductTerms]
  rw [← coproductTerms_erase t]
  exact map_filter_eraseCoproductTerm (coproductTerms t)

private theorem map_filter_mapCoproductTerm {β : Type v} (f : α → β) :
    ∀ terms : List (LRootedForest α × LRootedForest α),
      ((terms.filter fun term =>
            0 < LRootedForest.order term.1 ∧
              0 < LRootedForest.order term.2).map (mapCoproductTerm f)) =
        (terms.map (mapCoproductTerm f)).filter fun term =>
          0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2
  | [] => rfl
  | term :: terms => by
      by_cases hproper :
          0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2
      · have hproperMap :
            0 < LRootedForest.order (mapCoproductTerm f term).1 ∧
              0 < LRootedForest.order (mapCoproductTerm f term).2 := by
          simpa [mapCoproductTerm] using hproper
        simpa [hproper, hproperMap, mapCoproductTerm] using
          map_filter_mapCoproductTerm f terms
      · have hproperMap :
            ¬ (0 < LRootedForest.order (mapCoproductTerm f term).1 ∧
              0 < LRootedForest.order (mapCoproductTerm f term).2) := by
          simpa [mapCoproductTerm] using hproper
        simpa [hproper, hproperMap, mapCoproductTerm] using
          map_filter_mapCoproductTerm f terms

theorem properCoproductTerms_map {β : Type v} (f : α → β) (t : PLTree α) :
    properCoproductTerms (PLTree.map f t) =
      (properCoproductTerms t).map (mapCoproductTerm f) := by
  rw [properCoproductTerms, properCoproductTerms, coproductTerms_map]
  exact (map_filter_mapCoproductTerm f (coproductTerms t)).symm

private theorem map_filter_constLabelCoproductTerm (a : α) :
    ∀ terms : List (RootedForest × RootedForest),
      ((terms.filter fun term =>
            0 < RootedForest.order term.1 ∧
              0 < RootedForest.order term.2).map (constLabelCoproductTerm a)) =
        (terms.map (constLabelCoproductTerm a)).filter fun term =>
          0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2
  | [] => rfl
  | term :: terms => by
      by_cases hproper :
          0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2
      · have hproperLabel :
            0 < LRootedForest.order (constLabelCoproductTerm a term).1 ∧
              0 < LRootedForest.order (constLabelCoproductTerm a term).2 := by
          simpa [constLabelCoproductTerm] using hproper
        simpa [hproper, hproperLabel, constLabelCoproductTerm] using
          map_filter_constLabelCoproductTerm a terms
      · have hproperLabel :
            ¬ (0 < LRootedForest.order (constLabelCoproductTerm a term).1 ∧
              0 < LRootedForest.order (constLabelCoproductTerm a term).2) := by
          simpa [constLabelCoproductTerm] using hproper
        simpa [hproper, hproperLabel, constLabelCoproductTerm] using
          map_filter_constLabelCoproductTerm a terms

theorem properCoproductTerms_constLabel (a : α) (t : PTree) :
    properCoproductTerms (PLTree.constLabel a t) =
      (PTree.properCoproductTerms t).map (constLabelCoproductTerm a) := by
  rw [properCoproductTerms, PTree.properCoproductTerms, coproductTerms_constLabel]
  exact (map_filter_constLabelCoproductTerm a (PTree.coproductTerms t)).symm

theorem properCoproductTerms_mem_coproductTerms {t : PLTree α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTerms t) :
    term ∈ coproductTerms t :=
  (List.mem_filter.1 hterm).1

theorem properCoproductTerms_order {t : PLTree α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTerms t) :
    LRootedForest.order term.1 + LRootedForest.order term.2 = order t :=
  coproductTerms_order (properCoproductTerms_mem_coproductTerms hterm)

theorem properCoproductTerms_left_order_lt {t : PLTree α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTerms t) :
    LRootedForest.order term.1 < order t := by
  have hproper :
      0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hright_pos : 0 < LRootedForest.order term.2 := hproper.2
  have horder := properCoproductTerms_order hterm
  omega

theorem properCoproductTerms_right_order_lt {t : PLTree α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTerms t) :
    LRootedForest.order term.2 < order t := by
  have hproper :
      0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hleft_pos : 0 < LRootedForest.order term.1 := hproper.1
  have horder := properCoproductTerms_order hterm
  omega

/-- Multiply two finite lists of labelled coproduct basis terms. -/
def multiplyCoproductTerms
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    List (LRootedForest α × LRootedForest α) :=
  xs.flatMap fun x =>
    ys.map fun y => (x.1 + y.1, x.2 + y.2)

private theorem pair_add_eq (x y : LRootedForest α × LRootedForest α) :
    x + y = (x.1 + y.1, x.2 + y.2) := by
  cases x
  cases y
  rfl

private theorem filterMap_map_add_leftBoundaryCoproductTerm
    (x : LRootedForest α × LRootedForest α) :
    ∀ ys : List (LRootedForest α × LRootedForest α),
      (ys.map fun y => (x.1 + y.1, x.2 + y.2)).filterMap
          leftBoundaryCoproductTerm? =
        match leftBoundaryCoproductTerm? x with
        | none => []
        | some x' => (ys.filterMap leftBoundaryCoproductTerm?).map fun y => x' + y
  | [] => by
      cases leftBoundaryCoproductTerm? x <;> rfl
  | y :: ys => by
      rw [List.map_cons, List.filterMap_cons,
        filterMap_map_add_leftBoundaryCoproductTerm x ys]
      by_cases hx : LRootedForest.order x.1 = 0
      · by_cases hy : LRootedForest.order y.1 = 0
        · have hxy : LRootedForest.order (x.1 + y.1) = 0 := by
            rw [LRootedForest.order_add, hx, hy]
          simpa [leftBoundaryCoproductTerm?, hx, hy, hxy] using
            (show (x.1 + y.1, x.2 + y.2) = x + y by
              cases x
              cases y
              rfl)
        · have hxy : LRootedForest.order (x.1 + y.1) ≠ 0 := by
            intro hzero
            rw [LRootedForest.order_add, hx] at hzero
            exact hy (by simpa using hzero)
          simp [leftBoundaryCoproductTerm?, hx, hy]
      · have hxy : LRootedForest.order (x.1 + y.1) ≠ 0 := by
          intro hzero
          rw [LRootedForest.order_add] at hzero
          have hxzero : LRootedForest.order x.1 = 0 := by omega
          exact hx hxzero
        simp [leftBoundaryCoproductTerm?, hx]

private theorem filterMap_multiply_leftBoundaryCoproductTerm
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    (multiplyCoproductTerms xs ys).filterMap leftBoundaryCoproductTerm? =
      (xs.filterMap leftBoundaryCoproductTerm?).flatMap fun x =>
        (ys.filterMap leftBoundaryCoproductTerm?).map fun y => x + y := by
  induction xs with
  | nil =>
      simp [multiplyCoproductTerms]
  | cons x xs ih =>
      rw [multiplyCoproductTerms]
      rw [multiplyCoproductTerms] at ih
      simp only [List.flatMap_cons, List.filterMap_append]
      rw [filterMap_map_add_leftBoundaryCoproductTerm x ys, ih]
      cases hx : leftBoundaryCoproductTerm? x <;> simp [hx]

private theorem filterMap_map_add_rightBoundaryCoproductTerm
    (x : LRootedForest α × LRootedForest α) :
    ∀ ys : List (LRootedForest α × LRootedForest α),
      (ys.map fun y => (x.1 + y.1, x.2 + y.2)).filterMap
          rightBoundaryCoproductTerm? =
        match rightBoundaryCoproductTerm? x with
        | none => []
        | some x' => (ys.filterMap rightBoundaryCoproductTerm?).map fun y => x' + y
  | [] => by
      cases rightBoundaryCoproductTerm? x <;> rfl
  | y :: ys => by
      rw [List.map_cons, List.filterMap_cons,
        filterMap_map_add_rightBoundaryCoproductTerm x ys]
      by_cases hx : LRootedForest.order x.2 = 0
      · by_cases hy : LRootedForest.order y.2 = 0
        · have hxy : LRootedForest.order (x.2 + y.2) = 0 := by
            rw [LRootedForest.order_add, hx, hy]
          simpa [rightBoundaryCoproductTerm?, hx, hy, hxy] using
            (show (x.1 + y.1, x.2 + y.2) = x + y by
              cases x
              cases y
              rfl)
        · have hxy : LRootedForest.order (x.2 + y.2) ≠ 0 := by
            intro hzero
            rw [LRootedForest.order_add, hx] at hzero
            exact hy (by simpa using hzero)
          simp [rightBoundaryCoproductTerm?, hx, hy]
      · have hxy : LRootedForest.order (x.2 + y.2) ≠ 0 := by
          intro hzero
          rw [LRootedForest.order_add] at hzero
          have hxzero : LRootedForest.order x.2 = 0 := by omega
          exact hx hxzero
        simp [rightBoundaryCoproductTerm?, hx]

private theorem filterMap_multiply_rightBoundaryCoproductTerm
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    (multiplyCoproductTerms xs ys).filterMap rightBoundaryCoproductTerm? =
      (xs.filterMap rightBoundaryCoproductTerm?).flatMap fun x =>
        (ys.filterMap rightBoundaryCoproductTerm?).map fun y => x + y := by
  induction xs with
  | nil =>
      simp [multiplyCoproductTerms]
  | cons x xs ih =>
      rw [multiplyCoproductTerms]
      rw [multiplyCoproductTerms] at ih
      simp only [List.flatMap_cons, List.filterMap_append]
      rw [filterMap_map_add_rightBoundaryCoproductTerm x ys, ih]
      cases hx : rightBoundaryCoproductTerm? x <;> simp [hx]

/-- Multiplication of labelled coproduct terms commutes with erasing labels. -/
theorem multiplyCoproductTerms_erase
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    (multiplyCoproductTerms xs ys).map eraseCoproductTerm =
      PTree.multiplyCoproductTerms (xs.map eraseCoproductTerm) (ys.map eraseCoproductTerm) := by
  rw [multiplyCoproductTerms, PTree.multiplyCoproductTerms]
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro x _hx
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro y _hy
  simp [eraseCoproductTerm]

theorem multiplyCoproductTerms_map {β : Type v} (f : α → β)
    (xs ys : List (LRootedForest α × LRootedForest α)) :
    multiplyCoproductTerms (xs.map (mapCoproductTerm f)) (ys.map (mapCoproductTerm f)) =
      (multiplyCoproductTerms xs ys).map (mapCoproductTerm f) := by
  rw [multiplyCoproductTerms, multiplyCoproductTerms]
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro x _hx
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro y _hy
  exact (mapCoproductTerm_add f x y).symm

theorem multiplyCoproductTerms_constLabel (a : α)
    (xs ys : List (RootedForest × RootedForest)) :
    multiplyCoproductTerms (xs.map (constLabelCoproductTerm a))
        (ys.map (constLabelCoproductTerm a)) =
      (PTree.multiplyCoproductTerms xs ys).map (constLabelCoproductTerm a) := by
  rw [multiplyCoproductTerms, PTree.multiplyCoproductTerms]
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro x _hx
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro y _hy
  exact (constLabelCoproductTerm_add a x y).symm

/-- Multiplicative extension of labelled coproduct terms to planar labelled forests. -/
def coproductTermsList : List (PLTree α) → List (LRootedForest α × LRootedForest α)
  | [] => [(0, 0)]
  | t :: ts => multiplyCoproductTerms (coproductTerms t) (coproductTermsList ts)

/-- Labelled forest coproduct terms erase to the corresponding unlabelled terms. -/
theorem coproductTermsList_erase :
    ∀ ts : List (PLTree α),
      (coproductTermsList ts).map eraseCoproductTerm =
        PTree.coproductTermsList (ts.map PLTree.erase)
  | [] => by
      simp [coproductTermsList, PTree.coproductTermsList, eraseCoproductTerm,
        LRootedForest.erase]
  | t :: ts => by
      rw [coproductTermsList, PTree.coproductTermsList.eq_def]
      simp only [List.map_cons]
      rw [← coproductTerms_erase t, ← coproductTermsList_erase ts]
      exact multiplyCoproductTerms_erase (coproductTerms t) (coproductTermsList ts)

theorem coproductTermsList_map {β : Type v} (f : α → β) :
    ∀ ts : List (PLTree α),
      coproductTermsList (ts.map (PLTree.map f)) =
        (coproductTermsList ts).map (mapCoproductTerm f)
  | [] => by
      simp [coproductTermsList, mapCoproductTerm, LRootedForest.mapLabels]
  | t :: ts => by
      rw [List.map_cons, coproductTermsList, coproductTermsList, coproductTerms_map f t,
        coproductTermsList_map f ts]
      exact multiplyCoproductTerms_map f (coproductTerms t) (coproductTermsList ts)

theorem coproductTermsList_constLabel (a : α) :
    ∀ ts : List PTree,
      coproductTermsList (ts.map (PLTree.constLabel a)) =
        (PTree.coproductTermsList ts).map (constLabelCoproductTerm a)
  | [] => by
      simp [coproductTermsList, PTree.coproductTermsList, constLabelCoproductTerm,
        LRootedForest.constLabel]
  | t :: ts => by
      rw [List.map_cons, coproductTermsList, PTree.coproductTermsList.eq_def,
        coproductTerms_constLabel a t, coproductTermsList_constLabel a ts]
      exact multiplyCoproductTerms_constLabel a (PTree.coproductTerms t)
        (PTree.coproductTermsList ts)

theorem multiplyCoproductTerms_perm_left
    {xs ys zs : List (LRootedForest α × LRootedForest α)} (h : xs.Perm ys) :
    (multiplyCoproductTerms xs zs).Perm (multiplyCoproductTerms ys zs) := by
  rw [multiplyCoproductTerms, multiplyCoproductTerms]
  exact List.Perm.flatMap h (fun _ _ => List.Perm.refl _)

theorem multiplyCoproductTerms_perm_right
    {xs ys zs : List (LRootedForest α × LRootedForest α)} (h : ys.Perm zs) :
    (multiplyCoproductTerms xs ys).Perm (multiplyCoproductTerms xs zs) := by
  rw [multiplyCoproductTerms, multiplyCoproductTerms]
  exact List.Perm.flatMap (List.Perm.refl xs)
    (fun x _ => List.Perm.map (fun y => (x.1 + y.1, x.2 + y.2)) h)

theorem multiplyCoproductTerms_perm
    {xs xs' ys ys' : List (LRootedForest α × LRootedForest α)}
    (hxs : xs.Perm xs') (hys : ys.Perm ys') :
    (multiplyCoproductTerms xs ys).Perm (multiplyCoproductTerms xs' ys') :=
  (multiplyCoproductTerms_perm_left (zs := ys) hxs).trans
    (multiplyCoproductTerms_perm_right (xs := xs') hys)

theorem coproductTermsList_perm_rootCutsList :
    ∀ ts : List (PLTree α),
      (coproductTermsList ts).Perm
        ((rootCutsList ts).map RootCutList.coproductTerm)
  | [] => by
      simp [coproductTermsList, rootCutsList, RootCutList.coproductTerm,
        RootCutList.prunedForest, RootCutList.trunkForest]
  | t :: ts => by
      rw [coproductTermsList, rootCutsList]
      have hmul :
          (multiplyCoproductTerms (coproductTerms t) (coproductTermsList ts)).Perm
            (multiplyCoproductTerms ((childCuts t).map ChildCut.coproductTerm)
              ((rootCutsList ts).map RootCutList.coproductTerm)) :=
        multiplyCoproductTerms_perm (childCuts_coproductTerms_perm t).symm
          (coproductTermsList_perm_rootCutsList ts)
      simpa [multiplyCoproductTerms, List.flatMap_map, List.map_flatMap, List.map_map,
        Function.comp_def, RootCutList.coproductTerm_consChild, pair_add_eq] using hmul

theorem coproductTerms_node_perm (a : α) (ts : List (PLTree α)) :
    (coproductTerms (.node a ts)).Perm
      (((coproductTermsList ts).map fun term =>
          (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))) ++
        [(LRootedForest.singleton (LRootedTree.ofPLTree (.node a ts)), 0)]) := by
  have hroot :
      ((coproductTermsList ts).map fun term =>
          (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))).Perm
        ((rootCutsList ts).map fun c =>
          (((c.pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α),
            LRootedForest.singleton (LRootedTree.ofPLTree (.node a c.trunks)))) := by
    have h := (coproductTermsList_perm_rootCutsList ts).map
      (fun term => (term.1, LRootedForest.singleton (LRootedForest.graft a term.2)))
    have hmap :
        ((rootCutsList ts).map
            (((fun term =>
              (term.1, LRootedForest.singleton (LRootedForest.graft a term.2))) ∘
                RootCutList.coproductTerm))) =
          ((rootCutsList ts).map fun c =>
            (((c.pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) :
                LRootedForest α),
              LRootedForest.singleton (LRootedTree.ofPLTree (.node a c.trunks)))) := by
      apply List.map_congr_left
      intro c _
      have hgraft :
          LRootedForest.graft a c.trunkForest = LRootedTree.ofPLTree (.node a c.trunks) := by
        simpa [RootCutList.trunkForest] using LRootedForest.graft_ofPLTree_list a c.trunks
      change
        (c.prunedForest, LRootedForest.singleton (LRootedForest.graft a c.trunkForest)) =
          (((c.pruned.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α),
            LRootedForest.singleton (LRootedTree.ofPLTree (.node a c.trunks)))
      rw [hgraft]
      simp [RootCutList.prunedForest]
    simpa [hmap] using h
  rw [coproductTerms, cuts, rootCuts]
  simp only [List.map_append, List.map_map, Function.comp_def]
  exact (hroot.symm.append_right
    [(LRootedForest.singleton (LRootedTree.ofPLTree (.node a ts)), 0)]).trans (by simp)

theorem multiplyCoproductTerms_comm
    {xs ys : List (LRootedForest α × LRootedForest α)} :
    (multiplyCoproductTerms xs ys).Perm (multiplyCoproductTerms ys xs) := by
  rw [multiplyCoproductTerms, multiplyCoproductTerms]
  exact flatMap_map_swap
    (fun x y : LRootedForest α × LRootedForest α => (x.1 + y.1, x.2 + y.2))
    (fun y x : LRootedForest α × LRootedForest α => (y.1 + x.1, y.2 + x.2))
    (by intro x y; simp [add_comm]) xs ys

theorem multiplyCoproductTerms_assoc
    {xs ys zs : List (LRootedForest α × LRootedForest α)} :
    (multiplyCoproductTerms xs (multiplyCoproductTerms ys zs)).Perm
      (multiplyCoproductTerms (multiplyCoproductTerms xs ys) zs) := by
  simp [multiplyCoproductTerms, List.flatMap_assoc, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, add_assoc]

theorem coproductTermsList_append_perm (ts us : List (PLTree α)) :
    (coproductTermsList (ts ++ us)).Perm
      (multiplyCoproductTerms (coproductTermsList ts) (coproductTermsList us)) := by
  induction ts with
  | nil =>
      simp [coproductTermsList, multiplyCoproductTerms]
  | cons t ts ih =>
      rw [List.cons_append, coproductTermsList, coproductTermsList]
      exact (multiplyCoproductTerms_perm_right (xs := coproductTerms t) ih).trans
        multiplyCoproductTerms_assoc

theorem coproductTermsList_perm_of_list_perm {ts us : List (PLTree α)} (h : ts.Perm us) :
    (coproductTermsList ts).Perm (coproductTermsList us) := by
  induction h with
  | nil => rfl
  | cons t h ih =>
      simpa [coproductTermsList] using multiplyCoproductTerms_perm_right
        (xs := coproductTerms t) ih
  | swap t u ts =>
      have hassoc₁ :
          (multiplyCoproductTerms (coproductTerms t)
              (multiplyCoproductTerms (coproductTerms u) (coproductTermsList ts))).Perm
            (multiplyCoproductTerms
              (multiplyCoproductTerms (coproductTerms t) (coproductTerms u))
              (coproductTermsList ts)) :=
        multiplyCoproductTerms_assoc
      have hcomm :
          (multiplyCoproductTerms
              (multiplyCoproductTerms (coproductTerms t) (coproductTerms u))
              (coproductTermsList ts)).Perm
            (multiplyCoproductTerms
              (multiplyCoproductTerms (coproductTerms u) (coproductTerms t))
              (coproductTermsList ts)) :=
        multiplyCoproductTerms_perm_left multiplyCoproductTerms_comm
      have hassoc₂ :
          (multiplyCoproductTerms
              (multiplyCoproductTerms (coproductTerms u) (coproductTerms t))
              (coproductTermsList ts)).Perm
            (multiplyCoproductTerms (coproductTerms u)
              (multiplyCoproductTerms (coproductTerms t) (coproductTermsList ts))) :=
        multiplyCoproductTerms_assoc.symm
      simpa [coproductTermsList] using (hassoc₁.trans (hcomm.trans hassoc₂)).symm
  | trans htu huv ihu ihv => exact ihu.trans ihv

theorem coproductTermsList_forall₂_perm :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ PLTree.Perm ts us →
      (coproductTermsList ts).Perm (coproductTermsList us)
  | [], [], .nil => List.Perm.refl _
  | _ :: _, _ :: _, .cons h hs =>
      multiplyCoproductTerms_perm (coproductTerms_perm h)
        (coproductTermsList_forall₂_perm hs)

theorem coproductTermsList_listRelPerm {ts us : List (PLTree α)}
    (h : PTree.ListRelPerm PLTree.Perm ts us) :
    (coproductTermsList ts).Perm (coproductTermsList us) := by
  rcases h with ⟨ts', hp, hrel⟩
  exact (coproductTermsList_perm_of_list_perm hp).trans
    (coproductTermsList_forall₂_perm hrel)

theorem coproductTermsList_forestPerm {ts us : List (PLTree α)} (h : PLTree.ForestPerm ts us) :
    (coproductTermsList ts).Perm (coproductTermsList us) :=
  coproductTermsList_listRelPerm (listRelPerm_of_forestPerm h)

theorem multiplyCoproductTerms_order {xs ys : List (LRootedForest α × LRootedForest α)}
    {m n : Nat}
    (hxs : ∀ term ∈ xs, LRootedForest.order term.1 + LRootedForest.order term.2 = m)
    (hys : ∀ term ∈ ys, LRootedForest.order term.1 + LRootedForest.order term.2 = n)
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ multiplyCoproductTerms xs ys) :
    LRootedForest.order term.1 + LRootedForest.order term.2 = m + n := by
  simp [multiplyCoproductTerms] at hterm
  obtain ⟨x₁, x₂, hx, y₁, y₂, hy, hterm⟩ := hterm
  subst term
  have hx_order := hxs (x₁, x₂) hx
  have hy_order := hys (y₁, y₂) hy
  simp at hx_order hy_order
  rw [LRootedForest.order_add, LRootedForest.order_add]
  omega

/-- Every labelled planar-forest coproduct term conserves total order. -/
theorem coproductTermsList_order :
    ∀ {ts : List (PLTree α)} {term : LRootedForest α × LRootedForest α},
      term ∈ coproductTermsList ts →
        LRootedForest.order term.1 + LRootedForest.order term.2 = orderList ts
  | [], term, hterm => by
      simp [coproductTermsList] at hterm
      subst term
      simp
  | t :: ts, term, hterm => by
      exact multiplyCoproductTerms_order
        (fun term hterm => coproductTerms_order hterm)
        (fun term hterm => coproductTermsList_order hterm)
        hterm

/-- The only labelled planar-forest coproduct terms with empty left factor are `1 ⊗ φ`. -/
theorem coproductTermsList_left_eq_zero :
    ∀ {ts : List (PLTree α)} {term : LRootedForest α × LRootedForest α},
      term ∈ coproductTermsList ts → term.1 = 0 →
        term.2 = (ts.map LRootedTree.ofPLTree : LRootedForest α)
  | [], term, hterm, _ => by
      simp [coproductTermsList] at hterm
      subst term
      simp
  | t :: ts, term, hterm, hleft => by
      simp [coproductTermsList, multiplyCoproductTerms] at hterm
      obtain ⟨x₁, x₂, hx, y₁, y₂, hy, hterm⟩ := hterm
      subst term
      have hxleft : x₁ = 0 := lrootedForest_add_eq_zero_left hleft
      have hyleft : y₁ = 0 := lrootedForest_add_eq_zero_right hleft
      have hxright := coproductTerms_left_eq_zero (t := t) (term := (x₁, x₂)) hx hxleft
      have hyright :=
        coproductTermsList_left_eq_zero (ts := ts) (term := (y₁, y₂)) hy hyleft
      have hxright' : x₂ = LRootedForest.singleton (LRootedTree.ofPLTree t) := by
        simpa using hxright
      have hyright' : y₂ = (ts.map LRootedTree.ofPLTree : LRootedForest α) := by
        simpa using hyright
      change x₂ + y₂ = (LRootedTree.ofPLTree t :: ts.map LRootedTree.ofPLTree :
        List (LRootedTree α))
      rw [hxright', hyright']
      simp [LRootedForest.singleton]

/-- The only labelled planar-forest coproduct terms with empty right factor are `φ ⊗ 1`. -/
theorem coproductTermsList_right_eq_zero :
    ∀ {ts : List (PLTree α)} {term : LRootedForest α × LRootedForest α},
      term ∈ coproductTermsList ts → term.2 = 0 →
        term.1 = (ts.map LRootedTree.ofPLTree : LRootedForest α)
  | [], term, hterm, _ => by
      simp [coproductTermsList] at hterm
      subst term
      simp
  | t :: ts, term, hterm, hright => by
      simp [coproductTermsList, multiplyCoproductTerms] at hterm
      obtain ⟨x₁, x₂, hx, y₁, y₂, hy, hterm⟩ := hterm
      subst term
      have hxright : x₂ = 0 := lrootedForest_add_eq_zero_left hright
      have hyright : y₂ = 0 := lrootedForest_add_eq_zero_right hright
      have hxleft := coproductTerms_right_eq_zero (t := t) (term := (x₁, x₂)) hx hxright
      have hyleft :=
        coproductTermsList_right_eq_zero (ts := ts) (term := (y₁, y₂)) hy hyright
      have hxleft' : x₁ = LRootedForest.singleton (LRootedTree.ofPLTree t) := by
        simpa using hxleft
      have hyleft' : y₁ = (ts.map LRootedTree.ofPLTree : LRootedForest α) := by
        simpa using hyleft
      change x₁ + y₁ = (LRootedTree.ofPLTree t :: ts.map LRootedTree.ofPLTree :
        List (LRootedTree α))
      rw [hxleft', hyleft']
      simp [LRootedForest.singleton]

/-- A labelled planar-forest coproduct has exactly one term with empty left factor. -/
theorem coproductTermsList_leftBoundaryCoproductTerm :
    ∀ ts : List (PLTree α),
      (coproductTermsList ts).filterMap leftBoundaryCoproductTerm? =
        [((0 : LRootedForest α), (ts.map LRootedTree.ofPLTree : LRootedForest α))]
  | [] => by
      simp [coproductTermsList, leftBoundaryCoproductTerm?]
  | t :: ts => by
      rw [coproductTermsList, filterMap_multiply_leftBoundaryCoproductTerm,
        coproductTerms_leftBoundaryCoproductTerm t,
        coproductTermsList_leftBoundaryCoproductTerm ts]
      simp [LRootedForest.singleton]

/-- A labelled planar-forest coproduct has exactly one term with empty right factor. -/
theorem coproductTermsList_rightBoundaryCoproductTerm :
    ∀ ts : List (PLTree α),
      (coproductTermsList ts).filterMap rightBoundaryCoproductTerm? =
        [((ts.map LRootedTree.ofPLTree : LRootedForest α), (0 : LRootedForest α))]
  | [] => by
      simp [coproductTermsList, rightBoundaryCoproductTerm?]
  | t :: ts => by
      rw [coproductTermsList, filterMap_multiply_rightBoundaryCoproductTerm,
        coproductTerms_rightBoundaryCoproductTerm t,
        coproductTermsList_rightBoundaryCoproductTerm ts]
      simp [LRootedForest.singleton]

/-- The proper BCK coproduct terms for a planar labelled forest. -/
def properCoproductTermsList (ts : List (PLTree α)) :
    List (LRootedForest α × LRootedForest α) :=
  (coproductTermsList ts).filter fun term =>
    0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2

theorem properCoproductTermsList_erase (ts : List (PLTree α)) :
    (properCoproductTermsList ts).map eraseCoproductTerm =
      PTree.properCoproductTermsList (ts.map PLTree.erase) := by
  rw [properCoproductTermsList, PTree.properCoproductTermsList]
  rw [← coproductTermsList_erase ts]
  exact map_filter_eraseCoproductTerm (coproductTermsList ts)

theorem properCoproductTermsList_map {β : Type v} (f : α → β)
    (ts : List (PLTree α)) :
    properCoproductTermsList (ts.map (PLTree.map f)) =
      (properCoproductTermsList ts).map (mapCoproductTerm f) := by
  rw [properCoproductTermsList, properCoproductTermsList, coproductTermsList_map]
  exact (map_filter_mapCoproductTerm f (coproductTermsList ts)).symm

theorem properCoproductTermsList_constLabel (a : α) (ts : List PTree) :
    properCoproductTermsList (ts.map (PLTree.constLabel a)) =
      (PTree.properCoproductTermsList ts).map (constLabelCoproductTerm a) := by
  rw [properCoproductTermsList, PTree.properCoproductTermsList,
    coproductTermsList_constLabel]
  exact (map_filter_constLabelCoproductTerm a (PTree.coproductTermsList ts)).symm

theorem properCoproductTermsList_forall₂_perm
    {ts us : List (PLTree α)} (h : List.Forall₂ PLTree.Perm ts us) :
    (properCoproductTermsList ts).Perm (properCoproductTermsList us) :=
  List.Perm.filter _ (coproductTermsList_forall₂_perm h)

theorem properCoproductTermsList_mem_coproductTermsList {ts : List (PLTree α)}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTermsList ts) :
    term ∈ coproductTermsList ts :=
  (List.mem_filter.1 hterm).1

theorem properCoproductTermsList_order {ts : List (PLTree α)}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTermsList ts) :
    LRootedForest.order term.1 + LRootedForest.order term.2 = orderList ts :=
  coproductTermsList_order (properCoproductTermsList_mem_coproductTermsList hterm)

theorem properCoproductTermsList_left_order_lt {ts : List (PLTree α)}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTermsList ts) :
    LRootedForest.order term.1 < orderList ts := by
  have hproper :
      0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hright_pos : 0 < LRootedForest.order term.2 := hproper.2
  have horder := properCoproductTermsList_order hterm
  omega

theorem properCoproductTermsList_right_order_lt {ts : List (PLTree α)}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ properCoproductTermsList ts) :
    LRootedForest.order term.2 < orderList ts := by
  have hproper :
      0 < LRootedForest.order term.1 ∧ 0 < LRootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hleft_pos : 0 < LRootedForest.order term.1 := hproper.1
  have horder := properCoproductTermsList_order hterm
  omega

namespace Cut

/-- Coproduct terms of the trunk of a labelled cut, using `[(0, 0)]` for the full cut. -/
def trunkCoproductTerms (c : Cut α) : List (LRootedForest α × LRootedForest α) :=
  match c.trunk? with
  | none => [(0, 0)]
  | some trunk => coproductTerms trunk

theorem trunkCoproductTerms_order {c : Cut α}
    {term : LRootedForest α × LRootedForest α}
    (hterm : term ∈ c.trunkCoproductTerms) :
    LRootedForest.order term.1 + LRootedForest.order term.2 =
      LRootedForest.order c.trunkForest := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? with
      | none =>
          simp [trunkCoproductTerms, trunkForest] at hterm ⊢
          subst term
          simp
      | some trunk =>
          simpa [trunkCoproductTerms, trunkForest] using coproductTerms_order hterm

theorem trunkCoproductTerms_perm {c d : Cut α} (h : Perm c d) :
    c.trunkCoproductTerms.Perm d.trunkCoproductTerms := by
  rcases c with ⟨cp, ct⟩
  rcases d with ⟨dp, dt⟩
  rcases h with ⟨_, ht⟩
  cases ct with
  | none =>
      cases dt with
      | none => rfl
      | some u => simp [OptionPerm] at ht
  | some t =>
      cases dt with
      | none => simp [OptionPerm] at ht
      | some u =>
          simp [OptionPerm] at ht
          exact coproductTerms_perm (LRootedTree.ofPLTree_eq_iff.1 ht)

theorem trunkCoproductTerms_erase (c : Cut α) :
    c.trunkCoproductTerms.map eraseCoproductTerm =
      PTree.Cut.trunkCoproductTerms (Cut.erase c) := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? with
      | none =>
          have hzero : LRootedForest.erase (0 : LRootedForest α) = (0 : RootedForest) := by
            change LRootedForest.erase (LRootedForest.empty : LRootedForest α) =
              RootedForest.empty
            exact LRootedForest.erase_empty
          simp [trunkCoproductTerms, PTree.Cut.trunkCoproductTerms, Cut.erase,
            eraseCoproductTerm, hzero]
      | some trunk =>
          simp [trunkCoproductTerms, PTree.Cut.trunkCoproductTerms, Cut.erase,
            coproductTerms_erase]

end Cut

/-- Planar terms for `(Δ ⊗ id)Δ(t)`, keeping the original labelled cut representatives. -/
def nestedCoproductLeftTerms (t : PLTree α) :
    List (LRootedForest α × LRootedForest α × LRootedForest α) :=
  (cuts t).flatMap fun c =>
    (coproductTermsList c.pruned).map fun left => (left.1, left.2, c.trunkForest)

/-- Planar terms for `(id ⊗ Δ)Δ(t)`, keeping the original labelled cut representatives. -/
def nestedCoproductRightTerms (t : PLTree α) :
    List (LRootedForest α × LRootedForest α × LRootedForest α) :=
  (cuts t).flatMap fun c =>
    c.trunkCoproductTerms.map fun right => (c.prunedForest, right.1, right.2)

theorem nestedCoproductLeftTerms_erase (t : PLTree α) :
    (nestedCoproductLeftTerms t).map eraseTripleCoproductTerm =
      PTree.nestedCoproductLeftTerms (PLTree.erase t) := by
  rw [nestedCoproductLeftTerms, PTree.nestedCoproductLeftTerms, ← cuts_erase t]
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro c _hc
  rw [List.map_map]
  change
    List.map (eraseTripleCoproductTerm ∘ fun left => (left.1, left.2, c.trunkForest))
        (coproductTermsList c.pruned) =
      List.map (fun left => (left.1, left.2, PTree.Cut.trunkForest (Cut.erase c)))
        (PTree.coproductTermsList (c.pruned.map PLTree.erase))
  rw [← coproductTermsList_erase c.pruned, List.map_map]
  apply List.map_congr_left
  intro left _hleft
  simp [eraseTripleCoproductTerm, eraseCoproductTerm, Cut.erase_trunkForest]

theorem nestedCoproductRightTerms_erase (t : PLTree α) :
    (nestedCoproductRightTerms t).map eraseTripleCoproductTerm =
      PTree.nestedCoproductRightTerms (PLTree.erase t) := by
  rw [nestedCoproductRightTerms, PTree.nestedCoproductRightTerms, ← cuts_erase t]
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro c _hc
  rw [List.map_map, ← Cut.trunkCoproductTerms_erase c, List.map_map]
  apply List.map_congr_left
  intro right _hright
  simp [eraseTripleCoproductTerm, eraseCoproductTerm, Cut.erase_prunedForest]

theorem nestedCoproductLeftCut_forall₂_perm {c d : Cut α}
    (hpruned : List.Forall₂ PLTree.Perm c.pruned d.pruned)
    (htrunk : c.trunkForest = d.trunkForest) :
    ((coproductTermsList c.pruned).map
        fun left => (left.1, left.2, c.trunkForest)).Perm
      ((coproductTermsList d.pruned).map
        fun left => (left.1, left.2, d.trunkForest)) := by
  rw [htrunk]
  exact (coproductTermsList_forall₂_perm hpruned).map
    (fun left => (left.1, left.2, d.trunkForest))

theorem nestedCoproductLeftCut_perm {c d : Cut α} (h : Cut.Perm c d) :
    ((coproductTermsList c.pruned).map
        fun left => (left.1, left.2, c.trunkForest)).Perm
      ((coproductTermsList d.pruned).map
        fun left => (left.1, left.2, d.trunkForest)) := by
  rw [h.trunkForest_eq]
  exact (coproductTermsList_forestPerm h.1).map
    (fun left => (left.1, left.2, d.trunkForest))

theorem nestedCoproductLeftCuts_forall₂_perm :
    ∀ {cs ds : List (Cut α)}, List.Forall₂ Cut.Perm cs ds →
      (cs.flatMap fun c =>
        (coproductTermsList c.pruned).map
          fun left => (left.1, left.2, c.trunkForest)).Perm
      (ds.flatMap fun d =>
        (coproductTermsList d.pruned).map
          fun left => (left.1, left.2, d.trunkForest))
  | [], [], .nil => List.Perm.refl _
  | _ :: _, _ :: _, .cons h htail => by
      simp only [List.flatMap_cons]
      exact (nestedCoproductLeftCut_perm h).append
        (nestedCoproductLeftCuts_forall₂_perm htail)

theorem nestedCoproductLeftCuts_listRelPerm {cs ds : List (Cut α)}
    (h : PTree.ListRelPerm Cut.Perm cs ds) :
    (cs.flatMap fun c =>
        (coproductTermsList c.pruned).map
          fun left => (left.1, left.2, c.trunkForest)).Perm
      (ds.flatMap fun d =>
        (coproductTermsList d.pruned).map
          fun left => (left.1, left.2, d.trunkForest)) := by
  rcases h with ⟨cs', hp, hrel⟩
  exact (List.Perm.flatMap hp (fun _ _ => List.Perm.refl _)).trans
    (nestedCoproductLeftCuts_forall₂_perm hrel)

theorem nestedCoproductLeftTerms_listRelPerm {t u : PLTree α}
    (h : PTree.ListRelPerm Cut.Perm (cuts t) (cuts u)) :
    (nestedCoproductLeftTerms t).Perm (nestedCoproductLeftTerms u) := by
  simpa [nestedCoproductLeftTerms] using nestedCoproductLeftCuts_listRelPerm h

theorem nestedCoproductLeftTerms_perm {t u : PLTree α} (h : PLTree.Perm t u) :
    (nestedCoproductLeftTerms t).Perm (nestedCoproductLeftTerms u) :=
  nestedCoproductLeftTerms_listRelPerm (cuts_listRelPerm_of_perm h)

theorem nestedCoproductRightCut_perm {c d : Cut α} (h : Cut.Perm c d) :
    (c.trunkCoproductTerms.map
        fun right => (c.prunedForest, right.1, right.2)).Perm
      (d.trunkCoproductTerms.map
        fun right => (d.prunedForest, right.1, right.2)) := by
  rw [h.prunedForest_eq]
  exact (Cut.trunkCoproductTerms_perm h).map
    (fun right => (d.prunedForest, right.1, right.2))

theorem nestedCoproductRightCuts_forall₂_perm :
    ∀ {cs ds : List (Cut α)}, List.Forall₂ Cut.Perm cs ds →
      (cs.flatMap fun c =>
        c.trunkCoproductTerms.map
          fun right => (c.prunedForest, right.1, right.2)).Perm
      (ds.flatMap fun d =>
        d.trunkCoproductTerms.map
          fun right => (d.prunedForest, right.1, right.2))
  | [], [], .nil => List.Perm.refl _
  | _ :: _, _ :: _, .cons h htail => by
      simp only [List.flatMap_cons]
      exact (nestedCoproductRightCut_perm h).append
        (nestedCoproductRightCuts_forall₂_perm htail)

theorem nestedCoproductRightCuts_listRelPerm {cs ds : List (Cut α)}
    (h : PTree.ListRelPerm Cut.Perm cs ds) :
    (cs.flatMap fun c =>
        c.trunkCoproductTerms.map
          fun right => (c.prunedForest, right.1, right.2)).Perm
      (ds.flatMap fun d =>
        d.trunkCoproductTerms.map
          fun right => (d.prunedForest, right.1, right.2)) := by
  rcases h with ⟨cs', hp, hrel⟩
  exact (List.Perm.flatMap hp (fun _ _ => List.Perm.refl _)).trans
    (nestedCoproductRightCuts_forall₂_perm hrel)

theorem nestedCoproductRightTerms_listRelPerm {t u : PLTree α}
    (h : PTree.ListRelPerm Cut.Perm (cuts t) (cuts u)) :
    (nestedCoproductRightTerms t).Perm (nestedCoproductRightTerms u) := by
  simpa [nestedCoproductRightTerms] using nestedCoproductRightCuts_listRelPerm h

theorem nestedCoproductRightTerms_perm {t u : PLTree α} (h : PLTree.Perm t u) :
    (nestedCoproductRightTerms t).Perm (nestedCoproductRightTerms u) :=
  nestedCoproductRightTerms_listRelPerm (cuts_listRelPerm_of_perm h)

theorem nestedCoproductLeftTerms_order
    {t : PLTree α} {term : LRootedForest α × LRootedForest α × LRootedForest α}
    (hterm : term ∈ nestedCoproductLeftTerms t) :
    LRootedForest.order term.1 + LRootedForest.order term.2.1 +
        LRootedForest.order term.2.2 = order t := by
  simp [nestedCoproductLeftTerms] at hterm
  obtain ⟨c, hc, left₁, left₂, hleft, hterm⟩ := hterm
  subst term
  have hleft_order := coproductTermsList_order hleft
  have hcut := cuts_order hc
  change
    LRootedForest.order left₁ + LRootedForest.order left₂ = orderList c.pruned
      at hleft_order
  rw [← order_ofPLTree_list c.pruned] at hleft_order
  change
    LRootedForest.order left₁ + LRootedForest.order left₂ =
      LRootedForest.order c.prunedForest at hleft_order
  change
    LRootedForest.order left₁ + LRootedForest.order left₂ +
        LRootedForest.order c.trunkForest = order t
  omega

theorem nestedCoproductRightTerms_order
    {t : PLTree α} {term : LRootedForest α × LRootedForest α × LRootedForest α}
    (hterm : term ∈ nestedCoproductRightTerms t) :
    LRootedForest.order term.1 + LRootedForest.order term.2.1 +
        LRootedForest.order term.2.2 = order t := by
  simp [nestedCoproductRightTerms] at hterm
  obtain ⟨c, hc, right₁, right₂, hright, hterm⟩ := hterm
  subst term
  have hright_order := Cut.trunkCoproductTerms_order hright
  have hcut := cuts_order hc
  change
    LRootedForest.order right₁ + LRootedForest.order right₂ =
      LRootedForest.order c.trunkForest at hright_order
  change
    LRootedForest.order c.prunedForest + LRootedForest.order right₁ +
        LRootedForest.order right₂ = order t
  omega

@[simp]
theorem rootCutsList_nil :
    rootCutsList ([] : List (PLTree α)) = [{ pruned := [], trunks := [] }] := by
  simp [rootCutsList]

@[simp]
theorem rootCuts_node_nil (a : α) :
    rootCuts (.node a []) = [{ pruned := [], trunk := .node a [] }] := by
  simp [rootCuts]

end PLTree

end HopfAlgebras
