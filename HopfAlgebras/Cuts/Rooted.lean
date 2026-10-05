/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Forests.Rooted

/-!
# Admissible Cuts

This file defines finite admissible-cut data for planar rooted trees. The
resulting terms are the combinatorial input for the BCK/Connes-Kreimer
coproduct.

The definitions here are intentionally planar. Passing to non-planar trees and
building the coproduct on `ForestAlgebra` will require quotient-invariance
proofs and coefficient multiplicities.

## Main definitions

* `PTree.RootCut` - an admissible cut which keeps the root component
* `PTree.Cut` - an admissible cut, allowing the full cut
* `PTree.cuts` - finite list of admissible cuts
* `PTree.cutTerms` - admissible cuts as `(pruned forest, trunk index)` terms
* `PTree.coproductTerms` - admissible cuts as forest-pair coproduct terms

## References

* Alain Connes, Dirk Kreimer, *Hopf Algebras, Renormalization and
  Noncommutative Geometry*
* Loic Foissy, *An introduction to Hopf algebras of trees*
-/

namespace HopfAlgebras

namespace PTree

/-- A cut below the root, so the trunk remains a non-empty tree. -/
structure RootCut where
  pruned : List PTree
  trunk : PTree
deriving Repr

/-- A child-level cut choice. `none` means the edge above the child is cut. -/
structure ChildCut where
  pruned : List PTree
  trunk? : Option PTree
deriving Repr

/-- A root-preserving cut accumulated across a list of children. -/
structure RootCutList where
  pruned : List PTree
  trunks : List PTree
deriving Repr

/-- An admissible cut of a planar rooted tree. `none` is the full cut. -/
structure Cut where
  pruned : List PTree
  trunk? : Option PTree
deriving Repr

namespace RootCut

def Perm (c d : RootCut) : Prop :=
  PTree.ForestPerm c.pruned d.pruned ∧
    RootedTree.ofPTree c.trunk = RootedTree.ofPTree d.trunk

theorem Perm.refl (c : RootCut) : Perm c c :=
  ⟨PTree.ForestPerm.refl c.pruned, rfl⟩

theorem Perm.trans {c d e : RootCut} (hcd : Perm c d) (hde : Perm d e) :
    Perm c e :=
  ⟨PTree.ForestPerm.trans hcd.1 hde.1, hcd.2.trans hde.2⟩

/-- The trunk of a root cut, only when the cut prunes no trees. -/
def noPrunedTrunk? (c : RootCut) : Option PTree :=
  match c.pruned with
  | [] => some c.trunk
  | _ :: _ => none

end RootCut

def OptionPerm : Option PTree → Option PTree → Prop
  | none, none => True
  | some t, some u => RootedTree.ofPTree t = RootedTree.ofPTree u
  | _, _ => False

theorem OptionPerm.refl : ∀ t : Option PTree, OptionPerm t t
  | none => trivial
  | some _ => rfl

theorem OptionPerm.trans {t u v : Option PTree}
    (htu : OptionPerm t u) (huv : OptionPerm u v) : OptionPerm t v := by
  cases t <;> cases u <;> cases v <;> simp [OptionPerm] at htu huv ⊢
  exact htu.trans huv

namespace ChildCut

def Perm (c d : ChildCut) : Prop :=
  PTree.ForestPerm c.pruned d.pruned ∧ OptionPerm c.trunk? d.trunk?

theorem Perm.refl (c : ChildCut) : Perm c c :=
  ⟨PTree.ForestPerm.refl c.pruned, OptionPerm.refl c.trunk?⟩

theorem Perm.trans {c d e : ChildCut} (hcd : Perm c d) (hde : Perm d e) :
    Perm c e :=
  ⟨PTree.ForestPerm.trans hcd.1 hde.1, OptionPerm.trans hcd.2 hde.2⟩

theorem Perm.cutEdge {t u : PTree} (h : PTree.Perm t u) :
    Perm { pruned := [t], trunk? := none } { pruned := [u], trunk? := none } :=
  ⟨PTree.ForestPerm.cons h (PTree.ForestPerm.refl []), trivial⟩

theorem Perm.of_rootCut {c d : RootCut} (h : RootCut.Perm c d) :
    Perm { pruned := c.pruned, trunk? := some c.trunk }
      { pruned := d.pruned, trunk? := some d.trunk } :=
  h

/-- The trunk of a child cut choice, only when the choice prunes no trees. -/
def noPrunedTrunk? (c : ChildCut) : Option PTree :=
  match c.pruned with
  | [] => c.trunk?
  | _ :: _ => none

/-- The pruned forest of a child cut choice. -/
def prunedForest (c : ChildCut) : RootedForest :=
  (c.pruned.map RootedTree.ofPTree : RootedForest)

/-- The trunk forest of a child cut choice. Cutting the edge gives the empty trunk. -/
def trunkForest (c : ChildCut) : RootedForest :=
  match c.trunk? with
  | none => 0
  | some trunk => RootedForest.singleton (RootedTree.ofPTree trunk)

/-- The coproduct term encoded by a child cut choice. -/
def coproductTerm (c : ChildCut) : RootedForest × RootedForest :=
  (c.prunedForest, c.trunkForest)

end ChildCut

namespace RootCutList

def Perm (c d : RootCutList) : Prop :=
  PTree.ForestPerm c.pruned d.pruned ∧ PTree.ForestPerm c.trunks d.trunks

theorem Perm.refl (c : RootCutList) : Perm c c :=
  ⟨PTree.ForestPerm.refl c.pruned, PTree.ForestPerm.refl c.trunks⟩

theorem Perm.trans {c d e : RootCutList} (hcd : Perm c d) (hde : Perm d e) :
    Perm c e :=
  ⟨PTree.ForestPerm.trans hcd.1 hde.1, PTree.ForestPerm.trans hcd.2 hde.2⟩

def consChild (c : ChildCut) (r : RootCutList) : RootCutList :=
  { pruned := c.pruned ++ r.pruned
    trunks :=
      match c.trunk? with
      | none => r.trunks
      | some trunk => trunk :: r.trunks }

theorem Perm.consChild {c d : ChildCut} {r s : RootCutList}
    (hc : ChildCut.Perm c d) (hr : Perm r s) :
    Perm (RootCutList.consChild c r) (RootCutList.consChild d s) := by
  rcases c with ⟨cp, ct⟩
  rcases d with ⟨dp, dt⟩
  rcases hc with ⟨hp, ht⟩
  rcases r with ⟨rp, rt⟩
  rcases s with ⟨sp, st⟩
  rcases hr with ⟨hrp, hrt⟩
  cases ct with
  | none =>
      cases dt with
      | none =>
          exact ⟨PTree.ForestPerm.append hp hrp, hrt⟩
      | some u =>
          simp [OptionPerm] at ht
  | some t =>
      cases dt with
      | none =>
          simp [OptionPerm] at ht
      | some u =>
          exact ⟨PTree.ForestPerm.append hp hrp, PTree.ForestPerm.cons_eq ht hrt⟩

theorem Perm.consChild_swap (c d : ChildCut) (r : RootCutList) :
    Perm (RootCutList.consChild c (RootCutList.consChild d r))
      (RootCutList.consChild d (RootCutList.consChild c r)) := by
  rcases c with ⟨cp, ct⟩
  rcases d with ⟨dp, dt⟩
  rcases r with ⟨rp, rt⟩
  have hp : PTree.ForestPerm (cp ++ (dp ++ rp)) (dp ++ (cp ++ rp)) := by
    apply PTree.ForestPerm.of_list_perm
    simpa [List.append_assoc] using
      List.Perm.append_right rp
        (show (cp ++ dp).Perm (dp ++ cp) from List.perm_append_comm)
  cases ct with
  | none =>
      cases dt with
      | none =>
          exact ⟨hp, PTree.ForestPerm.refl rt⟩
      | some u =>
          exact ⟨hp, PTree.ForestPerm.refl (u :: rt)⟩
  | some t =>
      cases dt with
      | none =>
          exact ⟨hp, PTree.ForestPerm.refl (t :: rt)⟩
      | some u =>
          exact ⟨hp, PTree.ForestPerm.of_list_perm (List.Perm.swap t u rt).symm⟩

theorem RootCut.Perm.of_rootCutList {c d : RootCutList} (h : Perm c d) :
    RootCut.Perm { pruned := c.pruned, trunk := .node c.trunks }
      { pruned := d.pruned, trunk := .node d.trunks } :=
  ⟨h.1, RootedForest.ofPTree_node_eq_of_forestPerm h.2⟩

theorem Perm.combine {c d : ChildCut} {r s : RootCutList}
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

/-- The trunks of a root-preserving cut list, only when the cut prunes no trees. -/
def noPrunedTrunks? (c : RootCutList) : Option (List PTree) :=
  match c.pruned with
  | [] => some c.trunks
  | _ :: _ => none

/-- The pruned forest of a root-preserving cut list. -/
def prunedForest (c : RootCutList) : RootedForest :=
  (c.pruned.map RootedTree.ofPTree : RootedForest)

/-- The trunk forest of a root-preserving cut list. -/
def trunkForest (c : RootCutList) : RootedForest :=
  (c.trunks.map RootedTree.ofPTree : RootedForest)

/-- The coproduct term encoded by a root-preserving cut list. -/
def coproductTerm (c : RootCutList) : RootedForest × RootedForest :=
  (c.prunedForest, c.trunkForest)

@[simp]
theorem prunedForest_consChild (c : ChildCut) (r : RootCutList) :
    (consChild c r).prunedForest = c.prunedForest + r.prunedForest := by
  cases c
  cases r
  simp [prunedForest, ChildCut.prunedForest, consChild, List.map_append]

@[simp]
theorem trunkForest_consChild (c : ChildCut) (r : RootCutList) :
    (consChild c r).trunkForest = c.trunkForest + r.trunkForest := by
  cases c with
  | mk pruned trunk? =>
      cases r
      cases trunk? <;> simp [trunkForest, ChildCut.trunkForest, consChild,
        RootedForest.singleton]

@[simp]
theorem coproductTerm_consChild (c : ChildCut) (r : RootCutList) :
    (consChild c r).coproductTerm =
      c.coproductTerm + r.coproductTerm := by
  simp [coproductTerm, ChildCut.coproductTerm]

end RootCutList

theorem rootCut_perm_of_rootCutList_perm {c d : RootCutList}
    (h : RootCutList.Perm c d) :
    RootCut.Perm { pruned := c.pruned, trunk := .node c.trunks }
      { pruned := d.pruned, trunk := .node d.trunks } :=
  ⟨h.1, RootedForest.ofPTree_node_eq_of_forestPerm h.2⟩

namespace Cut

def Perm (c d : Cut) : Prop :=
  PTree.ForestPerm c.pruned d.pruned ∧ OptionPerm c.trunk? d.trunk?

theorem Perm.refl (c : Cut) : Perm c c :=
  ⟨PTree.ForestPerm.refl c.pruned, OptionPerm.refl c.trunk?⟩

theorem Perm.trans {c d e : Cut} (hcd : Perm c d) (hde : Perm d e) :
    Perm c e :=
  ⟨PTree.ForestPerm.trans hcd.1 hde.1, OptionPerm.trans hcd.2 hde.2⟩

theorem Perm.full {t u : PTree} (h : PTree.Perm t u) :
    Perm { pruned := [t], trunk? := none } { pruned := [u], trunk? := none } :=
  ⟨PTree.ForestPerm.cons h (PTree.ForestPerm.refl []), trivial⟩

theorem Perm.of_rootCut {c d : RootCut} (h : RootCut.Perm c d) :
    Perm { pruned := c.pruned, trunk? := some c.trunk }
      { pruned := d.pruned, trunk? := some d.trunk } :=
  h

end Cut

namespace ListRelPerm

private theorem forall₂_ofPTree_eq_map :
    ∀ ts : List PTree,
      List.Forall₂ (fun t τ => RootedTree.ofPTree t = τ) ts (ts.map RootedTree.ofPTree)
  | [] => .nil
  | _ :: ts => .cons rfl (forall₂_ofPTree_eq_map ts)

private theorem forall₂_perm_of_forall₂_ofPTree_eq :
    ∀ {ts us : List PTree},
      List.Forall₂ (fun t τ => RootedTree.ofPTree t = τ) ts (us.map RootedTree.ofPTree) →
        List.Forall₂ PTree.Perm ts us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs =>
      .cons (RootedTree.ofPTree_eq_iff.1 h) (forall₂_perm_of_forall₂_ofPTree_eq hs)

theorem of_forestPerm {ts us : List PTree} (h : PTree.ForestPerm ts us) :
    ListRelPerm PTree.Perm ts us := by
  have hp : (ts.map RootedTree.ofPTree).Perm (us.map RootedTree.ofPTree) :=
    Quotient.exact h
  obtain ⟨ts', hts', hrel⟩ :=
    PTree.forall2_perm_right (R := fun t τ => RootedTree.ofPTree t = τ) hp
      (forall₂_ofPTree_eq_map ts)
  exact ⟨ts', hts', forall₂_perm_of_forall₂_ofPTree_eq hrel⟩

end ListRelPerm

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

mutual

/-- Admissible cuts which keep the root component. -/
def rootCuts : PTree → List RootCut
  | .node ts => (rootCutsList ts).map fun c =>
      { pruned := c.pruned, trunk := .node c.trunks }

/-- Choices for a child: cut the edge above it, or keep it with a root-preserving cut. -/
def childCuts (t : PTree) : List ChildCut :=
  { pruned := [t], trunk? := none } ::
    (rootCuts t).map fun c => { pruned := c.pruned, trunk? := some c.trunk }

/-- Combine child cut choices into root-preserving cuts. -/
def rootCutsList : List PTree → List RootCutList
  | [] => [{ pruned := [], trunks := [] }]
  | t :: ts =>
      (childCuts t).flatMap fun c =>
        (rootCutsList ts).map fun rest =>
          RootCutList.consChild c rest

end

theorem rootCuts_node_listRelPerm_of_rootCutsList
    {ts us : List PTree}
    (h : ListRelPerm RootCutList.Perm (rootCutsList ts) (rootCutsList us)) :
    ListRelPerm RootCut.Perm (rootCuts (.node ts)) (rootCuts (.node us)) := by
  simpa [rootCuts] using
    ListRelPerm.map (fun h => rootCut_perm_of_rootCutList_perm h) h

theorem childCuts_listRelPerm_of_perm {t u : PTree} (htu : PTree.Perm t u)
    (hroot : ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) :
    ListRelPerm ChildCut.Perm (childCuts t) (childCuts u) := by
  rw [childCuts, childCuts]
  exact ListRelPerm.cons (ChildCut.Perm.cutEdge htu)
    (ListRelPerm.map (fun h => ChildCut.Perm.of_rootCut h) hroot)

theorem rootCutsList_cons_listRelPerm {t u : PTree} {ts us : List PTree}
    (hchild : ListRelPerm ChildCut.Perm (childCuts t) (childCuts u))
    (htail : ListRelPerm RootCutList.Perm (rootCutsList ts) (rootCutsList us)) :
    ListRelPerm RootCutList.Perm (rootCutsList (t :: ts)) (rootCutsList (u :: us)) := by
  rw [rootCutsList, rootCutsList]
  exact ListRelPerm.flatMap
    (fun hcut =>
      ListRelPerm.map (fun hrest => RootCutList.Perm.consChild hcut hrest) htail)
    hchild

theorem rootCutsList_cons_cons_listRelPerm_swap (t u : PTree) (ts : List PTree) :
    ListRelPerm RootCutList.Perm (rootCutsList (t :: u :: ts))
      (rootCutsList (u :: t :: ts)) := by
  rw [rootCutsList, rootCutsList, rootCutsList, rootCutsList]
  simp only [List.map_flatMap, List.map_map]
  change ListRelPerm RootCutList.Perm
    ((childCuts t).flatMap fun c =>
      (childCuts u).flatMap fun d =>
        (rootCutsList ts).map fun r =>
          RootCutList.consChild c (RootCutList.consChild d r))
    ((childCuts u).flatMap fun d =>
      (childCuts t).flatMap fun c =>
        (rootCutsList ts).map fun r =>
          RootCutList.consChild d (RootCutList.consChild c r))
  refine ListRelPerm.perm_left
    (flatMap₂_perm (childCuts t) (childCuts u)
      (fun c d =>
        (rootCutsList ts).map fun r =>
          RootCutList.consChild c (RootCutList.consChild d r))) ?_
  exact ListRelPerm.flatMap
    (fun {d d'} hd =>
      ListRelPerm.flatMap
        (fun {c c'} hc =>
          ListRelPerm.map
            (fun {r s} hr =>
              RootCutList.Perm.trans (RootCutList.Perm.consChild_swap c d r)
                (RootCutList.Perm.consChild hd (RootCutList.Perm.consChild hc hr)))
            (ListRelPerm.refl RootCutList.Perm.refl (rootCutsList ts)))
        (ListRelPerm.refl ChildCut.Perm.refl (childCuts t)))
    (ListRelPerm.refl ChildCut.Perm.refl (childCuts u))

theorem rootCutsList_listRelPerm_of_perm {ts us : List PTree} (h : ts.Perm us) :
    ListRelPerm RootCutList.Perm (rootCutsList ts) (rootCutsList us) := by
  induction h with
  | nil =>
      exact ListRelPerm.refl RootCutList.Perm.refl (rootCutsList [])
  | cons t _ ih =>
      exact rootCutsList_cons_listRelPerm
        (ListRelPerm.refl ChildCut.Perm.refl (childCuts t)) ih
  | swap t u ts =>
      exact rootCutsList_cons_cons_listRelPerm_swap u t ts
  | trans _ _ ih₁ ih₂ =>
      exact ListRelPerm.trans (R := RootCutList.Perm)
        (fun {x y z} => RootCutList.Perm.trans) ih₁ ih₂

theorem rootCutsList_listRelPerm_of_forall₂_childCuts :
    ∀ {ts us : List PTree},
      List.Forall₂
          (fun t u => ListRelPerm ChildCut.Perm (childCuts t) (childCuts u)) ts us →
        ListRelPerm RootCutList.Perm (rootCutsList ts) (rootCutsList us)
  | [], [], .nil => by
      rw [rootCutsList.eq_def]
      exact ListRelPerm.of_forall₂ (.cons (RootCutList.Perm.refl _) .nil)
  | _ :: _, _ :: _, .cons hchild htail =>
      rootCutsList_cons_listRelPerm hchild
        (rootCutsList_listRelPerm_of_forall₂_childCuts htail)

theorem rootCutsList_listRelPerm_of_forall₂_perm_rootCuts :
    ∀ {ts us : List PTree},
      List.Forall₂
          (fun t u =>
            PTree.Perm t u ∧ ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) ts us →
        ListRelPerm RootCutList.Perm (rootCutsList ts) (rootCutsList us)
  | [], [], .nil => by
      rw [rootCutsList.eq_def]
      exact ListRelPerm.of_forall₂ (.cons (RootCutList.Perm.refl _) .nil)
  | _ :: _, _ :: _, .cons h htail =>
      rootCutsList_cons_listRelPerm (childCuts_listRelPerm_of_perm h.1 h.2)
        (rootCutsList_listRelPerm_of_forall₂_perm_rootCuts htail)

theorem rootCuts_node_listRelPerm_of_forall₂_perm_rootCuts
    {ts us : List PTree}
    (h :
      List.Forall₂
        (fun t u =>
          PTree.Perm t u ∧ ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) ts us) :
    ListRelPerm RootCut.Perm (rootCuts (.node ts)) (rootCuts (.node us)) :=
  rootCuts_node_listRelPerm_of_rootCutsList
    (rootCutsList_listRelPerm_of_forall₂_perm_rootCuts h)

mutual

theorem rootCuts_listRelPerm_of_perm :
    ∀ {t u : PTree}, PTree.Perm t u →
      ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)
  | .node ts, .node us, PTree.Perm.node (ts1' := ts') hp hf => by
      have hleft :
          ListRelPerm RootCut.Perm (rootCuts (.node ts)) (rootCuts (.node ts')) :=
        rootCuts_node_listRelPerm_of_rootCutsList (rootCutsList_listRelPerm_of_perm hp)
      have hright :
          ListRelPerm RootCut.Perm (rootCuts (.node ts')) (rootCuts (.node us)) :=
        rootCuts_node_listRelPerm_of_forall₂_perm_rootCuts
          (forall₂_perm_rootCuts_of_forall₂_perm hf)
      exact ListRelPerm.trans (R := RootCut.Perm)
        (fun {x y z} => RootCut.Perm.trans) hleft hright

theorem forall₂_perm_rootCuts_of_forall₂_perm :
    ∀ {ts us : List PTree}, List.Forall₂ PTree.Perm ts us →
      List.Forall₂
        (fun t u =>
          PTree.Perm t u ∧ ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) ts us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h htail =>
      .cons ⟨h, rootCuts_listRelPerm_of_perm h⟩
        (forall₂_perm_rootCuts_of_forall₂_perm htail)

end

private theorem filterMap_rootCutList_noPrunedTrunks_map {α : Type}
    (f : List PTree → α) :
    ∀ cuts : List RootCutList,
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

private theorem flatMap_rootCut_noPrunedTrunk_singleton {α : Type}
    (f : PTree → α) :
    ∀ cuts : List RootCut,
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

/-- A root-preserving cut with no pruned trees is the no-cut root cut. -/
theorem rootCuts_pruned_eq_nil :
    ∀ {t : PTree} {c : RootCut}, c ∈ rootCuts t → c.pruned = [] → c.trunk = t
  | .node ts, c, hc, hpruned => by
      simp [rootCuts] at hc
      obtain ⟨cl, hcl, rfl⟩ := hc
      have htrunks := rootCutsList_pruned_eq_nil hcl hpruned
      simp [htrunks]

/-- A child cut choice with no pruned trees keeps the whole child tree. -/
theorem childCuts_pruned_eq_nil :
    ∀ {t : PTree} {c : ChildCut}, c ∈ childCuts t → c.pruned = [] → c.trunk? = some t
  | t, c, hc, hpruned => by
      simp [childCuts] at hc
      rcases hc with hc | hc
      · subst c
        simp at hpruned
      · obtain ⟨rc, hrc, rfl⟩ := hc
        exact congrArg some (rootCuts_pruned_eq_nil hrc hpruned)

/-- A root-preserving cut list with no pruned trees keeps every child tree. -/
theorem rootCutsList_pruned_eq_nil :
    ∀ {ts : List PTree} {c : RootCutList}, c ∈ rootCutsList ts → c.pruned = [] →
      c.trunks = ts
  | [], c, hc, hpruned => by
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
                simp [RootCutList.consChild, hccp, hrp] at hpruned
        | cons p ps =>
            simp [RootCutList.consChild, hccp] at hpruned
      have hcc_trunk := childCuts_pruned_eq_nil hcc hparts.1
      have hrest_trunks := rootCutsList_pruned_eq_nil hrest hparts.2
      simp [RootCutList.consChild, hcc_trunk, hrest_trunks]

end

mutual

/-- Exactly one root-preserving cut of a tree prunes no trees: the no-cut cut. -/
theorem rootCuts_noPrunedTrunks :
    ∀ t : PTree, (rootCuts t).filterMap RootCut.noPrunedTrunk? = [t]
  | .node ts => by
      rw [rootCuts]
      simp only [List.filterMap_map]
      have h := filterMap_rootCutList_noPrunedTrunks_map PTree.node (rootCutsList ts)
      rw [rootCutsList_noPrunedTrunks] at h
      simpa [Function.comp_def, RootCut.noPrunedTrunk?, RootCutList.noPrunedTrunks?] using h

/-- Exactly one child cut choice prunes no trees: the choice keeping the whole child. -/
theorem childCuts_noPrunedTrunks (t : PTree) :
    (childCuts t).filterMap ChildCut.noPrunedTrunk? = [t] := by
  rw [childCuts]
  simp only [List.filterMap_cons, ChildCut.noPrunedTrunk?, List.filterMap_map]
  change (rootCuts t).filterMap RootCut.noPrunedTrunk? = [t]
  exact rootCuts_noPrunedTrunks t

/-- Exactly one root-preserving cut list prunes no trees: the no-cut list. -/
theorem rootCutsList_noPrunedTrunks :
    ∀ ts : List PTree, (rootCutsList ts).filterMap RootCutList.noPrunedTrunks? = [ts]
  | [] => by
      simp [rootCutsList, RootCutList.noPrunedTrunks?]
  | t :: ts => by
      rw [rootCutsList]
      rw [childCuts]
      simp only [List.flatMap_cons, List.flatMap_map]
      have hinner :
          ∀ c : RootCut,
            (List.map
                (fun rest : RootCutList =>
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
            (fun rest : RootCutList =>
              { pruned := [t] ++ rest.pruned,
                trunks := rest.trunks })
            (rootCutsList ts)).filterMap RootCutList.noPrunedTrunks? ++
          List.flatMap
            (fun c : RootCut =>
              (List.map
                (fun rest : RootCutList =>
                  { pruned := c.pruned ++ rest.pruned,
                    trunks := c.trunk :: rest.trunks })
                (rootCutsList ts)).filterMap RootCutList.noPrunedTrunks?)
            (rootCuts t) = [t :: ts]
      rw [show
          (List.map
              (fun rest : RootCutList =>
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

/-- Root-preserving cuts conserve the order of a tree. -/
theorem rootCuts_order :
    ∀ {t : PTree} {c : RootCut}, c ∈ rootCuts t →
      orderList c.pruned + order c.trunk = order t
  | .node ts, c, hc => by
      simp [rootCuts] at hc
      obtain ⟨cl, hcl, rfl⟩ := hc
      have hcl_order := rootCutsList_order hcl
      simp
      omega

/-- Child cut choices conserve the order of the child tree. -/
theorem childCuts_order :
    ∀ {t : PTree} {c : ChildCut}, c ∈ childCuts t →
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

/-- Combined child cuts conserve the total order of a list of children. -/
theorem rootCutsList_order :
    ∀ {ts : List PTree} {c : RootCutList}, c ∈ rootCutsList ts →
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
          simp [RootCutList.consChild, hcct]
          omega
      | some trunk =>
          simp [hcct] at hcc_order
          simp [RootCutList.consChild, hcct]
          omega

end

/-- All admissible cuts, including the full cut. -/
def cuts (t : PTree) : List Cut :=
  (rootCuts t).map (fun c => { pruned := c.pruned, trunk? := some c.trunk }) ++
    [{ pruned := [t], trunk? := none }]

theorem cuts_listRelPerm_of_rootCuts {t u : PTree} (htu : PTree.Perm t u)
    (hroot : ListRelPerm RootCut.Perm (rootCuts t) (rootCuts u)) :
    ListRelPerm Cut.Perm (cuts t) (cuts u) := by
  rw [cuts, cuts]
  exact ListRelPerm.append
    (ListRelPerm.map (fun h => Cut.Perm.of_rootCut h) hroot)
    (ListRelPerm.of_forall₂ (.cons (Cut.Perm.full htu) .nil))

theorem cuts_listRelPerm_of_perm {t u : PTree} (h : PTree.Perm t u) :
    ListRelPerm Cut.Perm (cuts t) (cuts u) :=
  cuts_listRelPerm_of_rootCuts h (rootCuts_listRelPerm_of_perm h)

namespace Cut

/-- The pruned branches of a cut, as a non-planar rooted forest. -/
def prunedForest (c : Cut) : RootedForest :=
  (c.pruned.map RootedTree.ofPTree : RootedForest)

/-- The trunk of a cut, using the adjoined empty tree for the full cut. -/
def trunkIndex (c : Cut) : TreeIndex :=
  match c.trunk? with
  | none => .empty
  | some t => .tree (RootedTree.ofPTree t)

/-- The trunk of a cut, as a rooted forest. The full cut has empty trunk forest. -/
def trunkForest (c : Cut) : RootedForest :=
  match c.trunk? with
  | none => 0
  | some t => RootedForest.singleton (RootedTree.ofPTree t)

theorem Perm.prunedForest_eq {c d : Cut} (h : Perm c d) :
    c.prunedForest = d.prunedForest :=
  h.1

theorem Perm.trunkForest_eq {c d : Cut} (h : Perm c d) :
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
          simpa [trunkForest] using congrArg RootedForest.singleton ht

theorem Perm.coproductTerm_eq {c d : Cut} (h : Perm c d) :
    (c.prunedForest, c.trunkForest) = (d.prunedForest, d.trunkForest) := by
  simp [h.prunedForest_eq, h.trunkForest_eq]

@[simp]
theorem order_trunkForest (c : Cut) :
    RootedForest.order c.trunkForest = TreeIndex.order c.trunkIndex := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? <;> simp [trunkForest, trunkIndex]

end Cut

/-- Every admissible cut conserves total order between the pruned forest and trunk. -/
theorem cuts_order {t : PTree} {c : Cut} (hc : c ∈ cuts t) :
    RootedForest.order c.prunedForest + TreeIndex.order c.trunkIndex = order t := by
  simp [cuts] at hc
  rcases hc with hc | hc
  · obtain ⟨rc, hrc, rfl⟩ := hc
    simpa [Cut.prunedForest, Cut.trunkIndex] using rootCuts_order hrc
  · subst c
    simpa [Cut.prunedForest, Cut.trunkIndex] using RootedForest.order_ofPTree_list [t]

/-- The terms `(P^c(t), R^c(t))` appearing in the BCK coproduct of a planar tree. -/
def cutTerms (t : PTree) : List (RootedForest × TreeIndex) :=
  (cuts t).map fun c => (c.prunedForest, c.trunkIndex)

/-- The terms `P^c(t) ⊗ R^c(t)` appearing in the BCK coproduct of a planar tree. -/
def coproductTerms (t : PTree) : List (RootedForest × RootedForest) :=
  (cuts t).map fun c => (c.prunedForest, c.trunkForest)

/-- Keep exactly the coproduct terms whose left tensor factor is empty. -/
def leftBoundaryCoproductTerm? (term : RootedForest × RootedForest) :
    Option (RootedForest × RootedForest) :=
  if RootedForest.order term.1 = 0 then some term else none

/-- Keep exactly the coproduct terms whose right tensor factor is empty. -/
def rightBoundaryCoproductTerm? (term : RootedForest × RootedForest) :
    Option (RootedForest × RootedForest) :=
  if RootedForest.order term.2 = 0 then some term else none

/-- Every cut term conserves total order between the pruned forest and trunk. -/
theorem cutTerms_order {t : PTree} {term : RootedForest × TreeIndex}
    (hterm : term ∈ cutTerms t) :
    RootedForest.order term.1 + TreeIndex.order term.2 = order t := by
  simp [cutTerms] at hterm
  obtain ⟨c, hc, hterm⟩ := hterm
  subst term
  exact cuts_order hc

/-- Every coproduct term conserves total order between the two tensor factors. -/
theorem coproductTerms_order {t : PTree} {term : RootedForest × RootedForest}
    (hterm : term ∈ coproductTerms t) :
    RootedForest.order term.1 + RootedForest.order term.2 = order t := by
  simp [coproductTerms] at hterm
  obtain ⟨c, hc, hterm⟩ := hterm
  subst term
  simpa using cuts_order hc

private theorem ofPTree_list_eq_zero_iff (ts : List PTree) :
    ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) = 0 ↔ ts = [] := by
  constructor
  · intro h
    have horder :
        PTree.orderList ts = 0 := by
      have horder' := congrArg RootedForest.order h
      simpa [RootedForest.order_ofPTree_list] using horder'
    exact (PTree.orderList_eq_zero_iff ts).1 horder
  · intro h
    subst ts
    simp

private theorem rootedForest_add_eq_zero_left {φ ψ : RootedForest} (h : φ + ψ = 0) :
    φ = 0 := by
  have horder : RootedForest.order (φ + ψ) = 0 := by
    rw [h]
    simp
  rw [RootedForest.order_add] at horder
  have hφ : RootedForest.order φ = 0 := by omega
  exact (RootedForest.order_eq_zero_iff φ).1 hφ

private theorem rootedForest_add_eq_zero_right {φ ψ : RootedForest} (h : φ + ψ = 0) :
    ψ = 0 := by
  have horder : RootedForest.order (φ + ψ) = 0 := by
    rw [h]
    simp
  rw [RootedForest.order_add] at horder
  have hψ : RootedForest.order ψ = 0 := by omega
  exact (RootedForest.order_eq_zero_iff ψ).1 hψ

/-- The only coproduct term of a tree with empty left factor is `1 ⊗ t`. -/
theorem coproductTerms_left_eq_zero {t : PTree} {term : RootedForest × RootedForest}
    (hterm : term ∈ coproductTerms t) (hleft : term.1 = 0) :
    term.2 = RootedForest.singleton (RootedTree.ofPTree t) := by
  simp [coproductTerms] at hterm
  obtain ⟨c, hc, hterm⟩ := hterm
  subst term
  simp [cuts] at hc
  rcases hc with hc | hc
  · obtain ⟨rc, hrc, hcut⟩ := hc
    subst c
    have hpruned : rc.pruned = [] :=
      (ofPTree_list_eq_zero_iff rc.pruned).1 hleft
    have htrunk := rootCuts_pruned_eq_nil hrc hpruned
    simp [Cut.trunkForest, htrunk]
  · subst c
    exact False.elim
      (RootedForest.singleton_ne_zero (RootedTree.ofPTree t) hleft)

/-- The only coproduct term of a tree with empty right factor is `t ⊗ 1`. -/
theorem coproductTerms_right_eq_zero {t : PTree} {term : RootedForest × RootedForest}
    (hterm : term ∈ coproductTerms t) (hright : term.2 = 0) :
    term.1 = RootedForest.singleton (RootedTree.ofPTree t) := by
  simp [coproductTerms] at hterm
  obtain ⟨c, hc, hterm⟩ := hterm
  subst term
  simp [cuts] at hc
  rcases hc with hc | hc
  · obtain ⟨rc, hrc, hcut⟩ := hc
    subst c
    have hright' : RootedForest.singleton (RootedTree.ofPTree rc.trunk) = 0 := by
      simpa [Cut.trunkForest] using hright
    exact False.elim
      (RootedForest.singleton_ne_zero (RootedTree.ofPTree rc.trunk) hright')
  · subst c
    simp [Cut.prunedForest, RootedForest.singleton]

private theorem filterMap_rootCut_noPrunedBoundary (t : PTree) :
    (rootCuts t).filterMap
        (fun c => (RootCut.noPrunedTrunk? c).map fun u =>
          ((0 : RootedForest), RootedForest.singleton (RootedTree.ofPTree u))) =
      [((0 : RootedForest), RootedForest.singleton (RootedTree.ofPTree t))] := by
  rw [show (rootCuts t).filterMap
        (fun c => (RootCut.noPrunedTrunk? c).map fun u =>
          ((0 : RootedForest), RootedForest.singleton (RootedTree.ofPTree u))) =
      ((rootCuts t).filterMap RootCut.noPrunedTrunk?).map fun u =>
        ((0 : RootedForest), RootedForest.singleton (RootedTree.ofPTree u)) by
    induction rootCuts t with
    | nil => rfl
    | cons c cs ih =>
        cases h : RootCut.noPrunedTrunk? c <;> simp [List.filterMap, h, ih]]
  rw [rootCuts_noPrunedTrunks]
  rfl

/-- A tree coproduct has exactly one term with empty left factor, namely `1 ⊗ t`. -/
theorem coproductTerms_leftBoundaryCoproductTerm (t : PTree) :
    (coproductTerms t).filterMap leftBoundaryCoproductTerm? =
      [(0, RootedForest.singleton (RootedTree.ofPTree t))] := by
  rw [coproductTerms, cuts]
  simp only [List.map_append, List.map_map, List.filterMap_append, Function.comp_def]
  rw [show ((rootCuts t).map fun c =>
        (({ pruned := c.pruned, trunk? := some c.trunk } : Cut).prunedForest,
          ({ pruned := c.pruned, trunk? := some c.trunk } : Cut).trunkForest)).filterMap
        leftBoundaryCoproductTerm? =
      (rootCuts t).filterMap
        (fun c => (RootCut.noPrunedTrunk? c).map fun u =>
          ((0 : RootedForest), RootedForest.singleton (RootedTree.ofPTree u))) by
    induction rootCuts t with
    | nil => rfl
    | cons c cs ih =>
        rw [List.map_cons, List.filterMap_cons, ih]
        cases hc : c.pruned with
        | nil =>
            simp [leftBoundaryCoproductTerm?, RootCut.noPrunedTrunk?,
              Cut.prunedForest, Cut.trunkForest, hc]
        | cons p ps =>
            have horder : RootedForest.order
                ((c.pruned.map RootedTree.ofPTree : List RootedTree) :
                  RootedForest) ≠ 0 := by
              intro hzero
              have hnil : c.pruned = [] := by
                exact (ofPTree_list_eq_zero_iff c.pruned).1
                  ((RootedForest.order_eq_zero_iff _).1 hzero)
              simp [hc] at hnil
            simp [leftBoundaryCoproductTerm?, RootCut.noPrunedTrunk?,
              Cut.prunedForest, hc]]
  calc
    ((rootCuts t).filterMap
        (fun c => (RootCut.noPrunedTrunk? c).map fun u =>
          ((0 : RootedForest), RootedForest.singleton (RootedTree.ofPTree u)))) ++
        (List.map (fun c : Cut => (c.prunedForest, c.trunkForest))
          ([{ pruned := [t], trunk? := none }] : List Cut)).filterMap
            leftBoundaryCoproductTerm? =
      [(0, RootedForest.singleton (RootedTree.ofPTree t))] ++
        (List.map (fun c : Cut => (c.prunedForest, c.trunkForest))
          ([{ pruned := [t], trunk? := none }] : List Cut)).filterMap
            leftBoundaryCoproductTerm? := by
        exact congrArg
          (fun xs => xs ++
            (List.map (fun c : Cut => (c.prunedForest, c.trunkForest))
              ([{ pruned := [t], trunk? := none }] : List Cut)).filterMap
                leftBoundaryCoproductTerm?)
          (filterMap_rootCut_noPrunedBoundary t)
    _ = [(0, RootedForest.singleton (RootedTree.ofPTree t))] := by
      simp [leftBoundaryCoproductTerm?, Cut.prunedForest, Cut.trunkForest]

/-- A tree coproduct has exactly one term with empty right factor, namely `t ⊗ 1`. -/
theorem coproductTerms_rightBoundaryCoproductTerm (t : PTree) :
    (coproductTerms t).filterMap rightBoundaryCoproductTerm? =
      [(RootedForest.singleton (RootedTree.ofPTree t), 0)] := by
  rw [coproductTerms, cuts]
  simp only [List.map_append, List.map_map, List.filterMap_append, Function.comp_def]
  have hroot :
      ((rootCuts t).map fun c =>
        (({ pruned := c.pruned, trunk? := some c.trunk } : Cut).prunedForest,
          ({ pruned := c.pruned, trunk? := some c.trunk } : Cut).trunkForest)).filterMap
          rightBoundaryCoproductTerm? = [] := by
    induction rootCuts t with
    | nil => rfl
    | cons c cs ih =>
        rw [List.map_cons, List.filterMap_cons, ih]
        have horder : PTree.order c.trunk ≠ 0 :=
          Nat.ne_of_gt (PTree.order_pos c.trunk)
        simp [rightBoundaryCoproductTerm?, Cut.trunkForest, horder]
  rw [hroot]
  simp [rightBoundaryCoproductTerm?, Cut.prunedForest, Cut.trunkForest,
    RootedForest.singleton]

theorem coproductTerms_perm_of_cuts_listRelPerm {t u : PTree}
    (h : ListRelPerm Cut.Perm (cuts t) (cuts u)) :
    (coproductTerms t).Perm (coproductTerms u) := by
  rw [coproductTerms, coproductTerms]
  exact ListRelPerm.perm_of_eq
    (ListRelPerm.map (fun hcut => Cut.Perm.coproductTerm_eq hcut) h)

theorem coproductTerms_perm {t u : PTree} (h : PTree.Perm t u) :
    (coproductTerms t).Perm (coproductTerms u) :=
  coproductTerms_perm_of_cuts_listRelPerm (cuts_listRelPerm_of_perm h)

private theorem cons_perm_append_singleton {α : Type _} (x : α) :
    ∀ xs : List α, (x :: xs).Perm (xs ++ [x])
  | [] => by simp
  | y :: ys => by
      exact (List.Perm.swap x y ys).symm.trans
        ((cons_perm_append_singleton x ys).cons y)

theorem childCuts_coproductTerms_perm (t : PTree) :
    ((childCuts t).map ChildCut.coproductTerm).Perm (coproductTerms t) := by
  rw [childCuts, coproductTerms, cuts]
  simp only [List.map_cons, List.map_append, List.map_map, Function.comp_def,
    ChildCut.coproductTerm, ChildCut.prunedForest, ChildCut.trunkForest,
    Cut.prunedForest, Cut.trunkForest]
  exact cons_perm_append_singleton
    ((([t].map RootedTree.ofPTree : List RootedTree) : RootedForest), 0)
    ((rootCuts t).map fun c =>
      (((c.pruned.map RootedTree.ofPTree : List RootedTree) : RootedForest),
        RootedForest.singleton (RootedTree.ofPTree c.trunk)))

/-- The proper BCK coproduct terms, excluding the two counit terms. -/
def properCoproductTerms (t : PTree) : List (RootedForest × RootedForest) :=
  (coproductTerms t).filter fun term =>
    0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2

theorem properCoproductTerms_perm {t u : PTree} (h : PTree.Perm t u) :
    (properCoproductTerms t).Perm (properCoproductTerms u) :=
  List.Perm.filter _ (coproductTerms_perm h)

theorem properCoproductTerms_mem_coproductTerms {t : PTree}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTerms t) :
    term ∈ coproductTerms t :=
  (List.mem_filter.1 hterm).1

theorem properCoproductTerms_order {t : PTree} {term : RootedForest × RootedForest}
    (hterm : term ∈ properCoproductTerms t) :
    RootedForest.order term.1 + RootedForest.order term.2 = order t :=
  coproductTerms_order (properCoproductTerms_mem_coproductTerms hterm)

theorem properCoproductTerms_left_order_lt {t : PTree}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTerms t) :
    RootedForest.order term.1 < order t := by
  have hproper :
      0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hright_pos : 0 < RootedForest.order term.2 := hproper.2
  have horder := properCoproductTerms_order hterm
  omega

theorem properCoproductTerms_right_order_lt {t : PTree}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTerms t) :
    RootedForest.order term.2 < order t := by
  have hproper :
      0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hleft_pos : 0 < RootedForest.order term.1 := hproper.1
  have horder := properCoproductTerms_order hterm
  omega

/-- Multiply two finite lists of coproduct basis terms. -/
def multiplyCoproductTerms
    (xs ys : List (RootedForest × RootedForest)) : List (RootedForest × RootedForest) :=
  xs.flatMap fun x =>
    ys.map fun y => (x.1 + y.1, x.2 + y.2)

private theorem pair_add_eq (x y : RootedForest × RootedForest) :
    x + y = (x.1 + y.1, x.2 + y.2) := by
  cases x
  cases y
  rfl

private theorem filterMap_map_add_leftBoundaryCoproductTerm
    (x : RootedForest × RootedForest) :
    ∀ ys : List (RootedForest × RootedForest),
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
      by_cases hx : RootedForest.order x.1 = 0
      · by_cases hy : RootedForest.order y.1 = 0
        · have hxy : RootedForest.order (x.1 + y.1) = 0 := by
            rw [RootedForest.order_add, hx, hy]
          simpa [leftBoundaryCoproductTerm?, hx, hy, hxy] using
            (show (x.1 + y.1, x.2 + y.2) = x + y by
              cases x
              cases y
              rfl)
        · have hxy : RootedForest.order (x.1 + y.1) ≠ 0 := by
            intro hzero
            rw [RootedForest.order_add, hx] at hzero
            exact hy (by simpa using hzero)
          simp [leftBoundaryCoproductTerm?, hx, hy]
      · have hxy : RootedForest.order (x.1 + y.1) ≠ 0 := by
          intro hzero
          rw [RootedForest.order_add] at hzero
          have hxzero : RootedForest.order x.1 = 0 := by omega
          exact hx hxzero
        simp [leftBoundaryCoproductTerm?, hx]

private theorem filterMap_multiply_leftBoundaryCoproductTerm
    (xs ys : List (RootedForest × RootedForest)) :
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
    (x : RootedForest × RootedForest) :
    ∀ ys : List (RootedForest × RootedForest),
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
      by_cases hx : RootedForest.order x.2 = 0
      · by_cases hy : RootedForest.order y.2 = 0
        · have hxy : RootedForest.order (x.2 + y.2) = 0 := by
            rw [RootedForest.order_add, hx, hy]
          simpa [rightBoundaryCoproductTerm?, hx, hy, hxy] using
            (show (x.1 + y.1, x.2 + y.2) = x + y by
              cases x
              cases y
              rfl)
        · have hxy : RootedForest.order (x.2 + y.2) ≠ 0 := by
            intro hzero
            rw [RootedForest.order_add, hx] at hzero
            exact hy (by simpa using hzero)
          simp [rightBoundaryCoproductTerm?, hx, hy]
      · have hxy : RootedForest.order (x.2 + y.2) ≠ 0 := by
          intro hzero
          rw [RootedForest.order_add] at hzero
          have hxzero : RootedForest.order x.2 = 0 := by omega
          exact hx hxzero
        simp [rightBoundaryCoproductTerm?, hx]

private theorem filterMap_multiply_rightBoundaryCoproductTerm
    (xs ys : List (RootedForest × RootedForest)) :
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

/-- Multiplicative extension of coproduct terms to planar forests. -/
def coproductTermsList : List PTree → List (RootedForest × RootedForest)
  | [] => [(0, 0)]
  | t :: ts => multiplyCoproductTerms (coproductTerms t) (coproductTermsList ts)

theorem multiplyCoproductTerms_perm_left
    {xs ys zs : List (RootedForest × RootedForest)} (h : xs.Perm ys) :
    (multiplyCoproductTerms xs zs).Perm (multiplyCoproductTerms ys zs) := by
  rw [multiplyCoproductTerms, multiplyCoproductTerms]
  exact List.Perm.flatMap h (fun _ _ => List.Perm.refl _)

theorem multiplyCoproductTerms_perm_right
    {xs ys zs : List (RootedForest × RootedForest)} (h : ys.Perm zs) :
    (multiplyCoproductTerms xs ys).Perm (multiplyCoproductTerms xs zs) := by
  rw [multiplyCoproductTerms, multiplyCoproductTerms]
  exact List.Perm.flatMap (List.Perm.refl xs)
    (fun x _ => List.Perm.map (fun y => (x.1 + y.1, x.2 + y.2)) h)

theorem multiplyCoproductTerms_perm
    {xs xs' ys ys' : List (RootedForest × RootedForest)}
    (hxs : xs.Perm xs') (hys : ys.Perm ys') :
    (multiplyCoproductTerms xs ys).Perm (multiplyCoproductTerms xs' ys') :=
  (multiplyCoproductTerms_perm_left (zs := ys) hxs).trans
    (multiplyCoproductTerms_perm_right (xs := xs') hys)

theorem coproductTermsList_perm_rootCutsList :
    ∀ ts : List PTree,
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

theorem coproductTerms_node_perm (ts : List PTree) :
    (coproductTerms (.node ts)).Perm
      (((coproductTermsList ts).map fun term =>
          (term.1, RootedForest.singleton (RootedForest.graft term.2))) ++
        [(RootedForest.singleton (RootedTree.ofPTree (.node ts)), 0)]) := by
  have hroot :
      ((coproductTermsList ts).map fun term =>
          (term.1, RootedForest.singleton (RootedForest.graft term.2))).Perm
        ((rootCutsList ts).map fun c =>
          (((c.pruned.map RootedTree.ofPTree : List RootedTree) : RootedForest),
            RootedForest.singleton (RootedTree.ofPTree (.node c.trunks)))) := by
    have h := (coproductTermsList_perm_rootCutsList ts).map
      (fun term => (term.1, RootedForest.singleton (RootedForest.graft term.2)))
    have hmap :
        ((rootCutsList ts).map
            (((fun term =>
              (term.1, RootedForest.singleton (RootedForest.graft term.2))) ∘
                RootCutList.coproductTerm))) =
          ((rootCutsList ts).map fun c =>
            (((c.pruned.map RootedTree.ofPTree : List RootedTree) : RootedForest),
              RootedForest.singleton (RootedTree.ofPTree (.node c.trunks)))) := by
      apply List.map_congr_left
      intro c _
      have hgraft :
          RootedForest.graft c.trunkForest = RootedTree.ofPTree (.node c.trunks) := by
        simpa [RootCutList.trunkForest] using RootedForest.graft_ofPTree_list c.trunks
      change
        (c.prunedForest, RootedForest.singleton (RootedForest.graft c.trunkForest)) =
          (((c.pruned.map RootedTree.ofPTree : List RootedTree) : RootedForest),
            RootedForest.singleton (RootedTree.ofPTree (.node c.trunks)))
      rw [hgraft]
      simp [RootCutList.prunedForest]
    simpa [hmap] using h
  rw [coproductTerms, cuts, rootCuts]
  simp only [List.map_append, List.map_map, Function.comp_def]
  exact (hroot.symm.append_right
    [(RootedForest.singleton (RootedTree.ofPTree (.node ts)), 0)]).trans (by simp)

theorem multiplyCoproductTerms_comm {xs ys : List (RootedForest × RootedForest)} :
    (multiplyCoproductTerms xs ys).Perm (multiplyCoproductTerms ys xs) := by
  rw [multiplyCoproductTerms, multiplyCoproductTerms]
  exact flatMap_map_swap
    (fun x y : RootedForest × RootedForest => (x.1 + y.1, x.2 + y.2))
    (fun y x : RootedForest × RootedForest => (y.1 + x.1, y.2 + x.2))
    (by intro x y; simp [add_comm]) xs ys

theorem multiplyCoproductTerms_assoc {xs ys zs : List (RootedForest × RootedForest)} :
    (multiplyCoproductTerms xs (multiplyCoproductTerms ys zs)).Perm
      (multiplyCoproductTerms (multiplyCoproductTerms xs ys) zs) := by
  simp [multiplyCoproductTerms, List.flatMap_assoc, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, add_assoc]

theorem coproductTermsList_append_perm (ts us : List PTree) :
    (coproductTermsList (ts ++ us)).Perm
      (multiplyCoproductTerms (coproductTermsList ts) (coproductTermsList us)) := by
  induction ts with
  | nil =>
      simp [coproductTermsList, multiplyCoproductTerms]
  | cons t ts ih =>
      rw [List.cons_append, coproductTermsList, coproductTermsList]
      exact (multiplyCoproductTerms_perm_right (xs := coproductTerms t) ih).trans
        multiplyCoproductTerms_assoc

theorem coproductTermsList_perm_of_list_perm {ts us : List PTree} (h : ts.Perm us) :
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
    ∀ {ts us : List PTree}, List.Forall₂ PTree.Perm ts us →
      (coproductTermsList ts).Perm (coproductTermsList us)
  | [], [], .nil => List.Perm.refl _
  | _ :: _, _ :: _, .cons h hs =>
      multiplyCoproductTerms_perm (coproductTerms_perm h)
        (coproductTermsList_forall₂_perm hs)

theorem coproductTermsList_listRelPerm {ts us : List PTree}
    (h : ListRelPerm PTree.Perm ts us) :
    (coproductTermsList ts).Perm (coproductTermsList us) := by
  rcases h with ⟨ts', hp, hrel⟩
  exact (coproductTermsList_perm_of_list_perm hp).trans
    (coproductTermsList_forall₂_perm hrel)

theorem coproductTermsList_forestPerm {ts us : List PTree} (h : PTree.ForestPerm ts us) :
    (coproductTermsList ts).Perm (coproductTermsList us) :=
  coproductTermsList_listRelPerm (ListRelPerm.of_forestPerm h)

theorem multiplyCoproductTerms_order {xs ys : List (RootedForest × RootedForest)}
    {m n : Nat}
    (hxs : ∀ term ∈ xs, RootedForest.order term.1 + RootedForest.order term.2 = m)
    (hys : ∀ term ∈ ys, RootedForest.order term.1 + RootedForest.order term.2 = n)
    {term : RootedForest × RootedForest}
    (hterm : term ∈ multiplyCoproductTerms xs ys) :
    RootedForest.order term.1 + RootedForest.order term.2 = m + n := by
  simp [multiplyCoproductTerms] at hterm
  obtain ⟨x₁, x₂, hx, y₁, y₂, hy, hterm⟩ := hterm
  subst term
  have hx_order := hxs (x₁, x₂) hx
  have hy_order := hys (y₁, y₂) hy
  simp at hx_order hy_order
  rw [RootedForest.order_add, RootedForest.order_add]
  omega

/-- Every planar-forest coproduct term conserves total order. -/
theorem coproductTermsList_order :
    ∀ {ts : List PTree} {term : RootedForest × RootedForest},
      term ∈ coproductTermsList ts →
        RootedForest.order term.1 + RootedForest.order term.2 = orderList ts
  | [], term, hterm => by
      simp [coproductTermsList] at hterm
      subst term
      simp
  | t :: ts, term, hterm => by
      exact multiplyCoproductTerms_order
        (fun term hterm => coproductTerms_order hterm)
        (fun term hterm => coproductTermsList_order hterm)
        hterm

/-- The only planar-forest coproduct terms with empty left factor are `1 ⊗ φ`. -/
theorem coproductTermsList_left_eq_zero :
    ∀ {ts : List PTree} {term : RootedForest × RootedForest},
      term ∈ coproductTermsList ts → term.1 = 0 →
        term.2 = (ts.map RootedTree.ofPTree : RootedForest)
  | [], term, hterm, _ => by
      simp [coproductTermsList] at hterm
      subst term
      simp
  | t :: ts, term, hterm, hleft => by
      simp [coproductTermsList, multiplyCoproductTerms] at hterm
      obtain ⟨x₁, x₂, hx, y₁, y₂, hy, hterm⟩ := hterm
      subst term
      have hxleft : x₁ = 0 := rootedForest_add_eq_zero_left hleft
      have hyleft : y₁ = 0 := rootedForest_add_eq_zero_right hleft
      have hxright := coproductTerms_left_eq_zero (t := t) (term := (x₁, x₂)) hx hxleft
      have hyright :=
        coproductTermsList_left_eq_zero (ts := ts) (term := (y₁, y₂)) hy hyleft
      have hxright' : x₂ = RootedForest.singleton (RootedTree.ofPTree t) := by
        simpa using hxright
      have hyright' : y₂ = (ts.map RootedTree.ofPTree : RootedForest) := by
        simpa using hyright
      change x₂ + y₂ = (RootedTree.ofPTree t :: ts.map RootedTree.ofPTree : List RootedTree)
      rw [hxright', hyright']
      simp [RootedForest.singleton]

/-- The only planar-forest coproduct terms with empty right factor are `φ ⊗ 1`. -/
theorem coproductTermsList_right_eq_zero :
    ∀ {ts : List PTree} {term : RootedForest × RootedForest},
      term ∈ coproductTermsList ts → term.2 = 0 →
        term.1 = (ts.map RootedTree.ofPTree : RootedForest)
  | [], term, hterm, _ => by
      simp [coproductTermsList] at hterm
      subst term
      simp
  | t :: ts, term, hterm, hright => by
      simp [coproductTermsList, multiplyCoproductTerms] at hterm
      obtain ⟨x₁, x₂, hx, y₁, y₂, hy, hterm⟩ := hterm
      subst term
      have hxright : x₂ = 0 := rootedForest_add_eq_zero_left hright
      have hyright : y₂ = 0 := rootedForest_add_eq_zero_right hright
      have hxleft := coproductTerms_right_eq_zero (t := t) (term := (x₁, x₂)) hx hxright
      have hyleft :=
        coproductTermsList_right_eq_zero (ts := ts) (term := (y₁, y₂)) hy hyright
      have hxleft' : x₁ = RootedForest.singleton (RootedTree.ofPTree t) := by
        simpa using hxleft
      have hyleft' : y₁ = (ts.map RootedTree.ofPTree : RootedForest) := by
        simpa using hyleft
      change x₁ + y₁ = (RootedTree.ofPTree t :: ts.map RootedTree.ofPTree : List RootedTree)
      rw [hxleft', hyleft']
      simp [RootedForest.singleton]

/-- A planar-forest coproduct has exactly one term with empty left factor. -/
theorem coproductTermsList_leftBoundaryCoproductTerm :
    ∀ ts : List PTree,
      (coproductTermsList ts).filterMap leftBoundaryCoproductTerm? =
        [((0 : RootedForest), (ts.map RootedTree.ofPTree : RootedForest))]
  | [] => by
      simp [coproductTermsList, leftBoundaryCoproductTerm?]
  | t :: ts => by
      rw [coproductTermsList, filterMap_multiply_leftBoundaryCoproductTerm,
        coproductTerms_leftBoundaryCoproductTerm t,
        coproductTermsList_leftBoundaryCoproductTerm ts]
      simp [RootedForest.singleton]

/-- A planar-forest coproduct has exactly one term with empty right factor. -/
theorem coproductTermsList_rightBoundaryCoproductTerm :
    ∀ ts : List PTree,
      (coproductTermsList ts).filterMap rightBoundaryCoproductTerm? =
        [((ts.map RootedTree.ofPTree : RootedForest), (0 : RootedForest))]
  | [] => by
      simp [coproductTermsList, rightBoundaryCoproductTerm?]
  | t :: ts => by
      rw [coproductTermsList, filterMap_multiply_rightBoundaryCoproductTerm,
        coproductTerms_rightBoundaryCoproductTerm t,
        coproductTermsList_rightBoundaryCoproductTerm ts]
      simp [RootedForest.singleton]

/-- The proper BCK coproduct terms for a planar forest. -/
def properCoproductTermsList (ts : List PTree) : List (RootedForest × RootedForest) :=
  (coproductTermsList ts).filter fun term =>
    0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2

theorem properCoproductTermsList_forall₂_perm
    {ts us : List PTree} (h : List.Forall₂ PTree.Perm ts us) :
    (properCoproductTermsList ts).Perm (properCoproductTermsList us) :=
  List.Perm.filter _ (coproductTermsList_forall₂_perm h)

theorem properCoproductTermsList_mem_coproductTermsList {ts : List PTree}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTermsList ts) :
    term ∈ coproductTermsList ts :=
  (List.mem_filter.1 hterm).1

theorem properCoproductTermsList_order {ts : List PTree}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTermsList ts) :
    RootedForest.order term.1 + RootedForest.order term.2 = orderList ts :=
  coproductTermsList_order (properCoproductTermsList_mem_coproductTermsList hterm)

theorem properCoproductTermsList_left_order_lt {ts : List PTree}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTermsList ts) :
    RootedForest.order term.1 < orderList ts := by
  have hproper :
      0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hright_pos : 0 < RootedForest.order term.2 := hproper.2
  have horder := properCoproductTermsList_order hterm
  omega

theorem properCoproductTermsList_right_order_lt {ts : List PTree}
    {term : RootedForest × RootedForest} (hterm : term ∈ properCoproductTermsList ts) :
    RootedForest.order term.2 < orderList ts := by
  have hproper :
      0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2 :=
    of_decide_eq_true (List.mem_filter.1 hterm).2
  have hleft_pos : 0 < RootedForest.order term.1 := hproper.1
  have horder := properCoproductTermsList_order hterm
  omega

namespace Cut

/-- Coproduct terms of the trunk of a cut, using `[(0, 0)]` for the full cut. -/
def trunkCoproductTerms (c : Cut) : List (RootedForest × RootedForest) :=
  match c.trunk? with
  | none => [(0, 0)]
  | some trunk => coproductTerms trunk

theorem trunkCoproductTerms_order {c : Cut} {term : RootedForest × RootedForest}
    (hterm : term ∈ c.trunkCoproductTerms) :
    RootedForest.order term.1 + RootedForest.order term.2 =
      RootedForest.order c.trunkForest := by
  cases c with
  | mk pruned trunk? =>
      cases trunk? with
      | none =>
          simp [trunkCoproductTerms, trunkForest] at hterm ⊢
          subst term
          simp
      | some trunk =>
          simpa [trunkCoproductTerms, trunkForest] using coproductTerms_order hterm

theorem trunkCoproductTerms_perm {c d : Cut} (h : Perm c d) :
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
          exact coproductTerms_perm (RootedTree.ofPTree_eq_iff.1 ht)

end Cut

/-- Planar terms for `(Δ ⊗ id)Δ(t)`, keeping the original cut representatives. -/
def nestedCoproductLeftTerms (t : PTree) :
    List (RootedForest × RootedForest × RootedForest) :=
  (cuts t).flatMap fun c =>
    (coproductTermsList c.pruned).map fun left => (left.1, left.2, c.trunkForest)

/-- Planar terms for `(id ⊗ Δ)Δ(t)`, keeping the original cut representatives. -/
def nestedCoproductRightTerms (t : PTree) :
    List (RootedForest × RootedForest × RootedForest) :=
  (cuts t).flatMap fun c =>
    c.trunkCoproductTerms.map fun right => (c.prunedForest, right.1, right.2)

theorem nestedCoproductLeftCut_forall₂_perm {c d : Cut}
    (hpruned : List.Forall₂ PTree.Perm c.pruned d.pruned)
    (htrunk : c.trunkForest = d.trunkForest) :
    ((coproductTermsList c.pruned).map
        fun left => (left.1, left.2, c.trunkForest)).Perm
      ((coproductTermsList d.pruned).map
        fun left => (left.1, left.2, d.trunkForest)) := by
  rw [htrunk]
  exact (coproductTermsList_forall₂_perm hpruned).map
    (fun left => (left.1, left.2, d.trunkForest))

theorem nestedCoproductLeftCut_perm {c d : Cut} (h : Cut.Perm c d) :
    ((coproductTermsList c.pruned).map
        fun left => (left.1, left.2, c.trunkForest)).Perm
      ((coproductTermsList d.pruned).map
        fun left => (left.1, left.2, d.trunkForest)) := by
  rw [h.trunkForest_eq]
  exact (coproductTermsList_forestPerm h.1).map
    (fun left => (left.1, left.2, d.trunkForest))

theorem nestedCoproductLeftCuts_forall₂_perm :
    ∀ {cs ds : List Cut}, List.Forall₂ Cut.Perm cs ds →
      (cs.flatMap fun c =>
        (coproductTermsList c.pruned).map
          fun left => (left.1, left.2, c.trunkForest)).Perm
      (ds.flatMap fun d =>
        (coproductTermsList d.pruned).map
          fun left => (left.1, left.2, d.trunkForest))
  | [], [], .nil => List.Perm.refl _
  | _ :: _, _ :: _, .cons h hs =>
      List.Perm.append (nestedCoproductLeftCut_perm h)
        (nestedCoproductLeftCuts_forall₂_perm hs)

theorem nestedCoproductLeftCuts_listRelPerm {cs ds : List Cut}
    (h : ListRelPerm Cut.Perm cs ds) :
    (cs.flatMap fun c =>
        (coproductTermsList c.pruned).map
          fun left => (left.1, left.2, c.trunkForest)).Perm
      (ds.flatMap fun d =>
        (coproductTermsList d.pruned).map
          fun left => (left.1, left.2, d.trunkForest)) := by
  rcases h with ⟨cs', hp, hrel⟩
  exact (List.Perm.flatMap hp (fun _ _ => List.Perm.refl _)).trans
    (nestedCoproductLeftCuts_forall₂_perm hrel)

theorem nestedCoproductLeftTerms_listRelPerm {t u : PTree}
    (h : ListRelPerm Cut.Perm (cuts t) (cuts u)) :
    (nestedCoproductLeftTerms t).Perm (nestedCoproductLeftTerms u) := by
  simpa [nestedCoproductLeftTerms] using nestedCoproductLeftCuts_listRelPerm h

theorem nestedCoproductLeftTerms_perm {t u : PTree} (h : PTree.Perm t u) :
    (nestedCoproductLeftTerms t).Perm (nestedCoproductLeftTerms u) :=
  nestedCoproductLeftTerms_listRelPerm (cuts_listRelPerm_of_perm h)

theorem nestedCoproductRightCut_perm {c d : Cut} (h : Cut.Perm c d) :
    (c.trunkCoproductTerms.map
        fun right => (c.prunedForest, right.1, right.2)).Perm
      (d.trunkCoproductTerms.map
        fun right => (d.prunedForest, right.1, right.2)) := by
  rw [h.prunedForest_eq]
  exact (Cut.trunkCoproductTerms_perm h).map
    (fun right => (d.prunedForest, right.1, right.2))

theorem nestedCoproductRightCuts_forall₂_perm :
    ∀ {cs ds : List Cut}, List.Forall₂ Cut.Perm cs ds →
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

theorem nestedCoproductRightCuts_listRelPerm {cs ds : List Cut}
    (h : ListRelPerm Cut.Perm cs ds) :
    (cs.flatMap fun c =>
        c.trunkCoproductTerms.map
          fun right => (c.prunedForest, right.1, right.2)).Perm
      (ds.flatMap fun d =>
        d.trunkCoproductTerms.map
          fun right => (d.prunedForest, right.1, right.2)) := by
  rcases h with ⟨cs', hp, hrel⟩
  exact (List.Perm.flatMap hp (fun _ _ => List.Perm.refl _)).trans
    (nestedCoproductRightCuts_forall₂_perm hrel)

theorem nestedCoproductRightTerms_listRelPerm {t u : PTree}
    (h : ListRelPerm Cut.Perm (cuts t) (cuts u)) :
    (nestedCoproductRightTerms t).Perm (nestedCoproductRightTerms u) := by
  simpa [nestedCoproductRightTerms] using nestedCoproductRightCuts_listRelPerm h

theorem nestedCoproductRightTerms_perm {t u : PTree} (h : PTree.Perm t u) :
    (nestedCoproductRightTerms t).Perm (nestedCoproductRightTerms u) :=
  nestedCoproductRightTerms_listRelPerm (cuts_listRelPerm_of_perm h)

theorem nestedCoproductLeftTerms_order
    {t : PTree} {term : RootedForest × RootedForest × RootedForest}
    (hterm : term ∈ nestedCoproductLeftTerms t) :
    RootedForest.order term.1 + RootedForest.order term.2.1 +
        RootedForest.order term.2.2 = order t := by
  simp [nestedCoproductLeftTerms] at hterm
  obtain ⟨c, hc, left₁, left₂, hleft, hterm⟩ := hterm
  subst term
  have hleft_order := coproductTermsList_order hleft
  have hcut := cuts_order hc
  change
    RootedForest.order left₁ + RootedForest.order left₂ = orderList c.pruned
      at hleft_order
  rw [← RootedForest.order_ofPTree_list c.pruned] at hleft_order
  change
    RootedForest.order left₁ + RootedForest.order left₂ =
      RootedForest.order c.prunedForest at hleft_order
  rw [← Cut.order_trunkForest c] at hcut
  change
    RootedForest.order c.prunedForest + RootedForest.order c.trunkForest =
      order t at hcut
  change
    RootedForest.order left₁ + RootedForest.order left₂ +
        RootedForest.order c.trunkForest = order t
  omega

theorem nestedCoproductRightTerms_order
    {t : PTree} {term : RootedForest × RootedForest × RootedForest}
    (hterm : term ∈ nestedCoproductRightTerms t) :
    RootedForest.order term.1 + RootedForest.order term.2.1 +
        RootedForest.order term.2.2 = order t := by
  simp [nestedCoproductRightTerms] at hterm
  obtain ⟨c, hc, right₁, right₂, hright, hterm⟩ := hterm
  subst term
  have hright_order := Cut.trunkCoproductTerms_order hright
  have hcut := cuts_order hc
  change
    RootedForest.order right₁ + RootedForest.order right₂ =
      RootedForest.order c.trunkForest at hright_order
  rw [← Cut.order_trunkForest c] at hcut
  change
    RootedForest.order c.prunedForest + RootedForest.order c.trunkForest =
      order t at hcut
  change
    RootedForest.order c.prunedForest + RootedForest.order right₁ +
        RootedForest.order right₂ = order t
  omega

@[simp]
theorem rootCutsList_nil : rootCutsList [] = [{ pruned := [], trunks := [] }] :=
  by simp [rootCutsList]

@[simp]
theorem rootCuts_bullet :
    rootCuts bullet = [{ pruned := [], trunk := bullet }] :=
  by simp [rootCuts, bullet]

end PTree

end HopfAlgebras
