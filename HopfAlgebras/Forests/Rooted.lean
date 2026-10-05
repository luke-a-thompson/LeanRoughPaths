/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Trees.Rooted
import Mathlib.Data.Multiset.MapFold
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Rooted Forests

This file defines non-planar rooted forests as multisets of non-planar rooted
trees. These are the monomials in the commutative algebra of rooted forests.

## Main definitions

* `RootedForest` - non-planar rooted forests
* `RootedTree.branches` - the forest immediately below the root
* `RootedForest.graft` - the `B_+` operator grafting a forest onto a new root
* `RootedForest.order` - total number of vertices
* `RootedForest.treeFactorial` - product of tree factorials

## References

* John C. Butcher, *Numerical Methods for Ordinary Differential Equations*
* Philippe Chartier, Ernst Hairer, Gilles Vilmart,
  *Algebraic Structures of B-series*
-/

namespace HopfAlgebras

/-- Non-planar rooted forests, represented by multisets of non-planar rooted trees. -/
abbrev RootedForest : Type :=
  Multiset RootedTree

namespace PTree

/-- Two planar tree lists represent the same non-planar rooted forest. -/
def ForestPerm (ts us : List PTree) : Prop :=
  ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) =
    ((us.map RootedTree.ofPTree : List RootedTree) : RootedForest)

theorem ForestPerm.refl (ts : List PTree) : ForestPerm ts ts :=
  rfl

theorem ForestPerm.symm {ts us : List PTree} (h : ForestPerm ts us) :
    ForestPerm us ts :=
  Eq.symm h

theorem ForestPerm.trans {ts us vs : List PTree}
    (h₁ : ForestPerm ts us) (h₂ : ForestPerm us vs) :
    ForestPerm ts vs :=
  Eq.trans h₁ h₂

theorem ForestPerm.of_list_perm {ts us : List PTree} (h : ts.Perm us) :
    ForestPerm ts us :=
  Quotient.sound (h.map RootedTree.ofPTree)

theorem ForestPerm.of_forall₂_perm {ts us : List PTree}
    (h : List.Forall₂ PTree.Perm ts us) :
    ForestPerm ts us :=
  congrArg (fun vs : List RootedTree => (vs : RootedForest))
    (RootedTree.map_ofPTree_eq_of_forall₂_perm h)

theorem ForestPerm.cons_eq {t u : PTree} {ts us : List PTree}
    (ht : RootedTree.ofPTree t = RootedTree.ofPTree u) (h : ForestPerm ts us) :
    ForestPerm (t :: ts) (u :: us) := by
  dsimp [ForestPerm] at h ⊢
  simp only [List.map_cons]
  rw [ht]
  simpa using
    congrArg (fun φ : RootedForest => ({RootedTree.ofPTree u} : RootedForest) + φ) h

theorem ForestPerm.cons {t u : PTree} {ts us : List PTree}
    (ht : PTree.Perm t u) (h : ForestPerm ts us) :
    ForestPerm (t :: ts) (u :: us) :=
  ForestPerm.cons_eq (Quotient.sound (show t ≈ u from ht)) h

theorem ForestPerm.append {ts us vs ws : List PTree}
    (h₁ : ForestPerm ts us) (h₂ : ForestPerm vs ws) :
    ForestPerm (ts ++ vs) (us ++ ws) := by
  dsimp [ForestPerm] at h₁ h₂ ⊢
  simpa [List.map_append] using congrArg₂ HAdd.hAdd h₁ h₂

end PTree

namespace RootedTree

private def branchesAux : PTree → RootedForest
  | .node ts => (ts.map RootedTree.ofPTree : RootedForest)

private theorem branchesAux_sound :
    ∀ {t1 t2 : PTree}, PTree.Perm t1 t2 → branchesAux t1 = branchesAux t2
  | _, _, .node hp hf => by
      have hp' :=
        @Quotient.sound (List RootedTree) (List.isSetoid RootedTree) _ _
          (hp.map RootedTree.ofPTree)
      have hf' :=
        congrArg (fun ts : List RootedTree => (ts : RootedForest))
          (RootedTree.map_ofPTree_eq_of_forall₂_perm hf)
      exact hp'.trans hf'

/-- The forest immediately below the root of a non-planar rooted tree. -/
def branches : RootedTree → RootedForest :=
  Quotient.lift branchesAux (fun _ _ h => branchesAux_sound h)

@[simp]
theorem branches_ofPTree_node (ts : List PTree) :
    branches (ofPTree (.node ts)) = (ts.map ofPTree : RootedForest) :=
  rfl

@[simp]
theorem branches_bullet : branches bullet = 0 :=
  rfl

end RootedTree

namespace RootedForest

noncomputable section

/-- The empty rooted forest. -/
def empty : RootedForest :=
  0

/-- The one-tree forest. -/
def singleton (τ : RootedTree) : RootedForest :=
  {τ}

/-- The total number of vertices in a rooted forest. -/
def order (φ : RootedForest) : Nat :=
  (φ.map RootedTree.order).sum

/-- Predicate for rooted forests of a fixed order. -/
def IsOfOrder (φ : RootedForest) (n : Nat) : Prop :=
  order φ = n

/-- The product of the tree factorials in a rooted forest. -/
def treeFactorial (φ : RootedForest) : Nat :=
  (φ.map RootedTree.treeFactorial).prod

private theorem order_out (τ : RootedTree) :
    PTree.order (Quotient.out τ) = RootedTree.order τ := by
  rw [← RootedTree.order_ofPTree (Quotient.out τ)]
  rw [show RootedTree.ofPTree (Quotient.out τ) = τ from Quotient.out_eq τ]

private theorem treeFactorial_out (τ : RootedTree) :
    PTree.treeFactorial (Quotient.out τ) = RootedTree.treeFactorial τ := by
  rw [← RootedTree.treeFactorial_ofPTree (Quotient.out τ)]
  rw [show RootedTree.ofPTree (Quotient.out τ) = τ from Quotient.out_eq τ]

private theorem orderList_out :
    ∀ ts : List RootedTree,
      PTree.orderList (ts.map Quotient.out) = (ts.map RootedTree.order).sum
  | [] => rfl
  | τ :: ts => by
      simp [order_out τ, orderList_out ts]

private theorem treeFactorialList_out :
    ∀ ts : List RootedTree,
      PTree.treeFactorialList (ts.map Quotient.out) =
        (ts.map RootedTree.treeFactorial).prod
  | [] => rfl
  | τ :: ts => by
      simp [treeFactorial_out τ, treeFactorialList_out ts]

/--
The `B_+` operator: graft all roots in a forest onto one new common root.
-/
def graft : RootedForest → RootedTree :=
  Quotient.lift
    (fun ts : List RootedTree => RootedTree.ofPTree (.node (ts.map Quotient.out)))
    (fun ts1 ts2 h => by
      exact Quotient.sound <|
        PTree.Perm.node (h.map Quotient.out) (PTree.permForall2_refl _))

@[simp]
theorem graft_coe (ts : List RootedTree) :
    graft (ts : RootedForest) = RootedTree.ofPTree (.node (ts.map Quotient.out)) :=
  rfl

@[simp]
theorem graft_empty : graft empty = RootedTree.bullet := rfl

@[simp]
theorem graft_zero : graft (0 : RootedForest) = RootedTree.bullet := rfl

@[simp]
theorem branches_graft (φ : RootedForest) : RootedTree.branches (graft φ) = φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change (((ts.map Quotient.out).map RootedTree.ofPTree : List RootedTree) :
    RootedForest) = (ts : RootedForest)
  have h : (ts.map Quotient.out).map RootedTree.ofPTree = ts := by
    induction ts with
    | nil => rfl
    | cons τ ts ih =>
        simp [RootedTree.ofPTree_out τ, ih]
  rw [h]

theorem graft_injective : Function.Injective graft := by
  intro φ ψ h
  have hbranches := congrArg RootedTree.branches h
  simpa using hbranches

@[simp]
theorem graft_eq_graft_iff (φ ψ : RootedForest) : graft φ = graft ψ ↔ φ = ψ := by
  constructor
  · intro h
    exact graft_injective h
  · intro h
    rw [h]

@[simp]
theorem order_empty : order empty = 0 := by
  simp [empty, order]

@[simp]
theorem order_zero : order (0 : RootedForest) = 0 := by
  simp [order]

@[simp]
theorem order_singleton (τ : RootedTree) :
    order (singleton τ) = RootedTree.order τ := by
  simp [singleton, order]

theorem singleton_ne_zero (τ : RootedTree) : singleton τ ≠ 0 := by
  intro h
  have horder : order (singleton τ) = 0 := by
    rw [h]
    simp
  rw [order_singleton] at horder
  exact (Nat.ne_of_gt (RootedTree.order_pos τ)) horder

@[simp]
theorem order_ofPTree_list :
    ∀ ts : List PTree,
      order ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) = PTree.orderList ts
  | [] => rfl
  | t :: ts => by
      have ih := order_ofPTree_list ts
      simp [order] at ih
      simp [order, ih]

@[simp]
theorem treeFactorial_ofPTree_list :
    ∀ ts : List PTree,
      treeFactorial ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) =
        PTree.treeFactorialList ts
  | [] => rfl
  | t :: ts => by
      have ih := treeFactorial_ofPTree_list ts
      simp [treeFactorial] at ih
      simp [treeFactorial, ih]

@[simp]
theorem order_add (φ ψ : RootedForest) : order (φ + ψ) = order φ + order ψ := by
  simp [order, Multiset.map_add]

theorem order_coe_cons_pos (τ : RootedTree) (ts : List RootedTree) :
    0 < order (((τ :: ts) : List RootedTree) : RootedForest) := by
  have hτ := RootedTree.order_pos τ
  simp [order]
  omega

@[simp]
theorem order_eq_zero_iff (φ : RootedForest) : order φ = 0 ↔ φ = 0 := by
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

theorem order_pos_iff_ne_zero (φ : RootedForest) : 0 < order φ ↔ φ ≠ 0 := by
  constructor
  · intro h hzero
    rw [hzero] at h
    simp at h
  · intro h
    have horder : order φ ≠ 0 := fun hzero => h ((order_eq_zero_iff φ).1 hzero)
    omega

@[simp]
theorem treeFactorial_empty : treeFactorial empty = 1 := by
  simp [empty, treeFactorial]

@[simp]
theorem treeFactorial_zero : treeFactorial (0 : RootedForest) = 1 := by
  simp [treeFactorial]

@[simp]
theorem treeFactorial_singleton (τ : RootedTree) :
    treeFactorial (singleton τ) = RootedTree.treeFactorial τ := by
  simp [singleton, treeFactorial]

@[simp]
theorem treeFactorial_add (φ ψ : RootedForest) :
    treeFactorial (φ + ψ) = treeFactorial φ * treeFactorial ψ := by
  simp [treeFactorial, Multiset.map_add]

theorem treeFactorial_pos (φ : RootedForest) : 0 < treeFactorial φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change 0 < (ts.map RootedTree.treeFactorial).prod
  induction ts with
  | nil => simp
  | cons τ ts ih =>
      simp [Nat.mul_pos (RootedTree.treeFactorial_pos τ) ih]

theorem treeFactorial_ne_zero (φ : RootedForest) : treeFactorial φ ≠ 0 :=
  Nat.ne_of_gt (treeFactorial_pos φ)

@[simp]
theorem order_graft (φ : RootedForest) :
    RootedTree.order (graft φ) = 1 + order φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change RootedTree.order (graft (ts : RootedForest)) = 1 + order (ts : RootedForest)
  rw [graft_coe]
  simp [order, orderList_out]

@[simp]
theorem treeFactorial_graft (φ : RootedForest) :
    RootedTree.treeFactorial (graft φ) = (1 + order φ) * treeFactorial φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change RootedTree.treeFactorial (graft (ts : RootedForest)) = (1 + order (ts : RootedForest)) * treeFactorial (ts : RootedForest)
  rw [graft_coe]
  simp [order, treeFactorial, orderList_out, treeFactorialList_out]

private theorem forall2_out_perm_ofPTree :
    ∀ ts : List PTree,
      List.Forall₂ PTree.Perm ((ts.map RootedTree.ofPTree).map Quotient.out) ts
  | [] => .nil
  | t :: ts => by
      exact .cons (RootedTree.out_perm_ofPTree t) (forall2_out_perm_ofPTree ts)

/-- Grafting quotient classes of planar trees agrees with planar `PTree.node`. -/
theorem graft_ofPTree_list (ts : List PTree) :
    graft ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) =
      RootedTree.ofPTree (.node ts) := by
  change
    RootedTree.ofPTree (.node ((ts.map RootedTree.ofPTree).map Quotient.out)) =
      RootedTree.ofPTree (.node ts)
  exact Quotient.sound (PTree.perm_node_of_forall2 (forall2_out_perm_ofPTree ts))

theorem ofPTree_node_eq_of_forestPerm {ts us : List PTree} (h : PTree.ForestPerm ts us) :
    RootedTree.ofPTree (.node ts) = RootedTree.ofPTree (.node us) := by
  rw [← graft_ofPTree_list ts, ← graft_ofPTree_list us, h]

@[simp]
theorem graft_branches_ofPTree_node (ts : List PTree) :
    graft (RootedTree.branches (RootedTree.ofPTree (.node ts))) =
      RootedTree.ofPTree (.node ts) := by
  rw [RootedTree.branches_ofPTree_node]
  exact graft_ofPTree_list ts

@[simp]
theorem graft_branches (τ : RootedTree) : graft (RootedTree.branches τ) = τ := by
  refine Quotient.inductionOn τ ?_
  intro t
  cases t with
  | node ts => exact graft_branches_ofPTree_node ts

@[simp]
theorem order_branches (τ : RootedTree) :
    1 + order (RootedTree.branches τ) = RootedTree.order τ := by
  have h := congrArg RootedTree.order (graft_branches τ)
  change RootedTree.order (graft (RootedTree.branches τ)) = RootedTree.order τ at h
  rw [order_graft] at h
  exact h

theorem order_branches_lt (τ : RootedTree) :
    order (RootedTree.branches τ) < RootedTree.order τ := by
  rw [← order_branches τ]
  omega

theorem branches_eq_zero_of_order_eq_one (τ : RootedTree)
    (h : RootedTree.order τ = 1) : RootedTree.branches τ = 0 := by
  have hbranches := order_branches τ
  rw [h] at hbranches
  have hzero : order (RootedTree.branches τ) = 0 := by omega
  exact (order_eq_zero_iff _).1 hzero

theorem order_eq_one_iff_branches_eq_zero (τ : RootedTree) :
    RootedTree.order τ = 1 ↔ RootedTree.branches τ = 0 := by
  constructor
  · exact branches_eq_zero_of_order_eq_one τ
  · intro h
    rw [← order_branches τ, h]
    simp

theorem order_eq_one_iff_eq_graft_zero (τ : RootedTree) :
    RootedTree.order τ = 1 ↔ τ = graft 0 := by
  constructor
  · intro h
    calc
      τ = graft (RootedTree.branches τ) := (graft_branches τ).symm
      _ = graft 0 := by
          rw [branches_eq_zero_of_order_eq_one τ h]
  · intro h
    rw [h]
    simp

theorem treeFactorial_branches (τ : RootedTree) :
    RootedTree.order τ * treeFactorial (RootedTree.branches τ) =
      RootedTree.treeFactorial τ := by
  have h := congrArg RootedTree.treeFactorial (graft_branches τ)
  change
    RootedTree.treeFactorial (graft (RootedTree.branches τ)) =
      RootedTree.treeFactorial τ at h
  rw [treeFactorial_graft] at h
  rw [← order_branches τ]
  exact h

/-- Graft a rooted forest onto the root of a rooted tree. -/
def butcherProduct (φ : RootedForest) (τ : RootedTree) : RootedTree :=
  graft (φ + RootedTree.branches τ)

@[simp]
theorem butcherProduct_zero_left (τ : RootedTree) : butcherProduct 0 τ = τ := by
  simp [butcherProduct]

@[simp]
theorem butcherProduct_empty_left (τ : RootedTree) : butcherProduct empty τ = τ := by
  simp [empty, butcherProduct]

@[simp]
theorem branches_butcherProduct (φ : RootedForest) (τ : RootedTree) :
    RootedTree.branches (butcherProduct φ τ) = φ + RootedTree.branches τ := by
  simp [butcherProduct]

theorem butcherProduct_ofPTree_list (ts : List PTree) (t : PTree) :
    RootedTree.ofPTree (PTree.butcherProduct ts t) =
      butcherProduct ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest)
        (RootedTree.ofPTree t) := by
  cases t with
  | node us =>
      change RootedTree.ofPTree (PTree.node (ts ++ us)) =
        butcherProduct ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest)
          (RootedTree.ofPTree (PTree.node us))
      rw [← graft_ofPTree_list (ts ++ us)]
      simp [butcherProduct, List.map_append]

theorem butcherProduct_eq_iff_branches
    (φ ψ : RootedForest) (τ σ : RootedTree) :
    butcherProduct φ τ = butcherProduct ψ σ ↔
      φ + RootedTree.branches τ = ψ + RootedTree.branches σ := by
  simp [butcherProduct]

theorem butcherProduct_injective_left (τ : RootedTree) :
    Function.Injective (fun φ : RootedForest => butcherProduct φ τ) := by
  intro φ ψ h
  have hbranches := (butcherProduct_eq_iff_branches φ ψ τ τ).1 h
  exact add_right_cancel hbranches

theorem butcherProduct_injective_right (φ : RootedForest) :
    Function.Injective (butcherProduct φ) := by
  intro τ σ h
  have hbranches := (butcherProduct_eq_iff_branches φ φ τ σ).1 h
  have hbranches' : RootedTree.branches τ = RootedTree.branches σ :=
    add_left_cancel hbranches
  calc
    τ = graft (RootedTree.branches τ) := (graft_branches τ).symm
    _ = graft (RootedTree.branches σ) := by rw [hbranches']
    _ = σ := graft_branches σ

@[simp]
theorem butcherProduct_left_eq_left_iff
    (φ ψ : RootedForest) (τ : RootedTree) :
    butcherProduct φ τ = butcherProduct ψ τ ↔ φ = ψ := by
  constructor
  · intro h
    exact butcherProduct_injective_left τ h
  · intro h
    rw [h]

@[simp]
theorem butcherProduct_right_eq_right_iff
    (φ : RootedForest) (τ σ : RootedTree) :
    butcherProduct φ τ = butcherProduct φ σ ↔ τ = σ := by
  constructor
  · intro h
    exact butcherProduct_injective_right φ h
  · intro h
    rw [h]

@[simp]
theorem butcherProduct_assoc (φ ψ : RootedForest) (τ : RootedTree) :
    butcherProduct φ (butcherProduct ψ τ) = butcherProduct (φ + ψ) τ := by
  simp [butcherProduct, add_assoc]

@[simp]
theorem order_butcherProduct (φ : RootedForest) (τ : RootedTree) :
    RootedTree.order (butcherProduct φ τ) = order φ + RootedTree.order τ := by
  calc
    RootedTree.order (butcherProduct φ τ) =
        1 + order (φ + RootedTree.branches τ) := by
          simp [butcherProduct]
    _ = 1 + (order φ + order (RootedTree.branches τ)) := by
          rw [order_add]
    _ = order φ + (1 + order (RootedTree.branches τ)) := by
          omega
    _ = order φ + RootedTree.order τ := by
          rw [order_branches]

@[simp]
theorem treeFactorial_butcherProduct (φ : RootedForest) (τ : RootedTree) :
    RootedTree.treeFactorial (butcherProduct φ τ) =
      (order φ + RootedTree.order τ) * treeFactorial (φ + RootedTree.branches τ) := by
  calc
    RootedTree.treeFactorial (butcherProduct φ τ) =
        (1 + order (φ + RootedTree.branches τ)) *
          treeFactorial (φ + RootedTree.branches τ) := by
          simp [butcherProduct]
    _ = (1 + (order φ + order (RootedTree.branches τ))) *
          treeFactorial (φ + RootedTree.branches τ) := by
          rw [order_add]
    _ = (order φ + RootedTree.order τ) *
          treeFactorial (φ + RootedTree.branches τ) := by
          rw [← order_branches τ]
          congr 1
          omega

end

end RootedForest

end HopfAlgebras
