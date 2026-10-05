/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Algebra.LabelledForest
import HopfAlgebras.Trees.Planar
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The Algebra of Ordered Planar Forests

This file defines the noncommutative algebra freely spanned by ordered planar
forests. Multiplication is concatenation of ordered forests. The quotient maps
to the existing commutative non-planar forest algebras forget sibling order.

This is the algebraic carrier needed for ordered-tree Hopf algebras such as
the Munthe-Kaas-Wright Hopf algebra.

## Main definitions

* `PlanarForestAlgebra` - monoid algebra of ordered planar forests
* `LPlanarForestAlgebra` - labelled ordered planar forest algebra
* `PlanarForestAlgebra.toForestAlgebra` - forget planar order
* `LPlanarForestAlgebra.toLForestAlgebra` - forget planar order in the labelled case
-/

namespace HopfAlgebras

universe u v w x

/-- The noncommutative algebra freely spanned by ordered planar forests. -/
abbrev PlanarForestAlgebra (R : Type u) [Semiring R] : Type u :=
  MonoidAlgebra R PlanarForest

instance : One PlanarForest where
  one := []

instance : Mul PlanarForest where
  mul := List.append

instance : Monoid PlanarForest where
  one_mul _ := rfl
  mul_one ts := List.append_nil ts
  mul_assoc ts us vs := List.append_assoc ts us vs

namespace PlanarForest

@[simp]
theorem toRootedForest_nil :
    toRootedForest ([] : PlanarForest) = 0 :=
  rfl

@[simp]
theorem toRootedForest_empty :
    toRootedForest empty = 0 :=
  rfl

@[simp]
theorem toRootedForest_append (ts us : PlanarForest) :
    toRootedForest (ts ++ us) = toRootedForest ts + toRootedForest us := by
  simp [toRootedForest, List.map_append]

@[simp]
theorem toRootedForest_singleton (t : PlanarTree) :
    toRootedForest (singleton t) = RootedForest.singleton (PlanarTree.toRootedTree t) := by
  simp [toRootedForest, singleton, RootedForest.singleton, PlanarTree.toRootedTree]

end PlanarForest

namespace PlanarForestAlgebra

noncomputable section

variable {R : Type u}

/-- The monomial associated to an ordered planar forest. -/
def ofForest [Semiring R] (ts : PlanarForest) : PlanarForestAlgebra R :=
  MonoidAlgebra.single ts 1

@[simp]
theorem ofForest_empty [Semiring R] :
    ofForest (R := R) PlanarForest.empty = 1 := by
  change MonoidAlgebra.single ([] : PlanarForest) (1 : R) =
    MonoidAlgebra.single ([] : PlanarForest) 1
  rfl

@[simp]
theorem ofForest_nil [Semiring R] :
    ofForest (R := R) ([] : PlanarForest) = 1 := by
  change MonoidAlgebra.single ([] : PlanarForest) (1 : R) =
    MonoidAlgebra.single ([] : PlanarForest) 1
  rfl

@[simp]
theorem ofForest_append [Semiring R] (ts us : PlanarForest) :
    ofForest (R := R) (ts ++ us) = ofForest ts * ofForest us := by
  rw [ofForest, ofForest, ofForest, MonoidAlgebra.single_mul_single]
  change MonoidAlgebra.single (ts ++ us) (1 : R) =
    MonoidAlgebra.single (ts ++ us) (1 * 1)
  simp

@[simp]
theorem ofForest_singleton_mul [Semiring R] (t : PlanarTree) (ts : PlanarForest) :
    ofForest (R := R) (t :: ts) = ofForest [t] * ofForest ts := by
  exact ofForest_append [t] ts

/-- The counit value on an ordered forest monomial. -/
def counitCoeff [Zero R] [One R] (ts : PlanarForest) : R := by
  classical
  exact if ts = [] then 1 else 0

@[simp]
theorem counitCoeff_nil [Zero R] [One R] :
    counitCoeff (R := R) ([] : PlanarForest) = 1 := by
  classical
  simp [counitCoeff]

@[simp]
theorem counitCoeff_empty [Zero R] [One R] :
    counitCoeff (R := R) PlanarForest.empty = 1 := by
  classical
  simp [PlanarForest.empty]

theorem counitCoeff_ne_nil [Zero R] [One R] {ts : PlanarForest} (hts : ts ≠ []) :
    counitCoeff (R := R) ts = 0 := by
  classical
  simp [counitCoeff, hts]

theorem counitCoeff_append [Semiring R] (ts us : PlanarForest) :
    counitCoeff (R := R) (ts ++ us) = counitCoeff ts * counitCoeff us := by
  classical
  cases ts with
  | nil =>
      simp [counitCoeff]
  | cons t ts =>
      cases us with
      | nil =>
          simp [counitCoeff]
      | cons u us =>
          simp [counitCoeff]

private def counitMonoidHom (R : Type u) [CommSemiring R] :
    PlanarForest →* R where
  toFun ts := counitCoeff (R := R) ts
  map_one' := by
    change counitCoeff (R := R) ([] : PlanarForest) = 1
    simp
  map_mul' ts us := by
    change counitCoeff (R := R) (ts ++ us) = counitCoeff ts * counitCoeff us
    exact counitCoeff_append (R := R) ts us

/-- The counit algebra homomorphism, sending the empty ordered forest to `1`. -/
def counit (R : Type u) [CommSemiring R] : PlanarForestAlgebra R →ₐ[R] R :=
  (MonoidAlgebra.lift R R PlanarForest) (counitMonoidHom R)

@[simp]
theorem counit_ofForest [CommSemiring R] (ts : PlanarForest) :
    counit R (ofForest ts) = counitCoeff (R := R) ts := by
  simp [counit, ofForest, counitMonoidHom, counitCoeff]

@[simp]
theorem counit_ofForest_empty [CommSemiring R] :
    counit R (ofForest (R := R) PlanarForest.empty) = 1 := by
  simp

@[simp]
theorem counit_ofForest_nil [CommSemiring R] :
    counit R (ofForest (R := R) ([] : PlanarForest)) = 1 := by
  simp

@[simp]
theorem counit_ofForest_ne_nil [CommSemiring R] {ts : PlanarForest} (hts : ts ≠ []) :
    counit R (ofForest (R := R) ts) = 0 := by
  rw [counit_ofForest]
  exact counitCoeff_ne_nil hts

private def toForestAlgebraMonoidHom (R : Type u) [CommSemiring R] :
    PlanarForest →* ForestAlgebra R where
  toFun ts := ForestAlgebra.ofForest (R := R) (PlanarForest.toRootedForest ts)
  map_one' := by
    change ForestAlgebra.ofForest (R := R) (PlanarForest.toRootedForest []) = 1
    simp
  map_mul' ts us := by
    change
      ForestAlgebra.ofForest (R := R) (PlanarForest.toRootedForest (ts ++ us)) =
        ForestAlgebra.ofForest (R := R) (PlanarForest.toRootedForest ts) *
          ForestAlgebra.ofForest (R := R) (PlanarForest.toRootedForest us)
    rw [PlanarForest.toRootedForest_append, ForestAlgebra.ofForest_add]

/-- Forget planar order as an algebra morphism to the commutative forest algebra. -/
def toForestAlgebra (R : Type u) [CommSemiring R] :
    PlanarForestAlgebra R →ₐ[R] ForestAlgebra R :=
  (MonoidAlgebra.lift R (ForestAlgebra R) PlanarForest)
    (toForestAlgebraMonoidHom R)

@[simp]
theorem toForestAlgebra_ofForest [CommSemiring R] (ts : PlanarForest) :
    toForestAlgebra R (ofForest ts) =
      ForestAlgebra.ofForest (R := R) (PlanarForest.toRootedForest ts) := by
  simp [toForestAlgebra, ofForest, toForestAlgebraMonoidHom]

@[simp]
theorem toForestAlgebra_ofForest_empty [CommSemiring R] :
    toForestAlgebra R (ofForest (R := R) PlanarForest.empty) = 1 := by
  simp

@[simp]
theorem counit_comp_toForestAlgebra [CommSemiring R] :
    (ForestAlgebra.counit R).comp (toForestAlgebra R) = counit R := by
  refine MonoidAlgebra.algHom_ext ?_ (by ext)
  intro ts
  change
    ForestAlgebra.counit R
        (toForestAlgebra R (ofForest (R := R) ts)) =
      counit R (ofForest (R := R) ts)
  rw [toForestAlgebra_ofForest, ForestAlgebra.counit_ofForest, counit_ofForest]
  classical
  cases ts with
  | nil =>
      simp
  | cons t ts =>
      have hne : PlanarForest.toRootedForest (t :: ts) ≠ 0 := by
        have horder : 0 < RootedForest.order (PlanarForest.toRootedForest (t :: ts)) := by
          rw [PlanarForest.order_toRootedForest]
          change 0 < PlanarTree.order t + PlanarForest.order ts
          exact Nat.add_pos_left (PlanarTree.order_pos t) (PlanarForest.order ts)
        exact (RootedForest.order_pos_iff_ne_zero _).1 horder
      rw [ForestAlgebra.counitCoeff_ne_zero hne]
      simp [counitCoeff]

/-- Algebra characters on the ordered planar forest algebra. -/
abbrev Character (R : Type u) [CommSemiring R] : Type u :=
  PlanarForestAlgebra R →ₐ[R] R

namespace Character

variable [CommSemiring R]

/-- Evaluate a character on the monomial associated to an ordered planar forest. -/
def evalForest (χ : Character R) (ts : PlanarForest) : R :=
  χ (ofForest (R := R) ts)

@[simp]
theorem evalForest_empty (χ : Character R) :
    χ.evalForest PlanarForest.empty = 1 := by
  simp [evalForest]

@[simp]
theorem evalForest_nil (χ : Character R) :
    χ.evalForest ([] : PlanarForest) = 1 := by
  simp [evalForest]

@[simp]
theorem evalForest_append (χ : Character R) (ts us : PlanarForest) :
    χ.evalForest (ts ++ us) = χ.evalForest ts * χ.evalForest us := by
  simp [evalForest, ofForest_append]

@[ext]
theorem ext {χ ψ : Character R} (h : ∀ ts, χ.evalForest ts = ψ.evalForest ts) :
    χ = ψ := by
  refine MonoidAlgebra.algHom_ext ?_ (by ext)
  intro ts
  exact h ts

/-- Pull a commutative forest character back by forgetting planar order. -/
def comapToForestAlgebra (χ : ForestAlgebra.Character R) : Character R :=
  χ.comp (toForestAlgebra R)

@[simp]
theorem comapToForestAlgebra_evalForest
    (χ : ForestAlgebra.Character R) (ts : PlanarForest) :
    (comapToForestAlgebra χ).evalForest ts =
      χ.evalForest (PlanarForest.toRootedForest ts) := by
  simp [comapToForestAlgebra, evalForest, ForestAlgebra.Character.evalForest]

@[simp]
theorem comapToForestAlgebra_counit :
    comapToForestAlgebra (R := R) (ForestAlgebra.counit R) = counit R := by
  exact counit_comp_toForestAlgebra

end Character

end

end PlanarForestAlgebra

/-- The noncommutative algebra freely spanned by labelled ordered planar forests. -/
abbrev LPlanarForestAlgebra (α : Type u) (R : Type v) [Semiring R] : Type (max u v) :=
  MonoidAlgebra R (LPlanarForest α)

instance (α : Type u) : One (LPlanarForest α) where
  one := []

instance (α : Type u) : Mul (LPlanarForest α) where
  mul := List.append

instance (α : Type u) : Monoid (LPlanarForest α) where
  one := []
  mul := List.append
  one_mul _ := rfl
  mul_one ts := List.append_nil ts
  mul_assoc ts us vs := List.append_assoc ts us vs

namespace LPlanarForest

variable {α : Type u} {β : Type v}

@[simp]
theorem toRootedForest_nil :
    toRootedForest ([] : LPlanarForest α) = 0 :=
  rfl

@[simp]
theorem toRootedForest_empty :
    toRootedForest (empty : LPlanarForest α) = 0 :=
  rfl

@[simp]
theorem toRootedForest_append (ts us : LPlanarForest α) :
    toRootedForest (ts ++ us) = toRootedForest ts + toRootedForest us := by
  simp [toRootedForest, List.map_append]

@[simp]
theorem erase_append' (ts us : LPlanarForest α) :
    erase (ts ++ us) = PlanarForest.append (erase ts) (erase us) := by
  simpa [append] using erase_append (ts := ts) (us := us)

@[simp]
theorem constLabel_append (a : α) (ts us : PlanarForest) :
    constLabel a (ts ++ us) = constLabel a ts ++ constLabel a us := by
  simp [constLabel, List.map_append]

@[simp]
theorem toRootedForest_map (f : α → β) (ts : LPlanarForest α) :
    toRootedForest (map f ts) = LRootedForest.mapLabels f (toRootedForest ts) := by
  simp [toRootedForest, map, LRootedForest.mapLabels, List.map_map, Function.comp_def,
    LPlanarTree.map]

@[simp]
theorem toRootedForest_constLabel (a : α) (ts : PlanarForest) :
    toRootedForest (constLabel a ts) =
      LRootedForest.constLabel a (PlanarForest.toRootedForest ts) := by
  simp [toRootedForest, constLabel, LRootedForest.constLabel,
    PlanarForest.toRootedForest, List.map_map, Function.comp_def, LPlanarTree.constLabel]

end LPlanarForest

namespace LPlanarForestAlgebra

noncomputable section

variable {α : Type u} {β : Type w} {γ : Type x} {R : Type v}

/-- The monomial associated to a labelled ordered planar forest. -/
def ofForest [Semiring R] (ts : LPlanarForest α) : LPlanarForestAlgebra α R :=
  MonoidAlgebra.single ts 1

@[simp]
theorem ofForest_empty [Semiring R] :
    ofForest (R := R) (LPlanarForest.empty : LPlanarForest α) = 1 := by
  rw [LPlanarForest.empty]
  change MonoidAlgebra.single ([] : LPlanarForest α) (1 : R) =
    MonoidAlgebra.single ([] : LPlanarForest α) 1
  rfl

@[simp]
theorem ofForest_nil [Semiring R] :
    ofForest (R := R) ([] : LPlanarForest α) = 1 := by
  change MonoidAlgebra.single ([] : LPlanarForest α) (1 : R) =
    MonoidAlgebra.single ([] : LPlanarForest α) 1
  rfl

@[simp]
theorem ofForest_append [Semiring R] (ts us : LPlanarForest α) :
    ofForest (R := R) (ts ++ us) = ofForest ts * ofForest us := by
  rw [ofForest, ofForest, ofForest, MonoidAlgebra.single_mul_single]
  change MonoidAlgebra.single (ts ++ us) (1 : R) =
    MonoidAlgebra.single (ts ++ us) (1 * 1)
  simp

/-- The counit value on a labelled ordered forest monomial. -/
def counitCoeff [Zero R] [One R] (ts : LPlanarForest α) : R := by
  classical
  exact if ts = [] then 1 else 0

@[simp]
theorem counitCoeff_nil [Zero R] [One R] :
    counitCoeff (R := R) ([] : LPlanarForest α) = 1 := by
  classical
  simp [counitCoeff]

@[simp]
theorem counitCoeff_empty [Zero R] [One R] :
    counitCoeff (R := R) (LPlanarForest.empty : LPlanarForest α) = 1 := by
  classical
  rw [LPlanarForest.empty]
  exact counitCoeff_nil

theorem counitCoeff_ne_nil [Zero R] [One R] {ts : LPlanarForest α} (hts : ts ≠ []) :
    counitCoeff (R := R) ts = 0 := by
  classical
  simp [counitCoeff, hts]

theorem counitCoeff_append [Semiring R] (ts us : LPlanarForest α) :
    counitCoeff (R := R) (ts ++ us) = counitCoeff ts * counitCoeff us := by
  classical
  cases ts with
  | nil =>
      simp [counitCoeff]
  | cons t ts =>
      cases us with
      | nil =>
          simp [counitCoeff]
      | cons u us =>
          simp [counitCoeff]

theorem counitCoeff_map [Zero R] [One R] (f : α → β) (ts : LPlanarForest α) :
    counitCoeff (R := R) (LPlanarForest.map f ts) = counitCoeff (R := R) ts := by
  classical
  cases ts with
  | nil =>
      simp [counitCoeff, LPlanarForest.map]
  | cons t ts =>
      simp [counitCoeff, LPlanarForest.map]

theorem counitCoeff_erase [Zero R] [One R] (ts : LPlanarForest α) :
    PlanarForestAlgebra.counitCoeff (R := R) (LPlanarForest.erase ts) =
      counitCoeff (R := R) ts := by
  classical
  cases ts with
  | nil =>
      simp [counitCoeff, PlanarForestAlgebra.counitCoeff, LPlanarForest.erase]
  | cons t ts =>
      simp [counitCoeff, PlanarForestAlgebra.counitCoeff, LPlanarForest.erase]

private def counitMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    LPlanarForest α →* R where
  toFun ts := counitCoeff (R := R) ts
  map_one' := by
    change counitCoeff (R := R) ([] : LPlanarForest α) = 1
    simp
  map_mul' ts us := by
    change counitCoeff (R := R) (ts ++ us) =
      counitCoeff (R := R) ts * counitCoeff (R := R) us
    exact counitCoeff_append (R := R) ts us

/-- The counit algebra homomorphism, sending the empty ordered forest to `1`. -/
def counit (α : Type u) (R : Type v) [CommSemiring R] :
    LPlanarForestAlgebra α R →ₐ[R] R :=
  (MonoidAlgebra.lift R R (LPlanarForest α)) (counitMonoidHom α R)

@[simp]
theorem counit_ofForest [CommSemiring R] (ts : LPlanarForest α) :
    counit α R (ofForest ts) = counitCoeff (R := R) ts := by
  simp [counit, ofForest, counitMonoidHom, counitCoeff]

@[simp]
theorem counit_ofForest_empty [CommSemiring R] :
    counit α R (ofForest (R := R) (LPlanarForest.empty : LPlanarForest α)) = 1 := by
  simp

@[simp]
theorem counit_ofForest_ne_nil [CommSemiring R] {ts : LPlanarForest α} (hts : ts ≠ []) :
    counit α R (ofForest (R := R) ts) = 0 := by
  rw [counit_ofForest]
  exact counitCoeff_ne_nil hts

private def eraseLabelsMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    LPlanarForest α →* PlanarForestAlgebra R where
  toFun ts := PlanarForestAlgebra.ofForest (R := R) (LPlanarForest.erase ts)
  map_one' := by
    change PlanarForestAlgebra.ofForest (R := R) ([] : PlanarForest) = 1
    simp
  map_mul' ts us := by
    change
      PlanarForestAlgebra.ofForest (R := R) (LPlanarForest.erase (ts ++ us)) =
        PlanarForestAlgebra.ofForest (R := R) (LPlanarForest.erase ts) *
          PlanarForestAlgebra.ofForest (R := R) (LPlanarForest.erase us)
    rw [LPlanarForest.erase_append']
    change
      PlanarForestAlgebra.ofForest (R := R)
          (LPlanarForest.erase ts ++ LPlanarForest.erase us) =
        PlanarForestAlgebra.ofForest (R := R) (LPlanarForest.erase ts) *
          PlanarForestAlgebra.ofForest (R := R) (LPlanarForest.erase us)
    exact PlanarForestAlgebra.ofForest_append _ _

/-- Forget labels as an algebra morphism between ordered planar forest algebras. -/
def eraseLabels (α : Type u) (R : Type v) [CommSemiring R] :
    LPlanarForestAlgebra α R →ₐ[R] PlanarForestAlgebra R :=
  (MonoidAlgebra.lift R (PlanarForestAlgebra R) (LPlanarForest α))
    (eraseLabelsMonoidHom α R)

@[simp]
theorem eraseLabels_ofForest [CommSemiring R] (ts : LPlanarForest α) :
    eraseLabels α R (ofForest (R := R) ts) =
      PlanarForestAlgebra.ofForest (R := R) (LPlanarForest.erase ts) := by
  simp [eraseLabels, ofForest, eraseLabelsMonoidHom]

private def constLabelMonoidHom (a : α) (R : Type v) [CommSemiring R] :
    PlanarForest →* LPlanarForestAlgebra α R where
  toFun ts := ofForest (R := R) (LPlanarForest.constLabel a ts)
  map_one' := by
    change ofForest (R := R) (LPlanarForest.constLabel a ([] : PlanarForest)) = 1
    simp [LPlanarForest.constLabel]
  map_mul' ts us := by
    change
      ofForest (R := R) (LPlanarForest.constLabel a (ts ++ us)) =
        ofForest (R := R) (LPlanarForest.constLabel a ts) *
          ofForest (R := R) (LPlanarForest.constLabel a us)
    rw [LPlanarForest.constLabel_append, ofForest_append]

/-- Label every vertex by a fixed label as an algebra morphism. -/
def constLabel (a : α) (R : Type v) [CommSemiring R] :
    PlanarForestAlgebra R →ₐ[R] LPlanarForestAlgebra α R :=
  (MonoidAlgebra.lift R (LPlanarForestAlgebra α R) PlanarForest)
    (constLabelMonoidHom a R)

@[simp]
theorem constLabel_ofForest [CommSemiring R] (a : α) (ts : PlanarForest) :
    constLabel a R (PlanarForestAlgebra.ofForest (R := R) ts) =
      ofForest (R := R) (LPlanarForest.constLabel a ts) := by
  simp [constLabel, PlanarForestAlgebra.ofForest, constLabelMonoidHom]

private def mapLabelsMonoidHom (f : α → β) (R : Type v) [CommSemiring R] :
    LPlanarForest α →* LPlanarForestAlgebra β R where
  toFun ts := ofForest (R := R) (LPlanarForest.map f ts)
  map_one' := by
    change ofForest (R := R) (LPlanarForest.map f ([] : LPlanarForest α)) = 1
    simp [LPlanarForest.map]
  map_mul' ts us := by
    change
      ofForest (R := R) (LPlanarForest.map f (ts ++ us)) =
        ofForest (R := R) (LPlanarForest.map f ts) *
          ofForest (R := R) (LPlanarForest.map f us)
    rw [LPlanarForest.map_append, ofForest_append]

/-- Relabel ordered planar forests as an algebra morphism. -/
def mapLabels (R : Type v) [CommSemiring R] (f : α → β) :
    LPlanarForestAlgebra α R →ₐ[R] LPlanarForestAlgebra β R :=
  (MonoidAlgebra.lift R (LPlanarForestAlgebra β R) (LPlanarForest α))
    (mapLabelsMonoidHom f R)

@[simp]
theorem mapLabels_ofForest [CommSemiring R] (f : α → β) (ts : LPlanarForest α) :
    mapLabels (R := R) f (ofForest (R := R) ts) =
      ofForest (R := R) (LPlanarForest.map f ts) := by
  simp [mapLabels, ofForest, mapLabelsMonoidHom]

@[simp]
theorem mapLabels_id [CommSemiring R] :
    mapLabels (R := R) (fun a : α => a) =
      AlgHom.id R (LPlanarForestAlgebra α R) := by
  refine MonoidAlgebra.algHom_ext ?_ (by ext)
  intro ts
  change
    mapLabels (R := R) (fun a : α => a) (ofForest (R := R) ts) =
      (AlgHom.id R (LPlanarForestAlgebra α R)) (ofForest (R := R) ts)
  rw [mapLabels_ofForest, LPlanarForest.map_id]
  simp

theorem mapLabels_comp [CommSemiring R] (g : β → γ) (f : α → β) :
    (mapLabels (R := R) g).comp (mapLabels (R := R) f) =
      mapLabels (R := R) (g ∘ f) := by
  refine MonoidAlgebra.algHom_ext ?_ (by ext)
  intro ts
  change
    mapLabels (R := R) g
        (mapLabels (R := R) f (ofForest (R := R) ts)) =
      mapLabels (R := R) (g ∘ f) (ofForest (R := R) ts)
  rw [mapLabels_ofForest, mapLabels_ofForest, mapLabels_ofForest, LPlanarForest.map_comp]

private def toLForestAlgebraMonoidHom (α : Type u) (R : Type v) [CommSemiring R] :
    LPlanarForest α →* LForestAlgebra α R where
  toFun ts := LForestAlgebra.ofForest (R := R) (LPlanarForest.toRootedForest ts)
  map_one' := by
    change LForestAlgebra.ofForest (R := R) (LPlanarForest.toRootedForest []) = 1
    simp
  map_mul' ts us := by
    change
      LForestAlgebra.ofForest (R := R) (LPlanarForest.toRootedForest (ts ++ us)) =
        LForestAlgebra.ofForest (R := R) (LPlanarForest.toRootedForest ts) *
          LForestAlgebra.ofForest (R := R) (LPlanarForest.toRootedForest us)
    rw [LPlanarForest.toRootedForest_append, LForestAlgebra.ofForest_add]

/-- Forget planar order as an algebra morphism to the commutative labelled forest algebra. -/
def toLForestAlgebra (α : Type u) (R : Type v) [CommSemiring R] :
    LPlanarForestAlgebra α R →ₐ[R] LForestAlgebra α R :=
  (MonoidAlgebra.lift R (LForestAlgebra α R) (LPlanarForest α))
    (toLForestAlgebraMonoidHom α R)

@[simp]
theorem toLForestAlgebra_ofForest [CommSemiring R] (ts : LPlanarForest α) :
    toLForestAlgebra α R (ofForest ts) =
      LForestAlgebra.ofForest (R := R) (LPlanarForest.toRootedForest ts) := by
  simp [toLForestAlgebra, ofForest, toLForestAlgebraMonoidHom]

@[simp]
theorem eraseLabels_comp_toLForestAlgebra [CommSemiring R] :
    (LForestAlgebra.eraseLabels (α := α) R).comp (toLForestAlgebra α R) =
      (PlanarForestAlgebra.toForestAlgebra R).comp (eraseLabels α R) := by
  refine MonoidAlgebra.algHom_ext ?_ (by ext)
  intro ts
  change
    LForestAlgebra.eraseLabels (α := α) R
        (toLForestAlgebra α R (ofForest (R := R) ts)) =
      PlanarForestAlgebra.toForestAlgebra R
        (eraseLabels α R (ofForest (R := R) ts))
  rw [toLForestAlgebra_ofForest, eraseLabels_ofForest, LForestAlgebra.eraseLabels_ofForest,
    PlanarForestAlgebra.toForestAlgebra_ofForest]
  simp

@[simp]
theorem counit_comp_toLForestAlgebra [CommSemiring R] :
    (LForestAlgebra.counit α R).comp (toLForestAlgebra α R) = counit α R := by
  refine MonoidAlgebra.algHom_ext ?_ (by ext)
  intro ts
  change
    LForestAlgebra.counit α R
        (toLForestAlgebra α R (ofForest (R := R) ts)) =
      counit α R (ofForest (R := R) ts)
  rw [toLForestAlgebra_ofForest, LForestAlgebra.counit_ofForest, counit_ofForest]
  classical
  cases ts with
  | nil =>
      simp
  | cons t ts =>
      have hne : LPlanarForest.toRootedForest (t :: ts) ≠ 0 := by
        have horder :
            0 < LRootedForest.order (LPlanarForest.toRootedForest (t :: ts)) := by
          rw [LPlanarForest.order_toRootedForest]
          change 0 < LPlanarTree.order t + LPlanarForest.order ts
          exact Nat.add_pos_left (PLTree.order_pos t) (LPlanarForest.order ts)
        exact (LRootedForest.order_pos_iff_ne_zero _).1 horder
      rw [LForestAlgebra.counitCoeff_ne_zero hne]
      simp [counitCoeff]

theorem eraseLabels_comp_mapLabels [CommSemiring R] (f : α → β) :
    (eraseLabels β R).comp (mapLabels (R := R) f) =
      eraseLabels α R := by
  refine MonoidAlgebra.algHom_ext ?_ (by ext)
  intro ts
  change
    eraseLabels β R
        (mapLabels (R := R) f (ofForest (R := R) ts)) =
      eraseLabels α R (ofForest (R := R) ts)
  rw [mapLabels_ofForest, eraseLabels_ofForest, eraseLabels_ofForest]
  simp

theorem eraseLabels_comp_constLabel [CommSemiring R] (a : α) :
    (eraseLabels α R).comp (constLabel a R) =
      AlgHom.id R (PlanarForestAlgebra R) := by
  refine MonoidAlgebra.algHom_ext ?_ (by ext)
  intro ts
  change
    eraseLabels α R
        (constLabel a R (PlanarForestAlgebra.ofForest (R := R) ts)) =
      PlanarForestAlgebra.ofForest (R := R) ts
  rw [constLabel_ofForest, eraseLabels_ofForest]
  simp

theorem constLabel_injective [CommSemiring R] (a : α) :
    Function.Injective (constLabel a R : PlanarForestAlgebra R → LPlanarForestAlgebra α R) := by
  intro x y h
  have hErase := congrArg (eraseLabels α R) h
  simpa [← AlgHom.comp_apply, eraseLabels_comp_constLabel] using hErase

theorem mapLabels_comp_constLabel [CommSemiring R] (f : α → β) (a : α) :
    (mapLabels (R := R) f).comp (constLabel a R) =
      constLabel (f a) R := by
  refine MonoidAlgebra.algHom_ext ?_ (by ext)
  intro ts
  change
    mapLabels (R := R) f
        (constLabel a R (PlanarForestAlgebra.ofForest (R := R) ts)) =
      constLabel (f a) R (PlanarForestAlgebra.ofForest (R := R) ts)
  rw [constLabel_ofForest, mapLabels_ofForest, constLabel_ofForest]
  rw [LPlanarForest.map_constLabel]

/-- Algebra characters on the labelled ordered planar forest algebra. -/
abbrev Character (α : Type u) (R : Type v) [CommSemiring R] : Type (max u v) :=
  LPlanarForestAlgebra α R →ₐ[R] R

namespace Character

variable [CommSemiring R]

/-- Evaluate a character on the monomial associated to a labelled ordered planar forest. -/
def evalForest (χ : Character α R) (ts : LPlanarForest α) : R :=
  χ (ofForest (R := R) ts)

@[simp]
theorem evalForest_empty (χ : Character α R) :
    χ.evalForest (LPlanarForest.empty : LPlanarForest α) = 1 := by
  simp [evalForest]

@[simp]
theorem evalForest_nil (χ : Character α R) :
    χ.evalForest ([] : LPlanarForest α) = 1 := by
  simp [evalForest]

@[simp]
theorem evalForest_append (χ : Character α R) (ts us : LPlanarForest α) :
    χ.evalForest (ts ++ us) = χ.evalForest ts * χ.evalForest us := by
  simp [evalForest]

@[ext]
theorem ext {χ ψ : Character α R} (h : ∀ ts, χ.evalForest ts = ψ.evalForest ts) :
    χ = ψ := by
  refine MonoidAlgebra.algHom_ext ?_ (by ext)
  intro ts
  exact h ts

/-- Pull a labelled commutative forest character back by forgetting planar order. -/
def comapToLForestAlgebra (χ : LForestAlgebra.Character α R) : Character α R :=
  χ.comp (toLForestAlgebra α R)

/-- Pull an unlabelled ordered planar forest character back by forgetting labels. -/
def comapEraseLabels (χ : PlanarForestAlgebra.Character R) : Character α R :=
  χ.comp (eraseLabels α R)

/-- Pull a labelled ordered planar forest character back along constant labelling. -/
def comapConstLabel (a : α) (χ : Character α R) :
    PlanarForestAlgebra.Character R :=
  χ.comp (constLabel a R)

/-- Pull a labelled ordered planar forest character back along relabelling. -/
def comapMapLabels (f : α → β) (χ : Character β R) : Character α R :=
  χ.comp (mapLabels (R := R) f)

@[simp]
theorem comapToLForestAlgebra_evalForest
    (χ : LForestAlgebra.Character α R) (ts : LPlanarForest α) :
    (comapToLForestAlgebra χ).evalForest ts =
      χ.evalForest (LPlanarForest.toRootedForest ts) := by
  change
    χ (toLForestAlgebra α R (ofForest (R := R) ts)) =
      χ (LForestAlgebra.ofForest (R := R) (LPlanarForest.toRootedForest ts))
  rw [toLForestAlgebra_ofForest]

@[simp]
theorem comapEraseLabels_evalForest
    (χ : PlanarForestAlgebra.Character R) (ts : LPlanarForest α) :
    (comapEraseLabels (α := α) χ).evalForest ts =
      χ.evalForest (LPlanarForest.erase ts) := by
  change
    χ (eraseLabels α R (ofForest (R := R) ts)) =
      χ (PlanarForestAlgebra.ofForest (R := R) (LPlanarForest.erase ts))
  rw [eraseLabels_ofForest]

@[simp]
theorem comapConstLabel_evalForest
    (a : α) (χ : Character α R) (ts : PlanarForest) :
    (comapConstLabel a χ).evalForest ts =
      χ.evalForest (LPlanarForest.constLabel a ts) := by
  change
    χ (constLabel a R (PlanarForestAlgebra.ofForest (R := R) ts)) =
      χ (ofForest (R := R) (LPlanarForest.constLabel a ts))
  rw [constLabel_ofForest]

@[simp]
theorem comapMapLabels_evalForest
    (f : α → β) (χ : Character β R) (ts : LPlanarForest α) :
    (comapMapLabels f χ).evalForest ts =
      χ.evalForest (LPlanarForest.map f ts) := by
  change
    χ (mapLabels (R := R) f (ofForest (R := R) ts)) =
      χ (ofForest (R := R) (LPlanarForest.map f ts))
  rw [mapLabels_ofForest]

@[simp]
theorem comapMapLabels_id (χ : Character α R) :
    comapMapLabels (fun a : α => a) χ = χ := by
  simp [comapMapLabels]

theorem comapMapLabels_comp (g : β → γ) (f : α → β) (χ : Character γ R) :
    comapMapLabels f (comapMapLabels g χ) = comapMapLabels (g ∘ f) χ := by
  simp [comapMapLabels, AlgHom.comp_assoc, mapLabels_comp]

theorem comapEraseLabels_comapMapLabels (f : α → β)
    (χ : PlanarForestAlgebra.Character R) :
    comapMapLabels f (comapEraseLabels (α := β) χ) =
      comapEraseLabels (α := α) χ := by
  simp [comapMapLabels, comapEraseLabels, AlgHom.comp_assoc,
    eraseLabels_comp_mapLabels]

theorem comapConstLabel_comapMapLabels (f : α → β) (a : α)
    (χ : Character β R) :
    comapConstLabel a (comapMapLabels f χ) = comapConstLabel (f a) χ := by
  simp [comapConstLabel, comapMapLabels, AlgHom.comp_assoc,
    mapLabels_comp_constLabel]

theorem comapConstLabel_comapEraseLabels (a : α)
    (χ : PlanarForestAlgebra.Character R) :
    comapConstLabel a (comapEraseLabels (α := α) χ) = χ := by
  apply PlanarForestAlgebra.Character.ext
  intro ts
  change
    χ ((eraseLabels α R)
        (constLabel a R (PlanarForestAlgebra.ofForest (R := R) ts))) =
      χ (PlanarForestAlgebra.ofForest (R := R) ts)
  rw [constLabel_ofForest, eraseLabels_ofForest]
  simp

@[simp]
theorem comapToLForestAlgebra_counit :
    comapToLForestAlgebra (α := α) (R := R) (LForestAlgebra.counit α R) =
      counit α R := by
  exact counit_comp_toLForestAlgebra

@[simp]
theorem comapEraseLabels_counit :
    comapEraseLabels (α := α) (PlanarForestAlgebra.counit R) = counit α R := by
  apply ext
  intro ts
  rw [comapEraseLabels_evalForest]
  change
    PlanarForestAlgebra.counit R
        (PlanarForestAlgebra.ofForest (R := R) (LPlanarForest.erase ts)) =
      counit α R (ofForest (R := R) ts)
  rw [PlanarForestAlgebra.counit_ofForest, counit_ofForest, counitCoeff_erase]

theorem comapConstLabel_counit (a : α) :
    comapConstLabel a (counit α R) = PlanarForestAlgebra.counit R := by
  rw [← comapEraseLabels_counit (α := α) (R := R)]
  exact comapConstLabel_comapEraseLabels a (PlanarForestAlgebra.counit R)

end Character

end

end LPlanarForestAlgebra

end HopfAlgebras
