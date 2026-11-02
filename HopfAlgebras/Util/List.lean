/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# List lemmas

Small general-purpose `List` lemmas used across the library.
-/

namespace List

/-- Summing over `l.attach` equals summing over `l`; removes the `attach`
plumbing that recursive definitions introduce for termination. -/
theorem sum_attach_map {α : Type*} {M : Type*} [AddMonoid M]
    (l : List α) (f : α → M) :
    (l.attach.map fun i => f i.1).sum = (l.map f).sum :=
  congrArg List.sum (attach_map_val (l := l) (f := f))

/-- Choose one occurrence, retaining the other factors, including repeats. -/
def selections {α : Type*} : List α → List (α × List α)
  | [] => []
  | a :: as => (a, as) :: (selections as).map (fun p => (p.1, a :: p.2))

@[simp] theorem selections_length {α : Type*} (xs : List α) :
    (selections xs).length = xs.length := by
  induction xs <;> simp [selections, *]

theorem selections_perm {α : Type*} {xs : List α} {p : α × List α}
    (h : p ∈ selections xs) : (p.1 :: p.2).Perm xs := by
  induction xs generalizing p with
  | nil => simp [selections] at h
  | cons a xs ih =>
    simp only [selections, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩
    · exact .refl _
    · exact (List.Perm.swap _ _ _).trans ((ih hq).cons a)

theorem selections_rest_length {α : Type*} {xs : List α} {p : α × List α}
    (h : p ∈ selections xs) : p.2.length + 1 = xs.length := by
  simpa using (selections_perm h).length_eq

theorem selections_map {α β : Type*} (f : α → β) (xs : List α) :
    selections (xs.map f) = (selections xs).map (fun p => (f p.1, p.2.map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [selections, ih, List.map_map, Function.comp_def]

end List
