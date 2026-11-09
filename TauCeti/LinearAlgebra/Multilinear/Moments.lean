/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators

/-!
# Scalar moments and affine substitutions in multilinear maps

Let `B` be a multilinear map of `ι` arguments, with `ι` finite. Inserting the affine
expression `u i + a • v i` in every argument, the value `B (u + a • v)` is a polynomial in the
scalar `a` of degree at most the number of arguments: the coefficient of `a ^ #Sᶜ` is
`B (S.piecewise u v)`. Hence, if finitely many weights `c k` and scalars `a k` have
`∑ₖ c k * a k ^ j = 1` for every `j` up to the number of arguments, then
`∑ₖ c k • B (u + a k • v) = B (u + v)`.

This is the algebraic identity behind reflection extensions of functions across a hyperplane:
it compares the multilinear derivatives of a reflected sum `∑ₖ c k f (x', a k t)` on the
hyperplane with those of `f`.

## Main results

* `MultilinearMap.map_add_smul_univ`: the expansion of `B (u + a • v)` in powers of `a`.
* `MultilinearMap.sum_smul_apply_add_smul_of_moments`: the moment identity.
-/

public section

open Finset

variable {R : Type*} [CommSemiring R] {ι κ : Type*} [Fintype ι] [Fintype κ]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {F : Type*} [AddCommMonoid F] [Module R F]

namespace MultilinearMap

/-- A simultaneous affine scalar substitution in all arguments of a multilinear map expands as a
sum over the sets `S` of arguments in which the unscaled vector is kept. -/
theorem map_add_smul_univ [DecidableEq ι] (B : MultilinearMap R M F) (a : R) (u v : ∀ i, M i) :
    B (u + a • v) = ∑ S : Finset ι, a ^ #Sᶜ • B (S.piecewise u v) := by
  rw [B.map_add_univ]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  have h := B.map_piecewise_smul (fun _ ↦ a) (S.piecewise u v) Sᶜ
  rw [Finset.prod_const] at h
  rw [← h]
  congr 1
  ext i
  by_cases hi : i ∈ S <;> simp [hi]

/-- If the weights `c k` and the scalars `a k` have `∑ₖ c k * a k ^ j = 1` for every `j` up to the
number of arguments of a multilinear map `B`, then the weighted sum of the affine substitutions
`B (u + a k • v)` is `B (u + v)`. -/
theorem sum_smul_apply_add_smul_of_moments (B : MultilinearMap R M F) (a c : κ → R)
    (h : ∀ j ≤ Fintype.card ι, ∑ k, c k * a k ^ j = 1) (u v : ∀ i, M i) :
    ∑ k, c k • B (u + a k • v) = B (u + v) := by
  classical
  simp_rw [B.map_add_smul_univ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, B.map_add_univ]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [← Finset.sum_smul, h _ (Finset.card_le_univ _), one_smul]

end MultilinearMap
