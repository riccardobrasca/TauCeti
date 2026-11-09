/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.LinearCombination

/-!
# Seeley's reflection coefficients

There are real coefficients `c k`, `k ∈ ℕ`, such that `∑ₖ c k (-2 ^ k) ^ n = 1` for every
`n : ℕ`, and such that `∑ₖ |c k| 2 ^ (k n)` converges for every `n`
(`TauCeti.exists_smooth_halfspace_reflection_coefficients`). These are the coefficients of
Seeley's extension of a smooth function `f` on a closed halfspace `{t ≥ 0}` to the whole space,
`f (x, t) = ∑ₖ c k f (x, -2 ^ k t)` for `t < 0`: the first condition makes all the derivatives
of the two sides agree on the boundary hyperplane, and the second makes the series of derivatives
converge.

The proof follows Seeley. The entire series `F z = ∑ₙ aₙ zⁿ` with `a₀ = 1` and
`(2 ^ (n + 1) - 1) aₙ₊₁ = -2 aₙ` satisfies `F (2 z) = (1 - 2 z) F z`, so `F` vanishes at every
power `2 ^ n`. Dividing its coefficients by `1 + 2 ^ n` gives a series `C` with
`C z + C (2 z) = F z`, hence `C (2 ^ n) = (-1) ^ n C 1`. Since the coefficients `aₙ` alternate in
sign and decrease fast, grouping the terms of `C 1` in pairs shows `C 1 > 0`, and
`c k = aₖ / ((1 + 2 ^ k) C 1)` are the required coefficients.

## References

* R. T. Seeley, *Extension of `C^∞` functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public section

open Filter Finset
open scoped Topology

noncomputable section

namespace TauCeti

private def reflectionAux : ℕ → ℝ
  | 0 => 1
  | n + 1 => (-2 / ((2 : ℝ) ^ (n + 1) - 1)) * reflectionAux n

private theorem reflectionAux_zero : reflectionAux 0 = 1 := rfl

private theorem reflectionAux_succ (n : ℕ) :
    reflectionAux (n + 1) = (-2 / ((2 : ℝ) ^ (n + 1) - 1)) * reflectionAux n := rfl

private theorem reflectionAux_den_pos (n : ℕ) : 0 < (2 : ℝ) ^ (n + 1) - 1 := by
  have := one_lt_pow₀ (show (1 : ℝ) < 2 by norm_num) (Nat.succ_ne_zero n)
  simpa only [Nat.succ_eq_add_one] using sub_pos.mpr this

private theorem summable_reflectionAux (z : ℝ) :
    Summable (fun n ↦ reflectionAux n * z ^ n) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  have ht : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually_ge_atTop (4 * |z| + 1)] with n hn
  have hd := reflectionAux_den_pos n
  calc
    ‖reflectionAux (n + 1) * z ^ (n + 1)‖ =
        (2 * |z| / ((2 : ℝ) ^ (n + 1) - 1)) * ‖reflectionAux n * z ^ n‖ := by
      rw [reflectionAux_succ, pow_succ z]
      simp only [norm_mul, norm_div, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
        abs_of_pos hd]
      ring
    _ ≤ (1 / 2 : ℝ) * ‖reflectionAux n * z ^ n‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (div_le_iff₀ hd).mpr
      linarith

private theorem reflectionAux_rec (n : ℕ) :
    ((2 : ℝ) ^ (n + 1) - 1) * reflectionAux (n + 1) = -2 * reflectionAux n := by
  rw [reflectionAux_succ]
  field_simp [(reflectionAux_den_pos n).ne']

private def reflectionSeries (z : ℝ) : ℝ := ∑' n, reflectionAux n * z ^ n

private theorem reflectionSeries_two_mul (z : ℝ) :
    reflectionSeries (2 * z) = (1 - 2 * z) * reflectionSeries z := by
  have hterm (n : ℕ) : reflectionAux (n + 1) * (2 * z) ^ (n + 1) =
      reflectionAux (n + 1) * z ^ (n + 1) - 2 * z * (reflectionAux n * z ^ n) := by
    rw [mul_pow, pow_succ z]
    linear_combination z * z ^ n * reflectionAux_rec n
  have hs := (summable_reflectionAux z).tsum_eq_zero_add
  have hs₂ := (summable_reflectionAux (2 * z)).tsum_eq_zero_add
  simp only [reflectionAux_zero, pow_zero, mul_one] at hs hs₂
  change (∑' n, reflectionAux n * (2 * z) ^ n) =
    (1 - 2 * z) * ∑' n, reflectionAux n * z ^ n
  rw [hs₂, tsum_congr hterm,
    ((summable_nat_add_iff 1).2 (summable_reflectionAux z)).tsum_sub
      ((summable_reflectionAux z).mul_left (2 * z)), tsum_mul_left]
  linarith [hs]

private theorem reflectionSeries_pow_two (n : ℕ) :
    reflectionSeries ((2 : ℝ) ^ n) = 0 := by
  induction n with
  | zero =>
    have h := reflectionSeries_two_mul (1 / 2)
    norm_num at h ⊢
    exact h
  | succ n ih =>
    rw [pow_succ', reflectionSeries_two_mul, ih, mul_zero]

private def reflectionCoeff (n : ℕ) : ℝ := reflectionAux n / (1 + (2 : ℝ) ^ n)

private theorem reflectionCoeff_den_pos (n : ℕ) : 0 < 1 + (2 : ℝ) ^ n := by positivity

private theorem summable_reflectionCoeff (z : ℝ) :
    Summable (fun n ↦ reflectionCoeff n * z ^ n) := by
  refine (summable_reflectionAux z).abs.of_norm_bounded fun n ↦ ?_
  simp only [reflectionCoeff, norm_mul, norm_div, Real.norm_eq_abs, abs_mul,
    abs_of_pos (reflectionCoeff_den_pos n)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply div_le_self (abs_nonneg _)
  have := pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) n
  linarith

private def reflectionMomentSeries (z : ℝ) : ℝ := ∑' n, reflectionCoeff n * z ^ n

private theorem reflectionMomentSeries_add_two_mul (z : ℝ) :
    reflectionMomentSeries z + reflectionMomentSeries (2 * z) = reflectionSeries z := by
  rw [reflectionMomentSeries, reflectionMomentSeries,
    ← (summable_reflectionCoeff z).tsum_add (summable_reflectionCoeff (2 * z))]
  apply tsum_congr
  intro n
  rw [mul_pow]
  dsimp only [reflectionCoeff]
  field_simp [(reflectionCoeff_den_pos n).ne']

private theorem reflectionMomentSeries_pow_two (n : ℕ) :
    reflectionMomentSeries ((2 : ℝ) ^ n) = (-1 : ℝ) ^ n * reflectionMomentSeries 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := reflectionMomentSeries_add_two_mul ((2 : ℝ) ^ n)
    rw [reflectionSeries_pow_two, ih] at h
    rw [pow_succ', pow_succ' (-1)]
    linarith

private theorem reflectionAux_sign (n : ℕ) : 0 < (-1 : ℝ) ^ n * reflectionAux n := by
  induction n with
  | zero => norm_num [reflectionAux_zero]
  | succ n ih =>
    rw [reflectionAux_succ, pow_succ]
    have hp := mul_pos (div_pos (show (0 : ℝ) < 2 by norm_num) (reflectionAux_den_pos n)) ih
    convert hp using 1; ring

private theorem reflectionAux_even_pos (n : ℕ) : 0 < reflectionAux (2 * n) := by
  simpa only [pow_mul, neg_one_sq, one_pow, one_mul] using reflectionAux_sign (2 * n)

private theorem reflectionCoeff_pair_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ reflectionCoeff (2 * n) + reflectionCoeff (2 * n + 1) := by
  have hx : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * n) := by
    have := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (show 1 ≤ 2 * n by omega)
    simpa using this
  have hd : 0 < (2 : ℝ) ^ (2 * n + 1) - 1 := reflectionAux_den_pos (2 * n)
  have hc := (reflectionAux_even_pos n).le
  dsimp only [reflectionCoeff]
  rw [reflectionAux_succ]
  have hp : 0 ≤ 1 / (1 + (2 : ℝ) ^ (2 * n)) -
      2 / (((2 : ℝ) ^ (2 * n + 1) - 1) * (1 + (2 : ℝ) ^ (2 * n + 1))) := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (mul_pos hd (reflectionCoeff_den_pos _))
      (reflectionCoeff_den_pos _)).mpr
    rw [pow_succ]
    nlinarith [sq_nonneg ((2 : ℝ) ^ (2 * n) - 1)]
  convert mul_nonneg hc hp using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem reflectionMomentSeries_one_pos : 0 < reflectionMomentSeries 1 := by
  have hs : Summable reflectionCoeff := by simpa using summable_reflectionCoeff 1
  have he : Summable (fun n ↦ reflectionCoeff (2 * n)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  have ho : Summable (fun n ↦ reflectionCoeff (2 * n + 1)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  have heq := tsum_even_add_odd he ho
  have hshift := (he.add ho).sum_add_tsum_nat_add 2
  have htail : 0 ≤ ∑' n, (reflectionCoeff (2 * (n + 2)) +
      reflectionCoeff (2 * (n + 2) + 1)) :=
    tsum_nonneg fun n ↦ reflectionCoeff_pair_nonneg (by omega)
  have hfirst : 0 < ∑ n ∈ range 2,
      (reflectionCoeff (2 * n) + reflectionCoeff (2 * n + 1)) := by
    norm_num [Finset.sum_range_succ, reflectionCoeff, reflectionAux]
  rw [← he.tsum_add ho] at heq
  have hC : reflectionMomentSeries 1 = ∑' n, reflectionCoeff n := by
    simp only [reflectionMomentSeries, one_pow, mul_one]
  rw [hC, ← heq, ← hshift]
  exact add_pos_of_pos_of_nonneg hfirst htail

/-- **Seeley's reflection coefficients.** There are real coefficients `c k` with
`∑ₖ c k (-2 ^ k) ^ n = 1` for every `n`, whose absolute moments `∑ₖ |c k| 2 ^ (k n)` all
converge. -/
theorem exists_smooth_halfspace_reflection_coefficients :
    ∃ c : ℕ → ℝ,
      (∀ n : ℕ, HasSum (fun k ↦ c k * (-(2 : ℝ) ^ k) ^ n) 1) ∧
      (∀ n : ℕ, Summable (fun k ↦ |c k| * (2 : ℝ) ^ (k * n))) := by
  let C := reflectionMomentSeries 1
  have hC : C ≠ 0 := reflectionMomentSeries_one_pos.ne'
  refine ⟨fun k ↦ reflectionCoeff k / C, ?_, ?_⟩
  · intro n
    have hs := ((summable_reflectionCoeff ((2 : ℝ) ^ n)).hasSum.div_const C).mul_left
      ((-1 : ℝ) ^ n)
    have heq : (∑' k, reflectionCoeff k * ((2 : ℝ) ^ n) ^ k) =
        (-1 : ℝ) ^ n * C := reflectionMomentSeries_pow_two n
    rw [heq] at hs
    have hv : (-1 : ℝ) ^ n * (((-1 : ℝ) ^ n * C) / C) = 1 := by
      rw [mul_div_cancel_right₀ _ hC, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hv] at hs
    convert hs using 1
    ext k
    rw [neg_pow, ← pow_mul, ← pow_mul, Nat.mul_comm k n]
    ring
  · intro n
    have hs := (summable_reflectionCoeff ((2 : ℝ) ^ n)).abs.div_const |C|
    convert hs using 1
    ext k
    rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos (show (0 : ℝ) < 2 by norm_num),
      ← pow_mul, Nat.mul_comm n k]
    ring

end TauCeti
