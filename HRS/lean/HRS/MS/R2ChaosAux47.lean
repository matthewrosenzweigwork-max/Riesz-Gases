import HRS.MS.R2ChaosAux46

/-!
# HRS.MS.R2ChaosAux47 -- (e) part 2: `p`-th moments of `L²(dt)` norms from pointwise-in-time moments

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

* `s94_norm_L2path_pow_le`: `‖L²path g‖^p ≤ T^{p/2-1} ∫_0^T |g|^p dt` (`p ≥ 2`; the junk value `0` for `g ∉ L²` is harmless).
* `s94_moment_L2path`: if `‖f(t,·)‖_{L^p(P)} ≤ C` for `t ∈ [0,T]` then `E ‖L²path f(·,ζ)‖^p ≤ T^{p/2} C^p`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

section MomentL2

variable {T : ℝ}

theorem s94_norm_L2path_pow_le (hT : 0 < T) {g : ℝ → ℝ} (hg : Measurable g) {p : ℝ} (hp : 2 ≤ p) :
    ENNReal.ofReal (‖r2L2Path T g‖ ^ p) ≤
      ENNReal.ofReal (T ^ (p / 2 - 1)) * ∫⁻ t in Set.Icc (0 : ℝ) T, ‖g t‖ₑ ^ p := by
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  have hp0 : 0 < p := by linarith
  have hνu : ν Set.univ = ENNReal.ofReal T := by
    simp [hν, Measure.restrict_apply_univ]
  have h1 : ENNReal.ofReal (‖r2L2Path T g‖ ^ p) ≤ eLpNorm g 2 ν ^ p := by
    by_cases hm : MemLp g 2 ν
    · have : ‖r2L2Path T g‖ = (eLpNorm g 2 ν).toReal := by
        rw [s94_r2L2Path_eq hm]
        exact Lp.norm_toLp _ _
      rw [this, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le, ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
    · rw [s94_r2L2Path_eq_zero hm]
      simp [Real.zero_rpow hp0.ne']
  have hsm : AEStronglyMeasurable g ν := hg.aestronglyMeasurable
  have h2 : eLpNorm g 2 ν ≤ eLpNorm g (ENNReal.ofReal p) ν * ν Set.univ ^ (1 / 2 - 1 / p) := by
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := ENNReal.ofReal p)
      (by rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]; exact ENNReal.ofReal_le_ofReal hp) hsm
    simpa [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ p)] using this
  have h3 : eLpNorm g (ENNReal.ofReal p) ν ^ p = ∫⁻ t, ‖g t‖ₑ ^ p ∂ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hsm,
      ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  calc ENNReal.ofReal (‖r2L2Path T g‖ ^ p) ≤ eLpNorm g 2 ν ^ p := h1
    _ ≤ (eLpNorm g (ENNReal.ofReal p) ν * ν Set.univ ^ (1 / 2 - 1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h2 hp0.le
    _ = eLpNorm g (ENNReal.ofReal p) ν ^ p * (ν Set.univ) ^ (p / 2 - 1) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul]
        congr 2
        field_simp
    _ = ENNReal.ofReal (T ^ (p / 2 - 1)) * ∫⁻ t, ‖g t‖ₑ ^ p ∂ν := by
        rw [h3, hνu, ENNReal.ofReal_rpow_of_pos hT, mul_comm]

theorem s94_moment_L2path {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hT : 0 < T) {f : ℝ × Ω → ℝ} (hf : Measurable f) {p : ℝ} (hp : 2 ≤ p) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) T, eLpNorm (fun ζ => f (t, ζ)) (ENNReal.ofReal p) P ≤ ENNReal.ofReal C) :
    ∫⁻ ζ, ENNReal.ofReal (‖r2L2Path T (fun t => f (t, ζ))‖ ^ p) ∂P ≤ ENNReal.ofReal (T ^ (p / 2) * C ^ p) := by
  have hp0 : 0 < p := by linarith
  have hmz : ∀ ζ, Measurable fun t => f (t, ζ) := fun ζ => hf.comp (measurable_prodMk_right (y := ζ))
  have hf2 : Measurable fun q : Ω × ℝ => ‖f (q.2, q.1)‖ₑ ^ p := (hf.comp measurable_swap).enorm.pow_const p
  calc ∫⁻ ζ, ENNReal.ofReal (‖r2L2Path T (fun t => f (t, ζ))‖ ^ p) ∂P
      ≤ ∫⁻ ζ, ENNReal.ofReal (T ^ (p / 2 - 1)) * ∫⁻ t in Set.Icc (0 : ℝ) T, ‖f (t, ζ)‖ₑ ^ p ∂volume ∂P :=
        lintegral_mono fun ζ => s94_norm_L2path_pow_le hT (hmz ζ) hp
    _ = ENNReal.ofReal (T ^ (p / 2 - 1)) * ∫⁻ ζ, ∫⁻ t in Set.Icc (0 : ℝ) T, ‖f (t, ζ)‖ₑ ^ p ∂volume ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (T ^ (p / 2 - 1)) * ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ζ, ‖f (t, ζ)‖ₑ ^ p ∂P :=
        by rw [lintegral_lintegral_swap hf2.aemeasurable]
    _ ≤ ENNReal.ofReal (T ^ (p / 2 - 1)) * ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (C ^ p) := by
        have hbdd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ‖f (t, ζ)‖ₑ ^ p ∂P ≤ ENNReal.ofReal (C ^ p) := by
          intro t ht
          have hsm : AEStronglyMeasurable (fun ζ => f (t, ζ)) P :=
            (hf.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable
          have : ∫⁻ ζ, ‖f (t, ζ)‖ₑ ^ p ∂P = eLpNorm (fun ζ => f (t, ζ)) (ENNReal.ofReal p) P ^ p := by
            rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hsm,
              ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
          rw [this, ← ENNReal.ofReal_rpow_of_nonneg hC0 hp0.le]
          exact ENNReal.rpow_le_rpow (hC t ht) hp0.le
        exact mul_le_mul_right (setLIntegral_mono' measurableSet_Icc hbdd) _
    _ = ENNReal.ofReal (T ^ (p / 2) * C ^ p) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : T ^ (p / 2) = T ^ (p / 2 - 1) * T := by
          rw [← Real.rpow_add_one hT.ne']; ring_nf
        rw [this]; ring

end MomentL2

end HRS.MS.R2Chaos
