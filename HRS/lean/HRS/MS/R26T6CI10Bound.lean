import HRS.MS.GenPathAux6

/-!
# S11.1 I10: L³-to-L¹ interval inequality with sharp T^(2/3) scaling
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

theorem r26t6c_L3_l1_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : ℝ) (hT : 0 ≤ T)
    (g : Lp E 3 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    ∫ t in Set.Icc (0 : ℝ) T, ‖(g : ℝ → E) t‖ ≤
      T ^ (2 / 3 : ℝ) * ‖g‖ := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T)
  have hmem : MemLp (g : ℝ → E) 3 μ := Lp.memLp g
  have hae : AEStronglyMeasurable (g : ℝ → E) μ := hmem.aestronglyMeasurable
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (p := 1) (q := 3) (by norm_num) hae
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (3 : ℝ≥0∞).toReal) =
      (2 / 3 : ℝ) := by norm_num [ENNReal.toReal_ofNat]
  rw [hexp] at h1
  have hμu : μ Set.univ = ENNReal.ofReal T := by
    rw [show μ = volume.restrict (Set.Icc (0 : ℝ) T) by rfl,
      Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hint : ∫ t in Set.Icc (0 : ℝ) T, ‖(g : ℝ → E) t‖ =
      (eLpNorm (g : ℝ → E) 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    · exact integral_norm_eq_lintegral_enorm hae
    · exact hae
  rw [hint]
  have h2 : eLpNorm (g : ℝ → E) 3 μ ≠ ⊤ := hmem.eLpNorm_ne_top
  have h3 : μ Set.univ ^ (2 / 3 : ℝ) ≠ ⊤ := by
    rw [hμu]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  calc (eLpNorm (g : ℝ → E) 1 μ).toReal
      ≤ (eLpNorm (g : ℝ → E) 3 μ * μ Set.univ ^ (2 / 3 : ℝ)).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top h2 h3) h1
    _ = T ^ (2 / 3 : ℝ) * ‖g‖ := by
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, hμu,
        ENNReal.toReal_ofReal hT, Lp.norm_def, mul_comm]

theorem r26t6c_time_power_le_max (T : ℝ) (hT : 0 < T) :
    T ^ (2 / 3 : ℝ) ≤ max 1 T := by
  rcases le_total T 1 with hle | hge
  · have hpow : T ^ (2 / 3 : ℝ) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_ge hT hle
          (by norm_num : (0 : ℝ) ≤ 2 / 3)
    exact hpow.trans (le_max_left _ _)
  · have hpow : T ^ (2 / 3 : ℝ) ≤ T := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hge
          (by norm_num : (2 / 3 : ℝ) ≤ 1)
    exact hpow.trans (le_max_right _ _)

end HRS.MS.R26T6C
