import HRS.Whole.Q34Aux5

/-!
# Packet Q34, helper file 6: the compensated kernel `k_s` on `ℝ^d`
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

theorem measurable_kk : Measurable kk := by
  unfold kk
  fun_prop

theorem measurable_kk_norm_rpow (s : ℝ) : Measurable (fun u : Euc d => kk (‖u‖ ^ (-s))) :=
  measurable_kk.comp (measurable_norm.pow_const _)

/-- The total mass of `k_s` as a `lintegral`. -/
theorem lintegral_compKernel (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (hds : (d : ℝ) < 2 * s) :
    ∫⁻ u : Euc d, ENNReal.ofReal (kk (‖u‖ ^ (-s))) =
      ENNReal.ofReal (sphereArea d * Real.Gamma (2 - (d : ℝ) / s) /
        (s * ((d : ℝ) / s) * ((d : ℝ) / s - 1))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
  have hp2 : (d : ℝ) / s < 2 := by rw [div_lt_iff₀ hs0]; linarith
  set p : ℝ := (d : ℝ) / s with hp
  have hsp : s * p = d := by rw [hp]; field_simp
  have hsA := sphereArea_nonneg hd
  have hΓ : 0 < Real.Gamma (2 - p) := Real.Gamma_pos_of_pos (by linarith)
  have hG : Measurable (fun y : ℝ => ENNReal.ofReal (kk y)) := measurable_kk.ennreal_ofReal
  rw [lintegral_radial hd (fun t => ENNReal.ofReal (kk (t ^ (-s)))) (by
    exact (measurable_kk.comp (measurable_id.pow_const _)).ennreal_ofReal)]
  have hsubst := lintegral_subst_neg_rpow hs0 (-p - 1) (fun y => ENNReal.ofReal (kk y))
  rw [lintegral_kk_mass hp1 hp2] at hsubst
  have hexp : ∀ t : ℝ, 0 < t → ENNReal.ofReal (t ^ (d - 1)) = ENNReal.ofReal (t ^ (-s * (-p - 1) - s - 1)) := by
    intro t ht
    congr 1
    rw [← Real.rpow_natCast, Nat.cast_sub hd]
    congr 1
    push_cast
    nlinarith [hsp]
  have h2 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (kk (t ^ (-s))) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-s * (-p - 1) - s - 1)) *
        ENNReal.ofReal (kk (t ^ (-s))) :=
    setLIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [hexp t ht]
  rw [h2]
  have hX : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-s * (-p - 1) - s - 1)) *
        ENNReal.ofReal (kk (t ^ (-s))) =
      ENNReal.ofReal (s⁻¹) * ENNReal.ofReal (Real.Gamma (2 - p) / (p * (p - 1))) := by
    rw [hsubst, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs0.le), inv_mul_cancel₀ hs0.ne']
    simp
  rw [hX, ← mul_assoc, ← ENNReal.ofReal_mul hsA, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : p - 1 ≠ 0 := by linarith
  have : p ≠ 0 := by linarith
  field_simp


theorem compKernel_integrable_integral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (hds : (d : ℝ) < 2 * s) :
    Integrable (fun u : Euc d => kk (‖u‖ ^ (-s))) ∧
      ∫ u : Euc d, kk (‖u‖ ^ (-s)) = sphereArea d * Real.Gamma (2 - (d : ℝ) / s) /
        (s * ((d : ℝ) / s) * ((d : ℝ) / s - 1)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
  have hp2 : (d : ℝ) / s < 2 := by rw [div_lt_iff₀ hs0]; linarith
  have hsA := sphereArea_nonneg hd
  have hΓ : 0 < Real.Gamma (2 - (d : ℝ) / s) := Real.Gamma_pos_of_pos (by linarith)
  have hm := measurable_kk_norm_rpow (d := d) s
  have hnn : ∀ u : Euc d, 0 ≤ kk (‖u‖ ^ (-s)) := fun u =>
    kk_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  have hden : 0 < s * ((d : ℝ) / s) * ((d : ℝ) / s - 1) := by
    have : 0 < (d : ℝ) / s - 1 := by linarith
    positivity
  have hval : 0 ≤ sphereArea d * Real.Gamma (2 - (d : ℝ) / s) /
      (s * ((d : ℝ) / s) * ((d : ℝ) / s - 1)) := by positivity
  have hL := lintegral_compKernel hd hs0 hsd hds
  refine ⟨?_, ?_⟩
  · refine (integrable_of_lintegral_le hm hnn hval hL.le).1
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hm.aestronglyMeasurable,
      hL, ENNReal.toReal_ofReal hval]

theorem compKernel_tail (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (hds : (d : ℝ) < 2 * s) :
    ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L →
      ∫ u in {u : Euc d | L < ‖u‖}, kk (‖u‖ ^ (-s)) ≤ C * L ^ ((d : ℝ) - 2 * s) := by
  have hsA := sphereArea_nonneg hd
  have h2s : 0 < 2 * s - (d : ℝ) := by linarith
  refine ⟨sphereArea d / (2 * (2 * s - d)), fun L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  have hm := measurable_kk_norm_rpow (d := d) s
  have hnn : ∀ u : Euc d, 0 ≤ kk (‖u‖ ^ (-s)) := fun u =>
    kk_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  have hset : MeasurableSet {u : Euc d | L < ‖u‖} := measurableSet_lt measurable_const measurable_norm
  have hLp : 0 ≤ L ^ ((d : ℝ) - 2 * s) := Real.rpow_nonneg hL0.le _
  have hC : 0 ≤ sphereArea d / (2 * (2 * s - d)) * L ^ ((d : ℝ) - 2 * s) := by positivity
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun u => hnn u)) hm.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hC ?_
  have hpt : ∀ u : Euc d, ENNReal.ofReal (kk (‖u‖ ^ (-s))) ≤
      ENNReal.ofReal (2⁻¹) * ENNReal.ofReal (‖u‖ ^ (-(2 * s))) := by
    intro u
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := kk_le_half_sq (Real.rpow_nonneg (norm_nonneg u) (-s))
    have h2 : (‖u‖ ^ (-s)) ^ 2 = ‖u‖ ^ (-(2 * s)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1; push_cast; ring
    rw [h2] at h1
    linarith
  calc ∫⁻ u in {u : Euc d | L < ‖u‖}, ENNReal.ofReal (kk (‖u‖ ^ (-s)))
      ≤ ∫⁻ u in {u : Euc d | L < ‖u‖}, ENNReal.ofReal (2⁻¹) *
          ENNReal.ofReal (‖u‖ ^ (-(2 * s))) := lintegral_mono hpt
    _ = ENNReal.ofReal (2⁻¹) * ∫⁻ u in {u : Euc d | L < ‖u‖}, ENNReal.ofReal (‖u‖ ^ (-(2 * s))) :=
        lintegral_const_mul _ ((measurable_norm.pow_const _).ennreal_ofReal)
    _ ≤ ENNReal.ofReal (2⁻¹) * ∫⁻ u in {u : Euc d | L ≤ ‖u‖}, ENNReal.ofReal (‖u‖ ^ (-(2 * s))) := by
        exact mul_le_mul' le_rfl (lintegral_mono_set (fun u (hu : L < ‖u‖) => le_of_lt hu))
    _ = ENNReal.ofReal (2⁻¹) * ENNReal.ofReal (sphereArea d *
          (L ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ)))) := by
        rw [lintegral_compl_rpow hd hL0 hds]
    _ = ENNReal.ofReal (sphereArea d / (2 * (2 * s - d)) * L ^ ((d : ℝ) - 2 * s)) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        field_simp

theorem compKernel_taylor {s : ℝ} (u : Euc d) (hu : u ≠ 0) :
    kk (‖u‖ ^ (-s)) = ‖u‖ ^ (-(2 * s)) *
      ∫ t in Icc (0 : ℝ) 1, (1 - t) * Real.exp (-t * ‖u‖ ^ (-s)) := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  have ha : 0 < ‖u‖ ^ (-s) := Real.rpow_pos_of_pos hn _
  rw [integral_taylor ha]
  have h2 : (‖u‖ ^ (-s)) ^ 2 = ‖u‖ ^ (-(2 * s)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1; push_cast; ring
  rw [← h2]
  field_simp

end HRS.Whole.Q34
