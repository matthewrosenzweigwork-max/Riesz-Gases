import HRS.MS.SA16Y4Ct2

/-!
# S.A.16 (SA16Y4) Ct3: `‖f - ρ_n ⋆ f‖_{L^p} ≤ (n+1)^{-1} ‖∑_i |∂_i f|‖_{L^p}` for `f ∈ C_c^∞`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

section Ct3
variable {d : ℕ}

lemma sa16y4_G1_cont {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : IsCcInfty f) : Continuous (sa16y4_G1 f) := by
  unfold sa16y4_G1
  exact continuous_finset_sum _ fun i _ =>
    (((hf.1.continuous_fderiv (by simp)).clm_apply continuous_const)).abs

theorem sa16y4_mol_sub_eLp {p : ℝ} (hp : 1 ≤ p) (n : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : IsCcInfty f) :
    eLpNorm (fun x => f x - sa16q_mol n f x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) * eLpNorm (sa16y4_G1 f) (ENNReal.ofReal p) volume := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hG := sa16y4_G1_cont hf
  have hρc : Continuous (sa16y_rho d n) := (sa16y_rho_smooth n).continuous
  have hmol : Continuous (fun x => f x - sa16q_mol n f x) := by
    have := (sa16y3_conv_contDiff (sa16y_rho_integrable n).locallyIntegrable hf).continuous
    exact hf.1.continuous.sub (show Continuous (sa16q_mol n f) from this)
  set a : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun y => ENNReal.ofReal (sa16y_rho d n y * ‖y‖) with ha
  set Gn : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x => ENNReal.ofReal (sa16y4_G1 f x) with hGn
  have hGnm : Measurable Gn := hG.measurable.ennreal_ofReal
  have ham : Measurable a := ((hρc.mul continuous_norm).measurable).ennreal_ofReal
  set Fi : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun x y => ∫⁻ s in Ioc (0 : ℝ) 1, Gn (x - s • y) with hFi
  have hFm : Measurable (Function.uncurry Fi) := by
    have hm : Measurable (fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × ℝ =>
        Gn (q.1.1 - q.2 • q.1.2)) :=
      hGnm.comp ((measurable_fst.comp measurable_fst).sub (measurable_snd.smul (measurable_snd.comp measurable_fst)))
    exact Measurable.lintegral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1)) hm
  have hmink := sa16j_mink (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin d)))) hp ham hFm
  have hinner : ∀ y, ∫⁻ x, Fi x y ^ p ≤ ∫⁻ x, Gn x ^ p := fun y => sa16y4_seg_mink hp hGnm y
  have hmink2 : ∫⁻ x, (∫⁻ y, a y * Fi x y) ^ p ≤ (∫⁻ y, a y) ^ p * ∫⁻ x, Gn x ^ p := by
    refine hmink.trans ?_
    have h1 : ∫⁻ y, a y * ∫⁻ x, Fi x y ^ p ≤ ∫⁻ y, a y * ∫⁻ x, Gn x ^ p :=
      lintegral_mono fun y => mul_le_mul' le_rfl (hinner y)
    rw [lintegral_mul_const _ ham] at h1
    refine (mul_le_mul' le_rfl h1).trans (le_of_eq ?_)
    rw [← mul_assoc]
    congr 1
    conv_rhs => rw [show p = (p - 1) + 1 by ring]
    rw [ENNReal.rpow_add_of_nonneg (p - 1) 1 (show (0 : ℝ) ≤ p - 1 by linarith) zero_le_one, ENNReal.rpow_one]
  have hsa : ∫⁻ y, a y ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    have h1 : ∀ y, a y ≤ ENNReal.ofReal (sa16y_rho d n y) * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      intro y
      rw [ha, ← ENNReal.ofReal_mul (sa16y_rho_nonneg n y)]
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hz : 1 / ((n : ℝ) + 1) < ‖y‖
      · rw [sa16y_rho_supp n y hz]; simp
      · exact mul_le_mul_of_nonneg_left (not_lt.1 hz) (sa16y_rho_nonneg n y)
    refine (lintegral_mono h1).trans ?_
    rw [lintegral_mul_const _ (hρc.measurable.ennreal_ofReal),
      ← ofReal_integral_eq_lintegral_ofReal (sa16y_rho_integrable n)
        (Eventually.of_forall (sa16y_rho_nonneg n)), sa16y_rho_int, ENNReal.ofReal_one, one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt hmol.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt hG.aestronglyMeasurable, hpr]
  have hpt' : p ≠ 0 := hp0.ne'
  have hG1 : ∀ x, ‖sa16y4_G1 f x‖ₑ = Gn x := fun x => by
    rw [hGn, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by unfold sa16y4_G1; exact Finset.sum_nonneg fun i _ => abs_nonneg _)]
  simp_rw [hG1]
  calc (∫⁻ x, ‖f x - sa16q_mol n f x‖ₑ ^ p) ^ (1 / p)
      ≤ (∫⁻ x, (∫⁻ y, a y * Fi x y) ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono fun x => ENNReal.rpow_le_rpow (sa16y4_sub_pt hf n x) hp0.le)
          (by positivity)
    _ ≤ ((∫⁻ y, a y) ^ p * ∫⁻ x, Gn x ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow hmink2 (by positivity)
    _ = (∫⁻ y, a y) * (∫⁻ x, Gn x ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div, ENNReal.rpow_rpow_inv hpt']
    _ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) * (∫⁻ x, Gn x ^ p) ^ (1 / p) := mul_le_mul' hsa le_rfl

end Ct3

end HRS.Whole.AppendixA.Phase2SA16R
