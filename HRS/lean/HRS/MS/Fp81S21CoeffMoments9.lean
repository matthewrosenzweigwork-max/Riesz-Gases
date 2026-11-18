import HRS.MS.Fp81S21NoisePath6
import HRS.MS.R26T6CD01
import HRS.MC.E214FGauss
import HRS.Energy.StaticLimitAux

/-! A Gaussian sixth-moment estimate for the chart's `ℓ²(ℕ)` coefficient space.

The estimate is stated with coordinate Gaussianity explicit.  A `MomentRep`
certificate alone does not imply this hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS.MS.R26T6

private theorem fp81s21_coeff_enorm_rpow_eq_tsum
    (z : r26t6_Coeff) {s : ℝ} (hs : 0 < s) :
    ‖z‖ₑ ^ s = (∑' j : ℕ, ENNReal.ofReal (z j ^ 2)) ^ (s / 2) := by
  let z' : lp (fun _ : ℕ => ℝ) 2 := z
  have hsum : Summable (fun j : ℕ => z' j ^ 2) := HRS.StaticLimitAux.lp_sq_summable z'
  have hnorm : ‖z'‖ ^ 2 = ∑' j : ℕ, z' j ^ 2 := HRS.StaticLimitAux.lp_norm_sq z'
  have h1' : ∑' j : ℕ, ENNReal.ofReal (z' j ^ 2) = ENNReal.ofReal (‖z'‖ ^ 2) := by
    calc
      _ = ENNReal.ofReal (∑' j : ℕ, z' j ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg (z' j)) hsum).symm
      _ = _ := congrArg ENNReal.ofReal hnorm.symm
  have h1 : ∑' j : ℕ, ENNReal.ofReal (z j ^ 2) = ENNReal.ofReal (‖z‖ ^ 2) := by
    simpa [z'] using h1'
  rw [h1, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

/-- Uniform sixth moments for a Gaussian `ℓ²(ℕ)`-valued random variable.  Each
coordinate is a centered Gaussian, and `w` is a summable majorant of its
second moment.  The constant comes from the standard scalar Gaussian moment
inequality and is independent of the coefficient dimension. -/
theorem fp81s21_gaussian_coeff_sixthMoment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → r26t6_Coeff) (w : ℕ → ℝ)
    (hq : Measurable q)
    (hw0 : ∀ j, 0 ≤ w j) (hwsum : Summable w)
    (hGaussian : ∀ j, HasGaussianLaw (fun ω => q ω j) P)
    (hMean : ∀ j, ∫ ω, q ω j ∂P = 0)
    (hVariance : ∀ j, (∫ ω, (q ω j) ^ 2 ∂P) ≤ w j) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      fp81s21_Moment6 P q (Cg * (∑' j, w j) ^ 3) := by
  obtain ⟨Cg, hCg, hgm⟩ := HRS.MC.E214F.gaussian_rpow_moment
    (s := (6 : ℝ)) (by norm_num)
  let S : ℝ := ∑' j : ℕ, w j
  have hS0 : 0 ≤ S := tsum_nonneg hw0
  have hmeasXi : ∀ j, AEMeasurable (fun ω => q ω j) P :=
    fun j => (hGaussian j).aemeasurable
  have hfin : ∀ F : Finset ℕ,
      ∫⁻ ω, (∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) ^ (3 : ℝ) ∂P ≤
        ENNReal.ofReal (Cg * S ^ 3) := by
    intro F
    have hnorm : ∀ ω, (∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) =
        ‖∑ j ∈ F, (q ω j) ^ 2‖ₑ := by
      intro ω
      rw [← ofReal_norm, Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
    have hmink := eLpNorm_sum_le (μ := P) (f := fun j ω => (q ω j) ^ 2)
      (s := F) (p := ENNReal.ofReal (3 : ℝ)) (by norm_num)
    have hbound : ∀ j, eLpNorm (fun ω => (q ω j) ^ 2) (ENNReal.ofReal (3 : ℝ)) P ≤
        ENNReal.ofReal (Cg ^ (1 / 3 : ℝ) * w j) := by
      intro j
      have hs6 : (2 : ℝ) ≤ 6 := by norm_num
      have hc : 0 ≤ Cg ^ ((2 : ℝ) / 6) := Real.rpow_nonneg hCg _
      have hscalar := HRS.MC.E214F.eLpNorm_sq_le
        hs6 hCg P (fun ω => q ω j) (hGaussian j)
        (hgm P (fun ω => q ω j) (hGaussian j) (hMean j))
      have hbound' : eLpNorm (fun ω => (q ω j) ^ 2) (ENNReal.ofReal (6 / 2)) P ≤
          ENNReal.ofReal (Cg ^ ((2 : ℝ) / 6) * w j) := by
        exact hscalar.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hVariance j) hc))
      simpa [show (2 : ℝ) / 6 = 1 / 3 by norm_num,
        show (6 : ℝ) / 2 = 3 by norm_num] using hbound'
    have hsumBound :
        eLpNorm (∑ j ∈ F, fun ω => (q ω j) ^ 2) (ENNReal.ofReal (3 : ℝ)) P ≤
          ENNReal.ofReal (Cg ^ (1 / 3 : ℝ) * S) := by
      refine hmink.trans ((Finset.sum_le_sum fun j _ => hbound j).trans ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (Real.rpow_nonneg hCg _) (hw0 j)]
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hwsum.sum_le_tsum F (fun j _ => hw0 j))
        (Real.rpow_nonneg hCg _)
    have h2 :
        (∫⁻ ω, ‖∑ j ∈ F, (q ω j) ^ 2‖ₑ ^ (3 : ℝ) ∂P) =
          eLpNorm (∑ j ∈ F, fun ω => (q ω j) ^ 2) (ENNReal.ofReal (3 : ℝ)) P ^ (3 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top
        (by
          refine Finset.aestronglyMeasurable_sum F fun j _ => ?_
          exact ((hmeasXi j).pow_const 2).aestronglyMeasurable),
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3),
        ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num), ENNReal.rpow_one]
      simp only [Finset.sum_apply]
    calc
      _ = ∫⁻ ω, ‖∑ j ∈ F, (q ω j) ^ 2‖ₑ ^ (3 : ℝ) ∂P := by simp_rw [hnorm]
      _ = eLpNorm (∑ j ∈ F, fun ω => (q ω j) ^ 2)
          (ENNReal.ofReal (3 : ℝ)) P ^ (3 : ℝ) := h2
      _ ≤ (ENNReal.ofReal (Cg ^ (1 / 3 : ℝ) * S)) ^ (3 : ℝ) :=
        ENNReal.rpow_le_rpow hsumBound (by norm_num)
      _ = ENNReal.ofReal (Cg * S ^ 3) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        rw [Real.mul_rpow (Real.rpow_nonneg hCg _) hS0, ← Real.rpow_mul hCg]
        norm_num
  have hlim : ∀ ω, ‖q ω‖ₑ ^ (6 : ℝ) =
      ⨆ F : Finset ℕ, (∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) ^ (3 : ℝ) := by
    intro ω
    rw [fp81s21_coeff_enorm_rpow_eq_tsum (q ω) (by norm_num), ENNReal.tsum_eq_iSup_sum]
    have hmap := Monotone.map_iSup_of_continuousAt
      (f := fun x : ℝ≥0∞ => x ^ (3 : ℝ))
      (g := fun F : Finset ℕ => ∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2))
      (ENNReal.continuous_rpow_const.continuousAt)
      (ENNReal.monotone_rpow_of_nonneg (by norm_num))
      (by simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 3)])
    simpa [show (6 : ℝ) / 2 = 3 by norm_num] using hmap
  have hlin :
      (∫⁻ ω, ‖q ω‖ₑ ^ (6 : ℝ) ∂P) ≤ ENNReal.ofReal (Cg * S ^ 3) := by
    simp_rw [hlim]
    rw [lintegral_iSup_directed]
    · exact iSup_le hfin
    · intro F
      have hsumMeas : AEMeasurable
          (fun ω => ∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) P :=
        Finset.aemeasurable_fun_sum F fun j _ => ((hmeasXi j).pow_const 2).ennreal_ofReal
      exact hsumMeas.pow_const _
    · intro F F'
      refine ⟨F ∪ F', ?_, ?_⟩
      · intro ω
        exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (by simp)) (by norm_num)
      · intro ω
        exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (by simp)) (by norm_num)
  have hnonneg : ∀ ω, 0 ≤ ‖q ω‖ ^ 6 := fun ω => by positivity
  have hmeas : Measurable (fun ω => ‖q ω‖ ^ 6) := (measurable_norm.comp hq).pow_const 6
  have hlinReal :
      (∫⁻ ω, ENNReal.ofReal (‖q ω‖ ^ 6) ∂P) ≤ ENNReal.ofReal (Cg * S ^ 3) := by
    have hpoint (ω : Ω) : ENNReal.ofReal (‖q ω‖ ^ 6) = ‖q ω‖ₑ ^ (6 : ℝ) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ← ofReal_norm]
      exact (ENNReal.rpow_natCast (ENNReal.ofReal ‖q ω‖) 6).symm
    calc
      _ = ∫⁻ ω, ‖q ω‖ₑ ^ (6 : ℝ) ∂P := lintegral_congr fun ω => hpoint ω
      _ ≤ ENNReal.ofReal (Cg * S ^ 3) := hlin
  have hi : Integrable (fun ω => ‖q ω‖ ^ 6) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)]
    exact lt_of_le_of_lt hlinReal ENNReal.ofReal_lt_top
  have hIntegralENN :
      (∫⁻ ω, ENNReal.ofReal (‖q ω‖ ^ 6) ∂P) =
        ENNReal.ofReal (∫ ω, ‖q ω‖ ^ 6 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall hnonneg)).symm
  have hreal : ENNReal.ofReal (∫ ω, ‖q ω‖ ^ 6 ∂P) ≤ ENNReal.ofReal (Cg * S ^ 3) := by
    rw [← hIntegralENN]
    simpa [S] using hlinReal
  have hfinal : (∫ ω, ‖q ω‖ ^ 6 ∂P) ≤ Cg * S ^ 3 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hreal
  exact ⟨Cg, hCg, ⟨hq.aemeasurable, hi, by simpa [S] using hfinal⟩⟩

#print axioms HRS.Fp81.S21.fp81s21_gaussian_coeff_sixthMoment

end HRS.Fp81.S21
end
