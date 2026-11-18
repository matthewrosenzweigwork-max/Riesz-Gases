import HRS.Whole.Q34Aux12
import HRS.Whole.Q34Aux5

/-!
# Packet Q34, helper file 13: positive definiteness of the Riesz kernel (heat representation)
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

theorem diag_ae (ν : Measure (Euc d)) [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ z ∂(ν.prod ν), z.1 ≠ z.2 := by
  have hs : MeasurableSet {p : Euc d × Euc d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := ν) (ν := ν) hs).2
    (Filter.Eventually.of_forall fun x => ?_)
  · exact this
  · have h0 : ν {x} = 0 := measure_singleton x
    filter_upwards [(measure_eq_zero_iff_ae_notMem).1 h0] with y hy
    exact fun h => hy (by simpa using h.symm)

theorem noAtoms_nu {ρ : Euc d → ℝ} (hd : 1 ≤ d) : NullSingletonClass (withDensityReal ρ) := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  refine ⟨fun x => ?_⟩
  have h := withDensity_absolutelyContinuous (volume : Measure (Euc d))
    (fun x => ENNReal.ofReal (ρ x))
  exact h (measure_singleton x)

/-- The heat (Gaussian-mixture) representation of the Riesz kernel. -/
theorem riesz_heat {s : ℝ} (hs : 0 < s) (w : Euc d) :
    ‖w‖ ^ (-s) * Real.Gamma (s / 2) =
      ∫ τ in Ioi (0 : ℝ), τ ^ (s / 2 - 1) * Real.exp (-(‖w‖ ^ 2 * τ)) := by
  by_cases hw : w = 0
  · subst hw
    simp only [norm_zero]
    rw [Real.zero_rpow (by linarith : -s ≠ 0), zero_mul]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, neg_zero,
      Real.exp_zero, mul_one]
    symm
    apply integral_undef
    intro hint
    have h1 : IntegrableOn (fun τ : ℝ => τ ^ (s / 2 - 1)) (Ioi 1) :=
      IntegrableOn.mono_set (show IntegrableOn (fun τ : ℝ => τ ^ (s / 2 - 1)) (Ioi 0) volume from hint)
        (Ioi_subset_Ioi zero_le_one)
    have := (integrableOn_Ioi_rpow_iff (s := s / 2 - 1) (t := 1) one_pos).1 h1
    linarith
  · have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < s / 2) (by positivity)]
    congr 1
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hn.le,
      ← Real.rpow_neg hn.le]
    congr 1; push_cast; ring


theorem one_div_sq_rpow {s : ℝ} {w : Euc d} (hw : 0 < ‖w‖) :
    (1 / ‖w‖ ^ 2) ^ (s / 2) = ‖w‖ ^ (-s) := by
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hw.le,
    ← Real.rpow_neg hw.le]
  congr 1; push_cast; ring

/-- The Riesz kernel is positive definite (for integrands with absolutely convergent pairing). -/
theorem riesz_posdef {ν : Measure (Euc d)} [IsFiniteMeasure ν] [NullSingletonClass ν] {s : ℝ}
    (hs : 0 < s) {u : Euc d → ℝ} (hum : Measurable u) (hu : Integrable u ν)
    (hI : Integrable (fun z : Euc d × Euc d => ‖z.1 - z.2‖ ^ (-s) * (u z.1 * u z.2))
      (ν.prod ν)) :
    0 ≤ ∫ z, ‖z.1 - z.2‖ ^ (-s) * (u z.1 * u z.2) ∂(ν.prod ν) := by
  set a : ℝ := s / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha0
  set μτ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμτ
  set h : Euc d × Euc d → ℝ := fun z => u z.1 * u z.2 with hh
  set Ψ : (Euc d × Euc d) × ℝ → ℝ := fun p =>
    p.2 ^ (a - 1) * Real.exp (-(‖p.1.1 - p.1.2‖ ^ 2 * p.2)) * h p.1 with hΨ
  have hhm : Measurable h := (hum.comp measurable_fst).mul (hum.comp measurable_snd)
  have hΨm : Measurable Ψ := by
    have h1 : Measurable (fun p : (Euc d × Euc d) × ℝ => p.2 ^ (a - 1)) :=
      measurable_snd.pow_const _
    have h2 : Measurable (fun p : (Euc d × Euc d) × ℝ =>
        Real.exp (-(‖p.1.1 - p.1.2‖ ^ 2 * p.2))) := by
      have : Measurable (fun p : (Euc d × Euc d) × ℝ => ‖p.1.1 - p.1.2‖ ^ 2 * p.2) :=
        ((measurable_norm.comp ((measurable_fst.comp measurable_fst).sub
          (measurable_snd.comp measurable_fst))).pow_const 2).mul measurable_snd
      exact Real.measurable_exp.comp this.neg
    exact (h1.mul h2).mul (hhm.comp measurable_fst)
  -- pointwise identity
  have hpt : ∀ z : Euc d × Euc d,
      Real.Gamma a * (‖z.1 - z.2‖ ^ (-s) * h z) = ∫ τ, Ψ (z, τ) ∂μτ := by
    intro z
    have := riesz_heat hs (z.1 - z.2)
    have e : ∫ τ, Ψ (z, τ) ∂μτ = (∫ τ in Ioi (0 : ℝ), τ ^ (a - 1) *
        Real.exp (-(‖z.1 - z.2‖ ^ 2 * τ))) * h z := by
      rw [← integral_mul_const]
    rw [e, ← this]
    ring
  -- integrability of `Ψ` on the product
  have hΨi : Integrable Ψ ((ν.prod ν).prod μτ) := by
    refine ⟨hΨm.aestronglyMeasurable, ?_⟩
    have hF : ∀ᵐ z ∂(ν.prod ν), ∫⁻ τ, ‖Ψ (z, τ)‖ₑ ∂μτ =
        ENNReal.ofReal (Real.Gamma a) * ‖‖z.1 - z.2‖ ^ (-s) * h z‖ₑ := by
      filter_upwards [diag_ae ν] with z hz
      have hw : 0 < ‖z.1 - z.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
      have hr : 0 < ‖z.1 - z.2‖ ^ 2 := by positivity
      have e1 : ∫⁻ τ, ‖Ψ (z, τ)‖ₑ ∂μτ = ∫⁻ τ in Ioi (0 : ℝ),
          ENNReal.ofReal (τ ^ (a - 1) * Real.exp (-(‖z.1 - z.2‖ ^ 2 * τ))) *
            ENNReal.ofReal |h z| := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
        have hτ0 : 0 ≤ τ := le_of_lt (mem_Ioi.mp hτ)
        have hpos : 0 ≤ τ ^ (a - 1) * Real.exp (-(‖z.1 - z.2‖ ^ 2 * τ)) :=
          mul_nonneg (Real.rpow_nonneg hτ0 _) (Real.exp_pos _).le
        simp only [hΨ]
        rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hpos, ENNReal.ofReal_mul hpos]
      have hm : Measurable (fun τ : ℝ => ENNReal.ofReal (τ ^ (a - 1) *
          Real.exp (-(‖z.1 - z.2‖ ^ 2 * τ)))) :=
        ((measurable_id.pow_const _).mul
          (Real.measurable_exp.comp (measurable_id.const_mul _).neg)).ennreal_ofReal
      have hΓ' : (1 / ‖z.1 - z.2‖ ^ 2) ^ a = ‖z.1 - z.2‖ ^ (-s) := by
        rw [ha]; exact one_div_sq_rpow hw
      rw [hμτ, e1, lintegral_mul_const _ hm, lintegral_gamma_aux ha0 hr, hΓ',
        Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hΓ.le]
      congr 1
      have hnn := Real.rpow_nonneg (norm_nonneg (z.1 - z.2)) (-s)
      simp only [hh, abs_mul, abs_of_nonneg hnn]
      ring
    have hlp : ∫⁻ p, ‖Ψ p‖ₑ ∂((ν.prod ν).prod μτ) =
        ∫⁻ z, ∫⁻ τ, ‖Ψ (z, τ)‖ₑ ∂μτ ∂(ν.prod ν) :=
      lintegral_prod _ hΨm.enorm.aemeasurable
    simp only [HasFiniteIntegral]
    rw [hlp, lintegral_congr_ae hF, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI.2
  -- Fubini
  have hswap : ∫ z, ∫ τ, Ψ (z, τ) ∂μτ ∂(ν.prod ν) = ∫ τ, ∫ z, Ψ (z, τ) ∂(ν.prod ν) ∂μτ :=
    integral_integral_swap (f := fun z τ => Ψ (z, τ)) hΨi
  have hnonneg : 0 ≤ ∫ τ, ∫ z, Ψ (z, τ) ∂(ν.prod ν) ∂μτ := by
    refine setIntegral_nonneg measurableSet_Ioi fun τ hτ => ?_
    have hτ0 : 0 < τ := hτ
    have e : ∫ z, Ψ (z, τ) ∂(ν.prod ν) = τ ^ (a - 1) *
        ∫ z, Real.exp (-τ * ‖z.1 - z.2‖ ^ 2) * u z.1 * u z.2 ∂(ν.prod ν) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hΨ, hh]
      rw [show -(‖z.1 - z.2‖ ^ 2 * τ) = -τ * ‖z.1 - z.2‖ ^ 2 by ring]
      ring
    rw [e]
    exact mul_nonneg (Real.rpow_nonneg hτ0.le _) (gauss_posdef hum hu hτ0)
  have hmain : Real.Gamma a * ∫ z, ‖z.1 - z.2‖ ^ (-s) * (u z.1 * u z.2) ∂(ν.prod ν) =
      ∫ τ, ∫ z, Ψ (z, τ) ∂(ν.prod ν) ∂μτ := by
    rw [← hswap, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => hpt z)
  have : 0 ≤ Real.Gamma a * ∫ z, ‖z.1 - z.2‖ ^ (-s) * (u z.1 * u z.2) ∂(ν.prod ν) := by
    rw [hmain]; exact hnonneg
  exact nonneg_of_mul_nonneg_right this hΓ

end HRS.Whole.Q34
