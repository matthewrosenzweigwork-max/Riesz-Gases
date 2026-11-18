import HRS.PDE.MovCAux7

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_gibbs_Z {α : Type*} [MeasurableSpace α] (Pm : Measure α) [IsProbabilityMeasure Pm]
    (a : ℝ) (Fn : ℕ → α → ℝ) (F : α → ℝ) (hFn : ∀ n, Measurable (Fn n))
    (hF : Measurable F) (c : ℝ) (hc : ∀ n x, -c ≤ Fn n x)
    (hlim : ∀ᵐ x ∂Pm, Tendsto (fun n => Fn n x) atTop (𝓝 (F x))) (ha : a ≤ 0) :
    (∀ n, 0 < ∫ y, Real.exp (a * Fn n y) ∂Pm) ∧ 0 < ∫ y, Real.exp (a * F y) ∂Pm ∧
      Tendsto (fun n => ∫ y, Real.exp (a * Fn n y) ∂Pm) atTop
        (𝓝 (∫ y, Real.exp (a * F y) ∂Pm)) := by
  set K := Real.exp (-a * c) with hK
  have hexp : ∀ n x, Real.exp (a * Fn n x) ≤ K := fun n x => by
    rw [hK]; apply Real.exp_le_exp.2; nlinarith [hc n x]
  have hlimF : ∀ᵐ x ∂Pm, -c ≤ F x :=
    hlim.mono fun x hx => ge_of_tendsto' hx (fun n => hc n x)
  have hexpF : ∀ᵐ x ∂Pm, Real.exp (a * F x) ≤ K := hlimF.mono fun x hx => by
    rw [hK]; apply Real.exp_le_exp.2; nlinarith
  have hmeasE : ∀ n, Measurable (fun x => Real.exp (a * Fn n x)) := fun n =>
    Real.measurable_exp.comp (measurable_const.mul (hFn n))
  have hmeasEF : Measurable (fun x => Real.exp (a * F x)) :=
    Real.measurable_exp.comp (measurable_const.mul hF)
  refine ⟨fun n => integral_exp_pos ?_, integral_exp_pos ?_, ?_⟩
  · exact Integrable.mono' (integrable_const K) (hmeasE n).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexp n x)
  · exact Integrable.mono' (integrable_const K) hmeasEF.aestronglyMeasurable
      (hexpF.mono fun x hx => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hx)
  · refine tendsto_integral_of_dominated_convergence (fun _ => K)
      (fun n => (hmeasE n).aestronglyMeasurable) (integrable_const K) (fun n => ?_) ?_
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexp n x
    · filter_upwards [hlim] with x hx
      exact ((Real.continuous_exp.tendsto _).comp (hx.const_mul a))

theorem movc_smul_withDensity {α : Type*} [MeasurableSpace α] (Pm : Measure α) (f : α → ℝ)
    {Z : ℝ} (hZ : 0 < Z) :
    (ENNReal.ofReal Z)⁻¹ • Pm.withDensity (fun x => ENNReal.ofReal (f x)) =
      Pm.withDensity (fun x => ENNReal.ofReal (f x / Z)) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.smul_apply, withDensity_apply _ hs, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne')]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm]

/-- pair-term/one-body decomposition of the energy difference. -/
theorem movc_energy_diff_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hc : Continuous ρ) {C : ℝ} (hC : ∀ y, |ρ y| ≤ C)
    {M : ℝ} (hM0 : 0 ≤ M) {X : Config d N} (hX : X ∉ collisionSet d N) (hN : 1 ≤ N) :
    modulatedEnergyKernel (b15c_gReg d s M) X (withDensityReal ρ) -
      modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ) ≤
      (3 / 2) * (C * ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s M z|) := by
  haveI := isProb_withDensityReal hρ
  rw [movc_energy_eq _ hρ.measurable hρ.nonneg, movc_energy_eq _ hρ.measurable hρ.nonneg]
  set I := ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s M z| with hI
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (0 : Torus d))
  have hI0 : 0 ≤ I := integral_nonneg fun z => abs_nonneg _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpair : ∑ i, ∑ j ∈ Finset.univ.erase i, b15c_gReg d s M (X i - X j) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    exact b15c_gReg_le s M (sub_ne_zero.mpr fun h => hX ⟨i, j, hij, h⟩)
  have hdiff : ∀ x, |convFun (periodicRiesz d s) ρ x - convFun (b15c_gReg d s M) ρ x| ≤ C * I :=
    fun x => movc_convFun_diff_le hd hs0 hsd M hc hC x
  have h1 : (1 / (N : ℝ)) * ∑ i, convFun (periodicRiesz d s) ρ (X i) -
      (1 / (N : ℝ)) * ∑ i, convFun (b15c_gReg d s M) ρ (X i) ≤ C * I := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    calc (1 / (N : ℝ)) * ∑ i, (convFun (periodicRiesz d s) ρ (X i) - convFun (b15c_gReg d s M) ρ (X i))
        ≤ (1 / (N : ℝ)) * ∑ i : Fin N, (C * I) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hdiff _))
            (by positivity)
      _ = C * I := by simp; field_simp
  have h2 : ∫ x, convFun (b15c_gReg d s M) ρ x ∂(withDensityReal ρ) -
      ∫ x, convFun (periodicRiesz d s) ρ x ∂(withDensityReal ρ) ≤ C * I := by
    have hgi : Integrable (periodicRiesz d s) := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
    have hgc := movc_gReg_measurable hd hs0 hsd M
    have hgM : Integrable (b15c_gReg d s M) := hgc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have hga := CoercAux.measurable_periodicRiesz_one hd hs0 hsd
    have ia : Integrable (fun x => convFun (b15c_gReg d s M) ρ x) (withDensityReal ρ) :=
      Integrable.of_bound (movc_convFun_measurable hgc.measurable hρ.measurable).aestronglyMeasurable
        (C * ∫ z : Torus d, |b15c_gReg d s M z|)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact movc_conv_abs_le hgM hC x)
    have ib : Integrable (fun x => convFun (periodicRiesz d s) ρ x) (withDensityReal ρ) :=
      Integrable.of_bound (movc_convFun_measurable hga hρ.measurable).aestronglyMeasurable
        (C * ∫ z : Torus d, |periodicRiesz d s z|)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact movc_conv_abs_le hgi hC x)
    rw [← integral_sub ia ib]
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ) (C := C * I)
      (f := fun x => convFun (b15c_gReg d s M) ρ x - convFun (periodicRiesz d s) ρ x)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_sub_comm]; exact hdiff x)
    rw [Real.norm_eq_abs] at this
    simp at this
    exact (le_abs_self _).trans this
  have hP0 : 0 ≤ (1 / (2 * (N : ℝ) ^ 2)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpair hP0]

end HRS
