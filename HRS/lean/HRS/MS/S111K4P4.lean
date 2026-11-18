import HRS.MS.S111K4P3

/-!
# S11.1 / T03 (S11K4), packets `R26-T6C.P05` and `P06` (part 2): two-space integrals against `ρ dx ⊗ ρ dx`
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)
open HRS.MS.S111X1 (KData Wf Wf_bdd Wf_meas nl_swap plain_integrable kG_weighted kA kG_measurable prod_integrable_kernel)

variable {d : ℕ}

theorem k4_prod_nu_eq {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    (HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ) =
      (volume.prod volume : Measure (Euc d × Euc d)).withDensity
        (fun p => ENNReal.ofReal (ρ p.1) * ENNReal.ofReal (ρ p.2)) := by
  have hm : Measurable fun x => ENNReal.ofReal (ρ x) := hρ.measurable.ennreal_ofReal
  unfold HRS.Whole.withDensityReal
  exact prod_withDensity₀ hm.aemeasurable hm.aemeasurable

theorem k4_integrable_prod_nu {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (F : Euc d × Euc d → ℝ) :
    Integrable F ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) ↔
      Integrable (fun p => ρ p.1 * ρ p.2 * F p) (volume.prod volume : Measure (Euc d × Euc d)) := by
  have hm : Measurable fun p : Euc d × Euc d => ENNReal.ofReal (ρ p.1) * ENNReal.ofReal (ρ p.2) :=
    (hρ.measurable.ennreal_ofReal.comp measurable_fst).mul (hρ.measurable.ennreal_ofReal.comp measurable_snd)
  rw [k4_prod_nu_eq hρ, integrable_withDensity_iff_integrable_smul' hm
    (ae_of_all _ fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun p => ?_)
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ.nonneg p.1), ENNReal.toReal_ofReal (hρ.nonneg p.2)]

theorem k4_integral_prod_nu {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (F : Euc d × Euc d → ℝ) :
    ∫ p, F p ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) =
      ∫ p, ρ p.1 * ρ p.2 * F p ∂(volume.prod volume : Measure (Euc d × Euc d)) := by
  have hm : Measurable fun p : Euc d × Euc d => ENNReal.ofReal (ρ p.1) * ENNReal.ofReal (ρ p.2) :=
    (hρ.measurable.ennreal_ofReal.comp measurable_fst).mul (hρ.measurable.ennreal_ofReal.comp measurable_snd)
  rw [k4_prod_nu_eq hρ, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ.nonneg p.1), ENNReal.toReal_ofReal (hρ.nonneg p.2)]

/-- Pro `R26-T6C.P05` (commutator part): absolute integrability against `μ ⊗ μ`. -/
theorem k4_comm_integrable {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M)
    (hρ : HRS.Whole.IsProbDensity ρ) {a : Euc d → Euc d} (ham : Measurable a) {Ba : ℝ}
    (hBa : ∀ y, ‖a y‖ ≤ Ba) {u v : Euc d → ℝ} (hum : Measurable u) {Bu : ℝ} (hBu : ∀ x, |u x| ≤ Bu)
    (hvm : Measurable v) {Bv : ℝ} (hBv : ∀ x, |v x| ≤ Bv) :
    Integrable (fun xy : Euc d × Euc d => commutatorKernel d s a xy.1 xy.2 * u xy.1 * v xy.2)
      ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  rw [k4_integrable_prod_nu hρ]
  have hBa0 : 0 ≤ Ba := (norm_nonneg _).trans (hBa 0)
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hBv0 : 0 ≤ Bv := (abs_nonneg _).trans (hBv 0)
  have hmeas : Measurable fun p : Euc d × Euc d => ρ p.1 * ρ p.2 *
      (commutatorKernel d s a p.1 p.2 * u p.1 * v p.2) := by
    unfold commutatorKernel
    exact ((K.meas.comp measurable_fst).mul (K.meas.comp measurable_snd)).mul
      ((Measurable.inner ((ham.comp measurable_fst).sub (ham.comp measurable_snd))
        ((kG_measurable s).comp (measurable_fst.sub measurable_snd))).mul (hum.comp measurable_fst)
        |>.mul (hvm.comp measurable_snd))
  refine ((prod_integrable_kernel K).const_mul (2 * Ba * (Bu * Bv))).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  simp only [abs_mul]
  rw [abs_of_nonneg (K.nonneg p.1), abs_of_nonneg (K.nonneg p.2)]
  have h1 : |commutatorKernel d s a p.1 p.2| ≤ 2 * Ba * ‖rieszKernelGrad d s (p.1 - p.2)‖ := by
    unfold commutatorKernel
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    calc ‖a p.1 - a p.2‖ ≤ ‖a p.1‖ + ‖a p.2‖ := norm_sub_le _ _
      _ ≤ 2 * Ba := by linarith [hBa p.1, hBa p.2]
  have h2 := hBu p.1
  have h3 := hBv p.2
  have hρ1 := K.nonneg p.1
  have hρ2 := K.nonneg p.2
  calc ρ p.1 * ρ p.2 * (|commutatorKernel d s a p.1 p.2| * |u p.1| * |v p.2|)
      ≤ ρ p.1 * ρ p.2 * (2 * Ba * ‖rieszKernelGrad d s (p.1 - p.2)‖ * Bu * Bv) := by
        gcongr
    _ = 2 * Ba * (Bu * Bv) * (ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖)) := by ring

/-- The commutator splitting in `μ`-form (Pro `R26-T6C.P06`, the interaction term). -/
theorem k4_comm_split_nu {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M)
    (hρ : HRS.Whole.IsProbDensity ρ) {a : Euc d → Euc d} (ham : Measurable a) {Ba : ℝ}
    (hBa : ∀ y, ‖a y‖ ≤ Ba) {u v : Euc d → ℝ} (hum : Measurable u) {Bu : ℝ} (hBu : ∀ x, |u x| ≤ Bu)
    (hvm : Measurable v) {Bv : ℝ} (hBv : ∀ x, |v x| ≤ Bv) :
    (∫ x, u x * inner ℝ (a x) (Wf d s ρ v x) ∂(HRS.Whole.withDensityReal ρ)) +
      (∫ x, v x * inner ℝ (a x) (Wf d s ρ u x) ∂(HRS.Whole.withDensityReal ρ)) =
      ∫ xy, commutatorKernel d s a xy.1 xy.2 * u xy.1 * v xy.2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  have hint := (k4_integrable_prod_nu hρ _).1 (k4_comm_integrable K hρ ham hBa hum hBu hvm hBv)
  rw [tc2_integral_nu hρ, tc2_integral_nu hρ, k4_integral_prod_nu hρ,
    k4_commutator_split K ham hBa hum hBu hvm hBv, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [commutatorKernel]
  ring

end HRS.MS.S111K4
