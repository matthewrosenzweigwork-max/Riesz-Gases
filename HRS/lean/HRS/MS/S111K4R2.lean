import HRS.MS.S111K4R1

/-!
# S11.1 / V02 (S11K4), V07 (part): per-term continuity of the cubic-formula integrands, step 1
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)
open HRS.MS.S111X1 (KData Wf kA kG_measurable prod_integrable_kernel kG_weighted kA_nonneg)

variable {d : ℕ}

theorem k4_l1_le_l2 {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : MemLp f 2 μ) : ∫ x, |f x| ∂μ ≤ ‖k4_toL μ f‖ := by
  have hm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  rw [k4_toL_eq hf, Lp.norm_toLp]
  have h1 : ∫ x, |f x| ∂μ = (eLpNorm f 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp only [← Real.norm_eq_abs]
    first | exact integral_norm_eq_lintegral_enorm hm | skip
    all_goals exact hm
  have h2 : eLpNorm f 1 μ ≤ eLpNorm f 2 μ :=
    by
      have := eLpNorm_le_eLpNorm_of_exponent_le (μ := μ) (f := f) (p := 1) (q := 2) (by norm_num)
      exact this
  rw [h1]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top h2

/-- The commutator kernel of a field is even. -/
theorem k4_comm_even (s : ℝ) (w : Euc d → Euc d) (x y : Euc d) :
    commutatorKernel d s w y x = commutatorKernel d s w x y := by
  unfold commutatorKernel
  rw [show y - x = -(x - y) from (neg_sub x y).symm, HRS.MS.R2Interp.s102_rieszKernelGrad_neg, inner_neg_right,
    ← inner_neg_left, neg_sub]

/-- `|∬ κ_w Δ(x) c(y)| ≤ 2 B₁ B_c kA ∫|Δ| dμ`. -/
theorem k4_comm_TB {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) (hρ : HRS.Whole.IsProbDensity ρ)
    {w : Euc d → Euc d} (hwm : Measurable w) {B1 : ℝ} (hB1 : ∀ x, ‖w x‖ ≤ B1)
    {Δ c : Euc d → ℝ} (hΔm : Measurable Δ) {BΔ : ℝ} (hBΔ : ∀ x, |Δ x| ≤ BΔ) (hcm : Measurable c) {Bc : ℝ}
    (hBc : ∀ x, |c x| ≤ Bc) :
    |∫ p, commutatorKernel d s w p.1 p.2 * Δ p.1 * c p.2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))| ≤
      2 * B1 * Bc * kA d s M ρ * ∫ x, |Δ x| ∂(HRS.Whole.withDensityReal ρ) := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hBc0 : 0 ≤ Bc := (abs_nonneg _).trans (hBc 0)
  have hBΔ0 : 0 ≤ BΔ := (abs_nonneg _).trans (hBΔ 0)
  have hA0 := kA_nonneg K
  set g : Euc d × Euc d → ℝ := fun p => 2 * B1 * Bc * (ρ p.1 * |Δ p.1| * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖))
    with hg
  have hgi : Integrable g (volume.prod volume) := by
    have := (prod_integrable_kernel K).const_mul (2 * B1 * Bc * BΔ)
    refine this.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((measurable_const.mul (((K.meas.comp measurable_fst).mul (hΔm.comp measurable_fst).abs).mul
        ((K.meas.comp measurable_snd).mul ((kG_measurable s).comp (measurable_fst.sub measurable_snd)).norm)))).aestronglyMeasurable
    · simp only [hg, Real.norm_eq_abs]
      have h1 := K.nonneg p.1
      have h2 := K.nonneg p.2
      have hgnn : 0 ≤ 2 * B1 * Bc * (ρ p.1 * |Δ p.1| * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖)) := by
        positivity
      rw [abs_of_nonneg hgnn]
      have := hBΔ p.1
      calc 2 * B1 * Bc * (ρ p.1 * |Δ p.1| * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖))
          ≤ 2 * B1 * Bc * (ρ p.1 * BΔ * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖)) := by gcongr
        _ = _ := by ring
  rw [k4_integral_prod_nu hρ, ← Real.norm_eq_abs]
  have hint := (k4_integrable_prod_nu hρ _).1 (k4_comm_integrable K hρ hwm hB1 hΔm hBΔ hcm hBc)
  refine (norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun p => ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    simp only [abs_mul, hg]
    rw [abs_of_nonneg (K.nonneg p.1), abs_of_nonneg (K.nonneg p.2)]
    have h1 : |commutatorKernel d s w p.1 p.2| ≤ 2 * B1 * ‖rieszKernelGrad d s (p.1 - p.2)‖ := by
      unfold commutatorKernel
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      calc ‖w p.1 - w p.2‖ ≤ ‖w p.1‖ + ‖w p.2‖ := norm_sub_le _ _
        _ ≤ 2 * B1 := by linarith [hB1 p.1, hB1 p.2]
    have h2 := hBc p.2
    have hρ1 := K.nonneg p.1
    have hρ2 := K.nonneg p.2
    calc ρ p.1 * ρ p.2 * (|commutatorKernel d s w p.1 p.2| * |Δ p.1| * |c p.2|)
        ≤ ρ p.1 * ρ p.2 * (2 * B1 * ‖rieszKernelGrad d s (p.1 - p.2)‖ * |Δ p.1| * Bc) := by gcongr
      _ = _ := by ring
  · rw [integral_prod _ hgi]
    have hin : ∀ x, ∫ y, g (x, y) ≤ 2 * B1 * Bc * (ρ x * |Δ x|) * kA d s M ρ := by
      intro x
      have hw := kG_weighted K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd x
      have : ∀ y, g (x, y) = (2 * B1 * Bc * (ρ x * |Δ x|)) * (ρ y * ‖rieszKernelGrad d s (x - y)‖) := fun y => by
        simp only [hg]; ring
      simp_rw [this]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hw.2 (by have := K.nonneg x; positivity)
    have hfin : Integrable (fun x => ρ x * |Δ x|) := by
      refine (K.int.mul_const BΔ).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (K.meas.mul hΔm.abs).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (K.nonneg x) (abs_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hBΔ x) (K.nonneg x)
    have hr : ∫ x, 2 * B1 * Bc * (ρ x * |Δ x|) * kA d s M ρ =
        2 * B1 * Bc * kA d s M ρ * ∫ x, |Δ x| ∂(HRS.Whole.withDensityReal ρ) := by
      rw [tc2_integral_nu hρ]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
    rw [← hr]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => integral_nonneg fun y => ?_) ?_
      (Filter.Eventually.of_forall hin)
    · simp only [hg]
      have h1 := K.nonneg x
      have h2 := K.nonneg y
      positivity
    · exact (hfin.const_mul (2 * B1 * Bc)).mul_const (kA d s M ρ)

end HRS.MS.S111K4
