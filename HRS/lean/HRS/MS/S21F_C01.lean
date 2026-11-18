import HRS.MS.S21F_C01a
import HRS.MS.TransOpAux23

/-!
# S21F, packet R26-T3.C01: weighted convolution bound for the locally integrable Riesz force

`‖∇g(z)‖ ≤ W(z) = σ(‖z‖^{-(s+1)} 1_{‖z‖<1} + 1)` (merged `kG_envelope`), `∫ W(x-y) dμ(y) ≤ A` uniformly for the bounded Gaussian
thermal density (`db1G` is integrable since `s+1 < d`), and the weighted Cauchy-Schwarz/Tonelli (Schur) argument gives
`‖F‖²_{L²(μ)} ≤ A² ‖v‖²_{L²(μ)}` for `F(x) = ∫ ⟨∇g(x-y), v(y)⟩ dμ(y)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_force_core {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s + 1 < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (v : Euc d → Euc d) (hvm : Measurable v)
    (hv2 : Integrable (fun y => ‖v y‖ ^ 2) (HRS.Whole.withDensityReal ρ)) :
    ∫⁻ x, ENNReal.ofReal ((∫ y, inner ℝ (rieszKernelGrad d s (x - y)) (v y) ∂(HRS.Whole.withDensityReal ρ)) ^ 2)
        ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal ((HRS.MS.S111X1.kσ s * (M * (∫ z, HRS.MH.DualityRd.db1G (d := d) (s + 1) z) + 1)) ^ 2) *
        ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 2) ∂(HRS.Whole.withDensityReal ρ) := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set A : ℝ := HRS.MS.S111X1.kσ s * (M * (∫ z, HRS.MH.DualityRd.db1G (d := d) (s + 1) z) + 1) with hA
  have hGm : Measurable (rieszKernelGrad d s : Euc d → Euc d) := HRS.MS.S111X1.kG_measurable s
  have hmass : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (s21f_W d s (x - y)) ∂μ ≤ ENNReal.ofReal A :=
    fun x => s21f_force_mass hd hsd hρ hM x
  have hmass' : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (s21f_W d s (x - y)) ∂μ ≤ ENNReal.ofReal A := fun y => by
    have := hmass y
    refine le_trans (le_of_eq ?_) this
    refine lintegral_congr fun x => ?_
    rw [show y - x = -(x - y) by abel, s21f_W_even]
  have hWm : Measurable fun p : Euc d × Euc d => ENNReal.ofReal (s21f_W d s (p.1 - p.2)) :=
    ENNReal.measurable_ofReal.comp ((s21f_W_meas d s).comp (measurable_fst.sub measurable_snd))
  have hu : Measurable fun y : Euc d => ENNReal.ofReal ‖v y‖ :=
    ENNReal.measurable_ofReal.comp hvm.norm
  have hpt : ∀ x : Euc d, ENNReal.ofReal ((∫ y, inner ℝ (rieszKernelGrad d s (x - y)) (v y) ∂μ) ^ 2) ≤
      ENNReal.ofReal A * ∫⁻ y, ENNReal.ofReal (s21f_W d s (x - y)) * (ENNReal.ofReal ‖v y‖) ^ 2 ∂μ := by
    intro x
    set h : Euc d → ℝ := fun y => inner ℝ (rieszKernelGrad d s (x - y)) (v y) with hh
    have h1 : ENNReal.ofReal |∫ y, h y ∂μ| ≤ ∫⁻ y, ENNReal.ofReal (s21f_W d s (x - y)) * ENNReal.ofReal ‖v y‖ ∂μ := by
      calc ENNReal.ofReal |∫ y, h y ∂μ| ≤ ENNReal.ofReal (∫ y, ‖h y‖ ∂μ) :=
            ENNReal.ofReal_le_ofReal (by simpa using norm_integral_le_integral_norm (μ := μ) h)
        _ ≤ ∫⁻ y, ‖h y‖ₑ ∂μ := by
            have hhm : AEStronglyMeasurable h μ :=
              ((hGm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).inner hvm.aestronglyMeasurable
            by_cases hi : Integrable h μ
            · exact le_of_eq (ofReal_integral_norm_eq_lintegral_enorm hi)
            · have : ∫ y, ‖h y‖ ∂μ = 0 := integral_undef fun hn => hi ((integrable_norm_iff hhm).1 hn)
              rw [this]; simp
        _ ≤ _ := lintegral_mono fun y => by
            rw [← ofReal_norm, ← ENNReal.ofReal_mul (s21f_W_nonneg d s _)]
            refine ENNReal.ofReal_le_ofReal ?_
            calc ‖h y‖ ≤ ‖rieszKernelGrad d s (x - y)‖ * ‖v y‖ := norm_inner_le_norm _ _
              _ ≤ s21f_W d s (x - y) * ‖v y‖ := by
                gcongr
                exact HRS.MS.S111X1.kG_envelope hd hs0 _
    have hwm : Measurable fun y : Euc d => ENNReal.ofReal (s21f_W d s (x - y)) :=
      ENNReal.measurable_ofReal.comp ((s21f_W_meas d s).comp (measurable_const.sub measurable_id))
    have hcs := s21f_cs_sq μ hwm hu
    calc ENNReal.ofReal ((∫ y, h y ∂μ) ^ 2) = (ENNReal.ofReal |∫ y, h y ∂μ|) ^ 2 := by
          rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
      _ ≤ (∫⁻ y, ENNReal.ofReal (s21f_W d s (x - y)) * ENNReal.ofReal ‖v y‖ ∂μ) ^ 2 := pow_le_pow_left' h1 2
      _ ≤ _ := hcs
      _ ≤ _ := mul_le_mul_left (hmass x) _
  calc ∫⁻ x, ENNReal.ofReal ((∫ y, inner ℝ (rieszKernelGrad d s (x - y)) (v y) ∂μ) ^ 2) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal A * ∫⁻ y, ENNReal.ofReal (s21f_W d s (x - y)) * (ENNReal.ofReal ‖v y‖) ^ 2 ∂μ ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal A * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (s21f_W d s (x - y)) * (ENNReal.ofReal ‖v y‖) ^ 2 ∂μ ∂μ := by
        rw [lintegral_const_mul']; exact ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal A * ∫⁻ y, ∫⁻ x, ENNReal.ofReal (s21f_W d s (x - y)) * (ENNReal.ofReal ‖v y‖) ^ 2 ∂μ ∂μ := by
        rw [lintegral_lintegral_swap]
        exact (hWm.mul ((hu.pow_const 2).comp measurable_snd)).aemeasurable
    _ ≤ ENNReal.ofReal A * ∫⁻ y, ENNReal.ofReal A * (ENNReal.ofReal ‖v y‖) ^ 2 ∂μ := by
        gcongr with y
        calc ∫⁻ x, ENNReal.ofReal (s21f_W d s (x - y)) * (ENNReal.ofReal ‖v y‖) ^ 2 ∂μ
            = (∫⁻ x, ENNReal.ofReal (s21f_W d s (x - y)) ∂μ) * (ENNReal.ofReal ‖v y‖) ^ 2 :=
              lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          _ ≤ ENNReal.ofReal A * (ENNReal.ofReal ‖v y‖) ^ 2 := mul_le_mul_left (hmass' y) _
    _ = ENNReal.ofReal (A ^ 2) * ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 2) ∂μ := by
        have hA0 : 0 ≤ A := by
          have ha0 : 0 ≤ ∫ z, HRS.MH.DualityRd.db1G (d := d) (s + 1) z :=
            integral_nonneg fun z => HRS.MH.DualityRd.db1G_nonneg _ _
          have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
          have := HRS.MS.S111X1.kσ_nonneg s
          rw [hA]; positivity
        simp_rw [← ENNReal.ofReal_pow (norm_nonneg _)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul hA0, sq]

theorem s21f_force_l2_gen {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s + 1 < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Euc d → Euc d, MemLp v 2 (HRS.Whole.withDensityReal ρ) →
      MemLp (fun x => ∫ y, inner ℝ (rieszKernelGrad d s (x - y)) (v y) ∂(HRS.Whole.withDensityReal ρ))
        2 (HRS.Whole.withDensityReal ρ) ∧
      ∫ x, (∫ y, inner ℝ (rieszKernelGrad d s (x - y)) (v y) ∂(HRS.Whole.withDensityReal ρ)) ^ 2
          ∂(HRS.Whole.withDensityReal ρ) ≤ C * ∫ x, ‖v x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set A : ℝ := HRS.MS.S111X1.kσ s * (M * (∫ z, HRS.MH.DualityRd.db1G (d := d) (s + 1) z) + 1) with hA
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hA0 : 0 ≤ A := by
    have ha0 : 0 ≤ ∫ z, HRS.MH.DualityRd.db1G (d := d) (s + 1) z :=
      integral_nonneg fun z => HRS.MH.DualityRd.db1G_nonneg _ _
    have := HRS.MS.S111X1.kσ_nonneg s
    positivity
  refine ⟨A ^ 2, by positivity, fun v hv => ?_⟩
  set F : Euc d → ℝ := fun x => ∫ y, inner ℝ (rieszKernelGrad d s (x - y)) (v y) ∂μ with hF
  have hvm : AEStronglyMeasurable v μ := hv.aestronglyMeasurable
  have hGm : Measurable (rieszKernelGrad d s : Euc d → Euc d) := HRS.MS.S111X1.kG_measurable s
  have hFm : AEStronglyMeasurable F μ := by
    have hk : AEStronglyMeasurable (fun p : Euc d × Euc d => inner ℝ (rieszKernelGrad d s (p.1 - p.2)) (v p.2))
        (μ.prod μ) :=
      ((hGm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).inner
        (hvm.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd))
    exact hk.integral_prod_right'
  have hv2 : Integrable (fun y => ‖v y‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hvm).1 hv
  -- pass to a measurable modification of `v`
  obtain ⟨v', hv'm, hvv'⟩ : ∃ v' : Euc d → Euc d, Measurable v' ∧ v =ᵐ[μ] v' :=
    ⟨hvm.mk v, hvm.stronglyMeasurable_mk.measurable, hvm.ae_eq_mk⟩
  have hFF : ∀ x, F x = ∫ y, inner ℝ (rieszKernelGrad d s (x - y)) (v' y) ∂μ := by
    intro x
    refine integral_congr_ae ?_
    filter_upwards [hvv'] with y hy
    simp only [hy]
  have hv2' : Integrable (fun y => ‖v' y‖ ^ 2) μ :=
    hv2.congr (hvv'.mono fun y hy => by simp only [hy])
  have hcore := s21f_force_core hd hs0 hsd hρ hM v' hv'm hv2'
  have hN : ∫⁻ y, ENNReal.ofReal (‖v' y‖ ^ 2) ∂μ = ENNReal.ofReal (∫ y, ‖v y‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hv2 (Eventually.of_forall fun y => by positivity)]
    exact lintegral_congr_ae (hvv'.mono fun y hy => by simp only [hy])
  rw [hN] at hcore
  have hcore : ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ ≤
      ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (∫ y, ‖v y‖ ^ 2 ∂μ) := by
    simp only [hFF]; exact hcore
  have hFsq : Integrable (fun x => F x ^ 2) μ := by
    refine ⟨(continuous_pow 2).comp_aestronglyMeasurable hFm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg _)]
    exact lt_of_le_of_lt hcore (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  refine ⟨(memLp_two_iff_integrable_sq hFm).2 hFsq, ?_⟩
  have h2 : ENNReal.ofReal (∫ x, F x ^ 2 ∂μ) ≤ ENNReal.ofReal (A ^ 2 * ∫ y, ‖v y‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hFsq (Eventually.of_forall fun x => sq_nonneg _),
      ENNReal.ofReal_mul (by positivity)]
    exact hcore
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

theorem r26t3_force_l2 {p : Parameters} {δ : ℝ} (R : Trajectory p δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Euc p.d → Euc p.d,
      MemLp v 2 (HRS.Whole.withDensityReal R.ρβ) →
      MemLp (fun x => ∫ y, inner ℝ (rieszKernelGrad p.d p.s (x - y)) (v y) ∂(HRS.Whole.withDensityReal R.ρβ))
        2 (HRS.Whole.withDensityReal R.ρβ) ∧
      ∫ x, (∫ y, inner ℝ (rieszKernelGrad p.d p.s (x - y)) (v y) ∂(HRS.Whole.withDensityReal R.ρβ)) ^ 2
          ∂(HRS.Whole.withDensityReal R.ρβ) ≤ C * ∫ x, ‖v x‖ ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ) := by
  have hd := p.hd
  have hdr : (2 : ℝ) ≤ p.d := by exact_mod_cast hd
  have hsd : p.s < p.d := by have := p.hs; linarith
  have hsd1 : p.s + 1 < p.d := by have := p.hs; linarith
  obtain ⟨M₀, c, S, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal hd p.hs0 hsd p.ha p.hβ R.thermal
  refine s21f_force_l2_gen (by omega) p.hs0 hsd1 hTc.prob (M := |M₀|) fun x => ?_
  calc R.ρβ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2) := hTc.gauss x
    _ ≤ |M₀| * Real.exp (-c * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ |M₀| * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])) (abs_nonneg _)
    _ = |M₀| := mul_one _

end HRS.MS.R26T3
