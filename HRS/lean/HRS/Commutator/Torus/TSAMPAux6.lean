import HRS.Commutator.Torus.TSAMPAux5

/-!
# T-SAMP helpers, part 6: `vlo_bound_T` and `vhi_bounded_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_lip_continuous {L : ℝ} {v : Torus d → Euc d} (h : IsLipschitzVF L v) :
    Continuous v := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun y : Torus d => L * KernelGrad.tdist y x) (𝓝 x) (𝓝 (L * 0)) := by
    have := (CoercAux.continuous_tdist_left (d := d) x).tendsto x
    rw [CoercAux.tdist_self] at this
    exact this.const_mul L
  rw [mul_zero] at h1
  exact squeeze_zero (fun y => norm_nonneg _) (fun y => h y x) h1

lemma tsamp_lip_bound {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d} (h : IsLipschitzVF L v) (x : Torus d) :
    ‖v x‖ ≤ ‖v 0‖ + L * d := by
  have h1 := h x 0
  have h2 := KernelGrad.tdist_le_card (d := d) x
  have h3 : ‖v x‖ ≤ ‖v 0‖ + ‖v x - v 0‖ := by
    have := norm_le_insert' (v x) (v 0)
    linarith
  nlinarith [KernelGrad.tdist_nonneg x 0]

lemma tsamp_integrable_of_lip {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d} (h : IsLipschitzVF L v) :
    Integrable v := by
  have hc := tsamp_lip_continuous h
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace v)

lemma tsamp_conv_eq_flip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Torus d → ℝ) (f : Torus d → E) (x : Torus d) :
    tsampConv K f x = ∫ z, K z • f (x - z) := by
  unfold tsampConv
  have := integral_sub_left_eq_self (fun z => K z • f (x - z)) (volume : Measure (Torus d)) x
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [sub_sub_cancel]

lemma tsamp_conv_flip_integrable {K : Torus d → ℝ} (hKi : Integrable K) {v : Torus d → Euc d}
    {L : ℝ} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) (x : Torus d) :
    Integrable (fun z => K z • v (x - z)) := by
  have hm : AEStronglyMeasurable (fun z => K z • v (x - z)) volume :=
    hKi.1.smul ((tsamp_lip_continuous hv).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  refine (hKi.norm.mul_const (‖v 0‖ + L * d)).mono' hm (Eventually.of_forall fun z => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (tsamp_lip_bound hL hv _) (norm_nonneg _)

lemma tsamp_conv_lip {K : Torus d → ℝ} (hKi : Integrable K) {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L)
    (hv : IsLipschitzVF L v) :
    IsLipschitzVF (L * ∫ z, ‖K z‖) (tsampConv K v) := by
  intro x x'
  rw [tsamp_conv_eq_flip, tsamp_conv_eq_flip, ← integral_sub (tsamp_conv_flip_integrable hKi hL hv x)
    (tsamp_conv_flip_integrable hKi hL hv x')]
  have hb : ∀ z, ‖K z • v (x - z) - K z • v (x' - z)‖ ≤ ‖K z‖ * (L * KernelGrad.tdist x x') := by
    intro z
    rw [← smul_sub, norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have := hv (x - z) (x' - z)
    rwa [tsamp_tdist_sub_sub] at this
  calc ‖∫ z, (K z • v (x - z) - K z • v (x' - z))‖
      ≤ ∫ z, ‖K z‖ * (L * KernelGrad.tdist x x') :=
        norm_integral_le_of_norm_le (hKi.norm.mul_const _) (Eventually.of_forall hb)
    _ = (L * ∫ z, ‖K z‖) * KernelGrad.tdist x x' := by
        rw [integral_mul_const]; ring

lemma tsamp_conv_fcoef_comp (hd : 1 ≤ d) {K : Torus d → ℝ} (hKm : Measurable K) (hKi : Integrable K)
    {M : ℝ} (hKb : ∀ x : Torus d, x ≠ 0 → |K x| ≤ M) {f : Torus d → Euc d} (hf : Integrable f)
    (j : Fin d) (k : Lattice d) :
    Torus.fcoef (fun x => (tsampConv K f x) j) k =
      Torus.fcoef K k * Torus.fcoef (fun x => f x j) k := by
  have hfj : Integrable (fun x => f x j) :=
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integrable_comp hf
  have : (fun x => (tsampConv K f x) j) = textConv K (fun x => f x j) := by
    funext x
    rw [tsamp_conv_apply (tsamp_conv_integrable hd hKm hKb hf x) j]
    rfl
  rw [this]
  exact text_fcoef_conv hKi hfj k

theorem tsamp_integral_psi_kernel {η : ℝ} {K : Torus d → ℝ} (hKi : Integrable K)
    (hKcoef : ∀ k : Lattice d, Torus.fcoef K k = (((Whole.chi (η • Lattice.toEuc k)) : ℝ) : ℂ)) :
    ∫ x, K x = 1 := by
  have h0 := hKcoef 0
  rw [Torus.fcoef_zero] at h0
  have h1 : Whole.chi (η • Lattice.toEuc (0 : Lattice d)) = 1 := by
    apply Whole.cmxFB_chi_one
    have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    simp [this]
  rw [h1] at h0
  have : (∫ x, K x : ℝ) = 1 := by exact_mod_cast h0
  exact this

theorem tsamp_vlo_core (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → TorusSubTransport d s (PleqT η v) (C * K) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, C₁, C₂, hB, hC₁, hC₂, hker⟩ := tsamp_psi_kernel (d := d) hd1
  refine ⟨C₁, hC₁, fun η hη hη1 v K hT => ?_⟩
  obtain ⟨L, F, hL, hF, hLip, ⟨w, hrep, hnorm⟩, hLF⟩ := hT
  obtain ⟨hKint, hKb, hK1, hKcoef, -⟩ := hker η hη hη1
  set Kη : Torus d → ℝ := perio (Whole.psiL (d := d) η⁻¹) with hKη
  have hKm : Measurable Kη := by
    obtain ⟨hc, -⟩ := text_psiL_props (d := d) η⁻¹ (inv_pos.2 hη)
    exact tpos_perio_measurable hc.measurable
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : 0 < ((d : ℝ) - s) / 2 := by linarith
  obtain ⟨w', hw'm, hw'le, hw'rep⟩ := tsamp_reduce_w hα hrep
  set p : ℝ := 2 * d / ((d : ℝ) - s - 2) with hp
  have hdens : 0 < (d : ℝ) - s - 2 := by linarith
  have hp1 : 1 < p := by
    rw [hp, one_lt_div hdens]; linarith
  have hw'n : eLpNorm w' (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F :=
    (eLpNorm_mono_ae hw'm.aestronglyMeasurable hw'le).trans hnorm
  have hw'mem : MemLp w' (ENNReal.ofReal p) volume :=
    memLp_iff.2 (lt_of_le_of_lt hw'n ENNReal.ofReal_lt_top)
  have hw'int : Integrable w' := hw'mem.integrable (by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le)
  have hvint : Integrable v := tsamp_integrable_of_lip hL hLip
  have hI : ∫ z, ‖Kη z‖ ≤ C₁ := by simpa using hK1
  refine ⟨C₁ * L, C₁ * F, by positivity, by positivity, ?_, ⟨tsampConv Kη w', ?_, ?_⟩, ?_⟩
  · have := tsamp_conv_lip hKint hL hLip
    intro x y
    refine (this x y).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (KernelGrad.tdist_nonneg _ _)
    nlinarith
  · intro j k
    rw [show PleqT η v = tsampConv Kη v from rfl]
    rw [tsamp_conv_fcoef_comp hd1 hKm hKint hKb hw'int, tsamp_conv_fcoef_comp hd1 hKm hKint hKb hvint,
      hw'rep j k, hKcoef k]
    ring
  · have h1 := tsamp_conv_eLpNorm_le (E := Euc d) hKint hKm hw'm hp1
    refine h1.trans ?_
    calc ENNReal.ofReal (∫ y, ‖Kη y‖) * eLpNorm w' (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal C₁ * ENNReal.ofReal F := mul_le_mul' (ENNReal.ofReal_le_ofReal hI) hw'n
      _ = ENNReal.ofReal (C₁ * F) := (ENNReal.ofReal_mul hC₁.le).symm
  · nlinarith

end HRS.Commutator.TorusNote
