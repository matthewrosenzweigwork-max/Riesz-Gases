import HRS.MS.Fp81S21OscDatum
import HRS.MS.Fp81S21CovCoreDensity

/-!
# HRS S2.1(iii): linearity and the finite-horizon moving covariance bound

The moving noise weight is handled against the fixed thermal probability measure,
using the trajectory's density ratio and joint continuity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

private theorem fp81s21_covcore_rho_joint_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    Continuous fun z : ℝ≥0 × Euc p.d => R.ρ z.1 z.2 := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρβc : Continuous R.ρβ := by
    obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ']
    exact ψ'.continuous
  have hρβpos : ∀ x, 0 < R.ρβ x := fun x => HRS.Whole.u4_thermal_pos R.thermal x
  have hm : (p.d : ℝ) / 2 < ((102 * p.d + 1020 : ℕ) : ℝ) := by
    rw [HRS.MS.R2WinOrbNL.s103n_cast_m]
    nlinarith
  have hclass := HRS.MS.R2WinOrbNL.s103n_small_class R.resulting
    (r := p.C₁ * δ) le_rfl
  exact HRS.MS.R2S11.s11_class_continuous hρβc hρβpos hm hclass

private theorem fp81s21_propOsc_density_u2dec
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {t : ℝ} (_ht : 0 ≤ t) :
    ∃ A : ℝ, ∀ τ ∈ Icc (0 : ℝ) t,
      U2Dec 1 ((p.d + 1 : ℕ) : ℝ) A (R.ρ τ) := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  obtain ⟨c, K, hc, hK0, hρ⟩ := HRS.MS.S104e.s104e_gauss_rho
    p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁ 1 (by omega)
    R.thermal R.resulting
  obtain ⟨P, hP0, hU⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss
    (d := p.d) hc 1 (p.d + 1)
  refine ⟨P * K, fun τ hτ => ?_⟩
  obtain ⟨hreg, hbnd⟩ := hρ τ hτ.1
  exact hU (R.ρ τ) K hK0 hreg (fun k hk x => hbnd k hk x)

private theorem fp81s21_U_linear_of_osc_test
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {φ ψ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ)
    (hψ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ)
    (c : ℝ) {t r : ℝ} (ht : 0 ≤ t) (hr : r ∈ Icc (0 : ℝ) t) :
    r26t3_U R r t (fun x => φ x + c * ψ x) =
      fun x => r26t3_U R r t φ x + c * r26t3_U R r t ψ x := by
  obtain ⟨f, hf⟩ := HRS.Fp81.S21.fp81s21_adjoint_of_osc_test p R hφ ht
  obtain ⟨g, hg⟩ := HRS.Fp81.S21.fp81s21_adjoint_of_osc_test p R hψ ht
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  obtain ⟨A, hA⟩ := fp81s21_propOsc_density_u2dec p R ht
  have hlin0 := HRS.MS.R2WinOrbNL.s103c_lincomb p.hd p.hs0 hsd
    (show (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self p.d)
    R.ρ hA 1 c hf hg
  have hlin : IsClassicalAdjointW (r26t3_coeff R) t
      (fun x => φ x + c * ψ x) (fun q x => f q x + c * g q x) := by
    simpa [r26t3_coeff] using hlin0
  have huF := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hf
  have huG := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hg
  have huSum := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hlin
  have ef : r26t3_U R r t φ = f r := by
    simpa [r26t3_U, r26t3_coeff] using huF r hr
  have eg : r26t3_U R r t ψ = g r := by
    simpa [r26t3_U, r26t3_coeff] using huG r hr
  have esum : r26t3_U R r t (fun x => φ x + c * ψ x) =
      (fun x => f r x + c * g r x) := by
    simpa [r26t3_U, r26t3_coeff] using huSum r hr
  rw [esum, ef, eg]

private theorem fp81s21_U_osc_test_classical
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ)
    {t : ℝ} (ht : 0 ≤ t) :
    IsClassicalAdjointW (r26t3_coeff R) t φ (fun r => r26t3_U R r t φ) := by
  have hex : ∃ f, IsClassicalAdjointW (r26t3_coeff R) t φ f := by
    simpa [r26t3_coeff] using HRS.Fp81.S21.fp81s21_adjoint_of_osc_test p R hφ ht
  let f := Classical.choose hex
  have hf : IsClassicalAdjointW (r26t3_coeff R) t φ f := Classical.choose_spec hex
  have heq : ∀ r, r26t3_U R r t φ = f r := by
    intro r
    change HRS.Whole.propagatorW (r26t3_coeff R) r t φ = f r
    unfold HRS.Whole.propagatorW
    rw [dif_pos hex]
  have hfun : (fun r => r26t3_U R r t φ) = f := funext heq
  rw [hfun]
  exact hf

private theorem fp81s21_covcore_thermal_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) : Continuous R.ρβ := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
    p.hd p.hs0 hsd p.ha p.hβ
  rw [hρeq, ← hψ']
  exact ψ'.continuous

private theorem fp81s21_withDensityReal_le_smul
    {d : ℕ} {ρ σ : Euc d → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hσ : Measurable σ) (hdom : ∀ x, ρ x ≤ K * σ x) :
    HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal K • HRS.Whole.withDensityReal σ := by
  refine Measure.le_iff'.2 fun A => ?_
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply']
  rw [Measure.smul_apply, smul_eq_mul]
  rw [withDensity_apply']
  calc
    ∫⁻ x in A, ENNReal.ofReal (ρ x) ≤
        ∫⁻ x in A, ENNReal.ofReal K * ENNReal.ofReal (σ x) := by
      apply lintegral_mono
      intro x
      calc
        ENNReal.ofReal (ρ x) ≤ ENNReal.ofReal (K * σ x) :=
          ENNReal.ofReal_le_ofReal (hdom x)
        _ = ENNReal.ofReal K * ENNReal.ofReal (σ x) := ENNReal.ofReal_mul hK
    _ = ENNReal.ofReal K * ∫⁻ x in A, ENNReal.ofReal (σ x) := by
      rw [lintegral_const_mul]
      exact ENNReal.measurable_ofReal.comp hσ

private theorem fp81s21_centered_variance_domination
    {d : ℕ} {μ ν : Measure (Euc d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : ℝ} (hK : 0 ≤ K) (hμν : μ ≤ ENNReal.ofReal K • ν)
    {f : Euc d → ℝ} (hfμ : MemLp f 2 μ) (hfν : MemLp f 2 ν) :
    HRS.MS.S111X2.s111x2_centeredSquare μ f ≤
      K * HRS.MS.S111X2.s111x2_centeredSquare ν f := by
  let g : Euc d → ℝ := fun x => f x - HRS.Whole.pair ν f
  have hgm : MemLp g 2 μ := hfμ.sub (memLp_const _)
  have hgn : MemLp g 2 ν := hfν.sub (memLp_const _)
  have hvarμ : HRS.MS.S111X2.s111x2_centeredSquare μ f = ProbabilityTheory.variance f μ := by
    unfold HRS.MS.S111X2.s111x2_centeredSquare
    rw [ProbabilityTheory.variance_eq_integral hfμ.aemeasurable]
    rfl
  have hshift : ProbabilityTheory.variance f μ = ProbabilityTheory.variance g μ := by
    simpa [g, sub_eq_add_neg] using
      (ProbabilityTheory.variance_add_const hfμ.aestronglyMeasurable
        (-HRS.Whole.pair ν f)).symm
  have hvarle : ProbabilityTheory.variance g μ ≤ ∫ x, g x ^ 2 ∂μ :=
    ProbabilityTheory.variance_le_expectation_sq hgm.aestronglyMeasurable
  have hscaled : Integrable (fun x => g x ^ 2) (ENNReal.ofReal K • ν) :=
    hgn.integrable_sq.smul_measure ENNReal.ofReal_ne_top
  have hmeasure := integral_mono_measure hμν
    (Filter.Eventually.of_forall fun x => sq_nonneg (g x)) hscaled
  rw [integral_smul_measure, ENNReal.toReal_ofReal hK, smul_eq_mul] at hmeasure
  calc
    HRS.MS.S111X2.s111x2_centeredSquare μ f = ProbabilityTheory.variance f μ := hvarμ
    _ = ProbabilityTheory.variance g μ := hshift
    _ ≤ ∫ x, g x ^ 2 ∂μ := hvarle
    _ ≤ K * ∫ x, g x ^ 2 ∂ν := hmeasure
    _ = K * HRS.MS.S111X2.s111x2_centeredSquare ν f := by
      simp [g, HRS.MS.S111X2.s111x2_centeredSquare, HRS.Whole.projMean]

private theorem fp81s21_initial_cov_centered_bound
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) {f g : Euc p.d → ℝ}
    (hf : MemLp f 2 (r26t3_mu R 0)) (hg : MemLp g 2 (r26t3_mu R 0)) :
    |HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ f g| ≤
    Real.sqrt (HRS.MS.S111X2.s111x2_centeredSquare (r26t3_mu R 0) f) *
        Real.sqrt (HRS.MS.S111X2.s111x2_centeredSquare (r26t3_mu R 0) g) := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (0 : ℝ) < (p.d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) p.hd)
    linarith [p.hs]
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hP' : IsProbabilityMeasure (r26t3_mu R 0) := hP
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hP'
  obtain ⟨Mg, K, hK⟩ := HRS.MS.S111X2.s111x2_krep_of_tcref
    (le_trans (by norm_num : 1 ≤ 2) p.hd) p.hs0 hsd hc hTc
  have hform := HRS.MS.S111X2.s111x2_responseForm hK p.hγ le_rfl
  exact hform.schwarz f g hf hg

private theorem fp81s21_moving_pair_integral_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {t₁ t₂ T₀ : ℝ} (hT₀ : 0 ≤ T₀) (hT₁ : T₀ ≤ t₁) (hT₂ : T₀ ≤ t₂)
    {φ ψ : Euc p.d → ℝ}
    {f g : ℝ → Euc p.d → ℝ}
    (hf : IsClassicalAdjointW (r26t3_coeff R) t₁ φ f)
    (hg : IsClassicalAdjointW (r26t3_coeff R) t₂ ψ g) :
    ContinuousOn
      (fun v => ∫ x, inner ℝ (gradient (f v) x) (gradient (g v) x) * R.ρ v x)
      (Icc (0 : ℝ) T₀) := by
  obtain ⟨-, hC₁, hdata, -⟩ := r26t3_reference_data p δ hδ hδh R
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hρβc := fp81s21_covcore_thermal_continuous p R
  have hμprob : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμprob
  obtain ⟨Bf, hBf0, hBf⟩ := HRS.MS.S111X1.x1_fderiv_bdd hf
  obtain ⟨Bg, hBg0, hBg⟩ := HRS.MS.S111X1.x1_fderiv_bdd hg
  let F : ℝ → Euc p.d → ℝ := fun v x =>
    (R.ρ (max v 0) x / R.ρβ x) *
      inner ℝ
        (gradient (f (HRS.MS.S111X2.s111x2_clamp t₁ v)) x)
        (gradient (g (HRS.MS.S111X2.s111x2_clamp t₂ v)) x)
  have ht₁₀ : 0 ≤ t₁ := hT₀.trans hT₁
  have ht₂₀ : 0 ≤ t₂ := hT₀.trans hT₂
  have htime : Continuous fun v : ℝ => (⟨max v 0, le_max_right _ _⟩ : ℝ≥0) :=
    (continuous_id.max continuous_const).subtype_mk fun v => le_max_right _ _
  have hclamp₁ : Continuous fun v : ℝ =>
      (⟨HRS.MS.S111X2.s111x2_clamp t₁ v,
        HRS.MS.S111X2.s111x2_clamp_mem ht₁₀ v⟩ : Icc (0 : ℝ) t₁) :=
    (HRS.MS.S111X2.s111x2_clamp_cont t₁).subtype_mk fun v =>
      HRS.MS.S111X2.s111x2_clamp_mem ht₁₀ v
  have hclamp₂ : Continuous fun v : ℝ =>
      (⟨HRS.MS.S111X2.s111x2_clamp t₂ v,
        HRS.MS.S111X2.s111x2_clamp_mem ht₂₀ v⟩ : Icc (0 : ℝ) t₂) :=
    (HRS.MS.S111X2.s111x2_clamp_cont t₂).subtype_mk fun v =>
      HRS.MS.S111X2.s111x2_clamp_mem ht₂₀ v
  have hρmap : Continuous fun z : ℝ × Euc p.d => R.ρ (max z.1 0) z.2 := by
    exact (fp81s21_covcore_rho_joint_continuous p R).comp
      ((htime.comp continuous_fst).prodMk continuous_snd)
  have hβmap : Continuous fun z : ℝ × Euc p.d => R.ρβ z.2 := hρβc.comp continuous_snd
  have hratio : Continuous fun z : ℝ × Euc p.d => R.ρ (max z.1 0) z.2 / R.ρβ z.2 :=
    hρmap.div hβmap (fun z => (HRS.Whole.u4_thermal_pos R.thermal z.2).ne')
  have hgradf : Continuous fun z : ℝ × Euc p.d =>
      gradient (f (HRS.MS.S111X2.s111x2_clamp t₁ z.1)) z.2 :=
    (HRS.MS.S111X1.x1_cont_gradient hf).comp
      ((hclamp₁.comp continuous_fst).prodMk continuous_snd)
  have hgradg : Continuous fun z : ℝ × Euc p.d =>
      gradient (g (HRS.MS.S111X2.s111x2_clamp t₂ z.1)) z.2 :=
    (HRS.MS.S111X1.x1_cont_gradient hg).comp
      ((hclamp₂.comp continuous_fst).prodMk continuous_snd)
  have hFcont : Continuous fun z : ℝ × Euc p.d => F z.1 z.2 := by
    change Continuous fun z : ℝ × Euc p.d =>
      (R.ρ (max z.1 0) z.2 / R.ρβ z.2) *
        inner ℝ
          (gradient (f (HRS.MS.S111X2.s111x2_clamp t₁ z.1)) z.2)
          (gradient (g (HRS.MS.S111X2.s111x2_clamp t₂ z.1)) z.2)
    exact hratio.mul (hgradf.inner hgradg)
  have hbound : ∀ v ∈ Icc (0 : ℝ) T₀, ∀ x, |F v x| ≤ p.C₁ * Bf * Bg := by
    intro v hv x
    have hcl₁ := HRS.MS.S111X2.s111x2_clamp_id ⟨hv.1, hv.2.trans hT₁⟩
    have hcl₂ := HRS.MS.S111X2.s111x2_clamp_id ⟨hv.1, hv.2.trans hT₂⟩
    have hmax : max v 0 = v := max_eq_left hv.1
    have hρv := hdata v hv.1
    have hrat : 0 ≤ R.ρ v x / R.ρβ x := div_nonneg (hρv.2 x).le
      (HRS.Whole.u4_thermal_pos R.thermal x).le
    have hratub : R.ρ v x / R.ρβ x ≤ p.C₁ :=
      (div_le_iff₀ (HRS.Whole.u4_thermal_pos R.thermal x)).2 (by
        have := (R.resulting.ratio v hv.1 x).2
        nlinarith)
    have hinner := abs_real_inner_le_norm
      (gradient (f v) x) (gradient (g v) x)
    have hbf := hBf v ⟨hv.1, hv.2.trans hT₁⟩ x
    have hbg := hBg v ⟨hv.1, hv.2.trans hT₂⟩ x
    simp only [F, hmax, hcl₁, hcl₂]
    rw [abs_mul, abs_of_nonneg hrat]
    calc
      R.ρ v x / R.ρβ x *
          |inner ℝ (gradient (f v) x) (gradient (g v) x)|
          ≤ p.C₁ * (Bf * Bg) := by
            refine mul_le_mul hratub ?_ (abs_nonneg _) hC₁.le
            exact (hinner.trans (mul_le_mul hbf hbg (norm_nonneg _) hBf0))
      _ = p.C₁ * Bf * Bg := by ring
  have hconst : Integrable (fun _ : Euc p.d => p.C₁ * Bf * Bg) μstar := integrable_const _
  have hFparam := HRS.MS.Wad.s85_cont_param (μ := μstar) (t := T₀)
      (F := F) (bd := fun _ : Euc p.d => p.C₁ * Bf * Bg) hconst
    hFcont.continuousOn hbound
  have hρβm : Measurable R.ρβ := hρβc.measurable
  have hρβ0 : ∀ x, 0 ≤ R.ρβ x := fun x => (HRS.Whole.u4_thermal_pos R.thermal x).le
  have hF_eq : ∀ v ∈ Icc (0 : ℝ) T₀,
      (∫ x, inner ℝ (gradient (f v) x) (gradient (g v) x) * R.ρ v x) =
        ∫ x, F v x ∂μstar := by
    intro v hv
    have hcl₁ := HRS.MS.S111X2.s111x2_clamp_id ⟨hv.1, hv.2.trans hT₁⟩
    have hcl₂ := HRS.MS.S111X2.s111x2_clamp_id ⟨hv.1, hv.2.trans hT₂⟩
    have hmax : max v 0 = v := max_eq_left hv.1
    let G : Euc p.d → ℝ := fun x =>
      inner ℝ (gradient (f v) x) (gradient (g v) x)
    have hρvmeas : Measurable (R.ρ v) := (R.resulting.regular v hv.1).measurable
    have hρv0 : ∀ x, 0 ≤ R.ρ v x := fun x => (hdata v hv.1).2 x |>.le
    have hρrewrite := HRS.MP.RdRem.mrr_integral_withDensityReal
      (R.ρ v) hρvmeas hρv0 G
    have hβrewrite := HRS.MP.RdRem.mrr_integral_withDensityReal
      R.ρβ hρβm hρβ0 (fun x => (R.ρ v x / R.ρβ x) * G x)
    calc
      (∫ x, G x * R.ρ v x) = ∫ x, R.ρ v x * G x := by
        congr 1
        funext x
        ring
      _ = ∫ x, G x ∂(HRS.Whole.withDensityReal (R.ρ v)) := hρrewrite.symm
      _ = ∫ x, R.ρβ x * ((R.ρ v x / R.ρβ x) * G x) := by
        rw [hρrewrite]
        apply integral_congr_ae
        filter_upwards with x
        have hx := HRS.Whole.u4_thermal_pos R.thermal x
        symm
        calc
          R.ρβ x * (R.ρ v x / R.ρβ x * G x) =
              (R.ρβ x * (R.ρ v x / R.ρβ x)) * G x := by ring
          _ = R.ρ v x * G x := by
            field_simp [hx.ne']
      _ = ∫ x, F v x ∂μstar := by
        calc
          _ = ∫ x, (R.ρ v x / R.ρβ x) * G x ∂μstar := hβrewrite.symm
          _ = _ := by
            apply integral_congr_ae
            filter_upwards with x
            simp [F, hcl₁, hcl₂, hmax, G]
  have hparam' : ContinuousOn (fun v => ∫ x, F v x ∂μstar) (Icc (0 : ℝ) T₀) := by
    exact hFparam
  exact hparam'.congr fun v hv => hF_eq v hv

private theorem fp81s21_moving_noise_bound
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) {ψ φ : Euc p.d → ℝ}
    {f g : ℝ → Euc p.d → ℝ}
    (hf : IsClassicalAdjointW (r26t3_coeff R) r ψ f)
    (hg : IsClassicalAdjointW (r26t3_coeff R) t φ g)
    (hfProp : ∀ s ∈ Icc (0 : ℝ) r,
      HRS.Whole.propagatorW (r26t3_coeff R) s r ψ = f s)
    (hgProp : ∀ s ∈ Icc (0 : ℝ) t,
      HRS.Whole.propagatorW (r26t3_coeff R) s t φ = g s)
    (hC₁ : 0 < p.C₁)
    (hGf : IntegrableOn
      (fun s => ∫ x, ‖gradient (f s) x‖ ^ 2
        ∂(HRS.Whole.withDensityReal R.ρβ)) (Icc (0 : ℝ) r))
    (hGg : IntegrableOn
      (fun s => ∫ x, ‖gradient (g s) x‖ ^ 2
        ∂(HRS.Whole.withDensityReal R.ρβ)) (Icc (0 : ℝ) t))
    {Ef Eg : ℝ}
    (hEf : (∫ s in Icc (0 : ℝ) r, ∫ x, ‖gradient (f s) x‖ ^ 2
        ∂(HRS.Whole.withDensityReal R.ρβ)) ≤ Ef)
    (hEg : (∫ s in Icc (0 : ℝ) t, ∫ x, ‖gradient (g s) x‖ ^ 2
        ∂(HRS.Whole.withDensityReal R.ρβ)) ≤ Eg) :
    |noiseCovW (r26t3_coeff R) p.β⁻¹ r t ψ φ| ≤
      2 * p.β⁻¹ * Real.sqrt (p.C₁ * Ef) * Real.sqrt (p.C₁ * Eg) := by
  let T : ℝ := min r t
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  let U : ℝ → Euc p.d → Euc p.d := fun s x =>
    Real.sqrt (R.ρ s x) • gradient (f s) x
  let V : ℝ → Euc p.d → Euc p.d := fun s x =>
    Real.sqrt (R.ρ s x) • gradient (g s) x
  have hT0 : 0 ≤ T := le_min hr ht
  have hT_r : T ≤ r := min_le_left _ _
  have hT_t : T ≤ t := min_le_right _ _
  obtain ⟨-, hC₁', hdata, -⟩ := r26t3_reference_data p δ hδ hδh R
  have hρβc := fp81s21_covcore_thermal_continuous p R
  have hρβmeas : Measurable R.ρβ := hρβc.measurable
  have hρβnn : ∀ x, 0 ≤ R.ρβ x := fun x => (HRS.Whole.u4_thermal_pos R.thermal x).le
  have hμstarprob : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμstarprob
  have hBf := HRS.MS.S111X1.x1_fderiv_bdd hf
  have hBg := HRS.MS.S111X1.x1_fderiv_bdd hg
  obtain ⟨Bf, hBf0, hBf⟩ := hBf
  obtain ⟨Bg, hBg0, hBg⟩ := hBg
  have hpairff := fp81s21_moving_pair_integral_continuous p R hδ hδh
    (t₁ := r) (t₂ := r) (T₀ := T) hT0 hT_r hT_r hf hf
  have hpairgg := fp81s21_moving_pair_integral_continuous p R hδ hδh
    (t₁ := t) (t₂ := t) (T₀ := T) hT0 hT_t hT_t hg hg
  have hpairfg := fp81s21_moving_pair_integral_continuous p R hδ hδh
    (t₁ := r) (t₂ := t) (T₀ := T) hT0 hT_r hT_t hf hg
  have hρthermalInt : Integrable R.ρβ :=
    HRS.Whole.Q34.integrable_of_isProbDensity R.thermal.1.1
  have hGfT : IntegrableOn
      (fun s => ∫ x, ‖gradient (f s) x‖ ^ 2 ∂μstar) (Icc (0 : ℝ) T) :=
    hGf.mono_set (Icc_subset_Icc_right hT_r)
  have hGgT : IntegrableOn
      (fun s => ∫ x, ‖gradient (g s) x‖ ^ 2 ∂μstar) (Icc (0 : ℝ) T) :=
    hGg.mono_set (Icc_subset_Icc_right hT_t)
  have hscale : ∀ s ∈ Icc (0 : ℝ) T, ∀ x (a b : Euc p.d),
      inner ℝ (Real.sqrt (R.ρ s x) • a) (Real.sqrt (R.ρ s x) • b) =
        R.ρ s x * inner ℝ a b := by
    intro s hs x a b
    have hρnn : 0 ≤ R.ρ s x := (hdata s hs.1).2 x |>.le
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial, smul_eq_mul]
    calc
      Real.sqrt (R.ρ s x) * (Real.sqrt (R.ρ s x) * inner ℝ a b) =
          (Real.sqrt (R.ρ s x) * Real.sqrt (R.ρ s x)) * inner ℝ a b := by ring
      _ = R.ρ s x * inner ℝ a b := by
        rw [show Real.sqrt (R.ρ s x) * Real.sqrt (R.ρ s x) =
          (Real.sqrt (R.ρ s x)) ^ 2 by ring, Real.sq_sqrt hρnn]
  have hpointFF : ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
      inner ℝ (U s x) (U s x) * 1 =
        inner ℝ (gradient (f s) x) (gradient (f s) x) * R.ρ s x := by
    intro s hs x
    change inner ℝ (Real.sqrt (R.ρ s x) • gradient (f s) x)
        (Real.sqrt (R.ρ s x) • gradient (f s) x) * 1 = _
    rw [hscale s hs x]
    ring
  have hpointGG : ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
      inner ℝ (V s x) (V s x) * 1 =
        inner ℝ (gradient (g s) x) (gradient (g s) x) * R.ρ s x := by
    intro s hs x
    change inner ℝ (Real.sqrt (R.ρ s x) • gradient (g s) x)
        (Real.sqrt (R.ρ s x) • gradient (g s) x) * 1 = _
    rw [hscale s hs x]
    ring
  have hpointFG : ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
      inner ℝ (U s x) (V s x) * 1 =
        inner ℝ (gradient (f s) x) (gradient (g s) x) * R.ρ s x := by
    intro s hs x
    change inner ℝ (Real.sqrt (R.ρ s x) • gradient (f s) x)
        (Real.sqrt (R.ρ s x) • gradient (g s) x) * 1 = _
    rw [hscale s hs x]
    ring
  have hxuu : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun x => inner ℝ (U s x) (U s x) * 1) := by
    intro s hs
    have hρi := HRS.Whole.Q34.integrable_of_isProbDensity (hdata s hs.1).1
    have hρnn : ∀ x, 0 ≤ R.ρ s x := fun x => (hdata s hs.1).2 x |>.le
    have hsR : s ∈ Icc (0 : ℝ) r := ⟨hs.1, hs.2.trans hT_r⟩
    have hp := HRS.MS.S111X1.x1_pair_integrable hf hf hρi hρnn hsR hsR
    exact hp.congr (Filter.Eventually.of_forall fun x => (hpointFF s hs x).symm)
  have hxvv : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun x => inner ℝ (V s x) (V s x) * 1) := by
    intro s hs
    have hρi := HRS.Whole.Q34.integrable_of_isProbDensity (hdata s hs.1).1
    have hρnn : ∀ x, 0 ≤ R.ρ s x := fun x => (hdata s hs.1).2 x |>.le
    have hsT : s ∈ Icc (0 : ℝ) t := ⟨hs.1, hs.2.trans hT_t⟩
    have hp := HRS.MS.S111X1.x1_pair_integrable hg hg hρi hρnn hsT hsT
    exact hp.congr (Filter.Eventually.of_forall fun x => (hpointGG s hs x).symm)
  have hxuv : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun x => inner ℝ (U s x) (V s x) * 1) := by
    intro s hs
    have hρi := HRS.Whole.Q34.integrable_of_isProbDensity (hdata s hs.1).1
    have hρnn : ∀ x, 0 ≤ R.ρ s x := fun x => (hdata s hs.1).2 x |>.le
    have hsR : s ∈ Icc (0 : ℝ) r := ⟨hs.1, hs.2.trans hT_r⟩
    have hsT : s ∈ Icc (0 : ℝ) t := ⟨hs.1, hs.2.trans hT_t⟩
    have hp := HRS.MS.S111X1.x1_pair_integrable hf hg hρi hρnn hsR hsT
    exact hp.congr (Filter.Eventually.of_forall fun x => (hpointFG s hs x).symm)
  have hsu : IntegrableOn
      (fun s => ∫ x, inner ℝ (U s x) (U s x) * 1) (Icc (0 : ℝ) T) := by
    refine hpairff.integrableOn_Icc.congr_fun (fun s hs => ?_) measurableSet_Icc
    apply integral_congr_ae
    filter_upwards with x
    exact (hpointFF s hs x).symm
  have hsv : IntegrableOn
      (fun s => ∫ x, inner ℝ (V s x) (V s x) * 1) (Icc (0 : ℝ) T) := by
    refine hpairgg.integrableOn_Icc.congr_fun (fun s hs => ?_) measurableSet_Icc
    apply integral_congr_ae
    filter_upwards with x
    exact (hpointGG s hs x).symm
  have hsuv : IntegrableOn
      (fun s => ∫ x, inner ℝ (U s x) (V s x) * 1) (Icc (0 : ℝ) T) := by
    refine hpairfg.integrableOn_Icc.congr_fun (fun s hs => ?_) measurableSet_Icc
    apply integral_congr_ae
    filter_upwards with x
    exact (hpointFG s hs x).symm
  let Iuu : ℝ := ∫ s in Icc (0 : ℝ) T, ∫ x, inner ℝ (U s x) (U s x) * 1
  let Ivv : ℝ := ∫ s in Icc (0 : ℝ) T, ∫ x, inner ℝ (V s x) (V s x) * 1
  let Iuv : ℝ := ∫ s in Icc (0 : ℝ) T, ∫ x, inner ℝ (U s x) (V s x) * 1
  have hcs := HRS.MS.S111X1.x1_cs (fun _ => zero_le_one) U V T hxuu hxvv hxuv hsu hsv hsuv
  have hIuun : 0 ≤ Iuu := by
    refine setIntegral_nonneg measurableSet_Icc fun s _ => integral_nonneg fun x => ?_
    exact mul_nonneg real_inner_self_nonneg zero_le_one
  have hIvvn : 0 ≤ Ivv := by
    refine setIntegral_nonneg measurableSet_Icc fun s _ => integral_nonneg fun x => ?_
    exact mul_nonneg real_inner_self_nonneg zero_le_one
  have hIuuEq : Iuu = ∫ s in Icc (0 : ℝ) T,
      ∫ x, inner ℝ (gradient (f s) x) (gradient (f s) x) * R.ρ s x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    apply integral_congr_ae
    filter_upwards with x
    exact hpointFF s hs x
  have hIvvEq : Ivv = ∫ s in Icc (0 : ℝ) T,
      ∫ x, inner ℝ (gradient (g s) x) (gradient (g s) x) * R.ρ s x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    apply integral_congr_ae
    filter_upwards with x
    exact hpointGG s hs x
  have hdiagF : ∀ s ∈ Icc (0 : ℝ) T,
      (∫ x, inner ℝ (gradient (f s) x) (gradient (f s) x) * R.ρ s x) ≤
        p.C₁ * ∫ x, ‖gradient (f s) x‖ ^ 2 ∂μstar := by
    intro s hs
    have hρvmeas : Measurable (R.ρ s) := (R.resulting.regular s hs.1).measurable
    have hρvnn : ∀ x, 0 ≤ R.ρ s x := fun x => (hdata s hs.1).2 x |>.le
    have hμdom := fp81s21_withDensityReal_le_smul hC₁.le hρβmeas
      (fun x => (R.resulting.ratio s hs.1 x).2)
    have hgradc : Continuous fun x => gradient (f s) x :=
      (HRS.MS.S111X1.x1_cont_gradient hf).comp
        (Continuous.prodMk (continuous_const (y := (⟨s, ⟨hs.1, hs.2.trans hT_r⟩⟩ : Icc (0 : ℝ) r))) continuous_id)
    have hgradmem : MemLp (fun x => ‖gradient (f s) x‖) 2 μstar :=
      MemLp.of_bound hgradc.norm.aestronglyMeasurable Bf
        (Filter.Eventually.of_forall fun x => by
          simpa using hBf s ⟨hs.1, hs.2.trans hT_r⟩ x)
    have hgradint : Integrable (fun x => ‖gradient (f s) x‖ ^ 2) μstar := hgradmem.integrable_sq
    have hscaled : Integrable (fun x => ‖gradient (f s) x‖ ^ 2)
        (ENNReal.ofReal p.C₁ • μstar) :=
      hgradint.smul_measure ENNReal.ofReal_ne_top
    have hmono := integral_mono_measure hμdom
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖gradient (f s) x‖) hscaled
    rw [integral_smul_measure, ENNReal.toReal_ofReal hC₁.le, smul_eq_mul] at hmono
    have hρrewrite := HRS.MP.RdRem.mrr_integral_withDensityReal
      (R.ρ s) hρvmeas hρvnn (fun x => ‖gradient (f s) x‖ ^ 2)
    have heq : (∫ x, inner ℝ (gradient (f s) x) (gradient (f s) x) * R.ρ s x) =
        ∫ x, ‖gradient (f s) x‖ ^ 2 ∂(HRS.Whole.withDensityReal (R.ρ s)) := by
      calc
        _ = ∫ x, R.ρ s x * ‖gradient (f s) x‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards with x
          rw [real_inner_self_eq_norm_sq]
          ring
        _ = _ := hρrewrite.symm
    exact heq.trans_le hmono
  have hdiagG : ∀ s ∈ Icc (0 : ℝ) T,
      (∫ x, inner ℝ (gradient (g s) x) (gradient (g s) x) * R.ρ s x) ≤
        p.C₁ * ∫ x, ‖gradient (g s) x‖ ^ 2 ∂μstar := by
    intro s hs
    have hρvmeas : Measurable (R.ρ s) := (R.resulting.regular s hs.1).measurable
    have hρvnn : ∀ x, 0 ≤ R.ρ s x := fun x => (hdata s hs.1).2 x |>.le
    have hμdom := fp81s21_withDensityReal_le_smul hC₁.le hρβmeas
      (fun x => (R.resulting.ratio s hs.1 x).2)
    have hgradc : Continuous fun x => gradient (g s) x :=
      (HRS.MS.S111X1.x1_cont_gradient hg).comp
        (Continuous.prodMk (continuous_const (y := (⟨s, ⟨hs.1, hs.2.trans hT_t⟩⟩ : Icc (0 : ℝ) t))) continuous_id)
    have hgradmem : MemLp (fun x => ‖gradient (g s) x‖) 2 μstar :=
      MemLp.of_bound hgradc.norm.aestronglyMeasurable Bg
        (Filter.Eventually.of_forall fun x => by
          simpa using hBg s ⟨hs.1, hs.2.trans hT_t⟩ x)
    have hgradint : Integrable (fun x => ‖gradient (g s) x‖ ^ 2) μstar := hgradmem.integrable_sq
    have hscaled : Integrable (fun x => ‖gradient (g s) x‖ ^ 2)
        (ENNReal.ofReal p.C₁ • μstar) :=
      hgradint.smul_measure ENNReal.ofReal_ne_top
    have hmono := integral_mono_measure hμdom
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖gradient (g s) x‖) hscaled
    rw [integral_smul_measure, ENNReal.toReal_ofReal hC₁.le, smul_eq_mul] at hmono
    have hρrewrite := HRS.MP.RdRem.mrr_integral_withDensityReal
      (R.ρ s) hρvmeas hρvnn (fun x => ‖gradient (g s) x‖ ^ 2)
    have heq : (∫ x, inner ℝ (gradient (g s) x) (gradient (g s) x) * R.ρ s x) =
        ∫ x, ‖gradient (g s) x‖ ^ 2 ∂(HRS.Whole.withDensityReal (R.ρ s)) := by
      calc
        _ = ∫ x, R.ρ s x * ‖gradient (g s) x‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards with x
          rw [real_inner_self_eq_norm_sq]
          ring
        _ = _ := hρrewrite.symm
    exact heq.trans_le hmono
  have hGfTbound : ∫ s in Icc (0 : ℝ) T, ∫ x, ‖gradient (f s) x‖ ^ 2 ∂μstar ≤ Ef := by
    calc
      _ ≤ ∫ s in Icc (0 : ℝ) r, ∫ x, ‖gradient (f s) x‖ ^ 2 ∂μstar := by
        refine setIntegral_mono_set hGf ?_
          (Filter.Eventually.of_forall (Icc_subset_Icc_right hT_r))
        exact Filter.Eventually.of_forall fun s => integral_nonneg fun x => sq_nonneg _
      _ ≤ Ef := hEf
  have hGgTbound : ∫ s in Icc (0 : ℝ) T, ∫ x, ‖gradient (g s) x‖ ^ 2 ∂μstar ≤ Eg := by
    calc
      _ ≤ ∫ s in Icc (0 : ℝ) t, ∫ x, ‖gradient (g s) x‖ ^ 2 ∂μstar := by
        refine setIntegral_mono_set hGg ?_
          (Filter.Eventually.of_forall (Icc_subset_Icc_right hT_t))
        exact Filter.Eventually.of_forall fun s => integral_nonneg fun x => sq_nonneg _
      _ ≤ Eg := hEg
  have hIuuBound : Iuu ≤ p.C₁ * Ef := by
    rw [hIuuEq]
    calc
      _ ≤ ∫ s in Icc (0 : ℝ) T, p.C₁ *
          (∫ x, ‖gradient (f s) x‖ ^ 2 ∂μstar) := by
        refine setIntegral_mono_on hpairff.integrableOn_Icc
          (hGfT.const_mul p.C₁) measurableSet_Icc ?_
        intro s hs
        exact hdiagF s hs
      _ = p.C₁ * ∫ s in Icc (0 : ℝ) T,
          ∫ x, ‖gradient (f s) x‖ ^ 2 ∂μstar := by rw [integral_const_mul]
      _ ≤ p.C₁ * Ef := mul_le_mul_of_nonneg_left hGfTbound hC₁.le
  have hIvvBound : Ivv ≤ p.C₁ * Eg := by
    rw [hIvvEq]
    calc
      _ ≤ ∫ s in Icc (0 : ℝ) T, p.C₁ *
          (∫ x, ‖gradient (g s) x‖ ^ 2 ∂μstar) := by
        refine setIntegral_mono_on hpairgg.integrableOn_Icc
          (hGgT.const_mul p.C₁) measurableSet_Icc ?_
        intro s hs
        exact hdiagG s hs
      _ = p.C₁ * ∫ s in Icc (0 : ℝ) T,
          ∫ x, ‖gradient (g s) x‖ ^ 2 ∂μstar := by rw [integral_const_mul]
      _ ≤ p.C₁ * Eg := mul_le_mul_of_nonneg_left hGgTbound hC₁.le
  have hIuvEq : Iuv = ∫ s in Icc (0 : ℝ) T,
      ∫ x, inner ℝ (gradient (f s) x) (gradient (g s) x) * R.ρ s x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    apply integral_congr_ae
    filter_upwards with x
    exact hpointFG s hs x
  have hPropEq :
      (∫ s in Icc (0 : ℝ) T, ∫ x, inner ℝ
        (gradient (HRS.Whole.propagatorW (r26t3_coeff R) s r ψ) x)
        (gradient (HRS.Whole.propagatorW (r26t3_coeff R) s t φ) x) * R.ρ s x) = Iuv := by
    calc
      _ = ∫ s in Icc (0 : ℝ) T,
          ∫ x, inner ℝ (gradient (f s) x) (gradient (g s) x) * R.ρ s x := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro s hs
        have hsR : s ∈ Icc (0 : ℝ) r := ⟨hs.1, hs.2.trans hT_r⟩
        have hsT : s ∈ Icc (0 : ℝ) t := ⟨hs.1, hs.2.trans hT_t⟩
        apply integral_congr_ae
        filter_upwards with x
        rw [hfProp s hsR, hgProp s hsT]
      _ = Iuv := hIuvEq.symm
  have hIuvCS : Iuv ^ 2 ≤ Iuu * Ivv := hcs
  have hIuvabs : |Iuv| ≤ Real.sqrt Iuu * Real.sqrt Ivv := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1
    rw [sq_abs, mul_pow, Real.sq_sqrt hIuun, Real.sq_sqrt hIvvn]
    exact hIuvCS
  have hIuuSqrt : Real.sqrt Iuu ≤ Real.sqrt (p.C₁ * Ef) :=
    Real.sqrt_le_sqrt hIuuBound
  have hIvvSqrt : Real.sqrt Ivv ≤ Real.sqrt (p.C₁ * Eg) :=
    Real.sqrt_le_sqrt hIvvBound
  have hq : 0 < 2 * p.β⁻¹ := mul_pos (by norm_num) (inv_pos.mpr p.hβ)
  have hPropEq' :
      (∫ s in Icc (0 : ℝ) (min r t), ∫ x, inner ℝ
        (gradient (HRS.Whole.propagatorW (r26t3_coeff R) s r ψ) x)
        (gradient (HRS.Whole.propagatorW (r26t3_coeff R) s t φ) x) * R.ρ s x) = Iuv := by
    simpa [T] using hPropEq
  unfold HRS.Whole.noiseCovW
  change |2 * p.β⁻¹ *
      (∫ s in Icc (0 : ℝ) (min r t), ∫ x, inner ℝ
        (gradient (HRS.Whole.propagatorW (r26t3_coeff R) s r ψ) x)
        (gradient (HRS.Whole.propagatorW (r26t3_coeff R) s t φ) x) * R.ρ s x)| ≤ _
  rw [hPropEq']
  calc
    |2 * p.β⁻¹ * Iuv| = 2 * p.β⁻¹ * |Iuv| := by
      rw [abs_mul, abs_of_pos hq]
    _ ≤ 2 * p.β⁻¹ * (Real.sqrt Iuu * Real.sqrt Ivv) :=
      mul_le_mul_of_nonneg_left hIuvabs hq.le
    _ ≤ 2 * p.β⁻¹ * (Real.sqrt (p.C₁ * Ef) * Real.sqrt (p.C₁ * Eg)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul hIuuSqrt hIvvSqrt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · exact hq.le
    _ = 2 * p.β⁻¹ * Real.sqrt (p.C₁ * Ef) * Real.sqrt (p.C₁ * Eg) := by ring

private theorem fp81s21_covcore_bound_at
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {Cdec cdec CE : ℝ} (hCdec : 0 < Cdec) (hcdec : 0 < cdec)
    (hCE : 0 < CE)
    (hAdjointBounds : ∀ H : ℝ, 0 < H →
      ∀ (terminal : Euc p.d → ℝ) (u : ℝ → Euc p.d → ℝ),
        IsClassicalAdjointW (r26t3_coeff R) H terminal u →
        IntegrableOn
            (fun s => ∫ x, ‖gradient (u s) x‖ ^ 2
              ∂(HRS.Whole.withDensityReal R.ρβ)) (Icc (0 : ℝ) H) ∧
          (∀ s ∈ Icc (0 : ℝ) H,
            HRS.MS.S111X2.s111x2_centeredSquare (HRS.Whole.withDensityReal R.ρβ) (u s) ≤
              Cdec * Real.exp (-cdec * (H - s)) *
                HRS.MS.S111X2.s111x2_centeredSquare
                  (HRS.Whole.withDensityReal R.ρβ) terminal) ∧
          (∫ s in Icc (0 : ℝ) H, ∫ x, ‖gradient (u s) x‖ ^ 2
              ∂(HRS.Whole.withDensityReal R.ρβ)) ≤
            CE * HRS.MS.S111X2.s111x2_centeredSquare
              (HRS.Whole.withDensityReal R.ρβ) terminal)
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ ψ : Euc p.d → ℝ, IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ →
        MemLp ψ 2 (HRS.Whole.withDensityReal (R.ρ r)) →
        |HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ φ| ≤
          B * Real.sqrt (∫ x, ψ x ^ 2
            ∂(HRS.Whole.withDensityReal (R.ρ r))) := by
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  let μr : Measure (Euc p.d) := HRS.Whole.withDensityReal (R.ρ r)
  let μ₀ : Measure (Euc p.d) := HRS.Whole.withDensityReal (R.ρ 0)
  obtain ⟨-, hC₁, hdata, -⟩ := r26t3_reference_data p δ hδ hδh R
  have hρβmeas : Measurable R.ρβ := fp81s21_covcore_thermal_continuous p R |>.measurable
  have hρβnn : ∀ x, 0 ≤ R.ρβ x := fun x => (HRS.Whole.u4_thermal_pos R.thermal x).le
  have hμstarprob : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμstarprob
  have hμ₀prob : IsProbabilityMeasure μ₀ :=
    HRS.Whole.Q34.isProbabilityMeasure_nu (hdata 0 le_rfl).1
  letI : IsProbabilityMeasure μ₀ := hμ₀prob
  have hρ₀dom := fp81s21_withDensityReal_le_smul hC₁.le hρβmeas
    (fun x => (R.resulting.ratio 0 le_rfl x).2)
  have hρrmeas : Measurable (R.ρ r) := (R.resulting.regular r hr).measurable
  have hρβr : ∀ x, R.ρβ x ≤ p.C₁ * R.ρ r x := by
    intro x
    calc
      R.ρβ x = p.C₁ * (p.C₁⁻¹ * R.ρβ x) := by
        field_simp [ne_of_gt hC₁]
      _ ≤ p.C₁ * R.ρ r x :=
        mul_le_mul_of_nonneg_left (R.resulting.ratio r hr x).1 hC₁.le
  have hμstar_rdom := fp81s21_withDensityReal_le_smul hC₁.le hρrmeas hρβr
  obtain ⟨M, hM, hthermalBound⟩ := sol13_uniform_thermal_sup_bound p
  have hρβupper : ∀ x, R.ρβ x ≤ M := hthermalBound δ R
  have hφstar : MemLp φ 2 μstar :=
    HRS.MS.S111X1.x1_osc_memLp hρβmeas hρβnn hρβupper hφ
  have hrawφstar : Integrable (fun x => φ x ^ 2) μstar := hφstar.integrable_sq
  have hvarφnn : 0 ≤ HRS.MS.S111X2.s111x2_centeredSquare μstar φ :=
    integral_nonneg fun x => sq_nonneg _
  have hvarφ : HRS.MS.S111X2.s111x2_centeredSquare μstar φ ≤
      ∫ x, φ x ^ 2 ∂μstar := HRS.MS.R26T3.s21f_centered_le μstar hφstar
  let D : ℝ := max Cdec 1
  have hD1 : 1 ≤ D := le_max_right _ _
  have hDC : Cdec ≤ D := le_max_left _ _
  have hDnn : 0 ≤ D := le_trans (le_of_lt hCdec) hDC
  let Kψ : ℝ := p.C₁ ^ 2 * D
  let Kφ : ℝ := p.C₁ * D * HRS.MS.S111X2.s111x2_centeredSquare μstar φ
  have hKψnn : 0 ≤ Kψ := by positivity
  have hKφnn : 0 ≤ Kφ := by positivity
  let Eg : ℝ := CE * HRS.MS.S111X2.s111x2_centeredSquare μstar φ
  let BN : ℝ := 2 * p.β⁻¹ * p.C₁ * Real.sqrt CE * Real.sqrt (p.C₁ * Eg)
  have hBNnn : 0 ≤ BN := by
    dsimp [BN]
    have hβinv : 0 ≤ p.β⁻¹ := inv_nonneg.mpr p.hβ.le
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hβinv) hC₁.le)
      (Real.sqrt_nonneg CE)) (Real.sqrt_nonneg (p.C₁ * Eg))
  let B : ℝ := Real.sqrt Kψ * Real.sqrt Kφ + BN
  have hBnn : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hBnn, ?_⟩
  intro ψ hψ hψr
  have hψstar : MemLp ψ 2 μstar :=
    HRS.MS.S111X1.x1_osc_memLp hρβmeas hρβnn hρβupper hψ
  have hrawψ : Integrable (fun x => ψ x ^ 2) μr := hψr.integrable_sq
  have hrawψnn : 0 ≤ ∫ x, ψ x ^ 2 ∂μr := integral_nonneg fun x => sq_nonneg _
  have hscaledψ : Integrable (fun x => ψ x ^ 2)
      (ENNReal.ofReal p.C₁ • μr) := hrawψ.smul_measure ENNReal.ofReal_ne_top
  have hthermalRawψ := integral_mono_measure hμstar_rdom
    (Filter.Eventually.of_forall fun x => sq_nonneg (ψ x)) hscaledψ
  rw [integral_smul_measure, ENNReal.toReal_ofReal hC₁.le, smul_eq_mul] at hthermalRawψ
  have hvarψ : HRS.MS.S111X2.s111x2_centeredSquare μstar ψ ≤
      p.C₁ * ∫ x, ψ x ^ 2 ∂μr := by
    exact (HRS.MS.R26T3.s21f_centered_le μstar hψstar).trans hthermalRawψ
  have hvarψnn : 0 ≤ HRS.MS.S111X2.s111x2_centeredSquare μstar ψ :=
    integral_nonneg fun x => sq_nonneg _
  let f : ℝ → Euc p.d → ℝ := fun s => r26t3_U R s r ψ
  let g : ℝ → Euc p.d → ℝ := fun s => r26t3_U R s t φ
  have hf : IsClassicalAdjointW (r26t3_coeff R) r ψ f := by
    simpa [f] using fp81s21_U_osc_test_classical p R hψ hr
  have hg : IsClassicalAdjointW (r26t3_coeff R) t φ g := by
    simpa [g] using fp81s21_U_osc_test_classical p R hφ ht
  have hf₀μ₀ : MemLp (f 0) 2 μ₀ := by
    exact HRS.MS.S111X1.x1_classical_memLp hf ⟨le_rfl, hr⟩ μ₀
  have hg₀μ₀ : MemLp (g 0) 2 μ₀ := by
    exact HRS.MS.S111X1.x1_classical_memLp hg ⟨le_rfl, ht⟩ μ₀
  have hf₀star : MemLp (f 0) 2 μstar := by
    exact HRS.MS.S111X1.x1_classical_memLp hf ⟨le_rfl, hr⟩ μstar
  have hg₀star : MemLp (g 0) 2 μstar := by
    exact HRS.MS.S111X1.x1_classical_memLp hg ⟨le_rfl, ht⟩ μstar
  have hvarμ₀f := fp81s21_centered_variance_domination hC₁.le hρ₀dom hf₀μ₀ hf₀star
  have hvarμ₀g := fp81s21_centered_variance_domination hC₁.le hρ₀dom hg₀μ₀ hg₀star
  have hdecayf : HRS.MS.S111X2.s111x2_centeredSquare μstar (f 0) ≤
      D * HRS.MS.S111X2.s111x2_centeredSquare μstar ψ := by
    by_cases hr0 : r = 0
    · subst r
      have hterminal : f 0 = ψ := hf.terminal
      rw [hterminal]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD1 hvarψnn
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hdecay := (hAdjointBounds r hrpos ψ f hf).2.1 0 ⟨le_rfl, hr⟩
      have hexp : Real.exp (-cdec * (r - 0)) ≤ 1 := by
        apply Real.exp_le_one_iff.2
        nlinarith [mul_nonneg hcdec.le hr]
      have hcoef : Cdec * Real.exp (-cdec * (r - 0)) ≤ D := by
        calc
          _ ≤ Cdec * 1 := mul_le_mul_of_nonneg_left hexp hCdec.le
          _ ≤ D := by simpa only [mul_one] using hDC
      calc
        _ ≤ Cdec * Real.exp (-cdec * (r - 0)) *
              HRS.MS.S111X2.s111x2_centeredSquare μstar ψ := hdecay
        _ ≤ D * HRS.MS.S111X2.s111x2_centeredSquare μstar ψ :=
          mul_le_mul_of_nonneg_right hcoef hvarψnn
  have hdecayg : HRS.MS.S111X2.s111x2_centeredSquare μstar (g 0) ≤
      D * HRS.MS.S111X2.s111x2_centeredSquare μstar φ := by
    by_cases ht0 : t = 0
    · subst t
      have hterminal : g 0 = φ := hg.terminal
      rw [hterminal]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD1 hvarφnn
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hdecay := (hAdjointBounds t htpos φ g hg).2.1 0 ⟨le_rfl, ht⟩
      have hexp : Real.exp (-cdec * (t - 0)) ≤ 1 := by
        apply Real.exp_le_one_iff.2
        nlinarith [mul_nonneg hcdec.le ht]
      have hcoef : Cdec * Real.exp (-cdec * (t - 0)) ≤ D := by
        calc
          _ ≤ Cdec * 1 := mul_le_mul_of_nonneg_left hexp hCdec.le
          _ ≤ D := by simpa only [mul_one] using hDC
      calc
        _ ≤ Cdec * Real.exp (-cdec * (t - 0)) *
              HRS.MS.S111X2.s111x2_centeredSquare μstar φ := hdecay
        _ ≤ D * HRS.MS.S111X2.s111x2_centeredSquare μstar φ :=
          mul_le_mul_of_nonneg_right hcoef hvarφnn
  have hvarf : HRS.MS.S111X2.s111x2_centeredSquare μ₀ (f 0) ≤ Kψ *
      (∫ x, ψ x ^ 2 ∂μr) := by
    calc
      _ ≤ p.C₁ * HRS.MS.S111X2.s111x2_centeredSquare μstar (f 0) := hvarμ₀f
      _ ≤ p.C₁ * (D * HRS.MS.S111X2.s111x2_centeredSquare μstar ψ) :=
        mul_le_mul_of_nonneg_left hdecayf hC₁.le
      _ ≤ p.C₁ * (D * (p.C₁ * ∫ x, ψ x ^ 2 ∂μr)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hvarψ hDnn) hC₁.le
      _ = Kψ * (∫ x, ψ x ^ 2 ∂μr) := by dsimp [Kψ]; ring
  have hvarg : HRS.MS.S111X2.s111x2_centeredSquare μ₀ (g 0) ≤ Kφ := by
    calc
      _ ≤ p.C₁ * HRS.MS.S111X2.s111x2_centeredSquare μstar (g 0) := hvarμ₀g
      _ ≤ p.C₁ * (D * HRS.MS.S111X2.s111x2_centeredSquare μstar φ) :=
        mul_le_mul_of_nonneg_left hdecayg hC₁.le
      _ = Kφ := by dsimp [Kφ]; ring
  have hvarf_nonneg : 0 ≤ HRS.MS.S111X2.s111x2_centeredSquare μ₀ (f 0) :=
    integral_nonneg fun x => sq_nonneg _
  have hvarg_nonneg : 0 ≤ HRS.MS.S111X2.s111x2_centeredSquare μ₀ (g 0) :=
    integral_nonneg fun x => sq_nonneg _
  have hrootf : Real.sqrt (HRS.MS.S111X2.s111x2_centeredSquare μ₀ (f 0)) ≤
      Real.sqrt Kψ * Real.sqrt (∫ x, ψ x ^ 2 ∂μr) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1
    rw [Real.sq_sqrt hvarf_nonneg, mul_pow, Real.sq_sqrt hKψnn, Real.sq_sqrt hrawψnn]
    exact hvarf
  have hrootg : Real.sqrt (HRS.MS.S111X2.s111x2_centeredSquare μ₀ (g 0)) ≤ Real.sqrt Kφ :=
    Real.sqrt_le_sqrt hvarg
  have hinit := fp81s21_initial_cov_centered_bound p hδ hδh R hf₀μ₀ hg₀μ₀
  have hinitBound :
      |HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ₀ p.γ (f 0) (g 0)| ≤
        (Real.sqrt Kψ * Real.sqrt Kφ) *
          Real.sqrt (∫ x, ψ x ^ 2 ∂μr) := by
    calc
      _ ≤ Real.sqrt (HRS.MS.S111X2.s111x2_centeredSquare μ₀ (f 0)) *
          Real.sqrt (HRS.MS.S111X2.s111x2_centeredSquare μ₀ (g 0)) := hinit
      _ ≤ (Real.sqrt Kψ * Real.sqrt (∫ x, ψ x ^ 2 ∂μr)) * Real.sqrt Kφ :=
        mul_le_mul hrootf hrootg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = (Real.sqrt Kψ * Real.sqrt Kφ) *
          Real.sqrt (∫ x, ψ x ^ 2 ∂μr) := by ring
  let Ef : ℝ := CE * (p.C₁ * ∫ x, ψ x ^ 2 ∂μr)
  have hEfnn : 0 ≤ Ef := by dsimp [Ef]; positivity
  have hEgnn : 0 ≤ Eg := by dsimp [Eg]; positivity
  have hnoiseBound :
      |noiseCovW (r26t3_coeff R) p.β⁻¹ r t ψ φ| ≤
        BN * Real.sqrt (∫ x, ψ x ^ 2 ∂μr) := by
    by_cases hrpos : 0 < r
    · by_cases htpos : 0 < t
      · obtain ⟨hGfint, -, hGfbound⟩ := hAdjointBounds r hrpos ψ f hf
        obtain ⟨hGgint, -, hGgbound⟩ := hAdjointBounds t htpos φ g hg
        have hnoise := fp81s21_moving_noise_bound p R hδ hδh hr ht
          (ψ := ψ) (φ := φ) hf hg (by intro s hs; rfl) (by intro s hs; rfl) hC₁
          hGfint hGgint (Ef := Ef) (Eg := Eg) ?_ ?_
        · have hrootEf : Real.sqrt (p.C₁ * Ef) =
              p.C₁ * Real.sqrt CE * Real.sqrt (∫ x, ψ x ^ 2 ∂μr) := by
            dsimp [Ef]
            rw [show p.C₁ * (CE * (p.C₁ * ∫ x, ψ x ^ 2 ∂μr)) =
              (p.C₁ ^ 2 * CE) * (∫ x, ψ x ^ 2 ∂μr) by ring,
              Real.sqrt_mul (mul_nonneg (sq_nonneg _) hCE.le),
              Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC₁.le]
          have : |noiseCovW (r26t3_coeff R) p.β⁻¹ r t ψ φ| ≤
              2 * p.β⁻¹ * Real.sqrt (p.C₁ * Ef) * Real.sqrt (p.C₁ * Eg) := hnoise
          rw [hrootEf] at this
          dsimp [BN]
          calc
            _ ≤ 2 * p.β⁻¹ * (p.C₁ * Real.sqrt CE *
                  Real.sqrt (∫ x, ψ x ^ 2 ∂μr)) * Real.sqrt (p.C₁ * Eg) := this
            _ = (2 * p.β⁻¹ * p.C₁ * Real.sqrt CE * Real.sqrt (p.C₁ * Eg)) *
                Real.sqrt (∫ x, ψ x ^ 2 ∂μr) := by ring
        · calc
            (∫ s in Icc (0 : ℝ) r, ∫ x, ‖gradient (f s) x‖ ^ 2 ∂μstar)
                ≤ CE * HRS.MS.S111X2.s111x2_centeredSquare μstar ψ := hGfbound
            _ ≤ Ef := by dsimp [Ef]; exact mul_le_mul_of_nonneg_left hvarψ hCE.le
        · simpa [μstar, Eg] using hGgbound
      · have htzero : t = 0 := le_antisymm (le_of_not_gt htpos) ht
        subst t
        have hzero : noiseCovW (r26t3_coeff R) p.β⁻¹ r 0 ψ φ = 0 := by
          simp [HRS.Whole.noiseCovW, min_eq_right hr]
        rw [hzero]
        simpa using mul_nonneg hBNnn (Real.sqrt_nonneg (∫ x, ψ x ^ 2 ∂μr))
    · have hrzero : r = 0 := le_antisymm (le_of_not_gt hrpos) hr
      subst r
      have hzero : noiseCovW (r26t3_coeff R) p.β⁻¹ 0 t ψ φ = 0 := by
        simp [HRS.Whole.noiseCovW, min_eq_left ht]
      rw [hzero]
      simpa using mul_nonneg hBNnn (Real.sqrt_nonneg (∫ x, ψ x ^ 2 ∂μr))
  unfold HRS.MS.S21E.s21eCov HRS.Whole.linearGaussianCov
  change |HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ₀ p.γ
      (r26t3_U R 0 r ψ) (r26t3_U R 0 t φ) +
        noiseCovW (r26t3_coeff R) p.β⁻¹ r t ψ φ| ≤ _
  have hfzero : f 0 = r26t3_U R 0 r ψ := rfl
  have hgzero : g 0 = r26t3_U R 0 t φ := rfl
  rw [← hfzero, ← hgzero]
  dsimp [B]
  calc
    _ ≤ |HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ₀ p.γ (f 0) (g 0)| +
        |noiseCovW (r26t3_coeff R) p.β⁻¹ r t ψ φ| := abs_add_le _ _
    _ ≤ (Real.sqrt Kψ * Real.sqrt Kφ) *
          Real.sqrt (∫ x, ψ x ^ 2 ∂μr) + BN *
            Real.sqrt (∫ x, ψ x ^ 2 ∂μr) := add_le_add hinitBound hnoiseBound
    _ = (Real.sqrt Kψ * Real.sqrt Kφ + BN) *
          Real.sqrt (∫ x, ψ x ^ 2 ∂μr) := by ring

theorem fp81s21_s21ecov_linear
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    {ψ₁ ψ₂ φ : Euc p.d → ℝ}
    (hψ₁ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ₁)
    (hψ₂ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ₂)
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ) (c : ℝ) :
    HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t
        (fun x => ψ₁ x + c * ψ₂ x) φ =
      HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ₁ φ +
        c * HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ₂ φ := by
  let C := r26t3_coeff R
  let μ₀ := r26t3_mu R 0
  have hμ₀prob : IsProbabilityMeasure μ₀ := by
    obtain ⟨-, -, hdata, -⟩ := r26t3_reference_data p δ hδ hδh R
    exact HRS.Whole.Q34.isProbabilityMeasure_nu (hdata 0 le_rfl).1
  have hsum : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ)
      (fun x => ψ₁ x + c * ψ₂ x) := by
    let m : ℝ := (wholeSpaceIndex p.d : ℝ)
    have hsmulMem := (HRS.MS.S111X1.oscSub p.d m).smul_mem c hψ₂
    have hsumMem := (HRS.MS.S111X1.oscSub p.d m).add_mem hψ₁ hsmulMem
    change IsOscTest m (fun x => ψ₁ x + c * ψ₂ x) at hsumMem
    simpa [m] using hsumMem
  have hU₁ := fp81s21_U_osc_test_classical p R hψ₁ hr
  have hU₂ := fp81s21_U_osc_test_classical p R hψ₂ hr
  have hUs := fp81s21_U_osc_test_classical p R hsum hr
  have hUφ := fp81s21_U_osc_test_classical p R hφ ht
  let f₁ : ℝ → Euc p.d → ℝ := fun v => r26t3_U R v r ψ₁
  let f₂ : ℝ → Euc p.d → ℝ := fun v => r26t3_U R v r ψ₂
  let fs : ℝ → Euc p.d → ℝ := fun v => r26t3_U R v r (fun x => ψ₁ x + c * ψ₂ x)
  let g : ℝ → Euc p.d → ℝ := fun v => r26t3_U R v t φ
  letI : IsProbabilityMeasure μ₀ := hμ₀prob
  have hcf₁ : IsClassicalAdjointW C r ψ₁ f₁ := by simpa [f₁, C, r26t3_U, r26t3_coeff] using hU₁
  have hcf₂ : IsClassicalAdjointW C r ψ₂ f₂ := by simpa [f₂, C, r26t3_U, r26t3_coeff] using hU₂
  have hcfs : IsClassicalAdjointW C r (fun x => ψ₁ x + c * ψ₂ x) fs := by
    simpa [fs, C, r26t3_U, r26t3_coeff] using hUs
  have hcg : IsClassicalAdjointW C t φ g := by simpa [g, C, r26t3_U, r26t3_coeff] using hUφ
  have hUlin' : ∀ v ∈ Icc (0 : ℝ) (min r t),
      fs v = fun x => f₁ v x + c * f₂ v x := by
    intro v hv
    change r26t3_U R v r (fun x => ψ₁ x + c * ψ₂ x) = _
    exact fp81s21_U_linear_of_osc_test p R hψ₁ hψ₂ c (t := r) (r := v)
      hr ⟨hv.1, hv.2.trans (min_le_left _ _)⟩
  have hr0 : 0 ∈ Icc (0 : ℝ) r := ⟨le_rfl, hr⟩
  have hmem₁ : MemLp (f₁ 0) 2 μ₀ := by
    exact HRS.MS.S111X1.x1_classical_memLp hcf₁ hr0 μ₀
  have hmem₂ : MemLp (f₂ 0) 2 μ₀ := by
    exact HRS.MS.S111X1.x1_classical_memLp hcf₂ hr0 μ₀
  have h0min : (0 : ℝ) ∈ Icc (0 : ℝ) (min r t) := ⟨le_rfl, le_min hr ht⟩
  have hsum0 : fs 0 = fun x => f₁ 0 x + c * f₂ 0 x := hUlin' 0 h0min
  unfold HRS.MS.S21E.s21eCov HRS.Whole.linearGaussianCov
  change
    (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ₀ p.γ (fs 0) (g 0) +
      noiseCovW C p.β⁻¹ r t (fun x => ψ₁ x + c * ψ₂ x) φ) = _
  rw [hsum0]
  rw [HRS.MS.S111X1.x1_suscept_lin (rieszKernel p.d p.s) μ₀ p.γ hmem₁ hmem₂ c (g 0)]
  have hpair1 := fp81s21_moving_pair_integral_continuous p R hδ hδh
    (t₁ := r) (t₂ := t) (T₀ := min r t) (le_min hr ht)
    (min_le_left _ _) (min_le_right _ _) hcf₁ hcg
  have hpair2 := fp81s21_moving_pair_integral_continuous p R hδ hδh
    (t₁ := r) (t₂ := t) (T₀ := min r t) (le_min hr ht)
    (min_le_left _ _) (min_le_right _ _) hcf₂ hcg
  have hpairfs := fp81s21_moving_pair_integral_continuous p R hδ hδh
    (t₁ := r) (t₂ := t) (T₀ := min r t) (le_min hr ht)
    (min_le_left _ _) (min_le_right _ _) hcfs hcg
  have hI1 : IntegrableOn
      (fun v => ∫ x, inner ℝ (gradient (f₁ v) x) (gradient (g v) x) * R.ρ v x)
      (Icc (0 : ℝ) (min r t)) := hpair1.integrableOn_Icc
  have hI2 : IntegrableOn
      (fun v => ∫ x, inner ℝ (gradient (f₂ v) x) (gradient (g v) x) * R.ρ v x)
      (Icc (0 : ℝ) (min r t)) := hpair2.integrableOn_Icc
  have hIs : IntegrableOn
      (fun v => ∫ x, inner ℝ (gradient (fs v) x) (gradient (g v) x) * R.ρ v x)
      (Icc (0 : ℝ) (min r t)) := hpairfs.integrableOn_Icc
  have hspace : ∀ v ∈ Icc (0 : ℝ) (min r t),
      (∫ x, inner ℝ (gradient (fs v) x) (gradient (g v) x) * R.ρ v x) =
        (∫ x, inner ℝ (gradient (f₁ v) x) (gradient (g v) x) * R.ρ v x) +
          c * ∫ x, inner ℝ (gradient (f₂ v) x) (gradient (g v) x) * R.ρ v x := by
    intro v hv
    have hv₁ : v ∈ Icc (0 : ℝ) r := ⟨hv.1, hv.2.trans (min_le_left _ _)⟩
    have hv₂ : v ∈ Icc (0 : ℝ) t := ⟨hv.1, hv.2.trans (min_le_right _ _)⟩
    obtain ⟨-, -, hdata, -⟩ := r26t3_reference_data p δ hδ hδh R
    have hρi := HRS.Whole.Q34.integrable_of_isProbDensity (hdata v hv.1).1
    have hρnn : ∀ x, 0 ≤ R.ρ v x := fun x => (hdata v hv.1).2 x |>.le
    have hi₁ := HRS.MS.S111X1.x1_pair_integrable hcf₁ hcg hρi hρnn hv₁ hv₂
    have hi₂ := HRS.MS.S111X1.x1_pair_integrable hcf₂ hcg hρi hρnn hv₁ hv₂
    have hdiff₁ : DifferentiableAt ℝ (f₁ v) 0 := (hcf₁.c2 v hv₁).differentiable (by norm_num) 0
    have hdiff₂ : DifferentiableAt ℝ (f₂ v) 0 := (hcf₂.c2 v hv₁).differentiable (by norm_num) 0
    have hgrad : gradient (fun x => f₁ v x + c * f₂ v x) =
        fun x => gradient (f₁ v) x + c • gradient (f₂ v) x := by
      funext x
      exact HRS.MS.S111X1.x1_gradient_add_smul c
        ((hcf₁.c2 v hv₁).differentiable (by norm_num) x)
        ((hcf₂.c2 v hv₁).differentiable (by norm_num) x)
    rw [hUlin' v hv, hgrad]
    have heq : ∀ x,
        inner ℝ (gradient (f₁ v) x + c • gradient (f₂ v) x) (gradient (g v) x) * R.ρ v x =
          inner ℝ (gradient (f₁ v) x) (gradient (g v) x) * R.ρ v x +
            c * (inner ℝ (gradient (f₂ v) x) (gradient (g v) x) * R.ρ v x) := by
      intro x
      rw [inner_add_left, inner_smul_left]
      simp only [conj_trivial]
      ring
    simp_rw [heq]
    rw [integral_add hi₁ (hi₂.const_mul c), integral_const_mul]
  have hspace' : ∀ v ∈ Icc (0 : ℝ) (min r t),
      (∫ x, inner ℝ
          (gradient (HRS.Whole.propagatorW C v r (fun x => ψ₁ x + c * ψ₂ x)) x)
          (gradient (HRS.Whole.propagatorW C v t φ) x) * C.ρ v x) =
        (∫ x, inner ℝ (gradient (HRS.Whole.propagatorW C v r ψ₁) x)
          (gradient (HRS.Whole.propagatorW C v t φ) x) * C.ρ v x) +
          c * ∫ x, inner ℝ (gradient (HRS.Whole.propagatorW C v r ψ₂) x)
            (gradient (HRS.Whole.propagatorW C v t φ) x) * C.ρ v x := by
    intro v hv
    exact hspace v hv
  have hI1' : IntegrableOn
      (fun v => ∫ x, inner ℝ (gradient (HRS.Whole.propagatorW C v r ψ₁) x)
        (gradient (HRS.Whole.propagatorW C v t φ) x) * C.ρ v x)
      (Icc (0 : ℝ) (min r t)) := by
    exact hI1
  have hI2' : IntegrableOn
      (fun v => ∫ x, inner ℝ (gradient (HRS.Whole.propagatorW C v r ψ₂) x)
        (gradient (HRS.Whole.propagatorW C v t φ) x) * C.ρ v x)
      (Icc (0 : ℝ) (min r t)) := by
    exact hI2
  unfold HRS.Whole.noiseCovW
  rw [setIntegral_congr_fun measurableSet_Icc hspace']
  rw [integral_add hI1' (hI2'.const_mul c), integral_const_mul]
  simp only [r26t3_mu, r26t3_U, r26t3_coeff, C, μ₀, f₁, f₂, g]
  ring_nf

theorem sol13_covcore (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∀ R : Trajectory p δ,
          HRS.MS.S21E.S21eCovCore p.d p.s p.a p.β p.γ R.ρ := by
  obtain ⟨δdens, hδdens, hδdensHalf, hDensity⟩ := sol13_covcore_density p
  obtain ⟨δenergy, Q, Cdec, cdec, hδenergy, hδenergyHalf, hQ, hQδ,
    hCdec, hcdec, hAdjointEnergy⟩ := sol13_uniform_adjoint_energy p
  let δ0 : ℝ := min δdens δenergy
  have hδ0 : 0 < δ0 := lt_min hδdens hδenergy
  have hδ0half : δ0 ≤ 1 / 2 := le_trans (min_le_left _ _) hδdensHalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδδ0 R
  have hδdensity : δ ≤ δdens := hδδ0.trans (min_le_left _ _)
  have hδenergy' : δ ≤ δenergy := hδδ0.trans (min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := hδδ0.trans hδ0half
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμstarprob : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμstarprob
  obtain ⟨cE, CE, hcE, hCE, hEnergyBounds⟩ := r26t3_energy_bounds R
  have hAdjointBounds :
      ∀ H : ℝ, 0 < H →
        ∀ (terminal : Euc p.d → ℝ) (u : ℝ → Euc p.d → ℝ),
          IsClassicalAdjointW (r26t3_coeff R) H terminal u →
          IntegrableOn
              (fun s => ∫ x, ‖gradient (u s) x‖ ^ 2
                ∂(HRS.Whole.withDensityReal R.ρβ)) (Icc (0 : ℝ) H) ∧
            (∀ s ∈ Icc (0 : ℝ) H,
              HRS.MS.S111X2.s111x2_centeredSquare
                  (HRS.Whole.withDensityReal R.ρβ) (u s) ≤
                Cdec * Real.exp (-cdec * (H - s)) *
                  HRS.MS.S111X2.s111x2_centeredSquare
                    (HRS.Whole.withDensityReal R.ρβ) terminal) ∧
            (∫ s in Icc (0 : ℝ) H, ∫ x, ‖gradient (u s) x‖ ^ 2
                ∂(HRS.Whole.withDensityReal R.ρβ)) ≤
              CE * HRS.MS.S111X2.s111x2_centeredSquare
                (HRS.Whole.withDensityReal R.ρβ) terminal := by
    intro H hH terminal u hu
    obtain ⟨hAC, hder, hGradIntegrable, hEnergyFor⟩ :=
      hAdjointEnergy δ hδ hδenergy' R H hH terminal u hu
    refine ⟨?_, ?_, ?_⟩
    · simpa [μstar] using hGradIntegrable
    · intro s hs
      obtain ⟨-, hdecay⟩ := hEnergyFor s hs
      simpa [HRS.MS.S111X2.s111x2_centeredSquare, μstar] using hdecay
    · have hzero := hEnergyFor 0 ⟨le_rfl, hH.le⟩
      obtain ⟨hbudget, -⟩ := hzero
      have hu0Lp : MemLp (u 0) 2 μstar :=
        HRS.MS.S111X1.x1_classical_memLp hu ⟨le_rfl, hH.le⟩ μstar
      have hvar0nn : 0 ≤ HRS.MS.S111X2.s111x2_centeredSquare μstar (u 0) :=
        integral_nonneg fun x => sq_nonneg _
      have henergy0lower :
          cE * HRS.MS.S111X2.s111x2_centeredSquare μstar (u 0) ≤
            r26t3_energy R (u 0) := by
        simpa [HRS.MS.S111X2.s111x2_centeredSquare, μstar] using
          (hEnergyBounds (u 0) hu0Lp).1
      have henergy0nn : 0 ≤ r26t3_energy R (u 0) :=
        (mul_nonneg hcE.le hvar0nn).trans henergy0lower
      have hGradBudget :
          (∫ s in Icc (0 : ℝ) H, ∫ x, ‖gradient (u s) x‖ ^ 2 ∂μstar) ≤
            r26t3_energy R terminal := by
        dsimp [μstar] at hbudget ⊢
        linarith
      calc
        _ ≤ r26t3_energy R terminal := hGradBudget
        _ ≤ CE * HRS.MS.S111X2.s111x2_centeredSquare
              (HRS.Whole.withDensityReal R.ρβ) terminal := by
          have hterminalLp : MemLp terminal 2 μstar := by
            simpa [hu.terminal] using
              (HRS.MS.S111X1.x1_classical_memLp hu ⟨hH.le, le_rfl⟩ μstar)
          simpa [HRS.MS.S111X2.s111x2_centeredSquare, μstar] using
            (hEnergyBounds terminal hterminalLp).2
  intro r hr
  obtain ⟨hρmeas, hρpos, hρmem⟩ := hDensity δ hδ hδdensity R r hr
  refine ⟨hρmeas, hρpos, hρmem, ?_⟩
  intro t ht φ hφ
  refine ⟨?_, ?_⟩
  · intro ψ₁ ψ₂ hψ₁ hψ₂ c
    exact fp81s21_s21ecov_linear p R hδ hδhalf hr ht hψ₁ hψ₂ hφ c
  · obtain ⟨B, hBnn, hB⟩ := fp81s21_covcore_bound_at p R hδ hδhalf
      hCdec hcdec hCE hAdjointBounds hr ht hφ
    refine ⟨B, hBnn, ?_⟩
    intro ψ hψ
    exact hB ψ hψ (hρmem ψ hψ)

#print axioms fp81s21_s21ecov_linear
#print axioms sol13_covcore

end HRS.Fp81.S21

