import HRS.MS.WsPrepI1

/-!
# S21T packet 2: reference facts for `μ₀ = ρ⁰ dx`, the Gaussian path measure and its finite-dimensional laws

* `s21i_ref`: for `ρ⁰ ≤ C₁ ρ_β` a probability density, `ρ⁰` is bounded and (at `s = 0`) has a second logarithmic moment (the
  hypotheses of the S4.5 existence theorem and of `S45.s45_kdata`);
* `s21i_gauss_exists`: the centred Gaussian on `ℓ²` with the susceptibility covariance of the window cosine tests;
* `s21i_fdd`: the finite-dimensional laws of `γ₀ = Φ_* γ`: `multivariateGaussian 0` of the susceptibility covariances
  `C_{β₀}(U^{0,bw+t_i} φ_{α_i}, U^{0,bw+t_j} φ_{α_j})` (generic in the orbit `U` with the cosine series `S11pSeries`);
* `s21i_cov_le`, `s21i_gauss_coord`: `C_{β₀}(f,f) ≤ 4 B²` and the coordinate second moments of `γ` (the reference-generic form of
  `s21h_cov_le`, `s21h_gauss_coord`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

theorem s21i_ref (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {ρ0 : Euc d → ℝ} (hρ0 : HRS.Whole.IsProbDensity ρ0)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hr : ∀ x, ρ0 x ≤ C₁ * ρβ x) :
    ∃ M L : ℝ, (∀ x, ρ0 x ≤ M) ∧ (s = 0 → HasLogMoment2 (HRS.Whole.withDensityReal ρ0) L) := by
  have hρeq : ρβ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ
  obtain ⟨Cth, c, BU, hTh⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have hM : ∀ x, thermalDensity d s a β x ≤ Cth := fun x => (le_abs_self _).trans
    ((hTh.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hTh.hc])
      nlinarith [hTh.C0]))
  have hCth : 0 ≤ Cth := (hρβ.2.1.nonneg 0).trans (by rw [hρeq]; exact hM 0)
  refine ⟨C₁ * Cth, ?_⟩
  obtain ⟨L, hL⟩ := S45.s45_thermal_logmoment2 hTh
  refine ⟨C₁ * L, fun x => (hr x).trans ?_, fun _ => ?_⟩
  · rw [hρeq]; exact mul_le_mul_of_nonneg_left (hM x) hC₁
  · -- `μ₀ ≤ C₁ μ_β`
    have hle : HRS.Whole.withDensityReal ρ0 ≤ ENNReal.ofReal C₁ • thermalMeasure d s a β := by
      have e : thermalMeasure d s a β = HRS.Whole.withDensityReal (thermalDensity d s a β) := rfl
      rw [e]
      refine Measure.le_iff.2 fun A hA => ?_
      unfold HRS.Whole.withDensityReal
      rw [Measure.smul_apply, withDensity_apply _ hA, withDensity_apply _ hA, smul_eq_mul,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      rw [← ENNReal.ofReal_mul hC₁, ← hρeq]
      exact ENNReal.ofReal_le_ofReal (hr x)
    obtain ⟨hi, hint⟩ := hL
    have hi' : Integrable (fun x => Real.log (2 + ‖x‖) ^ 2) (ENNReal.ofReal C₁ • thermalMeasure d s a β) :=
      hi.smul_measure ENNReal.ofReal_ne_top
    refine ⟨hi'.mono_measure hle, ?_⟩
    calc ∫ x, Real.log (2 + ‖x‖) ^ 2 ∂(HRS.Whole.withDensityReal ρ0)
        ≤ ∫ x, Real.log (2 + ‖x‖) ^ 2 ∂(ENNReal.ofReal C₁ • thermalMeasure d s a β) :=
          integral_mono_measure hle (Filter.Eventually.of_forall fun x => by positivity) hi'
      _ = C₁ * ∫ x, Real.log (2 + ‖x‖) ^ 2 ∂(thermalMeasure d s a β) := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hC₁, smul_eq_mul]
      _ ≤ C₁ * L := mul_le_mul_of_nonneg_left hint hC₁

theorem s21i_cov_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ0 : Euc d → ℝ} (hρ0 : HRS.Whole.IsProbDensity ρ0)
    {M L : ℝ} (hM : ∀ x, ρ0 x ≤ M) (hL : s = 0 → HasLogMoment2 (HRS.Whole.withDensityReal ρ0) L) {β₀ : ℝ} (hβ₀ : 0 < β₀)
    {f : Euc d → ℝ} (hf : MemLp f 2 (HRS.Whole.withDensityReal ρ0)) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ0
    HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ0) β₀ f f ≤ 4 * B ^ 2 := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ0
  obtain ⟨K, hK⟩ : ∃ K : Lp ℝ 2 (HRS.Whole.withDensityReal ρ0) →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal ρ0),
      S45.IsKData (HRS.Whole.withDensityReal ρ0) (rieszKernel d s) K :=
    S45.s45_kdata hd hs0 hsd hρ0 hM hL
  rw [S45.s45_susceptibilityCov_eq hK hβ₀ hf hf]
  refine (S45.s45_inner_Rr_le hK hβ₀.le _).trans ?_
  have h := S45.s45_U_norm_le hf hB
  have h0 := norm_nonneg (S45.s45_U f hf)
  nlinarith

theorem s21i_gauss_coord (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ0 : Euc d → ℝ} (hρ0 : HRS.Whole.IsProbDensity ρ0)
    {M L : ℝ} (hM : ∀ x, ρ0 x ≤ M) (hL : s = 0 → HasLogMoment2 (HRS.Whole.withDensityReal ρ0) L) {β₀ : ℝ} (hβ₀ : 0 < β₀)
    {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) {γ : Measure SeqL2}
    (hγ : IsCenteredGaussianSeq γ fun i j =>
      HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ0) β₀ (φ i) (φ j)) (k : ℕ) :
    ∫⁻ z, ENNReal.ofReal (SeqL2.coord z k ^ 2) ∂γ ≤ ENNReal.ofReal (4 * cbNorm J (φ k) ^ 2) := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ0
  obtain ⟨hi, hv⟩ := hγ.2 k k
  have hmem : MemLp (φ k) 2 (HRS.Whole.withDensityReal ρ0) := HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 k)
  have hcov := s21i_cov_le hd hs0 hsd hρ0 hM hL hβ₀ hmem (fun x => HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 k) x)
  have hnn : ∀ z : SeqL2, 0 ≤ SeqL2.coord z k * SeqL2.coord z k := fun z => mul_self_nonneg _
  have e : ∫⁻ z, ENNReal.ofReal (SeqL2.coord z k ^ 2) ∂γ =
      ENNReal.ofReal (∫ z, SeqL2.coord z k * SeqL2.coord z k ∂γ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnn)]
    exact lintegral_congr fun z => by rw [sq]
  rw [e]
  exact ENNReal.ofReal_le_ofReal (hv.le.trans hcov)

/-- The finite-dimensional laws of `Φ_* γ`: the susceptibility covariances of the orbit `U`. -/
theorem s21i_fdd {D : S11pData d} {U : MultiIndex d → ℝ → Euc d → ℝ} {T m : ℝ} (hT : 0 < T)
    (hU : S11pSeries D T U) (σ : ℕ ≃ ℕ × MultiIndex d) {J : ℕ}
    (hφ : IsSummableFeatureFamily J (fun j => D.f (σ j))) (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ0 : Euc d → ℝ} (hρ0 : HRS.Whole.IsProbDensity ρ0) {M L : ℝ} (hM : ∀ x, ρ0 x ≤ M)
    (hL : s = 0 → HasLogMoment2 (HRS.Whole.withDensityReal ρ0) L) {β₀ : ℝ} (hβ₀ : 0 < β₀) {γ : Measure SeqL2}
    (hγ : IsCenteredGaussianSeq γ fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ0)
      β₀ (D.f (σ i)) (D.f (σ j))) :
    ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
      (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ0) β₀
        (U (αs i) (ts i)) (U (αs j) (ts j))).PosSemidef ∧
      (γ.map (s21gPhi σ hT m)).map (fun w : OscPath d m T => (WithLp.toLp 2 fun i =>
          OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
          (HRS.Whole.withDensityReal ρ0) β₀ (U (αs i) (ts i)) (U (αs j) (ts j))) := by
  intro p ts hts αs
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ0
  haveI hGg : IsGaussian γ := hγ.1.1
  obtain ⟨K, hK⟩ := S45.s45_kdata hd hs0 hsd hρ0 hM hL
  set ν := HRS.Whole.withDensityReal ρ0 with hν
  set w : Fin p → SeqL2 := fun i => s21gVec σ hT (ts i) (αs i) with hw
  have hψm : ∀ i, MemLp (U (αs i) (ts i)) 2 ν := fun i => by
    obtain ⟨Cb, hCb⟩ := s11p_U_bound hT hU (αs i) (ts i) (hts i)
    exact MemLp.of_bound (s11p_U_continuous hT hU (αs i) (ts i) (hts i)).aestronglyMeasurable Cb
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCb x)
  have hser : ∀ i x, HasSum (fun j => SeqL2.coord (w i) j * D.f (σ j) x) (U (αs i) (ts i) x) :=
    fun i x => s21i_series hT hU σ (ts i) (hts i) (αs i) x
  have hmean : ∫ z, id z ∂γ = 0 := HRS.HilbertCLTAux.gaussian_mean_zero hγ.1
  have hcovij : ∀ i j, covarianceBilin γ (w i) (w j) =
      HRS.Whole.susceptibilityCov (rieszKernel d s) ν β₀ (U (αs i) (ts i)) (U (αs j) (ts j)) := by
    intro i j
    have h := s21g_cov hK hβ₀ hφ (γ := γ) hγ (w i) (w j) (hψm i) (hψm j) (hser i) (hser j)
    rw [covarianceBilin_apply IsGaussian.memLp_two_id, hmean]
    simp only [id, sub_zero]
    exact h.2
  obtain ⟨hPSD, hlaw⟩ := s21g_fdd_gaussian γ hmean w
  have e : (Matrix.of fun i j => covarianceBilin γ (w i) (w j)) =
      Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) ν β₀ (U (αs i) (ts i)) (U (αs j) (ts j)) := by
    ext i j; exact hcovij i j
  rw [e] at hPSD hlaw
  refine ⟨hPSD, ?_⟩
  have hFm : Measurable (fun w : OscPath d m T => (WithLp.toLp 2 fun i =>
      OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) := by
    have h1 : Continuous fun w : OscPath d m T => (WithLp.toLp 2 fun i =>
        OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p)) := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      exact s11p_coord_at_continuous m T ⟨ts i, hts i⟩ (αs i)
    exact h1.measurable
  rw [Measure.map_map hFm (s21gPhi σ hT m).continuous.measurable]
  convert hlaw using 2
  funext z
  ext i
  simp only [Function.comp_apply]
  rw [s21gAw_apply, s21gPhi_coord_inner]

end HRS.MS.S21
