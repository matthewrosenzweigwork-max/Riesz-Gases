import HRS.MS.SuppU11Aux3
import HRS.Whole.CriticalNoise

/-!
# S8.8.G01: Gaussian base and increment moments on the admissible tests

`s88_gaussian_second_moments`: for a Gaussian functional `η` with the susceptibility covariance and `f, g ∈ C_b²`,
`η f, η g ∈ L²`, `E (η f)² ≤ ‖P_μ f‖²_{L²(μ)}` and `E (η f - η g)² ≤ ‖P_μ (f-g)‖²_{L²(μ)}`.
Only the two-dimensional law of `(η f, η g)` is used.  If the covariance matrix is not positive semidefinite, the pinned
`multivariateGaussian` is the Dirac mass at `0` and every moment vanishes; otherwise the moments are the quadratic forms
of the covariance matrix, which are bounded by the response estimate of Q34 and an `L²` bilinear expansion of the
resolvent.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole

lemma s88_bddcont {d : ℕ} {f : Euc d → ℝ} (hf : MemCb 2 f) :
    Continuous f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B := by
  refine ⟨hf.1.continuous, ?_⟩
  obtain ⟨B, hB⟩ := hf.2 0 (by norm_num)
  refine ⟨B, fun x => ?_⟩
  have := hB ⟨x, rfl⟩
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  exact this

/-- The response only sees the centered part of the datum. -/
lemma s88_resp_proj {d : ℕ} (g : Euc d → ℝ) (ν : Measure (Euc d)) [IsProbabilityMeasure ν] (β : ℝ)
    {ψ : Euc d → ℝ} (hψ : Integrable ψ ν) :
    HRS.Whole.responseInverse g ν β ψ =
      HRS.Whole.responseInverse g ν β (HRS.Whole.projMean ν ψ) := by
  have hpm : HRS.Whole.projMean ν (HRS.Whole.projMean ν ψ) = HRS.Whole.projMean ν ψ := by
    funext x
    have : HRS.Whole.pair ν (HRS.Whole.projMean ν ψ) = 0 := by
      simp only [HRS.Whole.pair, HRS.Whole.projMean]
      rw [integral_sub hψ (integrable_const _), integral_const]
      simp
    simp only [HRS.Whole.projMean, HRS.Whole.pair] at this ⊢
    rw [this]; ring
  have hfun : HRS.Whole.IsResponse g ν β ψ = HRS.Whole.IsResponse g ν β (HRS.Whole.projMean ν ψ) := by
    funext h
    unfold HRS.Whole.IsResponse
    rw [hpm]
  unfold HRS.Whole.responseInverse
  rw [hfun]

section Quad

variable {d : ℕ} {ρ : Euc d → ℝ} {M s : ℝ}
variable [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)]

/-- Bilinear expansion of the resolvent quadratic form. -/
theorem s88_resp_quadratic (h : Q34.Q34Hyp d s ρ M) {β : ℝ} (hβ : 0 < β)
    {ψ1 ψ2 : Euc d → ℝ} (h1 : MemL2Zero (HRS.Whole.withDensityReal ρ) ψ1)
    (h2 : MemL2Zero (HRS.Whole.withDensityReal ρ) ψ2) :
    HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) ψ1
        (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ψ1) +
      HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) ψ2
        (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ψ2) -
      HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) ψ1
        (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ψ2) -
      HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) ψ2
        (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ψ1) ≤
      ∫ x, (ψ1 x - ψ2 x) ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hRm : ∀ ψ, MemL2Zero ν ψ →
      MemL2Zero ν (HRS.Whole.responseInverse (rieszKernel d s) ν β ψ) :=
    fun ψ hψ => (u11_resp_isResponse h hβ hψ).1
  have h12 : MemL2Zero ν (fun x => ψ1 x - ψ2 x) :=
    ⟨h1.1.sub h2.1, by
      rw [integral_sub (h1.1.integrable one_le_two) (h2.1.integrable one_le_two), h1.2, h2.2]
      simp⟩
  set R : (Euc d → ℝ) → (Euc d → ℝ) :=
    HRS.Whole.responseInverse (rieszKernel d s) ν β with hR
  set Y1 : Lp ℝ 2 ν := (hRm _ h1).1.toLp (R ψ1) with hY1
  set Y2 : Lp ℝ 2 ν := (hRm _ h2).1.toLp (R ψ2) with hY2
  set Yd : Lp ℝ 2 ν := (hRm _ h12).1.toLp (R (fun x => ψ1 x - ψ2 x)) with hYd
  set E1 : Lp ℝ 2 ν := h1.1.toLp ψ1 with hE1
  set E2 : Lp ℝ 2 ν := h2.1.toLp ψ2 with hE2
  set Ed : Lp ℝ 2 ν := h12.1.toLp (fun x => ψ1 x - ψ2 x) with hEd
  have e1 : Y1 + β • Q34.Kc h Y1 = E1 := u11_resp_lp h hβ h1
  have e2 : Y2 + β • Q34.Kc h Y2 = E2 := u11_resp_lp h hβ h2
  have ed : Yd + β • Q34.Kc h Yd = Ed := u11_resp_lp h hβ h12
  have hEdsub : Ed = E1 - E2 := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp h12.1, MemLp.coeFn_toLp h1.1, MemLp.coeFn_toLp h2.1,
      Lp.coeFn_sub E1 E2] with x a b c d'
    rw [d', Pi.sub_apply]
    change (h12.1.toLp _ : Euc d → ℝ) x = _
    rw [a, b, c]
  have hYsub : Yd = Y1 - Y2 := by
    set U : Lp ℝ 2 ν := Yd - (Y1 - Y2) with hU
    have hUe : U + β • Q34.Kc h U = 0 := by
      have : U + β • Q34.Kc h U = (Yd + β • Q34.Kc h Yd) - (Y1 + β • Q34.Kc h Y1) +
          (Y2 + β • Q34.Kc h Y2) := by
        simp only [hU, map_sub, smul_sub]; abel
      rw [this, e1, e2, ed, hEdsub]; abel
    have hpos := Q34.Kc_pos h U
    have : inner ℝ (U + β • Q34.Kc h U) U = ‖U‖ ^ 2 + β * inner ℝ (Q34.Kc h U) U := by
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [hUe, inner_zero_left] at this
    have hU0 : ‖U‖ ^ 2 ≤ 0 := by nlinarith [mul_nonneg hβ.le hpos]
    have : U = 0 := norm_eq_zero.1 (by nlinarith [sq_nonneg ‖U‖, norm_nonneg U])
    exact sub_eq_zero.1 (by rw [← hU]; exact this)
  -- translate the pairings
  have hrep : ∀ (u v : Euc d → ℝ) (U V : Lp ℝ 2 ν), u =ᵐ[ν] (U : Euc d → ℝ) →
      v =ᵐ[ν] (V : Euc d → ℝ) → HRS.Whole.l2Inner ν u v = inner ℝ U V :=
    fun u v U V hu hv => Q34.l2Inner_eq hu hv
  have hE1ae : ψ1 =ᵐ[ν] (E1 : Euc d → ℝ) := (MemLp.coeFn_toLp h1.1).symm
  have hE2ae : ψ2 =ᵐ[ν] (E2 : Euc d → ℝ) := (MemLp.coeFn_toLp h2.1).symm
  have hEdae : (fun x => ψ1 x - ψ2 x) =ᵐ[ν] (Ed : Euc d → ℝ) := (MemLp.coeFn_toLp h12.1).symm
  have hY1ae : R ψ1 =ᵐ[ν] (Y1 : Euc d → ℝ) := (MemLp.coeFn_toLp (hRm _ h1).1).symm
  have hY2ae : R ψ2 =ᵐ[ν] (Y2 : Euc d → ℝ) := (MemLp.coeFn_toLp (hRm _ h2).1).symm
  have hYdae : R (fun x => ψ1 x - ψ2 x) =ᵐ[ν] (Yd : Euc d → ℝ) :=
    (MemLp.coeFn_toLp (hRm _ h12).1).symm
  have hq := (Q34.partD h hβ h12).2.2.2.1
  rw [hrep _ _ Ed Yd hEdae hYdae, hEdsub, hYsub] at hq
  have hq' : HRS.Whole.l2Inner ν ψ1 (R ψ1) + HRS.Whole.l2Inner ν ψ2 (R ψ2) -
      HRS.Whole.l2Inner ν ψ1 (R ψ2) - HRS.Whole.l2Inner ν ψ2 (R ψ1) =
      inner ℝ (E1 - E2) (Y1 - Y2) := by
    rw [hrep _ _ E1 Y1 hE1ae hY1ae, hrep _ _ E2 Y2 hE2ae hY2ae, hrep _ _ E1 Y2 hE1ae hY2ae,
      hrep _ _ E2 Y1 hE2ae hY1ae, inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  rw [hq']
  exact hq

end Quad

section Gauss

open Matrix

lemma s88_gauss_moment {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {p : ℕ}
    (V : Ω → EuclideanSpace ℝ (Fin p)) (hV : Measurable V) (S : Matrix (Fin p) (Fin p) ℝ)
    (hlaw : law P V = multivariateGaussian 0 S) (x : EuclideanSpace ℝ (Fin p)) :
    MemLp (fun z => ⟪x, V z⟫_ℝ) 2 P ∧
      ((S.PosSemidef → ∫ z, ⟪x, V z⟫_ℝ ^ 2 ∂P = x ⬝ᵥ S *ᵥ x) ∧
        (¬ S.PosSemidef → ∫ z, ⟪x, V z⟫_ℝ ^ 2 ∂P = 0)) := by
  have hmem : MemLp (fun z => ⟪x, V z⟫_ℝ) 2 P := by
    have h0 := IsGaussian.memLp_dual (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S)
      (innerSL ℝ x) 2 (by simp)
    rw [← hlaw] at h0
    exact h0.comp_of_map hV.aemeasurable
  have hint : ∫ z, ⟪x, V z⟫_ℝ ^ 2 ∂P =
      ∫ y, ⟪x, y⟫_ℝ ^ 2 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S) := by
    rw [← hlaw]
    have hc : Continuous (fun y : EuclideanSpace ℝ (Fin p) => ⟪x, y⟫_ℝ ^ 2) := by fun_prop
    exact (integral_map hV.aemeasurable hc.aestronglyMeasurable).symm
  refine ⟨hmem, fun hS => ?_, fun hS => ?_⟩
  · rw [hint]
    have h1 := covarianceBilin_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin p))) hS x x
    rw [covarianceBilin_apply IsGaussian.memLp_two_id] at h1
    rw [integral_id_multivariateGaussian'] at h1
    simp only [id, sub_zero] at h1
    rw [← h1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp [sq])
  · rw [hint, multivariateGaussian_of_not_posSemidef _ hS, integral_dirac]
    simp

end Gauss

section Final

open Matrix

theorem s88_gaussian_second_moments {d : ℕ} (hd : 2 ≤ d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (ρ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Ω → (Euc d → ℝ) → ℝ)
    (hη : IsGaussianFunctionalW P η
      (HRS.Whole.susceptibilityCov (rieszKernel d ((d : ℝ) / 2)) (HRS.Whole.withDensityReal ρ) β))
    (f g : Euc d → ℝ) (hf : MemCb 2 f) (hg : MemCb 2 g) :
    MemLp (fun z => η z f) 2 P ∧ MemLp (fun z => η z g) 2 P ∧
      (∫⁻ z, ENNReal.ofReal ((η z f) ^ 2) ∂P) ≤
        ENNReal.ofReal (∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) f x ^ 2
          ∂(HRS.Whole.withDensityReal ρ)) ∧
      (∫⁻ z, ENNReal.ofReal ((η z f - η z g) ^ 2) ∂P) ≤
        ENNReal.ofReal (∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) (fun y => f y - g y) x ^ 2
          ∂(HRS.Whole.withDensityReal ρ)) := by
  classical
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hprob : HRS.Whole.IsProbDensity ρ := hρ.1.1
  obtain ⟨M, hM⟩ := u11_rho_le hd ha hβ hρ
  haveI := Q34.isProbabilityMeasure_nu hprob
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : Q34.Q34Hyp d ((d : ℝ) / 2) ρ M :=
    ⟨by omega, by positivity, by linarith, hprob, hM⟩
  obtain ⟨hfc, Bf, hBf⟩ := s88_bddcont hf
  obtain ⟨hgc, Bg, hBg⟩ := s88_bddcont hg
  have hF := (u11_projMean_bound ν hfc hBf).1
  have hG := (u11_projMean_bound ν hgc hBg).1
  have hIf : Integrable f ν := (MemLp.of_bound hfc.aestronglyMeasurable Bf
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hBf x)).integrable one_le_two
  have hIg : Integrable g ν := (MemLp.of_bound hgc.aestronglyMeasurable Bg
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hBg x)).integrable one_le_two
  set ψ1 := HRS.Whole.projMean ν f with hψ1
  set ψ2 := HRS.Whole.projMean ν g with hψ2
  have hRf : HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) ν β f = HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) ν β ψ1 := s88_resp_proj _ ν β hIf
  have hRg : HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) ν β g = HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) ν β ψ2 := s88_resp_proj _ ν β hIg
  have hpm : ∀ x, HRS.Whole.projMean ν (fun y => f y - g y) x = ψ1 x - ψ2 x := by
    intro x
    simp only [hψ1, hψ2, HRS.Whole.projMean, HRS.Whole.pair]
    rw [integral_sub hIf hIg]; ring
  -- the Gaussian vector
  set φ : Fin 2 → Euc d → ℝ := ![f, g] with hφdef
  have hφ : ∀ i, MemCb 2 (φ i) := by
    intro i; fin_cases i
    · exact hf
    · exact hg
  set V : Ω → EuclideanSpace ℝ (Fin 2) := fun z => WithLp.toLp 2 (fun i => η z (φ i)) with hV
  have hVm : Measurable V :=
    (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun i => hη.1 (φ i))
  set S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    HRS.Whole.susceptibilityCov (rieszKernel d ((d : ℝ) / 2)) ν β (φ i) (φ j) with hS
  have hlaw : law P V = multivariateGaussian 0 S := hη.2 2 φ hφ
  have hS00 : S 0 0 = HRS.Whole.l2Inner ν ψ1 (HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) ν β ψ1) := by
    simp [hS, hφdef, HRS.Whole.susceptibilityCov, hRf, hψ1]
  have hS01 : S 0 1 = HRS.Whole.l2Inner ν ψ1 (HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) ν β ψ2) := by
    simp [hS, hφdef, HRS.Whole.susceptibilityCov, hRg, hψ1]
  have hS10 : S 1 0 = HRS.Whole.l2Inner ν ψ2 (HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) ν β ψ1) := by
    simp [hS, hφdef, HRS.Whole.susceptibilityCov, hRf, hψ2]
  have hS11 : S 1 1 = HRS.Whole.l2Inner ν ψ2 (HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) ν β ψ2) := by
    simp [hS, hφdef, HRS.Whole.susceptibilityCov, hRg, hψ2]
  set e0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1 with he0
  set e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1 with he1
  have hV0 : ∀ z, ⟪e0, V z⟫_ℝ = η z f := by intro z; simp [he0, hV, hφdef, EuclideanSpace.inner_single_left]
  have hV1 : ∀ z, ⟪e1, V z⟫_ℝ = η z g := by intro z; simp [he1, hV, hφdef, EuclideanSpace.inner_single_left]
  have hVd : ∀ z, ⟪e0 - e1, V z⟫_ℝ = η z f - η z g := by
    intro z; rw [inner_sub_left, hV0, hV1]
  obtain ⟨m0, c0, n0⟩ := s88_gauss_moment P V hVm S hlaw e0
  obtain ⟨m1, -, -⟩ := s88_gauss_moment P V hVm S hlaw e1
  obtain ⟨md, cd, nd⟩ := s88_gauss_moment P V hVm S hlaw (e0 - e1)
  simp only [hV0] at m0 c0 n0
  simp only [hV1] at m1
  simp only [hVd] at md cd nd
  have hηf : MemLp (fun z => η z f) 2 P := m0
  have hηg : MemLp (fun z => η z g) 2 P := m1
  have hηd : MemLp (fun z => η z f - η z g) 2 P := md
  have hnn : ∀ (X : Ω → ℝ), MemLp X 2 P →
      ∫⁻ z, ENNReal.ofReal (X z ^ 2) ∂P = ENNReal.ofReal (∫ z, X z ^ 2 ∂P) := fun X hX =>
    (ofReal_integral_eq_lintegral_ofReal hX.integrable_sq
      (Filter.Eventually.of_forall fun z => sq_nonneg _)).symm
  refine ⟨hηf, hηg, ?_, ?_⟩
  · rw [hnn _ hηf]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hPS : S.PosSemidef
    · rw [c0 hPS]
      have : e0.ofLp ⬝ᵥ S *ᵥ e0.ofLp = S 0 0 := by
        simp [he0, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      rw [this, hS00]
      exact (Q34.partD hQ hβ hF).2.2.2.1
    · rw [n0 hPS]; exact integral_nonneg fun x => sq_nonneg _
  · rw [hnn _ hηd]
    refine ENNReal.ofReal_le_ofReal ?_
    simp_rw [hpm]
    by_cases hPS : S.PosSemidef
    · rw [cd hPS]
      have : (e0 - e1).ofLp ⬝ᵥ S *ᵥ (e0 - e1).ofLp = S 0 0 - S 0 1 - S 1 0 + S 1 1 := by
        simp [he0, he1, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
        ring
      rw [this, hS00, hS01, hS10, hS11]
      have := s88_resp_quadratic hQ hβ hF hG
      linarith
    · rw [nd hPS]; exact integral_nonneg fun x => sq_nonneg _

end Final

end HRS.MS.S88Breakdown
