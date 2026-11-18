import HRS.MS.QprepAux6

/-!
# S4.6 packet A7: corrector data at three temperatures, generator identity (`★'`), covariance identification

`S46Feat`: a corrector `χ` of `φ` for the susceptibility `A = γ⁻¹ I + K_μ` about the thermal reference `μ_{a,β}`.
`s46_star`: `Δχ - β a ⟨x,∇χ⟩ - (β-γ) ⟨∇U,∇χ⟩ - γ H_μ = -γ φ + c₀` a.e. (copy of `s45_star`).
`s46_cov_identity`: `C_{ij} = γ⁻¹ ∫ ⟨∇χ_i, ∇φ_j⟩ dμ` for `C = ⟨P φ_i, (I + γ K)⁻¹ P φ_j⟩` (copy of `s45_cov_identity`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S46

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The data of one corrected feature (temperature `γ`, reference `μ_{a,β}`). -/
structure S46Feat (d : ℕ) (s a β γ : ℝ) (φ χ : Euc d → ℝ) (B : ℝ) : Prop where
  smooth : ContDiff ℝ 2 χ
  B1 : ∀ x, ‖gradient χ x‖ ≤ B
  B2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B
  corr : ∀ᵐ x ∂(thermalMeasure d s a β),
    susceptibilityOp (rieszKernel d s) (thermalMeasure d s a β) γ (thermalGen d s a β χ) x =
      projMean (thermalMeasure d s a β) φ x
  r2 : MemLp (thermalGen d s a β χ) 2 (thermalMeasure d s a β)

/-- A `k = 1` thermal corrector yields the data `S46Feat`, with `B = C ‖φ‖`. -/
theorem s46_feat_of_corrector {s a β γ C normφ : ℝ} {φ χ : Euc d → ℝ}
    (h : IsThermalCorrector d s a β γ 1 φ normφ C χ) : S46Feat d s a β γ φ χ (C * normφ) := by
  obtain ⟨-, h2, hr, hc, -, hb⟩ := h
  have h2' : ContDiff ℝ 2 χ := by
    have e : (((1 : ℕ) : WithTop ℕ∞) + 1) = 2 := by norm_num
    rwa [e] at h2
  have hbd : ∀ y, ‖iteratedFDeriv ℝ 1 χ y‖ + ‖iteratedFDeriv ℝ 2 χ y‖ ≤ C * normφ := fun y => by
    have := hb (fun _ => y)
    simpa [Fin.sum_univ_two] using this
  refine ⟨h2', fun x => ?_, fun x => ?_, hc, hr⟩
  · rw [s45_norm_gradient, ← norm_iteratedFDeriv_one]
    linarith [hbd x, norm_nonneg (iteratedFDeriv ℝ 2 χ x)]
  · refine (s45_norm_fderiv_gradient h2' x).trans ?_
    linarith [hbd x, norm_nonneg (iteratedFDeriv ℝ 1 χ x)]

theorem S46Feat.mono {s a β γ : ℝ} {φ χ : Euc d → ℝ} {B B' : ℝ} (h : S46Feat d s a β γ φ χ B)
    (hB : B ≤ B') : S46Feat d s a β γ φ χ B' :=
  ⟨h.smooth, fun x => (h.B1 x).trans hB, fun x => (h.B2 x).trans hB, h.corr, h.r2⟩

/-- The pointwise generator identity (`★'`). -/
theorem s46_star (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ C c BU : ℝ}
    (hγ : 0 < γ) (hT : ThermalData d s a β C c BU) {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ)
    {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2)
    {φ : Euc d → ℝ}
    (hcorr : ∀ᵐ x ∂(thermalMeasure d s a β),
      susceptibilityOp (rieszKernel d s) (thermalMeasure d s a β) γ (thermalGen d s a β χ) x =
        projMean (thermalMeasure d s a β) φ x) :
    ∃ c0 : ℝ, ∀ᵐ x ∂(volume : Measure (Euc d)),
      Laplacian.laplacian χ x - β * (a * ⟪x, gradient χ x⟫) -
        (β - γ) * ⟪gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x, gradient χ x⟫ -
        γ * ∫ y, commutatorKernel d s (gradient χ) x y ∂(thermalMeasure d s a β) = -γ * φ x + c0 := by
  have hUd : Differentiable ℝ (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) :=
    hT.Usmooth.differentiable (by simp)
  obtain ⟨F, hFdef⟩ : ∃ F : Euc d → ℝ, ∀ x, F x = ∫ y, rieszKernel d s (x - y) *
      thermalGen d s a β χ y ∂(thermalMeasure d s a β) := ⟨_, fun _ => rfl⟩
  refine ⟨γ * (pair (thermalMeasure d s a β) φ - pair (thermalMeasure d s a β) F),
    s45_ae_leb_of_ae_mu hT.prob hT.pos ?_⟩
  filter_upwards [hcorr] with x hx
  have h1 := s45_corr_identity hd hs0 hsd hT hχ hB1 hB2 x
  rw [h1, ← hFdef x]
  have h2 := s45_gen_eq (χ := χ) hUd x
  have hx' : γ⁻¹ * thermalGen d s a β χ x + (F x - pair (thermalMeasure d s a β) F) =
      φ x - pair (thermalMeasure d s a β) φ := by
    have e : (fun x => ∫ y, rieszKernel d s (x - y) * thermalGen d s a β χ y
        ∂(thermalMeasure d s a β)) = F := funext fun x => (hFdef x).symm
    unfold susceptibilityOp Kop projMean at hx
    rw [e] at hx
    exact hx
  have hγ0 : γ ≠ 0 := hγ.ne'
  have h3 : thermalGen d s a β χ x + γ * (F x - pair (thermalMeasure d s a β) F) =
      γ * (φ x - pair (thermalMeasure d s a β) φ) := by
    calc _ = γ * (γ⁻¹ * thermalGen d s a β χ x + (F x - pair (thermalMeasure d s a β) F)) := by
          field_simp
      _ = _ := by rw [hx']
  have h4 : ⟪a • x + gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x,
      gradient χ x⟫ = a * ⟪x, gradient χ x⟫ + ⟪gradient (convMeasure (rieszKernel d s)
        (thermalMeasure d s a β)) x, gradient χ x⟫ := by
    rw [inner_add_left, real_inner_smul_left]
  rw [h2, h4] at h3
  have h5 := real_inner_comm (gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x)
    (gradient χ x)
  rw [h5]
  linarith

/-- **The covariance identification** `C_{ij} = γ⁻¹ ∫ ⟨∇χ_i, ∇φ_j⟩ dμ` for the susceptibility covariance. -/
theorem s46_cov_identity (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ C c BU : ℝ}
    (hγ : 0 < γ) (hT : ThermalData d s a β C c BU) {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ)
    {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2)
    {φi φj : Euc d → ℝ} (hφi : MemLp φi 2 (thermalMeasure d s a β))
    (hr2 : MemLp (thermalGen d s a β χ) 2 (thermalMeasure d s a β))
    (hcorr : ∀ᵐ x ∂(thermalMeasure d s a β),
      susceptibilityOp (rieszKernel d s) (thermalMeasure d s a β) γ (thermalGen d s a β χ) x =
        projMean (thermalMeasure d s a β) φi x)
    (hφj : ContDiff ℝ 1 φj) {Bφ Dφ : ℝ} (hBφ : ∀ x, |φj x| ≤ Bφ)
    (hDφ : ∀ x, ‖fderiv ℝ φj x‖ ≤ Dφ) :
    susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ φi φj =
      γ⁻¹ * ∫ y, ⟪gradient χ y, gradient φj y⟫ ∂(thermalMeasure d s a β) := by
  have hd1 : 1 ≤ d := by omega
  have hμ : thermalMeasure d s a β = withDensityReal (thermalDensity d s a β) := rfl
  haveI hprob : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨L, hL⟩ := S45.s45_thermal_logmoment2 hT
  have hM : ∀ x, thermalDensity d s a β x ≤ C := fun x => (le_abs_self _).trans
    ((hT.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
      nlinarith [hT.C0]))
  obtain ⟨K, hK⟩ : ∃ K : Lp ℝ 2 (thermalMeasure d s a β) →L[ℝ] Lp ℝ 2 (thermalMeasure d s a β),
      IsKData (thermalMeasure d s a β) (rieszKernel d s) K :=
    S45.s45_kdata hd1 hs0 hsd hT.prob hM (L := L) (fun _ => hL)
  -- the mean of `r` is zero (IBP with `φ = 1`)
  have hmean : ∫ y, thermalGen d s a β χ y ∂(thermalMeasure d s a β) = 0 := by
    have h := S45.s45_ibp_mu hT hχ hB1 hB2 (φ := fun _ => (1 : ℝ)) contDiff_const (Bφ := 1) (Dφ := 0)
      (fun _ => by simp) (fun _ => by simp)
    simpa using h
  set Rh : Lp ℝ 2 (thermalMeasure d s a β) := hr2.toLp (thermalGen d s a β χ) with hRh
  have hRhae : (Rh : Euc d → ℝ) =ᵐ[thermalMeasure d s a β] thermalGen d s a β χ :=
    MemLp.coeFn_toLp hr2
  have hP : HRS.Whole.Q34.Pc (thermalMeasure d s a β) Rh = Rh := by
    rw [S45.s45_centered_iff, integral_congr_ae hRhae]; exact hmean
  have hUi := S45.s45_U_ae hφi
  have hkop : Kop (rieszKernel d s) (thermalMeasure d s a β) (thermalGen d s a β χ) =
      Kop (rieszKernel d s) (thermalMeasure d s a β) (Rh : Euc d → ℝ) :=
    (HRS.MS.TcR.tc2_kop_congr_ae hRhae).symm
  have heq : Rh + γ • K Rh = γ • S45.s45_U φi hφi := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add Rh (γ • K Rh), Lp.coeFn_smul γ (K Rh),
      Lp.coeFn_smul γ (S45.s45_U φi hφi), hRhae, hK.kop Rh hP, hcorr, hUi] with x e1 e2 e3 e4 e5 e6 e7
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, smul_eq_mul, e3, Pi.smul_apply, smul_eq_mul, e7, ← e5,
      e4, ← hkop]
    unfold susceptibilityOp at e6
    have : thermalGen d s a β χ x + γ * Kop (rieszKernel d s) (thermalMeasure d s a β)
        (thermalGen d s a β χ) x = γ * projMean (thermalMeasure d s a β) φi x := by
      calc _ = γ * (γ⁻¹ * thermalGen d s a β χ x + Kop (rieszKernel d s) (thermalMeasure d s a β)
            (thermalGen d s a β χ) x) := by field_simp
        _ = _ := by rw [e6]
    exact this
  have hRh2 : Rh = γ • S45.s45_Rr hK hγ.le (S45.s45_U φi hφi) := by
    rw [← map_smul, ← ContinuousLinearEquiv.symm_apply_eq, S45.s45_Rr_symm_apply]
    exact heq
  have hφj2 : MemLp φj 2 (thermalMeasure d s a β) :=
    MemLp.of_bound hφj.continuous.aestronglyMeasurable Bφ
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBφ x)
  have hRU : S45.s45_Rr hK hγ.le (S45.s45_U φi hφi) = γ⁻¹ • Rh := by
    rw [hRh2, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
  have hr1 : Integrable (thermalGen d s a β χ) (thermalMeasure d s a β) := hr2.integrable one_le_two
  have hφr : Integrable (fun x => φj x * thermalGen d s a β χ x) (thermalMeasure d s a β) :=
    hφj2.integrable_mul hr2
  have hin : ⟪S45.s45_U φj hφj2, Rh⟫ = ∫ x, φj x * thermalGen d s a β χ x ∂(thermalMeasure d s a β) := by
    rw [← HRS.Whole.Q34.l2Inner_eq (S45.s45_U_ae hφj2).symm hRhae.symm]
    unfold l2Inner projMean pair
    have : (fun x => (φj x - ∫ y, φj y ∂(thermalMeasure d s a β)) * thermalGen d s a β χ x) =
        fun x => φj x * thermalGen d s a β χ x -
          (∫ y, φj y ∂(thermalMeasure d s a β)) * thermalGen d s a β χ x := by
      funext x; ring
    rw [this, integral_sub hφr (hr1.const_mul _), integral_const_mul, hmean, mul_zero, sub_zero]
  rw [S45.s45_susceptibilityCov_eq hK hγ hφi hφj2, S45.s45_inner_Rr_comm hK hγ.le, hRU, real_inner_smul_right,
    hin, S45.s45_ibp_mu hT hχ hB1 hB2 hφj hBφ hDφ]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact real_inner_comm _ _


end S46

end
