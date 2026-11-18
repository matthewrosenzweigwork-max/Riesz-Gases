import HRS.MS.TiltAux5

/-!
# S4.7 packet P5b: the generator identity `(★')` and the covariance identification at the reference `ρ`

`s47_star`: `Δχ - q ⟨x, ∇χ⟩ + ⟨Bd + γ ∇U, ∇χ⟩ - γ H_μ = -γ φ + c₀` Lebesgue-a.e. (copy of `s46_star`; the drift
`(β - γ) ∇U` of S4.6 is `-(Bd + γ ∇U)`).  `s47_cov_identity`: `C_{ij} = γ⁻¹ ∫ ⟨∇χ_i, ∇φ_j⟩ dμ` (copy of `s46_cov_identity`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

/-- The pointwise generator identity (`★'`). -/
theorem s47_star (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {q γ C c BU BB : ℝ}
    {Bd : Euc d → Euc d} (hγ : 0 < γ) (hT : TRef d s ρ q C c BU BB Bd) {χ : Euc d → ℝ}
    (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) {φ : Euc d → ℝ}
    (hcorr : ∀ᵐ x ∂(withDensityReal ρ),
      susceptibilityOp (rieszKernel d s) (withDensityReal ρ) γ (weightedGen ρ χ) x =
        projMean (withDensityReal ρ) φ x) :
    ∃ c0 : ℝ, ∀ᵐ x ∂(volume : Measure (Euc d)),
      Laplacian.laplacian χ x - q * ⟪x, gradient χ x⟫ +
        ⟪Bd x + γ • gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) x, gradient χ x⟫ -
        γ * ∫ y, commutatorKernel d s (gradient χ) x y ∂(withDensityReal ρ) = -γ * φ x + c0 := by
  obtain ⟨F, hFdef⟩ : ∃ F : Euc d → ℝ, ∀ x, F x = ∫ y, rieszKernel d s (x - y) *
      weightedGen ρ χ y ∂(withDensityReal ρ) := ⟨_, fun _ => rfl⟩
  refine ⟨γ * (pair (withDensityReal ρ) φ - pair (withDensityReal ρ) F),
    s45_ae_leb_of_ae_mu hT.prob hT.pos ?_⟩
  filter_upwards [hcorr] with x hx
  have h1 := s47_corr_identity hd hs0 hsd hT hχ hB1 hB2 x
  rw [h1, ← hFdef x]
  have h2 := s47_gen_eq hT (χ := χ) x
  have hx' : γ⁻¹ * weightedGen ρ χ x + (F x - pair (withDensityReal ρ) F) =
      φ x - pair (withDensityReal ρ) φ := by
    have e : (fun x => ∫ y, rieszKernel d s (x - y) * weightedGen ρ χ y
        ∂(withDensityReal ρ)) = F := funext fun x => (hFdef x).symm
    unfold susceptibilityOp Kop projMean at hx
    rw [e] at hx
    exact hx
  have hγ0 : γ ≠ 0 := hγ.ne'
  have h3 : weightedGen ρ χ x + γ * (F x - pair (withDensityReal ρ) F) =
      γ * (φ x - pair (withDensityReal ρ) φ) := by
    calc _ = γ * (γ⁻¹ * weightedGen ρ χ x + (F x - pair (withDensityReal ρ) F)) := by
          field_simp
      _ = _ := by rw [hx']
  have h4 : ⟪q • x - Bd x, gradient χ x⟫ = q * ⟪x, gradient χ x⟫ - ⟪Bd x, gradient χ x⟫ := by
    rw [inner_sub_left, real_inner_smul_left]
  rw [h2, h4] at h3
  simp only [inner_add_left, real_inner_smul_left]
  have h5 := real_inner_comm (gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) x)
    (gradient χ x)
  rw [h5]
  linarith

theorem s47_cov_identity (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {q γ C c BU BB : ℝ}
    {Bd : Euc d → Euc d} (hγ : 0 < γ) (hT : TRef d s ρ q C c BU BB Bd) {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ)
    {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2)
    {φi φj : Euc d → ℝ} (hφi : MemLp φi 2 (withDensityReal ρ))
    (hr2 : MemLp (weightedGen ρ χ) 2 (withDensityReal ρ))
    (hcorr : ∀ᵐ x ∂(withDensityReal ρ),
      susceptibilityOp (rieszKernel d s) (withDensityReal ρ) γ (weightedGen ρ χ) x =
        projMean (withDensityReal ρ) φi x)
    (hφj : ContDiff ℝ 1 φj) {Bφ Dφ : ℝ} (hBφ : ∀ x, |φj x| ≤ Bφ)
    (hDφ : ∀ x, ‖fderiv ℝ φj x‖ ≤ Dφ) :
    susceptibilityCov (rieszKernel d s) (withDensityReal ρ) γ φi φj =
      γ⁻¹ * ∫ y, ⟪gradient χ y, gradient φj y⟫ ∂(withDensityReal ρ) := by
  have hd1 : 1 ≤ d := by omega
  haveI hprob : IsProbabilityMeasure (withDensityReal ρ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨L, hL⟩ := s47_logmoment2 hT
  have hM : ∀ x, ρ x ≤ C := fun x => (le_abs_self _).trans
    ((hT.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
      nlinarith [hT.C0]))
  obtain ⟨K, hK⟩ : ∃ K : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ),
      IsKData (withDensityReal ρ) (rieszKernel d s) K :=
    S45.s45_kdata hd1 hs0 hsd hT.prob hM (L := L) (fun _ => hL)
  -- the mean of `r` is zero (IBP with `φ = 1`)
  have hmean : ∫ y, weightedGen ρ χ y ∂(withDensityReal ρ) = 0 := by
    have h := s47_ibp_mu hT hχ hB1 hB2 (φ := fun _ => (1 : ℝ)) contDiff_const (Bφ := 1) (Dφ := 0)
      (fun _ => by simp) (fun _ => by simp)
    simpa using h
  set Rh : Lp ℝ 2 (withDensityReal ρ) := hr2.toLp (weightedGen ρ χ) with hRh
  have hRhae : (Rh : Euc d → ℝ) =ᵐ[withDensityReal ρ] weightedGen ρ χ :=
    MemLp.coeFn_toLp hr2
  have hP : HRS.Whole.Q34.Pc (withDensityReal ρ) Rh = Rh := by
    rw [S45.s45_centered_iff, integral_congr_ae hRhae]; exact hmean
  have hUi := S45.s45_U_ae hφi
  have hkop : Kop (rieszKernel d s) (withDensityReal ρ) (weightedGen ρ χ) =
      Kop (rieszKernel d s) (withDensityReal ρ) (Rh : Euc d → ℝ) :=
    (HRS.MS.TcR.tc2_kop_congr_ae hRhae).symm
  have heq : Rh + γ • K Rh = γ • S45.s45_U φi hφi := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add Rh (γ • K Rh), Lp.coeFn_smul γ (K Rh),
      Lp.coeFn_smul γ (S45.s45_U φi hφi), hRhae, hK.kop Rh hP, hcorr, hUi] with x e1 e2 e3 e4 e5 e6 e7
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, smul_eq_mul, e3, Pi.smul_apply, smul_eq_mul, e7, ← e5,
      e4, ← hkop]
    unfold susceptibilityOp at e6
    have : weightedGen ρ χ x + γ * Kop (rieszKernel d s) (withDensityReal ρ)
        (weightedGen ρ χ) x = γ * projMean (withDensityReal ρ) φi x := by
      calc _ = γ * (γ⁻¹ * weightedGen ρ χ x + Kop (rieszKernel d s) (withDensityReal ρ)
            (weightedGen ρ χ) x) := by field_simp
        _ = _ := by rw [e6]
    exact this
  have hRh2 : Rh = γ • S45.s45_Rr hK hγ.le (S45.s45_U φi hφi) := by
    rw [← map_smul, ← ContinuousLinearEquiv.symm_apply_eq, S45.s45_Rr_symm_apply]
    exact heq
  have hφj2 : MemLp φj 2 (withDensityReal ρ) :=
    MemLp.of_bound hφj.continuous.aestronglyMeasurable Bφ
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBφ x)
  have hRU : S45.s45_Rr hK hγ.le (S45.s45_U φi hφi) = γ⁻¹ • Rh := by
    rw [hRh2, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
  have hr1 : Integrable (weightedGen ρ χ) (withDensityReal ρ) := hr2.integrable one_le_two
  have hφr : Integrable (fun x => φj x * weightedGen ρ χ x) (withDensityReal ρ) :=
    hφj2.integrable_mul hr2
  have hin : ⟪S45.s45_U φj hφj2, Rh⟫ = ∫ x, φj x * weightedGen ρ χ x ∂(withDensityReal ρ) := by
    rw [← HRS.Whole.Q34.l2Inner_eq (S45.s45_U_ae hφj2).symm hRhae.symm]
    unfold l2Inner projMean pair
    have : (fun x => (φj x - ∫ y, φj y ∂(withDensityReal ρ)) * weightedGen ρ χ x) =
        fun x => φj x * weightedGen ρ χ x -
          (∫ y, φj y ∂(withDensityReal ρ)) * weightedGen ρ χ x := by
      funext x; ring
    rw [this, integral_sub hφr (hr1.const_mul _), integral_const_mul, hmean, mul_zero, sub_zero]
  rw [S45.s45_susceptibilityCov_eq hK hγ hφi hφj2, S45.s45_inner_Rr_comm hK hγ.le, hRU, real_inner_smul_right,
    hin, s47_ibp_mu hT hχ hB1 hB2 hφj hBφ hDφ]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact real_inner_comm _ _



end S47

end
