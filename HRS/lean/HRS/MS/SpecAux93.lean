import HRS.MS.SpecAux92

/-!
# S8M: the `L²(μ)` estimate of `D_v U` from positivity of the Riesz energy (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  Abstract Hilbert-space step `s8p_hilb_ineq`: if `ν A = C - B`, `B = K + T`,
`⟨A, K⟩ ≥ 0` then `‖B‖ ≤ 2 (‖C‖ + ‖T‖)`; transferred to `L²(μ)` (`s8p_L2_alg`).  For the eigenfunction `e = ν w + U - c`
(`a = D_v w`, `c = D_v e`, `b = D_v U`, `K = g*(ρ a)`, `T = g*(w D_vρ)`): `∫ b² dμ ≤ 8 (∫ c² dμ + ∫ T² dμ)` (`s8p_DU_L2_dir`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

theorem s8p_hilb_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {A B C T K : H}
    {ν : ℝ} (hν : 0 < ν) (h1 : ν • A = C - B) (h2 : B = K + T) (h3 : 0 ≤ ⟪A, K⟫) :
    ‖B‖ ≤ 2 * (‖C‖ + ‖T‖) := by
  have hAB : -(‖A‖ * ‖T‖) ≤ ⟪A, B⟫ := by
    rw [h2, inner_add_right]
    have := real_inner_le_norm A (-T)
    rw [inner_neg_right, norm_neg] at this
    linarith
  have hνA : ν * ⟪A, B⟫ = ⟪C, B⟫ - ‖B‖ ^ 2 := by
    rw [← real_inner_smul_left, h1, inner_sub_left, real_inner_self_eq_norm_sq]
  have hCB : ⟪C, B⟫ ≤ ‖C‖ * ‖B‖ := real_inner_le_norm _ _
  have hνn : ν * ‖A‖ ≤ ‖C‖ + ‖B‖ := by
    have : ‖ν • A‖ = ν * ‖A‖ := by rw [norm_smul, Real.norm_of_nonneg hν.le]
    rw [← this, h1]
    exact norm_sub_le _ _
  have hT0 := norm_nonneg T
  have hB0 := norm_nonneg B
  have hC0 := norm_nonneg C
  have hA0 := norm_nonneg A
  have key : ‖B‖ ^ 2 ≤ ‖C‖ * ‖B‖ + (‖C‖ + ‖B‖) * ‖T‖ := by
    have h4 : ν * ‖A‖ * ‖T‖ ≤ (‖C‖ + ‖B‖) * ‖T‖ := mul_le_mul_of_nonneg_right hνn hT0
    nlinarith [mul_le_mul_of_nonneg_left hAB hν.le]
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg hC0 hT0, sq_nonneg (‖C‖ - ‖T‖)]

theorem s8p_inner_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem s8p_norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, s8p_inner_toLp hf hf]
  simp [sq]

theorem s8p_L2_alg {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b c K T : α → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hc : MemLp c 2 μ) (hK : MemLp K 2 μ) (hT : MemLp T 2 μ)
    {ν : ℝ} (hν : 0 < ν) (h1 : ∀ x, ν * a x = c x - b x) (h2 : ∀ x, b x = K x + T x)
    (h3 : 0 ≤ ∫ x, a x * K x ∂μ) :
    ∫ x, b x ^ 2 ∂μ ≤ 8 * (∫ x, c x ^ 2 ∂μ + ∫ x, T x ^ 2 ∂μ) := by
  set A := ha.toLp a with hA
  set B := hb.toLp b with hB
  set C := hc.toLp c with hC
  set K' := hK.toLp K with hK'
  set T' := hT.toLp T with hT'
  have e1 : ν • A = C - B := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_smul ν A, Lp.coeFn_sub C B, ha.coeFn_toLp, hb.coeFn_toLp,
      hc.coeFn_toLp] with x hs hsub hAx hBx hCx
    rw [hs, hsub]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [hAx, hBx, hCx, h1 x]
  have e2 : B = K' + T' := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add K' T', hb.coeFn_toLp, hK.coeFn_toLp, hT.coeFn_toLp] with x hs hBx hKx hTx
    rw [hs]
    simp only [Pi.add_apply]
    rw [hBx, hKx, hTx, h2 x]
  have e3 : 0 ≤ ⟪A, K'⟫ := by
    rw [s8p_inner_toLp ha hK]; exact h3
  have key := s8p_hilb_ineq hν e1 e2 e3
  have hs1 := s8p_norm_toLp_sq hb
  have hs2 := s8p_norm_toLp_sq hc
  have hs3 := s8p_norm_toLp_sq hT
  rw [← hs1, ← hs2, ← hs3]
  have h0 := norm_nonneg B
  nlinarith [sq_nonneg (‖C‖ - ‖T'‖), norm_nonneg C, norm_nonneg T', mul_le_mul key key h0 (by positivity)]

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_E_fderiv_split (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) (β : ℝ) (φ : 𝓢R) (x v : Euc d) :
    fderiv ℝ (s8p_E d s β ρ φ) x v =
      β⁻¹ * fderiv ℝ (s8p_ws ρ φ) x v + fderiv ℝ (s8p_U d s ρ φ) x v := by
  have hw : DifferentiableAt ℝ (s8p_ws ρ φ) x := ((s8p_ws_smooth hρ φ).differentiable (by simp)) x
  have hU : DifferentiableAt ℝ (s8p_U d s ρ φ) x :=
    ((s8p_U_smooth hd hs0 hsd hρ hE φ).differentiable (by simp)) x
  have h : HasFDerivAt (s8p_E d s β ρ φ)
      (β⁻¹ • fderiv ℝ (s8p_ws ρ φ) x + fderiv ℝ (s8p_U d s ρ φ) x) x :=
    ((hw.hasFDerivAt.const_mul β⁻¹).add hU.hasFDerivAt).sub_const (s8p_Cc d s ρ φ)
  rw [h.fderiv]
  simp

theorem s8p_DU_L2_dir (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    {β : ℝ} (hβ : 0 < β) (φ : 𝓢R) (v : Euc d)
    (hc : MemLp (fun x => fderiv ℝ (s8p_E d s β ρ φ) x v) 2 (HRS.Whole.withDensityReal ρ)) :
    ∫ x, fderiv ℝ (s8p_U d s ρ φ) x v ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
      8 * (∫ x, (fderiv ℝ (s8p_E d s β ρ φ) x v) ^ 2 ∂(HRS.Whole.withDensityReal ρ) +
        ∫ x, (HRS.Whole.convFun (rieszKernel d s)
          (fun y => s8p_ws ρ φ y * fderiv ℝ ρ y v) x) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
  haveI := mov2e_isProb hρ
  have hGk := s8p_rhoDw_good hρ hE φ v
  have hGt := s8p_wDrho_good hρ hE φ v
  set K : Euc d → ℝ := HRS.Whole.convFun (rieszKernel d s) (fun y => ρ y * fderiv ℝ (s8p_ws ρ φ) y v) with hK
  set T : Euc d → ℝ := HRS.Whole.convFun (rieszKernel d s) (fun y => s8p_ws ρ φ y * fderiv ℝ ρ y v) with hT
  have hKm : Measurable K := s8p_convFun_meas hGk.1
  have hTm : Measurable T := s8p_convFun_meas hGt.1
  obtain ⟨bK, hbK⟩ := hGk.conv_bound hs0 hsd
  obtain ⟨bT, hbT⟩ := hGt.conv_bound hs0 hsd
  have hKL : MemLp K 2 (HRS.Whole.withDensityReal ρ) :=
    MemLp.of_bound hKm.aestronglyMeasurable bK (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hbK x)
  have hTL : MemLp T 2 (HRS.Whole.withDensityReal ρ) :=
    MemLp.of_bound hTm.aestronglyMeasurable bT (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hbT x)
  have hb_eq : ∀ x, fderiv ℝ (s8p_U d s ρ φ) x v = K x + T x := fun x => s8p_DU_split hd hs0 hsd hρ hE φ x v
  have hbL : MemLp (fun x => fderiv ℝ (s8p_U d s ρ φ) x v) 2 (HRS.Whole.withDensityReal ρ) := by
    have : (fun x => fderiv ℝ (s8p_U d s ρ φ) x v) = fun x => K x + T x := funext hb_eq
    rw [this]; exact hKL.add hTL
  have h1 : ∀ x, β⁻¹ * (β * (fderiv ℝ (s8p_E d s β ρ φ) x v - fderiv ℝ (s8p_U d s ρ φ) x v)) =
      fderiv ℝ (s8p_E d s β ρ φ) x v - fderiv ℝ (s8p_U d s ρ φ) x v := fun x => by
    field_simp
  have haL : MemLp (fun x => β * (fderiv ℝ (s8p_E d s β ρ φ) x v - fderiv ℝ (s8p_U d s ρ φ) x v)) 2
      (HRS.Whole.withDensityReal ρ) := (hc.sub hbL).const_mul β
  have h3 : 0 ≤ ∫ x, (β * (fderiv ℝ (s8p_E d s β ρ φ) x v - fderiv ℝ (s8p_U d s ρ φ) x v)) * K x
      ∂(HRS.Whole.withDensityReal ρ) := by
    rw [mov2e_integral_mu hρ]
    have := s8p_Good_energy_nonneg hd hs0 hsd hGk
    refine this.trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    have e := s8p_E_fderiv_split hd hs0.le hsd hρ hE β φ x v
    have e2 : β * (fderiv ℝ (s8p_E d s β ρ φ) x v - fderiv ℝ (s8p_U d s ρ φ) x v) =
        fderiv ℝ (s8p_ws ρ φ) x v := by
      rw [e]; field_simp; ring
    rw [e2]; ring
  exact s8p_L2_alg haL hbL hc hKL hTL (inv_pos.2 hβ) h1 hb_eq h3

end HRS.MS.Spec
