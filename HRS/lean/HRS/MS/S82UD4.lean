import HRS.MS.S82UD3

/-!
# S8.2 A01 (S82U): the zero `μ`-row of the triple model
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

section rows
variable {d : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
  {Gc c : ℝ}

lemma u_gt_col_int (hd : 2 ≤ d) (hM : 0 ≤ M) (hA : 0 ≤ A) (hQ : PairCorrector a beta rho M A f Q)
    (hG : 0 ≤ Gc) (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho) (y : Euc d) :
    Integrable (fun z => ‖s82p2_gt Q z y‖) (HRS.Whole.withDensityReal rho) := by
  have h1 := u_int_pole hd hM hG hc hρ hρG y
  have hb := h1.const_mul (A * jbracket y ^ M)
  refine Integrable.mono' hb (u_gt_section_measurable Q y).norm.aestronglyMeasurable ?_
  filter_upwards [s82t_mu_ae_ne hd rho y] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have := u_gt_bound_W hd hA hQ hz (W := Phase2S82.pairWeight M z y) le_rfl
  refine this.trans ?_
  unfold Phase2S82.pairWeight
  rw [u_pole_symm z y]
  have := (u_jb_rpow_pos M z).le
  have := (u_jb_rpow_pos M y).le
  nlinarith [mul_nonneg (mul_nonneg hA (u_jb_rpow_pos M y).le) (mul_nonneg (u_jb_rpow_pos M z).le
    (by linarith [u_pole_pos y z] : (0:ℝ) ≤ pole y z))]

lemma u_gt_row_int (hd : 2 ≤ d) (hM : 0 ≤ M) (hA : 0 ≤ A) (hQ : PairCorrector a beta rho M A f Q)
    (hG : 0 ≤ Gc) (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho) (x : Euc d) :
    Integrable (fun z => s82p2_gt Q x z) (HRS.Whole.withDensityReal rho) := by
  have h1 := u_int_pole hd hM hG hc hρ hρG x
  have hb := h1.const_mul (A * jbracket x ^ M)
  refine Integrable.mono' hb (u_gt_section_measurable' Q x).aestronglyMeasurable ?_
  filter_upwards [s82t_mu_ae_ne hd rho x] with z hz
  have := u_gt_bound_W hd hA hQ hz.symm (W := Phase2S82.pairWeight M x z) le_rfl
  refine this.trans ?_
  unfold Phase2S82.pairWeight
  have := (u_jb_rpow_pos M z).le
  have := (u_jb_rpow_pos M x).le
  nlinarith [mul_nonneg (mul_nonneg hA (u_jb_rpow_pos M x).le) (mul_nonneg (u_jb_rpow_pos M z).le
    (by linarith [u_pole_pos x z] : (0:ℝ) ≤ pole x z))]

lemma u_Jt_row_zero (hd : 2 ≤ d) (hQ : PairCorrector a beta rho M A f Q) (x : Euc d) :
    Integrable (fun z => s82t_Jt (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (s82p2_gt Q) x z)
      (HRS.Whole.withDensityReal rho) ∧
    ∫ z, s82t_Jt (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (s82p2_gt Q) x z
      ∂(HRS.Whole.withDensityReal rho) = 0 := by
  have hae : ∀ᵐ z ∂(HRS.Whole.withDensityReal rho),
      s82t_Jt (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (s82p2_gt Q) x z =
        pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x z := by
    filter_upwards [s82t_mu_ae_ne hd rho x] with z hz
    exact (s82t_pairJ_eq hd hQ x z hz.symm).symm
  obtain ⟨-, hint, -, hz⟩ := hQ.nonlocal.1
  exact ⟨(hint x).congr (hae.mono fun z hz => hz.symm), by rw [integral_congr_ae hae]; exact hz x⟩

theorem u_zero_row (hd : 2 ≤ d) (hM : 0 ≤ M) (hA : 0 ≤ A) (hQ : PairCorrector a beta rho M A f Q)
    {Λ K : ℝ} (hF : UForce d rho Λ) (hG : 0 < Gc) (hc : 0 < c)
    (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho)
    (hFm : Measurable (forceMean rho)) (hK : ∀ x, ‖forceMean rho x‖ ≤ K) {x y : Euc d} (hxy : x ≠ y) :
    ∫ z, uGm (forceMean rho) (s82p2_gt Q)
      (s82t_Jt (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (s82p2_gt Q)) x y z
      ∂(HRS.Whole.withDensityReal rho) = 0 := by
  set mu := HRS.Whole.withDensityReal rho with hmu
  haveI : IsProbabilityMeasure mu := HRS.Whole.Q09A.measure_isProb hF.prob
  set g := s82p2_gt Q with hg
  set Fm := forceMean rho with hFmdef
  set Gf := rieszKernelGrad d (criticalS d) with hGf
  set C := critCoeff d a beta rho with hC
  set Jt := s82t_Jt C mu g with hJt
  have hρ := hF.prob
  have hGm : Measurable Gf := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hgm1 := u_gt_section_measurable Q
  have hgm2 := u_gt_section_measurable' Q
  have hG0 : 0 ≤ Gc := hG.le
  -- pieces
  set U : Euc d → ℝ := fun z => inner ℝ (Gf (x - z)) (g z y - g x y) + inner ℝ (Fm z) (g z y) with hU
  set V : Euc d → ℝ := fun z => inner ℝ (Gf (y - z)) (g z x - g y x) + inner ℝ (Fm z) (g z x) with hV
  set Wz : Euc d → ℝ := fun z => inner ℝ (Fm x - Gf (x - y)) (g x z) +
    inner ℝ (Fm y + Gf (x - y)) (g y z) - Jt x z - Jt y z with hW
  set k : ℝ := inner ℝ (Fm x) (g x y) + inner ℝ (Fm y) (g y x) - Jt x y with hk
  -- integrability
  have hmeas_edge : ∀ p q : Euc d, Measurable (fun z => inner ℝ (Gf (p - z)) (g z q - g p q)) := fun p q =>
    Measurable.inner (hGm.comp (measurable_const.sub measurable_id)) ((hgm1 q).sub measurable_const)
  have hc1 : ∀ p q : Euc d, p ≠ q → Integrable (fun z => inner ℝ (Gf (p - z)) (g z q - g p q)) mu := by
    intro p q hpq
    refine Integrable.mono' (u_edge_int hd hM hA hQ hG0 hc hρ hρG hpq) (hmeas_edge p q).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  have hf6 : ∀ q : Euc d, Integrable (fun z => inner ℝ (Fm z) (g z q)) mu := by
    intro q
    refine Integrable.mono' ((u_gt_col_int hd hM hA hQ hG0 hc hρ hρG q).const_mul K)
      (Measurable.inner hFm (hgm1 q)).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hK z) (norm_nonneg _))
  have hUi : Integrable U mu := (hc1 x y hxy).add (hf6 y)
  have hVi : Integrable V mu := (hc1 y x hxy.symm).add (hf6 x)
  have hrow : ∀ w : Euc d, Integrable (fun z => inner ℝ w (g x z)) mu := fun w =>
    ContinuousLinearMap.integrable_comp (innerSL ℝ w) (u_gt_row_int hd hM hA hQ hG0 hc hρ hρG x)
  have hrow' : ∀ w : Euc d, Integrable (fun z => inner ℝ w (g y z)) mu := fun w =>
    ContinuousLinearMap.integrable_comp (innerSL ℝ w) (u_gt_row_int hd hM hA hQ hG0 hc hρ hρG y)
  have hWi : Integrable Wz mu :=
    ((((hrow _).add (hrow' _)).sub (u_Jt_row_zero hd hQ x).1).sub (u_Jt_row_zero hd hQ y).1)
  -- the integrals
  have hIW : ∫ z, Wz z ∂mu = 0 := by
    have e1 : ∫ z, inner ℝ (Fm x - Gf (x - y)) (g x z) ∂mu = 0 := by
      rw [integral_inner (u_gt_row_int hd hM hA hQ hG0 hc hρ hρG x),
        HRS.MS.S82P2.s82p2_gt_centered hd hM hA Gc c hG hc hρ hρG hQ x]
      simp
    have e2 : ∫ z, inner ℝ (Fm y + Gf (x - y)) (g y z) ∂mu = 0 := by
      rw [integral_inner (u_gt_row_int hd hM hA hQ hG0 hc hρ hρG y),
        HRS.MS.S82P2.s82p2_gt_centered hd hM hA Gc c hG hc hρ hρG hQ y]
      simp
    have h3 : Integrable (fun z => inner ℝ (Fm x - Gf (x - y)) (g x z) +
        inner ℝ (Fm y + Gf (x - y)) (g y z)) mu := (hrow _).add (hrow' _)
    have h4 : Integrable (fun z => inner ℝ (Fm x - Gf (x - y)) (g x z) +
        inner ℝ (Fm y + Gf (x - y)) (g y z) - Jt x z) mu := h3.sub (u_Jt_row_zero hd hQ x).1
    simp only [hW]
    rw [integral_sub h4 (u_Jt_row_zero hd hQ y).1, integral_sub h3 (u_Jt_row_zero hd hQ x).1,
      integral_add (hrow _) (hrow' _), e1, e2, (u_Jt_row_zero hd hQ x).2, (u_Jt_row_zero hd hQ y).2]
    ring
  set J1 : Euc d → Euc d → ℝ := s82t_J1 C g with hJ1
  have hIU : ∫ z, U z ∂mu = (J1 x y - inner ℝ (g x y) (Fm x)) - ∫ x', J1 x' y ∂mu := by
    have h1 : J1 x y = (∫ z, inner ℝ (Gf (x - z)) (g z y - g x y) ∂mu) + inner ℝ (g x y) (Fm x) :=
      u_LE_Q hd hM hA hQ hF hG0 hc hρG hxy
    have h2 : ∫ x', J1 x' y ∂mu = -∫ z, inner ℝ (g z y) (Fm z) ∂mu :=
      u_jmean_Q hd hM hA hQ hF hG0 hc hρG y
    simp only [hU]
    rw [integral_add (hc1 x y hxy) (hf6 y)]
    have h3 : ∫ z, inner ℝ (Fm z) (g z y) ∂mu = ∫ z, inner ℝ (g z y) (Fm z) ∂mu :=
      integral_congr_ae (Eventually.of_forall fun z => real_inner_comm _ _)
    rw [h3, ← neg_neg (∫ z, inner ℝ (g z y) (Fm z) ∂mu), ← h2]
    have h4 : ∫ z, inner ℝ (Gf (x - z)) (g z y - g x y) ∂mu = J1 x y - inner ℝ (g x y) (Fm x) := by
      rw [h1]; ring
    rw [h4]; ring
  have hIV : ∫ z, V z ∂mu = (J1 y x - inner ℝ (g y x) (Fm y)) - ∫ x', J1 x' x ∂mu := by
    have h1 : J1 y x = (∫ z, inner ℝ (Gf (y - z)) (g z x - g y x) ∂mu) + inner ℝ (g y x) (Fm y) :=
      u_LE_Q hd hM hA hQ hF hG0 hc hρG hxy.symm
    have h2 : ∫ x', J1 x' x ∂mu = -∫ z, inner ℝ (g z x) (Fm z) ∂mu :=
      u_jmean_Q hd hM hA hQ hF hG0 hc hρG x
    simp only [hV]
    rw [integral_add (hc1 y x hxy.symm) (hf6 x)]
    have h3 : ∫ z, inner ℝ (Fm z) (g z x) ∂mu = ∫ z, inner ℝ (g z x) (Fm z) ∂mu :=
      integral_congr_ae (Eventually.of_forall fun z => real_inner_comm _ _)
    rw [h3, ← neg_neg (∫ z, inner ℝ (g z x) (Fm z) ∂mu), ← h2]
    have h4 : ∫ z, inner ℝ (Gf (y - z)) (g z x - g y x) ∂mu = J1 y x - inner ℝ (g y x) (Fm y) := by
      rw [h1]; ring
    rw [h4]; ring
  -- pointwise identity
  have hae : ∀ᵐ z ∂mu, uGm Fm g Jt x y z = (1 / 3) * (U z + V z + Wz z + k) := by
    filter_upwards [s82t_mu_ae_ne hd rho x, s82t_mu_ae_ne hd rho y] with z hzx hzy
    have hgr := uT_group Fm g hxy hzx.symm hzy.symm
    unfold uGm
    rw [hgr]
    simp only [hU, hV, hW, hk, inner_sub_left, inner_sub_right, inner_add_left]
    ring
  rw [integral_congr_ae hae, integral_const_mul]
  have hUV : Integrable (fun z => U z + V z) mu := hUi.add hVi
  have hUVW : Integrable (fun z => U z + V z + Wz z) mu := hUV.add hWi
  rw [integral_add hUVW (integrable_const k), integral_add hUV hWi, integral_add hUi hVi, hIU, hIV, hIW]
  simp only [integral_const, measure_univ, ENNReal.toReal_one, one_smul]
  have hTx : Jt x y = (J1 x y - ∫ x', J1 x' y ∂mu) + (J1 y x - ∫ x', J1 x' x ∂mu) := rfl
  have hr : mu.real Set.univ = 1 := by simp
  rw [hk, hTx, real_inner_comm (g x y) (Fm x), real_inner_comm (g y x) (Fm y), hr]
  ring

end rows

end HRS.MS.S82U
