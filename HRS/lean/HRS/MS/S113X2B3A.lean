import HRS.MS.S113X2B3

/-!
# S11.3 X2 part B3A: mollification of bounded compactly supported densities

Smoothness, support, derivative formulas and the exact commutator decomposition
`g_δ = ν Δ(u_δ) - div (b u_δ) + c_δ`, via Mathlib's convolution API.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HRS.MS.S113X2B

variable {n : ℕ}

/-- S0: a mollifier exists. -/
theorem s113b_Moll_exists (n : ℕ) : Nonempty (s113b_Moll n) := by
  let f : ContDiffBump (0 : s113b_E n) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  exact ⟨⟨f.normed volume, f.contDiff_normed (n := ⊤), f.nonneg_normed,
    by rw [f.tsupport_normed_eq], f.integral_normed⟩⟩

/-! ### S1: the scaled mollifier -/

theorem s113b_scaled_cinf (m : s113b_Moll n) (δ : ℝ) : s113b_Cinf (m.scaled δ) :=
  contDiff_const.mul (m.smooth.comp (contDiff_id.const_smul δ⁻¹))

theorem s113b_scaled_nonneg (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) (z : s113b_E n) :
    0 ≤ m.scaled δ z :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hδ.le _)) (m.nonneg _)

theorem s113b_scaled_tsupport (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) :
    tsupport (m.scaled δ) ⊆ Metric.closedBall 0 δ := by
  refine closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall
  have hz' : m.ρ (δ⁻¹ • z) ≠ 0 := by
    intro h; exact hz (by simp [s113b_Moll.scaled, h])
  have h1 : δ⁻¹ • z ∈ Metric.closedBall (0 : s113b_E n) 1 := m.supp (subset_tsupport _ hz')
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hδ.le] at h1
  rw [mem_closedBall_zero_iff]
  have := mul_le_mul_of_nonneg_left h1 hδ.le
  rwa [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul, mul_one] at this

theorem s113b_scaled_hcs (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (m.scaled δ) :=
  (isCompact_closedBall (0 : s113b_E n) δ).of_isClosed_subset (isClosed_tsupport _)
    (s113b_scaled_tsupport m hδ)

theorem s113b_scaled_integral (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) :
    ∫ z, m.scaled δ z = 1 := by
  unfold s113b_Moll.scaled
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume m.ρ δ, finrank_euclideanSpace_fin,
    m.integral_one, abs_of_pos (pow_pos hδ _), smul_eq_mul, mul_one,
    inv_mul_cancel₀ (pow_pos hδ n).ne']

theorem s113b_scaled_c1 (m : s113b_Moll n) (δ : ℝ) : ContDiff ℝ 1 (m.scaled δ) :=
  (s113b_scaled_cinf m δ).of_le (by exact_mod_cast le_top)

theorem s113b_fderiv_c1 {f : s113b_E n → ℝ} (hf : s113b_Cinf f) : ContDiff ℝ 1 (fderiv ℝ f) :=
  hf.fderiv_right (WithTop.coe_le_coe.2 le_top)

theorem s113b_scaled_integrable (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (m.scaled δ) :=
  (s113b_scaled_cinf m δ).continuous.integrable_of_hasCompactSupport (s113b_scaled_hcs m hδ)

theorem s113b_lap_cont {φ : s113b_E n → ℝ} (hφ : s113b_Cinf φ) : Continuous (s113b_lap φ) := by
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (s113b_fderiv_c1 hφ).continuous_fderiv one_ne_zero
  exact continuous_finsetSum _ fun k _ =>
    (hc2.clm_apply continuous_const).clm_apply continuous_const

theorem s113b_lap_hcs {φ : s113b_E n → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (s113b_lap φ) := by
  have h := ((hc.fderiv ℝ).fderiv ℝ).comp_left
    (g := fun L : s113b_E n →L[ℝ] s113b_E n →L[ℝ] ℝ =>
      ∑ k : Fin n, L (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)) (by simp)
  exact h

/-! ### integrability and convolution -/

theorem s113b_int {u : s113b_E n → ℝ} {B : ℝ} {K : Set (s113b_E n)} (hm : Measurable u)
    (hB : ∀ y, |u y| ≤ B) (hK : IsCompact K) (hu0 : ∀ y, y ∉ K → u y = 0)
    {ψ : s113b_E n → ℝ} (hψ : Continuous ψ) : Integrable (fun y => u y * ψ y) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h1 : IntegrableOn ψ K := hψ.continuousOn.integrableOn_compact hK
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := K) ?_
    (fun y hy => by simp [hu0 y hy])
  refine Integrable.mono' (Integrable.const_mul (Integrable.norm h1) B)
    (hm.mul hψ.measurable).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [norm_mul]
  exact mul_le_mul (by simpa using hB y) le_rfl (norm_nonneg _) hB0

theorem s113b_int_u {u : s113b_E n → ℝ} {B : ℝ} {K : Set (s113b_E n)} (hm : Measurable u)
    (hB : ∀ y, |u y| ≤ B) (hK : IsCompact K) (hu0 : ∀ y, y ∉ K → u y = 0) : Integrable u := by
  simpa using s113b_int hm hB hK hu0 (ψ := fun _ => 1) continuous_const

/-- The convolution `u ⋆ φ`, `x ↦ ∫ u(y) φ(x-y) dy`. -/
def s113b_cv (u φ : s113b_E n → ℝ) : s113b_E n → ℝ :=
  convolution u φ (ContinuousLinearMap.mul ℝ ℝ) volume

theorem s113b_cv_apply (u φ : s113b_E n → ℝ) (x : s113b_E n) :
    s113b_cv u φ x = ∫ y, u y * φ (x - y) := by
  simp [s113b_cv, convolution_def]

theorem s113b_cv_fderiv {u φ : s113b_E n → ℝ} (hu : Integrable u) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (x w : s113b_E n) :
    fderiv ℝ (s113b_cv u φ) x w = s113b_cv u (fun z => fderiv ℝ φ z w) x := by
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hu.locallyIntegrable hφ x
  have hex : ConvolutionExistsAt u (fderiv ℝ φ) x
      (ContinuousLinearMap.precompR (s113b_E n) (ContinuousLinearMap.mul ℝ ℝ)) volume :=
    (hc.fderiv ℝ).convolutionExists_right _ hu.locallyIntegrable
      (hφ.continuous_fderiv one_ne_zero) x
  have e : s113b_cv u φ = convolution u φ (ContinuousLinearMap.mul ℝ ℝ) volume := rfl
  rw [e, h.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex w, s113b_cv_apply]
  simp [ContinuousLinearMap.precompR_apply]

theorem s113b_cv_cinf {u φ : s113b_E n → ℝ} (hu : Integrable u) (hφ : s113b_Cinf φ)
    (hc : HasCompactSupport φ) : s113b_Cinf (s113b_cv u φ) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hu.locallyIntegrable hφ

theorem s113b_mol_eq_cv (m : s113b_Moll n) (δ : ℝ) (u : s113b_E n → ℝ) :
    s113b_mol m δ u = s113b_cv u (m.scaled δ) := by
  funext x
  rw [s113b_cv_apply]
  exact integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)

theorem s113b_fderiv_apply_fd {f : s113b_E n → ℝ} {x : s113b_E n}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (e w : s113b_E n) :
    fderiv ℝ (fun z => fderiv ℝ f z e) x w = fderiv ℝ (fderiv ℝ f) x w e := by
  have h : HasFDerivAt (fun z => fderiv ℝ f z e)
      ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp x hf.hasFDerivAt
  rw [h.fderiv]
  rfl

theorem s113b_sum_single (L : s113b_E n →L[ℝ] ℝ) (w : s113b_E n) :
    ∑ k : Fin n, w k * L (EuclideanSpace.single k 1) = L w := by
  have h : w = ∑ k : Fin n, w k • EuclideanSpace.single k (1 : ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [h]
  simp [map_sum]

/-! ### S2, S3: mollification of a bounded compactly supported density -/

section Dens

variable {u : s113b_E n → ℝ} {B : ℝ} {K : Set (s113b_E n)}
  (hm : Measurable u) (hB : ∀ y, |u y| ≤ B) (hK : IsCompact K) (hu0 : ∀ y, y ∉ K → u y = 0)

include hm hB hK hu0

theorem s113b_mol_cinf (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) : s113b_Cinf (s113b_mol m δ u) := by
  rw [s113b_mol_eq_cv]
  exact s113b_cv_cinf (s113b_int_u hm hB hK hu0) (s113b_scaled_cinf m δ) (s113b_scaled_hcs m hδ)

theorem s113b_mol_nonneg (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) (h0 : ∀ y, 0 ≤ u y)
    (x : s113b_E n) : 0 ≤ s113b_mol m δ u x :=
  integral_nonneg fun y => mul_nonneg (s113b_scaled_nonneg m hδ _) (h0 y)

theorem s113b_mol_le (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) (hBu : ∀ y, u y ≤ B)
    (x : s113b_E n) : s113b_mol m δ u x ≤ B := by
  have hcont : Continuous fun y => m.scaled δ (x - y) :=
    (s113b_scaled_cinf m δ).continuous.comp (continuous_const.sub continuous_id)
  have hi1 : Integrable (fun y => m.scaled δ (x - y) * u y) :=
    (s113b_int hm hB hK hu0 hcont).congr (ae_of_all _ fun y => mul_comm _ _)
  have hi2 : Integrable (fun y => m.scaled δ (x - y) * B) :=
    ((s113b_scaled_integrable m hδ).comp_sub_left x).mul_const B
  calc s113b_mol m δ u x ≤ ∫ y, m.scaled δ (x - y) * B :=
        integral_mono hi1 hi2 fun y => mul_le_mul_of_nonneg_left (hBu y) (s113b_scaled_nonneg m hδ _)
    _ = B := by
        rw [integral_mul_const, integral_sub_left_eq_self (m.scaled δ) volume x,
          s113b_scaled_integral m hδ, one_mul]

theorem s113b_mol_eq_zero (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) {x : s113b_E n}
    (h : ∀ y ∈ K, δ < dist x y) : s113b_mol m δ u x = 0 := by
  unfold s113b_mol
  have : (fun y => m.scaled δ (x - y) * u y) = fun _ => 0 := by
    funext y
    by_cases hy : y ∈ K
    · have hn : x - y ∉ tsupport (m.scaled δ) := fun hmem => by
        have := s113b_scaled_tsupport m hδ hmem
        rw [mem_closedBall_zero_iff, ← dist_eq_norm] at this
        exact absurd (h y hy) (not_lt.2 this)
      rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]
    · rw [hu0 y hy, mul_zero]
  rw [this]; simp

theorem s113b_mol_tsupport (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) :
    tsupport (s113b_mol m δ u) ⊆ Metric.cthickening δ K := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_cthickening
  by_contra hxK
  refine hx (s113b_mol_eq_zero hm hB hK hu0 m hδ fun y hy => ?_)
  by_contra hle
  exact hxK (Metric.mem_cthickening_of_dist_le x y δ K hy (not_lt.1 hle))

theorem s113b_mol_hcs (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (s113b_mol m δ u) :=
  (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _)
    (s113b_mol_tsupport hm hB hK hu0 m hδ)

theorem s113b_mol_fderiv (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) (x w : s113b_E n) :
    fderiv ℝ (s113b_mol m δ u) x w = ∫ y, u y * fderiv ℝ (m.scaled δ) (x - y) w := by
  rw [s113b_mol_eq_cv, s113b_cv_fderiv (s113b_int_u hm hB hK hu0) (s113b_scaled_c1 m δ)
    (s113b_scaled_hcs m hδ), s113b_cv_apply]

theorem s113b_mol_lap (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) (x : s113b_E n) :
    s113b_lap (s113b_mol m δ u) x = ∫ y, u y * s113b_lap (m.scaled δ) (x - y) := by
  have hu := s113b_int_u hm hB hK hu0
  have hφ := s113b_scaled_cinf m δ
  have hv := s113b_mol_cinf hm hB hK hu0 m hδ
  have hvd : DifferentiableAt ℝ (fderiv ℝ (s113b_mol m δ u)) x :=
    ((s113b_fderiv_c1 hv).differentiable one_ne_zero).differentiableAt
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ (m.scaled δ))) :=
    (s113b_fderiv_c1 hφ).continuous_fderiv one_ne_zero
  have hk : ∀ k : Fin n, fderiv ℝ (fderiv ℝ (s113b_mol m δ u)) x (EuclideanSpace.single k 1)
      (EuclideanSpace.single k 1) = ∫ y, u y * fderiv ℝ (fderiv ℝ (m.scaled δ)) (x - y)
        (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) := by
    intro k
    set e : s113b_E n := EuclideanSpace.single k 1 with he
    have hfun : (fun z => fderiv ℝ (s113b_mol m δ u) z e)
        = s113b_cv u (fun z => fderiv ℝ (m.scaled δ) z e) := by
      funext z
      rw [s113b_mol_eq_cv]
      exact s113b_cv_fderiv hu (s113b_scaled_c1 m δ) (s113b_scaled_hcs m hδ) z e
    have hDc1 : ContDiff ℝ 1 (fun z => fderiv ℝ (m.scaled δ) z e) :=
      (s113b_fderiv_c1 hφ).clm_apply contDiff_const
    have hDcs : HasCompactSupport (fun z => fderiv ℝ (m.scaled δ) z e) :=
      (s113b_scaled_hcs m hδ).fderiv_apply ℝ e
    rw [← s113b_fderiv_apply_fd hvd, hfun, s113b_cv_fderiv hu hDc1 hDcs, s113b_cv_apply]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have hd : DifferentiableAt ℝ (fderiv ℝ (m.scaled δ)) (x - y) :=
      ((s113b_fderiv_c1 hφ).differentiable one_ne_zero).differentiableAt
    simp only
    rw [s113b_fderiv_apply_fd hd]
  have hint : ∀ k : Fin n, Integrable (fun y => u y * fderiv ℝ (fderiv ℝ (m.scaled δ)) (x - y)
        (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)) := fun k =>
    s113b_int hm hB hK hu0 (((hc2.comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const).clm_apply continuous_const)
  calc s113b_lap (s113b_mol m δ u) x
      = ∑ k : Fin n, ∫ y, u y * fderiv ℝ (fderiv ℝ (m.scaled δ)) (x - y)
          (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) :=
        Finset.sum_congr rfl fun k _ => hk k
    _ = ∫ y, ∑ k : Fin n, u y * fderiv ℝ (fderiv ℝ (m.scaled δ)) (x - y)
          (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) :=
        (integral_finsetSum _ fun k _ => hint k).symm
    _ = ∫ y, u y * s113b_lap (m.scaled δ) (x - y) := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [s113b_lap, Finset.mul_sum]

/-! ### S4: the exact decomposition `g_δ = ν Δ u_δ - div (b u_δ) + c_δ` -/

theorem s113b_gdel_eq (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) (ν : ℝ) {b : s113b_E n → s113b_E n}
    (hb : ContDiff ℝ 1 b) (x : s113b_E n) :
    s113b_gdel m δ ν b u x = ν * s113b_lap (s113b_mol m δ u) x
      - s113b_div (fun y => (s113b_mol m δ u y) • b y) x + s113b_comm m δ b u x := by
  have hφ := s113b_scaled_cinf m δ
  have hD : Continuous (fderiv ℝ (m.scaled δ)) := (s113b_scaled_c1 m δ).continuous_fderiv one_ne_zero
  have hL := s113b_lap_cont hφ
  have hbc : Continuous b := hb.continuous
  have hsub : Continuous fun y : s113b_E n => x - y := continuous_const.sub continuous_id
  have hint1 : Integrable (fun y => u y * s113b_lap (m.scaled δ) (x - y)) :=
    s113b_int hm hB hK hu0 (hL.comp hsub)
  have hint2 : Integrable (fun y => u y * fderiv ℝ (m.scaled δ) (x - y) (b x)) :=
    s113b_int hm hB hK hu0 ((hD.comp hsub).clm_apply (continuous_const (y := b x)))
  have hint3 : Integrable (fun y => u y * fderiv ℝ (m.scaled δ) (x - y) (b y)) :=
    s113b_int hm hB hK hu0 ((hD.comp hsub).clm_apply hbc)
  have hint4 : Integrable (fun y => u y * m.scaled δ (x - y)) :=
    s113b_int hm hB hK hu0 (hφ.continuous.comp hsub)
  have hvd : DifferentiableAt ℝ (s113b_mol m δ u) x :=
    ((s113b_mol_cinf hm hB hK hu0 m hδ).differentiable (by simp)).differentiableAt
  have hbk : ∀ k : Fin n, DifferentiableAt ℝ (fun y => b y k) x := fun k =>
    (((EuclideanSpace.proj k : s113b_E n →L[ℝ] ℝ).contDiff.comp hb).differentiable one_ne_zero).differentiableAt
  have hdiv : s113b_div (fun y => (s113b_mol m δ u y) • b y) x
      = s113b_mol m δ u x * s113b_div b x + fderiv ℝ (s113b_mol m δ u) x (b x) := by
    unfold s113b_div
    have hk : ∀ k : Fin n, fderiv ℝ (fun y => (s113b_mol m δ u y • b y) k) x (EuclideanSpace.single k 1)
        = s113b_mol m δ u x * fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1)
          + b x k * fderiv ℝ (s113b_mol m δ u) x (EuclideanSpace.single k 1) := by
      intro k
      have h : (fun y => (s113b_mol m δ u y • b y) k) = fun y => s113b_mol m δ u y * b y k := by
        funext y; simp
      rw [h]
      have h2 := fderiv_mul hvd (hbk k)
      have h3 : fderiv ℝ (fun y => s113b_mol m δ u y * b y k) x
          = s113b_mol m δ u x • fderiv ℝ (fun y => b y k) x + b x k • fderiv ℝ (s113b_mol m δ u) x := h2
      rw [h3]
      simp
    simp_rw [hk]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, s113b_sum_single]
  have hvx : s113b_mol m δ u x = ∫ y, u y * m.scaled δ (x - y) := by
    rw [s113b_mol_eq_cv, s113b_cv_apply]
  have e1 : s113b_gdel m δ ν b u x = ν * (∫ y, u y * s113b_lap (m.scaled δ) (x - y))
      - ∫ y, u y * fderiv ℝ (m.scaled δ) (x - y) (b y) := by
    unfold s113b_gdel
    have : ∀ y, u y * (ν * s113b_lap (m.scaled δ) (x - y) - fderiv ℝ (m.scaled δ) (x - y) (b y))
        = ν * (u y * s113b_lap (m.scaled δ) (x - y)) - u y * fderiv ℝ (m.scaled δ) (x - y) (b y) :=
      fun y => by ring
    simp_rw [this]
    rw [integral_sub (hint1.const_mul ν) hint3, integral_const_mul]
  have e2 : s113b_comm m δ b u x = (∫ y, u y * fderiv ℝ (m.scaled δ) (x - y) (b x))
      - (∫ y, u y * fderiv ℝ (m.scaled δ) (x - y) (b y))
      + s113b_div b x * (∫ y, u y * m.scaled δ (x - y)) := by
    unfold s113b_comm
    have : ∀ y, u y * (fderiv ℝ (m.scaled δ) (x - y) (b x - b y) + s113b_div b x * m.scaled δ (x - y))
        = u y * fderiv ℝ (m.scaled δ) (x - y) (b x) - u y * fderiv ℝ (m.scaled δ) (x - y) (b y)
          + s113b_div b x * (u y * m.scaled δ (x - y)) := fun y => by rw [map_sub]; ring
    simp_rw [this]
    have hs : Integrable (fun y => u y * fderiv ℝ (m.scaled δ) (x - y) (b x)
        - u y * fderiv ℝ (m.scaled δ) (x - y) (b y)) := hint2.sub hint3
    rw [integral_add hs (hint4.const_mul _), integral_sub hint2 hint3, integral_const_mul]
  rw [e1, e2, hdiv, s113b_mol_lap hm hB hK hu0 m hδ, s113b_mol_fderiv hm hB hK hu0 m hδ, hvx]
  ring

end Dens

/-! ### S5: a uniform bound for `g_δ` and joint measurability -/

theorem s113b_gdel_bound (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) (ν : ℝ)
    {b : s113b_E n → s113b_E n} (hb : Continuous b) {K : Set (s113b_E n)} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ (u : s113b_E n → ℝ) (B : ℝ), (∀ y, |u y| ≤ B) → (∀ y, y ∉ K → u y = 0) →
      ∀ x, |s113b_gdel m δ ν b u x| ≤ C * B := by
  have hφ := s113b_scaled_cinf m δ
  have hcs := s113b_scaled_hcs m hδ
  have hD : Continuous (fderiv ℝ (m.scaled δ)) := (s113b_scaled_c1 m δ).continuous_fderiv one_ne_zero
  obtain ⟨Cl, hCl⟩ := (s113b_lap_cont hφ).bounded_above_of_compact_support (s113b_lap_hcs hcs)
  obtain ⟨Cd, hCd⟩ := hD.bounded_above_of_compact_support (hcs.fderiv ℝ)
  obtain ⟨Cb, hCb⟩ := hK.exists_bound_of_continuousOn hb.continuousOn
  have hCd0 : 0 ≤ Cd := (norm_nonneg _).trans (hCd 0)
  refine ⟨(|ν| * Cl + Cd * Cb) * volume.real K, fun u B hB hu0 x => ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hH : ∀ y ∈ K, ‖u y * (ν * s113b_lap (m.scaled δ) (x - y)
      - fderiv ℝ (m.scaled δ) (x - y) (b y))‖ ≤ B * (|ν| * Cl + Cd * Cb) := by
    intro y hy
    rw [norm_mul]
    refine mul_le_mul (by simpa using hB y) ?_ (norm_nonneg _) hB0
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul le_rfl (by simpa using hCl (x - y)) (norm_nonneg _) (abs_nonneg _)
    · exact ((fderiv ℝ (m.scaled δ) (x - y)).le_opNorm (b y)).trans
        (mul_le_mul (hCd _) (hCb y hy) (norm_nonneg _) hCd0)
  have hz : ∀ y, y ∉ K → u y * (ν * s113b_lap (m.scaled δ) (x - y)
      - fderiv ℝ (m.scaled δ) (x - y) (b y)) = 0 := fun y hy => by rw [hu0 y hy, zero_mul]
  unfold s113b_gdel
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hH).trans ?_
  exact le_of_eq (by ring)

theorem s113b_mol_measurable (m : s113b_Moll n) (δ : ℝ) {U : ℝ × s113b_E n → ℝ} (hU : Measurable U) :
    Measurable fun z : ℝ × s113b_E n => s113b_mol m δ (fun y => U (z.1, y)) z.2 := by
  have hρ : Measurable (m.scaled δ) := (s113b_scaled_cinf m δ).continuous.measurable
  have hG : Measurable fun p : (ℝ × s113b_E n) × s113b_E n => m.scaled δ (p.1.2 - p.2) * U (p.1.1, p.2) :=
    (hρ.comp (measurable_snd.comp measurable_fst |>.sub measurable_snd)).mul
      (hU.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact (hG.stronglyMeasurable.integral_prod_right').measurable

theorem s113b_gdel_measurable (m : s113b_Moll n) (δ ν : ℝ) {b : s113b_E n → s113b_E n}
    (hb : Continuous b) {U : ℝ × s113b_E n → ℝ} (hU : Measurable U) :
    Measurable fun z : ℝ × s113b_E n => s113b_gdel m δ ν b (fun y => U (z.1, y)) z.2 := by
  have hφ := s113b_scaled_cinf m δ
  have hD : Continuous (fderiv ℝ (m.scaled δ)) := (s113b_scaled_c1 m δ).continuous_fderiv one_ne_zero
  have hL := s113b_lap_cont hφ
  have hH : Continuous fun p : (ℝ × s113b_E n) × s113b_E n =>
      ν * s113b_lap (m.scaled δ) (p.1.2 - p.2) - fderiv ℝ (m.scaled δ) (p.1.2 - p.2) (b p.2) :=
    (continuous_const.mul (hL.comp (continuous_snd.comp continuous_fst |>.sub continuous_snd))).sub
      ((hD.comp (continuous_snd.comp continuous_fst |>.sub continuous_snd)).clm_apply
        (hb.comp continuous_snd))
  have hG : Measurable fun p : (ℝ × s113b_E n) × s113b_E n => U (p.1.1, p.2) *
      (ν * s113b_lap (m.scaled δ) (p.1.2 - p.2) - fderiv ℝ (m.scaled δ) (p.1.2 - p.2) (b p.2)) :=
    (hU.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul hH.measurable
  exact (hG.stronglyMeasurable.integral_prod_right').measurable

end HRS.MS.S113X2B
