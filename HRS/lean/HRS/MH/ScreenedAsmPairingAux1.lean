import HRS.MH.ScreenedP1Aux2
import HRS.MH.ScreenedK3Aux2

/-!
# Helpers for `screened_pairing` at `s = d-1` (ASM-pairing, `ScreenedAsmPairing.lean`)

Measurability of the argument `v` of an `IsGradKernelRep d s i v u` for `0 ≤ s`, without the restriction
`s < d-1` used in `p1_aesm_of_rep`.  The kernel is differentiated only away from the origin: for a test
function `φ` with compact support avoiding `y`, the convolution `g * ∂_iφ (y)` equals `∫ ∂_ig(y-z) φ(z) dz`
(integration by parts on `tsupport φ`, Mathlib `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`),
which is positive when `φ ≥ 0` is supported in `{z_i > k}` and `y_i < k`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- The kernel `g = rieszKernel d s` is differentiable off the origin. -/
lemma q1_diff_kernel {s : ℝ} {w : Euc d} (hw : w ≠ 0) :
    DifferentiableAt ℝ (rieszKernel d s) w := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hu : 0 < ‖w‖ ^ 2 + (0 : ℝ) ^ 2 := by
    rw [zero_pow two_ne_zero, add_zero]
    exact pow_pos hpos 2
  have h := movtr_gEps_hasFDerivAt (d := d) s 0 w hu
  rw [movtr_gEps_zero] at h
  exact h.differentiableAt

/-- Partial derivative of the kernel in the `i`-th coordinate is the `i`-th coordinate of its gradient. -/
lemma q1_fderiv_kernel_single {s : ℝ} (w : Euc d) (i : Fin d) :
    fderiv ℝ (rieszKernel d s) w (EuclideanSpace.single i 1) = rieszKernelGrad d s w i := by
  have h : ∀ v : Euc d, fderiv ℝ (rieszKernel d s) w v = inner ℝ (rieszKernelGrad d s w) v := by
    intro v
    unfold rieszKernelGrad gradient
    rw [InnerProductSpace.toDual_symm_apply]
  rw [h]
  simp [EuclideanSpace.inner_single_right]

/-- `∂_z [g(y - z)]` in the direction `e_i`. -/
lemma q1_fderiv_F {s : ℝ} {y z : Euc d} (hz : y - z ≠ 0) (i : Fin d) :
    fderiv ℝ (fun x => rieszKernel d s (y - x)) z (EuclideanSpace.single i 1) =
      -rieszKernelGrad d s (y - z) i := by
  have h1 : HasFDerivAt (fun x : Euc d => y - x) (-(ContinuousLinearMap.id ℝ (Euc d))) z :=
    (hasFDerivAt_id z).const_sub y
  have h2 : HasFDerivAt (fun x => rieszKernel d s (y - x))
      ((fderiv ℝ (rieszKernel d s) (y - z)).comp (-(ContinuousLinearMap.id ℝ (Euc d)))) z :=
    (q1_diff_kernel (s := s) hz).hasFDerivAt.comp z h1
  rw [h2.fderiv]
  simp [q1_fderiv_kernel_single]

/-- The `i`-th coordinate of the gradient kernel is continuous off the origin. -/
lemma q1_grad_cont {s : ℝ} {w : Euc d} (hw : w ≠ 0) (i : Fin d) :
    ContinuousAt (fun u : Euc d => rieszKernelGrad d s u i) w := by
  have hc : ContinuousAt (fun u : Euc d => (-(movtr_sigma s * ‖u‖ ^ (-s - 2))) * u i) w := by
    apply ContinuousAt.mul
    · apply ContinuousAt.neg
      apply ContinuousAt.mul continuousAt_const
      exact ContinuousAt.rpow_const (continuous_norm.continuousAt) (Or.inl (norm_ne_zero_iff.2 hw))
    · exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.continuousAt
  refine hc.congr (Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hw) fun u hu => ?_)
  have hu' : u ≠ 0 := hu
  simp [movtr_rieszKernelGrad_eq s hu']

/-- The `i`-th gradient kernel is strictly positive where `w_i < 0`. -/
lemma q1_kernel_pos {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) {w : Euc d} (hw : w i < 0) :
    0 < rieszKernelGrad d s w i := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hσ : 0 < movtr_sigma s := by
    unfold movtr_sigma
    split_ifs with h
    · norm_num
    · exact lt_of_le_of_ne hs0 (Ne.symm h)
  have hn : 0 < ‖w‖ ^ (-s - 2) := Real.rpow_pos_of_pos (norm_pos_iff.2 hw0) _
  rw [movtr_rieszKernelGrad_eq s hw0]
  simp only [PiLp.smul_apply, smul_eq_mul]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos (mul_pos hσ hn)) hw

/-- A function continuous on a compact set `K` which contains the support of a continuous `G` gives an
integrable product. -/
lemma q1_int_of_cs {F G : Euc d → ℝ} {K : Set (Euc d)} (hK : IsCompact K) (hGc : Continuous G)
    (hGs : Function.support G ⊆ K) (hF : ContinuousOn F K) :
    Integrable (fun x => F x * G x) := by
  have hsub : Function.support (fun x => F x * G x) ⊆ K := by
    intro x hx
    have hx' : G x ≠ 0 := right_ne_zero_of_mul hx
    exact hGs hx'
  rw [← integrableOn_iff_integrable_of_support_subset hsub]
  exact (hF.mul hGc.continuousOn).integrableOn_compact hK

/-- Continuity of `z ↦ ∂_ig(y - z)` on a set not containing `y`. -/
lemma q1_K_contOn {s : ℝ} (i : Fin d) (y : Euc d) (K : Set (Euc d)) (hK : ∀ z ∈ K, y - z ≠ 0) :
    ContinuousOn (fun z => rieszKernelGrad d s (y - z) i) K := fun z hz =>
  ((q1_grad_cont (s := s) (hK z hz) i).comp
    (continuousAt_const.sub continuousAt_id : ContinuousAt (fun x : Euc d => y - x) z)).continuousWithinAt

/-- A point `y` with `y_i < k` is not in the closed support of a function vanishing below `k`. -/
lemma q1_not_mem_tsupport {φ : Euc d → ℝ} {i : Fin d} {k : ℝ} (hφsupp : ∀ x, φ x ≠ 0 → k < x i)
    {y : Euc d} (hy : y i < k) : y ∉ tsupport φ := by
  intro hmem
  have hsub : tsupport φ ⊆ {x : Euc d | k ≤ x i} :=
    closure_minimal (fun x hx => le_of_lt (hφsupp x hx))
      (isClosed_le continuous_const (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous)
  have h2 : k ≤ y i := hsub hmem
  linarith

/-- Integration by parts: for a compactly supported Schwartz `φ` and `y ∉ tsupport φ`,
`g * ∂_iφ (y) = ∫ ∂_ig(y - z) φ(z) dz`. -/
lemma q1_conv_eq {s : ℝ} {φ : SchwartzMap (Euc d) ℝ} (hφ : HasCompactSupport ⇑φ) (i : Fin d)
    {y : Euc d} (hy : y ∉ tsupport ⇑φ) :
    HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y =
      ∫ z, rieszKernelGrad d s (y - z) i * φ z := by
  have hne : ∀ z ∈ tsupport ⇑φ, y - z ≠ 0 := fun z hz h => hy (by
    rw [sub_eq_zero] at h
    rw [h]
    exact hz)
  have hdiffF : ∀ z ∈ tsupport ⇑φ, DifferentiableAt ℝ (fun x => rieszKernel d s (y - x)) z :=
    fun z hz => (q1_diff_kernel (s := s) (hne z hz)).comp z (differentiableAt_id.const_sub y)
  have hFc : ContinuousOn (fun x => rieszKernel d s (y - x)) (tsupport ⇑φ) := fun z hz =>
    (hdiffF z hz).continuousAt.continuousWithinAt
  have hKc : ContinuousOn (fun x => rieszKernelGrad d s (y - x) i) (tsupport ⇑φ) :=
    q1_K_contOn (s := s) i y _ hne
  have hD := k3_sch_deriv_props φ i
  have hint0 : Integrable (fun x => rieszKernel d s (y - x) * φ x) :=
    q1_int_of_cs (G := ⇑φ) (K := tsupport ⇑φ) hφ.isCompact φ.continuous (subset_tsupport _) hFc
  have hint1 : Integrable (fun x => rieszKernel d s (y - x) *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    apply q1_int_of_cs (G := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) (K := tsupport ⇑φ)
      hφ.isCompact hD.1
    · intro x hx
      have hx' : fderiv ℝ φ x ≠ 0 := by
        intro h0
        apply hx
        simp [h0]
      exact (support_fderiv_subset ℝ) hx'
    · exact hFc
  have hpt : ∀ x, fderiv ℝ (fun z => rieszKernel d s (y - z)) x (EuclideanSpace.single i 1) * φ x =
      -(rieszKernelGrad d s (y - x) i * φ x) := by
    intro x
    by_cases hx : φ x = 0
    · simp [hx]
    · have hxt : x ∈ tsupport ⇑φ := subset_tsupport _ hx
      rw [q1_fderiv_F (hne x hxt) i]
      ring
  have hint2 : Integrable (fun x => fderiv ℝ (fun z => rieszKernel d s (y - z)) x
      (EuclideanSpace.single i 1) * φ x) := by
    have hK0 : Integrable (fun x => rieszKernelGrad d s (y - x) i * φ x) :=
      q1_int_of_cs (G := ⇑φ) (K := tsupport ⇑φ) hφ.isCompact φ.continuous (subset_tsupport _) hKc
    exact (hK0.neg).congr (ae_of_all _ fun x => (hpt x).symm)
  have IBP : ∫ x, rieszKernel d s (y - x) * fderiv ℝ φ x (EuclideanSpace.single i 1) =
      -∫ x, fderiv ℝ (fun z => rieszKernel d s (y - z)) x (EuclideanSpace.single i 1) * φ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint2 hint1 hint0
      (fun z hz => hdiffF z hz) (fun z _ => φ.differentiableAt)
  simp only [HRS.Whole.convFun]
  rw [IBP]
  simp only [hpt, integral_neg, neg_neg]

/-- Positivity of the convolution `∫ ∂_ig(y-z) φ(z) dz` for `φ ≥ 0` supported in `{z_i > k}` and `y_i < k`. -/
lemma q1_conv_pos {s : ℝ} (hs0 : 0 ≤ s) {φ : SchwartzMap (Euc d) ℝ} (hφ : HasCompactSupport ⇑φ)
    (hφnn : ∀ x, 0 ≤ φ x) (i : Fin d) {k : ℝ} (hφsupp : ∀ x, φ x ≠ 0 → k < x i) (x0 : Euc d)
    (hx0 : φ x0 ≠ 0) {y : Euc d} (hy : y i < k) :
    0 < ∫ z, rieszKernelGrad d s (y - z) i * φ z := by
  have hyt : y ∉ tsupport ⇑φ := q1_not_mem_tsupport hφsupp hy
  have hne : ∀ z ∈ tsupport ⇑φ, y - z ≠ 0 := fun z hz h => hyt (by
    rw [sub_eq_zero] at h
    rw [h]
    exact hz)
  have hint : Integrable (fun z => rieszKernelGrad d s (y - z) i * φ z) :=
    q1_int_of_cs (G := ⇑φ) (K := tsupport ⇑φ) hφ.isCompact φ.continuous (subset_tsupport _)
      (q1_K_contOn (s := s) i y _ hne)
  have hnn : 0 ≤ fun z => rieszKernelGrad d s (y - z) i * φ z := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    · have hzk : k < z i := hφsupp z hz
      have hneg : (y - z) i < 0 := by
        rw [PiLp.sub_apply]
        linarith
      have hK := q1_kernel_pos hs0 i hneg
      exact mul_nonneg hK.le (hφnn z)
  have hopen : IsOpen {x : Euc d | φ x ≠ 0} := isOpen_ne_fun φ.continuous continuous_const
  have hmpos : 0 < volume {x : Euc d | φ x ≠ 0} := hopen.measure_pos volume ⟨x0, hx0⟩
  have hsub : {x : Euc d | φ x ≠ 0} ⊆ Function.support (fun z => rieszKernelGrad d s (y - z) i * φ z) := by
    intro z hz
    have hz' : φ z ≠ 0 := hz
    have hzk : k < z i := hφsupp z hz'
    have hneg : (y - z) i < 0 := by
      rw [PiLp.sub_apply]
      linarith
    exact mul_ne_zero (q1_kernel_pos hs0 i hneg).ne' hz'
  exact (integral_pos_iff_support_of_nonneg hnn hint).2 (lt_of_lt_of_le hmpos (measure_mono hsub))

/-- A compactly supported bump, nonnegative, supported in `{x_i > k}` and nonzero somewhere. -/
lemma q1_bump (k : ℝ) (i : Fin d) :
    ∃ φ : SchwartzMap (Euc d) ℝ, HasCompactSupport ⇑φ ∧ (∀ x, 0 ≤ φ x) ∧
      (∀ x, φ x ≠ 0 → k < x i) ∧ ∃ x0 : Euc d, φ x0 ≠ 0 := by
  let c : ContDiffBump (EuclideanSpace.single i (k + 1) : Euc d) :=
    ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hg : ContDiff ℝ ∞ (c : Euc d → ℝ) := c.contDiff
  have hgc : HasCompactSupport (c : Euc d → ℝ) := c.hasCompactSupport
  obtain ⟨φ, hφ⟩ : ∃ φ : SchwartzMap (Euc d) ℝ, ⇑φ = c := ⟨hgc.toSchwartzMap hg, rfl⟩
  have hφx : ∀ x, φ x = c x := fun x => congrFun hφ x
  refine ⟨φ, ?_, fun x => ?_, fun x hx => ?_, EuclideanSpace.single i (k + 1), ?_⟩
  · rw [hφ]
    exact hgc
  · rw [hφx]
    exact c.nonneg
  · rw [hφx] at hx
    have hsupp : x ∈ Function.support (c : Euc d → ℝ) := hx
    have hr : c.rOut = 1 / 2 := rfl
    rw [c.support_eq, Metric.mem_ball, dist_eq_norm, hr] at hsupp
    have h1 : ‖(x - EuclideanSpace.single i (k + 1)) i‖ ≤ ‖x - EuclideanSpace.single i (k + 1)‖ :=
      PiLp.norm_apply_le _ i
    have h2 : (x - EuclideanSpace.single i (k + 1)) i = x i - (k + 1) := by
      simp [EuclideanSpace.single_apply]
    rw [h2, Real.norm_eq_abs] at h1
    have h3 := abs_lt.mp (lt_of_le_of_lt h1 hsupp)
    linarith [h3.1]
  · rw [hφx]
    have hmem : (EuclideanSpace.single i (k + 1) : Euc d) ∈
        Metric.closedBall (EuclideanSpace.single i (k + 1) : Euc d) c.rIn :=
      Metric.mem_closedBall_self c.rIn_pos.le
    rw [c.one_of_mem_closedBall hmem]
    norm_num

/-- The covering argument: `v` is a.e.-strongly measurable when `IsGradKernelRep d s i v u`, `s ≥ 0`. -/
lemma q1_aesm_of_rep {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) {v u : Euc d → ℝ}
    (h : IsGradKernelRep d s i v u) : AEStronglyMeasurable v volume := by
  have key : ∀ k : ℕ, AEStronglyMeasurable v (volume.restrict {y : Euc d | y i < k}) := by
    intro k
    obtain ⟨φ, hφcs, hφnn, hφsupp, x0, hx0⟩ := q1_bump (d := d) (k : ℝ) i
    have hUo : IsOpen {y : Euc d | y i < k} :=
      isOpen_lt (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous continuous_const
    have hUm : MeasurableSet {y : Euc d | y i < k} := hUo.measurableSet
    have hGm : AEStronglyMeasurable (fun y : Euc d => ∫ z, rieszKernelGrad d s (y - z) i * φ z) volume := by
      have hF : AEStronglyMeasurable (fun p : Euc d × Euc d => rieszKernelGrad d s (p.1 - p.2) i * φ p.2)
          (volume.prod volume) := by
        apply Measurable.aestronglyMeasurable
        exact ((k4_comp_measurable s i).comp (measurable_fst.sub measurable_snd)).mul
          (φ.continuous.measurable.comp measurable_snd)
      exact hF.integral_prod_right'
    have hΘae : (fun y : Euc d => HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y) =ᵐ[volume.restrict {y : Euc d | y i < k}]
        (fun y : Euc d => ∫ z, rieszKernelGrad d s (y - z) i * φ z) := by
      filter_upwards [ae_restrict_mem hUm] with y hy
      exact q1_conv_eq hφcs i (q1_not_mem_tsupport hφsupp hy)
    have hΘpos : ∀ y ∈ {y : Euc d | y i < k}, HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y ≠ 0 := by
      intro y hy
      have hy' : y i < k := hy
      rw [q1_conv_eq hφcs i (q1_not_mem_tsupport hφsupp hy')]
      exact (q1_conv_pos hs0 hφcs hφnn i hφsupp x0 hx0 hy').ne'
    have hΘaesm : AEStronglyMeasurable (fun y : Euc d => HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y)
        (volume.restrict {y : Euc d | y i < k}) :=
      hGm.restrict.congr hΘae.symm
    have hvΘ : Integrable (fun y => v y * HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y) volume := (h φ).2.1
    have hinvm : AEStronglyMeasurable (fun y : Euc d => (HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y)⁻¹)
        (volume.restrict {y : Euc d | y i < k}) :=
      (hΘaesm.aemeasurable.inv).aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun y : Euc d => v y * HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y * (HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y)⁻¹)
        (volume.restrict {y : Euc d | y i < k}) :=
      hvΘ.aestronglyMeasurable.restrict.mul hinvm
    refine hprod.congr ?_
    filter_upwards [ae_restrict_mem hUm] with y hy
    have hy' : y i < k := hy
    exact mul_inv_cancel_right₀ (hΘpos y (by exact hy)) (v y)
  have hU : (⋃ k : ℕ, {y : Euc d | y i < k}) = univ := by
    ext y
    simp only [mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (y i)
    exact ⟨n, hn⟩
  have hall := (aestronglyMeasurable_iUnion_iff (μ := volume) (f := v)
    (s := fun k : ℕ => {y : Euc d | y i < k})).2 key
  rw [hU, Measure.restrict_univ] at hall
  exact hall

end HRS.MH.Screened
