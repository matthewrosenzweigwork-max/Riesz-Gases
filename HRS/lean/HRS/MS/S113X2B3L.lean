import HRS.MS.S113X2B3

/-!
# S11.3 X2 part B (worker S11Z3), Lebesgue-point convergence of mollifications and the Friedrichs commutator
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HRS.MS.S113X2B

variable {n : ℕ}

/-- The scaled kernel `κ_δ(z) = δ^{-n} κ(z/δ)`. -/
def s113b_kd (κ : s113b_E n → ℝ) (δ : ℝ) (z : s113b_E n) : ℝ := (δ ^ n)⁻¹ * κ (δ⁻¹ • z)

lemma s113b_scaled_eq (m : s113b_Moll n) (δ : ℝ) : m.scaled δ = s113b_kd m.ρ δ := rfl

/-- The volume of the unit ball. -/
def s113b_V (n : ℕ) : ℝ := (volume : Measure (s113b_E n)).real (Metric.ball 0 1)

lemma s113b_V_nonneg : 0 ≤ s113b_V n := measureReal_nonneg

lemma s113b_real_ball (x : s113b_E n) {δ : ℝ} (hδ : 0 ≤ δ) :
    (volume : Measure (s113b_E n)).real (Metric.closedBall x δ) = δ ^ n * s113b_V n := by
  rw [Measure.addHaar_real_closedBall _ x hδ, finrank_euclideanSpace_fin]
  rfl

lemma s113b_integrable_of_ball {x : s113b_E n} {δ c : ℝ} {f : s113b_E n → ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hb : ∀ y, |f y| ≤ c * (Metric.closedBall x δ).indicator (fun _ => (1 : ℝ)) y) :
    Integrable f (volume : Measure (s113b_E n)) := by
  have hg : Integrable (fun y => c * (Metric.closedBall x δ).indicator (fun _ => (1 : ℝ)) y) volume :=
    ((integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const measure_closedBall_lt_top.ne)).const_mul _
  exact hg.mono' hf (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hb y)

lemma s113b_ball_int_bound {x : s113b_E n} {δ M : ℝ} (hδ : 0 < δ) (f : s113b_E n → ℝ)
    (hf : ∀ y, |f y| ≤ (δ ^ n)⁻¹ * M * (Metric.closedBall x δ).indicator (fun _ => (1 : ℝ)) y) :
    |∫ y, f y| ≤ M * s113b_V n := by
  have hg : Integrable (fun y => (δ ^ n)⁻¹ * M * (Metric.closedBall x δ).indicator (fun _ => (1 : ℝ)) y) volume :=
    ((integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const measure_closedBall_lt_top.ne)).const_mul _
  have h1 := norm_integral_le_of_norm_le (f := f) hg (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hf y)
  rw [integral_const_mul, integral_indicator_const _ Metric.isClosed_closedBall.measurableSet,
    s113b_real_ball x hδ.le] at h1
  have hp : (δ ^ n) ≠ 0 := pow_ne_zero _ hδ.ne'
  calc |∫ y, f y| = ‖∫ y, f y‖ := (Real.norm_eq_abs _).symm
    _ ≤ _ := h1
    _ = M * s113b_V n := by simp only [smul_eq_mul, mul_one]; field_simp

lemma s113b_kd_zero {κ : s113b_E n → ℝ} (hκ0 : ∀ z, 1 < ‖z‖ → κ z = 0) {δ : ℝ} (hδ : 0 < δ)
    {z : s113b_E n} (hz : δ < ‖z‖) : s113b_kd κ δ z = 0 := by
  unfold s113b_kd
  rw [hκ0 _ ?_, mul_zero]
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ, lt_inv_mul_iff₀ hδ]
  simpa using hz

lemma s113b_kd_bound {κ : s113b_E n → ℝ} {M : ℝ} (hκM : ∀ z, |κ z| ≤ M)
    (hκ0 : ∀ z, 1 < ‖z‖ → κ z = 0) {δ : ℝ} (hδ : 0 < δ) (x y : s113b_E n) :
    |s113b_kd κ δ (x - y)| ≤ (δ ^ n)⁻¹ * M * (Metric.closedBall x δ).indicator (fun _ => (1 : ℝ)) y := by
  by_cases hy : y ∈ Metric.closedBall x δ
  · rw [indicator_of_mem hy, mul_one, s113b_kd, abs_mul, abs_of_pos (inv_pos.2 (pow_pos hδ n))]
    exact mul_le_mul_of_nonneg_left (hκM _) (inv_pos.2 (pow_pos hδ n)).le
  · have : δ < ‖x - y‖ := by
      rw [Metric.mem_closedBall, not_le, dist_eq_norm, norm_sub_rev] at hy
      exact hy
    rw [s113b_kd_zero hκ0 hδ this]
    simp [indicator_of_notMem hy]

lemma s113b_kd_integral {κ : s113b_E n → ℝ} {δ : ℝ} (hδ : 0 < δ) (x : s113b_E n) :
    ∫ y, s113b_kd κ δ (x - y) = ∫ z, κ z := by
  rw [integral_sub_left_eq_self (fun z => s113b_kd κ δ z) volume x]
  unfold s113b_kd
  rw [integral_const_mul, Measure.integral_comp_smul (volume : Measure (s113b_E n)) κ δ⁻¹,
    finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos hδ n), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (pow_pos hδ n).ne', one_mul]

lemma s113b_loc_int {u : s113b_E n → ℝ} {B : ℝ} (hu : Measurable u) (hB : ∀ y, |u y| ≤ B) :
    LocallyIntegrable u (volume : Measure (s113b_E n)) := by
  rw [locallyIntegrable_iff]
  intro k hk
  exact Measure.integrableOn_of_bounded (M := B) hk.measure_lt_top.ne hu.aestronglyMeasurable
    (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hB y)

lemma s113b_leb_ae {u : s113b_E n → ℝ} {B : ℝ} (hu : Measurable u) (hB : ∀ y, |u y| ≤ B) :
    ∀ᵐ x ∂(volume : Measure (s113b_E n)),
      Tendsto (fun δ : ℝ => ⨍ y in Metric.closedBall x δ, ‖u y - u x‖) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure (s113b_E n))
    (s113b_loc_int hu hB) 1] with x hx
  exact hx (fun _ => x) id tendsto_id (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : 0 < δ := hδ
    exact Metric.mem_closedBall_self (by simpa using hδ'.le))

lemma s113b_kd_measurable {κ : s113b_E n → ℝ} (hκm : Measurable κ) (δ : ℝ) (x : s113b_E n) :
    Measurable (fun y => s113b_kd κ δ (x - y)) := by
  unfold s113b_kd
  have : Measurable (fun y : s113b_E n => δ⁻¹ • (x - y)) := by fun_prop
  exact measurable_const.mul (hκm.comp this)

lemma s113b_kd_mul_integrable {κ : s113b_E n → ℝ} {M : ℝ} (hκm : Measurable κ) (hκM : ∀ z, |κ z| ≤ M)
    (hκ0 : ∀ z, 1 < ‖z‖ → κ z = 0) {u : s113b_E n → ℝ} {B : ℝ} (hu : Measurable u)
    (hB : ∀ y, |u y| ≤ B) {δ : ℝ} (hδ : 0 < δ) (x : s113b_E n) :
    Integrable (fun y => s113b_kd κ δ (x - y) * u y) (volume : Measure (s113b_E n)) := by
  refine s113b_integrable_of_ball (x := x) (δ := δ) (c := (δ ^ n)⁻¹ * M * B)
    ((s113b_kd_measurable hκm δ x).mul hu).aestronglyMeasurable (fun y => ?_)
  rw [abs_mul]
  have h1 := s113b_kd_bound hκM hκ0 hδ x y
  have h2 := hB y
  calc _ ≤ ((δ ^ n)⁻¹ * M * (Metric.closedBall x δ).indicator (fun _ => (1 : ℝ)) y) * B :=
        mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
    _ = _ := by ring

theorem s113b_kern_tendsto {κ : s113b_E n → ℝ} {M : ℝ} (hκm : Measurable κ) (hκM : ∀ z, |κ z| ≤ M)
    (hκ0 : ∀ z, 1 < ‖z‖ → κ z = 0) {u : s113b_E n → ℝ} {B : ℝ} (hu : Measurable u)
    (hB : ∀ y, |u y| ≤ B) {x : s113b_E n}
    (hx : Tendsto (fun δ : ℝ => ⨍ y in Metric.closedBall x δ, ‖u y - u x‖) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun δ => ∫ y, s113b_kd κ δ (x - y) * u y) (𝓝[>] 0) (𝓝 ((∫ z, κ z) * u x)) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hκM 0)
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ (by simpa using hx.const_mul (M * s113b_V n))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ : 0 < δ := hδ
  have hkm := s113b_kd_measurable hκm δ x
  have hki : Integrable (fun y => s113b_kd κ δ (x - y)) volume :=
    s113b_integrable_of_ball hkm.aestronglyMeasurable (fun y => s113b_kd_bound hκM hκ0 hδ x y)
  have hkui := s113b_kd_mul_integrable hκm hκM hκ0 hu hB hδ x
  have hd : (∫ y, s113b_kd κ δ (x - y) * u y) - (∫ z, κ z) * u x
      = ∫ y, s113b_kd κ δ (x - y) * (u y - u x) := by
    simp only [mul_sub]
    rw [integral_sub hkui (hki.mul_const _), integral_mul_const, s113b_kd_integral hδ]
  rw [Real.dist_eq, hd]
  -- bound by the average
  have hui : IntegrableOn (fun y => ‖u y - u x‖) (Metric.closedBall x δ) volume := by
    refine Measure.integrableOn_of_bounded (M := 2 * B) measure_closedBall_lt_top.ne
      (hu.sub measurable_const).norm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [norm_norm, Real.norm_eq_abs]
    have := abs_sub (u y) (u x)
    have := hB y; have := hB x
    linarith [abs_sub (u y) (u x), hB y, hB x]
  have hg : Integrable ((Metric.closedBall x δ).indicator (fun y => (δ ^ n)⁻¹ * M * ‖u y - u x‖)) volume :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2 (hui.const_mul _)
  have h1 := norm_integral_le_of_norm_le hg (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hy : y ∈ Metric.closedBall x δ
    · rw [indicator_of_mem hy]
      have h1 := s113b_kd_bound hκM hκ0 hδ x y
      rw [indicator_of_mem hy, mul_one] at h1
      rw [Real.norm_eq_abs] at *
      exact mul_le_mul h1 le_rfl (abs_nonneg _) (mul_nonneg (inv_pos.2 (pow_pos hδ n)).le hM0)
    · have : δ < ‖x - y‖ := by
        rw [Metric.mem_closedBall, not_le, dist_eq_norm, norm_sub_rev] at hy
        exact hy
      rw [indicator_of_notMem hy, s113b_kd_zero hκ0 hδ this]
      simp)
  rw [integral_indicator Metric.isClosed_closedBall.measurableSet, integral_const_mul] at h1
  have h2 := measure_smul_setAverage (μ := volume) (fun y => ‖u y - u x‖)
    (measure_closedBall_lt_top (x := x) (r := δ)).ne
  rw [measureReal_def] at h2
  calc |∫ y, s113b_kd κ δ (x - y) * (u y - u x)|
      = ‖∫ y, s113b_kd κ δ (x - y) * (u y - u x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ _ := h1
    _ = M * s113b_V n * ⨍ y in Metric.closedBall x δ, ‖u y - u x‖ := by
        have h3 : ∫ y in Metric.closedBall x δ, ‖u y - u x‖
            = (δ ^ n * s113b_V n) * ⨍ y in Metric.closedBall x δ, ‖u y - u x‖ := by
          rw [← h2, ← measureReal_def, s113b_real_ball x hδ.le, smul_eq_mul]
        rw [h3]
        have hp : (δ ^ n) ≠ 0 := pow_ne_zero _ hδ.ne'
        field_simp


/-! ### Basic facts on the mollifier -/

lemma s113b_hcs (m : s113b_Moll n) : HasCompactSupport m.ρ :=
  IsCompact.of_isClosed_subset (isCompact_closedBall 0 1) (isClosed_tsupport _) m.supp

lemma s113b_not_tsupport (m : s113b_Moll n) {w : s113b_E n} (hw : 1 < ‖w‖) : w ∉ tsupport m.ρ := by
  intro h
  have := m.supp h
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

lemma s113b_rho_zero (m : s113b_Moll n) {w : s113b_E n} (hw : 1 < ‖w‖) : m.ρ w = 0 :=
  image_eq_zero_of_notMem_tsupport (s113b_not_tsupport m hw)

lemma s113b_drho_zero (m : s113b_Moll n) {w : s113b_E n} (hw : 1 < ‖w‖) : fderiv ℝ m.ρ w = 0 :=
  fderiv_of_notMem_tsupport (𝕜 := ℝ) (s113b_not_tsupport m hw)

lemma s113b_rho_cont (m : s113b_Moll n) : Continuous m.ρ := m.smooth.continuous

lemma s113b_drho_cont (m : s113b_Moll n) : Continuous (fderiv ℝ m.ρ) :=
  m.smooth.continuous_fderiv (by simp)

lemma s113b_zero_out_bdd {G : Type*} [NormedAddCommGroup G] {f : s113b_E n → G} (hc : Continuous f)
    (h0 : ∀ w, 1 < ‖w‖ → f w = 0) : ∃ C, 0 ≤ C ∧ ∀ w, ‖f w‖ ≤ C := by
  have hcs : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_closedBall (0 : s113b_E n) 1) (fun w hw => h0 w (by simpa using hw))
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨max C 0, le_max_right _ _, fun w => (hC w).trans (le_max_left _ _)⟩

lemma s113b_zero_out_int {f : s113b_E n → ℝ} (hc : Continuous f) (h0 : ∀ w, 1 < ‖w‖ → f w = 0) :
    Integrable f (volume : Measure (s113b_E n)) :=
  hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall (0 : s113b_E n) 1) (fun w hw => h0 w (by simpa using hw)))

/-- Mollification converges almost everywhere. -/
theorem s113b_mol_tendsto_ae (m : s113b_Moll n) {u : s113b_E n → ℝ} {B : ℝ} {K : Set (s113b_E n)}
    (hm : Measurable u) (hB : ∀ y, |u y| ≤ B) (hK : IsCompact K) (hKu : ∀ y, y ∉ K → u y = 0) :
    ∀ᵐ x ∂(volume : Measure (s113b_E n)),
      Tendsto (fun δ => s113b_mol m δ u x) (nhdsWithin 0 (Ioi 0)) (nhds (u x)) := by
  obtain ⟨C, -, hC⟩ := s113b_zero_out_bdd (s113b_rho_cont m) (fun w hw => s113b_rho_zero m hw)
  filter_upwards [s113b_leb_ae hm hB] with x hx
  have := s113b_kern_tendsto (M := C) (s113b_rho_cont m).measurable
    (fun z => by simpa [Real.norm_eq_abs] using hC z) (fun z hz => s113b_rho_zero m hz) hm hB hx
  rw [m.integral_one, one_mul] at this
  exact this

/-! ### Derivative of the scaled mollifier -/

lemma s113b_fderiv_scaled (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) (z v : s113b_E n) :
    fderiv ℝ (m.scaled δ) z v = (δ ^ n)⁻¹ * δ⁻¹ * fderiv ℝ m.ρ (δ⁻¹ • z) v := by
  have hρ : DifferentiableAt ℝ m.ρ (δ⁻¹ • z) :=
    (m.smooth.differentiable (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun z : s113b_E n => δ⁻¹ • z) (δ⁻¹ • ContinuousLinearMap.id ℝ (s113b_E n)) z :=
    (hasFDerivAt_id z).const_smul δ⁻¹
  have h3 := (hρ.hasFDerivAt.comp z h1).const_mul ((δ ^ n)⁻¹)
  have h4 : HasFDerivAt (m.scaled δ) _ z := h3
  rw [h4.fderiv]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

lemma s113b_dscaled_bound (m : s113b_Moll n) {C : ℝ} (hC : ∀ w, ‖fderiv ℝ m.ρ w‖ ≤ C) {δ : ℝ}
    (hδ : 0 < δ) (x y e : s113b_E n) :
    |fderiv ℝ (m.scaled δ) (x - y) e| ≤
      (δ ^ n)⁻¹ * (δ⁻¹ * C * ‖e‖) * (Metric.closedBall x δ).indicator (fun _ => (1 : ℝ)) y := by
  by_cases hy : y ∈ Metric.closedBall x δ
  · rw [indicator_of_mem hy, mul_one, s113b_fderiv_scaled m hδ, abs_mul, abs_mul,
      abs_of_pos (inv_pos.2 (pow_pos hδ n)), abs_of_pos (inv_pos.2 hδ), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 (pow_pos hδ n)).le
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hδ).le
    calc _ ≤ ‖fderiv ℝ m.ρ (δ⁻¹ • (x - y)) e‖ := (Real.norm_eq_abs _).symm.le
      _ ≤ ‖fderiv ℝ m.ρ (δ⁻¹ • (x - y))‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖e‖ := mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · have : δ < ‖x - y‖ := by
      rw [Metric.mem_closedBall, not_le, dist_eq_norm, norm_sub_rev] at hy
      exact hy
    have h1 : 1 < ‖δ⁻¹ • (x - y)‖ := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ, lt_inv_mul_iff₀ hδ]
      simpa using this
    rw [s113b_fderiv_scaled m hδ, s113b_drho_zero m h1]
    simp [indicator_of_notMem hy]

/-! ### Integration by parts for the kernel `Dρ(w)(A w)` -/

lemma s113b_expand (L : s113b_E n →L[ℝ] ℝ) (w : s113b_E n) :
    L w = ∑ k, w k * L (EuclideanSpace.single k 1) := by
  have : w = ∑ k, w k • EuclideanSpace.single k (1 : ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]

lemma s113b_ibp (m : s113b_Moll n) (j k : Fin n) :
    ∫ w, w k * fderiv ℝ m.ρ w (EuclideanSpace.single j 1) = - (if k = j then (1 : ℝ) else 0) := by
  have hf : ∀ w, fderiv ℝ (fun w : s113b_E n => w k) w (EuclideanSpace.single j 1)
      = if k = j then (1 : ℝ) else 0 := by
    intro w
    have := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) k).fderiv (x := w)
    show (fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) k) w) _ = _
    rw [this]
    simp [eq_comm]
  have hcont : Continuous (fun w : s113b_E n => w k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) k).continuous
  have hdiff : ∀ w, DifferentiableAt ℝ (fun w : s113b_E n => w k) w :=
    fun w => (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) k).differentiableAt
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (s113b_E n)))
    (f := fun w : s113b_E n => w k) (g := m.ρ) (v := EuclideanSpace.single j 1)
    (by simp only [hf]
        exact (s113b_zero_out_int (s113b_rho_cont m) (fun w hw => s113b_rho_zero m hw)).const_mul _)
    (s113b_zero_out_int (hcont.mul ((s113b_drho_cont m).clm_apply continuous_const))
      (fun w hw => by simp [s113b_drho_zero m hw]))
    (s113b_zero_out_int (hcont.mul (s113b_rho_cont m)) (fun w hw => by simp [s113b_rho_zero m hw]))
    (fun w _ => hdiff w) (fun w _ => (m.smooth.differentiable (by simp)).differentiableAt)
  rw [this]
  simp only [hf]
  by_cases hkj : k = j
  · simp [hkj, m.integral_one]
  · simp [hkj]


/-- The kernel `w ↦ Dρ(w)(A w)`. -/
def s113b_kA (m : s113b_Moll n) (A : s113b_E n →L[ℝ] s113b_E n) (w : s113b_E n) : ℝ :=
  fderiv ℝ m.ρ w (A w)

lemma s113b_kA_cont (m : s113b_Moll n) (A : s113b_E n →L[ℝ] s113b_E n) : Continuous (s113b_kA m A) :=
  (s113b_drho_cont m).clm_apply A.continuous

lemma s113b_kA_zero (m : s113b_Moll n) (A : s113b_E n →L[ℝ] s113b_E n) {w : s113b_E n} (hw : 1 < ‖w‖) :
    s113b_kA m A w = 0 := by
  simp [s113b_kA, s113b_drho_zero m hw]

lemma s113b_int_kA (m : s113b_Moll n) (A : s113b_E n →L[ℝ] s113b_E n) :
    ∫ w, s113b_kA m A w = - ∑ k, A (EuclideanSpace.single k 1) k := by
  have h1 : ∀ w, s113b_kA m A w = ∑ j, ∑ k, A (EuclideanSpace.single k 1) j *
      (w k * fderiv ℝ m.ρ w (EuclideanSpace.single j 1)) := by
    intro w
    unfold s113b_kA
    rw [s113b_expand (fderiv ℝ m.ρ w) (A w)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := s113b_expand ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) j).comp A) w
    simp only [ContinuousLinearMap.comp_apply] at this
    have h2 : (A w) j = ∑ k, w k * A (EuclideanSpace.single k 1) j := this
    rw [h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hint : ∀ j k : Fin n, Integrable (fun w : s113b_E n => A (EuclideanSpace.single k 1) j *
      (w k * fderiv ℝ m.ρ w (EuclideanSpace.single j 1))) volume := by
    intro j k
    refine Integrable.const_mul (s113b_zero_out_int ?_ (fun w hw => by simp [s113b_drho_zero m hw])) _
    exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) k).continuous.mul
      ((s113b_drho_cont m).clm_apply continuous_const)
  simp_rw [h1]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
  simp_rw [integral_finsetSum _ (fun k _ => hint _ k), integral_const_mul, s113b_ibp m]
  simp only [mul_neg, mul_ite, mul_one, mul_zero, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp

/-! ### Taylor and Lipschitz bounds for a `C²` field -/

lemma s113b_taylor {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 2 b) (x : s113b_E n) :
    ∃ L r : ℝ, 0 < r ∧ ∀ y, ‖y - x‖ ≤ r →
      ‖b y - b x - fderiv ℝ b x (y - x)‖ ≤ L * ‖y - x‖ ^ 2 := by
  have hD : ContDiff ℝ 1 (fderiv ℝ b) := hb.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, t, ht, hLip⟩ := hD.contDiffAt.exists_lipschitzOnWith (x := x)
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨K, r / 2, by positivity, fun y hy => ?_⟩
  have hdb : Differentiable ℝ b := hb.differentiable (by norm_num)
  set s := ‖y - x‖ with hs
  have hg : ∀ z, HasFDerivAt (fun z => b z - fderiv ℝ b x z) (fderiv ℝ b z - fderiv ℝ b x) z :=
    fun z => (hdb z).hasFDerivAt.sub (fderiv ℝ b x).hasFDerivAt
  have hbd : ∀ z ∈ Metric.closedBall x s, ‖fderiv ℝ (fun z => b z - fderiv ℝ b x z) z‖ ≤ K * s := by
    intro z hz
    rw [(hg z).fderiv]
    have hzt : z ∈ t := hrt (by
      rw [Metric.mem_ball]
      have := Metric.mem_closedBall.1 hz
      linarith)
    have hxt : x ∈ t := hrt (Metric.mem_ball_self hr)
    have h1 := hLip.dist_le_mul z hzt x hxt
    rw [dist_eq_norm, dist_eq_norm] at h1
    refine h1.trans ?_
    have := Metric.mem_closedBall.1 hz
    rw [dist_eq_norm] at this
    exact mul_le_mul_of_nonneg_left this K.2
  have hys : y ∈ Metric.closedBall x s := by simp [Metric.mem_closedBall, dist_eq_norm, s]
  have := (convex_closedBall x s).norm_image_sub_le_of_norm_fderiv_le (f := fun z => b z - fderiv ℝ b x z)
    (fun z _ => (hg z).differentiableAt) hbd (Metric.mem_closedBall_self (norm_nonneg _)) hys
  calc _ = ‖(b y - fderiv ℝ b x y) - (b x - fderiv ℝ b x x)‖ := by rw [map_sub]; congr 1; abel
    _ ≤ K * s * ‖y - x‖ := this
    _ = K * s ^ 2 := by rw [← hs]; ring

lemma s113b_lip {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 2 b) (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ x ∈ Metric.closedBall (0 : s113b_E n) R, ‖fderiv ℝ b x‖ ≤ L) ∧
      ∀ x ∈ Metric.closedBall (0 : s113b_E n) R, ∀ y ∈ Metric.closedBall (0 : s113b_E n) R,
        ‖b x - b y‖ ≤ L * ‖x - y‖ := by
  have hc : Continuous (fderiv ℝ b) := hb.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : s113b_E n) R).exists_bound_of_continuousOn hc.continuousOn
  have hL : ∀ x ∈ Metric.closedBall (0 : s113b_E n) R, ‖fderiv ℝ b x‖ ≤ max C 0 :=
    fun x hx => (hC x hx).trans (le_max_left _ _)
  refine ⟨max C 0, le_max_right _ _, hL, fun x hx y hy => ?_⟩
  have := (convex_closedBall (0 : s113b_E n) R).norm_image_sub_le_of_norm_fderiv_le (f := b)
    (fun z _ => (hb.differentiable (by norm_num)) z) hL hy hx
  exact this

lemma s113b_div_eq {b : s113b_E n → s113b_E n} {x : s113b_E n} (hb : DifferentiableAt ℝ b x) :
    s113b_div b x = ∑ k, fderiv ℝ b x (EuclideanSpace.single k 1) k := by
  unfold s113b_div
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) k).hasFDerivAt.comp x hb.hasFDerivAt
  have h2 : fderiv ℝ (fun y => b y k) x = (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) k).comp (fderiv ℝ b x) :=
    h.fderiv
  rw [h2]
  rfl

lemma s113b_div_bound {b : s113b_E n → s113b_E n} {x : s113b_E n} (hb : DifferentiableAt ℝ b x) :
    |s113b_div b x| ≤ n * ‖fderiv ℝ b x‖ := by
  rw [s113b_div_eq hb]
  calc |∑ k, fderiv ℝ b x (EuclideanSpace.single k 1) k|
      ≤ ∑ k : Fin n, |fderiv ℝ b x (EuclideanSpace.single k 1) k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, ‖fderiv ℝ b x‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc |fderiv ℝ b x (EuclideanSpace.single k 1) k|
            = ‖fderiv ℝ b x (EuclideanSpace.single k 1) k‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ b x (EuclideanSpace.single k 1)‖ := PiLp.norm_apply_le _ _
          _ ≤ ‖fderiv ℝ b x‖ * ‖(EuclideanSpace.single k (1 : ℝ) : s113b_E n)‖ := ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ b x‖ := by simp
    _ = n * ‖fderiv ℝ b x‖ := by simp


/-! ### The commutator -/

lemma s113b_far {δ : ℝ} (hδ : 0 < δ) {z : s113b_E n} (hz : δ < ‖z‖) : 1 < ‖δ⁻¹ • z‖ := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ, lt_inv_mul_iff₀ hδ]
  simpa using hz

theorem s113b_comm_eq_zero (m : s113b_Moll n) (b : s113b_E n → s113b_E n) {u : s113b_E n → ℝ}
    {K : Set (s113b_E n)} (hKu : ∀ y, y ∉ K → u y = 0) {δ : ℝ} (hδ : 0 < δ) (x : s113b_E n)
    (hx : ∀ y ∈ K, δ < dist x y) : s113b_comm m δ b u x = 0 := by
  unfold s113b_comm
  have : ∀ y, u y * (fderiv ℝ (m.scaled δ) (x - y) (b x - b y) + s113b_div b x * m.scaled δ (x - y)) = 0 := by
    intro y
    by_cases hy : y ∈ K
    · have h : 1 < ‖δ⁻¹ • (x - y)‖ := s113b_far hδ (by simpa [dist_eq_norm] using hx y hy)
      rw [s113b_fderiv_scaled m hδ, s113b_drho_zero m h]
      simp [s113b_Moll.scaled, s113b_rho_zero m h]
    · rw [hKu y hy, zero_mul]
  exact (integral_congr_ae (ae_of_all _ this)).trans (integral_zero _ _)

theorem s113b_comm_bound (m : s113b_Moll n) {b : s113b_E n → s113b_E n} {K : Set (s113b_E n)}
    (hb : ContDiff ℝ 2 b) (hK : IsCompact K) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ ∀ (B : ℝ) (u : s113b_E n → ℝ), Measurable u → (∀ y, |u y| ≤ B) →
      (∀ y, y ∉ K → u y = 0) → ∀ δ ∈ Ioo 0 δ0, ∀ x, |s113b_comm m δ b u x| ≤ C * B := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : s113b_E n)
  obtain ⟨L, hL0, hLD, hLip⟩ := s113b_lip hb (R + 1)
  obtain ⟨Cρ, hCρ0, hCρ⟩ := s113b_zero_out_bdd (s113b_rho_cont m) (fun w hw => s113b_rho_zero m hw)
  obtain ⟨Cd, hCd0, hCd⟩ := s113b_zero_out_bdd (s113b_drho_cont m) (fun w hw => s113b_drho_zero m hw)
  refine ⟨1, (Cd * L + n * L * Cρ) * s113b_V n, one_pos, fun B u hu hB hKu δ hδ x => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have key : ∀ y, |u y * (fderiv ℝ (m.scaled δ) (x - y) (b x - b y) + s113b_div b x * m.scaled δ (x - y))|
      ≤ (δ ^ n)⁻¹ * (B * (Cd * L + n * L * Cρ)) * (Metric.closedBall x δ).indicator (fun _ => (1 : ℝ)) y := by
    intro y
    have hp : 0 < (δ ^ n)⁻¹ := inv_pos.2 (pow_pos hδ0 n)
    have hfac : 0 ≤ Cd * L + n * L * Cρ := by positivity
    by_cases hyK : y ∈ K
    swap
    · rw [hKu y hyK, zero_mul, abs_zero]
      have : 0 ≤ (Metric.closedBall x δ).indicator (fun _ => (1 : ℝ)) y := indicator_nonneg (fun _ _ => zero_le_one) _
      positivity
    have hd := s113b_dscaled_bound m (fun w => by simpa using hCd w) hδ0 x y (b x - b y)
    have hs := s113b_kd_bound (κ := m.ρ) (M := Cρ) (fun z => by simpa [Real.norm_eq_abs] using hCρ z)
      (fun z hz => s113b_rho_zero m hz) hδ0 x y
    by_cases hyb : y ∈ Metric.closedBall x δ
    swap
    · rw [indicator_of_notMem hyb, mul_zero] at hd ⊢
      rw [indicator_of_notMem hyb, mul_zero] at hs
      have h1 := abs_nonpos_iff.1 hd
      have h2 := abs_nonpos_iff.1 hs
      change |u y * _| ≤ _
      rw [h1, show m.scaled δ (x - y) = 0 from h2]
      simp
    rw [indicator_of_mem hyb, mul_one] at hd hs ⊢
    have hxy : ‖x - y‖ ≤ δ := by
      have := Metric.mem_closedBall.1 hyb
      rwa [dist_comm, dist_eq_norm] at this
    have hyR : y ∈ Metric.closedBall (0 : s113b_E n) (R + 1) := by
      have := hR hyK
      rw [Metric.mem_closedBall, dist_zero_right] at this ⊢
      linarith
    have hxR : x ∈ Metric.closedBall (0 : s113b_E n) (R + 1) := by
      have := hR hyK
      rw [Metric.mem_closedBall, dist_zero_right] at this ⊢
      have h3 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by simpa using norm_add_le (x - y) y
      linarith [hδ.2]
    have hbxy : ‖b x - b y‖ ≤ L * δ := (hLip x hxR y hyR).trans (mul_le_mul_of_nonneg_left hxy hL0)
    have hdiv : |s113b_div b x| ≤ n * L :=
      (s113b_div_bound ((hb.differentiable (by norm_num)) x)).trans
        (mul_le_mul_of_nonneg_left (hLD x hxR) (Nat.cast_nonneg n))
    have hD : |fderiv ℝ (m.scaled δ) (x - y) (b x - b y)| ≤ (δ ^ n)⁻¹ * (Cd * L) := by
      refine hd.trans (mul_le_mul_of_nonneg_left ?_ hp.le)
      calc δ⁻¹ * Cd * ‖b x - b y‖ ≤ δ⁻¹ * Cd * (L * δ) :=
            mul_le_mul_of_nonneg_left hbxy (by positivity)
        _ = Cd * L := by field_simp
    have hS : |s113b_div b x * m.scaled δ (x - y)| ≤ n * L * ((δ ^ n)⁻¹ * Cρ) := by
      rw [abs_mul]
      exact mul_le_mul hdiv (show |m.scaled δ (x - y)| ≤ (δ ^ n)⁻¹ * Cρ from hs) (abs_nonneg _) (by positivity)
    calc |u y * (fderiv ℝ (m.scaled δ) (x - y) (b x - b y) + s113b_div b x * m.scaled δ (x - y))|
        = |u y| * |fderiv ℝ (m.scaled δ) (x - y) (b x - b y) + s113b_div b x * m.scaled δ (x - y)| := abs_mul _ _
      _ ≤ B * ((δ ^ n)⁻¹ * (Cd * L) + n * L * ((δ ^ n)⁻¹ * Cρ)) :=
          mul_le_mul (hB y) ((abs_add_le _ _).trans (add_le_add hD hS)) (abs_nonneg _) hB0
      _ = _ := by ring
  have := s113b_ball_int_bound hδ0 _ key
  unfold s113b_comm
  calc _ ≤ _ := this
    _ = _ := by ring


lemma s113b_comm_decomp (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) (b : s113b_E n → s113b_E n)
    (u : s113b_E n → ℝ) (x : s113b_E n)
    (h1 : Integrable (fun y => s113b_kd (s113b_kA m (fderiv ℝ b x)) δ (x - y) * u y) volume)
    (h2 : Integrable (fun y => s113b_kd m.ρ δ (x - y) * u y) volume)
    (h3 : Integrable (fun y => u y * fderiv ℝ (m.scaled δ) (x - y)
      (b x - b y - fderiv ℝ b x (x - y))) volume) :
    s113b_comm m δ b u x = (∫ y, s113b_kd (s113b_kA m (fderiv ℝ b x)) δ (x - y) * u y)
      + s113b_div b x * (∫ y, s113b_kd m.ρ δ (x - y) * u y)
      + ∫ y, u y * fderiv ℝ (m.scaled δ) (x - y) (b x - b y - fderiv ℝ b x (x - y)) := by
  have hpt : ∀ y, u y * (fderiv ℝ (m.scaled δ) (x - y) (b x - b y) + s113b_div b x * m.scaled δ (x - y))
      = (s113b_kd (s113b_kA m (fderiv ℝ b x)) δ (x - y) * u y
          + s113b_div b x * (s113b_kd m.ρ δ (x - y) * u y))
        + u y * fderiv ℝ (m.scaled δ) (x - y) (b x - b y - fderiv ℝ b x (x - y)) := by
    intro y
    have hD : fderiv ℝ (m.scaled δ) (x - y) (b x - b y)
        = fderiv ℝ (m.scaled δ) (x - y) (fderiv ℝ b x (x - y))
          + fderiv ℝ (m.scaled δ) (x - y) (b x - b y - fderiv ℝ b x (x - y)) := by
      rw [← map_add]; congr 1; abel
    have hA : fderiv ℝ (m.scaled δ) (x - y) (fderiv ℝ b x (x - y))
        = s113b_kd (s113b_kA m (fderiv ℝ b x)) δ (x - y) := by
      rw [s113b_fderiv_scaled m hδ]
      unfold s113b_kd s113b_kA
      rw [map_smul, map_smul, smul_eq_mul]
      ring
    have hs : m.scaled δ (x - y) = s113b_kd m.ρ δ (x - y) := rfl
    rw [hD, hA, hs]
    ring
  unfold s113b_comm
  have h12 : Integrable (fun y => s113b_kd (s113b_kA m (fderiv ℝ b x)) δ (x - y) * u y
      + s113b_div b x * (s113b_kd m.ρ δ (x - y) * u y)) volume := h1.add (h2.const_mul _)
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add h12 h3,
    integral_add h1 (h2.const_mul _), integral_const_mul]

theorem s113b_comm_tendsto_ae (m : s113b_Moll n) {b : s113b_E n → s113b_E n} {u : s113b_E n → ℝ}
    {B : ℝ} {K : Set (s113b_E n)} (hb : ContDiff ℝ 2 b) (hm : Measurable u) (hB : ∀ y, |u y| ≤ B)
    (hK : IsCompact K) (hKu : ∀ y, y ∉ K → u y = 0) :
    ∀ᵐ x ∂(volume : Measure (s113b_E n)),
      Tendsto (fun δ => s113b_comm m δ b u x) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  obtain ⟨Cρ, hCρ0, hCρ⟩ := s113b_zero_out_bdd (s113b_rho_cont m) (fun w hw => s113b_rho_zero m hw)
  obtain ⟨Cd, hCd0, hCd⟩ := s113b_zero_out_bdd (s113b_drho_cont m) (fun w hw => s113b_drho_zero m hw)
  filter_upwards [s113b_leb_ae hm hB] with x hx
  set A := fderiv ℝ b x with hA
  obtain ⟨L, r, hr, hT⟩ := s113b_taylor hb x
  obtain ⟨M1, -, hM1⟩ := s113b_zero_out_bdd (s113b_kA_cont m A) (fun w hw => s113b_kA_zero m A hw)
  have hbc : Continuous b := hb.continuous
  -- pointwise bound for the Taylor remainder part
  have hpt : ∀ δ, 0 < δ → δ ≤ r → ∀ y, |u y * fderiv ℝ (m.scaled δ) (x - y) (b x - b y - A (x - y))|
      ≤ (δ ^ n)⁻¹ * (B * Cd * |L| * δ) * (Metric.closedBall x δ).indicator (fun _ => (1 : ℝ)) y := by
    intro δ hδ hδr y
    have hp : 0 < (δ ^ n)⁻¹ := inv_pos.2 (pow_pos hδ n)
    have hd := s113b_dscaled_bound m (fun w => by simpa using hCd w) hδ x y (b x - b y - A (x - y))
    by_cases hyb : y ∈ Metric.closedBall x δ
    swap
    · rw [indicator_of_notMem hyb, mul_zero] at hd ⊢
      rw [abs_mul, abs_nonpos_iff.1 hd]
      simp
    rw [indicator_of_mem hyb, mul_one] at hd ⊢
    have hxy : ‖x - y‖ ≤ δ := by
      have := Metric.mem_closedBall.1 hyb
      rwa [dist_comm, dist_eq_norm] at this
    have he : ‖b x - b y - A (x - y)‖ ≤ |L| * δ ^ 2 := by
      have h1 := hT y (by rw [norm_sub_rev]; exact hxy.trans hδr)
      have h2 : b x - b y - A (x - y) = -(b y - b x - A (y - x)) := by
        rw [map_sub, map_sub]; abel
      rw [h2, norm_neg]
      refine h1.trans ?_
      rw [norm_sub_rev y x]
      exact mul_le_mul (le_abs_self L) (pow_le_pow_left₀ (norm_nonneg _) hxy 2) (by positivity) (abs_nonneg _)
    calc |u y * fderiv ℝ (m.scaled δ) (x - y) (b x - b y - A (x - y))|
        = |u y| * |fderiv ℝ (m.scaled δ) (x - y) (b x - b y - A (x - y))| := abs_mul _ _
      _ ≤ B * ((δ ^ n)⁻¹ * (δ⁻¹ * Cd * (|L| * δ ^ 2))) :=
          mul_le_mul (hB y) (hd.trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left he (by positivity)) hp.le)) (abs_nonneg _) hB0
      _ = (δ ^ n)⁻¹ * (B * Cd * |L| * δ) := by field_simp
  have hcontE : ∀ δ, 0 < δ → Continuous (fun y => fderiv ℝ (m.scaled δ) (x - y) (b x - b y - A (x - y))) := by
    intro δ hδ
    have : (fun y => fderiv ℝ (m.scaled δ) (x - y) (b x - b y - A (x - y)))
        = fun y => (δ ^ n)⁻¹ * δ⁻¹ * fderiv ℝ m.ρ (δ⁻¹ • (x - y)) (b x - b y - A (x - y)) :=
      funext fun y => s113b_fderiv_scaled m hδ _ _
    rw [this]
    have := s113b_drho_cont m
    have := A.continuous
    fun_prop
  have hE : ∀ δ, 0 < δ → δ ≤ r → Integrable (fun y => u y * fderiv ℝ (m.scaled δ) (x - y)
      (b x - b y - A (x - y))) volume := fun δ hδ hδr =>
    s113b_integrable_of_ball (x := x) (δ := δ) (c := (δ ^ n)⁻¹ * (B * Cd * |L| * δ))
      (hm.aestronglyMeasurable.mul (hcontE δ hδ).aestronglyMeasurable) (hpt δ hδ hδr)
  have hT1 := s113b_kern_tendsto (κ := s113b_kA m A) (M := M1) (s113b_kA_cont m A).measurable
    (fun z => by simpa [Real.norm_eq_abs] using hM1 z) (fun z hz => s113b_kA_zero m A hz) hm hB hx
  have hT2 := s113b_kern_tendsto (κ := m.ρ) (M := Cρ) (s113b_rho_cont m).measurable
    (fun z => by simpa [Real.norm_eq_abs] using hCρ z) (fun z hz => s113b_rho_zero m hz) hm hB hx
  have hT3 : Tendsto (fun δ => ∫ y, u y * fderiv ℝ (m.scaled δ) (x - y) (b x - b y - A (x - y)))
      (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun δ : ℝ => (B * Cd * |L| * s113b_V n) * δ) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (B * Cd * |L| * s113b_V n)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
    rw [Real.norm_eq_abs]
    have := s113b_ball_int_bound hδ.1 _ (hpt δ hδ.1 hδ.2.le)
    calc _ ≤ _ := this
      _ = _ := by ring
  have hsum := (hT1.add (hT2.const_mul (s113b_div b x))).add hT3
  have hlim : (∫ z, s113b_kA m A z) * u x + s113b_div b x * ((∫ z, m.ρ z) * u x) + 0 = 0 := by
    rw [s113b_int_kA, m.integral_one, s113b_div_eq ((hb.differentiable (by norm_num)) x)]
    ring
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
  have hδ0 : 0 < δ := hδ.1
  exact (s113b_comm_decomp m hδ0 b u x
    (s113b_kd_mul_integrable (s113b_kA_cont m A).measurable
      (fun z => by simpa [Real.norm_eq_abs] using hM1 z) (fun z hz => s113b_kA_zero m A hz) hm hB hδ0 x)
    (s113b_kd_mul_integrable (s113b_rho_cont m).measurable
      (fun z => by simpa [Real.norm_eq_abs] using hCρ z) (fun z hz => s113b_rho_zero m hz) hm hB hδ0 x)
    (hE δ hδ0 hδ.2.le)).symm

end HRS.MS.S113X2B
