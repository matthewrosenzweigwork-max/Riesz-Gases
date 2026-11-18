import HRS.Whole.MovtrAux2

/-!
# MOVTR auxiliary 3: the limit `ε → 0` and the gradient of the potential
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

lemma movtr_gEps_cont_eps (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    Continuous (fun ε : ℝ => movtr_gEps d s ε z) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : ∀ ε : ℝ, 0 < ‖z‖ ^ 2 + ε ^ 2 := fun ε => by positivity
  unfold movtr_gEps
  by_cases hs : s = 0
  · simp only [hs, ite_true]
    exact (Continuous.log (continuous_const.add (continuous_pow 2)) (fun ε => (hu ε).ne')).const_mul _
  · simp only [hs, ite_false]
    exact (continuous_const.add (continuous_pow 2)).rpow_const (fun ε => Or.inl (hu ε).ne')

lemma movtr_dEps_cont_eps (s : ℝ) (e : Euc d) {z : Euc d} (hz : z ≠ 0) :
    Continuous (fun ε : ℝ => movtr_dEps d s ε e z) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : ∀ ε : ℝ, 0 < ‖z‖ ^ 2 + ε ^ 2 := fun ε => by positivity
  unfold movtr_dEps
  exact (((continuous_const.add (continuous_pow 2)).rpow_const
    (fun ε => Or.inl (hu ε).ne')).const_mul _).neg.mul continuous_const

lemma movtr_dEps_abs_le_z {s : ℝ} (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 ≤ ε) (e z : Euc d) (he : ‖e‖ ≤ 1)
    (hz : z ≠ 0) : |movtr_dEps d s ε e z| ≤ movtr_sigma s * ‖z‖ ^ (-s - 1) := by
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  unfold movtr_dEps
  have hup : 0 ≤ (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) := Real.rpow_nonneg hu.le _
  rw [abs_mul, abs_neg, abs_of_nonneg (mul_nonneg hσ hup)]
  have h1 : (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) ≤ ‖z‖ ^ (-s - 2) := by
    have : ‖z‖ ^ (-s - 2) = (‖z‖ ^ 2) ^ (-s / 2 - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
      congr 1; push_cast; ring
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by linarith)
  have h2 : |inner ℝ z e| ≤ ‖z‖ := by
    calc |inner ℝ z e| ≤ ‖z‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖z‖ * 1 := by gcongr
      _ = ‖z‖ := by ring
  have h3 : ‖z‖ ^ (-s - 1) = ‖z‖ ^ (-s - 2) * ‖z‖ := by
    rw [show (-s - 1) = (-s - 2) + 1 by ring, Real.rpow_add hzpos, Real.rpow_one]
  rw [h3, ← mul_assoc]
  calc movtr_sigma s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * |inner ℝ z e|
      ≤ movtr_sigma s * ‖z‖ ^ (-s - 2) * ‖z‖ := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hσ) h2 (abs_nonneg _)
        exact mul_nonneg hσ (Real.rpow_nonneg hzpos.le _)
    _ = _ := by ring


/-- The integrable majorant of the force integrand. -/
def movtr_b2 (d : ℕ) (s c C : ℝ) (x z : Euc d) : ℝ :=
  movtr_sigma s * (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (fun z => C * ‖z‖ ^ (-s)) z +
    4 ^ (s + 1) * C * Real.exp (-c * ‖x - z‖ ^ 2))

lemma movtr_b2_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (x : Euc d) : Integrable (movtr_b2 d s c C x) := by
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  have h1 : IntegrableOn (fun z : Euc d => C * ‖z‖ ^ (-s)) (Metric.ball 0 (1 / 2)) := by
    have hdim : 1 ≤ Module.finrank ℝ (Euc d) := by simpa using hd
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) hdim (C := |C|) (α := s) (r := 1 / 2)
      (by simpa using hsd) ?_ ?_
    · refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun z _ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    · exact (measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable
  have h2 : Integrable (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
      (fun z => C * ‖z‖ ^ (-s))) := by
    rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    refine h1.mono_set ?_
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have h3 : Integrable (fun z : Euc d => Real.exp (-c * ‖x - z‖ ^ 2)) := by
    have := (movtr_integrable_rpow_gauss (d := d) hd (α := 0) (by
      have : (1:ℝ) ≤ d := by exact_mod_cast hd
      linarith) hc).comp_sub_left x
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp
  unfold movtr_b2
  exact (h2.add (h3.const_mul _)).const_mul _

lemma movtr_b2_bound_gen (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d)
    {z : Euc d} (hz : z ≠ 0) {a : ℝ} (hD : |a| ≤ movtr_sigma s * ‖z‖ ^ (-s - 1)) :
    |a * movtr_R ρ x z| ≤ movtr_b2 d s c C x z := by
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hdiff : Differentiable ℝ ρ := hρ1.differentiable (by norm_num)
  rw [abs_mul]
  unfold movtr_b2 movtr_R
  by_cases hB : ‖z‖ ≤ 1 / 4
  · have hmem : z ∈ Metric.closedBall (0 : Euc d) (1 / 4) := by simpa using hB
    rw [Set.indicator_of_mem hmem]
    simp only [hB, ite_true]
    have hmv : |ρ (x - z) - ρ x| ≤ C * ‖z‖ := by
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := ρ) (C := C) (s := Set.univ)
        (x := x) (y := x - z) (fun y _ => hdiff y)
        (fun y _ => (h1 y).trans (by
          calc C * Real.exp (-c * ‖y‖ ^ 2) ≤ C * 1 := by
                apply mul_le_mul_of_nonneg_left _ hC
                apply Real.exp_le_one_iff.mpr; nlinarith [sq_nonneg ‖y‖]
            _ = C := by ring)) convex_univ (Set.mem_univ _) (Set.mem_univ _)
      simpa [Real.norm_eq_abs] using this
    have : ‖z‖ ^ (-s - 1) * ‖z‖ = ‖z‖ ^ (-s) := by
      rw [← Real.rpow_add_one hzpos.ne']; congr 1; ring
    calc |a| * |ρ (x - z) - ρ x|
        ≤ (movtr_sigma s * ‖z‖ ^ (-s - 1)) * (C * ‖z‖) :=
          mul_le_mul hD hmv (abs_nonneg _) (mul_nonneg hσ (Real.rpow_nonneg hzpos.le _))
      _ = movtr_sigma s * (C * (‖z‖ ^ (-s - 1) * ‖z‖)) := by ring
      _ = movtr_sigma s * (C * ‖z‖ ^ (-s)) := by rw [this]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hσ
        have : 0 ≤ 4 ^ (s + 1) * C * Real.exp (-c * ‖x - z‖ ^ 2) := by positivity
        linarith
  · have hnmem : z ∉ Metric.closedBall (0 : Euc d) (1 / 4) := by simpa using hB
    rw [Set.indicator_of_notMem hnmem]
    simp only [hB, ite_false]
    push Not at hB
    have h4 : ‖z‖ ^ (-s - 1) ≤ 4 ^ (s + 1) := by
      have h5 : ((1 / 4 : ℝ)) ^ (-s - 1) = 4 ^ (s + 1) := by
        rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_sub', neg_neg]
        ring_nf
      rw [← h5]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hB.le (by linarith)
    have h6 := h0 (x - z)
    calc |a| * |ρ (x - z)|
        ≤ (movtr_sigma s * 4 ^ (s + 1)) * (C * Real.exp (-c * ‖x - z‖ ^ 2)) := by
          apply mul_le_mul _ h6 (abs_nonneg _) (by positivity)
          exact hD.trans (mul_le_mul_of_nonneg_left h4 hσ)
      _ = movtr_sigma s * (4 ^ (s + 1) * C * Real.exp (-c * ‖x - z‖ ^ 2)) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hσ
        have : 0 ≤ C * ‖z‖ ^ (-s) := mul_nonneg hC (Real.rpow_nonneg hzpos.le _)
        linarith


lemma movtr_b2_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x e : Euc d) (he : ‖e‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) {z : Euc d} (hz : z ≠ 0) :
    |movtr_dEps d s ε e z * movtr_R ρ x z| ≤ movtr_b2 d s c C x z :=
  movtr_b2_bound_gen hd hs0 hsd hc hC hρ1 h0 h1 x hz (movtr_dEps_abs_le_z hs0 hε e z he hz)

lemma movtr_R_measurable {ρ : Euc d → ℝ} (hρc : Continuous ρ) (x : Euc d) :
    Measurable (movtr_R ρ x) := by
  unfold movtr_R
  have h1 : Measurable fun z : Euc d => ρ (x - z) :=
    hρc.measurable.comp (measurable_const.sub measurable_id)
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
    (h1.sub measurable_const) h1

lemma movtr_ae_ne_zero (hd : 1 ≤ d) : ({0} : Set (Euc d))ᶜ ∈ ae (volume : Measure (Euc d)) := by
  have : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  exact compl_mem_ae_iff.mpr (measure_singleton 0)

/-- The integral identity at `ε = 0`: the potential differentiated on the density side equals the
cancellation form. -/
lemma movtr_eq_zero (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x e : Euc d) (he : ‖e‖ ≤ 1) :
    ∫ z, rieszKernel d s z * fderiv ℝ ρ (x - z) e =
      ∫ z, movtr_dEps d s 0 e z * movtr_R ρ x z := by
  have hρc : Continuous ρ := hρ1.continuous
  have hfd : Continuous (fderiv ℝ ρ) := hρ1.continuous_fderiv (by norm_num)
  have hnt := movtr_ae_ne_zero (d := d) hd
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  have hlmem : Set.Ioc (0 : ℝ) 1 ∈ l := Ioc_mem_nhdsGT one_pos
  -- T1
  have T1 : Tendsto (fun ε : ℝ => ∫ z, movtr_gEps d s ε z * fderiv ℝ ρ (x - z) e) l
      (𝓝 (∫ z, movtr_gEps d s 0 z * fderiv ℝ ρ (x - z) e)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => C * Real.exp (c * ‖x‖ ^ 2) *
        ((2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun ε => ?_
      exact ((movtr_gEps_measurable (d := d) s ε).aestronglyMeasurable).mul
        ((hfd.comp (continuous_const.sub continuous_id)).clm_apply continuous_const).aestronglyMeasurable
    · filter_upwards [hlmem] with ε hε
      filter_upwards [hnt] with z hz
      rw [norm_mul, Real.norm_eq_abs]
      have hg := movtr_gEps_abs_le hs0 hε.1.le hε.2 hz
      have hfz : ‖fderiv ℝ ρ (x - z) e‖ ≤ C * (Real.exp (c * ‖x‖ ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2)) := by
        calc ‖fderiv ℝ ρ (x - z) e‖ ≤ ‖fderiv ℝ ρ (x - z)‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖fderiv ℝ ρ (x - z)‖ * 1 := by gcongr
          _ = ‖fderiv ℝ ρ (x - z)‖ := by ring
          _ ≤ C * Real.exp (-c * ‖x - z‖ ^ 2) := h1 _
          _ ≤ _ := mul_le_mul_of_nonneg_left (movtr_gauss_shift hc le_rfl z) hC
      calc |movtr_gEps d s ε z| * ‖fderiv ℝ ρ (x - z) e‖
          ≤ (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) *
              (C * (Real.exp (c * ‖x‖ ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) :=
            mul_le_mul hg hfz (norm_nonneg _) ((abs_nonneg _).trans hg)
        _ = _ := by ring
    · exact ((movtr_majorant_integrable hd hs0 hsd (c := c / 2) (by positivity)).const_mul _)
    · filter_upwards [hnt] with z hz
      exact ((movtr_gEps_cont_eps s hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul_const _
  -- T2
  have T2 : Tendsto (fun ε : ℝ => ∫ z, movtr_dEps d s ε e z * movtr_R ρ x z) l
      (𝓝 (∫ z, movtr_dEps d s 0 e z * movtr_R ρ x z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (movtr_b2 d s c C x) ?_ ?_
      (movtr_b2_integrable hd hs0 hsd hc x) ?_
    · filter_upwards [hlmem] with ε hε
      have hu : ∀ w : Euc d, 0 < ‖w‖ ^ 2 + ε ^ 2 := fun w => by have := hε.1; positivity
      have hdE : Continuous (movtr_dEps d s ε e) := by
        unfold movtr_dEps
        exact ((((continuous_norm.pow 2).add continuous_const).rpow_const
          (fun z => Or.inl (hu z).ne')).const_mul _).neg.mul (continuous_id.inner continuous_const)
      exact hdE.aestronglyMeasurable.mul (movtr_R_measurable hρc x).aestronglyMeasurable
    · filter_upwards [hlmem] with ε hε
      filter_upwards [hnt] with z hz
      rw [Real.norm_eq_abs]
      exact movtr_b2_bound hd hs0 hsd hc hC hρ1 h0 h1 x e he hε.1.le hz
    · filter_upwards [hnt] with z hz
      exact ((movtr_dEps_cont_eps s e hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul_const _
  have T1' : Tendsto (fun ε : ℝ => ∫ z, movtr_dEps d s ε e z * movtr_R ρ x z) l
      (𝓝 (∫ z, movtr_gEps d s 0 z * fderiv ℝ ρ (x - z) e)) := by
    refine T1.congr' ?_
    filter_upwards [hlmem] with ε hε
    exact movtr_eq_eps hd hs0 hsd hε.1 hε.2 hc hC hρ1 h0 h1 x e he
  rw [← movtr_gEps_zero d s]
  exact tendsto_nhds_unique T1' T2

end HRS.Whole
