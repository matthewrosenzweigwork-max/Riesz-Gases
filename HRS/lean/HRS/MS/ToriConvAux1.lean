import HRS.MS.ToriCoefB

/-!
# MS-TORI-DRIFTCONV, helper file 1: the whole-space operator `T^E`, the kernel package, integrability

`tcv_TE k g x = ∫_{ℝ^d} k(z) • (g(x - z) - 1_{|z| ≤ 1/4} g(x)) dz` (whole-space analogue of `tcb_T`).
`tcv_Kerns` collects the kernel facts needed for the convergence `T^{Q_L}_{k_L} g_L → T^E_{k_E} g`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriConv

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

/-- The whole-space cancellation convolution operator. -/
def tcv_TE {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (k : Euc d → ℝ) (g : Euc d → W)
    (x : Euc d) : W :=
  ∫ z, tcb_F k g x z

/-- Kernel package for the convergence of `T^{Q_L}_{k_L}` to `T^E_{k_E}`. -/
structure tcv_Kerns (d : ℕ) (s : ℝ) (kL : ℝ → Euc d → ℝ) (kE : Euc d → ℝ) (Kf Cn : ℝ) : Prop where
  hKf : 0 ≤ Kf
  hCn : 0 ≤ Cn
  kern : ∀ L : ℝ, 1 ≤ L → tcb_Kern L (kL L) Kf
  near : ∀ L : ℝ, 1 ≤ L → ∀ z : Euc d, ‖z‖ ≤ 1 / 2 → |kL L z| * ‖z‖ ≤ Cn * ‖z‖ ^ (-s)
  measE : Measurable kE
  nearE : ∀ z : Euc d, ‖z‖ ≤ 1 / 2 → |kE z| * ‖z‖ ≤ Cn * ‖z‖ ^ (-s)
  farE : ∀ z : Euc d, 1 / 4 < ‖z‖ → |kE z| ≤ Kf
  awayE : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ z : Euc d, δ ≤ ‖z‖ → |kE z| ≤ C
  conv : ∀ δ R η : ℝ, 0 < δ → 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ z : Euc d, δ ≤ ‖z‖ →
    ‖z‖ ≤ R → |kL L z - kE z| ≤ η

theorem tcv_rpow_integrableOn (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.ball (0 : Euc d) (1 / 2)) volume := by
  have hfin : 1 ≤ Module.finrank ℝ (Euc d) := by
    rw [finrank_euclideanSpace_fin]; exact hd
  refine integrableOn_ball_of_norm_le_rpow hfin (C := 1) (α := s)
    (f := fun z : Euc d => ‖z‖ ^ (-s))
    (by rw [finrank_euclideanSpace_fin]; exact hsd) ?_
    ((measurable_norm.pow_const _).aestronglyMeasurable)
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]

theorem tcv_N_subset_ball : tcb_N d ⊆ Metric.ball (0 : Euc d) (1 / 2) := fun z hz => by
  have : ‖z‖ ≤ 1 / 4 := by simpa [tcb_N] using hz
  rw [Metric.mem_ball, dist_zero_right]
  linarith

theorem tcv_near_small (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∫ z in Metric.closedBall (0 : Euc d) δ, ‖z‖ ^ (-s) ≤ ε := by
  set δn : ℕ → ℝ := fun n => 1 / (4 * ((n : ℝ) + 1)) with hδn
  have hpos : ∀ n, 0 < δn n := fun n => by positivity
  have hle : ∀ n, δn n ≤ 1 / 4 := fun n => by
    rw [hδn]
    simp only
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hanti : Antitone fun n : ℕ => Metric.closedBall (0 : Euc d) (δn n) := by
    intro a b hab
    refine Metric.closedBall_subset_closedBall ?_
    rw [hδn]
    simp only
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith
  have hint : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.closedBall (0 : Euc d) (δn 0)) volume := by
    refine (tcv_rpow_integrableOn hd hsd).mono_set ?_
    refine Metric.closedBall_subset_ball ?_
    have := hle 0
    linarith
  have hT := tendsto_setIntegral_of_antitone (μ := (volume : Measure (Euc d)))
    (f := fun z : Euc d => ‖z‖ ^ (-s)) (fun n => Metric.isClosed_closedBall.measurableSet) hanti
    ⟨0, hint⟩
  have hsub : (⋂ n, Metric.closedBall (0 : Euc d) (δn n)) ⊆ {0} := by
    intro z hz
    simp only [mem_iInter, Metric.mem_closedBall, dist_zero_right] at hz
    by_contra hz0
    have hz0' : 0 < ‖z‖ := norm_pos_iff.2 hz0
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (4 * ‖z‖))
    have h1 := hz n
    rw [hδn] at h1
    simp only at h1
    rw [le_div_iff₀ (by positivity)] at h1
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  haveI : Nontrivial (Euc d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have hnull : volume (⋂ n, Metric.closedBall (0 : Euc d) (δn n)) = 0 :=
    measure_mono_null hsub (measure_singleton 0)
  rw [setIntegral_measure_zero _ hnull] at hT
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hT).2 ε hε).exists
  exact ⟨δn n, hpos n, hle n, hn.le⟩

theorem tcv_F_near {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (k : Euc d → ℝ)
    (g : Euc d → W) (hg : Differentiable ℝ g) (B1 : ℝ) (hB1 : ∀ y, ‖fderiv ℝ g y‖ ≤ B1)
    (x z : Euc d) (hz : ‖z‖ ≤ 1 / 4) : ‖tcb_F k g x z‖ ≤ |k z| * ‖z‖ * B1 := by
  have hzN : z ∈ tcb_N d := by simpa [tcb_N] using hz
  unfold tcb_F
  rw [Set.indicator_of_mem hzN, norm_smul, Real.norm_eq_abs]
  have := tcb_mvt g hg B1 hB1 x z
  have h2 : |k z| * ‖g (x - z) - g x‖ ≤ |k z| * (B1 * ‖z‖) :=
    mul_le_mul_of_nonneg_left this (abs_nonneg _)
  nlinarith

theorem tcv_F_far {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (k : Euc d → ℝ)
    (g : Euc d → W) (x z : Euc d) (hz : ¬ ‖z‖ ≤ 1 / 4) :
    tcb_F k g x z = k z • g (x - z) := by
  have hzN : z ∉ tcb_N d := by simpa [tcb_N] using hz
  unfold tcb_F
  rw [Set.indicator_of_notMem hzN, sub_zero]

theorem tcv_F_aesm {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {k : Euc d → ℝ}
    (hk : Measurable k) (g : Euc d → W) (hg : Continuous g) (x : Euc d) (μ : Measure (Euc d)) :
    AEStronglyMeasurable (tcb_F k g x) μ := by
  unfold tcb_F
  refine AEStronglyMeasurable.smul hk.aestronglyMeasurable ?_
  refine AEStronglyMeasurable.sub ?_ ?_
  · exact (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact (aestronglyMeasurable_const).indicator tcb_measurableSet_N

theorem tcv_intN {s : ℝ} (hd : 1 ≤ d) (hsd : s < d) {k : Euc d → ℝ} {Cn : ℝ} (hmeas : Measurable k)
    (hnear : ∀ z : Euc d, ‖z‖ ≤ 1 / 2 → |k z| * ‖z‖ ≤ Cn * ‖z‖ ^ (-s)) :
    IntegrableOn (fun z : Euc d => |k z| * ‖z‖) (tcb_N d) volume := by
  have h1 : IntegrableOn (fun z : Euc d => Cn * ‖z‖ ^ (-s)) (tcb_N d) volume :=
    IntegrableOn.mono_set ((tcv_rpow_integrableOn hd hsd).const_mul Cn) tcv_N_subset_ball
  refine Integrable.mono' h1 ((hmeas.abs.mul measurable_norm).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem tcb_measurableSet_N fun z hz => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
  have hz1 : ‖z‖ ≤ 1 / 4 := by simpa [tcb_N] using hz
  exact hnear z (by linarith)

/-- Pointwise bound of the whole-space integrand. -/
theorem tcv_F_bound_E {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {k : Euc d → ℝ} {Kf : ℝ}
    (hKf : 0 ≤ Kf) (hfar : ∀ z : Euc d, 1 / 4 < ‖z‖ → |k z| ≤ Kf) (g : Euc d → W)
    (hg : Differentiable ℝ g) (B1 : ℝ) (hB1 : ∀ y, ‖fderiv ℝ g y‖ ≤ B1) (x z : Euc d) :
    ‖tcb_F k g x z‖ ≤ (tcb_N d).indicator (fun z => |k z| * ‖z‖ * B1) z + Kf * ‖g (x - z)‖ := by
  have hK0 : 0 ≤ Kf * ‖g (x - z)‖ := mul_nonneg hKf (norm_nonneg _)
  by_cases hzN : z ∈ tcb_N d
  · rw [Set.indicator_of_mem hzN]
    have h1 : ‖z‖ ≤ 1 / 4 := by simpa [tcb_N] using hzN
    have := tcv_F_near k g hg B1 hB1 x z h1
    linarith
  · rw [Set.indicator_of_notMem hzN, zero_add]
    have h1 : ¬ ‖z‖ ≤ 1 / 4 := by simpa [tcb_N] using hzN
    rw [tcv_F_far k g x z h1, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hfar z (not_le.1 h1)) (norm_nonneg _)

theorem tcv_F_integrable_E {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : ℝ} {kL : ℝ → Euc d → ℝ}
    {kE : Euc d → ℝ} {Kf Cn : ℝ} (hd : 1 ≤ d) (hsd : s < d) (hk : tcv_Kerns d s kL kE Kf Cn)
    (g : Euc d → W) (hg : Differentiable ℝ g) (B1 : ℝ) (hB1 : ∀ y, ‖fderiv ℝ g y‖ ≤ B1)
    (hint : Integrable g) (x : Euc d) : Integrable (tcb_F kE g x) := by
  have hintN := tcv_intN hd hsd hk.measE hk.nearE
  have hdom : Integrable (fun z => (tcb_N d).indicator (fun z => |kE z| * ‖z‖ * B1) z +
      Kf * ‖g (x - z)‖) := by
    refine Integrable.add ?_ ?_
    · rw [integrable_indicator_iff tcb_measurableSet_N]
      exact hintN.mul_const B1
    · exact ((hint.comp_sub_left x).norm).const_mul Kf
  refine Integrable.mono' hdom (tcv_F_aesm hk.measE g hg.continuous x _) ?_
  exact Filter.Eventually.of_forall fun z =>
    tcv_F_bound_E hk.hKf hk.farE g hg B1 hB1 x z

end HRS.MS.ToriConv
