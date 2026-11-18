import HRS.MS.SA12Z3NearN4A
import HRS.MS.SA12Z3NearN7C

/-!
# S.A.12 N4 (SA12Z3), part B: smoothed first Riesz pairings

`S_ε(u,v) = ∬ u(x) D_ε(x-y) v(y)`: skew in `(u,v)`, converges to `∫ u T v` (`T = firstRiesz i`) as `ε → 0+`,
and the commutator form `S_ε(f a, h) - S_ε(f, a h)` is bounded uniformly in `ε` by the `κ`-Young bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- The smoothed pairing. -/
def sa12z3_S (d : ℕ) (s : ℝ) (i : Fin d) (ε : ℝ) (u v : Euc d → ℝ) : ℝ :=
  ∫ p : Euc d × Euc d, u p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * v p.2
    ∂(volume.prod volume)

theorem sa12z3_S_skew (s : ℝ) (i : Fin d) (ε : ℝ) (u v : Euc d → ℝ) :
    sa12z3_S d s i ε u v = -sa12z3_S d s i ε v u := by
  unfold sa12z3_S
  rw [← integral_neg]
  calc _ = ∫ p : Euc d × Euc d, u p.swap.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ))
        (p.swap.1 - p.swap.2) * v p.swap.2 ∂(volume.prod volume) :=
        (integral_prod_swap (fun p : Euc d × Euc d => u p.1 *
          movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * v p.2)
          (μ := volume) (ν := volume)).symm
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [Prod.fst_swap, Prod.snd_swap]
        rw [← neg_sub p.1 p.2, movtr_dEps_odd]
        ring

theorem sa12z3_Leps_lim (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {u w : Euc d → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) (hw : Continuous w) (hwc : HasCompactSupport w) :
    Tendsto (fun ε : ℝ => ∫ p : Euc d × Euc d, u p.1 * movtr_gEps d s ε (p.1 - p.2) * w p.2
      ∂(volume.prod volume)) (𝓝[>] 0)
      (𝓝 (∫ x, u x * HRS.Whole.convFun (rieszKernel d s) w x)) := by
  obtain ⟨R1, hR1⟩ := huc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨R2, hR2⟩ := hwc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set ρ : ℝ := max R1 R2 with hρ
  have hsu : Function.support u ⊆ Metric.closedBall (0 : Euc d) ρ := fun x hx =>
    Metric.closedBall_subset_closedBall (le_max_left _ _) (hR1 (subset_tsupport _ hx))
  have hw0 : ∀ y, y ∉ Metric.closedBall (0 : Euc d) ρ → w y = 0 := fun y hy => by
    by_contra h
    exact hy (Metric.closedBall_subset_closedBall (le_max_right _ _) (hR2 (subset_tsupport _
      (Function.mem_support.2 h))))
  obtain ⟨Cu, hCu⟩ := hu.bounded_above_of_compact_support huc
  have hw_cs : HasCompactSupport w := hwc
  have hbd_int : Integrable (fun p : Euc d × Euc d =>
      Cu * (‖w p.2‖ * sa12z2_maj d s ρ (p.1 - p.2))) (volume.prod volume) := by
    have hwn : Integrable (fun y => ‖w y‖) :=
      (hw.norm).integrable_of_hasCompactSupport hw_cs.norm
    have h := hwn.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
      (sa12z2_maj_integrable hd hs0 hsd ρ)
    have h' : Integrable (fun p : Euc d × Euc d =>
        ‖w p.2‖ * sa12z2_maj d s ρ (p.1 - p.2)) (volume.prod volume) := by
      simpa using h
    exact h'.const_mul Cu
  have hPhi_meas : ∀ ε : ℝ, Measurable (fun p : Euc d × Euc d =>
      u p.1 * movtr_gEps d s ε (p.1 - p.2) * w p.2) := fun ε =>
    ((hu.measurable.comp measurable_fst).mul
      ((movtr_gEps_measurable (d := d) s ε).comp (measurable_fst.sub measurable_snd))).mul
      (hw.measurable.comp measurable_snd)
  have hPhi_bd : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ᵐ p ∂(volume.prod volume : Measure (Euc d × Euc d)),
      ‖u p.1 * movtr_gEps d s ε (p.1 - p.2) * w p.2‖ ≤
        Cu * (‖w p.2‖ * sa12z2_maj d s ρ (p.1 - p.2)) := by
    intro ε h0 h1
    filter_upwards [sa12z2_diag_ae hd] with p hp
    exact sa12z2_phi_bound hs0 h0 h1 hCu hsu hw0 p hp
  have hΦ0_int : Integrable (fun p : Euc d × Euc d => u p.1 * movtr_gEps d s 0 (p.1 - p.2) * w p.2)
      (volume.prod volume) :=
    hbd_int.mono' (hPhi_meas 0).aestronglyMeasurable (hPhi_bd 0 le_rfl zero_le_one)
  have hΦ0_eq : ∀ x : Euc d, ∫ y, u x * movtr_gEps d s 0 (x - y) * w y =
      u x * HRS.Whole.convFun (rieszKernel d s) w x := by
    intro x
    rw [movtr_gEps_zero]
    unfold HRS.Whole.convFun
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [mul_assoc]
  have hfubini : ∫ p : Euc d × Euc d, u p.1 * movtr_gEps d s 0 (p.1 - p.2) * w p.2 ∂(volume.prod volume) =
      ∫ x, u x * HRS.Whole.convFun (rieszKernel d s) w x := by
    refine (integral_prod _ hΦ0_int).trans ?_
    exact integral_congr_ae (Eventually.of_forall hΦ0_eq)
  rw [← hfubini]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun p : Euc d × Euc d => Cu * (‖w p.2‖ * sa12z2_maj d s ρ (p.1 - p.2)))
    (Eventually.of_forall fun ε => (hPhi_meas ε).aestronglyMeasurable) ?_ hbd_int ?_
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    exact hPhi_bd ε hε.1.le hε.2.le
  · filter_upwards [sa12z2_diag_ae hd] with p hp
    have hc := movtr_gEps_cont_eps (d := d) s hp
    have ht : Tendsto (fun ε => movtr_gEps d s ε (p.1 - p.2)) (𝓝[>] 0)
        (𝓝 (movtr_gEps d s 0 (p.1 - p.2))) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (ht.const_mul (u p.1)).mul_const (w p.2)

/-- `S_ε(u,v) → ∫ u T v` for `v ∈ C¹_c`. -/
theorem sa12z3_S_lim (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {u v : Euc d → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
    Tendsto (fun ε : ℝ => sa12z3_S d s i ε u v) (𝓝[>] 0)
      (𝓝 (∫ x, u x * firstRiesz d s i v x)) := by
  have hDc : Continuous (D1 i v) := (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h := sa12z3_Leps_lim hd hs0 hsd hu huc hDc (D1_supp hvc i)
  have e1 : (fun x => u x * HRS.Whole.convFun (rieszKernel d s) (D1 i v) x) =
      fun x => u x * firstRiesz d s i v x :=
    funext fun x => by rw [sa12z3_firstRiesz_eq' hs0 hsd i hv hvc x]; rfl
  rw [e1] at h
  refine h.congr' ?_
  obtain ⟨R1, hR1⟩ := huc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨R2, hR2⟩ := hvc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set ρ : ℝ := max R1 R2 with hρ
  have hsu : Function.support u ⊆ Metric.closedBall (0 : Euc d) ρ := fun x hx =>
    Metric.closedBall_subset_closedBall (le_max_left _ _) (hR1 (subset_tsupport _ hx))
  have hsv : Function.support v ⊆ Metric.closedBall (0 : Euc d) ρ := fun x hx =>
    Metric.closedBall_subset_closedBall (le_max_right _ _) (hR2 (subset_tsupport _ hx))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have := sa12z2_prod_eq hu hsu s hε i hv hvc hsv
  unfold sa12z3_S
  rw [← this]
  rfl

/-- Skew-adjointness of `T = firstRiesz`. -/
theorem sa12z3_T_skew (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {u v : Euc d → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
    ∫ x, u x * firstRiesz d s i v x = -∫ x, v x * firstRiesz d s i u x := by
  have h1 := sa12z3_S_lim hd hs0 hsd i hu.continuous huc hv hvc
  have h2 := sa12z3_S_lim hd hs0 hsd i hv.continuous hvc hu huc
  have h3 : Tendsto (fun ε : ℝ => sa12z3_S d s i ε u v) (𝓝[>] 0)
      (𝓝 (-∫ x, v x * firstRiesz d s i u x)) := by
    have := h2.neg
    refine this.congr fun ε => ?_
    rw [sa12z3_S_skew s i ε u v]
  exact tendsto_nhds_unique h1 h3

end HRS.MH.AdjointRd.Phase2SA12Near
