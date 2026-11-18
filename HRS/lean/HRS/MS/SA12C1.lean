import HRS.MS.SA12K6
import HRS.MS.SA12V1

/-!
# S.A.12(c), packet E7.01: exact translation averaging over one period cell

`sa12c_avg_family`: for a continuous `F(c,x)` with `F(c+Lk, x+Lk) = F(c,x)` and `F c x = 0` for `‖x-c‖ > R`,
`∫_{c ∈ Q_L} ∫_x F c x = ∫_v ∫_{x ∈ Q_L} F (x-v) x` (Pro return, `energy:eq:average-family`).
`sa12c_avg_scalar`: the case `F c x = w(x-c) h(x)`: `∫_{c∈Q_L}∫_x w(x-c)h(x) = (∫ w) ∫_{Q_L} h`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- the shifted integrand `G c v = F c (c+v)` is bounded -/
theorem sa12c_G_bdd {L : ℝ} (hL : 0 < L) {F : Euc d → Euc d → ℝ} (hc : Continuous (Function.uncurry F))
    (hper : ∀ (c x : Euc d) (k : Fin d → ℤ), F (c + L • latticePt k) (x + L • latticePt k) = F c x) {R : ℝ}
    (hsupp : ∀ c x, R < ‖x - c‖ → F c x = 0) :
    ∃ B : ℝ, ∀ c v : Euc d, |F c (c + v)| ≤ B := by
  set G : Euc d × Euc d → ℝ := fun p => F p.1 (p.1 + p.2) with hG
  have hGc : Continuous G := hc.comp (continuous_fst.prodMk (continuous_fst.add continuous_snd))
  have hK : IsCompact ({c : Euc d | ∀ i, c i ∈ Icc (0 : ℝ) L} ×ˢ Metric.closedBall (0 : Euc d) R) :=
    (HRS.MS.ToriCoefB.tcb_compact_Icc 0 L).prod (isCompact_closedBall _ _)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hGc.continuousOn
  refine ⟨max B 0, fun c v => ?_⟩
  by_cases hv : ‖v‖ ≤ R
  · obtain ⟨k, hk⟩ := sa12v_reduce L hL c
    have hcm : c + L • latticePt k ∈ {c : Euc d | ∀ i, c i ∈ Icc (0 : ℝ) L} := by
      intro i; simpa [latticePt] using hk i
    have h1 := hB (c + L • latticePt k, v) ⟨hcm, by simpa using hv⟩
    have e : G (c + L • latticePt k, v) = F c (c + v) := by
      simp only [hG]
      have := hper c (c + v) k
      rw [← this]; congr 1; abel
    rw [e, Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  · have : F c (c + v) = 0 := hsupp c (c + v) (by simpa using not_le.1 hv)
    rw [this]; simp

theorem sa12c_avg_family {L : ℝ} (hL : 0 < L) {F : Euc d → Euc d → ℝ} (hc : Continuous (Function.uncurry F))
    (hper : ∀ (c x : Euc d) (k : Fin d → ℤ), F (c + L • latticePt k) (x + L • latticePt k) = F c x) {R : ℝ}
    (hsupp : ∀ c x, R < ‖x - c‖ → F c x = 0) :
    ∫ c in periodBox d L, ∫ x, F c x = ∫ v, ∫ x in periodBox d L, F (x - v) x := by
  obtain ⟨B, hB⟩ := sa12c_G_bdd hL hc hper hsupp
  set G : Euc d → Euc d → ℝ := fun c v => F c (c + v) with hG
  have hGc : Continuous (Function.uncurry G) := hc.comp (continuous_fst.prodMk (continuous_fst.add continuous_snd))
  have hGs : ∀ c v, R < ‖v‖ → G c v = 0 := fun c v hv => hsupp c (c + v) (by simpa using hv)
  have h1 : ∀ c, ∫ x, F c x = ∫ v, G c v := fun c => by
    simp only [hG]
    exact (integral_add_left_eq_self (fun x => F c x) c).symm
  simp_rw [h1]
  have : IsFiniteMeasure (volume.restrict (periodBox d L)) := sa12v_box_fin L
  have hint : Integrable (Function.uncurry G) ((volume.restrict (periodBox d L)).prod volume) := by
    have hdom : Integrable (fun p : Euc d × Euc d => |B| * (Metric.closedBall (0 : Euc d) R).indicator
        (fun _ => (1 : ℝ)) p.2) ((volume.restrict (periodBox d L)).prod volume) := by
      refine Integrable.const_mul ?_ _
      have h2 : Integrable (fun v : Euc d => (Metric.closedBall (0 : Euc d) R).indicator (fun _ => (1 : ℝ)) v)
          (volume : Measure (Euc d)) :=
        (integrable_indicator_iff measurableSet_closedBall).2
          (integrableOn_const (measure_closedBall_lt_top (μ := (volume : Measure (Euc d))) (x := (0 : Euc d)) (r := R)).ne)
      exact h2.comp_snd (μ := volume.restrict (periodBox d L))
    refine Integrable.mono' hdom hGc.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    by_cases hv : ‖p.2‖ ≤ R
    · have : p.2 ∈ Metric.closedBall (0 : Euc d) R := by simpa using hv
      rw [Set.indicator_of_mem this, mul_one, Real.norm_eq_abs]
      exact (hB p.1 p.2).trans (le_abs_self _)
    · have h0 : G p.1 p.2 = 0 := hGs _ _ (not_le.1 hv)
      have : p.2 ∉ Metric.closedBall (0 : Euc d) R := by simpa using hv
      rw [Set.indicator_of_notMem this]
      simp [Function.uncurry, h0]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  have hper' : ∀ (x : Euc d) (k : Fin d → ℤ), (fun c => G c v) (x + L • latticePt k) = (fun c => G c v) x := by
    intro x k
    simp only [hG]
    have := hper x (x + v) k
    rw [← this]; congr 1; abel
  have := sa12k_box_shift (d := d) L hL (Φ := fun c => G c v) hper' v
  simp only [hG, sub_add_cancel] at this ⊢
  exact this.symm

theorem sa12c_avg_scalar {L : ℝ} (hL : 0 < L) {w h : Euc d → ℝ} (hw : Continuous w) (hh : Continuous h)
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), h (x + L • latticePt k) = h x) {R : ℝ}
    (hsupp : ∀ v, R < ‖v‖ → w v = 0) :
    ∫ c in periodBox d L, ∫ x, w (x - c) * h x = (∫ v, w v) * ∫ x in periodBox d L, h x := by
  have hF := sa12c_avg_family (L := L) hL (F := fun c x => w (x - c) * h x)
    ((hw.comp (continuous_snd.sub continuous_fst)).mul (hh.comp continuous_snd))
    (fun c x k => by
      rw [hper x k]; congr 2; abel)
    (R := R) (fun c x hx => by simp [hsupp _ hx])
  rw [hF]
  simp only [sub_sub_cancel]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]

end HRS.MH.AdjointRd.Phase2SA12C

end
