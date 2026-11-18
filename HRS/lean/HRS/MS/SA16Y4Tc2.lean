import HRS.MS.SA16Y4Tc1

/-!
# S.A.16 (SA16Y4) Tc2: equi-Lipschitz plus pointwise continuity in the parameter gives local uniform continuity

`sa16y4_locunif`: if `|f r x - f r y| ≤ L ‖x - y‖` for `r ∈ I` and `r ↦ f r x` is continuous on `I` for every `x`, then for each ball
`closedBall 0 R`, `r0 ∈ I` and `ε > 0` there is `δ` with `|f r x - f r0 x| ≤ ε` for `r ∈ I`, `|r - r0| < δ`, `‖x‖ ≤ R`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R

section Tc2
variable {d : ℕ}

theorem sa16y4_locunif {I : Set ℝ} {L : ℝ} (hL : 0 ≤ L) (f : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hlip : ∀ r ∈ I, ∀ x y, |f r x - f r y| ≤ L * ‖x - y‖)
    (hpt : ∀ x, ContinuousOn (fun r => f r x) I) (R : ℝ) {r0 : ℝ} (hr0 : r0 ∈ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ I, |r - r0| < δ → ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ R →
      |f r x - f r0 x| ≤ ε := by
  set η : ℝ := ε / (4 * (L + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨t, htK, htfin, hcov⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).finite_cover_balls hη0
  have hev : ∀ᶠ r in 𝓝[I] r0, ∀ c ∈ htfin.toFinset, |f r c - f r0 c| < ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro c _
    have := (hpt c r0 hr0).tendsto
    have h2 := (Metric.tendsto_nhds.1 this) (ε / 2) (by positivity)
    filter_upwards [h2] with r hr
    rwa [Real.dist_eq] at hr
  obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨δ, hδ, fun r hr hrd x hx => ?_⟩
  have hrm : r ∈ Metric.ball r0 δ ∩ I := ⟨by rwa [Metric.mem_ball, Real.dist_eq], hr⟩
  have hc := hδ' hrm
  obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.1 (hcov (mem_closedBall_zero_iff.2 hx))
  have hcf : c ∈ htfin.toFinset := htfin.mem_toFinset.2 hct
  have h1 := hlip r hr x c
  have h2 := hlip r0 hr0 x c
  have h3 := hc c hcf
  have hxc' : ‖x - c‖ < η := by rwa [Metric.mem_ball, dist_eq_norm] at hxc
  have e1 : L * ‖x - c‖ ≤ L * η := mul_le_mul_of_nonneg_left hxc'.le hL
  have e2 : L * η ≤ ε / 4 := by
    rw [hη, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [abs_lt] at h3
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end Tc2

end HRS.Whole.AppendixA.Phase2SA16R
