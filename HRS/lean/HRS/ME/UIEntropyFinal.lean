import HRS.ME.UIEntropy
import HRS.MD.EQLawFlow
import HRS.Sections.Sec5

/-!
# Proposition 5.10, last sentence: the entropy bound implies uniform integrability

Proof of the repaired statement of `HRS.ui_of_entropy_bound` (ISSUES `ME: ME-R6`): the frozen statement carries no
hypotheses on `d`, `s`, `V`, `β`, so `canonicalGibbs` may be a junk measure (non-measurable `V`, `β < 0`, a non-integrable
Boltzmann weight); the repair adds the hypotheses of the surrounding Proposition 5.10 (`2 ≤ d`, `0 ≤ s < d`, smooth `V`,
`0 < β`), under which `canonicalGibbs` is a probability measure (`HRS.MD.EQLawFlow.eqlaw_gibbs_prob`).  The tail estimate is
`HRS.ME.UIEntropy.ui_tail_of_relEntropy` applied to each `n`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.ME.UIEntropyFinal

variable {d : ℕ}

theorem ui_of_entropy_bound_proof (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ν : ∀ n : ℕ, Measure (Config d (n + 2)))
    (hν : ∀ n, IsProbabilityMeasure (ν n)) (H₀ : ℝ)
    (hH : ∀ n, relEntropy (ν n) (canonicalGibbs (periodicRiesz d s) V (n + 2) β) ≤
      ENNReal.ofReal H₀) :
    (∀ L : ℝ, 1 < L → uiTail d s β V ν L ≤ ENNReal.ofReal ((H₀ + Real.exp (-1)) / Real.log L)) ∧
      Tendsto (uiTail d s β V ν) atTop (𝓝 0) := by
  have hP : ∀ n, IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V (n + 2) β) := fun n =>
    HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega)
  have hb : ∀ L : ℝ, 1 < L → uiTail d s β V ν L ≤ ENNReal.ofReal ((H₀ + Real.exp (-1)) / Real.log L) := by
    intro L hL
    unfold uiTail
    refine iSup_le fun n => ?_
    haveI := hν n
    haveI := hP n
    exact (HRS.ME.UIEntropy.ui_tail_of_relEntropy (ν n) _ H₀ L hL (hH n)).2
  refine ⟨hb, ?_⟩
  have hlim : Tendsto (fun L : ℝ => ENNReal.ofReal ((H₀ + Real.exp (-1)) / Real.log L)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => (H₀ + Real.exp (-1)) / Real.log L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim (Eventually.of_forall fun L => bot_le) ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL using hb L hL

end HRS.ME.UIEntropyFinal
