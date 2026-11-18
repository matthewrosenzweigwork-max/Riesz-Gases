import HRS.MP.SelfSimP5Core
import HRS.MP.SelfSimP5DsHyp

/-!
# P5 interface lemma (8) `ss5_dissipation_core` for `ι = Fin N`

Proved from `HRS.MP.SelfSimP5Core.p4_core_cpt` (the P4 level chain on `EucConfig 1 N`) by transport along the
linear isometric (up to the sup norm) volume-preserving equivalence `e : EuclideanSpace ℝ (Fin N) ≃ EucConfig 1 N`,
`(e z) k = single 0 (z k)`.  Helpers `p5d_*`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSimP4 HRS.MP.SelfSimP5
  HRS.MP.SelfSimP5Core
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Ds

/-- `ss5_dissipation_core` for `ι = Fin N`. -/
theorem ss5_dissipation_core_proof {N : ℕ} {U : EuclideanSpace ℝ (Fin N) → ℝ} (hU : ContDiff ℝ 2 U)
    {K : ℝ≥0} (hK : LipschitzWith K (gradient U)) (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * ‖z‖ ^ 2 - C ≤ U z)
    {θ : ℝ} (hθ : 0 < θ) {μ : ℝ → Measure (EuclideanSpace ℝ (Fin N))}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (μ t)) {T : ℝ} (hT : 0 ≤ T)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂(μ t) ≤ M)
    (hnar : ∀ g : EuclideanSpace ℝ (Fin N) → ℝ, Continuous g → (∃ C : ℝ, ∀ z, |g z| ≤ C) →
      ContinuousOn (fun t => ∫ z, g z ∂(μ t)) (Icc (0 : ℝ) T))
    (hfp : ss5_WeakFP θ U μ) (hfin : ss5_ent θ U (μ 0) < ⊤) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ss5_ent θ U (μ t) + ((ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, ss5_fish θ U (μ r) : ℝ≥0∞) : EReal)
        ≤ ss5_ent θ U (μ 0) := by
  have hV := p5d_potHyp hU hK hconf T
  have hμ := p5d_flowHyp hU hprob hmom hnar hfp
  haveI := hprob 0 le_rfl
  have hent : ∀ t, 0 ≤ t → gibbsEntropyW (p4GibbsOf θ (p5d_V U)) (p5d_mu μ t) = ss5_ent θ U (μ t) :=
    fun t ht => by
      haveI := hprob t ht
      rw [p5d_mu_of_nonneg μ ht, ← p5d_ent]
  have hfin' : gibbsEntropyW (p4GibbsOf θ (p5d_V U)) (p5d_mu μ 0) < ⊤ := by
    rw [hent 0 le_rfl]
    exact hfin
  intro t ht
  have h := HRS.MP.SelfSimP5Core.p4_core_cpt_proof hθ hT hV hμ hfin' t ht
  rw [hent t ht.1, hent 0 le_rfl] at h
  have hF : ∫⁻ r in Icc (0 : ℝ) t, fisherCptW (p4GibbsOf θ (p5d_V U)) (p5d_mu μ r) =
      ∫⁻ r in Icc (0 : ℝ) t, ss5_fish θ U (μ r) := by
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    haveI := hprob r hr.1
    rw [p5d_mu_of_nonneg μ hr.1, ← p5d_fish (hU.differentiable (by norm_num))]
  rw [hF] at h
  exact h

example {N : ℕ} := (@ss5_dissipation_core_proof N :
  type_of% (@HRS.MP.SelfSimP5.ss5_dissipation_core (Fin N) _ _))

end HRS.MP.SelfSimP5Ds
