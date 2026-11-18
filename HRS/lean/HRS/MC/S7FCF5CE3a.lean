import HRS.MC.S7FCDefs
import HRS.Energy.Modulated
import HRS.Sections.AllTimeAux1

/-!
# Proof of `fcf5_E3a_zeta_decomp` (packet fcf5c, E3a of `S7FCF5Plan.lean`)

`ζ = η - E η` at a fixed time `t ≥ 0`: with `μ = μ^t = withDensityReal (R.ρ t)` and `Q = P.map (X_t)`,
the mean `E η^t = √N • ofMeasureDiff r (meanEmpirical Q) μ` (pushforward along `X_t` and the honest Bochner integral
`integral_ofMeasureDiff_empirical`), and the coordinatewise identity
`ofMeasureDiff (empirical x) μ = ofMeasureDiff (empirical x) (meanEmpirical Q) + ofMeasureDiff (meanEmpirical Q) μ`.
No file of this packet imports a sorried module.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5C

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

theorem fcf5_E3a_zeta_decomp_proof (R : Regime d) (r : ℝ) (hr : (d : ℝ) < 2 * r) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hX : ∀ t : ℝ≥0, Measurable (X t)) (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    zetaE r (P.map (X t.toNNReal)) (X t.toNNReal ω) =
      etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t)) -
        ∫ ω', etaE r (X t.toNNReal ω') (withDensityReal (R.ρ t)) ∂P := by
  have hρ : IsProbDensity (R.ρ t) := (alltime_traj R t).mf.density t ⟨ht, le_rfl⟩
  haveI : IsProbabilityMeasure (withDensityReal (R.ρ t)) := isProb_withDensityReal hρ
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    (Measure.isProbabilityMeasure_map_iff (hX t.toNNReal).aemeasurable).2 inferInstance
  have hF := measurable_ofMeasureDiff_empirical hr (withDensityReal (R.ρ t)) hN
  have hmean := integral_ofMeasureDiff_empirical hr (P.map (X t.toNNReal))
    (withDensityReal (R.ρ t)) hN hF.aemeasurable
  have hint : ∫ ω', etaE r (X t.toNNReal ω') (withDensityReal (R.ρ t)) ∂P =
      Real.sqrt N • NegSobolev.ofMeasureDiff r (meanEmpirical (P.map (X t.toNNReal)))
        (withDensityReal (R.ρ t)) := by
    have h1 : (fun ω' => etaE r (X t.toNNReal ω') (withDensityReal (R.ρ t))) =
        fun ω' => Real.sqrt N •
          NegSobolev.ofMeasureDiff r (empirical (X t.toNNReal ω')) (withDensityReal (R.ρ t)) := rfl
    rw [h1, integral_smul, ← hmean,
      integral_map (hX t.toNNReal).aemeasurable hF.aestronglyMeasurable]
  haveI := empirical_isProbabilityMeasure hN (X t.toNNReal ω)
  haveI := isProbabilityMeasure_meanEmpirical (P.map (X t.toNNReal)) hN
  have hadd := NegSobolev.ofMeasureDiff_add hr (empirical (X t.toNNReal ω))
    (meanEmpirical (P.map (X t.toNNReal))) (withDensityReal (R.ρ t))
  rw [hint]
  unfold zetaE etaE flucE
  rw [← smul_sub]
  congr 1
  rw [hadd]
  abel

end HRS.MC.Sec7.S7FCF5C

end
