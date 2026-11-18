import HRS.MC.S7FCW12E

/-!
# FC-E start-`a` packet, part B: the centred particle quadratic field for every start `a` (prefix `S7FCF5E_`)

* `S7FCF5E_aemeasurable_quadField`: `ω ↦ toL2 r T (t ↦ quadFieldAt r s μ^· P X (a+t) ω)` is `AEMeasurable` for every
  `a ≥ 0`.  The centred field is handled by `s7fcw12_centred_aemeasurable` with the time-shifted process
  `Y t ω = X (a+t) ω` and the shifted kernel `Ψ t x = quadFieldTilde (μ^{a+t}) x`; on `[0,T]` the shifted time
  `a + t` is `≥ 0`, so `s7fcw12_rhoPos_eq` identifies the density with `R.ρ (a+t)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCW12

namespace HRS.MC.Sec7.S7FCF5E

variable {d : ℕ}

/-- The centred particle quadratic field of the window `a + ·` is `AEMeasurable` in `ω` (`L²([0,T];E_r)`-valued). -/
theorem S7FCF5E_aemeasurable_quadField (R : Regime d) (r : ℝ) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    AEMeasurable (fun ω => HRS.Sec7.toL2 r T
      (fun t => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (a + t) ω)) P := by
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X (a + t).toNNReal ω) (Set.Icc 0 T) :=
    hcont.mono fun ω hω =>
      (continuous_pi fun i => (hω i).comp
        (continuous_real_toNNReal.comp (continuous_const.add continuous_id))).continuousOn
  have hfq : Measurable fun q : ℝ × Config d N => ((a + q.1, q.2) : ℝ × Config d N) :=
    (measurable_const.add measurable_fst).prodMk measurable_snd
  have hΨ : Measurable fun q : ℝ × Config d N =>
      quadFieldTilde r R.D.s (withDensityReal fun y => s7fcw12_rhoPos R (a + q.1, y)) q.2 := by
    have key := (HRS.MC.Sec7.S7FCW12.s7fcw12_quadTilde_measurable R r).comp hfq
    exact key
  refine HRS.MC.Sec7.S7FCW12.s7fcw12_centred_aemeasurable hT P (fun t ω => X (a + t).toNNReal ω)
    (fun t => hadapt _) hc (fun _ => 0)
    (fun t x => quadFieldTilde r R.D.s (withDensityReal fun y => s7fcw12_rhoPos R (a + t, y)) x)
    hΨ (fun t ω => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (a + t) ω) ?_
  intro t ht ω
  have hat : 0 ≤ a + t := add_nonneg ha ht.1
  have hμ : withDensityReal (R.ρ (a + t)) = withDensityReal fun y => s7fcw12_rhoPos R (a + t, y) := by
    congr 1
    funext y
    rw [s7fcw12_rhoPos_eq R hat y]
  simp only [quadFieldAt, hμ]

end HRS.MC.Sec7.S7FCF5E

end
