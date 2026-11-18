import HRS.MS.Fp81S21MovingHeat2
import HRS.MS.Fp81S21InitialWindow
import HRS.MS.R2InterpAux4

/-!
# HRS S2.1(iii), packet 12c: moving heat regularity on observation windows

This file carries the selected 12a/12b full-horizon heat family through the
physical restriction map.  The restricted laws are probabilities, and hence
their heat functions have the generic `C^5` derivative formulas.  Projected
convergence on a window is deliberately not asserted here: `s102_conv_equicont`
needs an `S102LipProj` bound for the restricted family and the local projection
family, which does not follow just by mapping the full-horizon laws.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Sec7 HRS.MS.R26T3 HRS.MS.R2Interp

/-- The complete full-horizon regularity clause supplied by 12a and 12b,
with its selected future kept as an explicit argument. -/
abbrev fp81s21_moving_heat_full_clause (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H)) : Prop :=
  (∀ H v, IsProbabilityMeasure (future H v)) ∧
  (∀ H : ℝ, 0 < H → ∀ v ∈ Icc (0 : ℝ) H,
    IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H v (future H v)) ∧
  (∀ H : ℝ, ∀ hH : 0 < H,
    S102LipProj (future H) (fun L => s102_Pj H hH L)) ∧
  (∀ H : ℝ, ∀ hH : 0 < H,
    (∀ L, ‖(s102_Pj H hH L : OscPath p.d (wholeSpaceIndex p.d : ℝ) H →L[ℝ]
      OscPath p.d (wholeSpaceIndex p.d : ℝ) H)‖ ≤ 1) ∧
    (∀ w : OscPath p.d (wholeSpaceIndex p.d : ℝ) H,
      Tendsto (fun L => s102_Pj H hH L w) atTop (𝓝 w)) ∧
    (∀ (j : ℕ) (v : TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) j),
      v ∈ projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) j →
      Tendsto (fun L => tensorPow j (s102_Pj H hH L) v) atTop (𝓝 v)) ∧
    (∀ (Φ : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → ℝ), MemCb 5 Φ →
      ∀ (Y : ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
      ContinuousOn Y (Icc 0 H) → ∀ j : ℕ, j ≤ 2 →
      ContinuousOn
        (fun τ => iteratedFDeriv ℝ j (r2HeatFn (future H) Φ τ) (Y τ)) (Icc 0 H) ∧
      (∀ L, ContinuousOn
        (fun τ => s102_projHeatD (future H) Φ (s102_Pj H hH L) j τ (Y τ)) (Icc 0 H)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ τ ∈ Icc (0 : ℝ) H,
        ‖s102_projHeatD (future H) Φ (s102_Pj H hH L) j τ (Y τ) -
          iteratedFDeriv ℝ j (r2HeatFn (future H) Φ τ) (Y τ)‖ ≤ ε) ∧
    (∀ (Φ : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → ℝ), MemCb 5 Φ →
      ∀ u : ℝ, ContDiff ℝ 5 (r2HeatFn (future H) Φ u) ∧
      ∀ j ≤ 5, ∀ y,
        iteratedFDeriv ℝ j (r2HeatFn (future H) Φ u) y =
          ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂(future H u) ∧
        ‖iteratedFDeriv ℝ j (r2HeatFn (future H) Φ u) y‖ ≤
          ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖))

/-- Restricting any member of a selected future family to a physical window
preserves its probability mass. -/
theorem fp81s21_windowFuture_isProbability
    {p : Parameters}
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : ∀ H v, IsProbabilityMeasure (future H v))
    (b : ℝ) (hb : 0 ≤ b) (v : ℝ) :
    IsProbabilityMeasure (windowFuture future b hb v) := by
  change IsProbabilityMeasure
    (Measure.map
      (HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
        (H := b + p.T) hb le_rfl)
      (future (b + p.T) v))
  apply (Measure.isProbabilityMeasure_map_iff
    ((HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
      (H := b + p.T) hb le_rfl).continuous.measurable.aemeasurable)).2
  exact hfuture (b + p.T) v

/-- The restricted future has the generic `C^5` heat derivative formulas on
`Window p`, at every heat parameter. -/
theorem fp81s21_windowFuture_heat_derivs
    {p : Parameters}
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : ∀ H v, IsProbabilityMeasure (future H v))
    (b : ℝ) (hb : 0 ≤ b) (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ) (u : ℝ) :
    ContDiff ℝ 5 (r2HeatFn (windowFuture future b hb) Φ u) ∧
    ∀ j ≤ 5, ∀ y,
      iteratedFDeriv ℝ j (r2HeatFn (windowFuture future b hb) Φ u) y =
        ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂(windowFuture future b hb u) ∧
      ‖iteratedFDeriv ℝ j (r2HeatFn (windowFuture future b hb) Φ u) y‖ ≤
        ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ := by
  letI : IsProbabilityMeasure (windowFuture future b hb u) :=
    fp81s21_windowFuture_isProbability future hfuture b hb u
  exact s102_r2HeatFn_derivs (windowFuture future b hb) u hΦ

/-- The selected future from packet 12 has all 12a/12b clauses, and its
physical window restrictions are probabilities with `C^5` heat derivative
bounds.  The theorem exposes the exact completed restriction-level portion of
12c; projected-derivative convergence on windows remains a separate producer. -/
theorem fp81s21_moving_heat_family_window_derivs (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ future : (H : ℝ) → ℝ →
            Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
          fp81s21_moving_heat_full_clause p R future ∧
          (∀ b : ℝ, ∀ hb : 0 ≤ b, ∀ v : ℝ,
            IsProbabilityMeasure (windowFuture future b hb v)) ∧
          (∀ b : ℝ, ∀ hb : 0 ≤ b,
            ∀ (Φ : Window p → ℝ), MemCb 5 Φ → ∀ u : ℝ,
              ContDiff ℝ 5 (r2HeatFn (windowFuture future b hb) Φ u) ∧
              ∀ j ≤ 5, ∀ y,
                iteratedFDeriv ℝ j (r2HeatFn (windowFuture future b hb) Φ u) y =
                  ∫ z, iteratedFDeriv ℝ j Φ (y + z)
                    ∂(windowFuture future b hb u) ∧
                ‖iteratedFDeriv ℝ j
                    (r2HeatFn (windowFuture future b hb) Φ u) y‖ ≤
                  ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) := by
  obtain ⟨δ0, hδ0, hδ0half, hfamily⟩ := fp81s21_moving_heat_regularity p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨future, hprob, hgauss, hlip, hregularity⟩ :=
    hfamily δ hδ hδle R
  refine ⟨future, ?_, ?_, ?_⟩
  · exact ⟨hprob, hgauss, hlip, hregularity⟩
  · intro b hb v
    exact fp81s21_windowFuture_isProbability future hprob b hb v
  · intro b hb Φ hΦ u
    exact fp81s21_windowFuture_heat_derivs future hprob b hb Φ hΦ u

#print axioms HRS.Fp81.S21.fp81s21_windowFuture_isProbability
#print axioms HRS.Fp81.S21.fp81s21_windowFuture_heat_derivs
#print axioms HRS.Fp81.S21.fp81s21_moving_heat_family_window_derivs

end HRS.Fp81.S21

end
