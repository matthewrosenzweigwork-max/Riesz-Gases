import HRS.MS.Fp81S21MovingHeat
import HRS.MS.R2InterpAux22

/-!
# Moving heat regularity along continuous prediction paths

The future is the witness supplied by the moving Lipschitz-projection theorem.  The
projected derivative below evaluates the derivative of the test at the projected point;
it does not insert projections in the derivative arguments.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Sec7 HRS.MS.R26T3 HRS.MS.R2Interp

/-- The selected moving future has the projection, time-continuity and spatial heat
regularity needed along continuous prediction curves, on every positive horizon. -/
theorem fp81s21_moving_heat_regularity (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ future : (H : ℝ) → ℝ →
            Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
          (∀ H v, IsProbabilityMeasure (future H v)) ∧
          (∀ H : ℝ, 0 < H → ∀ v ∈ Icc (0 : ℝ) H,
            IsR2FutureGaussian (r26t3_coeff R)
              (wholeSpaceIndex p.d : ℝ) H v (future H v)) ∧
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
              ∀ (Y : ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) H), ContinuousOn Y (Icc 0 H) →
              ∀ j : ℕ, j ≤ 2 →
              ContinuousOn (fun τ => iteratedFDeriv ℝ j (r2HeatFn (future H) Φ τ) (Y τ)) (Icc 0 H) ∧
              (∀ L, ContinuousOn (fun τ => s102_projHeatD (future H) Φ (s102_Pj H hH L) j τ (Y τ)) (Icc 0 H)) ∧
              ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ τ ∈ Icc (0 : ℝ) H,
                ‖s102_projHeatD (future H) Φ (s102_Pj H hH L) j τ (Y τ) -
                  iteratedFDeriv ℝ j (r2HeatFn (future H) Φ τ) (Y τ)‖ ≤ ε) ∧
            (∀ (Φ : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → ℝ), MemCb 5 Φ →
              ∀ u : ℝ, ContDiff ℝ 5 (r2HeatFn (future H) Φ u) ∧
              ∀ j ≤ 5, ∀ y,
                iteratedFDeriv ℝ j (r2HeatFn (future H) Φ u) y =
                  ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂(future H u) ∧
                ‖iteratedFDeriv ℝ j (r2HeatFn (future H) Φ u) y‖ ≤
                  ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖)) := by
  obtain ⟨δ0, hδ0, hδ0half, hfamily⟩ := fp81s21_moving_heat_lipProj p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨future, hprob, hgauss, hlip⟩ := hfamily δ hδ hδle R
  refine ⟨future, hprob, hgauss, hlip, ?_⟩
  intro H hH
  obtain ⟨hP1, hconv, htensor⟩ :=
    s102_projection_strong (d := p.d) (wholeSpaceIndex p.d : ℝ) H hH
  refine ⟨hP1, hconv, htensor, ?_, ?_⟩
  · intro Φ hΦ Y hY j hj
    exact s102_conv_equicont (future H) (hprob H) (fun L => s102_Pj H hH L)
      hP1 hconv (hlip H hH) hΦ Y hY j hj
  · intro Φ hΦ u
    letI : IsProbabilityMeasure (future H u) := hprob H u
    exact s102_r2HeatFn_derivs (future H) u hΦ

#print axioms HRS.Fp81.S21.fp81s21_moving_heat_regularity

end HRS.Fp81.S21

end
