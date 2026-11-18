import HRS.MS.Fp81S21WeightedNorm
import HRS.MS.R2InterpAux10

/-!
Prediction uses `r2Predicted C w z u = windowPathOf m T 0
  (fun t => if t ≤ u then r2PathAt w t else r2Vprop C m t u (z u))`.
Thus the past comes from `w` at time `t`, while the future reads `z u`
at the source time `u`. The definition of `r2Vprop` applies `z u` to
`propagatorW C u t (hermiteFunD α)`. Its normalized coordinates are
`z u (propagatorW C u t (oscTestFun m α))` under the hypotheses of
`s102_Vprop_coord`. These orbits are weighted tests by `s102_orbit_test`;
they are not assumed to be compact smooth tests.

The chart pairing is `inner ℝ z (E.encode f)`. On weighted tests its
norm is bounded by `‖z‖ * (weightedSobolevE r Pw f).toReal`. The compact
smooth dual norm of this action is exactly `ENNReal.ofReal ‖z‖` by
`fp81s21_chartAction_dualNorm`. Extending equality with a physical field
from compact smooth tests to an orbit requires the physical field's
weighted-test linearity and continuity as well as density.

The requested map has type
`C(Set.Icc (0 : ℝ) (L + p.T), r26t6_Coeff) →L[ℝ]
 C(Set.Icc (0 : ℝ) (L + p.T), Window p)`. For `b = max (a-L) 0`,
`θ = a-b`, `h = θ+p.T`, its physical specification must use absolute
source time `b + min v h`, restrict the corresponding global prediction
to `[a,a+p.T]`, and remain constant after `h`. The chart path is read
at the corresponding relative time. The intended uniform bound chooses
`K_pred` after `R,L` and before `a`. The physical identity additionally
requires the weighted field and oscillator past to agree with the chart
action at the relevant times.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp

/-- The chart action extends continuously to every weighted test. -/
theorem fp81s21_chartAction_weighted_bound
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) (f : Euc d → ℝ) (hf : IsR2WeightedTest r Pw f) :
    |fp81s21_chartAction E z f| ≤ ‖z‖ * (weightedSobolevE r Pw f).toReal := by
  unfold fp81s21_chartAction
  rw [← E.norm f hf]
  exact abs_real_inner_le_norm _ _

/-- Every chart action is an admissible weighted functional. -/
theorem fp81s21_chartAction_S102Z
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) : S102Z r Pw (fp81s21_chartAction E z) := by
  refine ⟨?_, ?_, ⟨‖z‖, fp81s21_chartAction_weighted_bound E z⟩⟩
  · intro f g hf hg
    simp [fp81s21_chartAction, E.add f g hf hg, inner_add_right]
  · intro c f hf
    simp [fp81s21_chartAction, E.smul c f hf, inner_smul_right]

#print axioms HRS.Fp81.S21.fp81s21_chartAction_weighted_bound
#print axioms HRS.Fp81.S21.fp81s21_chartAction_S102Z

end HRS.Fp81.S21
