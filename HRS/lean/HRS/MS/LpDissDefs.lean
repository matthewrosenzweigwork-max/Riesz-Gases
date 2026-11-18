import HRS.Whole.AppendixAAdjoint

/-!
# S.A.16 cutoff companions (definitions only)

Literal cutoff companions of the frozen `fracLap` and `dissipationDensity`; no normalization is added.
Namespace `HRS.Whole.AppendixA.BreakdownSA16`, prefix `sa16bd_`.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA

universe u

namespace HRS.Whole.AppendixA.BreakdownSA16

def sa16bd_convexityConst (p : ℝ) : ℝ :=
  (4 : ℝ) ^ (2 - p) / 32

def sa16bd_lapCut (d : ℕ) (θ ε : ℝ) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ z in {z : Euc d | ε < ‖z‖},
    (f x - f (x - z)) / ‖z‖ ^ ((d : ℝ) + θ)

def sa16bd_dissCut {ι : Type u} [Fintype ι] (d : ℕ) (θ p ε : ℝ)
    (W : Euc d → ι → ℝ) (x : Euc d) : ℝ≥0∞ :=
  ∫⁻ z in {z : Euc d | ε < ‖z‖},
    ENNReal.ofReal ((vnorm (W x) + vnorm (W (x - z))) ^ (p - 2) *
      vnorm (fun i => W x i - W (x - z) i) ^ 2 / ‖z‖ ^ ((d : ℝ) + θ))

end HRS.Whole.AppendixA.BreakdownSA16
