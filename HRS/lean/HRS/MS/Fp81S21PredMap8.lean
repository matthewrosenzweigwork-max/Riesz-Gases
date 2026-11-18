import HRS.MS.Fp81S21PredMap7
import HRS.MS.R2InterpAux129

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

/-- The charted propagated distribution is continuous in its source time
when the terminal time is fixed. -/
theorem fp81s21_chartVprop_source_cont
    {d r : ℕ} {Pw m T : ℝ} {C : WholeCoeff d} {c : MultiIndex d → ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c)
    (hlin : S102Lin C m T) (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) T) :
    ContinuousOn (fun u => r2Vprop C m q u (fp81s21_chartAction E z)) (Icc 0 q) := by
  have hZ : ∀ u ∈ Icc (0 : ℝ) T,
      S102Z r Pw (fp81s21_chartAction E z) := by
    intro u hu
    exact fp81s21_chartAction_S102Z E z
  have hM : ∀ u ∈ Icc (0 : ℝ) T, ∀ f : Euc d → ℝ,
      IsR2WeightedTest r Pw f →
      |fp81s21_chartAction E z f| ≤ ‖z‖ * (weightedSobolevE r Pw f).toReal := by
    intro u hu f hf
    exact fp81s21_chartAction_weighted_bound E z f hf
  have hc : ∀ α : MultiIndex d,
      ContinuousOn (fun u => fp81s21_chartAction E z
        (propagatorW C u q (oscTestFun m α))) (Icc 0 q) := by
    intro α
    simpa only [fp81s21_chartAction] using
      (continuousOn_const.inner (fp81s21_chartOrbit_source_cont hP hD E hq α))
  exact s102_V_slice_cont (M := ‖z‖) hP hD hlin hZ hM hq hc

#print axioms HRS.Fp81.S21.fp81s21_chartVprop_source_cont

end HRS.Fp81.S21
