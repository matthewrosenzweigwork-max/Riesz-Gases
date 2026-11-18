import HRS.MS.S111K4J01C

/-!
# S11.1 / J01 piece: the B04 drift structure for the forcing of every `L¹` coefficient path (S11K4)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem zq_drift {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {C : WholeCoeff d} {c0 S T u : ℝ}
    {b : MultiIndex d → ℝ} (hPw : (d : ℝ) / 2 + 1 < Pw) (hT : 0 < T) (hc0 : 0 < c0) (hu : 0 ≤ u)
    (hbs : Summable fun α => b α ^ 2) (hbS : (∑' α, b α ^ 2) ≤ S)
    (hW : S111k2WindowOrbitInput C (wholeSpaceIndex d : ℝ) c0 r b)
    (hco : ChartedOrbits E C (wholeSpaceIndex d : ℝ) (u + T)) (q : TimeCoeff (u + T)) :
    S111k2Drift C (wholeSpaceIndex d : ℝ) c0 r b S T u Pw (zq E q) := by
  refine ⟨hW, hc0, hT, hu, hbs, hbS, by linarith, zq_L1F E q, ?_, fun v _ => zq_mass E q v⟩
  intro t ht phi hphi
  have ht0 : t ∈ Set.Icc (0 : ℝ) (u + T) := ⟨hu.trans ht.1, ht.2⟩
  have h := hco.2 t ht0 phi hphi
  exact ((qr_sm E q).aestronglyMeasurable.inner h).aemeasurable

end HRS.MS.S111K4J01
