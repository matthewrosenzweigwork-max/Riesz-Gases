import HRS.MS.R2InterpAux70
import HRS.MS.MovBridgeAux7

/-!
# S10.2 (worker S102), part 71: the standing assumptions `S102Std` and `S102Lin` for the thermal quadratic coefficient
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ}

theorem s102_osc_schwartz (m : ℝ) (α : MultiIndex d) : ∃ f : SchwartzMap (Euc d) ℝ, ⇑f = oscTestFun m α := by
  obtain ⟨ψ, hψ⟩ := HRS.MS.MovOsc.mova3c_hermite_schwartz (d := d) α.degree α rfl
  refine ⟨(oscEigenvalue d α ^ (-(m / 2))) • ψ, ?_⟩
  funext x
  simp [hψ, oscTestFun]

theorem s102_combo_schwartz (m : ℝ) {φ : Euc d → ℝ} (hφ : IsR2DualCombo m φ) :
    ∃ f : SchwartzMap (Euc d) ℝ, ⇑f = φ := by
  obtain ⟨S, c, rfl⟩ := hφ
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by funext x; simp⟩
  | insert a S ha ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨ψ, hψ⟩ := s102_osc_schwartz m a
    refine ⟨(c a) • ψ + g, ?_⟩
    funext x
    have := congrFun hg x
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, hψ, smul_eq_mul, Finset.sum_insert ha, this]

end HRS.MS.R2Interp

end
