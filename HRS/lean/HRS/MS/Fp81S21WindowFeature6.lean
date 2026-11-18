import HRS.MS.Fp81S21WindowFeature5
import HRS.MS.Fp81S21PosDerivTrace

/-!
# HRS S2.1 packet 15c: positive trace estimate interface

This assembly uses the qualitative S101 envelope for feature regularity and the
separate positive-order window bound for the sharpened trace estimate.  The
positive-order bound is left explicit here so its exponential amplitude and
quantifier order remain visible to packet 15d.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ}

/-- The S101 positive-order trace estimate specialized to the observation
window feature.  `hPos` is the packet 15c exponential estimate consumed by
this assembly. -/
theorem fp81s21_window_feature_trace_bound_pos_of_data
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a v : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (hv : v ∈ Icc (0 : ℝ) (a + H))
    (hD : S101Data C m (a + H) r c)
    (hterminal : ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    {P Bpos : ℝ} {η : (Euc d → ℝ) → ℝ}
    (hP : (d : ℝ) < 2 * P)
    (hη : IsBoundedLinearOnE r P η)
    (hBpos : 0 ≤ Bpos)
    (hPos : ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤ Bpos)
    (Dc : KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ)
    (hDc : ∀ u w, Dc u w =
      η (s101Fm (fp81s21_window_feature C m H a v) (s101Rk u w))) :
    ENNReal.ofReal (HRS.traceNormForm Dc) ≤
      dualNormE r P η *
        ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r * Bpos ^ 2)) := by
  obtain ⟨hreg, hFull⟩ := fp81s21_window_feature_contDiff_full_of_data
    hd hH a ha v hv hD hterminal
  exact fp81s21_s101_trace_bound_pos hP hreg hFull hη hBpos hPos Dc hDc

#print axioms fp81s21_window_feature_trace_bound_pos_of_data

end HRS.Fp81.S21

end
