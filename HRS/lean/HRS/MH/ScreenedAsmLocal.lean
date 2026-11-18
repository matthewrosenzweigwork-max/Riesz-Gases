import HRS.MH.ScreenedS3
import HRS.MH.ScreenedS4
import HRS.MH.ScreenedL1

/-!
# Assemblies `screened_local_global` and `screened_local` (S.B.4(ii))

`screened_local_global_proof`: Fourier packet S3 (`kg_fourier_h_proof`) gives the constant `c > 0` and the
Fourier identity; the representative packet S4 (`kg_rep_of_symbol_proof`) turns it into the global bound.
`screened_local_proof`: `s < d - 1` is `screened_local_lt_proof` (L1); `s ≥ d - 1` is the global bound,
with `C₀ = 0` and the indicator norm dominated by the full norm (`eLpNorm_indicator_le`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

theorem screened_local_global_proof : type_of% @HRS.Whole.screened_local_global := by
  intro d hd s hsd hs1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by linarith
  obtain ⟨c0, hc0, hid⟩ := kg_fourier_h_proof hd hs0 hsd
  exact kg_rep_of_symbol_proof hd hsd hs1 c0 hc0 hid

theorem screened_local_proof : type_of% @HRS.Whole.screened_local := by
  intro d hd s hs0 hsd
  by_cases hs : s < (d : ℝ) - 1
  · obtain ⟨a, A, hA⟩ := screened_local_lt_proof hd hs0 hs
    refine ⟨max a 0, max A 0, fun i ρ hρ c v hsupp hv => ?_⟩
    obtain ⟨w, hw, hbd⟩ := hA i ρ hρ c v hsupp hv
    refine ⟨w, hw, fun c' r' hr' => ?_⟩
    have h1 : ρ ^ a ≤ ρ ^ (max a 0) := Real.rpow_le_rpow_of_exponent_le hρ (le_max_left _ _)
    have h2 : 0 < ρ ^ a := Real.rpow_pos_of_pos (by linarith) a
    have h3 : A ≤ max A 0 := le_max_left _ _
    have h4 : 0 ≤ max A 0 := le_max_right _ _
    have key : A * ρ ^ a ≤ max A 0 * ρ ^ (max a 0) :=
      calc A * ρ ^ a ≤ max A 0 * ρ ^ a := mul_le_mul_of_nonneg_right h3 h2.le
        _ ≤ max A 0 * ρ ^ (max a 0) := mul_le_mul_of_nonneg_left h1 h4
    exact (hbd c' r' hr').trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal key) zero_le)
  · have hs1 : (d : ℝ) - 1 ≤ s := not_lt.mp hs
    have hkg : kgOrder d s = s + 1 - d := by
      unfold kgOrder
      exact max_eq_left (by linarith)
    obtain ⟨c0, hc0, hid⟩ := kg_fourier_h_proof hd hs0 hsd
    obtain ⟨C, hC⟩ := kg_rep_of_symbol_proof hd hsd hs1 c0 hc0 hid
    refine ⟨0, max C 0, fun i ρ _ c v _ hv => ?_⟩
    rw [hkg] at hv ⊢
    obtain ⟨w, hw, _, hnorm⟩ := hC i v hv
    refine ⟨w, hw, fun c' r' _ => ?_⟩
    have hm : MeasurableSet (Metric.closedBall c' r') := measurableSet_closedBall
    have key : C ≤ max C 0 * ρ ^ (0 : ℝ) := by
      rw [Real.rpow_zero, mul_one]
      exact le_max_left _ _
    exact (eLpNorm_indicator_le w hm).trans (hnorm.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal key) zero_le))

end HRS.MH.Screened
