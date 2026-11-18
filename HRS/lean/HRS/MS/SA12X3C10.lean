import HRS.MS.SA12X3C10E

/-!
# S.A.12 C10 (SA12X3): `moving_uloc_equivalence`

The moving cell supremum on the fine lattice and the literal Fourier uloc norm are equivalent
(`sa12x3_cellEnergy_le_uloc` for the upper bound and `sa12x3_piece_le_cellSup` for the lower bound).
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

theorem sa12x3_sq_to_sqrt {X Y : ℝ≥0∞} {K : ℝ} (hK : 0 < K) (h : X ^ 2 ≤ ENNReal.ofReal K * Y) :
    X ≤ ENNReal.ofReal (Real.sqrt K) * Y ^ (1 / 2 : ℝ) := by
  calc X = (X ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ ≤ (ENNReal.ofReal K * Y) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal K ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg hK.le (by norm_num), Real.sqrt_eq_rpow]

end HRS.MH.AdjointRd.Phase2SA12Near

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem moving_uloc_equivalence (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T, ∀ u : Euc d → ℝ, BddJets m u →
        ENNReal.ofReal c₁ * ulocNormE m χ u ≤ (cellSup m χ Ψ τ u) ^ (1 / 2 : ℝ) ∧
        (cellSup m χ Ψ τ u) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c₂ * ulocNormE m χ u := by
  obtain ⟨K1, hK1, h1⟩ := sa12x3_piece_le_cellSup hd m Cb T χ χh hχ
  obtain ⟨K2, hK2, h2⟩ := sa12x3_cellEnergy_le_uloc hd m Cb T χ χh hχ
  refine ⟨(Real.sqrt K1)⁻¹, Real.sqrt K2, by positivity, Real.sqrt_pos.2 hK2, ?_⟩
  intro b Ψ hb hΨ τ hτ u hu
  constructor
  · have hU : ulocNormE m χ u ≤ ENNReal.ofReal (Real.sqrt K1) * (cellSup m χ Ψ τ u) ^ (1 / 2 : ℝ) := by
      unfold ulocNormE
      refine iSup_le fun c => ?_
      exact sa12x3_sq_to_sqrt hK1 (h1 b Ψ hb hΨ τ hτ u hu.1 c)
    calc ENNReal.ofReal (Real.sqrt K1)⁻¹ * ulocNormE m χ u
        ≤ ENNReal.ofReal (Real.sqrt K1)⁻¹ * (ENNReal.ofReal (Real.sqrt K1) * (cellSup m χ Ψ τ u) ^ (1 / 2 : ℝ)) :=
          by gcongr
      _ = (cellSup m χ Ψ τ u) ^ (1 / 2 : ℝ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (Real.sqrt_pos.2 hK1).ne',
            ENNReal.ofReal_one, one_mul]
  · have hS : cellSup m χ Ψ τ u ≤ ENNReal.ofReal K2 * ulocNormE m χ u ^ 2 := by
      unfold cellSup
      exact iSup_le fun z => h2 b Ψ hb hΨ τ hτ u hu.1 (cellPt d z)
    calc (cellSup m χ Ψ τ u) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal K2 * ulocNormE m χ u ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hS (by norm_num)
      _ = ENNReal.ofReal K2 ^ (1 / 2 : ℝ) * (ulocNormE m χ u ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt K2) * ulocNormE m χ u := by
          rw [ENNReal.ofReal_rpow_of_nonneg hK2.le (by norm_num), Real.sqrt_eq_rpow]
          congr 1
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

end HRS.MH.AdjointRd.Phase2SA12Construction
