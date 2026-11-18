import HRS.MS.SA12X4W2
import HRS.MS.SA12BuildC12
import HRS.MH.ScreenedA3a

/-!
# S.A.12 (SA12X4) W3: the fine-lattice weights are comparable with the unit-lattice cell weights and summable
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- `⟨cellPt z⟩^{-(d+3)} ≤ ⌈√d⌉^{d+3} ⟨latticePt z⟩^{-(d+3)}`. -/
theorem sa12x4_wt_le_cellWeight (hd : 1 ≤ d) (z : Fin d → ℤ) :
    jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) ≤
      (⌈Real.sqrt d⌉ : ℝ) ^ ((d : ℝ) + 3) * cellWeight d z := by
  set κ : ℝ := (⌈Real.sqrt d⌉ : ℝ) with hκ
  have hκ1 : 1 ≤ κ := HRS.MH.AdjointRd.Phase2SA12Construction.sa12c12_kappa_ge hd
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos hκ1
  set p : ℝ := (d : ℝ) + 3 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hj1 : ∀ v : Euc d, 0 < jbracket v := fun v => by unfold jbracket; positivity
  have hc : cellPt d z = κ⁻¹ • latticePt z := rfl
  have hle : jbracket (latticePt z) ≤ κ * jbracket (cellPt d z) := by
    unfold jbracket
    rw [hc, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hκ0)]
    rw [← Real.sqrt_sq hκ0.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ0.le]
    refine Real.sqrt_le_sqrt ?_
    have : κ ^ 2 * (κ⁻¹ * ‖latticePt z‖) ^ 2 = ‖latticePt z‖ ^ 2 := by field_simp
    nlinarith [sq_nonneg ‖latticePt z‖, sq_nonneg κ, mul_nonneg (sq_nonneg κ) (sq_nonneg ((κ⁻¹ * ‖latticePt z‖)))]
  have h2 : jbracket (latticePt z) ^ p ≤ (κ * jbracket (cellPt d z)) ^ p :=
    Real.rpow_le_rpow (hj1 _).le hle hp0
  rw [Real.mul_rpow hκ0.le (hj1 _).le] at h2
  unfold cellWeight
  rw [Real.rpow_neg (hj1 _).le, Real.rpow_neg (hj1 _).le]
  have hA : 0 < jbracket (cellPt d z) ^ p := Real.rpow_pos_of_pos (hj1 _) p
  have hB : 0 < jbracket (latticePt z) ^ p := Real.rpow_pos_of_pos (hj1 _) p
  have hK : 0 < κ ^ p := Real.rpow_pos_of_pos hκ0 p
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hA hB]
  nlinarith [h2]

theorem sa12x4_wt_tsum_lt_top (hd : 1 ≤ d) :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) < ⊤ := by
  set K : ℝ := (⌈Real.sqrt d⌉ : ℝ) ^ ((d : ℝ) + 3) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact Real.rpow_nonneg (by have := HRS.MH.AdjointRd.Phase2SA12Construction.sa12c12_kappa_ge hd; linarith) _
  calc ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3)))
      ≤ ∑' z : Fin d → ℤ, ENNReal.ofReal K * ENNReal.ofReal (cellWeight d z) :=
        ENNReal.tsum_le_tsum fun z => by
          rw [← ENNReal.ofReal_mul hK0]
          exact ENNReal.ofReal_le_ofReal (sa12x4_wt_le_cellWeight hd z)
    _ = ENNReal.ofReal K * ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) := ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (HRS.MH.Screened.cellWeight_tsum_lt_top_proof hd)

end HRS.MH.AdjointRd.Phase2SA12X4
