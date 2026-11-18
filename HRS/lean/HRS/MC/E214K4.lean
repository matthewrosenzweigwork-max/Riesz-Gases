import HRS.MC.E214K3
import HRS.MD.EQInterpHolder
import HRS.MC.S7PIDMDecay
import HRS.MC.S7PIDIIncr

/-!
# Packet E214K, part 4: log-convexity of the diagonal weights on a single coefficient sequence, and
`vprop_compare_modes_proof` (P2a, basis-vector form)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214K

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final

variable {d : ℕ}

/-- Log-convexity: three elements of `E_{j₁}, E_m, E_{j₂}` with the same Fourier coefficients and the norm bounds
`M w^{-j₁}`, `M w^{-j₂}` at the end levels satisfy the bound `M w^{-m}` at the middle level. -/
theorem norm_interp {j1 m j2 w M : ℝ} (hw : 0 < w) (hM : 0 ≤ M) (h1 : j1 < m) (h2 : m < j2)
    {X : NegSobolev d m} {G1 : NegSobolev d j1} {G2 : NegSobolev d j2}
    (hX : ∀ k, NegSobolev.fourierCoeff X k = NegSobolev.fourierCoeff G1 k)
    (hG2 : ∀ k, NegSobolev.fourierCoeff G2 k = NegSobolev.fourierCoeff G1 k)
    (b1 : ‖G1‖ ≤ M * w ^ (-j1)) (b2 : ‖G2‖ ≤ M * w ^ (-j2)) :
    ‖X‖ ≤ M * w ^ (-m) := by
  set α : ℝ := (m - j1) / (j2 - j1) with hα
  have hd12 : 0 < j2 - j1 := by linarith
  have hα0 : 0 < α := div_pos (by linarith) hd12
  have hα1 : α < 1 := by rw [hα, div_lt_one hd12]; linarith
  have hαe : α * (j2 - j1) = m - j1 := by rw [hα]; field_simp
  have hsq : ∀ x : ℝ, (M * w ^ (-x)) ^ 2 = w ^ (-2 * x) * M ^ 2 := by
    intro x
    rw [mul_pow, ← Real.rpow_natCast (w ^ (-x)) 2, ← Real.rpow_mul hw.le]
    rw [mul_comm]; congr 2; push_cast; ring
  have e1 : HRS.MD.EQInterp.ce m X = HRS.MD.EQInterp.ce m G1 := by
    simp only [HRS.MD.EQInterp.ce]
    rw [show (fun k => NegSobolev.fourierCoeff X k) = fun k => NegSobolev.fourierCoeff G1 k from funext hX]
  have e2 : HRS.MD.EQInterp.ce j2 G1 = HRS.MD.EQInterp.ce j2 G2 := by
    simp only [HRS.MD.EQInterp.ce]
    rw [show (fun k => NegSobolev.fourierCoeff G2 k) = fun k => NegSobolev.fourierCoeff G1 k from funext hG2]
  have hb1 : ENNReal.ofReal (‖G1‖ ^ 2) ≤ ENNReal.ofReal (w ^ (-2 * j1) * M ^ 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hsq]; exact pow_le_pow_left₀ (norm_nonneg _) b1 2
  have hb2 : ENNReal.ofReal (‖G2‖ ^ 2) ≤ ENNReal.ofReal (w ^ (-2 * j2) * M ^ 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hsq]; exact pow_le_pow_left₀ (norm_nonneg _) b2 2
  have hce : ENNReal.ofReal (‖X‖ ^ 2) ≤ ENNReal.ofReal (w ^ (-2 * m) * M ^ 2) := by
    rw [HRS.MD.EQInterp.ofReal_norm_sq_eq_ce, e1]
    calc HRS.MD.EQInterp.ce m G1
        ≤ HRS.MD.EQInterp.ce j1 G1 ^ (1 - α) * HRS.MD.EQInterp.ce j2 G1 ^ α :=
          HRS.MD.EQInterp.ce_holder j1 m j2 α hα0 hα1 hαe G1
      _ = ENNReal.ofReal (‖G1‖ ^ 2) ^ (1 - α) * ENNReal.ofReal (‖G2‖ ^ 2) ^ α := by
          rw [e2, HRS.MD.EQInterp.ofReal_norm_sq_eq_ce, HRS.MD.EQInterp.ofReal_norm_sq_eq_ce]
      _ ≤ ENNReal.ofReal (w ^ (-2 * j1) * M ^ 2) ^ (1 - α) *
            ENNReal.ofReal (w ^ (-2 * j2) * M ^ 2) ^ α := by
          gcongr
      _ = ENNReal.ofReal (w ^ (-2 * m) * M ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hα0.le,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [HRS.MD.EQInterp.holder_term w M α j1 m j2 hw hα0 hα1 hαe]
  have hX2 : ‖X‖ ^ 2 ≤ w ^ (-2 * m) * M ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hce
  have hnn : 0 ≤ M * w ^ (-m) := mul_nonneg hM (Real.rpow_nonneg hw.le _)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).mp ?_
  rw [hsq]; exact hX2

end HRS.MC.E214K

end
