import HRS.Whole.Adjoint
import HRS.MS.SuppU8Aux17
import HRS.MS.SuppU8Aux7

/-!
# Worker U8 aux 18: from `decayNormE` to operator-norm decay bounds
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

theorem u8_jbracket_bound (x : Euc d) : 1 + ‖x‖ ≤ Real.sqrt 2 * jbracket x := by
  unfold jbracket
  rw [← Real.sqrt_mul (by norm_num)]
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (‖x‖ - 1)]

/-- Constant of the conversion. -/
def u8_Cconv (d k : ℕ) (b : ℝ) : ℝ := (d : ℝ) ^ k * Real.sqrt 2 ^ (b + k)

theorem u8_Cconv_nonneg (d k : ℕ) (b : ℝ) : 0 ≤ u8_Cconv d k b := by
  unfold u8_Cconv; positivity

theorem u8_conv (hd : 1 ≤ d) (k : ℕ) (bexp : ℝ) (hb : 0 ≤ bexp) (v : Euc d → ℝ)
    (h : decayNormE k bexp v < ⊤) :
    ∀ j ≤ k, ∀ x : Euc d, ‖iteratedFDeriv ℝ j v x‖ ≤
      ((decayNormE k bexp v).toReal * u8_Cconv d k bexp) * (1 + ‖x‖) ^ (-(bexp + j)) := by
  intro j hj x
  set N := (decayNormE k bexp v).toReal with hN
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hjb : 0 < jbracket x := by unfold jbracket; positivity
  have hcoord : ∀ r : Fin j → Fin d,
      jbracket x ^ (bexp + j) * |iteratedFDeriv ℝ j v x (fun l => EuclideanSpace.single (r l) 1)| ≤ N := by
    intro r
    have h1 : ENNReal.ofReal (jbracket x ^ (bexp + (j : ℝ)) * |partialDeriv r v x|) ≤
        decayNormE k bexp v := by
      unfold decayNormE derivSupE
      exact le_iSup_of_le (⟨j, by omega⟩ : Fin (k + 1)) (le_iSup_of_le r (le_iSup_of_le x le_rfl))
    exact (ENNReal.ofReal_le_iff_le_toReal h.ne).1 h1
  have hop := HRS.U8.u8_opnorm_le j (iteratedFDeriv ℝ j v x)
  have hjpow : 0 < jbracket x ^ (bexp + j) := Real.rpow_pos_of_pos hjb _
  have hterm : ∀ r : Fin j → Fin d,
      |iteratedFDeriv ℝ j v x (fun l => EuclideanSpace.single (r l) 1)| ≤
        N * jbracket x ^ (-(bexp + j)) := by
    intro r
    have := hcoord r
    rw [Real.rpow_neg hjb.le]
    rw [← div_eq_mul_inv, le_div_iff₀ hjpow]
    linarith
  have hsum : ∑ r : Fin j → Fin d,
      |iteratedFDeriv ℝ j v x (fun l => EuclideanSpace.single (r l) 1)| ≤
      (d : ℝ) ^ j * (N * jbracket x ^ (-(bexp + j))) := by
    calc _ ≤ ∑ r : Fin j → Fin d, N * jbracket x ^ (-(bexp + j)) := Finset.sum_le_sum (fun r _ => hterm r)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        simp
  have hjb2 : jbracket x ^ (-(bexp + j)) ≤ Real.sqrt 2 ^ (bexp + j) * (1 + ‖x‖) ^ (-(bexp + j)) := by
    have hle : (1 + ‖x‖) / Real.sqrt 2 ≤ jbracket x := by
      rw [div_le_iff₀ (by linarith)]
      have := u8_jbracket_bound x
      linarith
    have h1 : jbracket x ^ (-(bexp + j)) ≤ ((1 + ‖x‖) / Real.sqrt 2) ^ (-(bexp + j)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hle (by
        have : (0 : ℝ) ≤ j := by positivity
        linarith)
    rw [HRS.U8.u8_rpow_div _ _ _ (by positivity) (by linarith), neg_neg] at h1
    linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow1 : (d : ℝ) ^ j ≤ (d : ℝ) ^ k := pow_le_pow_right₀ hd1 hj
  have hpow2 : Real.sqrt 2 ^ (bexp + (j : ℝ)) ≤ Real.sqrt 2 ^ (bexp + (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hs2 (by
      have : (j : ℝ) ≤ k := by exact_mod_cast hj
      linarith)
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  calc ‖iteratedFDeriv ℝ j v x‖ ≤ ∑ r : Fin j → Fin d,
        |iteratedFDeriv ℝ j v x (fun l => EuclideanSpace.single (r l) 1)| := hop
    _ ≤ (d : ℝ) ^ j * (N * jbracket x ^ (-(bexp + j))) := hsum
    _ ≤ (d : ℝ) ^ j * (N * (Real.sqrt 2 ^ (bexp + j) * (1 + ‖x‖) ^ (-(bexp + j)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hjb2 hN0
    _ = ((d : ℝ) ^ j * Real.sqrt 2 ^ (bexp + j)) * N * (1 + ‖x‖) ^ (-(bexp + j)) := by ring
    _ ≤ ((d : ℝ) ^ k * Real.sqrt 2 ^ (bexp + k)) * N * (1 + ‖x‖) ^ (-(bexp + j)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hN0
        exact mul_le_mul hpow1 hpow2 (by positivity) (by positivity)
    _ = (N * u8_Cconv d k bexp) * (1 + ‖x‖) ^ (-(bexp + j)) := by
        unfold u8_Cconv; ring

end HRS.Whole
