import HRS.Commutator.Torus.TSAMPAux27

/-!
# T-SAMP helpers, part 28: vector-valued cell suprema
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_enorm_le_sum (v : Euc d) : ‖v‖ₑ ≤ ∑ i, ‖v i‖ₑ := by
  have h := Whole.cmxHLS_norm_toLp_le (d := d) (fun i => v i)
  have e : (WithLp.toLp 2 (fun i => v i) : Euc d) = v := by ext i; rfl
  rw [e] at h
  have e2 : ∑ i, ‖v i‖ₑ = ENNReal.ofReal (∑ i, |v i|) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    simp [Real.enorm_eq_ofReal_abs]
  rw [e2, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (by simpa using h)

lemma tsamp_cellSup_vec {η p : ℝ} (hp : 1 < p) (f : Torus d → Euc d) {B : ℝ≥0∞}
    (h : ∀ i : Fin d, (∑ j : Fin d → Fin (nCells η),
      (⨆ x ∈ cellT (nCells η) j, ‖f x i‖ₑ) ^ p) ^ (1 / p) ≤ B) :
    cellSupNorm η p f ≤ (d : ℝ≥0∞) * B := by
  have hp0 : 0 < p := by linarith
  have hp' : 1 ≤ p := hp.le
  unfold cellSupNorm
  have hB : ∀ i : Fin d, ∑ j : Fin d → Fin (nCells η), (⨆ x ∈ cellT (nCells η) j, ‖f x i‖ₑ) ^ p ≤ B ^ p := by
    intro i
    have := ENNReal.rpow_le_rpow (h i) hp0.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at this
  have h1 : ∀ j : Fin d → Fin (nCells η), (⨆ x ∈ cellT (nCells η) j, ‖f x‖ₑ) ≤
      ∑ i : Fin d, ⨆ x ∈ cellT (nCells η) j, ‖f x i‖ₑ := by
    intro j
    refine iSup₂_le fun x hx => ?_
    exact (tsamp_enorm_le_sum (f x)).trans (Finset.sum_le_sum fun i _ =>
      le_iSup₂ (f := fun x (_ : x ∈ cellT (nCells η) j) => ‖f x i‖ₑ) x hx)
  have h2 : ∑ j : Fin d → Fin (nCells η), (⨆ x ∈ cellT (nCells η) j, ‖f x‖ₑ) ^ p ≤
      (d : ℝ≥0∞) ^ p * B ^ p := by
    calc ∑ j : Fin d → Fin (nCells η), (⨆ x ∈ cellT (nCells η) j, ‖f x‖ₑ) ^ p
        ≤ ∑ j : Fin d → Fin (nCells η), (∑ i : Fin d, ⨆ x ∈ cellT (nCells η) j, ‖f x i‖ₑ) ^ p :=
          Finset.sum_le_sum fun j _ => ENNReal.rpow_le_rpow (h1 j) hp0.le
      _ ≤ ∑ j : Fin d → Fin (nCells η), ((d : ℝ≥0∞) ^ (p - 1) *
            ∑ i : Fin d, (⨆ x ∈ cellT (nCells η) j, ‖f x i‖ₑ) ^ p) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset (Fin d))
            (fun i => ⨆ x ∈ cellT (nCells η) j, ‖f x i‖ₑ) hp'
          simpa using this
      _ = (d : ℝ≥0∞) ^ (p - 1) * ∑ i : Fin d, ∑ j : Fin d → Fin (nCells η),
            (⨆ x ∈ cellT (nCells η) j, ‖f x i‖ₑ) ^ p := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (d : ℝ≥0∞) ^ (p - 1) * ∑ i : Fin d, B ^ p :=
          mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hB i)
      _ = (d : ℝ≥0∞) ^ p * B ^ p := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
          congr 1
          by_cases hd0 : (d : ℝ≥0∞) = 0
          · rw [hd0, ENNReal.zero_rpow_of_pos hp0, ENNReal.zero_rpow_of_pos (by linarith), zero_mul]
          · have hdt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
            calc (d : ℝ≥0∞) ^ (p - 1) * d = (d : ℝ≥0∞) ^ (p - 1) * (d : ℝ≥0∞) ^ (1 : ℝ) := by
                  rw [ENNReal.rpow_one]
              _ = (d : ℝ≥0∞) ^ p := by
                  rw [← ENNReal.rpow_add _ _ hd0 hdt]; congr 1; ring
  calc (∑ j : Fin d → Fin (nCells η), (⨆ x ∈ cellT (nCells η) j, ‖f x‖ₑ) ^ p) ^ (1 / p)
      ≤ ((d : ℝ≥0∞) ^ p * B ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow h2 (by positivity)
    _ = (d : ℝ≥0∞) * B := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne',
          ENNReal.rpow_one]

end HRS.Commutator.TorusNote
