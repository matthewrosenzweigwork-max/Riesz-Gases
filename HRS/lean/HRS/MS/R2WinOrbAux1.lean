import HRS.MS.QsfOsc4
import HRS.Whole.Window

/-!
# S10.3 (worker S102), part 1: numerics of `r2_window_orbits` (summability of `b_α`, `C_b^k` bounds of the dual tests)

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  `b_α = λ_α^{(J-m)/2}` with `J = 18d+180`, `m = 24d+240`, `k = 4d+42`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole

variable {d : ℕ}

/-- `b_α` of `r2_window_orbits`. -/
def s103_b (d : ℕ) (α : MultiIndex d) : ℝ :=
  oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2)

theorem s103_summable (hd : 1 ≤ d) : Summable fun α : MultiIndex d => s103_b d α := by
  have h := (summable_oscEigenvalue_rpow_iff (d := d) hd ((3 * d + 30 : ℕ) : ℝ)).2 (by
    push_cast; nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  refine h.congr fun α => ?_
  unfold s103_b
  congr 1
  push_cast
  ring

theorem s103_ofReal_iSup {ι : Type*} [Nonempty ι] (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i) (hb : BddAbove (Set.range f)) :
    ⨆ i, ENNReal.ofReal (f i) = ENNReal.ofReal (⨆ i, f i) := by
  obtain ⟨B, hB⟩ := hb
  have hB' : ∀ i, f i ≤ B := fun i => hB ⟨i, rfl⟩
  apply le_antisymm
  · exact iSup_le fun i => ENNReal.ofReal_le_ofReal (le_ciSup ⟨B, hB⟩ i)
  · have hfin : (⨆ i, ENNReal.ofReal (f i)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun i => ENNReal.ofReal_le_ofReal (hB' i))
    refine ENNReal.ofReal_le_of_le_toReal (ciSup_le fun i => ?_)
    calc f i = (ENNReal.ofReal (f i)).toReal := (ENNReal.toReal_ofReal (h0 i)).symm
      _ ≤ _ := ENNReal.toReal_mono hfin (le_iSup (fun i => ENNReal.ofReal (f i)) i)

/-- `r2CbNormE` is the real `C_b^k` norm for functions of class `C_b^k`. -/
theorem s103_cbE_eq {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) :
    r2CbNormE k f = ENNReal.ofReal (cbNorm k f) := by
  unfold r2CbNormE cbNorm
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.iSup_nonneg fun x => norm_nonneg _)]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact s103_ofReal_iSup _ (fun x => norm_nonneg _) (hf.2 j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))

/-- `C_b^k` bound of the dual tests by `b_α`. -/
theorem s103_phi_cb (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ α : MultiIndex d,
      MemCb (4 * d + 42) (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) ∧
      cbNorm (4 * d + 42) (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) ≤ K * s103_b d α := by
  obtain ⟨K, hK0, hK⟩ := S45.s45_cb_oscTest hd (4 * d + 42) ((24 * d + 240 : ℕ) : ℝ)
  refine ⟨K, hK0, fun α => ⟨(hK α).1, ?_⟩⟩
  refine ((hK α).2).trans (mul_le_mul_of_nonneg_left ?_ hK0)
  unfold s103_b
  refine Real.rpow_le_rpow_of_exponent_le (one_le_oscEigenvalue α) ?_
  push_cast
  nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

end HRS.MS.R2WinOrb

end
