import HRS.MS.MovAdjAux23

/-!
# S6.7 (packet P5, part 1): `cbNormVecE` bookkeeping and joint-continuity of the source

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.PoisHigh HRS.MS.Mov63 HRS.MS.FlowB HRS.MS.PoisSg HRS.MS.PoisFlow
  HRS.MS.PoisMax

variable {d : ℕ}

/-- The finite case of `cbNormVecE`: real bounds with the exact sum. -/
theorem s67_cb_fin {j : ℕ} {v : Euc d → Euc d} (h : cbNormVecE j v ≠ ⊤) :
    ∃ Y : ℕ → ℝ, (∀ i, 0 ≤ Y i) ∧ (∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i v x‖ ≤ Y i) ∧
      cbNormVecE j v = ENNReal.ofReal (∑ i ∈ Finset.range (j + 1), Y i) := by
  set Z : ℕ → ℝ≥0∞ := fun i => ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ i v x‖ with hZdef
  have hZ : ∀ i ≤ j, Z i ≠ ⊤ := fun i hi =>
    ne_top_of_le_ne_top h (Finset.single_le_sum (f := Z) (fun _ _ => bot_le)
      (Finset.mem_range.2 (by omega)))
  refine ⟨fun i => if i ≤ j then (Z i).toReal else 0, fun i => by dsimp only; split_ifs <;> simp, ?_, ?_⟩
  · intro i hi x
    simp only [hi, ite_true]
    have := le_iSup (fun x => ENNReal.ofReal ‖iteratedFDeriv ℝ i v x‖) x
    exact (ENNReal.ofReal_le_iff_le_toReal (hZ i hi)).1 this
  · unfold cbNormVecE
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> simp)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
    show (⨆ x, ENNReal.ofReal ‖iteratedFDeriv ℝ i v x‖) = ENNReal.ofReal (if i ≤ j then (Z i).toReal else 0)
    rw [if_pos hi', ENNReal.ofReal_toReal (hZ i hi')]

/-- Upper bound of `cbNormVecE` by real derivative bounds. -/
theorem s67_cb_le {j : ℕ} {v : Euc d → Euc d} {Y : ℕ → ℝ}
    (hY : ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i v x‖ ≤ Y i) :
    cbNormVecE j v ≤ ENNReal.ofReal (∑ i ∈ Finset.range (j + 1), Y i) := by
  unfold cbNormVecE
  have hY0 : ∀ i ∈ Finset.range (j + 1), 0 ≤ Y i := fun i hi =>
    (norm_nonneg _).trans (hY i (by have := Finset.mem_range.1 hi; omega) 0)
  rw [ENNReal.ofReal_sum_of_nonneg hY0]
  refine Finset.sum_le_sum fun i hi => ?_
  exact iSup_le fun x => ENNReal.ofReal_le_ofReal (hY i (by have := Finset.mem_range.1 hi; omega) x)

/-- the gradient of a `C^{j+1}` function is `C^j` -/
theorem s67_grad_contDiff {u : Euc d → ℝ} {j : ℕ} (hu : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) u) :
    ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient u x) := by
  have h := hu.fderiv_right (m := (j : WithTop ℕ∞)) (by push_cast; exact le_rfl)
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp h

/-- the sum of `M` shifted by one over `Icc 1 k` -/
theorem s67_sum_shift {k j : ℕ} (hk : k ≤ j + 1) (Y : ℕ → ℝ) (hY : ∀ i, 0 ≤ Y i) (B : ℝ) :
    ∑ i ∈ Finset.Icc 1 k, (if 1 ≤ i ∧ i ≤ j + 1 then Y (i - 1) else B) ≤
      ∑ i ∈ Finset.range (j + 1), Y i := by
  have h1 : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by ext i; simp
  rw [h1, Finset.sum_Ico_eq_sum_range]
  have h2 : ∀ i ∈ Finset.range (k + 1 - 1), (if 1 ≤ 1 + i ∧ 1 + i ≤ j + 1 then Y (1 + i - 1) else B) = Y i := by
    intro i hi
    have := Finset.mem_range.1 hi
    have h3 : 1 ≤ 1 + i ∧ 1 + i ≤ j + 1 := ⟨by omega, by omega⟩
    simp only [h3, and_self, ite_true]
    congr 1; omega
  rw [Finset.sum_congr rfl h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    (fun i _ _ => hY i)

end HRS.MS.MovAdj
