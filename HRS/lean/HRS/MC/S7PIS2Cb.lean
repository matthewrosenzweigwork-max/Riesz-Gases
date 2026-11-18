import HRS.MC.S7PIDefs

/-!
# Packet piS2, part 1: `s7_PIS_memCb_comp` (composition of a `C_b^5` functional with a bounded operator)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

theorem S7PIS2_norm_iter_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {Φ : E → ℝ}
    (hΦ : MemCb k Φ) {j : ℕ} (hj : j ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ j Φ x‖ ≤ ⨆ z : E, ‖iteratedFDeriv ℝ j Φ z‖ :=
  le_ciSup (hΦ.2 j hj) x

theorem S7PIS2_iSup_le_cbNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {Φ : E → ℝ}
    {j : ℕ} (hj : j ≤ k) : (⨆ z : E, ‖iteratedFDeriv ℝ j Φ z‖) ≤ cbNorm k Φ := by
  unfold HRS.cbNorm
  exact Finset.single_le_sum (f := fun i => ⨆ z : E, ‖iteratedFDeriv ℝ i Φ z‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem S7PIS2_iter_comp_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Λ : E →L[ℝ] F) {Φ : F → ℝ} (hΦ : MemCb 5 Φ)
    {j : ℕ} (hj : j ≤ 5) (x : E) :
    ‖iteratedFDeriv ℝ j (fun x => Φ (Λ x)) x‖ ≤ (⨆ z : F, ‖iteratedFDeriv ℝ j Φ z‖) * ‖Λ‖ ^ j := by
  show ‖iteratedFDeriv ℝ j (Φ ∘ Λ) x‖ ≤ _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right Λ hΦ.1 x (by exact_mod_cast hj)]
  calc ‖(iteratedFDeriv ℝ j Φ (Λ x)).compContinuousLinearMap fun _ => Λ‖
      ≤ ‖iteratedFDeriv ℝ j Φ (Λ x)‖ * ∏ _i : Fin j, ‖Λ‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ j Φ (Λ x)‖ * ‖Λ‖ ^ j := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (S7PIS2_norm_iter_le hΦ hj _) (by positivity)

theorem s7_PIS_memCb_comp_proof {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (Λ : E →L[ℝ] F) {Φ : F → ℝ} (hΦ : MemCb 5 Φ) :
    MemCb 5 (fun x => Φ (Λ x)) ∧ cbNorm 5 (fun x => Φ (Λ x)) ≤ (1 + ‖Λ‖) ^ 5 * cbNorm 5 Φ ∧
      (‖Λ‖ ≤ 1 → cbNorm 5 (fun x => Φ (Λ x)) ≤ cbNorm 5 Φ) := by
  have hnn : ∀ j : ℕ, 0 ≤ (⨆ z : F, ‖iteratedFDeriv ℝ j Φ z‖) := fun j =>
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hmem : MemCb 5 (fun x => Φ (Λ x)) := by
    refine ⟨hΦ.1.comp Λ.contDiff, fun j hj => ?_⟩
    refine ⟨(⨆ z : F, ‖iteratedFDeriv ℝ j Φ z‖) * ‖Λ‖ ^ j, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact S7PIS2_iter_comp_le Λ hΦ hj x
  have hsup : ∀ j ≤ 5, (⨆ x : E, ‖iteratedFDeriv ℝ j (fun x => Φ (Λ x)) x‖) ≤
      (⨆ z : F, ‖iteratedFDeriv ℝ j Φ z‖) * ‖Λ‖ ^ j := fun j hj =>
    ciSup_le fun x => S7PIS2_iter_comp_le Λ hΦ hj x
  have hmain : ∀ C : ℝ, 0 ≤ C → (∀ j ≤ 5, ‖Λ‖ ^ j ≤ C) →
      cbNorm 5 (fun x => Φ (Λ x)) ≤ C * cbNorm 5 Φ := by
    intro C hC hj
    unfold HRS.cbNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hjm => ?_
    have hj5 : j ≤ 5 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjm)
    calc (⨆ x : E, ‖iteratedFDeriv ℝ j (fun x => Φ (Λ x)) x‖)
        ≤ (⨆ z : F, ‖iteratedFDeriv ℝ j Φ z‖) * ‖Λ‖ ^ j := hsup j hj5
      _ ≤ (⨆ z : F, ‖iteratedFDeriv ℝ j Φ z‖) * C :=
          mul_le_mul_of_nonneg_left (hj j hj5) (hnn j)
      _ = C * (⨆ z : F, ‖iteratedFDeriv ℝ j Φ z‖) := mul_comm _ _
  refine ⟨hmem, hmain ((1 + ‖Λ‖) ^ 5) (by positivity) ?_, fun hΛ => ?_⟩
  · intro j hj
    calc ‖Λ‖ ^ j ≤ (1 + ‖Λ‖) ^ j :=
          pow_le_pow_left₀ (norm_nonneg _) (by linarith) j
      _ ≤ (1 + ‖Λ‖) ^ 5 := pow_le_pow_right₀ (by linarith [norm_nonneg Λ]) hj
  · have := hmain 1 zero_le_one (fun j _ => pow_le_one₀ (norm_nonneg _) hΛ)
    simpa using this

end HRS.MC.Sec7.S7PIS2

end
