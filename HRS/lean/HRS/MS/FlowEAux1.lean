import HRS.Whole.AppendixALemmas

/-!
# MS-FLOW-E: `C_b^{m+1}` norm of a cutoff composed with a map with bounded derivatives

Route in `FlowEPlan.md`.
-/

open Set
open scoped ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

namespace HRS.MS.FlowE

theorem cb_comp_bound {d : ℕ} (m : ℕ) (χ : Euc d → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D : ℝ, 1 ≤ D → ∀ f : Euc d → Euc d,
      ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f →
      (∀ x, ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 → ‖iteratedFDeriv ℝ i f x‖ ≤ D) → ∀ z : Euc d,
      MemCb (m + 1) (fun x => χ (f x - z)) ∧
        cbNorm (m + 1) (fun x => χ (f x - z)) ≤ K * D ^ (m + 1) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := hχc.exists_bound_iteratedFDeriv hχ (m + 1)
  refine ⟨(∑ j ∈ Finset.range (m + 2), (j.factorial : ℝ)) * Cχ, by positivity, ?_⟩
  intro D hD f hf hfD z
  have hgs : ContDiff ℝ ∞ (fun y : Euc d => χ (y - z)) := hχ.comp (contDiff_id.sub contDiff_const)
  have hg : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y : Euc d => χ (y - z)) :=
    hgs.of_le (by exact_mod_cast le_top)
  have hbound : ∀ j : ℕ, j ≤ m + 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (fun x => χ (f x - z)) x‖ ≤ (j.factorial : ℝ) * Cχ * D ^ (m + 1) := by
    intro j hj x
    have h1 : (fun x => χ (f x - z)) = (fun y : Euc d => χ (y - z)) ∘ f := rfl
    have hjN : (j : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
    have := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := fun y : Euc d => χ (y - z)) (f := f)
      (n := j) hg hf hjN x (C := Cχ) (D := D)
      (fun i hi => by
        rw [iteratedFDeriv_comp_sub]
        exact hCχ i (hi.trans hj) _)
      (fun i h1 h2 => (hfD x i h1 (h2.trans hj)).trans (by
        calc D = D ^ 1 := (pow_one D).symm
          _ ≤ D ^ i := pow_le_pow_right₀ hD h1))
    rw [h1]
    refine this.trans ?_
    have : (0 : ℝ) ≤ (j.factorial : ℝ) * Cχ := by positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hj) this
  refine ⟨⟨hg.comp hf, fun j hj => ⟨(j.factorial : ℝ) * Cχ * D ^ (m + 1), ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hbound j hj x
  · unfold cbNorm
    calc _ ≤ ∑ j ∈ Finset.range (m + 1 + 1), (j.factorial : ℝ) * Cχ * D ^ (m + 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact ciSup_le fun x => hbound j (by simp at hj; omega) x
      _ = (∑ j ∈ Finset.range (m + 2), (j.factorial : ℝ)) * Cχ * D ^ (m + 1) := by
          rw [Finset.sum_mul, Finset.sum_mul]

end HRS.MS.FlowE
