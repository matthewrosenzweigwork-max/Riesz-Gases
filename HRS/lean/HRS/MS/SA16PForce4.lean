import HRS.MS.SA16PForce3

/-!
# SA16P P4, part 4: `Φ_K ρ ∈ C^k` with uniform derivative bounds (induction on `k`)
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace HRS.Whole.AppendixA.Phase2SA16P

section Ind
variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

set_option synthInstance.maxHeartbeats 400000 in
theorem sa16p_phi_contDiff (hd : 1 ≤ d) {K : 𝔼 → ℝ} (hKm : Measurable K) {c s : ℝ} (hc : 0 ≤ c)
    (hs0 : 0 ≤ s) (hsd : s < d) (hK : ∀ z, z ≠ 0 → |K z| ≤ c * ‖z‖ ^ (-s - 1)) :
    ∀ (k : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (ρ : 𝔼 → F) (A : ℝ), ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) ρ →
      (∀ j ≤ k + 1, ∀ y, ‖iteratedFDeriv ℝ j ρ y‖ ≤ A * sa16p_w d y) →
      ContDiff ℝ (k : WithTop ℕ∞) (sa16p_phiF K ρ) ∧
        ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (sa16p_phiF K ρ) x‖ ≤ sa16p_C0 d c s * A := by
  intro k
  induction k with
  | zero =>
    intro F _ _ _ ρ A hρ hb
    have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
    have hρw : ∀ y, ‖ρ y‖ ≤ A * sa16p_w d y := fun y => by
      simpa using hb 0 (by omega) y
    have hρ1w : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A * sa16p_w d y := fun y => by
      rw [sa16p_norm_fderiv_eq]; exact hb 1 (by omega) y
    have hA : 0 ≤ A := by
      have := (norm_nonneg (ρ 0)).trans (hρw 0)
      have hw := sa16p_w_pos (d := d) 0
      nlinarith
    have hρ1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A := fun y =>
      (hρ1w y).trans (mul_le_of_le_one_right hA (sa16p_w_le_one y))
    refine ⟨?_, fun j hj x => ?_⟩
    · exact contDiff_zero.2 (sa16p_continuous_phi hd hKm hc hs0 hsd hK (by simpa using hρ) hρw hρ1)
    · have : j = 0 := by omega
      subst this
      rw [norm_iteratedFDeriv_zero]
      exact (sa16p_phi_bound hd hKm hc hs0 hsd hK hρd hρw hρ1 x).2
  | succ k ih =>
    intro F _ _ _ ρ A hρ hb
    have hρ2 : ContDiff ℝ 2 ρ := hρ.of_le (by
      have : (2 : WithTop ℕ∞) ≤ ((k + 1 + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega : 2 ≤ k + 1 + 1)
      exact this)
    have hρd : Differentiable ℝ ρ := hρ2.differentiable (by norm_num)
    have hρw : ∀ y, ‖ρ y‖ ≤ A * sa16p_w d y := fun y => by
      simpa using hb 0 (by omega) y
    have hρ1w : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A * sa16p_w d y := fun y => by
      rw [sa16p_norm_fderiv_eq]; exact hb 1 (by omega) y
    have hA : 0 ≤ A := by
      have := (norm_nonneg (ρ 0)).trans (hρw 0)
      have hw := sa16p_w_pos (d := d) 0
      nlinarith
    have hρ1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A := fun y =>
      (hρ1w y).trans (mul_le_of_le_one_right hA (sa16p_w_le_one y))
    have hρ2b : ∀ y, ‖fderiv ℝ (fderiv ℝ ρ) y‖ ≤ A := fun y => by
      have h1 := sa16p_norm_fderiv_eq (fderiv ℝ ρ) y
      have h2 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1) (f := ρ) (x := y)
      rw [h1, h2]
      exact (hb 2 (by omega) y).trans (mul_le_of_le_one_right hA (sa16p_w_le_one y))
    have hasfd : ∀ x, HasFDerivAt (sa16p_phiF K ρ) (sa16p_phiF K (fderiv ℝ ρ) x) x := fun x =>
      sa16p_phi_hasFDerivAt hd hKm hc hs0 hsd hK hρ2 hρw hρ1w hρ2b x
    have hfd : fderiv ℝ (sa16p_phiF K ρ) = sa16p_phiF K (fderiv ℝ ρ) := funext fun x => (hasfd x).fderiv
    have hρ' : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ ρ) := by
      have := hρ.fderiv_right (m := ((k + 1 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast le_rfl)
      exact this
    obtain ⟨ih1, ih2⟩ := ih (fderiv ℝ ρ) A hρ' (fun j hj y => by
      rw [norm_iteratedFDeriv_fderiv]; exact hb (j + 1) (by omega) y)
    refine ⟨?_, fun j hj x => ?_⟩
    · rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hasfd x).differentiableAt, by simp, ?_⟩
      rw [hfd]; exact ih1
    · rcases j with _ | j
      · rw [norm_iteratedFDeriv_zero]
        exact (sa16p_phi_bound hd hKm hc hs0 hsd hK hρd hρw hρ1 x).2
      · rw [← norm_iteratedFDeriv_fderiv, hfd]
        exact ih2 j (by omega) x

end Ind

end HRS.Whole.AppendixA.Phase2SA16P
