import HRS.MS.R26T8AP06a6
import HRS.MS.R26T8AP06b

/-!
# S8.2 local Newton layer, packet T8A.P06c: uniform quantitative limit jets
`r26t8a_limit_jets`: for `h` of class `C^(k+1)` off `0` with `|D^i h z| <= A (1 + |z|^(-(sigma+i)) (1+|log|z||)^b)` (`i <= k+1`) and `k < -sigma`,
the jets `D^j h z`, `j <= k`, have limits `Lambda j` as `z -> 0` with the explicit rate `|D^j h z - Lambda j| <= C A |z|^eps`,
`eps = min(-sigma-k, 1)/2`, `C` universal (independent of `A`, `h`).  Obtained from `r26t8a_p06_T` (P06a).
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology

namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_limit_jets {d : ℕ} (hd : 2 ≤ d) (k b : ℕ) (σ : ℝ) (hk : (k : ℝ) < -σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ h : Euc d → ℝ, ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) h {z | z ≠ 0} →
      (∀ i ≤ k + 1, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 →
        ‖iteratedFDeriv ℝ i h z‖ ≤ A * r26t8a_jetEnvelope b (σ + i) ‖z‖) →
      ∃ Λ : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ,
        (∀ j ≤ k, ‖Λ j‖ ≤ C * A) ∧
        (∀ j ≤ k, ∀ (τ : Equiv.Perm (Fin j)) (v : Fin j → Euc d), Λ j (v ∘ τ) = Λ j v) ∧
        ∀ j ≤ k, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
          ‖iteratedFDeriv ℝ j h z - Λ j‖ ≤ C * A * ‖z‖ ^ (min (-σ - k) 1 / 2) := by
  have hall : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (j ≤ k → ∀ A : ℝ, 0 ≤ A → ∀ h : Euc d → ℝ,
      ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) h {z | z ≠ 0} →
      (∀ i ≤ k + 1, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 →
        ‖iteratedFDeriv ℝ i h z‖ ≤ A * r26t8a_jetEnvelope b (σ + i) ‖z‖) →
      ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ, ‖T‖ ≤ C * A ∧
        (∀ (τ : Equiv.Perm (Fin j)) (v : Fin j → Euc d), T (v ∘ τ) = T v) ∧
        ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
          ‖iteratedFDeriv ℝ j h z - T‖ ≤
            C * A * (‖z‖ ^ (min (-(σ + j)) 1) * (1 + |Real.log ‖z‖|) ^ b)) := by
    intro j
    by_cases hj : j ≤ k
    · obtain ⟨C, hC0, hC⟩ := r26t8a_p06_T d hd b (k + 1) σ j (by omega)
        (lt_of_le_of_lt (by exact_mod_cast hj) hk)
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose Cj hCj0 hCj using hall
  set a0 : ℝ := min (-σ - k) 1 with ha0
  have ha00 : 0 < a0 := lt_min (by linarith) one_pos
  set ε : ℝ := a0 / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  set M : ℝ := r26t8a_p06_M ε b with hM
  have hM0 : 0 ≤ M := by rw [hM]; unfold r26t8a_p06_M; positivity
  set C0 : ℝ := ∑ j ∈ Finset.range (k + 1), Cj j with hC0def
  have hC00 : 0 ≤ C0 := Finset.sum_nonneg fun j _ => hCj0 j
  have hCle : ∀ j ≤ k, Cj j ≤ C0 := fun j hj =>
    Finset.single_le_sum (f := Cj) (fun i _ => hCj0 i) (Finset.mem_range.2 (by omega))
  refine ⟨C0 * (1 + M), by positivity, fun A hA h hc hjet => ?_⟩
  have hex : ∀ j : ℕ, ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ, j ≤ k →
      (‖T‖ ≤ Cj j * A ∧ (∀ (τ : Equiv.Perm (Fin j)) (v : Fin j → Euc d), T (v ∘ τ) = T v) ∧
        ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
          ‖iteratedFDeriv ℝ j h z - T‖ ≤
            Cj j * A * (‖z‖ ^ (min (-(σ + j)) 1) * (1 + |Real.log ‖z‖|) ^ b)) := by
    intro j
    by_cases hj : j ≤ k
    · obtain ⟨T, hT⟩ := hCj j hj A hA h hc hjet
      exact ⟨T, fun _ => hT⟩
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose Λ hΛ using hex
  refine ⟨Λ, fun j hj => ?_, fun j hj => (hΛ j hj).2.1, fun j hj z hz hz1 => ?_⟩
  · refine (hΛ j hj).1.trans ?_
    have := hCle j hj
    nlinarith [mul_le_mul_of_nonneg_right this hA, mul_nonneg hC00 hM0, mul_nonneg (mul_nonneg hC00 hM0) hA]
  · refine ((hΛ j hj).2.2 z hz hz1).trans ?_
    have hzle1 : ‖z‖ ≤ 1 := by linarith
    have haj : a0 ≤ min (-(σ + j)) 1 := by
      refine min_le_min ?_ le_rfl
      have : (j : ℝ) ≤ k := by exact_mod_cast hj
      linarith
    have h1 : ‖z‖ ^ (min (-(σ + j)) 1) ≤ ‖z‖ ^ a0 := Real.rpow_le_rpow_of_exponent_ge hz hzle1 haj
    have h2 : ‖z‖ ^ a0 = ‖z‖ ^ ε * ‖z‖ ^ ε := by
      rw [← Real.rpow_add hz]; congr 1; rw [hε]; ring
    have h3 := r26t8a_p06_slog b hε0 hz hzle1
    have hlog : 0 ≤ (1 + |Real.log ‖z‖|) ^ b := by positivity
    have hzε : 0 ≤ ‖z‖ ^ ε := Real.rpow_nonneg hz.le _
    have key : ‖z‖ ^ (min (-(σ + j)) 1) * (1 + |Real.log ‖z‖|) ^ b ≤ M * ‖z‖ ^ ε := by
      calc _ ≤ ‖z‖ ^ a0 * (1 + |Real.log ‖z‖|) ^ b := mul_le_mul_of_nonneg_right h1 hlog
        _ = ‖z‖ ^ ε * (‖z‖ ^ ε * (1 + |Real.log ‖z‖|) ^ b) := by rw [h2]; ring
        _ ≤ ‖z‖ ^ ε * M := mul_le_mul_of_nonneg_left h3 hzε
        _ = _ := mul_comm _ _
    have hCA : Cj j * A ≤ C0 * A := mul_le_mul_of_nonneg_right (hCle j hj) hA
    calc Cj j * A * (‖z‖ ^ (min (-(σ + j)) 1) * (1 + |Real.log ‖z‖|) ^ b)
        ≤ C0 * A * (M * ‖z‖ ^ ε) := mul_le_mul hCA key (by positivity) (by positivity)
      _ ≤ C0 * (1 + M) * A * ‖z‖ ^ ε := by nlinarith [mul_nonneg (mul_nonneg hC00 hA) hzε]

end HRS.MS.R26T8A
