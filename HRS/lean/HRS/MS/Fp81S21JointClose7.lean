import HRS.MS.Fp81S21JointClose3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Filter Topology
open scoped ENNReal NNReal
namespace HRS.Fp81.S21

/-- A family of cutoff estimates with one set of constants uniform in the
objects being compared gives a single vanishing profile. -/
theorem fp81s21_jointClose_uniform_cutoff_profile
    {α : ℕ → Type*} (w : (N : ℕ) → α N → ℝ≥0∞)
    (s : ℕ → ℝ) (t c K : ℕ → ℕ → ℝ) (M : ℝ) (d : ℕ → ℝ)
    (hs : ∀ m, 0 ≤ s m) (ht : ∀ m k, 0 ≤ t m k)
    (hc : ∀ m k, 0 ≤ c m k) (hM : 0 ≤ M) (hd : ∀ N, 0 ≤ d N)
    (hs0 : Tendsto s atTop (𝓝 0))
    (ht0 : ∀ m, Tendsto (t m) atTop (𝓝 0))
    (hd0 : Tendsto d atTop (𝓝 0))
    (hbound : ∀ N, 2 ≤ N → ∀ x m k r,
      w N x ≤ ENNReal.ofReal (fp81s21_jointClose_cutoffBound s t c K M d m k r N)) :
    ∃ q : ℕ → ℝ, (∀ N, 0 ≤ q N) ∧ Tendsto q atTop (𝓝 0) ∧
      ∀ N, 2 ≤ N → ∀ x, w N x ≤ ENNReal.ofReal (q N) := by
  let b := fp81s21_jointClose_cutoffBound s t c K M d
  obtain ⟨hq, hq0⟩ := fp81s21_jointClose_cutoff_profile s t c K M d
    hs ht hc hM hd hs0 ht0 hd0
  refine ⟨fp81s21_jointClose_profile b, hq, hq0, ?_⟩
  intro N hN x
  apply fp81s21_jointClose_inf_bound (w N x) b N
  · refine ⟨0, ?_⟩
    rintro y ⟨⟨m, k, r⟩, rfl⟩
    dsimp [b, fp81s21_jointClose_cutoffBound]
    exact add_nonneg (add_nonneg (add_nonneg (hs m) (ht m k))
      (div_nonneg (hc m k) (Real.sqrt_nonneg _)))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  · exact hbound N hN x

#print axioms fp81s21_jointClose_uniform_cutoff_profile
end HRS.Fp81.S21
end
