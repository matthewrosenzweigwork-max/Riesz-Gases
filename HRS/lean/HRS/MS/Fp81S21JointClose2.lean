import HRS.MS.Fp81S21JointClose

/-! Sequential selection for the uniform joint-comparison profile. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Filter Topology
namespace HRS.Fp81.S21

/-- Nested limits supply the fixed approximation choices needed by the
infimum profile: choose `m`, then `k`, then the cutoff, before varying `N`. -/
theorem fp81s21_jointClose_sequential_profile
    (b : ℕ → ℕ → ℕ → ℕ → ℝ)
    (bN : ℕ → ℕ → ℕ → ℝ) (bR : ℕ → ℕ → ℝ) (bK : ℕ → ℝ)
    (hb : ∀ m k r N, 0 ≤ b m k r N)
    (hN : ∀ m k r, Tendsto (b m k r) atTop (𝓝 (bN m k r)))
    (hR : ∀ m k, Tendsto (bN m k) atTop (𝓝 (bR m k)))
    (hK : ∀ m, Tendsto (bR m) atTop (𝓝 (bK m)))
    (hM : Tendsto bK atTop (𝓝 0)) :
    (∀ N, 0 ≤ fp81s21_jointClose_profile b N) ∧
      Tendsto (fp81s21_jointClose_profile b) atTop (𝓝 0) := by
  apply fp81s21_jointClose_profile_spec b hb
  intro ε hε
  have hm : ∀ᶠ m in atTop, bK m < ε := (tendsto_order.1 hM).2 ε hε
  obtain ⟨m, hm⟩ := hm.exists
  have hk : ∀ᶠ k in atTop, bR m k < ε := (tendsto_order.1 (hK m)).2 ε hm
  obtain ⟨k, hk⟩ := hk.exists
  have hr : ∀ᶠ r in atTop, bN m k r < ε := (tendsto_order.1 (hR m k)).2 ε hk
  obtain ⟨r, hr⟩ := hr.exists
  exact ⟨m, k, r, (tendsto_order.1 (hN m k r)).2 ε hr⟩

#print axioms fp81s21_jointClose_sequential_profile
end HRS.Fp81.S21
end
