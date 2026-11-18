import HRS.MS.SA12DE7N

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part O: the `H^m` bound for a distributional limit of smooth functions

`sa12de7_Hm_bound_of_weak_limit`: let `F n ∈ C^∞`, `S n` sets exhausting `ℝ^d`, with zero-extended jets
`1_{S n} ∂^idx F n ∈ L²` (`j ≤ m`) of weighted energy `∑_j C(m,j) ∑_idx ∫ (·)² ≤ B²` for all `n`, and `u` locally integrable with
`∫ F n ψ → ∫ u ψ` for every real `C_c^∞` test `ψ`.  Then `u ∈ H^m` and `‖u‖_{H^m} ≤ B` (`sobolevNormE`, the exact
Fourier norm).  This is the weak-compactness / lower-semicontinuity step of packet E7.08: `S n` is a period cell
(`L_n`-box) of the periodic solution `F n (τ)` at a fixed time `τ`, the bound `B²` comes from E7.06 and E7.07.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.MH.AdjointRd HRS.Whole.AppendixA HRS.Whole.Q09A

variable {d : ℕ}

theorem sa12de7_Hm_bound_of_weak_limit {m : ℕ} (F : ℕ → Euc d → ℝ) (u : Euc d → ℝ) (S : ℕ → Set (Euc d)) {B : ℝ}
    (hB0 : 0 ≤ B) (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hS : ∀ R : ℝ, ∀ᶠ n in atTop, Metric.closedBall (0 : Euc d) R ⊆ S n)
    (hmem : ∀ n j, j ≤ m → ∀ idx : Fin j → Fin d, MemLp ((S n).indicator (partialDeriv idx (F n))) 2 volume)
    (hbound : ∀ n, ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
      ∑ idx : Fin j → Fin d, ∫ x, ((S n).indicator (partialDeriv idx (F n)) x) ^ 2 ≤ B ^ 2)
    (hu : LocallyIntegrable u volume)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, F n x * ψ x) atTop (𝓝 (∫ x, u x * ψ x))) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u ∧ sobolevNormE (m : ℝ) u ≤ ENNReal.ofReal B := by
  obtain ⟨G, hGm, hGE, hG0, hGs⟩ := sa12de7_weak_limit_jets F u S hB0 hF hS hmem hbound hconv
  -- `G 0 idx = u` almost everywhere
  have hae : ∀ idx : Fin 0 → Fin d, G 0 idx =ᵐ[volume] u := by
    intro idx
    have hG0m := hGm 0 (Nat.zero_le _) idx
    have hloc : LocallyIntegrable (fun x => G 0 idx x - u x) volume :=
      (hG0m.locallyIntegrable (by norm_num)).sub hu
    have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hloc (by
      intro Ψ hΨ hΨc
      have hcc : IsCcInfty Ψ := ⟨hΨ, hΨc⟩
      have i1 : Integrable (fun x => G 0 idx x * Ψ x) volume := hG0m.integrable_mul (sa12de7_cc_memLp hcc)
      have i2 : Integrable (fun x => u x * Ψ x) volume :=
        hu.integrable_smul_right_of_hasCompactSupport hΨ.continuous hΨc |>.congr
          (Eventually.of_forall fun x => by simp [mul_comm])
      have := hG0 idx Ψ hcc
      have e : ∀ x, Ψ x • (G 0 idx x - u x) = G 0 idx x * Ψ x - u x * Ψ x := fun x => by
        simp [smul_eq_mul]; ring
      simp only [e]
      rw [integral_sub i1 i2, this, sub_self])
    filter_upwards [key] with x hx
    exact sub_eq_zero.1 hx
  let g : (j : ℕ) → (Fin j → Fin d) → Euc d → ℝ := fun j idx => if j = 0 then u else G j idx
  have hg0 : ∀ idx : Fin 0 → Fin d, g 0 idx = u := fun idx => by simp [g]
  have hgs : ∀ j, j ≠ 0 → ∀ idx : Fin j → Fin d, g j idx = G j idx := fun j hj idx => by simp [g, hj]
  have hu2 : MemLp u 2 volume := (hGm 0 (Nat.zero_le _) Fin.elim0).ae_eq (hae Fin.elim0)
  have hwj : SA12WeakJet m u g := by
    refine ⟨hg0, ?_, ?_⟩
    · intro j hj idx
      by_cases h0 : j = 0
      · subst h0; rw [hg0]; exact hu2
      · rw [hgs j h0]; exact hGm j hj idx
    · intro j hj i idx ψ hψ
      rw [hgs (j + 1) (Nat.succ_ne_zero j), hGs j hj i idx ψ hψ]
      congr 1
      by_cases h0 : j = 0
      · subst h0
        rw [hg0]
        exact integral_congr_ae (by filter_upwards [hae idx] with x hx; rw [hx])
      · rw [hgs j h0]
  have hE : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * ∑ idx : Fin j → Fin d, ∫ x, (g j idx x) ^ 2 ≤ B ^ 2 := by
    refine le_trans (le_of_eq ?_) hGE
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun idx _ => ?_
    by_cases h0 : j = 0
    · subst h0
      rw [hg0]
      exact integral_congr_ae (by filter_upwards [hae idx] with x hx; rw [hx])
    · rw [hgs j h0]
  exact ⟨(sa12de7_sobolev_jet_weak hwj).1, sa12de7_sobolevNormE_le_of_weak_jet hwj hB0 hE⟩

end HRS.MS.SA12DE7
