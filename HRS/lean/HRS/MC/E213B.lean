import Mathlib

/-!
# Packet E213B: abstract epsilon lemmas (Theorem 2.13)

Two general lemmas over an arbitrary index type `ι` and an arbitrary real-valued error functional.

* `HRS.MC.E213B.e213b_exists_eps` (L1): a qualitative uniform bound `∀ η > 0, ∃ N₀, ∀ N ≥ N₀, ∀ x, |F N x| ≤ η`,
  together with boundedness of each `F N`, yields a sequence `ε → 0` with `|F N x| ≤ ε N` for all `N ≥ 2` and all `x`.
  The construction is `ε N := max 0 (⨆ x, |F N x|)`; the supremum is genuine because each `F N` is bounded (`hb`).
* `HRS.MC.E213B.e213b_double_limit` (L2): the order of limits (`N → ∞` first, then `R → ∞`) for a bound
  `|H N x| ≤ A N + B R + C R * e R N`.
-/

open Filter Topology

namespace HRS.MC.E213B

/-- L1: a qualitative uniform bound with boundedness for each fixed `N` gives a sequence `ε → 0`. -/
theorem e213b_exists_eps {ι : Type*} (F : ℕ → ι → ℝ)
    (hF : ∀ η > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x, |F N x| ≤ η)
    (hb : ∀ N, ∃ C : ℝ, ∀ x, |F N x| ≤ C) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ N, 0 ≤ ε N) ∧
      ∀ N, 2 ≤ N → ∀ x, |F N x| ≤ ε N := by
  refine ⟨fun N => max 0 (⨆ x, |F N x|), ?_, fun N => le_max_left _ _, ?_⟩
  · rw [tendsto_order]
    constructor
    · intro a ha
      exact Eventually.of_forall fun N => lt_of_lt_of_le ha (le_max_left _ _)
    · intro b hb0
      obtain ⟨N₀, hN₀⟩ := hF (b / 2) (by linarith)
      refine Eventually.mono (eventually_ge_atTop N₀) fun N hN => ?_
      have hsup : (⨆ x, |F N x|) ≤ b / 2 :=
        Real.iSup_le (fun x => hN₀ N hN x) (by linarith)
      exact max_lt (by linarith) (by linarith)
  · intro N _ x
    have hbdd : BddAbove (Set.range fun y => |F N y|) := by
      obtain ⟨C, hC⟩ := hb N
      refine ⟨C, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact hC y
    exact le_max_of_le_right (le_ciSup hbdd x)

/-- L2: order of limits `N → ∞` then `R → ∞`. -/
theorem e213b_double_limit {ι : Type*}
    (A : ℕ → ℝ) (hA : Tendsto A atTop (𝓝 0))
    (B : ℕ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (C : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (he : ∀ R, 1 ≤ R → Tendsto (e R) atTop (𝓝 0))
    (H : ℕ → ι → ℝ)
    (hH : ∀ R, 1 ≤ R → ∀ N x, |H N x| ≤ A N + B R + C R * e R N) :
    ∀ η > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x, |H N x| ≤ η := by
  intro η hη
  have h3 : (0 : ℝ) < η / 3 := by linarith
  have hlt : ∀ᶠ y in 𝓝 (0 : ℝ), y < η / 3 := gt_mem_nhds h3
  -- choose R ≥ 1 with B R ≤ η / 3
  obtain ⟨R, hR1, hBR⟩ : ∃ R : ℕ, 1 ≤ R ∧ B R ≤ η / 3 := by
    have h1 : ∀ᶠ R in atTop, B R < η / 3 := hB.eventually hlt
    obtain ⟨R, hR1, hR⟩ := ((eventually_ge_atTop 1).and h1).exists
    exact ⟨R, hR1, hR.le⟩
  -- N-thresholds for A and for C R * e R
  have hCe : Tendsto (fun N => C R * e R N) atTop (𝓝 0) := by
    have := (he R hR1).const_mul (C R)
    rwa [mul_zero] at this
  have hA2 : ∀ᶠ N in atTop, A N < η / 3 := hA.eventually hlt
  have hCe2 : ∀ᶠ N in atTop, C R * e R N < η / 3 := hCe.eventually hlt
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hA2.and hCe2)
  refine ⟨N₀, fun N hN x => ?_⟩
  obtain ⟨h4, h5⟩ := hN₀ N hN
  calc |H N x| ≤ A N + B R + C R * e R N := hH R hR1 N x
    _ ≤ η := by linarith

end HRS.MC.E213B
