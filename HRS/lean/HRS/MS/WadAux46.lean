import HRS.MS.WadAux45

/-!
# S8.3 (Route A): the existence conjunct of `HRS.Whole.weighted_adjoint_decay`

`s85_exists_semigroup`: for the critical quadratic model, every `M > 0`, the extension `s85_Ulim` of the
projected classical semigroup satisfies the frozen `IsWeightedSemigroup` (maps `C_M` into `C_M`, linear, bounded on
bounded time intervals, `U_0 = id`, semigroup law, and the classical clause on `C_c^∞`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s85_zero_memCM (M : ℝ) : MemCM M (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨continuous_const, ?_⟩
  simpa using tendsto_const_nhds (x := (0 : ℝ)) (f := cocompact (Euc d))

/-- **Existence conjunct of S8.3.** -/
theorem s85_exists_semigroup (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {M : ℝ} (hM : 0 < M) :
    IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M (s85_Ulim a β ρβ M) := by
  have HH : ∀ T : ℝ, 0 < T → S85Hyp d a β T M ρβ := fun T hT => ⟨hd, ha, hβ, hT, hM.le, hρ⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht f hf
    exact s85_Ulim_memCM (HH (t + 1) (by linarith)) hM ht (by linarith) hf
  · intro t ht f g hf hg
    funext x
    have e : (f + g) = fun y => 1 * f y + g y := by funext y; simp
    rw [e]
    simpa using s85_Ulim_lin (HH (t + 1) (by linarith)) ht (by linarith) hf hg 1 x
  · intro t ht c f hf
    funext x
    have H := HH (t + 1) (by linarith)
    have e : (c • f) = fun y => c * f y + (fun _ : Euc d => (0 : ℝ)) y := by funext y; simp
    rw [e]
    have := s85_Ulim_lin H ht (by linarith) hf (s85_zero_memCM M) c x
    rw [this, s85_Ulim_zero_fun H ht (by linarith)]
    simp
  · intro T hT
    obtain ⟨K, hK0, hK⟩ := s85_Ulim_wsup (HH (max T 1) (lt_of_lt_of_le one_pos (le_max_right _ _)))
    exact ⟨K, fun t ht f hf => hK ht.1 (ht.2.trans (le_max_left _ _)) hf⟩
  · intro f hf
    funext x
    exact s85_Ulim_at_zero (HH 1 one_pos) hf x
  · intro t s ht hs f hf
    funext x
    exact s85_semigroup (HH (t + s + 1) (by linarith)) hM ht hs (by linarith) hf x
  · intro t ht φ hφd hφc
    exact s85_Ulim_classical (HH (t + 1) (by linarith)) ht (by linarith) ⟨hφd, hφc⟩

end HRS.MS.Wad
