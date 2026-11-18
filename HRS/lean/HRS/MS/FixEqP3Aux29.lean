import HRS.MS.FixEqP3Aux28

/-!
# S5.7 `fixed_equation` (worker S57P), part 41: `E sup_t ‖X^N_t - X_t‖⁴` for the two noise fields on a common isonormal process
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau HRS.MS.U10

variable {d : ℕ}

theorem s57p_el_zero {T : ℝ} (w : ℝ × Euc d → ℝ) (A : ℝ × Euc d → Euc d) : s57pel T w A 0 = 0 := by
  by_cases h : MemLp (s57pkf w A 0) 2 (s57pμ d T)
  · rw [s57p_el_eq h]
    have hae : s57pkf w A 0 =ᵐ[s57pμ d T] 0 := by
      have hnull : ∀ᵐ p ∂(s57pμ d T), p.1 ≠ 0 :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae
          (by simpa using (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)))
      filter_upwards [hnull, s57p_ae_fst (d := d) T] with p h1 h2
      have : ¬ p.1 ≤ 0 := fun h3 => h1 (le_antisymm h3 h2.1)
      simp [s57pkf, this]
    rw [MemLp.toLp_congr h MemLp.zero hae, MemLp.toLp_zero]
  · unfold s57pel; rw [dif_neg h]

theorem s57p_noise_zero {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ω₀ : Type} [MeasurableSpace Ω₀] {Q : Measure Ω₀} {W : H → Ω₀ → ℝ} (hI : Sb7Iso Q W) {m : ℝ}
    {X : ℝ → Ω₀ → OscDual d m} {κ : ℝ → MultiIndex d → H} {T : ℝ} (h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T)
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α, ∀ᵐ w ∂Q, OscDual.coord (X t w) α = W (κ t α) w)
    (hκ : ∀ α, κ 0 α = 0) : ∀ᵐ w ∂Q, X 0 w = 0 := by
  have hc := ae_all_iff.2 (hX 0 h0)
  have hW : ∀ α : MultiIndex d, W (0 : H) =ᵐ[Q] fun _ => (0 : ℝ) := fun α => by
    have := hI.lin 0 0 (0 : H) 0
    simpa using this
  have hW' := ae_all_iff.2 hW
  filter_upwards [hc, hW'] with w h1 h2
  refine lp.ext (funext fun α => ?_)
  have := h1 α
  rw [hκ α] at this
  have h3 := h2 α
  change OscDual.coord (X 0 w) α = 0
  rw [this]
  exact h3 ▸ rfl

end HRS.MS.FixEq
