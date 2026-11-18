import HRS.Main.A9Aux18

/-!
# Packet A9, part 19: the first moment of the field `E‖σ_N Ξ_N^t‖_{H^{-γ}}`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

section Moment

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

/-- `E‖𝕀‖ ≤ K_tr (1 + C_in²)`. -/
theorem a9_I_moment {Ktr : ℝ} (hKtr0 : 0 ≤ Ktr)
    (hKtr : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ),
      AdjointData S.s (gammaIdx d) Rg MB Λ VB D ν₀ S.T ρ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∀ F : NegSobolev d (gammaIdx d : ℝ), ‖transportField D ρ t (gammaIdx d : ℝ) F‖ ≤ ‖F‖ * Ktr)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {Cin : ℝ} {εf : ℕ → ℝ}
    {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)} {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin) :
    ∫⁻ ω, ENNReal.ofReal ‖a9I S R N t ω‖ ∂(R N).P ≤ ENNReal.ofReal (Ktr * (1 + Cin ^ 2)) := by
  have hS' := a9_standing_mStar hS
  have hA : AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    a9_adjointData a9_mStar_le_gamma hS hN
  obtain ⟨-, -, h0⟩ := a8p_flow_facts hS' hN
  have hsm := hfield.second_moment N hN
  have hAN := a8p_A_abs_le S N
  have hF0 : ∫⁻ ω, ‖a9F0 S R N ω‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (Cin ^ 2) := by
    refine le_trans (le_of_eq ?_) ((le_self_add).trans hsm)
    refine lintegral_congr_ae ?_
    filter_upwards [h0] with ω hω
    unfold a9F0; rw [hω]
  have hCin : 0 ≤ Cin ^ 2 := sq_nonneg _
  calc ∫⁻ ω, ENNReal.ofReal ‖a9I S R N t ω‖ ∂(R N).P
      ≤ ∫⁻ ω, ENNReal.ofReal Ktr * (1 + ‖a9F0 S R N ω‖ₑ ^ 2) ∂(R N).P := by
        refine lintegral_mono fun ω => ?_
        have h1 : ‖a9I S R N t ω‖ ≤ Ktr * ‖a9F0 S R N ω‖ := by
          unfold a9I
          rw [norm_smul, Real.norm_eq_abs]
          have := hKtr (S.dyn N) (S.ρ N) hA t ht (a9F0 S R N ω)
          calc |S.AN N| * ‖transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (a9F0 S R N ω)‖
              ≤ 1 * (‖a9F0 S R N ω‖ * Ktr) := mul_le_mul hAN this (norm_nonneg _) zero_le_one
            _ = _ := by ring
        calc ENNReal.ofReal ‖a9I S R N t ω‖ ≤ ENNReal.ofReal (Ktr * ‖a9F0 S R N ω‖) :=
              ENNReal.ofReal_le_ofReal h1
          _ = ENNReal.ofReal Ktr * ‖a9F0 S R N ω‖ₑ := by
              rw [ENNReal.ofReal_mul hKtr0, ofReal_norm]
          _ ≤ ENNReal.ofReal Ktr * (1 + ‖a9F0 S R N ω‖ₑ ^ 2) := by
              refine mul_le_mul_right ?_ _
              rcases le_total ‖a9F0 S R N ω‖ₑ 1 with h | h
              · exact h.trans le_self_add
              · calc ‖a9F0 S R N ω‖ₑ ≤ ‖a9F0 S R N ω‖ₑ ^ 2 := by
                      calc ‖a9F0 S R N ω‖ₑ = ‖a9F0 S R N ω‖ₑ ^ 1 := (pow_one _).symm
                        _ ≤ _ := pow_le_pow_right₀ h (by norm_num)
                  _ ≤ _ := le_add_self
    _ = ENNReal.ofReal Ktr * (1 + ∫⁻ ω, ‖a9F0 S R N ω‖ₑ ^ 2 ∂(R N).P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal Ktr * (1 + ENNReal.ofReal (Cin ^ 2)) := by gcongr
    _ = ENNReal.ofReal (Ktr * (1 + Cin ^ 2)) := by
        rw [ENNReal.ofReal_mul hKtr0, ENNReal.ofReal_add zero_le_one hCin, ENNReal.ofReal_one]

end Moment

end HRS.Main.A9
