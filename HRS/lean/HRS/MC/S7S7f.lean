import HRS.MC.S7S7fAux7
import HRS.MC.S7S7z

/-!
# Packet S7f: assembly of `HRS.Sec7.static_field` (Proposition 7.7, `M:F:thm:static`)

Relocation: `static_field_proof` has the statement of the frozen `HRS.Sec7.static_field` verbatim.

* `γ = 0`: the product case `S7z`.
* `γ > 0`: mode data `S7a`; for `Φ` in the `C_b^5` unit ball and `f = steinSolG G Φ` the exact identity
  (`s7f_exact_identity`: Stein equation, Gaussian contraction expansion, `S7c`)
  `√N (E Φ(W_N) - E Φ(G)) = R1 - T_A + γ T_B`; `R1 = O(N^{-1/2})` by `S7b(iii)` (`s7f_R1_bound`);
  `T_A -> L_A`, `T_B -> L_B/2` uniformly (`S7d`); and `-L_A + γ L_B/2 = (1/6) ∫∫ D³Φ(G)[ℓ_x,ℓ_x,ℓ_x]`
  (`s7f_limit_identity`: `sed_B9cancel`, symmetry of `D³f`, `stein_third_derivative`, `S7e`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7f

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

theorem static_field_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (r : ℝ)
    (hr : r = 2 * (d : ℝ) + 6) (γ : ℝ) (hγ : 0 ≤ γ) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (NegSobolev d r) 5,
      |Real.sqrt N *
          (∫ X, Φ (zetaE r (modulatedGibbs (periodicRiesz d s) N γ (withDensityReal ρ)) X)
              ∂(modulatedGibbs (periodicRiesz d s) N γ (withDensityReal ρ)) - ∫ F, Φ F ∂G) -
        (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F
            ![ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x] ∂(withDensityReal ρ) ∂G| ≤ ε := by
  rcases hγ.eq_or_lt with h0 | hpos
  · subst h0
    exact HRS.MC.Sec7.S7z.s7_S7z_product_case_proof hd hs0 hs r hr ρ hρ G hG
  · intro ε hε
    obtain ⟨a, v, C₀, hmode⟩ := HRS.MC.Sec7.S7a.s7_S7a_mode_data_proof hd hs0 hs r hr γ hγ ρ hρ
    obtain ⟨K, hK0, hK⟩ := s7f_R1_bound hd hs0 hs hr hγ hρ hmode G hG
    set ε' : ℝ := ε / (3 + γ) with hε'
    have hε'pos : 0 < ε' := div_pos hε (by linarith)
    obtain ⟨N₁, hN₁⟩ := HRS.MC.Sec7.S7d.s7_S7d_uniform_limits_proof hd hs0 hs r hr hγ hρ hmode G hG
      ε' hε'pos
    have hev : ∀ᶠ N : ℕ in atTop, K / Real.sqrt N ≤ ε' := by
      have h1 : Tendsto (fun N : ℕ => K / Real.sqrt N) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      exact h1.eventually (ge_mem_nhds hε'pos)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hev
    refine ⟨max N₁ N₂, fun N hN hN1 Φ hΦ => ?_⟩
    have hid := s7f_exact_identity hd hs0 hs hr hγ hρ hmode G hG hN1 hΦ
    have hlim := s7f_limit_identity hd hs0 hs hr hγ hρ hmode G hG hΦ
    have hR1 := (hK N hN1 Φ hΦ).trans (hN₂ N (le_trans (le_max_right _ _) hN))
    obtain ⟨hA, hB⟩ := hN₁ N (le_trans (le_max_left _ _) hN) hN1 Φ hΦ
    have hB' := hB hpos
    change |Real.sqrt N * (∫ X, Φ (zetaE r (sed_Q d s N γ ρ) X) ∂(sed_Q d s N γ ρ) - ∫ F, Φ F ∂G) -
      (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F
            ![ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x] ∂(withDensityReal ρ) ∂G| ≤ ε
    rw [hid, ← hlim]
    obtain ⟨hA1, hA2⟩ := abs_le.1 hA
    obtain ⟨hB1, hB2⟩ := abs_le.1 hB'
    obtain ⟨hR1', hR2'⟩ := abs_le.1 hR1
    have e1 := mul_le_mul_of_nonneg_left hB1 hγ
    have e2 := mul_le_mul_of_nonneg_left hB2 hγ
    have hε3 : ε' * (3 + γ) = ε := by rw [hε']; field_simp
    rw [abs_le]
    constructor <;> nlinarith [mul_pos hε'pos hε'pos]

end HRS.MC.Sec7.S7f

end
