import HRS.MC.S7E3aAux8

/-!
# Packet `s7_E3b_supercritical_variance`

Route.  For `eps > 0` the chaos limit `Q_eps` of the cut-off pair kernel satisfies
`E Q_eps^2 <= (1/2) ||h°_eps||^2` (`E1`) and, for every `eta > 0`,
`E Q_eps^2 >= (1 - 4 eta)/2 ||h°_eps||^2 - K_eta` (file `S7E3bAux6`: `C = 1 - B` with `B` compact along the
basis (`S7E3bAux3`) and the rows of `H_eps` uniformly bounded in `l^2` (`S7E3bAux4`)).  By `localDiv_critical`,
`||h°_eps||^2 = J log(1/eps) + O(1)`; the ratio lemma `S7E3bAux7` gives the claim.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.E3b

open HRS HRS.Sec7

variable {d : ℕ}

theorem s7_E3b_supercritical_variance_proof (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 < s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ) (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε)) :
    Tendsto (fun ε : ℝ => (∫ ω, Q ε ω ^ 2 ∂P) /
        (localDivCoeff d s ρ φ / (2 * (2 * s - d)) * ε ^ ((d : ℝ) - 2 * s))) (𝓝[>] 0) (𝓝 1) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hpos2 : 0 < 2 * s - d := by linarith
  set J := localDivCoeff d s ρ φ with hJdef
  have hJ : 0 < J := localDivCoeff_pos hd hs0 hsd ρ hρ φ hφ hnc
  obtain ⟨hup, hlow⟩ := E3Aux8.e3_two_sided hd hs0.le hsd hβ ρ hρ φ hφ e he P G hG Q hQ
  have hT := localDiv_supercritical hd hs hsd ρ hρ φ hφ hnc
  have h1 : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have hpow : Tendsto (fun ε : ℝ => (ε⁻¹) ^ (2 * s - d)) (𝓝[>] 0) atTop :=
    (tendsto_rpow_atTop hpos2).comp h1
  have hD : Tendsto (fun ε : ℝ => J / (2 * (2 * s - d)) * ε ^ ((d : ℝ) - 2 * s)) (𝓝[>] 0) atTop := by
    have := hpow.const_mul_atTop (show 0 < J / (2 * (2 * s - d)) by positivity)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.inv_rpow (le_of_lt hε), ← Real.rpow_neg (le_of_lt hε)]
    congr 2; ring
  refine E3Aux7.e3_ratio (T := fun ε => s7_hcNorm2 d ρ (hCut d s φ ε)) hD ?_ hup hlow
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have : (2 : ℝ) * (J / (2 * (2 * s - d)) * ε ^ ((d : ℝ) - 2 * s)) = J / (2 * s - d) * ε ^ ((d : ℝ) - 2 * s) := by
    field_simp
  rw [this]
  rfl

end HRS.MC.Sec7.E3b

end
