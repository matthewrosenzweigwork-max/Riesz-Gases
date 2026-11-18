import HRS.MC.S7E3aAux8

/-!
# Packet `s7_E3a_critical_variance`

Route.  For `eps > 0` the chaos limit `Q_eps` of the cut-off pair kernel satisfies
`E Q_eps^2 <= (1/2) ||h°_eps||^2` (`E1`) and, for every `eta > 0`,
`E Q_eps^2 >= (1 - 4 eta)/2 ||h°_eps||^2 - K_eta` (file `S7E3aAux6`: `C = 1 - B` with `B` compact along the
basis (`S7E3aAux3`) and the rows of `H_eps` uniformly bounded in `l^2` (`S7E3aAux4`)).  By `localDiv_critical`,
`||h°_eps||^2 = J log(1/eps) + O(1)`; the ratio lemma `S7E3aAux7` gives the claim.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.E3a

open HRS HRS.Sec7

variable {d : ℕ}

theorem s7_E3a_critical_variance_proof (hd : 2 ≤ d) {s : ℝ} (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ) (he : IsONBL2Zero (withDensityReal ρ) e)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε)) :
    Tendsto (fun ε : ℝ => (∫ ω, Q ε ω ^ 2 ∂P) /
        (localDivCoeff d s ρ φ / 2 * Real.log (1 / ε))) (𝓝[>] 0) (𝓝 1) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  set J := localDivCoeff d s ρ φ with hJdef
  have hJ : 0 < J := localDivCoeff_pos hd hs0 hsd ρ hρ φ hφ hnc
  obtain ⟨hup, hlow⟩ := E3Aux8.e3_two_sided hd hs0.le hsd hβ ρ hρ φ hφ e he P G hG Q hQ
  obtain ⟨C, ε₀, hε₀, hcr⟩ := localDiv_critical hd hcrit ρ hρ φ hφ hnc
  have h1 : Tendsto (fun ε : ℝ => 1 / ε) (𝓝[>] 0) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
  have hlog : Tendsto (fun ε : ℝ => Real.log (1 / ε)) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp h1
  have hL : Tendsto (fun ε : ℝ => J * Real.log (1 / ε)) (𝓝[>] 0) atTop :=
    hlog.const_mul_atTop hJ
  have hD : Tendsto (fun ε : ℝ => J / 2 * Real.log (1 / ε)) (𝓝[>] 0) atTop :=
    hlog.const_mul_atTop (by positivity)
  refine E3Aux7.e3_ratio (T := fun ε => s7_hcNorm2 d ρ (hCut d s φ ε)) hD ?_ hup hlow
  -- the ratio of the first moment
  have hrem : Tendsto (fun ε : ℝ => (s7_hcNorm2 d ρ (hCut d s φ ε) - J * Real.log (1 / ε)) /
      (J * Real.log (1 / ε))) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := |C|)).div_atTop hL)
    have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo 0 ε₀ := Ioo_mem_nhdsGT hε₀
    filter_upwards [hε, hL.eventually_gt_atTop 0] with ε hε hpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    exact (hcr ε hε).trans (le_abs_self C)
  have := hrem.const_add 1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hL.eventually_gt_atTop 0] with ε hpos
  have hne : J * Real.log (1 / ε) ≠ 0 := hpos.ne'
  have hJne : J ≠ 0 := hJ.ne'
  have hlne : Real.log (1 / ε) ≠ 0 := by
    intro h; apply hne; rw [h, mul_zero]
  show 1 + (s7_hcNorm2 d ρ (hCut d s φ ε) - J * Real.log (1 / ε)) / (J * Real.log (1 / ε)) =
    s7_hcNorm2 d ρ (hCut d s φ ε) / (2 * (J / 2 * Real.log (1 / ε)))
  field_simp
  ring

end HRS.MC.Sec7.E3a

end
