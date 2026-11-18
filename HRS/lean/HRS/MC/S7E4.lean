import HRS.MC.S7E4Aux5
import HRS.MC.S7E3a
import HRS.MC.S7E3b

/-!
# Packet `s7_E4_normalized_clt`

Route.  By `E3a`/`E3b`, `sigma_eps^2 = E Q_eps^2 -> infinity`.  For a sequence `eps_n -> 0+` and any accuracy
`delta`, the finite section `S_L` of `Q_{eps_n}` (`L` large) is `delta`-close in `L^2` and, by the spectral
theorem for `C^{1/2} H C^{1/2}` (`S7E4Aux1`, `S7E4Aux5`), has the law of `(1/2) sum_k a_k (g_k^2 - 1)` with
`|a_k| <= Lam` (`S7E4Aux4`: Schur test for the cut-off kernel).  The abstract argument of `S7E4Aux3`
(`W4` and Slutsky) concludes.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.E4

open HRS HRS.Sec7

variable {d : ℕ}

theorem e4_ratio_top {l : Filter ℝ} {X D : ℝ → ℝ} (hD : Tendsto D l atTop)
    (hT : Tendsto (fun ε => X ε / D ε) l (𝓝 1)) : Tendsto X l atTop := by
  have h := Tendsto.pos_mul_atTop one_pos hT hD
  refine h.congr' ?_
  filter_upwards [hD.eventually_gt_atTop 0] with ε hε
  exact div_mul_cancel₀ _ hε.ne'

theorem e4_sigma_top (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ) (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε)) :
    Tendsto (fun ε : ℝ => ∫ ω, Q ε ω ^ 2 ∂P) (𝓝[>] 0) atTop := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0' : 0 < s := by linarith
  set J := localDivCoeff d s ρ φ with hJdef
  have hJ : 0 < J := localDivCoeff_pos hd hs0' hsd ρ hρ φ hφ hnc
  rcases hs.eq_or_lt with hcrit | hsup
  · have hT := E3a.s7_E3a_critical_variance_proof hd hcrit.symm hβ ρ hρ φ hφ hnc e he P G hG Q hQ
    have h1 : Tendsto (fun ε : ℝ => 1 / ε) (𝓝[>] 0) atTop := by
      simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
    have hD : Tendsto (fun ε : ℝ => J / 2 * Real.log (1 / ε)) (𝓝[>] 0) atTop :=
      (Real.tendsto_log_atTop.comp h1).const_mul_atTop (by positivity)
    exact e4_ratio_top hD hT
  · have hT := E3b.s7_E3b_supercritical_variance_proof hd hsup hsd hβ ρ hρ φ hφ hnc e he P G hG Q hQ
    have hpos2 : 0 < 2 * s - d := by linarith
    have h1 : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
    have hpow : Tendsto (fun ε : ℝ => (ε⁻¹) ^ (2 * s - d)) (𝓝[>] 0) atTop :=
      (tendsto_rpow_atTop hpos2).comp h1
    have hD : Tendsto (fun ε : ℝ => J / (2 * (2 * s - d)) * ε ^ ((d : ℝ) - 2 * s)) (𝓝[>] 0) atTop := by
      have := hpow.const_mul_atTop (show 0 < J / (2 * (2 * s - d)) by positivity)
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Real.inv_rpow (le_of_lt hε), ← Real.rpow_neg (le_of_lt hε)]
      congr 2; ring
    exact e4_ratio_top hD hT


theorem s7_E4_normalized_clt_proof (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ) (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε)) :
    ∀ F : ℝ → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun ε : ℝ => ∫ ω, F (Q ε ω / Real.sqrt (∫ ω', Q ε ω' ^ 2 ∂P)) ∂P) (𝓝[>] 0)
        (𝓝 (∫ y, F y ∂(gaussianReal 0 1))) := by
  intro F hF hFb
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0' : 0 < s := by linarith
  have hs0 : 0 ≤ s := hs0'.le
  obtain ⟨Λ, hΛ, hquad⟩ := E4A4.quad_bound hd hs0 hsd hρ hφ he
  obtain ⟨c, hc0, hc1, hall⟩ := E1.s7_E1_variance_sandwich_proof hd hs0 hsd hβ ρ hρ
  have hadm := (E1b.s7_E1b_cutoff_kernel_admissible_proof hd hs0 hsd ρ hρ φ hφ).1
  have hQ2 : ∀ ε, 0 < ε → MemLp (Q ε) 2 P := fun ε hε => by
    obtain ⟨hm, hsy, hL2⟩ := hadm ε hε
    exact (hall e he P G hG _ hm hsy hL2 (Q ε) (hQ ε hε).1 (hQ ε hε).2).1
  have hσ2 := e4_sigma_top hd hs hsd hβ ρ hρ φ hφ hnc e he P G hG Q hQ
  -- sequences
  refine Filter.tendsto_of_seq_tendsto fun u hu => ?_
  have hpos : ∀ᶠ n in atTop, 0 < u n := by
    have := (tendsto_nhdsWithin_iff.1 hu).2
    filter_upwards [this] with n hn using hn
  have hvar : Tendsto (fun n => ∫ ω, Q (u n) ω ^ 2 ∂P) atTop atTop := hσ2.comp hu
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (hpos.and (hvar.eventually_gt_atTop 0))
  rw [← tendsto_add_atTop_iff_nat n0]
  have hvar' : Tendsto (fun n : ℕ => ∫ ω, Q (u (n + n0)) ω ^ 2 ∂P) atTop atTop :=
    hvar.comp (tendsto_add_atTop_nat n0)
  have key := E4A3.normalized_clt (P := P) (fun n => Q (u (n + n0)))
    (fun n => hQ2 _ (hn0 (n + n0) (by omega)).1)
    (fun n => Real.sqrt (∫ ω, Q (u (n + n0)) ω ^ 2 ∂P))
    (fun n => Real.sqrt_pos.2 (hn0 (n + n0) (by omega)).2)
    (fun n => Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _))
    (Real.tendsto_sqrt_atTop.comp hvar') (Λ := Λ) hΛ
    (fun n δ hδ => E4A5.approx hd hs0 hsd hβ hρ hφ he hG hquad hΛ (hn0 (n + n0) (by omega)).1
      (hQ _ (hn0 (n + n0) (by omega)).1).1 (hQ _ (hn0 (n + n0) (by omega)).1).2 hδ) F hF hFb
  exact key

end HRS.MC.Sec7.E4

end
