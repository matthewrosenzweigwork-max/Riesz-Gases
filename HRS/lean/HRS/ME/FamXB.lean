/-
# HRS.ME.FamX (packet X2, part B): data for the frozen `critical_family_fixed_limsup`

`sharpness_data`: the constants of the sharpness lower bound, uniform in the thermal family `ρ`:
a lower bound `v ≤ ∫₀^R |√N E[Y³]| dθ` for `N ≥ N₁`, and the pointwise bound
`|√N E[Y³]| ≤ K · √N · W₂(law Y, Gaussian)` for every thermal family and every `N ≥ 2`, `θ ∈ [0,R]`.
These are the two ingredients of `critical_family_sharpness_lower` (`HRS/ME/FamWE.lean`), which are
re-assembled here without modifying that file.

`h_continuous`: the integrand `θ ↦ |√N E[Y_{N,θ}³]|` is continuous (for `N ≥ 2`).
-/
import HRS.ME.FamWE

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.FamX

open HRS

/-- The integrand of the sharpness bound is continuous in `θ`. -/
theorem h_continuous {d : ℕ} (hd : 2 ≤ d) {β : ℝ} (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0)
    {N : ℕ} (hN : 2 ≤ N) :
    Continuous (fun θ : ℝ => |Real.sqrt N * ∫ X, rateY d ((d : ℝ) / 2) k β N θ X ^ 3
      ∂(rateGibbs d ((d : ℝ) / 2) k β θ N)|) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : (d : ℝ) / 2 ≤ (d : ℝ) / 2 := le_rfl
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨_, hcV, _, hV⟩ := finite_response_rates hd hs hsd β hβ k hk N hN
  have hder : (fun θ : ℝ => Real.sqrt N * ∫ X, rateY d ((d : ℝ) / 2) k β N θ X ^ 3
      ∂(rateGibbs d ((d : ℝ) / 2) k β θ N)) =
      deriv (rateVarN d ((d : ℝ) / 2) k β N) :=
    funext fun θ => (hV θ).deriv.symm
  have hcont : Continuous (fun θ : ℝ => Real.sqrt N * ∫ X, rateY d ((d : ℝ) / 2) k β N θ X ^ 3
      ∂(rateGibbs d ((d : ℝ) / 2) k β θ N)) := by
    rw [hder]
    exact hcV.continuous_deriv (by norm_num)
  exact hcont.abs

/-- **Data of the sharpness lower bound.**  Uniform in the thermal family `ρ`: a constant `K`, a
level `v > 0`, a threshold `N₁ ≥ 2` with `v ≤ ∫₀^R |√N E Y³|` for `N ≥ N₁`, and the pointwise
bound `|√N E Y³| ≤ K √N W₂` for every thermal family `ρ`, `N ≥ 2`, `θ ∈ [0,R]`. -/
theorem sharpness_data {d : ℕ} (hd : 2 ≤ d) {β : ℝ} (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) :
    ∃ K v : ℝ, 0 < K ∧ 0 < v ∧ ∃ N₁ : ℕ, 2 ≤ N₁ ∧
      (∀ N : ℕ, N₁ ≤ N → v ≤ ∫ θ in (0:ℝ)..(16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
          |Real.sqrt N * ∫ X, rateY d ((d : ℝ) / 2) k β N θ X ^ 3
            ∂(rateGibbs d ((d : ℝ) / 2) k β θ N)|) ∧
      (∀ ρ : ℝ → Torus d → ℝ,
        (∀ θ, IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) (rateV k β θ) β (ρ θ)) →
        ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Set.Icc (0:ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
          ENNReal.ofReal |Real.sqrt N * ∫ X, rateY d ((d : ℝ) / 2) k β N θ X ^ 3
            ∂(rateGibbs d ((d : ℝ) / 2) k β θ N)| ≤
          ENNReal.ofReal K * (ENNReal.ofReal (Real.sqrt N) *
            wassersteinE 2 (Main.rateLaw d ((d : ℝ) / 2) k β N θ)
              (Main.rateGaussian d ((d : ℝ) / 2) k β (ρ θ)))) := by
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (d : ℝ) / 2 := ⟨_, rfl⟩
  rw [← hsdef]
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hsd : s < d := by rw [hsdef]; linarith
  have hs : (d : ℝ) / 2 ≤ s := hsdef.symm.le
  have hd1 : 1 ≤ d := by omega
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = rieszCoeff d s k := ⟨_, rfl⟩
  rw [← hgdef]
  have hg : 0 ≤ g := by rw [hgdef]; exact (rieszCoeff_pos hd hs0 hsd k hk).le
  have h1g : 0 < 1 + β * g := by
    have := mul_nonneg hβ.le hg
    linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 16 * (1 + β * g) := ⟨_, rfl⟩
  rw [← hRdef]
  obtain ⟨v0, hv0def⟩ : ∃ v0 : ℝ, v0 = 1 / (2 * (1 + β * g)) := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hv0 : 0 < v0 := by rw [hv0def]; exact div_pos one_pos (by linarith)
  have hRv : 2 / R = v0 / 4 := by
    rw [hRdef, hv0def]; field_simp; ring
  -- a canonical thermal family
  have hex : ∀ θ : ℝ, ∃ ρ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ := fun θ =>
    let ⟨ρ, h, _, _⟩ := PDE.MFThermalAssembly.thermal_exists_continuous hd1 s hs0 hsd
      (rateV k β θ) (Q32c.q32c_rateV_continuous k θ) β hβ
    ⟨ρ, h⟩
  choose ρs hρs using hex
  obtain ⟨D, hD2, hDtail⟩ := response_subGaussian_proof hd hs hsd β hβ k hk ρs hρs 0 R
  have hDpos : 0 < D := by linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 3 * Real.sqrt (32 * D ^ 2) := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hKdef]; positivity
  -- the variance at `θ = 0` converges to `v0`
  have hlim := HRS.ME.FamW.rateVarN_zero_tendsto hd hs hsd hβ k hk (ρs 0) (hρs 0)
  have hcov0 : susceptibilityCov (periodicRiesz d s) (withDensityReal (ρs 0)) β
      (Torus.cosMode k) (Torus.cosMode k) = v0 := by
    rw [HRS.ME.FamW.thermal_rateV_zero hd hs0 hsd hβ k (ρs 0) (hρs 0), hv0def, hgdef]
    exact HRS.ME.FamW.susceptibilityCov_one_cos hd hs0 hsd hβ k hk
  rw [hcov0] at hlim
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    (hlim.eventually (lt_mem_nhds (show v0 / 2 < v0 by linarith)))
  refine ⟨K, v0 / 4, hKpos, by linarith, max N1 2, le_max_right _ _, ?_, ?_⟩
  · intro N hN
    have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hN1' : N1 ≤ N := le_trans (le_max_left _ _) hN
    have hV : v0 / 2 < rateVarN d s k β N 0 := hN1 N hN1'
    have hvar := HRS.ME.FamW.rate_variation_lower hd hs hsd hβ k hk hN2 hRpos
    rw [hRv] at hvar
    linarith
  · intro ρ hρ N hN θ hθ
    have hN0 : 0 < N := by omega
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
    have hρeq : ρ θ = ρs θ :=
      HRS.ME.FamW.thermal_eq_of_thermal hd hs0 hsd hβ k θ _ _ (hρ θ) (hρs θ)
    have hp := HRS.ME.FamW.third_moment_pointwise hd hs hsd hβ k hN0 θ
      (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρs θ)) β
        (Torus.cosMode k) (Torus.cosMode k)) D hDpos
      (fun x hx => hDtail x hx N hN θ hθ)
    rw [← hKdef] at hp
    have hG : Main.rateGaussian d s k β (ρ θ) = gaussianReal 0
        (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρs θ)) β
          (Torus.cosMode k) (Torus.cosMode k)).toNNReal := by
      rw [hρeq]; rfl
    rw [hG]
    have hL : Main.rateLaw d s k β N θ = (rateGibbs d s k β θ N).map (rateY d s k β N θ) := rfl
    rw [hL]
    calc ENNReal.ofReal |Real.sqrt N * ∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N)|
        = ENNReal.ofReal (Real.sqrt N) *
            ENNReal.ofReal |∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N)| := by
          rw [abs_mul, abs_of_pos hsqrt, ENNReal.ofReal_mul hsqrt.le]
      _ ≤ ENNReal.ofReal (Real.sqrt N) * (ENNReal.ofReal K *
            wassersteinE 2 ((rateGibbs d s k β θ N).map (rateY d s k β N θ))
              (gaussianReal 0 (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρs θ)) β
                (Torus.cosMode k) (Torus.cosMode k)).toNNReal)) := mul_le_mul' le_rfl hp
      _ = ENNReal.ofReal K * (ENNReal.ofReal (Real.sqrt N) *
            wassersteinE 2 ((rateGibbs d s k β θ N).map (rateY d s k β N θ))
              (gaussianReal 0 (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρs θ)) β
                (Torus.cosMode k) (Torus.cosMode k)).toNNReal)) := by ring

end HRS.ME.FamX
