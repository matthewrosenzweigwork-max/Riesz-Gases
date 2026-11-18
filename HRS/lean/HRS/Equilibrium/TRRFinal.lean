/-
# TRR final: proof of Lemma 4.18 `thermal_response_rates` (relocated; statement copied verbatim).
-/
import HRS.Equilibrium.TRRAux9

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.TRR

variable {d : ℕ}

section Rates

variable {s : ℝ}

theorem thermal_response_rates_proof (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Euc d => ρ p.1 (Torus.mk p.2)) ∧
    (∀ θ, IsResponse (periodicRiesz d s) (withDensityReal (ρ θ)) β (Torus.cosMode k)
      (fun x => deriv (fun θ' => ρ θ' x) θ / ρ θ x)) ∧
    (∀ θ, HasDerivAt (fun θ' => pair (withDensityReal (ρ θ')) (Torus.cosMode k))
      (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
        (Torus.cosMode k) (Torus.cosMode k)) θ) ∧
    ((d : ℝ) / 2 < s →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun θ => supercriticalBias d s β (ρ θ) (Torus.cosMode k)) ∧
        supercriticalBias d s β (ρ 0) (Torus.cosMode k) = 0 ∧
        HasDerivAt (fun θ => supercriticalBias d s β (ρ θ) (Torus.cosMode k))
          (sphereArea d * Real.Gamma (2 - d / s) * β ^ ((d : ℝ) / s) /
            (2 * s * (d / s) * (d / s - 1) * (1 + β * rieszCoeff d s k) ^ 2)) 0 ∧
        0 < sphereArea d * Real.Gamma (2 - d / s) * β ^ ((d : ℝ) / s) /
            (2 * s * (d / s) * (d / s - 1) * (1 + β * rieszCoeff d s k) ^ 2)) := by
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs0 : 0 ≤ s := by linarith
  refine ⟨trr_clause1 hd hs0 hsd hβ k ρ hρ, trr_clause2 hd hs0 hsd hβ k ρ hρ,
    trr_clause3 hd hs0 hsd hβ k ρ hρ, fun hlt => ?_⟩
  have hspos : 0 < s := by linarith
  have hfun : (fun θ => supercriticalBias d s β (ρ θ) (Torus.cosMode k)) =
      fun θ => biasC d s β * Psi hd hs0 hsd hβ k θ :=
    funext fun θ => trr_bias_eq hd hs0 hsd hβ k ρ hρ θ
  have hpos : 0 < 1 + β * rieszCoeff d s k := by
    have := rieszCoeff_pos hd hs0 hsd k hk
    positivity
  have hp1 : (1 : ℝ) < d / s := by rw [lt_div_iff₀ hspos]; linarith
  have hp2 : (d : ℝ) / s < 2 := by rw [div_lt_iff₀ hspos]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfun]; exact contDiff_const.mul (contDiff_Psi hd hs0 hsd hβ k)
  · rw [trr_bias_eq hd hs0 hsd hβ k ρ hρ 0, Psi_zero hd hs0 hsd hβ k hk, mul_zero]
  · rw [hfun]
    have := (hasDerivAt_Psi_zero hd hs0 hsd hβ k hk).const_mul (biasC d s β)
    convert this using 1
    unfold biasC
    have h1 : (d : ℝ) / s - 1 ≠ 0 := by linarith
    have h2 : (d : ℝ) / s ≠ 0 := by linarith
    have h3 : (1 + β * rieszCoeff d s k) ≠ 0 := hpos.ne'
    have h4 : s ≠ 0 := hspos.ne'
    generalize (d : ℝ) / s = p at *
    field_simp
  · have hA : 0 < sphereArea d := by
      unfold sphereArea
      have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
      positivity
    have hG : 0 < Real.Gamma (2 - d / s) := Real.Gamma_pos_of_pos (by linarith)
    have hB : 0 < β ^ ((d : ℝ) / s) := Real.rpow_pos_of_pos hβ _
    have hden : 0 < 2 * s * (d / s) * (d / s - 1) * (1 + β * rieszCoeff d s k) ^ 2 := by
      have : 0 < (d : ℝ) / s - 1 := by linarith
      have : 0 < (d : ℝ) / s := by linarith
      positivity
    positivity

end Rates

end HRS.TRR

example := (@HRS.TRR.thermal_response_rates_proof : type_of% @HRS.thermal_response_rates)
