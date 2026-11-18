import HRS.MC.L2C0
import HRS.MC.L2C1
import HRS.MC.L2C4
import HRS.MC.L2C6Aux1
import HRS.MC.L2C6Aux2

/-!
# Packet L2C-6b: the uniform `L²` covariance bound for the stationary Gaussian limit `η̄`

Relocated proof of `HRS.MC.L2Cov.l2cs_cov_stationary` (the frozen statement stays `sorry` in
`HRS/MC/L2CovSpec.lean`; the tie `example` is in `HRS/MC/L2C6Tie.lean`).

Route: as in L2C-6a with the frozen coefficient `ρ_β`: `E[η̄²] ≤ 2 C_β(ψ,ψ) + 2 noiseCovariance`,
`ψ = Ū^{0,t}φ` smooth (L2C-0), `C_β(ψ,ψ) ≤ K ‖Q_βψ‖² = K ‖S_β(t)φ‖² ≤ K C₁ ‖Q_βφ‖²` (L2C-1 (1)),
`‖Q_βφ‖² ≤ (2+2Λ_β)‖φ‖²`; the noise term is the frozen conjunct of L2C-4.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.PDE

namespace HRS.MC.L2C6b

variable {d : ℕ}

/-- (Packet L2C-6b.)  Verbatim copy of `HRS.MC.L2Cov.l2cs_cov_stationary`. -/
theorem l2c6b_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Ys₀ : Ω → NegSobolev d r) (ηs : ℝ → Ω → NegSobolev d r),
      IsCenteredGaussianWithCov r (P.map Ys₀)
        (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β) →
      (∀ T : ℝ, IsLinearFluctuationSolution P R.D (fun _ => R.ρβ) r R.D.invβ T Ys₀ ηs) →
      ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
        MemLp (fun ω => NegSobolev.eval (ηs t ω) φ) 2 P ∧
        ∫ ω, NegSobolev.eval (ηs t ω) φ ^ 2 ∂P ≤ C * PDE.l2NormSq φ := by
  obtain ⟨C1, c1, hC1, hc1, H1⟩ := HRS.MC.L2C1.l2c1_proof R
  obtain ⟨C4, H4⟩ := HRS.MC.L2C4.l2c4_proof R
  obtain ⟨hth, hsm, -⟩ := R.thermal
  have hρc : Continuous R.ρβ := HRS.MC.L2C6Aux.l2c6_cont_of_smooth hsm
  obtain ⟨Λβ, hΛβ⟩ := (isCompact_range hρc).bddAbove
  have hupβ : ∀ x, R.ρβ x ≤ Λβ := fun x => hΛβ ⟨x, rfl⟩
  have hΛβ0 : 0 ≤ Λβ := (hth.1.nonneg 0).trans (hupβ 0)
  have hβ : 0 ≤ R.β := R.hβ.le
  obtain ⟨K, hK0, hK⟩ := HRS.MC.L2C6Aux.l2c6_cov_le R.hd R.D.hs0 R.D.hsd hth.1 hupβ hβ
  refine ⟨2 * K * C1 * (2 + 2 * Λβ) + 2 * max C4 0, ?_⟩
  intro Ω _ P _ Ys₀ ηs hY hη t ht φ hφ
  have hψs := (HRS.MC.L2C0.l2c0_proof R φ hφ 0 t le_rfl ht).2
  obtain ⟨hmem, hmom⟩ := HRS.MC.L2C6Aux.l2c6_second_moment P R.D (fun _ => R.ρβ) r R.D.invβ _ Ys₀ ηs
    hY hη ht hφ hψs
  refine ⟨hmem, hmom.trans ?_⟩
  set ψ := propagator R.D (fun _ => R.ρβ) 0 t φ with hψ
  have hψc : Continuous ψ := HRS.MC.L2C6Aux.l2c6_cont_of_smooth hψs
  have hA : 0 ≤ PDE.l2NormSq φ := integral_nonneg fun x => sq_nonneg _
  have hcov := hK ψ hψc (pair (withDensityReal R.ρβ) ψ)
  have hW : ∫ x, (ψ x - pair (withDensityReal R.ρβ) ψ) ^ 2 =
      PDE.l2NormSq (PDE.equilibriumSemigroup R.D R.ρβ t φ) := rfl
  rw [hW] at hcov
  have h1 := (H1 φ hφ t ht).1
  have hexp : Real.exp (-c1 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hQ := HRS.MC.L2C4.l2c4_Q_bound hth.1 hρc hupβ (HRS.MC.L2C6Aux.l2c6_cont_of_smooth hφ)
  have hQ0 : 0 ≤ PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := integral_nonneg fun x => sq_nonneg _
  have h1' : PDE.l2NormSq (PDE.equilibriumSemigroup R.D R.ρβ t φ) ≤
      C1 * ((2 + 2 * Λβ) * PDE.l2NormSq φ) := by
    refine h1.trans ?_
    calc C1 * Real.exp (-c1 * t) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ)
        ≤ C1 * 1 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := by
          gcongr
      _ = C1 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := by ring
      _ ≤ _ := by gcongr
  have h4 := (H4 φ hφ t ht).2
  have hn : max (noiseCovariance R.D (fun _ => R.ρβ) R.D.invβ t φ φ) 0 ≤ max C4 0 * PDE.l2NormSq φ :=
    max_le (h4.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hA))
      (mul_nonneg (le_max_right _ _) hA)
  have hc : susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β ψ ψ ≤
      K * (C1 * ((2 + 2 * Λβ) * PDE.l2NormSq φ)) :=
    hcov.trans (mul_le_mul_of_nonneg_left h1' hK0)
  nlinarith [hc, hn]

end HRS.MC.L2C6b
