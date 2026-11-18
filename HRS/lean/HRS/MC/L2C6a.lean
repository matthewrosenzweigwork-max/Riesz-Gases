import HRS.MC.L2C0
import HRS.MC.L2C3
import HRS.MC.L2C4
import HRS.MC.L2C6Aux1
import HRS.MC.L2C6Aux2

/-!
# Packet L2C-6a: the uniform `L²` covariance bound for the prepared Gaussian limit `η`

Relocated proof of `HRS.MC.L2Cov.l2cs_cov_prepared` (the frozen statement stays `sorry` in
`HRS/MC/L2CovSpec.lean`; the tie `example` is in `HRS/MC/L2C6Tie.lean`).

Route: `η^t(φ) = Y₀(ψ) + g`, `ψ = U^{0,t}φ` smooth (L2C-0), `g` the centred Gaussian noise part of
`gaussian_part` (variance `noiseCovariance`); `E[η²] ≤ 2 E[Y₀(ψ)²] + 2 E[g²]` (`l2c6_second_moment`),
`E[Y₀(ψ)²] = susceptibilityCov ψ ψ ≤ K ‖Q_β ψ‖²` (`l2c6_cov_le`), `‖Q_βψ‖² ≤ C₃ ‖Q_βφ‖²` (L2C-3 (1), `r = 0`),
`‖Q_βφ‖² ≤ (2+2Λ_β)‖φ‖²`; the noise term is L2C-4.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.PDE

namespace HRS.MC.L2C6a

variable {d : ℕ}

/-- (Packet L2C-6a.)  Verbatim copy of `HRS.MC.L2Cov.l2cs_cov_prepared`. -/
theorem l2c6a_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y₀ : Ω → NegSobolev d r) (η : ℝ → Ω → NegSobolev d r),
      IsCenteredGaussianWithCov r (P.map Y₀)
        (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) →
      (∀ T : ℝ, IsLinearFluctuationSolution P R.D R.ρ r R.D.invβ T Y₀ η) →
      ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
        MemLp (fun ω => NegSobolev.eval (η t ω) φ) 2 P ∧
        ∫ ω, NegSobolev.eval (η t ω) φ ^ 2 ∂P ≤ C * PDE.l2NormSq φ := by
  obtain ⟨C3, c3, κ3, hC3, hc3, -, H3⟩ := HRS.MC.L2C3.l2c3_proof R
  obtain ⟨C4, H4⟩ := HRS.MC.L2C4.l2c4_proof R
  obtain ⟨hth, hsm, -⟩ := R.thermal
  have hρc : Continuous R.ρβ := HRS.MC.L2C6Aux.l2c6_cont_of_smooth hsm
  obtain ⟨Λβ, hΛβ⟩ := (isCompact_range hρc).bddAbove
  have hupβ : ∀ x, R.ρβ x ≤ Λβ := fun x => hΛβ ⟨x, rfl⟩
  have hΛβ0 : 0 ≤ Λβ := (hth.1.nonneg 0).trans (hupβ 0)
  have hρ₀c : Continuous R.ρ₀ := HRS.MC.L2C6Aux.l2c6_cont_of_smooth R.hρ₀.smooth
  obtain ⟨Λ₀, hΛ₀⟩ := (isCompact_range hρ₀c).bddAbove
  have hup₀ : ∀ x, R.ρ₀ x ≤ Λ₀ := fun x => hΛ₀ ⟨x, rfl⟩
  have hβ₀ : 0 ≤ R.β₀ := by
    rcases R.hβ₀ with h | ⟨-, h⟩
    · exact h.le
    · exact h.ge
  obtain ⟨K, hK0, hK⟩ := HRS.MC.L2C6Aux.l2c6_cov_le R.hd R.D.hs0 R.D.hsd R.hρ₀.density hup₀ hβ₀
  refine ⟨2 * K * C3 * (2 + 2 * Λβ) + 2 * max C4 0, ?_⟩
  intro Ω _ P _ Y₀ η hY hη t ht φ hφ
  have hψs := (HRS.MC.L2C0.l2c0_proof R φ hφ 0 t le_rfl ht).1
  obtain ⟨hmem, hmom⟩ := HRS.MC.L2C6Aux.l2c6_second_moment P R.D R.ρ r R.D.invβ _ Y₀ η hY hη ht hφ hψs
  refine ⟨hmem, hmom.trans ?_⟩
  set ψ := propagator R.D R.ρ 0 t φ with hψ
  have hψc : Continuous ψ := HRS.MC.L2C6Aux.l2c6_cont_of_smooth hψs
  have hA : 0 ≤ PDE.l2NormSq φ := integral_nonneg fun x => sq_nonneg _
  have hcov := hK ψ hψc (pair (withDensityReal R.ρβ) ψ)
  have hW : ∫ x, (ψ x - pair (withDensityReal R.ρβ) ψ) ^ 2 =
      PDE.l2NormSq (projMean (withDensityReal R.ρβ) ψ) := rfl
  rw [hW] at hcov
  have h3 := (H3 φ hφ 0 t le_rfl ht).1
  have hexp : Real.exp (-c3 * (t - 0)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hQ := HRS.MC.L2C4.l2c4_Q_bound hth.1 hρc hupβ (HRS.MC.L2C6Aux.l2c6_cont_of_smooth hφ)
  have hQ0 : 0 ≤ PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := integral_nonneg fun x => sq_nonneg _
  have h3' : PDE.l2NormSq (projMean (withDensityReal R.ρβ) ψ) ≤
      C3 * ((2 + 2 * Λβ) * PDE.l2NormSq φ) := by
    refine h3.trans ?_
    calc C3 * Real.exp (-c3 * (t - 0)) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ)
        ≤ C3 * 1 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := by
          gcongr
      _ = C3 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := by ring
      _ ≤ _ := by gcongr
  have h4 := (H4 φ hφ t ht).1
  have hn : max (noiseCovariance R.D R.ρ R.D.invβ t φ φ) 0 ≤ max C4 0 * PDE.l2NormSq φ :=
    max_le (h4.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hA))
      (mul_nonneg (le_max_right _ _) hA)
  have hc : susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀ ψ ψ ≤
      K * (C3 * ((2 + 2 * Λβ) * PDE.l2NormSq φ)) :=
    hcov.trans (mul_le_mul_of_nonneg_left h3' hK0)
  nlinarith [hc, hn]

end HRS.MC.L2C6a
