import HRS.MC.L2C0
import HRS.MC.L2C1
import HRS.MC.L2C3
import HRS.MC.L2C5
import HRS.MC.L2C6Aux1
import HRS.MC.L2C6Aux2
import HRS.MC.L2C6cAux2

/-!
# Packet L2C-6c: exponential `L²` relaxation of the coupled difference `η - η̄`

Relocated proof of `HRS.MC.L2Cov.l2cs_cov_difference` (the frozen statement stays `sorry` in
`HRS/MC/L2CovSpec.lean`; the tie `example` is in `HRS/MC/L2C6cTie.lean`).

Route: `η^t(φ) - η̄^t(φ) = [Y₀(ψ) - Ys₀(ψ')] + [G - Gs]`, `ψ = U^{0,t}φ`, `ψ' = Ū^{0,t}φ` (smooth by L2C-0);
`E[(·)²] ≤ 4 C₀(ψ,ψ) + 4 C_β(ψ',ψ') + 2 max(Σ₁₁ + Σ₂₂ - 2Σ₁₂, 0)` (`l2c6c_second_moment`, no independence
needed), the first by `susceptibilityCov ≤ K ‖Q_β ψ‖²` and L2C-3 (1), the second by L2C-1 (1), the third by L2C-5.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.PDE

namespace HRS.MC.L2C6c

variable {d : ℕ}

/-- (Packet L2C-6c.)  Verbatim copy of `HRS.MC.L2Cov.l2cs_cov_difference`. -/
theorem l2c6c_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∃ C c : ℝ, 0 < c ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r),
      IsCenteredGaussianWithCov r (P.map Y₀)
        (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) →
      IsCenteredGaussianWithCov r (P.map Ys₀)
        (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β) →
      IndepFun Y₀ Ys₀ P →
      (∀ T : ℝ, IsLinearFluctuationSolution P R.D R.ρ r R.D.invβ T Y₀ η) →
      (∀ T : ℝ, IsLinearFluctuationSolution P R.D (fun _ => R.ρβ) r R.D.invβ T Ys₀ ηs) →
      IsSameNoise R.D R.ρ (fun _ => R.ρβ) r P Y₀ Ys₀ η ηs →
      ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
        MemLp (fun ω => NegSobolev.eval (η t ω) φ - NegSobolev.eval (ηs t ω) φ) 2 P ∧
        ∫ ω, (NegSobolev.eval (η t ω) φ - NegSobolev.eval (ηs t ω) φ) ^ 2 ∂P ≤
          C * Real.exp (-c * t) * PDE.l2NormSq φ := by
  obtain ⟨C3, c3, κ3, hC3, hc3, -, H3⟩ := HRS.MC.L2C3.l2c3_proof R
  obtain ⟨C1, c1, hC1, hc1, H1⟩ := HRS.MC.L2C1.l2c1_proof R
  obtain ⟨C5, c5, hc5, H5⟩ := HRS.MC.L2C5.l2c5_proof R
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
  obtain ⟨K0, hK00, hK0⟩ := HRS.MC.L2C6Aux.l2c6_cov_le R.hd R.D.hs0 R.D.hsd R.hρ₀.density hup₀ hβ₀
  obtain ⟨Kb, hKb0, hKb⟩ := HRS.MC.L2C6Aux.l2c6_cov_le R.hd R.D.hs0 R.D.hsd hth.1 hupβ R.hβ.le
  set c : ℝ := min c3 (min c1 c5) with hcdef
  have hcpos : 0 < c := lt_min hc3 (lt_min hc1 hc5)
  have hcc3 : c ≤ c3 := min_le_left _ _
  have hcc1 : c ≤ c1 := (min_le_right _ _).trans (min_le_left _ _)
  have hcc5 : c ≤ c5 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨4 * K0 * C3 * (2 + 2 * Λβ) + 4 * Kb * C1 * (2 + 2 * Λβ) + 2 * max C5 0, c, hcpos, ?_⟩
  intro Ω _ P _ Y₀ Ys₀ η ηs hY hYs _ hη hηs hN t ht φ hφ
  obtain ⟨hψs, hψs'⟩ := HRS.MC.L2C0.l2c0_proof R φ hφ 0 t le_rfl ht
  obtain ⟨hmem, hmom⟩ := l2c6c_second_moment P R.D R.ρ (fun _ => R.ρβ) r _ _ Y₀ Ys₀ η ηs hY hYs hη hηs
    hN ht hφ hψs hψs'
  refine ⟨hmem, hmom.trans ?_⟩
  set ψ := propagator R.D R.ρ 0 t φ with hψ
  set ψ' := propagator R.D (fun _ => R.ρβ) 0 t φ with hψ'
  have hψc : Continuous ψ := HRS.MC.L2C6Aux.l2c6_cont_of_smooth hψs
  have hψc' : Continuous ψ' := HRS.MC.L2C6Aux.l2c6_cont_of_smooth hψs'
  have hA : 0 ≤ PDE.l2NormSq φ := integral_nonneg fun x => sq_nonneg _
  have hE : Real.exp (-c * t) > 0 := Real.exp_pos _
  have hE3 : Real.exp (-c3 * (t - 0)) ≤ Real.exp (-c * t) := by
    apply Real.exp_le_exp.2; nlinarith
  have hE1 : Real.exp (-c1 * t) ≤ Real.exp (-c * t) := by
    apply Real.exp_le_exp.2; nlinarith
  have hE5 : Real.exp (-c5 * t) ≤ Real.exp (-c * t) := by
    apply Real.exp_le_exp.2; nlinarith
  have hQ := HRS.MC.L2C4.l2c4_Q_bound hth.1 hρc hupβ (HRS.MC.L2C6Aux.l2c6_cont_of_smooth hφ)
  have hQ0 : 0 ≤ PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := integral_nonneg fun x => sq_nonneg _
  -- initial field of the prepared system
  have hcov := hK0 ψ hψc (pair (withDensityReal R.ρβ) ψ)
  have hW : ∫ x, (ψ x - pair (withDensityReal R.ρβ) ψ) ^ 2 =
      PDE.l2NormSq (projMean (withDensityReal R.ρβ) ψ) := rfl
  rw [hW] at hcov
  have h3 := (H3 φ hφ 0 t le_rfl ht).1
  have h3' : PDE.l2NormSq (projMean (withDensityReal R.ρβ) ψ) ≤
      C3 * Real.exp (-c * t) * ((2 + 2 * Λβ) * PDE.l2NormSq φ) := by
    refine h3.trans ?_
    calc C3 * Real.exp (-c3 * (t - 0)) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ)
        ≤ C3 * Real.exp (-c * t) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := by gcongr
      _ ≤ _ := by gcongr
  have hc0 : susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀ ψ ψ ≤
      K0 * (C3 * Real.exp (-c * t) * ((2 + 2 * Λβ) * PDE.l2NormSq φ)) :=
    hcov.trans (mul_le_mul_of_nonneg_left h3' hK00)
  -- stationary initial field
  have hcov' := hKb ψ' hψc' (pair (withDensityReal R.ρβ) ψ')
  have hW' : ∫ x, (ψ' x - pair (withDensityReal R.ρβ) ψ') ^ 2 =
      PDE.l2NormSq (PDE.equilibriumSemigroup R.D R.ρβ t φ) := rfl
  rw [hW'] at hcov'
  have h1 := (H1 φ hφ t ht).1
  have h1' : PDE.l2NormSq (PDE.equilibriumSemigroup R.D R.ρβ t φ) ≤
      C1 * Real.exp (-c * t) * ((2 + 2 * Λβ) * PDE.l2NormSq φ) := by
    refine h1.trans ?_
    calc C1 * Real.exp (-c1 * t) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ)
        ≤ C1 * Real.exp (-c * t) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := by gcongr
      _ ≤ _ := by gcongr
  have hcb : susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β ψ' ψ' ≤
      Kb * (C1 * Real.exp (-c * t) * ((2 + 2 * Λβ) * PDE.l2NormSq φ)) :=
    hcov'.trans (mul_le_mul_of_nonneg_left h1' hKb0)
  -- noise
  have h5 := H5 φ hφ t ht
  have hn : max (crossNoiseCov R.D R.D.invβ R.ρ R.ρ t t φ φ +
        crossNoiseCov R.D R.D.invβ (fun _ => R.ρβ) (fun _ => R.ρβ) t t φ φ -
        2 * crossNoiseCov R.D R.D.invβ R.ρ (fun _ => R.ρβ) t t φ φ) 0 ≤
      max C5 0 * Real.exp (-c * t) * PDE.l2NormSq φ := by
    refine max_le ?_ (by positivity)
    refine h5.trans ?_
    calc C5 * Real.exp (-c5 * t) * PDE.l2NormSq φ ≤ max C5 0 * Real.exp (-c * t) * PDE.l2NormSq φ := by
          gcongr
          exact le_max_left _ _
      _ = _ := rfl
  have e1 : 4 * (K0 * (C3 * Real.exp (-c * t) * ((2 + 2 * Λβ) * PDE.l2NormSq φ))) =
      4 * K0 * C3 * (2 + 2 * Λβ) * Real.exp (-c * t) * PDE.l2NormSq φ := by ring
  have e2 : 4 * (Kb * (C1 * Real.exp (-c * t) * ((2 + 2 * Λβ) * PDE.l2NormSq φ))) =
      4 * Kb * C1 * (2 + 2 * Λβ) * Real.exp (-c * t) * PDE.l2NormSq φ := by ring
  nlinarith [hc0, hcb, hn, e1, e2]

end HRS.MC.L2C6c
