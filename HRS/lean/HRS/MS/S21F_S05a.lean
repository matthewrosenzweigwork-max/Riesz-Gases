import HRS.MS.R2MtAux1
import HRS.MS.S21F_D00

/-!
# S21F, packet R26-T3.S05 (part a): `L^r(μ^{⊗N})` norm of the density of a Gibbs law

For `b = γ`, `rγ` with `GibbsWellDefined` and `|log K_b| ≤ A`:
`‖dQ_{N,γ}/dμ^{⊗N}‖_{L^r} ≤ (e^{(r+1)A})^{1/r}`, since `∫ ψ^r dμ^{⊗N} = K_γ^{-r} K_{rγ}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_ratio_le {K K2 A r : ℝ} (hK : 0 < K) (hK2 : 0 < K2) (h1 : |Real.log K| ≤ A)
    (h2 : |Real.log K2| ≤ A) (hr : 0 ≤ r) :
    (K⁻¹) ^ r * K2 ≤ Real.exp ((r + 1) * A) := by
  have hpos : 0 < (K⁻¹) ^ r * K2 := mul_pos (Real.rpow_pos_of_pos (inv_pos.2 hK) _) hK2
  have hl : Real.log ((K⁻¹) ^ r * K2) ≤ (r + 1) * A := by
    rw [Real.log_mul (Real.rpow_pos_of_pos (inv_pos.2 hK) _).ne' hK2.ne', Real.log_rpow (inv_pos.2 hK),
      Real.log_inv]
    have a1 := (abs_le.1 h1).1
    have a2 := (abs_le.1 h2).2
    nlinarith
  calc (K⁻¹) ^ r * K2 = Real.exp (Real.log ((K⁻¹) ^ r * K2)) := (Real.exp_log hpos).symm
    _ ≤ _ := Real.exp_le_exp.2 hl

theorem s21f_dens_Lr {d N : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}
    (hGm : Measurable (Function.uncurry G)) {γ r A : ℝ} (hr : 1 < r)
    (hW : GibbsWellDefined G N γ μ) (hW2 : GibbsWellDefined G N (r * γ) μ)
    (h1 : |Real.log (pairNormalizer G N γ μ)| ≤ A) (h2 : |Real.log (pairNormalizer G N (r * γ) μ)| ≤ A) :
    eLpNorm (fun X : EucConfig d N =>
        ((pairGibbs G N γ μ).rnDeriv (Measure.pi fun _ : Fin N => μ) X).toReal) (ENNReal.ofReal r)
      (Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal (Real.exp ((r + 1) * A) ^ (1 / r)) := by
  have hr0 : 0 < r := by linarith
  have hK := hW.normalizer_pos
  have hK2 := hW2.normalizer_pos
  set ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hν
  have hψm : Measurable (HRS.MS.R2Mt.s92_dens G N γ μ) := HRS.MS.R2Mt.s92_dens_meas hGm γ
  have hQ : pairGibbs G N γ μ = ν.withDensity (HRS.MS.R2Mt.s92_dens G N γ μ) := HRS.MS.R2Mt.s92_pairGibbs_eq hGm hW
  have hae : (pairGibbs G N γ μ).rnDeriv ν =ᵐ[ν] HRS.MS.R2Mt.s92_dens G N γ μ := by
    rw [hQ]; exact Measure.rnDeriv_withDensity ν hψm
  have hcongr : eLpNorm (fun X => ((pairGibbs G N γ μ).rnDeriv ν X).toReal) (ENNReal.ofReal r) ν =
      eLpNorm (fun X => (HRS.MS.R2Mt.s92_dens G N γ μ X).toReal) (ENNReal.ofReal r) ν :=
    eLpNorm_congr_ae (hae.mono fun X hX => by simp only [hX])
  rw [hcongr]
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hmeas : Measurable (fun X => (HRS.MS.R2Mt.s92_dens G N γ μ X).toReal) := hψm.ennreal_toReal
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hmeas.aestronglyMeasurable,
    ENNReal.toReal_ofReal hr0.le]
  have hpt : ∀ X : EucConfig d N, ‖(HRS.MS.R2Mt.s92_dens G N γ μ X).toReal‖ₑ ^ r =
      ENNReal.ofReal ((pairNormalizer G N γ μ)⁻¹ ^ r) *
        ENNReal.ofReal (Real.exp (-(r * γ) * N * pairEnergy G X μ)) := by
    intro X
    have h0 : 0 ≤ (pairNormalizer G N γ μ)⁻¹ * Real.exp (-γ * N * pairEnergy G X μ) :=
      mul_nonneg (inv_nonneg.2 hK.le) (Real.exp_pos _).le
    have e1 : (HRS.MS.R2Mt.s92_dens G N γ μ X).toReal = (pairNormalizer G N γ μ)⁻¹ * Real.exp (-γ * N * pairEnergy G X μ) := by
      unfold HRS.MS.R2Mt.s92_dens; rw [ENNReal.toReal_ofReal h0]
    rw [e1, ← ofReal_norm, Real.norm_of_nonneg h0, ENNReal.ofReal_rpow_of_nonneg h0 hr0.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.2 hK.le) _),
      Real.mul_rpow (inv_nonneg.2 hK.le) (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring_nf
  have hint : ∫⁻ X, ‖(HRS.MS.R2Mt.s92_dens G N γ μ X).toReal‖ₑ ^ r ∂ν =
      ENNReal.ofReal ((pairNormalizer G N γ μ)⁻¹ ^ r) * ENNReal.ofReal (pairNormalizer G N (r * γ) μ) := by
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hν, HRS.MS.Wr.wr9_partition hW2]
  rw [hint, ← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.2 hK.le) _)]
  have hle := s21f_ratio_le hK hK2 h1 h2 hr0.le
  calc (ENNReal.ofReal ((pairNormalizer G N γ μ)⁻¹ ^ r * pairNormalizer G N (r * γ) μ)) ^ (1 / r)
      ≤ (ENNReal.ofReal (Real.exp ((r + 1) * A))) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hle) (by positivity)
    _ = ENNReal.ofReal (Real.exp ((r + 1) * A) ^ (1 / r)) :=
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity)

end HRS.MS.R26T3
