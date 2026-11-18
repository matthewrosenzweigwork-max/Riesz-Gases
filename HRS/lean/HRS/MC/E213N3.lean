import HRS.MC.E213N2
import HRS.MC.E213A
import HRS.MC.E213L
import HRS.MC.S7FCW4D1
import HRS.Main.ThermLinFinal

/-!
# E213N3 (e5): the global Gaussian limit field `η*` of a regime

For `R : Regime d` and `r = 2d + 6` there are a probability space `Ω' = E_r × Ω_G` (product form) and
`η* : ℝ → Ω' → E_r` with `IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η*`.
The data `ν`, `Pg`, `Vev`, `ℱ`, `G`, `Zs` are exposed (named outputs): `Y₀ = pr₁` is independent of the noise
part `pr₂`, `η*(t) = Vev t 0 Y₀ + Zs t (pr₂)`, `G` is the half-line Gaussian martingale and `Zs t` its
stochastic convolution.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213N

open HRS HRS.Sec7 HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.ThermLin

variable {d : ℕ}

/-- `IsLinearFluctuationSolution` only sees `ρ` on `[0,∞)`. -/
theorem e213n_linSol_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (D : DynData d)
    {ρ ρ' : ℝ → Torus d → ℝ} (hρ : ∀ s : ℝ, 0 ≤ s → ρ s = ρ' s) {m q q' T : ℝ} (hq : q = q')
    {Y₀ : Ω → NegSobolev d m} {Y : ℝ → Ω → NegSobolev d m}
    (h : IsLinearFluctuationSolution P D ρ m q T Y₀ Y) :
    IsLinearFluctuationSolution P D ρ' m q' T Y₀ Y := by
  subst hq
  refine ⟨h.init, h.cont, h.meas, fun p ts φ hts hφ => ?_⟩
  obtain ⟨hind, hlaw⟩ := h.gaussian_part p ts φ hts hφ
  have hprop : ∀ r t φ', propagator D ρ r t φ' = propagator D ρ' r t φ' :=
    fun r t φ' => HRS.MC.Sec7.S7FCW4.S7FCW4_propagator_congr D ρ ρ' hρ r t φ'
  simp only [hprop] at hind hlaw
  dsimp only
  refine ⟨hind, ?_⟩
  rw [hlaw]
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  congr 1
  exact setIntegral_congr_fun measurableSet_Icc (fun r hr => by simp only [hρ r hr.1])

theorem e213n_global_gaussian_field (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∃ (Ωg : Type) (mΩ : MeasurableSpace Ωg) (Pg : Measure Ωg) (_ : IsProbabilityMeasure Pg)
      (ν : Measure (NegSobolev d r)) (_ : IsProbabilityMeasure ν) (Cr : ℝ)
      (Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r)
      (ℱ : Filtration ℝ mΩ) (G Zs : ℝ → Ωg → NegSobolev d r),
      IsCenteredGaussianWithCov r ν
        (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) ∧
      0 ≤ Cr ∧ IsDualEvolution R.D R.ρ r Vev ∧ (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr) ∧
      IsGlobalNoise r R.β⁻¹ R.ρ Vev Pg ℱ G Zs ∧
      IndepFun (fun p : NegSobolev d r × Ωg => p.1) (fun p => p.2) (ν.prod Pg) ∧
      (∀ T : ℝ, IsLinearFluctuationSolution (ν.prod Pg) R.D R.ρ r R.D.invβ T (fun p => p.1)
        (fun t p => Vev t 0 p.1 + Zs t p.2)) ∧
      IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r (ν.prod Pg)
        (fun t p => Vev t 0 p.1 + Zs t p.2) := by
  set S := HRS.MC.Sec7.FCPlan.s7fcPrep R with hS
  have htr : IsSmoothPositiveTrajectory d S.s S.β S.V S.ρ0 S.ρ :=
    HRS.MC.E213A.isSmoothPositiveTrajectory_of_prepared S
  have hdyn : htr.dyn = R.D := HRS.MC.Sec7.S7FCW4.S7FCW4_dyn R
  have hρS : ∀ s : ℝ, 0 ≤ s → S.ρ s = R.ρ s := fun s hs => HRS.MC.Sec7.S7FCW4.S7FCW4_rho_eq R hs
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm : (d : ℝ) / 2 + 2 < r := by rw [hr]; linarith
  have hβ₀ : 0 ≤ R.β₀ := by
    rcases R.hβ₀ with h | ⟨-, h⟩
    · exact h.le
    · exact h.ge
  -- initial law
  obtain ⟨ν, hνp, hνg⟩ := HRS.Main.preparedGaussian_exists_proof S R.β₀ hβ₀ r (by linarith)
  haveI := hνp
  have hνcov : IsCenteredGaussianWithCov r ν
      (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) := by
    refine ⟨hνg.1, fun φ ψ hφ hψ => ?_⟩
    rw [hνg.2 φ ψ hφ hψ]
    exact HRS.MC.E213L.e213l_preparedCov_eq_susceptibilityCov_density R.hρ₀ R.D.s R.β₀ hφ hψ
  -- noise
  obtain ⟨Cr, Vev, Ωg, mΩ, Pg, hPg, ℱ, G, Zs, hCr, hdual, hplain, hKb, hN⟩ :=
    e213n_exists_global_noise (m := r) R.hd htr hm
  haveI := hPg
  have hdens : noiseDens r S.β⁻¹ S.ρ = noiseDens r R.β⁻¹ R.ρ := by
    funext σ
    unfold noiseDens
    by_cases h : 0 ≤ σ
    · simp only [if_pos h, hρS σ h]; rfl
    · simp only [if_neg h]
  have hN' : IsGlobalNoise r R.β⁻¹ R.ρ Vev Pg ℱ G Zs :=
    ⟨hN.cont, hN.zero, fun S' hS' => by rw [← hdens]; exact hN.mart S' hS', hN.meas, hN.contOn,
      hN.conv, hN.zero_Zs⟩
  have hdual' : IsDualEvolution R.D R.ρ r Vev := by
    intro u t hu hut z φ hφ
    have := hdual u t hu hut z φ hφ
    rw [this, hdyn]
    congr 1
    exact HRS.MC.Sec7.S7FCW4.S7FCW4_propagator_congr R.D S.ρ R.ρ hρS u t φ
  have hlin : ∀ T : ℝ, IsLinearFluctuationSolution (ν.prod Pg) R.D R.ρ r R.D.invβ T
      (fun p => p.1) (fun t p => Vev t 0 p.1 + Zs t p.2) := by
    intro T
    have h := e213n_linearSolution R.hd htr hm hCr hdual hplain hKb hN ν T
    rw [hdyn] at h
    exact e213n_linSol_congr R.D hρS R.hDβ.symm h
  refine ⟨Ωg, mΩ, Pg, hPg, ν, hνp, Cr, Vev, ℱ, G, Zs, hνcov, hCr, hdual', hplain, hKb, hN',
    indepFun_prod (μ := ν) (ν := Pg) (X := (id : NegSobolev d r → NegSobolev d r))
      (Y := (id : Ωg → Ωg)) measurable_id measurable_id, hlin, ?_⟩
  refine ⟨fun p => p.1, ?_, hlin⟩
  have : (ν.prod Pg).map (fun p : NegSobolev d r × Ωg => p.1) = ν := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [this]
  exact hνcov

/-- GS-1: the global Gaussian limit field of a regime at level `r = 2d + 6`, on a probability space. -/
theorem e213n_exists_gaussianLimitField (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (η : ℝ → Ω' → NegSobolev d r),
      IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η := by
  obtain ⟨Ωg, mΩ, Pg, hPg, ν, hν, Cr, Vev, ℱ, G, Zs, -, -, -, -, -, -, -, -, hGL⟩ :=
    e213n_global_gaussian_field R r hr
  exact ⟨NegSobolev d r × Ωg, inferInstance, ν.prod Pg, inferInstance, _, hGL⟩

end HRS.MC.E213N

end
