import HRS.MS.Fp81S21Uniform3
import HRS.MS.Fp81S21MovingNoise
import HRS.MS.S21H2_S14aD5
import HRS.MS.ProClosureS111PhysicalWick

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/--
The supplied Gaussian realization does contain the fixed-time information used
below.  Its `evolution.gaussian` field states that every finite vector of
oscillator observations has a centered multivariate Gaussian law whose matrix
is the transported susceptibility covariance plus `noiseCovW`.  In
particular, at a time `u` in a horizon `H`, `gaussian_observation_law_and_second`
turns this field into the second-moment identity for each oscillator test.
-/
theorem fp81s21_gaussLin_cov_nonneg
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) {u : ℝ} (hu : 0 ≤ u)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    0 ≤ HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u u φ φ := by
  let μ₀ : Measure (Euc p.d) := r26t3_mu R 0
  have hμ₀ : IsProbabilityMeasure μ₀ := by
    change IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0))
    exact HRS.Whole.Q34.isProbabilityMeasure_nu
      (R.resulting.global 0 |>.density 0 ⟨le_rfl, le_rfl⟩)
  letI : IsProbabilityMeasure μ₀ := hμ₀
  obtain ⟨Mg, K, hK⟩ := HRS.MS.R26T3.s21h2_krep_init hδ hδhalf R
  have hform := HRS.MS.S111X2.s111x2_responseForm
    (g := rieszKernel p.d p.s) hK p.hγ le_rfl
  obtain ⟨f, hf⟩ := HRS.Fp81.S21.fp81s21_adjoint_of_osc_test p R hφ hu
  have hfprop : r26t3_U R 0 u φ = f 0 := by
    have hsd : p.s < (p.d : ℝ) := by
      have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
      linarith [p.hs]
    have huF := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
      δ p.c₁ p.C₁ R.thermal R.admissible R.resulting u hu ⟨hu, le_rfl⟩ hf
    simpa [r26t3_U, r26t3_coeff] using huF 0 ⟨le_rfl, hu⟩
  have hfmem : MemLp (f 0) 2 μ₀ :=
    HRS.MS.S111X1.x1_classical_memLp hf ⟨le_rfl, hu⟩ μ₀
  have hUmem : MemLp (r26t3_U R 0 u φ) 2 μ₀ := by
    rw [hfprop]
    exact hfmem
  have hMg : 0 ≤ Mg := hK.nonneg
  have hden : 0 < 1 + p.γ * Mg := by
    have hp : 0 ≤ p.γ * Mg := mul_nonneg p.hγ hMg
    linarith
  have hcoef : 0 ≤ (1 + p.γ * Mg)⁻¹ := inv_nonneg.mpr hden.le
  have hvar : 0 ≤ HRS.MS.S111X2.s111x2_centeredSquare μ₀ (r26t3_U R 0 u φ) := by
    unfold HRS.MS.S111X2.s111x2_centeredSquare
    exact integral_nonneg fun x => sq_nonneg _
  have hsusc : 0 ≤ HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
      μ₀ p.γ (r26t3_U R 0 u φ) (r26t3_U R 0 u φ) :=
    (mul_nonneg hcoef hvar).trans (hform.coercive (r26t3_U R 0 u φ) hUmem).1
  let H : ℝ := u + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have huH : u ∈ Icc (0 : ℝ) H := by
    constructor
    · exact hu
    · dsimp [H]
      linarith
  have hnoise := (HRS.Fp81.S21.movingNoiseFeature_spec p R hδ hδhalf hH).2
    0 ⟨le_rfl, hH.le⟩ u huH u huH φ φ hφ hφ
  have hnoise' :
      HRS.Whole.noiseCovW (r26t3_coeff R) p.β⁻¹ u u φ φ =
        inner ℝ (HRS.Fp81.S21.movingNoiseFeature R 0 u φ)
          (HRS.Fp81.S21.movingNoiseFeature R 0 u φ) := by
    have hρcoeff : (r26t3_coeff R).ρ = R.ρ := rfl
    rw [HRS.Whole.noiseCovW, min_self, hρcoeff]
    simpa [r26t3_U] using hnoise.symm
  have hnoise_nonneg : 0 ≤ HRS.Whole.noiseCovW (r26t3_coeff R) p.β⁻¹ u u φ φ := by
    rw [hnoise']
    exact real_inner_self_nonneg
  have hdecomp :
      HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u u φ φ =
        HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ₀ p.γ
          (r26t3_U R 0 u φ) (r26t3_U R 0 u φ) +
        HRS.Whole.noiseCovW (r26t3_coeff R) p.β⁻¹ u u φ φ := by
    rfl
  rw [hdecomp]
  exact add_nonneg hsusc hnoise_nonneg

private theorem fp81s21_gaussLin_withDensity_le
    {d : ℕ} {ρ σ : Euc d → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hσ : Measurable σ) (hρσ : ∀ x, ρ x ≤ K * σ x) :
    HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal K • HRS.Whole.withDensityReal σ := by
  refine Measure.le_iff'.2 fun A => ?_
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply']
  rw [Measure.smul_apply, smul_eq_mul]
  rw [withDensity_apply']
  calc
    ∫⁻ x in A, ENNReal.ofReal (ρ x) ≤
        ∫⁻ x in A, ENNReal.ofReal K * ENNReal.ofReal (σ x) := by
      apply lintegral_mono
      intro x
      calc
        ENNReal.ofReal (ρ x) ≤ ENNReal.ofReal (K * σ x) :=
          ENNReal.ofReal_le_ofReal (hρσ x)
        _ = ENNReal.ofReal K * ENNReal.ofReal (σ x) := ENNReal.ofReal_mul hK
    _ = ENNReal.ofReal K * ∫⁻ x in A, ENNReal.ofReal (σ x) := by
      rw [lintegral_const_mul]
      exact ENNReal.measurable_ofReal.comp hσ

private theorem fp81s21_gaussLin_thermal_measurable
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) : Measurable R.ρβ := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
    p.hd p.hs0 hsd p.ha p.hβ
  rw [hρeq, ← hψ']
  exact ψ'.continuous.measurable

/--
Uniform second-moment identity and bound on the oscillator-test domain.
`Kstar` is selected after `R` and before the realization and time.  The
comparison is with `μstar = withDensityReal R.ρβ`; no thermal Gaussian law is
substituted for the supplied `G.P`.
-/
theorem fp81s21_gaussLin_test_second_moment_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ Kstar : ℝ, 0 ≤ Kstar ∧
          ∀ G : GaussianRealization R, ∀ u : ℝ, 0 ≤ u →
            ∀ φ : Euc p.d → ℝ,
              IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
              MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ) →
              MemLp (fun ω => OscDual.eval (G.Z u ω) φ) 2 G.P ∧
              (∫ ω, OscDual.eval (G.Z u ω) φ ^ 2 ∂G.P =
                HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u u φ φ) ∧
              (∫ ω, OscDual.eval (G.Z u ω) φ ^ 2 ∂G.P ≤
                Kstar ^ 2 * ∫ x, φ x ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ)) := by
  obtain ⟨δcov, hδcov, hδcovHalf, hCov⟩ :=
    HRS.Fp81.S21.fp81s21_uniform_covariance_domination p
  refine ⟨δcov, hδcov, hδcovHalf, ?_⟩
  intro δ hδ hδδ0 R
  obtain ⟨Kcov, hKcov, hCovR⟩ := hCov δ hδ hδδ0 R
  have hδhalf : δ ≤ 1 / 2 := hδδ0.trans hδcovHalf
  obtain ⟨-, hC1, -, -⟩ := HRS.MS.R26T3.r26t3_reference_data p δ hδ hδhalf R
  let Kstar : ℝ := Real.sqrt (Kcov * p.C₁)
  have hKstar : 0 ≤ Kstar := Real.sqrt_nonneg _
  refine ⟨Kstar, hKstar, ?_⟩
  intro G u hu φ hφ hφstar
  let μu : Measure (Euc p.d) := r26t3_mu R u
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμdom : μu ≤ ENNReal.ofReal p.C₁ • μstar := by
    have hρβm : Measurable R.ρβ := fp81s21_gaussLin_thermal_measurable p R
    have hpoint : ∀ x, R.ρ u x ≤ p.C₁ * R.ρβ x :=
      fun x => (R.resulting.ratio u hu x).2
    simpa [μu, μstar, r26t3_mu] using
      fp81s21_gaussLin_withDensity_le hC1.le hρβm hpoint
  have hscaled : Integrable (fun x => φ x ^ 2) (ENNReal.ofReal p.C₁ • μstar) :=
    (hφstar.integrable_sq).smul_measure ENNReal.ofReal_ne_top
  have hIcompare :
      ∫ x, φ x ^ 2 ∂μu ≤ p.C₁ * ∫ x, φ x ^ 2 ∂μstar := by
    have hmono := integral_mono_measure hμdom
      (Filter.Eventually.of_forall fun x => sq_nonneg (φ x)) hscaled
    rw [integral_smul_measure, ENNReal.toReal_ofReal hC1.le, smul_eq_mul] at hmono
    exact hmono
  have hcovNonneg := fp81s21_gaussLin_cov_nonneg p hδ hδhalf R hu hφ
  have hcovBound :
      |HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u u φ φ| ≤
        Kcov * Real.sqrt (∫ x, φ x ^ 2 ∂μu) *
          Real.sqrt (∫ x, φ x ^ 2 ∂μu) := by
    simpa [μu, r26t3_mu] using hCovR u u hu hu φ φ hφ hφ
  have hIu : 0 ≤ ∫ x, φ x ^ 2 ∂μu := integral_nonneg fun x => sq_nonneg _
  have hroot :
      Real.sqrt (∫ x, φ x ^ 2 ∂μu) * Real.sqrt (∫ x, φ x ^ 2 ∂μu) =
        ∫ x, φ x ^ 2 ∂μu := by
    calc
      _ = (Real.sqrt (∫ x, φ x ^ 2 ∂μu)) ^ 2 := by ring
      _ = _ := Real.sq_sqrt hIu
  have hcovUpper :
      HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u u φ φ ≤
        Kcov * ∫ x, φ x ^ 2 ∂μu := by
    calc
      _ ≤ |HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u u φ φ| := le_abs_self _
      _ ≤ Kcov * Real.sqrt (∫ x, φ x ^ 2 ∂μu) *
          Real.sqrt (∫ x, φ x ^ 2 ∂μu) := by simpa using hcovBound
      _ = Kcov * ∫ x, φ x ^ 2 ∂μu := by calc
        _ = Kcov * (Real.sqrt (∫ x, φ x ^ 2 ∂μu) *
            Real.sqrt (∫ x, φ x ^ 2 ∂μu)) := by ring
        _ = _ := by rw [hroot]
  have hsecond := HRS.MS.ProClosureS111.gaussian_observation_law_and_second
    (G.evolution (u + 1)) ⟨hu, by linarith⟩ ⟨φ, hφ⟩ (by
      simpa [HRS.MS.S21E.s21eCov, r26t3_coeff, r26t3_mu,
        HRS.Whole.linearGaussianCov] using hcovNonneg)
  have hevalMeas : Measurable (fun ω => OscDual.eval (G.Z u ω) φ) := by
    have heq : (fun ω => OscDual.eval (G.Z u ω) φ) =
        fun ω => HRS.MS.ProClosureS111.gaussianOscEval ⟨φ, hφ⟩ (G.Z u ω) := by
      funext ω
      exact (HRS.MS.ProClosureS111.gaussianOscEval_apply ⟨φ, hφ⟩ _).symm
    rw [heq]
    exact (HRS.MS.ProClosureS111.gaussianOscEval ⟨φ, hφ⟩).continuous.measurable.comp
      ((G.evolution (u + 1)).meas u)
  obtain ⟨v, hLaw⟩ := hsecond.1
  have hevalMem : MemLp (fun ω => OscDual.eval (G.Z u ω) φ) 2 G.P := by
    have hid : MemLp (id : ℝ → ℝ) 2
        (G.P.map (fun ω => OscDual.eval (G.Z u ω) φ)) := by
      rw [hLaw]
      exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id hevalMeas.aemeasurable).1 hid
  have hfinal :
      ∫ x, OscDual.eval (G.Z u x) φ ^ 2 ∂G.P ≤
        Kstar ^ 2 * ∫ x, φ x ^ 2 ∂μstar := by
    have hk : Kstar ^ 2 = Kcov * p.C₁ := by
      dsimp [Kstar]
      rw [Real.sq_sqrt (mul_nonneg hKcov hC1.le)]
    calc
      _ = HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u u φ φ := hsecond.2
      _ ≤ Kcov * ∫ x, φ x ^ 2 ∂μu := hcovUpper
      _ ≤ Kcov * (p.C₁ * ∫ x, φ x ^ 2 ∂μstar) :=
        mul_le_mul_of_nonneg_left hIcompare hKcov
      _ = Kstar ^ 2 * ∫ x, φ x ^ 2 ∂μstar := by rw [hk]; ring
  exact ⟨hevalMem, hsecond.2, hfinal⟩

/--
Every oscillator observation of the supplied realization has the prescribed
centered scalar Gaussian law.  The time is unrestricted because the evolution
record provides a field for each horizon, and `u` lies in `[0,u+1]`.
-/
theorem fp81s21_gaussLin_test_gaussian_law (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ G : GaussianRealization R, ∀ u : ℝ, 0 ≤ u →
          ∀ φ : Euc p.d → ℝ,
            IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
            ∃ v : ℝ≥0,
              G.P.map (fun ω => OscDual.eval (G.Z u ω) φ) = gaussianReal 0 v := by
  obtain ⟨δ0, hδ0, hδ0half, hbound⟩ := fp81s21_gaussLin_test_second_moment_bound p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδδ0 R G u hu φ hφ
  have hδhalf : δ ≤ 1 / 2 := hδδ0.trans hδ0half
  obtain ⟨_, _, _⟩ := hbound δ hδ hδδ0 R
  have hcovNonneg := fp81s21_gaussLin_cov_nonneg p hδ hδhalf R hu hφ
  have hobs := HRS.MS.ProClosureS111.gaussian_observation_law_and_second
    (G.evolution (u + 1)) ⟨hu, by linarith⟩ ⟨φ, hφ⟩ (by
      simpa [HRS.MS.S21E.s21eCov, r26t3_coeff, r26t3_mu,
        HRS.Whole.linearGaussianCov] using hcovNonneg)
  exact hobs.1

#print axioms fp81s21_gaussLin_cov_nonneg
#print axioms fp81s21_gaussLin_test_second_moment_bound
#print axioms fp81s21_gaussLin_test_gaussian_law

end HRS.Fp81.S21

end
