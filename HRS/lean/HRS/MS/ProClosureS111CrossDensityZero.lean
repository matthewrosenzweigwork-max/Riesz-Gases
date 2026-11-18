import HRS.MS.ProClosureS111CovarianceAllTime
import HRS.MS.ProClosureS111ZeroMassBase
import HRS.MS.S111X2Aux41
import HRS.MS.S111X1G2
import HRS.MS.R2ChaosAux39

/-!
Every frozen physical cross-density has zero mass and is uniquely determined
as an L²(mu) class.  The proof first obtains centered covariance control from
the accepted physical two-by-two positivity theorem and the all-time bound.
Smooth compact cutoffs then detect the constant mode.  No extra centering or
joint-measurability assumption is added to IsR2CrossDensities.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Matrix

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.R26T6

variable {d : ℕ}

/-- The centered covariance bound holds between any two nonnegative times,
with one constant fixed before the density, preparation and tests. -/
theorem physical_cross_covariance_centered (hd : 2 ≤ d)
    (s a beta : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ L : ℝ, 0 < L ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho → ∀ gamma : ℝ, 0 ≤ gamma →
      ∀ r t : ℝ, 0 ≤ r → 0 ≤ t → ∀ phi psi : Euc d → ℝ,
      IsOscTest (wholeSpaceIndex d : ℝ) phi →
      IsOscTest (wholeSpaceIndex d : ℝ) psi →
      |linearGaussianCov (r26t6_thermalCoeff d s a beta rho) beta⁻¹
        (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma)
        r t phi psi| ≤ L *
          Real.sqrt (∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal rho) phi x ^ 2 ∂HRS.Whole.withDensityReal rho) *
          Real.sqrt (∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal rho) psi x ^ 2 ∂HRS.Whole.withDensityReal rho) := by
  obtain ⟨L, hL, hdiag⟩ := physical_covariance_all_time hd s a beta hs0 hs ha hbeta
  refine ⟨L, hL, fun rho hrho gamma hgamma r t hr ht phi psi hphi hpsi => ?_⟩
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  let C := r26t6_thermalCoeff d s a beta rho
  let ts : Fin 2 → ℝ := ![r, t]
  let tests : Fin 2 → Euc d → ℝ := ![phi, psi]
  have hts : ∀ i, 0 ≤ ts i := by intro i; fin_cases i <;> assumption
  have htests : ∀ i, IsOscTest (wholeSpaceIndex d : ℝ) (tests i) := by
    intro i; fin_cases i <;> assumption
  let f : Fin 2 → ℝ → Euc d → ℝ := fun i v => propagatorW C v (ts i) (tests i)
  have hf : ∀ i, IsClassicalAdjointW C (ts i) (tests i) (f i) := fun i =>
    x1_prop_classical (exist_of_thermal hd hs0 hs ha hbeta hrho (ts i) (hts i)
      (tests i) (htests i))
  have hmem : ∀ i, MemLp (propagatorW C 0 (ts i) (tests i)) 2 mu :=
    fun i => x1_classical_memLp (hf i) ⟨le_rfl, hts i⟩ mu
  let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    linearGaussianCov C beta⁻¹ (HRS.Whole.susceptibilityCov (rieszKernel d s) mu gamma)
      (ts i) (ts j) (tests i) (tests j)
  have hS : S.PosSemidef :=
    s111x2_cov_psd2 hd hs0 hs ha hbeta hrho hgamma ts hts tests f hf hmem
  have hsym : S 1 0 = S 0 1 := by
    have hh := hS.1
    change S.conjTranspose = S at hh
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hh
    simpa only [Matrix.conjTranspose_apply, star_trivial] using he
  have hdet : 0 ≤ S 0 0 * S 1 1 - S 0 1 * S 1 0 := by
    simpa only [Matrix.det_fin_two] using hS.det_nonneg
  rw [hsym] at hdet
  have hsq : (S 0 1) ^ 2 ≤ S 0 0 * S 1 1 := by nlinarith
  let Vphi : ℝ := ∫ x, HRS.Whole.projMean mu phi x ^ 2 ∂mu
  let Vpsi : ℝ := ∫ x, HRS.Whole.projMean mu psi x ^ 2 ∂mu
  have hVphi : 0 ≤ Vphi := integral_nonneg fun x => sq_nonneg _
  have hVpsi : 0 ≤ Vpsi := integral_nonneg fun x => sq_nonneg _
  have h00 : 0 ≤ S 0 0 ∧ S 0 0 ≤ L * Vphi :=
    hdiag rho hrho gamma hgamma r hr phi hphi
  have h11 : 0 ≤ S 1 1 ∧ S 1 1 ≤ L * Vpsi :=
    hdiag rho hrho gamma hgamma t ht psi hpsi
  have hprod : S 0 0 * S 1 1 ≤ (L * Vphi) * (L * Vpsi) :=
    mul_le_mul h00.2 h11.2 h11.1 (mul_nonneg hL.le hVphi)
  have hroot : 0 ≤ L * Real.sqrt Vphi * Real.sqrt Vpsi := by positivity
  have hroot2 : (L * Real.sqrt Vphi * Real.sqrt Vpsi) ^ 2 =
      (L * Vphi) * (L * Vpsi) := by
    simp only [mul_pow, Real.sq_sqrt hVphi, Real.sq_sqrt hVpsi]
    ring
  change |S 0 1| ≤ L * Real.sqrt Vphi * Real.sqrt Vpsi
  nlinarith [sq_abs (S 0 1)]

theorem cross_density_pair_relative (rho chi b : Euc d → ℝ)
    (hrho : HRS.Whole.IsProbDensity rho) (hpos : ∀ x, 0 < rho x) :
    (∫ x, (chi x / rho x) * b x ∂HRS.Whole.withDensityReal rho) = ∫ x, b x * chi x := by
  rw [HRS.MS.Gap.gap1_integral_wdr hrho.measurable hrho.nonneg]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hx : rho x ≠ 0 := ne_of_gt (hpos x)
  field_simp

/-- Zero mass follows for EVERY cross-density satisfying the frozen interface,
not merely for a specially selected Riesz representative. -/
theorem physical_cross_density_zero_mass (hd : 2 ≤ d)
    {s a beta gamma T u : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma) (hu : 0 ≤ u)
    {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d s a beta rho)
    (tau : Fin 3 → Icc (0 : ℝ) T) (phi : Fin 3 → Euc d → ℝ)
    (hphi : ∀ i, IsOscTest (wholeSpaceIndex d : ℝ) (phi i))
    (chi : Fin 3 → ℝ → Euc d → ℝ)
    (hchi : IsR2CrossDensities d s a beta gamma rho T u tau phi chi) :
    ∀ i, ∀ r ∈ Icc (0 : ℝ) (u + T),
      MemL2Zero (HRS.Whole.withDensityReal rho) (fun x => chi i r x / rho x) := by
  obtain ⟨L, hL, hcov⟩ := physical_cross_covariance_centered hd s a beta hs0 hs ha hbeta
  have hX : X1Input d s a beta 0 rho :=
    x1Input_of_exist hd hs0 hs ha hbeta 0 hrho
      (exist_of_thermal hd hs0 hs ha hbeta hrho)
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  intro i r hr
  refine ⟨(hchi i r hr).1, ?_⟩
  apply integral_zero_of_centered_test_bound mu (fun x => chi i r x / rho x)
    ((hchi i r hr).1.integrable one_le_two)
    (L * Real.sqrt (∫ x, HRS.Whole.projMean mu (phi i) x ^ 2 ∂mu))
  intro b hbs hbc
  have hbo : IsOscTest (wholeSpaceIndex d : ℝ) b :=
    ⟨hbs, memOsc_schwartz _ (hbc.toSchwartzMap hbs)⟩
  rw [cross_density_pair_relative rho (chi i r) b hrho.1.1 hX.pos,
    ((hchi i r hr).2 b hbo).2]
  have hb := hcov rho hrho gamma hgamma r (u + tau i) hr.1
    (add_nonneg hu (tau i).property.1) b (phi i) hbo (hphi i)
  simpa only [HRS.MS.R26T6.r26t6_thermalCoeff, HRS.Whole.projMean,
    HRS.Whole.pair, mul_assoc, mul_left_comm, mul_comm] using hb

/-- Frozen cross-densities have a unique relative L² class at every time.
There is no assertion of a simultaneous spatial exceptional set over times. -/
theorem physical_cross_density_unique (hd : 2 ≤ d)
    {s a beta gamma T u : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta)
    {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d s a beta rho)
    (tau : Fin 3 → Icc (0 : ℝ) T) (phi : Fin 3 → Euc d → ℝ)
    (chi eta : Fin 3 → ℝ → Euc d → ℝ)
    (hchi : IsR2CrossDensities d s a beta gamma rho T u tau phi chi)
    (heta : IsR2CrossDensities d s a beta gamma rho T u tau phi eta) :
    ∀ i, ∀ r ∈ Icc (0 : ℝ) (u + T),
      (fun x => chi i r x / rho x) =ᵐ[HRS.Whole.withDensityReal rho]
        (fun x => eta i r x / rho x) := by
  have hX : X1Input d s a beta 0 rho :=
    x1Input_of_exist hd hs0 hs ha hbeta 0 hrho
      (exist_of_thermal hd hs0 hs ha hbeta hrho)
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  intro i r hr
  let f : Euc d → ℝ := fun x => chi i r x / rho x
  let g : Euc d → ℝ := fun x => eta i r x / rho x
  have hf : MemLp f 2 mu := (hchi i r hr).1
  have hg : MemLp g 2 mu := (heta i r hr).1
  have hz : (f - g) =ᵐ[mu] 0 := HRS.MS.R2Chaos.s94_test_separates hrho.1.1
    (hf.sub hg) (fun b hb => by
      have hbo : IsOscTest (wholeSpaceIndex d : ℝ) b :=
        ⟨hb.1, memOsc_schwartz _ (hb.2.toSchwartzMap hb.1)⟩
      have hb2 : MemLp b 2 mu :=
        MemLp.of_bound hb.1.continuous.aestronglyMeasurable
          (HRS.MS.R2Chaos.s94_test_bounded hb).choose
          (ae_of_all mu fun x => by simpa only [Real.norm_eq_abs] using
            (HRS.MS.R2Chaos.s94_test_bounded hb).choose_spec x)
      simp only [Pi.sub_apply, sub_mul]
      have hsplit : (∫ x, f x * b x - g x * b x ∂mu) =
          (∫ x, f x * b x ∂mu) - ∫ x, g x * b x ∂mu := by
        simpa only [Pi.mul_apply, Pi.sub_apply] using
          (integral_sub (hf.integrable_mul hb2) (hg.integrable_mul hb2))
      rw [hsplit]
      rw [cross_density_pair_relative rho (chi i r) b hrho.1.1 hX.pos,
        cross_density_pair_relative rho (eta i r) b hrho.1.1 hX.pos,
        ((hchi i r hr).2 b hbo).2, ((heta i r hr).2 b hbo).2]
      exact sub_self _)
  filter_upwards [hz] with x hx
  exact sub_eq_zero.1 hx

#print axioms physical_cross_covariance_centered
#print axioms physical_cross_density_zero_mass
#print axioms physical_cross_density_unique

end HRS.MS.ProClosureS111
