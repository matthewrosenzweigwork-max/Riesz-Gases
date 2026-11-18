import HRS.MS.ProClosureS111PhysicalWick
import HRS.MS.ProClosureS111PairedGaussianDecay

/-!
Actual physical covariance bounds for the two native Gaussian coordinate
sequences and their difference. The caller supplies only the exact shared
law. These are the quantitative hypotheses of accepted S111K4J; no new
finite Wick or L²-limit argument is used in the physical endpoint.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Chaos HRS.MS.S111X1

variable {d : ℕ}

/-- Both physical covariance operators are uniformly bounded, and their
common-law difference covariance decays at the sharp squared rate.
Constants precede the density, preparation, probability space, basis,
time, section dimension, and coefficient vector. -/
theorem physical_paired_coordinate_bounds (hd : 2 ≤ d)
    (s a beta lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hlam : 0 < lam) :
    ∃ A L : ℝ, 0 < A ∧ 0 < L ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho →
      IsR2Poincare (HRS.Whole.withDensityReal rho) lam →
      ∀ gamma : ℝ, 0 ≤ gamma →
      ∀ (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega)
        [IsProbabilityMeasure P] (H : ℝ)
        (Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d)),
      r26t6_SharedThermalLaw P s a beta gamma H rho Z →
      ∀ basis : ℕ → Euc d → ℝ,
      IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis →
      ∀ t ∈ Icc (0 : ℝ) H, ∀ n : ℕ, ∀ alpha : Fin n → ℝ,
        (∫ w, (∑ i, alpha i * OscDual.eval (Z 0 t w) (basis i)) ^ 2 ∂P) ≤
            L * ∑ i, alpha i ^ 2 ∧
        (∫ w, (∑ i, alpha i * OscDual.eval (Z 1 t w) (basis i)) ^ 2 ∂P) ≤
            L * ∑ i, alpha i ^ 2 ∧
        (∫ w, (∑ i, alpha i * (OscDual.eval (Z 0 t w) (basis i) -
          OscDual.eval (Z 1 t w) (basis i))) ^ 2 ∂P) ≤
            A * Real.exp (-2 * (lam / beta) * t) * ∑ i, alpha i ^ 2 := by
  obtain ⟨A, hA, hdec⟩ := physical_initial_difference_variance_decay
    hd s a beta lam hs0 hs ha hbeta hlam
  obtain ⟨L, hL, hseq⟩ := physical_gaussian_sequence_uniform hd s a beta hs0 hs ha hbeta
  refine ⟨A, L, hA, hL, fun rho hrho hP gamma hgamma Omega _ P _ H Z hZ basis hbasis t ht n alpha => ?_⟩
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  have hZ0 : IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
      (wholeSpaceIndex d) beta⁻¹ H (HRS.Whole.susceptibilityCov (rieszKernel d s) mu gamma) (Z 0) := by
    simpa only [r26t6_preparation, ite_true, mu] using hZ.evolution 0
  have hZ1 : IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
      (wholeSpaceIndex d) beta⁻¹ H (HRS.Whole.susceptibilityCov (rieszKernel d s) mu beta) (Z 1) := by
    simpa [r26t6_preparation, mu] using hZ.evolution 1
  have hX := hseq rho hrho gamma hgamma Omega P H (Z 0) hZ0 basis hbasis t ht
  have hY := hseq rho hrho beta hbeta.le Omega P H (Z 1) hZ1 basis hbasis t ht
  refine ⟨by simpa only [s94q, s94lin] using (hX n).2 alpha,
    by simpa only [s94q, s94lin] using (hY n).2 alpha, ?_⟩
  let test : Fin n → oscSub d (wholeSpaceIndex d) := fun i =>
    ⟨basis i, r2Test_isOscTest _ (hbasis.1 i)⟩
  let psi : oscSub d (wholeSpaceIndex d) := ∑ i, alpha i • test i
  have hpsi : (psi : Euc d → ℝ) = fun x => ∑ i : Fin n, alpha i * basis i x := by
    funext x
    simp [psi, test]
  have hV : (∫ x, HRS.Whole.projMean mu (psi : Euc d → ℝ) x ^ 2 ∂mu) = ∑ i, alpha i ^ 2 := by
    rw [hpsi]
    exact s94_projMean_sq_lincomb mu (fun i : Fin n => hbasis.1 i)
      (fun i j : Fin n => by simpa [Fin.ext_iff] using hbasis.2.1 i j) alpha
  have heval : ∀ (j : Fin 2) (w : Omega),
      (∑ i : Fin n, alpha i * OscDual.eval (Z j t w) (basis i)) =
        OscDual.eval (Z j t w) (psi : Euc d → ℝ) := by
    intro j w
    rw [← gaussianTestEvaluation_apply (Z j t w) psi]
    simp only [psi, map_sum, map_smul, gaussianTestEvaluation_apply, test, smul_eq_mul]
  have he : (fun w => ∑ i : Fin n, alpha i *
      (OscDual.eval (Z 0 t w) (basis i) - OscDual.eval (Z 1 t w) (basis i))) =
      fun w => OscDual.eval (Z 0 t w) (psi : Euc d → ℝ) -
        OscDual.eval (Z 1 t w) (psi : Euc d → ℝ) := by
    funext w
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, heval 0 w, heval 1 w]
  have he2 : (∫ w, (∑ i : Fin n, alpha i *
      (OscDual.eval (Z 0 t w) (basis i) - OscDual.eval (Z 1 t w) (basis i))) ^ 2 ∂P) =
      ∫ w, (OscDual.eval (Z 0 t w) (psi : Euc d → ℝ) -
        OscDual.eval (Z 1 t w) (psi : Euc d → ℝ)) ^ 2 ∂P := by
    apply integral_congr_ae
    exact ae_of_all _ fun w =>
      congrArg (fun x : ℝ => x ^ 2) (congrFun he w)
  have hsecond := (physical_shared_difference_moments hd hs0 hs ha hbeta hgamma
    hrho hZ ht psi.property).2.1
  rw [he2, hsecond]
  have h := hdec rho hrho hP gamma hgamma t ht.1 (psi : Euc d → ℝ) psi.property
  rw [hV] at h
  exact h

#print axioms physical_paired_coordinate_bounds

end HRS.MS.ProClosureS111
