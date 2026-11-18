import HRS.MS.ProClosureS111PairedSequences
import HRS.MS.ProClosureS111PairedGaussianFamilies
import HRS.MS.S111K4J

/-!
Actual physical paired Wick decay, using accepted k4_wick_difference_L2.
The new work supplies its exact mixed Gaussian law, uniform individual
covariance bounds, and sharp difference covariance from thermal data.
The accepted full-kernel finite-section and L²-limit proof is reused.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Chaos HRS.MS.S111T HRS.MS.S111X1

variable {d : ℕ}

/-- Every square-integrable pair of frozen Wick realizations on the exact
shared physical law satisfies exponential paired decay. The kernel need
only satisfy the accepted L² hypothesis: symmetry and pointwise
measurability are not extra hypotheses of this bound. -/
theorem physical_paired_wick_bound (hd : 2 ≤ d)
    (s a beta lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hlam : 0 < lam) :
    ∃ B : ℝ, 0 < B ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho →
      IsR2Poincare (HRS.Whole.withDensityReal rho) lam →
      ∀ gamma : ℝ, 0 ≤ gamma →
      ∀ (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega)
        [IsProbabilityMeasure P] (H : ℝ)
        (Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d)),
      r26t6_SharedThermalLaw P s a beta gamma H rho Z →
      ∀ basis : ℕ → Euc d → ℝ, IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis →
      ∀ t ∈ Icc (0 : ℝ) H, ∀ k : Euc d → Euc d → ℝ,
      MemLp (fun xy : Euc d × Euc d => k xy.1 xy.2) 2
        ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho)) →
      ∀ Q0 Q1 : Omega → ℝ,
      IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
        (fun i w => OscDual.eval (Z 0 t w) (basis i)) k Q0 →
      IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
        (fun i w => OscDual.eval (Z 1 t w) (basis i)) k Q1 →
      MemLp Q0 2 P → MemLp Q1 2 P →
        (∫ w, (Q0 w - Q1 w) ^ 2 ∂P) ≤ B * Real.exp (-2 * (lam / beta) * t) *
          ∫ xy, k xy.1 xy.2 ^ 2 ∂((HRS.Whole.withDensityReal rho).prod
            (HRS.Whole.withDensityReal rho)) := by
  obtain ⟨A, L, hA, hL, hcoord⟩ := physical_paired_coordinate_bounds
    hd s a beta lam hs0 hs ha hbeta hlam
  refine ⟨16 * L * A, by positivity,
    fun rho hrho hP gamma hgamma Omega _ P _ H Z hZ basis hbasis t ht k hk2 Q0 Q1 hQ0 hQ1 hQ02 hQ12 => ?_⟩
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  let z : ℕ → Omega → ℝ := fun i w => OscDual.eval (Z 0 t w) (basis i)
  let zb : ℕ → Omega → ℝ := fun i w => OscDual.eval (Z 1 t w) (basis i)
  let delta := Real.sqrt A * Real.exp (-(lam / beta) * t)
  have hdeltasq : delta ^ 2 = A * Real.exp (-2 * (lam / beta) * t) := by
    have hexp : Real.exp (-(lam / beta) * t) ^ 2 = Real.exp (-2 * (lam / beta) * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    dsimp [delta]
    rw [mul_pow, Real.sq_sqrt hA.le, hexp]
  have hzm : ∀ j : Fin 2, ∀ i : ℕ,
      AEMeasurable (fun w => OscDual.eval (Z j t w) (basis i)) P := by
    intro j i
    let phi : oscSub d (wholeSpaceIndex d) :=
      ⟨basis i, r2Test_isOscTest _ (hbasis.1 i)⟩
    have hm := (gaussianOscEval phi).continuous.measurable.comp ((hZ.evolution j).meas t)
    change Measurable (fun w => gaussianOscEval phi (Z j t w)) at hm
    simpa only [gaussianOscEval_apply] using hm.aemeasurable
  have hG : ∀ n : ℕ, HRS.IsCenteredGaussian
      (P.map fun w (i : Fin 2 × Fin n) => if i.1 = 0 then z i.2 w else zb i.2 w) := by
    intro n
    exact shared_paired_test_gaussian hZ ht
      (fun i : Fin n => ⟨basis i, r2Test_isOscTest _ (hbasis.1 i)⟩)
  have hvar : ∀ n : ℕ, ∀ c : Fin n → ℝ,
      (∫ w, (∑ i, c i * z i w) ^ 2 ∂P) ≤ Real.sqrt L ^ 2 * ∑ i, c i ^ 2 ∧
      (∫ w, (∑ i, c i * zb i w) ^ 2 ∂P) ≤ Real.sqrt L ^ 2 * ∑ i, c i ^ 2 ∧
      (∫ w, (∑ i, c i * (z i w - zb i w)) ^ 2 ∂P) ≤ delta ^ 2 * ∑ i, c i ^ 2 := by
    intro n c
    simpa only [Real.sq_sqrt hL.le, hdeltasq] using
      hcoord rho hrho hP gamma hgamma Omega P H Z hZ basis hbasis t ht n c
  have h := HRS.MS.S111K4.k4_wick_difference_L2 P mu basis hbasis z zb
    (hzm 0) (hzm 1) hG (Real.sqrt L) delta (Real.sqrt_nonneg _) (by dsimp [delta]; positivity)
    hvar k hk2 Q0 Q1 hQ0 hQ1 hQ02 hQ12
  rw [Real.sq_sqrt hL.le, hdeltasq] at h
  convert h using 1 <;> ring

/-- A genuine physical common-law producer with paired Wick realizations
and a uniform exponentially decaying L² difference for every native basis,
time, and symmetric L² kernel. The law and the Wick fields are constructed;
the finite-to-kernel difference estimate is the accepted S111K4J theorem. -/
theorem physical_shared_law_with_paired_wick (hd : 2 ≤ d)
    (s a beta lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hlam : 0 < lam) :
    ∃ B : ℝ, 0 < B ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho →
      IsR2Poincare (HRS.Whole.withDensityReal rho) lam →
      ∀ gamma : ℝ, 0 ≤ gamma → ∀ H : ℝ, ∀ hH : 0 < H,
      ∃ P : Measure (PathPair d (wholeSpaceIndex d) H), ∃ hprob : IsProbabilityMeasure P,
        r26t6_SharedThermalLaw P s a beta gamma H rho
          (pairedProcess d (wholeSpaceIndex d) H hH.le) ∧
        ∀ basis : ℕ → Euc d → ℝ, IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis →
        ∀ t ∈ Icc (0 : ℝ) H, ∀ k : Euc d → Euc d → ℝ,
        Measurable (fun xy : Euc d × Euc d => k xy.1 xy.2) →
        (∀ x y, k x y = k y x) →
        MemLp (fun xy : Euc d × Euc d => k xy.1 xy.2) 2
          ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho)) →
        ∃ Q0 Q1 : PathPair d (wholeSpaceIndex d) H → ℝ,
          MemLp Q0 2 P ∧ MemLp Q1 2 P ∧
          IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
            (fun i w => OscDual.eval (pairedProcess d (wholeSpaceIndex d) H hH.le 0 t w) (basis i)) k Q0 ∧
          IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
            (fun i w => OscDual.eval (pairedProcess d (wholeSpaceIndex d) H hH.le 1 t w) (basis i)) k Q1 ∧
          (∫ w, (Q0 w - Q1 w) ^ 2 ∂P) ≤ B * Real.exp (-2 * (lam / beta) * t) *
            ∫ xy, k xy.1 xy.2 ^ 2 ∂((HRS.Whole.withDensityReal rho).prod
              (HRS.Whole.withDensityReal rho)) := by
  obtain ⟨B, hB, hbound⟩ := physical_paired_wick_bound hd s a beta lam hs0 hs ha hbeta hlam
  obtain ⟨L, hL, hwick⟩ := physical_wick_exists_uniform hd s a beta hs0 hs ha hbeta
  refine ⟨B, hB, fun rho hrho hP gamma hgamma H hH => ?_⟩
  obtain ⟨P, hprob, hZ⟩ := physical_shared_thermal_law hd s a beta gamma H
    hs0 hs ha hbeta hgamma hH rho hrho
  letI : IsProbabilityMeasure P := hprob
  let Z := pairedProcess d (wholeSpaceIndex d) H hH.le
  refine ⟨P, hprob, hZ, fun basis hbasis t ht k hkm hks hk2 => ?_⟩
  have hZ0 : IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
      (wholeSpaceIndex d) beta⁻¹ H
      (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma) (Z 0) := by
    simpa only [r26t6_preparation, ite_true] using hZ.evolution 0
  have hZ1 : IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
      (wholeSpaceIndex d) beta⁻¹ H
      (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) beta) (Z 1) := by
    simpa [r26t6_preparation] using hZ.evolution 1
  obtain ⟨Q0, hQ0, hW0, -⟩ := hwick rho hrho gamma hgamma
    (PathPair d (wholeSpaceIndex d) H) P H (Z 0) hZ0 basis hbasis t ht k hkm hks hk2
  obtain ⟨Q1, hQ1, hW1, -⟩ := hwick rho hrho beta hbeta.le
    (PathPair d (wholeSpaceIndex d) H) P H (Z 1) hZ1 basis hbasis t ht k hkm hks hk2
  exact ⟨Q0, Q1, hQ0, hQ1, hW0, hW1,
    hbound rho hrho hP gamma hgamma (PathPair d (wholeSpaceIndex d) H) P H Z hZ
      basis hbasis t ht k hk2 Q0 Q1 hW0 hW1 hQ0 hQ1⟩

#print axioms physical_paired_wick_bound
#print axioms physical_shared_law_with_paired_wick

end HRS.MS.ProClosureS111
