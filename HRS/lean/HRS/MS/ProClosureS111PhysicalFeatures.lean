import HRS.MS.ProClosureS111InitialGaussianBounds
import HRS.MS.ProClosureS111NoiseBounds
import HRS.MS.ProClosureS111NoiseLinear
import HRS.MS.ProClosureS111CovarianceAllTime
import HRS.MS.R26T6CD03
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
The concrete paired physical feature map. There are three mutually
orthogonal components: preparation-gamma initial data, preparation-beta
initial data, and common noise. Thus the two initial fields are independent
and the noise is shared, exactly as in the frozen SharedThermalLaw.

All inputs of the later path constructor are proved here from the actual
thermal propagator and its response operator. In particular, the mixed
Gram identity holds on every original oscillator test.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.R26T6

variable {d : ℕ}

abbrev PhysicalFeatureSpace (mu : Measure (Euc d)) :=
  WithLp 2 (Lp ℝ 2 mu × WithLp 2 (Lp ℝ 2 mu × NoiseHilbert mu))

def physicalFeatureTriple {mu : Measure (Euc d)}
    (a b : Lp ℝ 2 mu) (n : NoiseHilbert mu) : PhysicalFeatureSpace mu :=
  WithLp.toLp 2 (a, WithLp.toLp 2 (b, n))

theorem physicalFeatureTriple_inner {mu : Measure (Euc d)}
    (a b a' b' : Lp ℝ 2 mu) (n n' : NoiseHilbert mu) :
    inner ℝ (physicalFeatureTriple a b n) (physicalFeatureTriple a' b' n') =
      inner ℝ a a' + (inner ℝ b b' + inner ℝ n n') := rfl

theorem physicalFeatureTriple_add {mu : Measure (Euc d)}
    (a b a' b' : Lp ℝ 2 mu) (n n' : NoiseHilbert mu) :
    physicalFeatureTriple a b n + physicalFeatureTriple a' b' n' =
      physicalFeatureTriple (a + a') (b + b') (n + n') := rfl

theorem physicalFeatureTriple_sub {mu : Measure (Euc d)}
    (a b a' b' : Lp ℝ 2 mu) (n n' : NoiseHilbert mu) :
    physicalFeatureTriple a b n - physicalFeatureTriple a' b' n' =
      physicalFeatureTriple (a - a') (b - b') (n - n') := rfl

theorem physicalFeatureTriple_smul {mu : Measure (Euc d)}
    (c : ℝ) (a b : Lp ℝ 2 mu) (n : NoiseHilbert mu) :
    c • physicalFeatureTriple a b n =
      physicalFeatureTriple (c • a) (c • b) (c • n) := rfl

theorem physicalFeatureTriple_norm_sq {mu : Measure (Euc d)}
    (a b : Lp ℝ 2 mu) (n : NoiseHilbert mu) :
    ‖physicalFeatureTriple a b n‖ ^ 2 = ‖a‖ ^ 2 + (‖b‖ ^ 2 + ‖n‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, physicalFeatureTriple_inner]
  simp only [real_inner_self_eq_norm_sq]

section Linear

variable {s a beta gamma : ℝ} {rho : Euc d → ℝ}
variable [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
variable {K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal rho)} {Mg : ℝ}
variable (hX : X1Input d s a beta 0 rho)
variable (hK : KRep (rieszKernel d s) (HRS.Whole.withDensityReal rho) K Mg)
variable (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)

def physicalLinearAt (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) :
    oscSub d (wholeSpaceIndex d) →ₗ[ℝ] PhysicalFeatureSpace (HRS.Whole.withDensityReal rho) where
  toFun phi := if i = 0 then
      physicalFeatureTriple (initialGaussianLinear hX hK hgamma ht phi) 0
        (noiseLinear hX beta⁻¹ ht phi)
    else physicalFeatureTriple 0 (initialGaussianLinear hX hK hbeta ht phi)
      (noiseLinear hX beta⁻¹ ht phi)
  map_add' phi psi := by
    by_cases hi : i = 0 <;> simp only [hi, if_true, if_false, map_add,
      physicalFeatureTriple_add, add_zero, zero_add]
  map_smul' c phi := by
    by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false, map_smul,
      physicalFeatureTriple_smul, smul_zero, RingHom.id_apply]

def physicalLinear (i : Fin 2) (t : ℝ) :
    oscSub d (wholeSpaceIndex d) →ₗ[ℝ] PhysicalFeatureSpace (HRS.Whole.withDensityReal rho) :=
  if ht : 0 ≤ t then physicalLinearAt hX hK hbeta hgamma i ht else 0

theorem physicalLinear_apply (i : Fin 2) {t : ℝ} (ht : 0 ≤ t)
    (phi : oscSub d (wholeSpaceIndex d)) :
    physicalLinear hX hK hbeta hgamma i t phi =
      if i = 0 then
        physicalFeatureTriple
          (initialGaussianFeature hK hgamma (x1C d s a beta rho) t (phi : Euc d → ℝ)) 0
          (scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) beta⁻¹ t
            (phi : Euc d → ℝ))
      else physicalFeatureTriple 0
        (initialGaussianFeature hK hbeta (x1C d s a beta rho) t (phi : Euc d → ℝ))
        (scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) beta⁻¹ t
          (phi : Euc d → ℝ)) := by
  simp only [physicalLinear, dif_pos ht, physicalLinearAt, LinearMap.coe_mk,
    AddHom.coe_mk, initialGaussianLinear_apply, noiseLinear_apply]

end Linear

section Physical

variable {s a beta gamma : ℝ} {rho : Euc d → ℝ}
variable [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
variable {K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal rho)} {Mg : ℝ}
variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
variable (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
variable (hrho : IsThermalEquilibrium d s a beta rho)
variable (hX : X1Input d s a beta 0 rho)
variable (hK : KRep (rieszKernel d s) (HRS.Whole.withDensityReal rho) K Mg)

include hd hs0 hs ha hbeta hgamma hrho hX hK in
theorem physicalLinear_gram (i j : Fin 2) {t v : ℝ} (ht : 0 ≤ t) (hv : 0 ≤ v)
    (phi psi : oscSub d (wholeSpaceIndex d)) :
    inner ℝ (physicalLinear hX hK hbeta.le hgamma i t phi)
      (physicalLinear hX hK hbeta.le hgamma j v psi) =
      (if i = j then HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho)
        (r26t6_preparation beta gamma i)
        (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 t (phi : Euc d → ℝ))
        (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 v (psi : Euc d → ℝ))
      else 0) + noiseCovW (r26t6_thermalCoeff d s a beta rho) beta⁻¹
        t v (phi : Euc d → ℝ) (psi : Euc d → ℝ) := by
  have hf := initialProp_memLp hX ht phi
  have hg := initialProp_memLp hX hv psi
  have hAg := initialGaussianFeature_inner hK hgamma
    (x1C d s a beta rho) t v (phi : Euc d → ℝ) (psi : Euc d → ℝ) hf hg
  have hAb := initialGaussianFeature_inner hK hbeta.le
    (x1C d s a beta rho) t v (phi : Euc d → ℝ) (psi : Euc d → ℝ) hf hg
  have hN := physical_noise_feature_inner hd hs0 hs ha hbeta hrho ht hv phi.property psi.property
  have hAg' := hAg
  simp only [x1C] at hAg'
  have hAb' := hAb
  simp only [x1C] at hAb'
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · have hij : i = j := hi.trans hj.symm
      simp only [physicalLinear_apply hX hK hbeta.le hgamma i ht,
        physicalLinear_apply hX hK hbeta.le hgamma j hv, if_pos hi, if_pos hj,
        if_pos hij, physicalFeatureTriple_inner, hAg', hN, r26t6_preparation,
        r26t6_thermalCoeff, x1C, inner_zero_left, inner_zero_right, add_zero, zero_add]
    · have hnij : i ≠ j := by
        intro hij
        exact hj (hij.symm.trans hi)
      simp only [physicalLinear_apply hX hK hbeta.le hgamma i ht,
        physicalLinear_apply hX hK hbeta.le hgamma j hv, if_pos hi, if_neg hj,
        if_neg hnij, physicalFeatureTriple_inner, hN, r26t6_preparation,
        r26t6_thermalCoeff, x1C, inner_zero_left, inner_zero_right, add_zero, zero_add]
  · by_cases hj : j = 0
    · have hnij : i ≠ j := by
        intro hij
        exact hi (hij.trans hj)
      simp only [physicalLinear_apply hX hK hbeta.le hgamma i ht,
        physicalLinear_apply hX hK hbeta.le hgamma j hv, if_neg hi, if_pos hj,
        if_neg hnij, physicalFeatureTriple_inner, hN, r26t6_preparation,
        r26t6_thermalCoeff, x1C, inner_zero_left, inner_zero_right, add_zero, zero_add]
    · have hij : i = j := by
        fin_cases i <;> fin_cases j <;> simp_all
      simp only [physicalLinear_apply hX hK hbeta.le hgamma i ht,
        physicalLinear_apply hX hK hbeta.le hgamma j hv, if_neg hi, if_neg hj,
        if_pos hij, physicalFeatureTriple_inner, hAb', hN, r26t6_preparation,
        r26t6_thermalCoeff, x1C, inner_zero_left, inner_zero_right, add_zero, zero_add]

include hd hs0 hs ha hbeta hgamma hrho hX hK in
/-- The feature map is continuous in the original oscillator norm on all
tests. The physical all-time covariance estimate supplies the bound. -/
theorem physicalLinear_osc_bound (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ phi : oscSub d (wholeSpaceIndex d),
      ‖physicalLinear hX hK hbeta.le hgamma i t phi‖ ≤
        B * oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ) := by
  obtain ⟨L, hL, hcov⟩ := physical_covariance_all_time hd s a beta hs0 hs ha hbeta
  obtain ⟨M, hM⟩ := hX.bdd
  have hM0 : 0 ≤ M := (hX.nonneg 0).trans (hM 0)
  have htheta : 0 ≤ r26t6_preparation beta gamma i := by
    unfold r26t6_preparation
    split_ifs
    · exact hgamma
    · exact hbeta.le
  refine ⟨Real.sqrt (L * M), Real.sqrt_nonneg _, fun phi => ?_⟩
  have hsame : ‖physicalLinear hX hK hbeta.le hgamma i t phi‖ ^ 2 =
      linearGaussianCov (r26t6_thermalCoeff d s a beta rho) beta⁻¹
        (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho)
          (r26t6_preparation beta gamma i)) t t (phi : Euc d → ℝ) (phi : Euc d → ℝ) := by
    rw [← real_inner_self_eq_norm_sq,
      physicalLinear_gram hd hs0 hs ha hbeta hgamma hrho hX hK i i ht ht]
    simp only [ite_true, linearGaussianCov]
  have hphiLp := x1_osc_memLp hX.meas hX.nonneg hM phi.property
  have hproj := projMean_sq_le hX.meas hX.nonneg hrho.1.1.integral_one hX.int hphiLp
  have hinput := initialTest_sq_bound hX.meas hX.nonneg hM0 hM
    (Nat.cast_nonneg (wholeSpaceIndex d)) phi
  have hsq : ‖physicalLinear hX hK hbeta.le hgamma i t phi‖ ^ 2 ≤
      (L * M) * oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ) ^ 2 := by
    calc
      _ = _ := hsame
      _ ≤ L * ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal rho) (phi : Euc d → ℝ) x ^ 2
          ∂HRS.Whole.withDensityReal rho := (hcov rho hrho _ htheta t ht phi phi.property).2
      _ ≤ L * ∫ x, (phi : Euc d → ℝ) x ^ 2 ∂HRS.Whole.withDensityReal rho :=
        mul_le_mul_of_nonneg_left hproj hL.le
      _ ≤ L * (M * oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hinput hL.le
      _ = _ := by ring
  have hnorm : 0 ≤ oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ) :=
    Real.sqrt_nonneg _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hnorm)).1
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hL.le hM0)]
  exact hsq

end Physical

#print axioms physicalLinear_gram
#print axioms physicalLinear_osc_bound

end HRS.MS.ProClosureS111
