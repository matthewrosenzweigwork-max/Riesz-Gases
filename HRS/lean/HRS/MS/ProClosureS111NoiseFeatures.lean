import HRS.MS.ProClosureS111PhysicalJets
import HRS.MS.S111X1G2
import HRS.MS.S111X2Aux41
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Prod

/-!
The actual common-noise feature of the thermal Gaussian evolution.
Its ambient Hilbert space is fixed: L²(dt ⊗ rho dx; R^d). Each feature is
the gradient of the physical adjoint, cut off to [0,t], with the exact
sqrt(2/beta) normalization. Classical adjoint bounds prove membership;
Fubini identifies its Gram form with the frozen `noiseCovW`, for every
original oscillator test, including time zero.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111X2

variable {d : ℕ}

abbrev NoiseHilbert (mu : Measure (Euc d)) :=
  Lp (Euc d) 2 ((volume : Measure ℝ).prod mu)

def noiseVector (C : WholeCoeff d) (t : ℝ) (phi : Euc d → ℝ)
    (p : ℝ × Euc d) : Euc d :=
  if p.1 ∈ Icc (0 : ℝ) t then gradient (propagatorW C p.1 t phi) p.2 else 0

def noiseClass (C : WholeCoeff d) (mu : Measure (Euc d))
    (t : ℝ) (phi : Euc d → ℝ) : NoiseHilbert mu :=
  if h : MemLp (noiseVector C t phi) 2 ((volume : Measure ℝ).prod mu)
    then h.toLp (noiseVector C t phi) else 0

def scaledNoiseClass (C : WholeCoeff d) (mu : Measure (Euc d))
    (q t : ℝ) (phi : Euc d → ℝ) : NoiseHilbert mu :=
  Real.sqrt (2 * q) • noiseClass C mu t phi

theorem noiseClass_ae {C : WholeCoeff d} {mu : Measure (Euc d)}
    {t : ℝ} {phi : Euc d → ℝ}
    (h : MemLp (noiseVector C t phi) 2 ((volume : Measure ℝ).prod mu)) :
    (noiseClass C mu t phi : ℝ × Euc d → Euc d) =ᵐ[(volume : Measure ℝ).prod mu]
      noiseVector C t phi := by
  rw [noiseClass, dif_pos h]
  exact h.coeFn_toLp

theorem classical_gradient_continuous {C : WholeCoeff d} {t : ℝ}
    {phi : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t phi f) :
    Continuous (fun p : Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2) := by
  have h := (jetGradientEquiv d).continuous.comp (hf.cont_c2 1 (by norm_num))
  simpa only [Function.comp_def, jetGradientEquiv_apply] using h

theorem noiseVector_stronglyMeasurable {C : WholeCoeff d} {t : ℝ}
    (ht : 0 ≤ t) {phi : Euc d → ℝ}
    (hf : IsClassicalAdjointW C t phi (fun r => propagatorW C r t phi)) :
    StronglyMeasurable (noiseVector C t phi) := by
  let F : ℝ × Euc d → Euc d := fun p =>
    gradient (propagatorW C (Set.projIcc 0 t ht p.1) t phi) p.2
  have hF : Continuous F :=
    (classical_gradient_continuous hf).comp
      (((continuous_projIcc (h := ht)).comp continuous_fst).prodMk continuous_snd)
  have he : noiseVector C t phi = (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))).indicator F := by
    funext p
    by_cases hp : p.1 ∈ Icc (0 : ℝ) t
    · simp [noiseVector, Set.indicator_of_mem, hp, F, Set.projIcc_of_mem ht hp]
    · simp [noiseVector, hp]
  rw [he]
  exact hF.stronglyMeasurable.indicator (measurableSet_Icc.prod MeasurableSet.univ)

theorem noiseVector_memLp {C : WholeCoeff d} {mu : Measure (Euc d)}
    [IsProbabilityMeasure mu] {t : ℝ} (ht : 0 ≤ t) {phi : Euc d → ℝ}
    (hf : IsClassicalAdjointW C t phi (fun r => propagatorW C r t phi)) :
    MemLp (noiseVector C t phi) 2 ((volume : Measure ℝ).prod mu) := by
  obtain ⟨B, hB⟩ := hf.bdd 1 (by norm_num)
  have hS : MeasurableSet (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hSf : ((volume : Measure ℝ).prod mu)
      (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) ≠ (∞ : ENNReal) := by
    simp only [Measure.prod_prod, measure_univ, mul_one]
    simp [Real.volume_Icc]
  have hmajor : MemLp
      ((Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))).indicator (fun _ => B))
      2 ((volume : Measure ℝ).prod mu) :=
    memLp_indicator_const 2 hS B (Or.inr hSf)
  refine hmajor.mono' (noiseVector_stronglyMeasurable ht hf).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  by_cases hp : p.1 ∈ Icc (0 : ℝ) t
  · simp only [noiseVector, if_pos hp,
      Set.indicator_of_mem (show p ∈ Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d)) from ⟨hp, mem_univ _⟩)]
    rw [HRS.MS.MovDec.mov2e_norm_gradient, ← norm_iteratedFDeriv_one]
    exact hB p.1 hp p.2
  · simp [noiseVector, hp]

/-- The feature Gram form, before multiplying by the physical noise rate. -/
theorem noiseClass_inner {C : WholeCoeff d} {mu : Measure (Euc d)}
    [IsProbabilityMeasure mu] {t v : ℝ} (ht : 0 ≤ t) (hv : 0 ≤ v)
    {phi psi : Euc d → ℝ}
    (hf : IsClassicalAdjointW C t phi (fun r => propagatorW C r t phi))
    (hg : IsClassicalAdjointW C v psi (fun r => propagatorW C r v psi)) :
    inner ℝ (noiseClass C mu t phi) (noiseClass C mu v psi) =
      ∫ r in Icc (0 : ℝ) (min t v), ∫ x,
        inner ℝ (gradient (propagatorW C r t phi) x)
          (gradient (propagatorW C r v psi) x) ∂mu := by
  have hm1 := noiseVector_memLp ht hf (mu := mu)
  have hm2 := noiseVector_memLp hv hg (mu := mu)
  have he : (fun p => inner ℝ (noiseClass C mu t phi p) (noiseClass C mu v psi p))
      =ᵐ[(volume : Measure ℝ).prod mu]
      (fun p => inner ℝ (noiseVector C t phi p) (noiseVector C v psi p)) := by
    filter_upwards [noiseClass_ae hm1, noiseClass_ae hm2] with p hp hq
    rw [hp, hq]
  have hi : Integrable (fun p => inner ℝ (noiseVector C t phi p) (noiseVector C v psi p))
      ((volume : Measure ℝ).prod mu) :=
    (L2.integrable_inner (𝕜 := ℝ) (noiseClass C mu t phi) (noiseClass C mu v psi)).congr he
  rw [L2.inner_def, integral_congr_ae he, integral_prod _ hi]
  have hpoint : (fun r => ∫ x, inner ℝ (noiseVector C t phi (r, x))
        (noiseVector C v psi (r, x)) ∂mu) =
      (Icc (0 : ℝ) (min t v)).indicator (fun r => ∫ x,
        inner ℝ (gradient (propagatorW C r t phi) x)
          (gradient (propagatorW C r v psi) x) ∂mu) := by
    funext r
    by_cases hr : r ∈ Icc (0 : ℝ) (min t v)
    · have hrt : r ∈ Icc (0 : ℝ) t := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
      have hrv : r ∈ Icc (0 : ℝ) v := ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
      simp [noiseVector, hrt, hrv, hr]
    · have hnot : ¬ (r ∈ Icc (0 : ℝ) t ∧ r ∈ Icc (0 : ℝ) v) := by
        rintro ⟨hrt, hrv⟩
        exact hr ⟨hrt.1, le_min hrt.2 hrv.2⟩
      by_cases hrt : r ∈ Icc (0 : ℝ) t
      · have hrv : r ∉ Icc (0 : ℝ) v := fun h => hnot ⟨hrt, h⟩
        simp [noiseVector, hrt, hrv, hr]
      · simp [noiseVector, hrt, hr]
  rw [hpoint, integral_indicator measurableSet_Icc]

theorem scaledNoiseClass_inner {C : WholeCoeff d} {mu : Measure (Euc d)}
    [IsProbabilityMeasure mu] {q t v : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) (hv : 0 ≤ v)
    {phi psi : Euc d → ℝ}
    (hf : IsClassicalAdjointW C t phi (fun r => propagatorW C r t phi))
    (hg : IsClassicalAdjointW C v psi (fun r => propagatorW C r v psi)) :
    inner ℝ (scaledNoiseClass C mu q t phi) (scaledNoiseClass C mu q v psi) =
      (2 * q) * ∫ r in Icc (0 : ℝ) (min t v), ∫ x,
        inner ℝ (gradient (propagatorW C r t phi) x)
          (gradient (propagatorW C r v psi) x) ∂mu := by
  simp only [scaledNoiseClass, real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, Real.mul_self_sqrt (mul_nonneg (by norm_num) hq), noiseClass_inner ht hv hf hg]

/-- The actual physical feature has exactly the frozen noise covariance.
No Gaussian evolution, abstract feature representation, or orbit input is
assumed in this theorem. -/
theorem physical_noise_feature_inner (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    {t v : ℝ} (ht : 0 ≤ t) (hv : 0 ≤ v)
    {phi psi : Euc d → ℝ}
    (hphi : IsOscTest (wholeSpaceIndex d) phi)
    (hpsi : IsOscTest (wholeSpaceIndex d) psi) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    inner ℝ (scaledNoiseClass C (HRS.Whole.withDensityReal rho) beta⁻¹ t phi)
      (scaledNoiseClass C (HRS.Whole.withDensityReal rho) beta⁻¹ v psi) =
      noiseCovW C beta⁻¹ t v phi psi := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  have hX := x1Input_of_exist hd hs0 hs ha hbeta (0 : ℝ) hrho
    (exist_of_thermal hd hs0 hs ha hbeta hrho)
  have hf := x1_prop_classical (hX.exist t ht phi hphi)
  have hg := x1_prop_classical (hX.exist v hv psi hpsi)
  have hfeature := scaledNoiseClass_inner (C := C) (mu := HRS.Whole.withDensityReal rho)
    (inv_nonneg.2 hbeta.le) ht hv hf hg
  have hnoise := s111x2_noise_eq hd hs0 hs ha hbeta hrho ht hv hf hg
  exact hfeature.trans hnoise.symm

#print axioms physical_noise_feature_inner

end HRS.MS.ProClosureS111
