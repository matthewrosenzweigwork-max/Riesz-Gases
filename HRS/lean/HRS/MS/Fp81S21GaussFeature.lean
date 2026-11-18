import HRS.MS.Fp81S21MovingNoise
import HRS.MS.ProClosureS111InitialGaussianFeatures
import HRS.MS.S21H2_S14aD5
import HRS.MS.S21E_Dens

/-!
# HRS S2.1(iii), SOL71 A1: initial and moving-noise Gaussian features

The initial feature is the generic positive-square-root feature from S11.1,
specialized to the actual initial density and the actual KRep supplied by
`s21h2_krep_init`.  The joint feature lives in the Hilbert direct sum
`WithLp 2 (L²(μ₀) × MovingNoiseHilbert p.d)`.

Exact types:
* `fp81s21_initialGaussianFeature R hK t φ : Lp ℝ 2 (r26t3_mu R 0)`;
* `fp81s21_combinedFeature R hK t φ : WithLp 2
    (Lp ℝ 2 (r26t3_mu R 0) × MovingNoiseHilbert p.d)`;
* `fp81s21_combinedFeature_gram` identifies its inner product with
  `HRS.MS.S21E.s21eCov` for every pair of nonnegative times.

This file does not assert a uniform oscillator envelope for the initial
feature; that requires the separate moving-orbit bound from the design.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.S111X2

/-- The actual initial reference is a probability measure. -/
theorem fp81s21_initialMeasure_isProbability
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    IsProbabilityMeasure (r26t3_mu R 0) := by
  change IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0))
  exact HRS.Whole.Q34.isProbabilityMeasure_nu
    (R.resulting.global 0 |>.density 0 ⟨le_rfl, le_rfl⟩)

/-- `s21h2_krep_init` supplies the actual KRep at `μ₀ = r26t3_mu R 0`. -/
theorem fp81s21_actualInitialKRep_exists
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)] :
    ∃ Mg : ℝ, ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0),
      KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  exact s21h2_krep_init hδ hδhalf R

/-- The actual initial feature `sqrt(R_γ) P_{μ₀}[U^{0,t} φ]`. -/
def fp81s21_initialGaussianFeature
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (t : ℝ) (φ : Euc p.d → ℝ) : Lp ℝ 2 (r26t3_mu R 0) :=
  HRS.MS.ProClosureS111.initialGaussianFeature hK p.hγ
    (r26t3_coeff R) t φ

private theorem fp81s21_initial_orbit_memLp
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {t : ℝ} (ht : 0 ≤ t) {φ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    MemLp (propagatorW (r26t3_coeff R) 0 t φ) 2 (r26t3_mu R 0) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  have hclass := fp81s21_U_osc_test_classical p R hφ ht
  exact HRS.MS.S111X1.x1_classical_memLp hclass ⟨le_rfl, ht⟩ _

/-- The feature map is linear on oscillator tests, using linearity of the
actual moving propagator and the continuous linear centered response map. -/
theorem fp81s21_initialGaussianFeature_add_smul
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {t : ℝ} (ht : 0 ≤ t) {φ ψ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ)
    (hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) ψ) (c : ℝ) :
    fp81s21_initialGaussianFeature p R hK t (fun x => φ x + c * ψ x) =
      fp81s21_initialGaussianFeature p R hK t φ +
        c • fp81s21_initialGaussianFeature p R hK t ψ := by
  let μ₀ := r26t3_mu R 0
  have hsum : IsOscTest (wholeSpaceIndex p.d : ℝ)
      (fun x => φ x + c * ψ x) := by
    let m : ℝ := wholeSpaceIndex p.d
    have hsmul := (HRS.MS.S111X1.oscSub p.d m).smul_mem c hψ
    have hadd := (HRS.MS.S111X1.oscSub p.d m).add_mem hφ hsmul
    change IsOscTest m (fun x => φ x + c * ψ x) at hadd
    simpa [m] using hadd
  have hφmem := fp81s21_initial_orbit_memLp p R ht hφ
  have hψmem := fp81s21_initial_orbit_memLp p R ht hψ
  have hsumMem := fp81s21_initial_orbit_memLp p R ht hsum
  have hU := fp81s21_U_linear_of_osc_test p R hφ hψ c ht
    ⟨le_rfl, ht⟩
  have hU' : propagatorW (r26t3_coeff R) 0 t (fun x => φ x + c * ψ x) =
      fun x => propagatorW (r26t3_coeff R) 0 t φ x +
        c * propagatorW (r26t3_coeff R) 0 t ψ x := by
    simpa only [r26t3_U] using hU
  have hLp : HRS.MS.S111X2.s111x2_toLp μ₀
        (propagatorW (r26t3_coeff R) 0 t (fun x => φ x + c * ψ x)) =
      HRS.MS.S111X2.s111x2_toLp μ₀ (propagatorW (r26t3_coeff R) 0 t φ) +
        c • HRS.MS.S111X2.s111x2_toLp μ₀ (propagatorW (r26t3_coeff R) 0 t ψ) := by
    apply Lp.ext
    filter_upwards [HRS.MS.S111X2.s111x2_toLp_ae hsumMem,
      HRS.MS.S111X2.s111x2_toLp_ae hφmem,
      HRS.MS.S111X2.s111x2_toLp_ae hψmem,
      Lp.coeFn_add (HRS.MS.S111X2.s111x2_toLp μ₀
        (propagatorW (r26t3_coeff R) 0 t φ))
        (c • HRS.MS.S111X2.s111x2_toLp μ₀
          (propagatorW (r26t3_coeff R) 0 t ψ)),
      Lp.coeFn_smul c (HRS.MS.S111X2.s111x2_toLp μ₀
        (propagatorW (r26t3_coeff R) 0 t ψ))] with x hsumx hφx hψx hadd hsmul
    calc
      (HRS.MS.S111X2.s111x2_toLp μ₀
        (propagatorW (r26t3_coeff R) 0 t (fun x => φ x + c * ψ x)) : Euc p.d → ℝ) x =
          propagatorW (r26t3_coeff R) 0 t (fun x => φ x + c * ψ x) x := hsumx
      _ = propagatorW (r26t3_coeff R) 0 t φ x +
          c * propagatorW (r26t3_coeff R) 0 t ψ x := congrFun hU' x
      _ = (HRS.MS.S111X2.s111x2_toLp μ₀ (propagatorW (r26t3_coeff R) 0 t φ) +
          c • HRS.MS.S111X2.s111x2_toLp μ₀
            (propagatorW (r26t3_coeff R) 0 t ψ) : Lp ℝ 2 μ₀) x := by
        rw [← hφx, ← hψx, hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul]
  simp only [fp81s21_initialGaussianFeature,
    HRS.MS.ProClosureS111.initialGaussianFeature]
  rw [hLp]
  simp only [map_add, map_smul]
  rfl

/-- Contraction of the actual initial feature by its generic Gaussian feature
bound. -/
theorem fp81s21_initialGaussianFeature_norm_le
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (t : ℝ) (φ : Euc p.d → ℝ) :
    ‖fp81s21_initialGaussianFeature p R hK t φ‖ ≤
      ‖HRS.MS.S111X2.s111x2_toLp (r26t3_mu R 0)
        (propagatorW (r26t3_coeff R) 0 t φ)‖ := by
  exact HRS.MS.ProClosureS111.initialGaussianFeature_norm_le
    hK p.hγ (r26t3_coeff R) t φ

/-- The combined, horizon independent Hilbert feature space. -/
abbrev Fp81S21GaussFeatureHilbert (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) :=
  WithLp 2 (Lp ℝ 2 (r26t3_mu R 0) × MovingNoiseHilbert p.d)

/-- The combined initial-plus-noise feature at time `t`. -/
def fp81s21_combinedFeature
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (t : ℝ) (φ : Euc p.d → ℝ) : Fp81S21GaussFeatureHilbert p R :=
  WithLp.toLp 2
    (fp81s21_initialGaussianFeature p R hK t φ,
      movingNoiseFeature R 0 t φ)

/-- The combined feature map is linear on oscillator tests. -/
theorem fp81s21_combinedFeature_add_smul
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) {φ ψ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ)
    (hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) ψ) (c : ℝ) :
    fp81s21_combinedFeature p R hK t (fun x => φ x + c * ψ x) =
      fp81s21_combinedFeature p R hK t φ +
        c • fp81s21_combinedFeature p R hK t ψ := by
  unfold fp81s21_combinedFeature
  rw [fp81s21_initialGaussianFeature_add_smul p R hK ht.1 hφ hψ c,
    fp81s21_movingNoiseFeature_add_smul p R hδ hδhalf hH ⟨le_rfl, hH.le⟩ ht
      hφ hψ c]
  rfl

/-- Gram identity for the combined feature.  The feature definition has no
horizon; a finite positive horizon is chosen only to apply the noise-feature
specification. -/
theorem fp81s21_combinedFeature_gram
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    {ψ φ : Euc p.d → ℝ}
    (hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) ψ)
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    inner ℝ (fp81s21_combinedFeature p R hK r ψ)
      (fp81s21_combinedFeature p R hK t φ) =
      HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ φ := by
  let μ₀ := r26t3_mu R 0
  let H := max r t + 1
  have hH : 0 < H := by
    dsimp [H]
    linarith [le_max_left r t]
  have hrH : r ∈ Icc (0 : ℝ) H := by
    constructor
    · exact hr
    · dsimp [H]
      linarith [le_max_left r t]
  have htH : t ∈ Icc (0 : ℝ) H := by
    constructor
    · exact ht
    · dsimp [H]
      linarith [le_max_right r t]
  have hinitial := HRS.MS.ProClosureS111.initialGaussianFeature_inner
    hK p.hγ (r26t3_coeff R) r t ψ φ
    (fp81s21_initial_orbit_memLp p R hr hψ)
    (fp81s21_initial_orbit_memLp p R ht hφ)
  have hinitial' :
      inner ℝ (fp81s21_initialGaussianFeature p R hK r ψ)
        (fp81s21_initialGaussianFeature p R hK t φ) =
        HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ₀ p.γ
          (propagatorW (r26t3_coeff R) 0 r ψ)
          (propagatorW (r26t3_coeff R) 0 t φ) := by
    simpa only [fp81s21_initialGaussianFeature] using hinitial
  have hnoise := (movingNoiseFeature_spec p R hδ hδhalf hH).2
    0 ⟨le_rfl, hH.le⟩ r hrH t htH ψ φ hψ hφ
  have hnoiseCov :
      inner ℝ (movingNoiseFeature R 0 r ψ) (movingNoiseFeature R 0 t φ) =
        HRS.Whole.noiseCovW (r26t3_coeff R) p.β⁻¹ r t ψ φ := by
    have hnoise0 :
        inner ℝ (movingNoiseFeature R 0 r ψ) (movingNoiseFeature R 0 t φ) =
          2 * p.β⁻¹ * ∫ u in Icc (0 : ℝ) (min r t), ∫ x,
            inner ℝ (gradient (propagatorW (r26t3_coeff R) u r ψ) x)
              (gradient (propagatorW (r26t3_coeff R) u t φ) x) * R.ρ u x := by
      simpa only [r26t3_U] using hnoise
    calc
      _ = 2 * p.β⁻¹ * ∫ u in Icc (0 : ℝ) (min r t), ∫ x,
            inner ℝ (gradient (propagatorW (r26t3_coeff R) u r ψ) x)
              (gradient (propagatorW (r26t3_coeff R) u t φ) x) * R.ρ u x := hnoise0
      _ = HRS.Whole.noiseCovW (r26t3_coeff R) p.β⁻¹ r t ψ φ := by
            rw [HRS.Whole.noiseCovW]
            rw [show (r26t3_coeff R).ρ = R.ρ by rfl]
  have hpair := WithLp.prod_inner_apply (𝕜 := ℝ)
    (WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK r ψ,
      movingNoiseFeature R 0 r ψ) : Fp81S21GaussFeatureHilbert p R)
    (WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK t φ,
      movingNoiseFeature R 0 t φ))
  have hpair' :
      inner ℝ (WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK r ψ,
        movingNoiseFeature R 0 r ψ))
        (WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK t φ,
          movingNoiseFeature R 0 t φ)) =
        inner ℝ (fp81s21_initialGaussianFeature p R hK r ψ)
          (fp81s21_initialGaussianFeature p R hK t φ) +
        inner ℝ (movingNoiseFeature R 0 r ψ) (movingNoiseFeature R 0 t φ) := by
    simpa only [WithLp.ofLp_toLp] using hpair
  calc
    _ = inner ℝ (fp81s21_initialGaussianFeature p R hK r ψ)
          (fp81s21_initialGaussianFeature p R hK t φ) +
        inner ℝ (movingNoiseFeature R 0 r ψ) (movingNoiseFeature R 0 t φ) := by
          exact hpair'
    _ = HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ₀ p.γ
          (propagatorW (r26t3_coeff R) 0 r ψ)
          (propagatorW (r26t3_coeff R) 0 t φ) +
        HRS.Whole.noiseCovW (r26t3_coeff R) p.β⁻¹ r t ψ φ := by
          rw [hinitial', hnoiseCov]
    _ = HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ φ := by
          rfl

#print axioms HRS.Fp81.S21.fp81s21_initialMeasure_isProbability
#print axioms HRS.Fp81.S21.fp81s21_actualInitialKRep_exists
#print axioms HRS.Fp81.S21.fp81s21_initialGaussianFeature_add_smul
#print axioms HRS.Fp81.S21.fp81s21_initialGaussianFeature_norm_le
#print axioms HRS.Fp81.S21.fp81s21_combinedFeature_add_smul
#print axioms HRS.Fp81.S21.fp81s21_combinedFeature_gram

end HRS.Fp81.S21

end
