import HRS.MS.Fp81S21GaussFeature
import HRS.MS.Fp81S21GaussIncr
import HRS.MS.Fp81S21GaussIncr2
import HRS.MS.Fp81S21GaussIncr3

/-!
# HRS S2.1(iii), SOL71 G2: initial-feature increment contribution

This file proves the start-uniform increment estimate for the initial Gaussian
feature.  The full Gaussian increment theorem also needs an exponentially
decaying terminal-time difference estimate for the noise gradient; that
additional estimate is not among the G1 exports.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.CovMeas
open HRS.MS.S111X1 HRS.MS.S111X2

private theorem fp81s21_gaussIncrFull_orbit_increment_pointwise
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {B : ℝ}
    (hscalar : ∀ H : ℝ, 0 < H → ∀ b : ℝ, 0 ≤ b →
      ∀ α : MultiIndex p.d, ∀ z ∈ Icc b (b + H), ∀ x : Euc p.d,
        |s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
            (b + H) b z α x| ≤ B * s104_b p.d α ∧
        s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
            (b + H) b z α x =
          propagatorW (r26t3_coeff R) b z
            (generatorW (r26t3_coeff R) z
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
    {a H s t : ℝ} (ha : 0 ≤ a) (hH : 0 < H)
    (hs : s ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (α : MultiIndex p.d) (x : Euc p.d) :
    |propagatorW (r26t3_coeff R) 0 (a + t)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x -
      propagatorW (r26t3_coeff R) 0 (a + s)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x| ≤
      B * s104_b p.d α * |t - s| := by
  let T : ℝ := a + H
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let f : ℝ → ℝ := fun z => propagatorW (r26t3_coeff R) 0 z φ x
  let f' : ℝ → ℝ := fun z =>
    propagatorW (r26t3_coeff R) 0 z
      (generatorW (r26t3_coeff R) z φ) x
  have hT : 0 < T := by dsimp [T]; linarith
  have h0T : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hder : ∀ z ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt f (f' z) (Icc (0 : ℝ) T) z := by
    intro z hz
    have hd := fp81s21_moving_terminal_derivative_within p R hT hterm α
      0 h0T z hz hT x
    simpa [f, f', φ] using hd
  have hderBound : ∀ z ∈ Icc (0 : ℝ) T, ‖f' z‖ ≤ B * s104_b p.d α := by
    intro z hz
    have hb := hscalar T hT 0 le_rfl α z (by simpa using hz) x
    change ‖propagatorW (r26t3_coeff R) 0 z
        (generatorW (r26t3_coeff R) z φ) x‖ ≤ _
    calc
      _ = |propagatorW (r26t3_coeff R) 0 z
          (generatorW (r26t3_coeff R) z φ) x| := Real.norm_eq_abs _
      _ = |s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          T 0 z α x| := by rw [← hb.2, zero_add]
      _ ≤ B * s104_b p.d α := by simpa only [zero_add] using hb.1
  have hsT : a + s ∈ Icc (0 : ℝ) T := by
    change 0 ≤ a + s ∧ a + s ≤ T
    constructor
    · linarith [ha, hs.1]
    · dsimp [T]
      linarith [hs.2]
  have htT : a + t ∈ Icc (0 : ℝ) T := by
    change 0 ≤ a + t ∧ a + t ≤ T
    constructor
    · linarith [ha, ht.1]
    · dsimp [T]
      linarith [ht.2]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (s := Icc (0 : ℝ) T) hder hderBound
    (convex_Icc (0 : ℝ) T) hsT htT
  have htime : ‖(a + t) - (a + s)‖ = |t - s| := by
    rw [Real.norm_eq_abs]
    congr 1 <;> ring
  calc
    _ = ‖f (a + t) - f (a + s)‖ := by rw [Real.norm_eq_abs]
    _ ≤ B * s104_b p.d α * ‖(a + t) - (a + s)‖ := hmvt
    _ = B * s104_b p.d α * |t - s| := by rw [htime]

private theorem fp81s21_gaussIncrFull_initial_feature_norm_le
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
      Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {B a H s t : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hs : s ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (α : MultiIndex p.d)
    (hpoint : ∀ x : Euc p.d,
      |propagatorW (r26t3_coeff R) 0 (a + t)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x -
        propagatorW (r26t3_coeff R) 0 (a + s)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x| ≤
        B * s104_b p.d α * |t - s|) :
    ‖fp81s21_initialGaussianFeature p R hK (a + t)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
      fp81s21_initialGaussianFeature p R hK (a + s)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ≤
      B * s104_b p.d α * |t - s| := by
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
    HRS.MS.GenPath.s56_isOscTest _ α
  have ht0 : 0 ≤ a + t := by linarith [ha, ht.1]
  have hs0 : 0 ≤ a + s := by linarith [ha, hs.1]
  have hmemt : MemLp (propagatorW (r26t3_coeff R) 0 (a + t) φ) 2 μ := by
    have hc := fp81s21_U_osc_test_classical p R hφ ht0
    exact HRS.MS.S111X1.x1_classical_memLp hc ⟨le_rfl, ht0⟩ μ
  have hmems : MemLp (propagatorW (r26t3_coeff R) 0 (a + s) φ) 2 μ := by
    have hc := fp81s21_U_osc_test_classical p R hφ hs0
    exact HRS.MS.S111X1.x1_classical_memLp hc ⟨le_rfl, hs0⟩ μ
  have hpointAE : ∀ᵐ x ∂μ,
      ‖(HRS.MS.S111X2.s111x2_toLp μ
          (propagatorW (r26t3_coeff R) 0 (a + t) φ) -
        HRS.MS.S111X2.s111x2_toLp μ
          (propagatorW (r26t3_coeff R) 0 (a + s) φ) : Lp ℝ 2 μ) x‖ ≤
        B * s104_b p.d α * |t - s| := by
    filter_upwards [Lp.coeFn_sub
        (HRS.MS.S111X2.s111x2_toLp μ
          (propagatorW (r26t3_coeff R) 0 (a + t) φ))
        (HRS.MS.S111X2.s111x2_toLp μ
          (propagatorW (r26t3_coeff R) 0 (a + s) φ)),
      HRS.MS.S111X2.s111x2_toLp_ae hmemt,
      HRS.MS.S111X2.s111x2_toLp_ae hmems] with x hsub htx hsx
    rw [hsub, Pi.sub_apply, htx, hsx, Real.norm_eq_abs]
    exact hpoint x
  have hbound := Lp.norm_le_of_ae_bound
    (mul_nonneg (mul_nonneg hB (s104_b_nonneg α)) (abs_nonneg _)) hpointAE
  have hmeasure : measureUnivNNReal μ = 1 := by simp [μ, measureUnivNNReal]
  rw [hmeasure] at hbound
  have hbound' :
      ‖HRS.MS.S111X2.s111x2_toLp μ
          (propagatorW (r26t3_coeff R) 0 (a + t) φ) -
        HRS.MS.S111X2.s111x2_toLp μ
          (propagatorW (r26t3_coeff R) 0 (a + s) φ)‖ ≤
        B * s104_b p.d α * |t - s| := by
    simpa using hbound
  have hcontract := HRS.MS.ProClosureS111.initialGaussianFeature_sub_norm_le
    hK p.hγ (r26t3_coeff R) (a + t) (a + s) φ
  simpa [fp81s21_initialGaussianFeature, φ] using hcontract.trans hbound'

/-- Uniform initial-feature contribution to the full increment estimate.
The feature parameters are fixed after `R` and before the horizon, shift, and
times. -/
theorem fp81s21_gaussian_initial_feature_increment_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∀ (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)],
        ∃ B : ℝ, 0 ≤ B ∧
          ∃ Mg : ℝ, ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
            Lp ℝ 2 (r26t3_mu R 0),
          ∃ hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg,
            ∀ H : ℝ, 0 < H → ∀ a : ℝ, 0 ≤ a →
              ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
                ∀ α : MultiIndex p.d,
                  ‖fp81s21_initialGaussianFeature p R hK (a + t)
                      (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
                    fp81s21_initialGaussianFeature p R hK (a + s)
                      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2 ≤
                    (B * s104_b p.d α) ^ 2 * |t - s| ^ 2 := by
  obtain ⟨δc, Co, co, hδc, hδchalf, hco, hcommon⟩ :=
    fp81s21_common_radius p
  obtain ⟨δs, hδs, hδshalf, hscalar⟩ :=
    fp81s21_gauss_incr_scalar_terminal_bound p
  let δ0 : ℝ := min δc δs
  have hδ0 : 0 < δ0 := lt_min hδc hδs
  have hδ0half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδchalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hμ
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
  have hδcR : δ ≤ δc := hδle.trans (min_le_left _ _)
  have hδsR : δ ≤ δs := hδle.trans (min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0half
  obtain ⟨B, hB, hscalarR⟩ := hscalar δ hδ hδsR R
  obtain ⟨_, _, hterm, _⟩ :=
    hcommon δ hδ hδcR R.ρβ R.thermal
  obtain ⟨Mg, K, hK⟩ := fp81s21_actualInitialKRep_exists p hδ hδhalf R
  refine ⟨B, hB, Mg, K, hK, ?_⟩
  intro H hH a ha s hs t ht α
  have hpoint := fp81s21_gaussIncrFull_orbit_increment_pointwise
    p R hterm hscalarR ha hH hs ht α
  have hnorm := fp81s21_gaussIncrFull_initial_feature_norm_le
    p R hK hB ha hs ht α hpoint
  have hcoef : 0 ≤ B * s104_b p.d α * |t - s| :=
    mul_nonneg (mul_nonneg hB (s104_b_nonneg α)) (abs_nonneg _)
  calc
    _ ≤ (B * s104_b p.d α * |t - s|) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hcoef).2 hnorm
    _ = (B * s104_b p.d α) ^ 2 * |t - s| ^ 2 := by ring

#print axioms fp81s21_gaussian_initial_feature_increment_bound

end HRS.Fp81.S21

end
