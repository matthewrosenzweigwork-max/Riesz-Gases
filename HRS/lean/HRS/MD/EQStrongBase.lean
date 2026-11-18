import HRS.MD.EQInitParticle
import HRS.Stochastic.LyonsZhengSpec
import HRS.Sections.Q38bAux1

/-!
# EQ-STRONG (flow clause), base: the Fourier statistics as Lyons-Zheng test functions

`stF N w f X = w * (√N * (N⁻¹ * ∑_i f (X i)))` is `w √N μ_N(f)`.  For `f = e_k` (`Torus.realMode k`) it is an `IsLZTest` for every
finite measure (`C^∞` on the covering space, bounded), and `configGradSq (stF N w e_k) ≤ 2 w² ⟨k⟩²` pointwise
(`∂_a e_k = 2π k_a e_{-k}`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQStrong

open HRS.LZ

variable {d : ℕ}

/-- `w √N μ_N(f)` as a function of the configuration. -/
def stF (N : ℕ) (w : ℝ) (f : Torus d → ℝ) (X : Config d N) : ℝ :=
  w * (Real.sqrt N * ((N : ℝ)⁻¹ * ∑ i, f (X i)))

theorem stF_eq_pair {N : ℕ} (hN : 0 < N) (w : ℝ) (f : Torus d → ℝ) (X : Config d N) :
    stF N w f X = w * (Real.sqrt N * pair (empirical X) f) := by
  unfold stF
  rw [pair_empirical hN]

theorem continuous_stF (N : ℕ) (w : ℝ) {f : Torus d → ℝ} (hf : Continuous f) :
    Continuous (stF N w f) := by
  unfold stF
  exact continuous_const.mul (continuous_const.mul (continuous_const.mul
    (continuous_finsetSum _ fun i _ => hf.comp (continuous_apply i))))

theorem abs_stF_le (N : ℕ) (w B : ℝ) {f : Torus d → ℝ} (hB : ∀ x, |f x| ≤ B) (hB0 : 0 ≤ B)
    (hN : 0 < N) (X : Config d N) :
    |stF N w f X| ≤ |w| * (Real.sqrt N * B) := by
  unfold stF
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : |(N : ℝ)⁻¹ * ∑ i, f (X i)| ≤ B := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hN0)]
    have : |∑ i, f (X i)| ≤ N * B := by
      calc |∑ i, f (X i)| ≤ ∑ i, |f (X i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hB _
        _ = N * B := by simp
    calc (N : ℝ)⁻¹ * |∑ i, f (X i)| ≤ (N : ℝ)⁻¹ * (N * B) := by gcongr
      _ = B := by field_simp
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  gcongr

theorem configLift_stF (N : ℕ) (w : ℝ) (f : Torus d → ℝ) :
    configLift (fun _ => stF N w f) 0 =
      fun Y : Fin N → Euc d => (w * Real.sqrt N * (N : ℝ)⁻¹) * ∑ i, Torus.lift f (Y i) := by
  funext Y
  simp only [configLift, stF, Torus.lift, Function.comp]
  ring

theorem contDiff_configLift_stF (N : ℕ) (w : ℝ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ContDiff ℝ 1 (configLift (fun _ => stF N w f) 0) := by
  rw [configLift_stF]
  have hg : ContDiff ℝ 1 (Torus.lift f) :=
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf)
      (by exact_mod_cast le_top)
  exact contDiff_const.mul (ContDiff.sum fun i _ => hg.comp (contDiff_apply ℝ _ i))

theorem fderiv_configLift_stF (N : ℕ) (w : ℝ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (Y : Fin N → Euc d) (i₀ : Fin N) (a : Fin d) :
    fderiv ℝ (configLift (fun _ => stF N w f) 0) Y (configBasis d N (i₀, a)) =
      (w * Real.sqrt N * (N : ℝ)⁻¹) *
        fderiv ℝ (Torus.lift f) (Y i₀) (EuclideanSpace.single a 1) := by
  have hg : ContDiff ℝ 1 (Torus.lift f) :=
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf)
      (by exact_mod_cast le_top)
  have hgd : Differentiable ℝ (Torus.lift f) := hg.differentiable (by simp)
  have hterm : ∀ i : Fin N, HasFDerivAt (fun Y : Fin N → Euc d => Torus.lift f (Y i))
      ((fderiv ℝ (Torus.lift f) (Y i)).comp (ContinuousLinearMap.proj i)) Y := by
    intro i
    exact (hgd (Y i)).hasFDerivAt.comp Y
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i))
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  have hall := hsum.const_mul (w * Real.sqrt N * (N : ℝ)⁻¹)
  rw [configLift_stF, hall.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  congr 1
  rw [Finset.sum_eq_single i₀]
  · simp [configBasis]
  · intro i _ hi
    simp [configBasis, Pi.single_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem configGradSq_stF_realMode (N : ℕ) (w : ℝ) (k : NonzeroLattice d) (X : Config d N) :
    configGradSq (stF N w (Torus.realMode k)) X =
      (w * Real.sqrt N * (N : ℝ)⁻¹) ^ 2 *
        ∑ i : Fin N, ∑ a : Fin d, (2 * Real.pi * (k.1 a : ℝ) *
          Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ (X i)) ^ 2 := by
  have hf := HRS.q38b_isSmooth_realMode (d := d) k
  unfold configGradSq
  rw [Fintype.sum_prod_type]
  simp only [fderiv_configLift_stF N w hf, mul_pow]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := HRS.q38b_partialDeriv_realMode_eq a k (X i)
  unfold Torus.partialDeriv at this
  rw [this]; ring

theorem sum_sq_partial_le (k : NonzeroLattice d) (x : Torus d) :
    ∑ a : Fin d, (2 * Real.pi * (k.1 a : ℝ) * Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ x) ^ 2
      ≤ 2 * Lattice.jp k.1 ^ 2 := by
  have he : (Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ x) ^ 2 ≤ 2 := by
    have h1 := Torus.abs_realMode_le (⟨-k.1, neg_ne_zero.2 k.2⟩ : NonzeroLattice d) x
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [abs_nonneg (Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ x), sq_abs
      (Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ x), Real.sqrt_nonneg 2]
  have hnorm : ∑ a : Fin d, ((k.1 a : ℝ)) ^ 2 = Lattice.enorm k.1 ^ 2 := by
    unfold Lattice.enorm Lattice.toEuc
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have hjp : (2 * Real.pi * Lattice.enorm k.1) ^ 2 ≤ Lattice.jp k.1 ^ 2 := by
    have := Torus.two_pi_enorm_le_jp k.1
    have h0 : 0 ≤ 2 * Real.pi * Lattice.enorm k.1 := by
      unfold Lattice.enorm; positivity
    exact pow_le_pow_left₀ h0 this 2
  calc ∑ a : Fin d, (2 * Real.pi * (k.1 a : ℝ) * Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ x) ^ 2
      = (2 * Real.pi) ^ 2 * (∑ a : Fin d, ((k.1 a : ℝ)) ^ 2) *
          (Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ x) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = (2 * Real.pi * Lattice.enorm k.1) ^ 2 *
          (Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ x) ^ 2 := by rw [hnorm]; ring
    _ ≤ Lattice.jp k.1 ^ 2 * 2 := by
        gcongr
    _ = _ := by ring

theorem configGradSq_stF_le (N : ℕ) (hN : 0 < N) (w : ℝ) (k : NonzeroLattice d) (X : Config d N) :
    configGradSq (stF N w (Torus.realMode k)) X ≤ 2 * w ^ 2 * Lattice.jp k.1 ^ 2 := by
  rw [configGradSq_stF_realMode]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∑ i : Fin N, ∑ a : Fin d, (2 * Real.pi * (k.1 a : ℝ) *
      Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ (X i)) ^ 2 ≤ N * (2 * Lattice.jp k.1 ^ 2) := by
    calc _ ≤ ∑ _i : Fin N, 2 * Lattice.jp k.1 ^ 2 :=
          Finset.sum_le_sum fun i _ => sum_sq_partial_le k (X i)
      _ = _ := by simp
  have hc : (w * Real.sqrt N * (N : ℝ)⁻¹) ^ 2 * N = w ^ 2 := by
    have : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
    calc (w * Real.sqrt N * (N : ℝ)⁻¹) ^ 2 * N = w ^ 2 * Real.sqrt N ^ 2 * ((N : ℝ)⁻¹) ^ 2 * N := by ring
      _ = w ^ 2 := by rw [this]; field_simp
  calc (w * Real.sqrt N * (N : ℝ)⁻¹) ^ 2 * _ ≤ (w * Real.sqrt N * (N : ℝ)⁻¹) ^ 2 * (N * (2 * Lattice.jp k.1 ^ 2)) := by
        gcongr
    _ = (w * Real.sqrt N * (N : ℝ)⁻¹) ^ 2 * N * (2 * Lattice.jp k.1 ^ 2) := by ring
    _ = _ := by rw [hc]; ring

theorem measurable_configGradSq_stF (N : ℕ) (w : ℝ) (k : NonzeroLattice d) :
    Measurable (configGradSq (stF N w (Torus.realMode k))) := by
  have : configGradSq (stF N w (Torus.realMode k)) = fun X : Config d N =>
      (w * Real.sqrt N * (N : ℝ)⁻¹) ^ 2 *
        ∑ i : Fin N, ∑ a : Fin d, (2 * Real.pi * (k.1 a : ℝ) *
          Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ (X i)) ^ 2 := by
    funext X; exact configGradSq_stF_realMode N w k X
  rw [this]
  refine Continuous.measurable ?_
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun a _ => ?_)
  exact (continuous_const.mul ((Torus.continuous_realMode _).comp (continuous_apply i))).pow 2

theorem isLZTest_stF (N : ℕ) (hN : 0 < N) (w : ℝ) (k : NonzeroLattice d) (μ : Measure (Config d N))
    [IsFiniteMeasure μ] : IsLZTest μ (stF N w (Torus.realMode k)) := by
  have hf := HRS.q38b_isSmooth_realMode (d := d) k
  have hc := continuous_stF N w (Torus.continuous_realMode k)
  refine ⟨hc.measurable, ?_, (contDiff_configLift_stF N w hf).contDiffOn, ?_⟩
  · refine MemLp.of_bound hc.aestronglyMeasurable (|w| * (Real.sqrt N * Real.sqrt 2))
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    exact abs_stF_le N w (Real.sqrt 2) (fun x => Torus.abs_realMode_le k x) (Real.sqrt_nonneg _) hN X
  · refine Integrable.mono' (integrable_const (2 * w ^ 2 * Lattice.jp k.1 ^ 2))
      (measurable_configGradSq_stF N w k).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact configGradSq_stF_le N hN w k X
    · unfold configGradSq
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem integral_configGradSq_stF_le (N : ℕ) (hN : 0 < N) (w : ℝ) (k : NonzeroLattice d)
    (μ : Measure (Config d N)) [IsProbabilityMeasure μ] :
    ∫ Y, configGradSq (stF N w (Torus.realMode k)) Y ∂μ ≤ 2 * w ^ 2 * Lattice.jp k.1 ^ 2 := by
  have hint := (isLZTest_stF N hN w k μ).energy
  calc ∫ Y, configGradSq (stF N w (Torus.realMode k)) Y ∂μ
      ≤ ∫ _Y, 2 * w ^ 2 * Lattice.jp k.1 ^ 2 ∂μ :=
        integral_mono hint (integrable_const _) fun Y => configGradSq_stF_le N hN w k Y
    _ = _ := by simp

end HRS.MD.EQStrong
