import HRS.MS.Fp81S21WickG13
import HRS.MC.E213U18e

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- The product kernel attached to a finite family of `L²` functions. -/
abbrev fp81s21_wickG_finite_rank_kernel
    {d m : ℕ} (u : Fin m → Euc d → ℝ)
    (c : Fin m → Fin m → ℝ) (z : Euc d × Euc d) : ℝ :=
  r2FiniteRankKernel c u z.1 z.2

/-- The centered half-Wick polynomial for a finite family of canonical `L²`
representatives. -/
abbrev fp81s21_wickG_finite_rank_polynomial
    {d m : ℕ} {μ : Measure (Euc d)} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ) (ω : Ω) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
    ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
      ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P)

/-- The finite-rank half-Wick polynomial for a bounded Gaussian `L²`
extension is centered and has the sharp `Kstar² / sqrt 2` bound in the
product-kernel norm. -/
theorem fp81s21_wickG_finite_rank_bound
    {d m : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ) :
    MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ) ∧
    MemLp (fp81s21_wickG_finite_rank_polynomial L u hu c) 2 P ∧
    (∫ ω, fp81s21_wickG_finite_rank_polynomial L u hu c ω ∂P) = 0 ∧
    (∫ ω, (fp81s21_wickG_finite_rank_polynomial L u hu c ω) ^ 2 ∂P ≤
      (1 / 2 : ℝ) * Kstar ^ 4 *
        ∫ z, (fp81s21_wickG_finite_rank_kernel u c z) ^ 2 ∂(μ.prod μ)) ∧
    ∃ hW : MemLp (fp81s21_wickG_finite_rank_polynomial L u hu c) 2 P,
      ∃ hk : MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ),
        ‖hW.toLp (fp81s21_wickG_finite_rank_polynomial L u hu c)‖ ≤
          Kstar ^ 2 / Real.sqrt 2 *
            ‖hk.toLp (fp81s21_wickG_finite_rank_kernel u c)‖ := by
  classical
  let f : Fin m → Lp ℝ 2 μ := fun i => (hu i).toLp (u i)
  let W : Ω → ℝ := fp81s21_wickG_finite_rank_polynomial L u hu c
  let k : Euc d × Euc d → ℝ := fp81s21_wickG_finite_rank_kernel u c
  obtain ⟨q, e, M, he, hdecompBasis, hkMem, _hKernelAE, hKernelInt⟩ :=
    fp81s21_wickG_kernel_orthonormal_coordinates u hu c
  have hdecomp : ∀ i, f i = ∑ a, M i a • e a := by
    intro i
    exact hdecompBasis i
  have hcoord := fp81s21_wickG_finite_coordinate_change
    L Kstar hL hJoint f e M he hdecomp c
  have hcoordBound := hcoord.2
  let d' : Fin q → Fin q → ℝ := fun a b =>
    ∑ i, ∑ j, c i j * M i a * M j b
  have hWmem : MemLp W 2 P := by
    let X : Ω → Fin m → ℝ := fun ω i => (L (f i)) ω
    have hXm : AEMeasurable X P := AEMeasurable.of_eval fun i =>
      (Lp.stronglyMeasurable (L (f i))).aestronglyMeasurable.aemeasurable
    have hXlaw : HasGaussianLaw X P := ⟨hXm, (hJoint m f).1⟩
    have hcoord4 : ∀ i, MemLp (fun ω => (L (f i)) ω) 4 P := by
      intro i
      let π : (Fin m → ℝ) →L[ℝ] ℝ :=
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i
      have heq : (fun ω => (L (f i)) ω) = fun ω => π (X ω) := by
        funext ω
        simp [X, π, ContinuousLinearMap.proj_apply]
      have hLaw : HasGaussianLaw (fun ω => (L (f i)) ω) P := by
        rw [heq]
        exact hXlaw.map_fun π
      exact hLaw.memLp (by norm_num)
    have hQmem : ∀ i j, MemLp (fun ω => (L (f i)) ω * (L (f j)) ω -
        ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P) 2 P := by
      intro i j
      have hp : MemLp (fun ω => (L (f i)) ω * (L (f j)) ω) 2 P :=
        HRS.MC.QRSpec.Wick.qrpw_memLp2_mul (hcoord4 i) (hcoord4 j)
      exact hp.sub (memLp_const _)
    have hrow : ∀ i, MemLp (fun ω => ∑ j, c i j *
        ((L (f i)) ω * (L (f j)) ω -
          ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P)) 2 P := by
      intro i
      exact memLp_finsetSum _ fun j _ => (hQmem i j).const_mul (c i j)
    have hsum : MemLp (fun ω => ∑ i, ∑ j, c i j *
        ((L (f i)) ω * (L (f j)) ω -
          ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P)) 2 P :=
      memLp_finsetSum _ fun i _ => hrow i
    have hW' : MemLp (fun ω => (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
        ((L (f i)) ω * (L (f j)) ω -
          ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P)) 2 P := hsum.const_mul _
    exact hW'
  have hWmemEq : MemLp (fp81s21_wickG_finite_rank_polynomial L u hu c) 2 P := by
    simpa [f, W, fp81s21_wickG_finite_rank_polynomial] using hWmem
  have hPairInt : ∀ i j, Integrable
      (fun ω => (L (f i)) ω * (L (f j)) ω) P := by
    intro i j
    exact (Lp.memLp (L (f i))).integrable_mul (Lp.memLp (L (f j)))
  have hCenteredInt : ∀ i j, Integrable
      (fun ω => (L (f i)) ω * (L (f j)) ω -
        ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P) P := by
    intro i j
    exact (hPairInt i j).sub (integrable_const _)
  have hCenteredMean : ∀ i j, ∫ ω, (L (f i)) ω * (L (f j)) ω -
      ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P ∂P = 0 := by
    intro i j
    rw [integral_sub (hPairInt i j) (integrable_const _)]
    simp [measure_univ]
  have hWmean : ∫ ω, W ω ∂P = 0 := by
    calc
      ∫ ω, W ω ∂P = (1 / 2 : ℝ) * ∫ ω, ∑ i, ∑ j, c i j *
          ((L (f i)) ω * (L (f j)) ω -
            ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P) ∂P := by
              dsimp [W, fp81s21_wickG_finite_rank_polynomial]
              rw [integral_const_mul]
      _ = (1 / 2 : ℝ) * ∑ i, ∫ ω, ∑ j, c i j *
          ((L (f i)) ω * (L (f j)) ω -
            ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P) ∂P := by
              rw [integral_finset_sum _ fun i _ =>
                integrable_finset_sum _ fun j _ => (hCenteredInt i j).const_mul (c i j)]
      _ = (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
          (∫ ω, ((L (f i)) ω * (L (f j)) ω -
            ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P) ∂P) := by
              apply congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
              apply Finset.sum_congr rfl
              intro i hi
              rw [integral_finset_sum _ fun j _ => (hCenteredInt i j).const_mul (c i j)]
              apply Finset.sum_congr rfl
              intro j hj
              rw [integral_const_mul]
      _ = 0 := by simp [hCenteredMean]
  have hboundW : ∫ ω, W ω ^ 2 ∂P ≤
      (1 / 2 : ℝ) * Kstar ^ 4 *
        ∫ z : Euc d × Euc d, k z ^ 2 ∂(μ.prod μ) := by
    dsimp [W, f, k, fp81s21_wickG_finite_rank_polynomial,
      fp81s21_wickG_finite_rank_kernel]
    calc
      ∫ ω, ((1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
          ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
            ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P)) ^ 2 ∂P ≤
        (1 / 2 : ℝ) * Kstar ^ 4 * ∑ a, ∑ b, d' a b ^ 2 := by
          simpa [f, d'] using hcoordBound
      _ = (1 / 2 : ℝ) * Kstar ^ 4 *
          ∫ z : Euc d × Euc d,
            (r2FiniteRankKernel c u z.1 z.2) ^ 2 ∂(μ.prod μ) := by
              rw [← hKernelInt]
  have hkMemKernel : MemLp (fp81s21_wickG_finite_rank_kernel u c)
      2 (μ.prod μ) := by
    exact hkMem
  have hWnormSq : ‖hWmemEq.toLp (fp81s21_wickG_finite_rank_polynomial L u hu c)‖ ^ 2 =
      ∫ ω, (fp81s21_wickG_finite_rank_polynomial L u hu c ω) ^ 2 ∂P := by
    calc
      ‖hWmemEq.toLp (fp81s21_wickG_finite_rank_polynomial L u hu c)‖ ^ 2 =
          inner ℝ (hWmemEq.toLp (fp81s21_wickG_finite_rank_polynomial L u hu c))
            (hWmemEq.toLp (fp81s21_wickG_finite_rank_polynomial L u hu c)) :=
              (real_inner_self_eq_norm_sq _).symm
      _ = ∫ ω, (fp81s21_wickG_finite_rank_polynomial L u hu c ω) ^ 2 ∂P := by
            rw [L2.inner_def]
            exact integral_congr_ae (hWmemEq.coeFn_toLp.mono fun ω hω => by
              simp [fp81s21_wickG_finite_rank_polynomial, hω]
              nlinarith [sq_abs (∑ i, ∑ j, c i j *
                ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
                  ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P))])
  have hKnormSq :
      ‖hkMemKernel.toLp (fp81s21_wickG_finite_rank_kernel u c)‖ ^ 2 =
        ∫ z : Euc d × Euc d,
          (fp81s21_wickG_finite_rank_kernel u c z) ^ 2 ∂(μ.prod μ) := by
    calc
      ‖hkMemKernel.toLp (fp81s21_wickG_finite_rank_kernel u c)‖ ^ 2 =
          inner ℝ (hkMemKernel.toLp (fp81s21_wickG_finite_rank_kernel u c))
            (hkMemKernel.toLp (fp81s21_wickG_finite_rank_kernel u c)) :=
              (real_inner_self_eq_norm_sq _).symm
      _ = ∫ z : Euc d × Euc d,
          (fp81s21_wickG_finite_rank_kernel u c z) ^ 2 ∂(μ.prod μ) := by
            rw [L2.inner_def]
            exact integral_congr_ae (hkMemKernel.coeFn_toLp.mono fun z hz => by
              simp [fp81s21_wickG_finite_rank_kernel, hz, sq_abs])
  have hWnormsq_le :
      ‖hWmemEq.toLp (fp81s21_wickG_finite_rank_polynomial L u hu c)‖ ^ 2 ≤
        (Kstar ^ 2 / Real.sqrt 2 *
          ‖hkMemKernel.toLp (fp81s21_wickG_finite_rank_kernel u c)‖) ^ 2 := by
    rw [hWnormSq]
    have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc
      ∫ ω, (fp81s21_wickG_finite_rank_polynomial L u hu c ω) ^ 2 ∂P ≤
          (1 / 2 : ℝ) * Kstar ^ 4 *
            ∫ z, (fp81s21_wickG_finite_rank_kernel u c z) ^ 2 ∂(μ.prod μ) := by
              simpa [W, k, fp81s21_wickG_finite_rank_polynomial,
                fp81s21_wickG_finite_rank_kernel] using hboundW
      _ = (Kstar ^ 2 / Real.sqrt 2 *
          ‖hkMemKernel.toLp (fp81s21_wickG_finite_rank_kernel u c)‖) ^ 2 := by
            calc
              (1 / 2 : ℝ) * Kstar ^ 4 *
                  ∫ z, (fp81s21_wickG_finite_rank_kernel u c z) ^ 2 ∂(μ.prod μ) =
                  (Kstar ^ 4 / 2) *
                    ∫ z, (fp81s21_wickG_finite_rank_kernel u c z) ^ 2 ∂(μ.prod μ) := by ring
              _ = (Kstar ^ 4 / 2) *
                  ‖hkMemKernel.toLp (fp81s21_wickG_finite_rank_kernel u c)‖ ^ 2 := by
                    rw [← hKnormSq]
              _ = (Kstar ^ 2 / Real.sqrt 2 *
                  ‖hkMemKernel.toLp (fp81s21_wickG_finite_rank_kernel u c)‖) ^ 2 := by
                    rw [mul_pow, div_pow, hs]
                    ring
  have hnorm :
      ‖hWmemEq.toLp (fp81s21_wickG_finite_rank_polynomial L u hu c)‖ ≤
        Kstar ^ 2 / Real.sqrt 2 *
          ‖hkMemKernel.toLp (fp81s21_wickG_finite_rank_kernel u c)‖ :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (by positivity) (norm_nonneg _))).1 hWnormsq_le
  refine ⟨hkMemKernel, hWmemEq, ?_, ?_, ⟨hWmemEq, hkMemKernel, hnorm⟩⟩
  · simpa [W, fp81s21_wickG_finite_rank_polynomial] using hWmean
  · simpa [W, k, fp81s21_wickG_finite_rank_polynomial,
      fp81s21_wickG_finite_rank_kernel] using hboundW

#print axioms fp81s21_wickG_finite_rank_bound

end HRS.Fp81.S21

end
