import HRS.MS.Fp81S21WickB22
import HRS.MS.PROS13SeparatedB

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- The product-space coordinate swap on `L²(μ ⊗ μ)`, induced by the
measure-preserving map `Prod.swap`. -/
def fp81s21_wickB23_swapLp {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    Lp ℝ 2 (μ.prod μ) →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod μ) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.swap
    (Measure.measurePreserving_swap (μ := μ) (ν := μ))

/-- The full-domain contractive symmetrization `S k = (k + k ∘ swap) / 2` on
product `L²`. -/
def fp81s21_wickB23_symmetrize {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 (μ.prod μ) :=
  (1 / 2 : ℝ) •
    (ContinuousLinearMap.id ℝ (Lp ℝ 2 (μ.prod μ)) +
      (fp81s21_wickB23_swapLp μ).toContinuousLinearMap)

theorem fp81s21_wickB23_symmetrize_apply {d : ℕ}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (k : Lp ℝ 2 (μ.prod μ)) :
    fp81s21_wickB23_symmetrize μ k =
      (1 / 2 : ℝ) • (k + fp81s21_wickB23_swapLp μ k) := rfl

theorem fp81s21_wickB23_swapLp_ae {d : ℕ}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (k : Lp ℝ 2 (μ.prod μ)) :
    (fp81s21_wickB23_swapLp μ k : Euc d × Euc d → ℝ) =ᵐ[μ.prod μ]
      fun z => k z.swap := by
  exact Lp.coeFn_compMeasurePreserving k
    (Measure.measurePreserving_swap (μ := μ) (ν := μ))

private theorem fp81s21_wickB23_swapLp_involutive {d : ℕ}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (k : Lp ℝ 2 (μ.prod μ)) :
    fp81s21_wickB23_swapLp μ (fp81s21_wickB23_swapLp μ k) = k := by
  apply Lp.ext
  let hmp : MeasurePreserving (Prod.swap : Euc d × Euc d → Euc d × Euc d)
      (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have h1 := fp81s21_wickB23_swapLp_ae μ (fp81s21_wickB23_swapLp μ k)
  have h2 := fp81s21_wickB23_swapLp_ae μ k
  have h2c := hmp.quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h2c] with z hz1 hz2
  simpa only [Function.comp_apply, Prod.swap_swap] using hz1.trans hz2

theorem fp81s21_wickB23_symmetrize_contracting {d : ℕ}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (k : Lp ℝ 2 (μ.prod μ)) :
    ‖fp81s21_wickB23_symmetrize μ k‖ ≤ ‖k‖ := by
  rw [fp81s21_wickB23_symmetrize_apply]
  have hswap : ‖fp81s21_wickB23_swapLp μ k‖ = ‖k‖ :=
    (fp81s21_wickB23_swapLp μ).norm_map k
  calc
    ‖(1 / 2 : ℝ) • (k + fp81s21_wickB23_swapLp μ k)‖ =
        (1 / 2 : ℝ) * ‖k + fp81s21_wickB23_swapLp μ k‖ := by
          rw [norm_smul]
          norm_num
    _ ≤ (1 / 2 : ℝ) * (‖k‖ + ‖fp81s21_wickB23_swapLp μ k‖) := by
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖k‖ := by rw [hswap]; ring

theorem fp81s21_wickB23_symmetrize_idempotent {d : ℕ}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (k : Lp ℝ 2 (μ.prod μ)) :
    fp81s21_wickB23_symmetrize μ (fp81s21_wickB23_symmetrize μ k) =
      fp81s21_wickB23_symmetrize μ k := by
  calc
    fp81s21_wickB23_symmetrize μ (fp81s21_wickB23_symmetrize μ k) =
        (1 / 2 : ℝ) •
          (fp81s21_wickB23_symmetrize μ k +
            fp81s21_wickB23_swapLp μ (fp81s21_wickB23_symmetrize μ k)) :=
      fp81s21_wickB23_symmetrize_apply μ _
    _ = (1 / 2 : ℝ) • (k + fp81s21_wickB23_swapLp μ k) := by
      rw [fp81s21_wickB23_symmetrize_apply,
        map_smul, map_add, fp81s21_wickB23_swapLp_involutive]
      module
    _ = fp81s21_wickB23_symmetrize μ k :=
      (fp81s21_wickB23_symmetrize_apply μ k).symm

theorem fp81s21_wickB23_symmetrize_antisymmetric_zero {d : ℕ}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (k : Lp ℝ 2 (μ.prod μ))
    (hanti : fp81s21_wickB23_swapLp μ k = -k) :
    fp81s21_wickB23_symmetrize μ k = 0 := by
  rw [fp81s21_wickB23_symmetrize_apply, hanti]
  simp

/-- Symmetric coefficient matrix associated to an arbitrary finite-rank
kernel. -/
def fp81s21_wickB23_symmCoeff {m : ℕ}
    (c : Fin m → Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => (c i j + c j i) / 2

theorem fp81s21_wickB23_kernel_symmCoeff {d m : ℕ}
    (u : Fin m → Euc d → ℝ) (c : Fin m → Fin m → ℝ)
    (x y : Euc d) :
    r2FiniteRankKernel (fp81s21_wickB23_symmCoeff c) u x y =
      (r2FiniteRankKernel c u x y + r2FiniteRankKernel c u y x) / 2 := by
  classical
  have hswap :
      (∑ i, ∑ j, c j i * u i x * u j y) =
        ∑ i, ∑ j, c i j * u i y * u j x := by
    calc
      _ = ∑ j, ∑ i, c j i * u i x * u j y := Finset.sum_comm
      _ = ∑ j, ∑ i, c j i * u j y * u i x := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, ∑ j, c i j * u i y * u j x := rfl
  change (∑ i, ∑ j, ((c i j + c j i) / 2) * u i x * u j y) =
    (∑ i, ∑ j, c i j * u i x * u j y +
      ∑ i, ∑ j, c i j * u i y * u j x) / 2
  calc
    _ = ∑ i, ∑ j, ((1 / 2 : ℝ) * c i j * u i x * u j y +
        (1 / 2 : ℝ) * c j i * u i x * u j y) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (1 / 2 : ℝ) *
        (∑ i, ∑ j, c i j * u i x * u j y +
          ∑ i, ∑ j, c j i * u i x * u j y) := by
          have hA :
              (∑ i : Fin m, ∑ j : Fin m,
                (1 / 2 : ℝ) * (c i j * u i x * u j y)) =
                (1 / 2 : ℝ) * (∑ i, ∑ j, c i j * u i x * u j y) := by
            calc
              _ = ∑ i, ∑ j, (1 / 2 : ℝ) *
                  (c i j * u i x * u j y) := rfl
              _ = _ := by simp only [← Finset.mul_sum]
          have hB :
              (∑ i : Fin m, ∑ j : Fin m,
                (1 / 2 : ℝ) * (c j i * u i x * u j y)) =
                (1 / 2 : ℝ) * (∑ i, ∑ j, c j i * u i x * u j y) := by
            calc
              _ = ∑ i, ∑ j, (1 / 2 : ℝ) *
                  (c j i * u i x * u j y) := rfl
              _ = _ := by simp only [← Finset.mul_sum]
          calc
            _ = (∑ i, ∑ j, (1 / 2 : ℝ) *
                  (c i j * u i x * u j y)) +
                (∑ i, ∑ j, (1 / 2 : ℝ) *
                  (c j i * u i x * u j y)) := by
                    simp only [Finset.sum_add_distrib]
                    apply congrArg₂ (fun a b : ℝ => a + b)
                    · apply Finset.sum_congr rfl
                      intro i hi
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
                    · apply Finset.sum_congr rfl
                      intro i hi
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
            _ = _ := by rw [hA, hB]; ring
    _ = _ := by rw [hswap]; ring

/-- `S` sends a finite-rank product kernel to the kernel with the symmetrized
coefficient matrix. Both `MemLp` witnesses are explicit so this statement
applies to arbitrary `L²` input families. -/
theorem fp81s21_wickB23_symmetrize_finite_rank
    {d m : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ)
    (hk : MemLp (fun z : Euc d × Euc d => r2FiniteRankKernel c u z.1 z.2)
      2 (μ.prod μ))
    (hs : MemLp (fun z : Euc d × Euc d =>
      r2FiniteRankKernel (fp81s21_wickB23_symmCoeff c) u z.1 z.2)
      2 (μ.prod μ)) :
    fp81s21_wickB23_symmetrize μ
        (hk.toLp (fun z => r2FiniteRankKernel c u z.1 z.2)) =
      hs.toLp (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (fp81s21_wickB23_symmCoeff c) u z.1 z.2) := by
  apply Lp.ext
  let f : Euc d × Euc d → ℝ := fun z => r2FiniteRankKernel c u z.1 z.2
  let fs : Euc d × Euc d → ℝ := fun z =>
    r2FiniteRankKernel (fp81s21_wickB23_symmCoeff c) u z.1 z.2
  let k := hk.toLp f
  have hmp : MeasurePreserving (Prod.swap : Euc d × Euc d → Euc d × Euc d)
      (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hswap := fp81s21_wickB23_swapLp_ae μ k
  have hadd := Lp.coeFn_add k (fp81s21_wickB23_swapLp μ k)
  have hsmul := Lp.coeFn_smul (1 / 2 : ℝ)
    (k + fp81s21_wickB23_swapLp μ k)
  have hkernel := hk.coeFn_toLp
  have hkernelComp := hmp.quasiMeasurePreserving.ae_eq_comp hkernel
  have hsym := hs.coeFn_toLp
  filter_upwards [hswap, hadd, hsmul, hkernel, hkernelComp, hsym]
      with z hswap' hadd' hsmul' hk' hkComp hs'
  change ((1 / 2 : ℝ) •
      (k + fp81s21_wickB23_swapLp μ k)) z =
    hs.toLp (fun z : Euc d × Euc d =>
      r2FiniteRankKernel (fp81s21_wickB23_symmCoeff c) u z.1 z.2) z
  rw [hsmul']
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hadd']
  simp only [Pi.add_apply]
  rw [hswap', hk']
  have hkComp' : k z.swap = f z.swap := by
    simpa [Function.comp_apply, k, f] using hkComp
  rw [hkComp', hs']
  rw [fp81s21_wickB23_kernel_symmCoeff]
  simp only [f, Prod.swap]
  ring

/-- The exact symmetric finite-rank density theorem available in the branch:
the input function is pointwise symmetric, square-integrable on `μ ⊗ μ`, and
`μ` is any probability measure on `Euc d`. It returns symmetric coefficient
data with the stated `eLpNorm` error. This is the form used after choosing a
symmetric representative in the range of `S`. -/
theorem fp81s21_wickB23_symmetric_finite_rank_approx
    {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2)
      2 (μ.prod μ))
    (hsym : ∀ x y, h x y = h y x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ),
      IsR2FiniteRankData c u ∧
      eLpNorm (fun z : Euc d × Euc d =>
        r2FiniteRankKernel c u z.1 z.2 - h z.1 z.2)
        2 (μ.prod μ) ≤ ENNReal.ofReal ε :=
  HRS.MS.R26T3.pro_s13_generic_separated_approx μ h hh hsym ε hε

#print axioms fp81s21_wickB23_swapLp_ae
#print axioms fp81s21_wickB23_symmetrize_contracting
#print axioms fp81s21_wickB23_symmetrize_idempotent
#print axioms fp81s21_wickB23_symmetrize_antisymmetric_zero
#print axioms fp81s21_wickB23_symmetrize_finite_rank
#print axioms fp81s21_wickB23_symmetric_finite_rank_approx

end HRS.Fp81.S21

end
