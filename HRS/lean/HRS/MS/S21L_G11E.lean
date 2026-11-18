import HRS.Prob.HilbertCLT
import HRS.MS.R2ChaosAux13

/-!
# S21L G11E -- Hilbert-valued Wick sections: Parseval in expectation and the isometry bound (R26-T3.G11, fifth step)

For a Hilbert space `B` with a Hilbert basis `b` and a family `z` of jointly Gaussian coordinates (`S94GSeq`, covariance
bounded by `Λ`), the vector Wick section `S = ∑_{i,j<n} (z_i z_j - E z_i z_j) • C_ij` (symmetric `C_ij ∈ B`) lies in `L²(P;B)`
and `E ‖S‖² ≤ 2 Λ² ∑_{i,j<n} ‖C_ij‖²` (`s21l_vec_isometry`), by Parseval in expectation along `b`
(`s21l_hasSum_sq`) and the scalar isometry `s94_sec_diff_le`.  Prefix `s21l_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.deprecated false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS.MS.R2Chaos HRS.Whole

section Vec

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem s21l_hasSum_sq {ι : Type*} (b : HilbertBasis ι ℝ B) {X : Ω → B} (hX : MemLp X 2 P) :
    HasSum (fun i => ∫ ω, (inner ℝ (b i) (X ω)) ^ 2 ∂P) (∫ ω, ‖X ω‖ ^ 2 ∂P) := by
  have hint := fun i => HilbertCLTAux.integrable_inner_sq P hX (b i)
  have hnorm := HilbertCLTAux.integrable_sq_norm_of_memLp2 hX
  have hsum : Summable (fun i => ∫ ω, (inner ℝ (b i) (X ω)) ^ 2 ∂P) := by
    refine summable_of_sum_le (c := ∫ ω, ‖X ω‖ ^ 2 ∂P) (fun i => integral_nonneg fun ω => sq_nonneg _)
      (fun F => ?_)
    rw [← integral_finsetSum _ (fun i _ => hint i)]
    refine integral_mono (integrable_finsetSum _ fun i _ => hint i) hnorm (fun ω => ?_)
    have := b.orthonormal.sum_inner_products_le (X ω) (s := F)
    simpa [real_inner_comm] using this
  have habs : Summable (fun i => ∫ ω, ‖(inner ℝ (b i) (X ω)) ^ 2‖ ∂P) := by
    simpa [Real.norm_of_nonneg (sq_nonneg _)] using hsum
  have : Countable ι := HilbertCLTAux.countable_of_orthonormal b.orthonormal
  have := integral_tsum_of_summable_integral_norm hint habs
  have hpt : ∀ ω, ∑' i, (inner ℝ (b i) (X ω)) ^ 2 = ‖X ω‖ ^ 2 := by
    intro ω
    have := b.tsum_inner_mul_inner (X ω) (X ω)
    simp only [real_inner_self_eq_norm_sq] at this
    rw [← this]
    refine tsum_congr fun i => ?_
    rw [real_inner_comm]; ring
  simp_rw [hpt] at this
  rw [← this]
  exact hsum.hasSum

theorem s21l_hasSum_norm_sq {ι : Type*} (b : HilbertBasis ι ℝ B) (x : B) :
    HasSum (fun i => (inner ℝ (b i) x) ^ 2) (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 1
  funext i
  have := real_inner_comm (b i) x
  rw [this, sq]

theorem s21l_vec_isometry {z : ℕ → Ω → ℝ} {Λ : ℝ} (hz : S94GSeq P z Λ) (hΛ0 : 0 ≤ Λ) {C : ℕ → ℕ → B}
    (hC : ∀ i j, C i j = C j i) (n : ℕ) :
    MemLp (fun ω => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • C i j) 2 P ∧
    ∫ ω, ‖∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • C i j‖ ^ 2 ∂P ≤
        2 * Λ ^ 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ‖C i j‖ ^ 2 := by
  have hzz : ∀ i j, MemLp (fun ζ => z i ζ * z j ζ) 2 P := fun i j => by
    have hi' : i < max (i + 1) (j + 1) := lt_max_of_lt_left (Nat.lt_succ_self i)
    have hj' : j < max (i + 1) (j + 1) := lt_max_of_lt_right (Nat.lt_succ_self j)
    exact (hz (max (i + 1) (j + 1))).1.memLp_zz ⟨i, hi'⟩ ⟨j, hj'⟩
  have hw : ∀ i j, MemLp (fun ω => z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) 2 P := fun i j =>
    (hzz i j).sub (memLp_const _)
  have hterm : ∀ i j, MemLp (fun ω => (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • C i j) 2 P := fun i j => by
    have := ((ContinuousLinearMap.id ℝ ℝ).smulRight (C i j)).comp_memLp' (hw i j)
    exact this.ae_eq (Filter.Eventually.of_forall fun ω => by simp)
  have hS : MemLp (fun ω => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • C i j) 2 P :=
    memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => hterm i j
  refine ⟨hS, ?_⟩
  obtain ⟨ι, hι, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := B)
  have hP := s21l_hasSum_sq b hS
  -- coordinates are scalar Wick sections
  have hcoord : ∀ s ω, inner ℝ (b s) (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • C i j) =
      s94Sec P z (fun p q => inner ℝ (b s) (C p q)) n ω := by
    intro s ω
    unfold s94Sec
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right]
    ring
  have hbound : ∀ s, ∫ ω, (inner ℝ (b s) (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • C i j)) ^ 2 ∂P ≤
      2 * Λ ^ 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (inner ℝ (b s) (C i j)) ^ 2 := by
    intro s
    simp_rw [hcoord s]
    have hA : ∀ p q, inner ℝ (b s) (C p q) = inner ℝ (b s) (C q p) := fun p q => by rw [hC p q]
    have h0 := s94_sec_diff_le hz hΛ0 (A := fun p q => inner ℝ (b s) (C p q)) hA (Nat.zero_le n)
    have e0 : s94Sec P z (fun p q => inner ℝ (b s) (C p q)) 0 = fun _ => 0 := by
      funext ζ; simp [s94Sec]
    rw [e0] at h0
    simp only [sub_zero] at h0
    have eT : s94T (fun p q => inner ℝ (b s) (C p q)) 0 = 0 := by simp [s94T]
    rw [eT, sub_zero] at h0
    exact h0
  have hG : HasSum (fun s => 2 * Λ ^ 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (inner ℝ (b s) (C i j)) ^ 2)
      (2 * Λ ^ 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ‖C i j‖ ^ 2) := by
    refine HasSum.mul_left _ ?_
    refine hasSum_sum fun i _ => ?_
    refine hasSum_sum fun j _ => ?_
    exact s21l_hasSum_norm_sq b (C i j)
  exact hasSum_le hbound hP hG

end Vec

end HRS.MS.R26T3
