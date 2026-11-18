import HRS.MS.FinNoiseAux28

/-!
# S8.6 `finite_noise`: Hilbert-Schmidt norm of a composition between two Hilbert spaces (S86)

`s86_hs_comp_between`: for `A : G →L G` and `B : K →L G`, `∑_k ‖A B e_k‖² ≤ ‖B‖² ∑_i ‖A b_i‖²` (`e`, `b` Hilbert bases of
`K`, `G`), in `ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K G : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {ι κ : Type*} (e : HilbertBasis ι ℝ K) (b : HilbertBasis κ ℝ G)

theorem s86_hs_comp_between (A : G →L[ℝ] G) (B : K →L[ℝ] G) :
    ∑' k, ENNReal.ofReal (‖A (B (e k))‖ ^ 2) ≤
      ENNReal.ofReal (‖B‖ ^ 2) * ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2) := by
  have h1 : ∀ k, ENNReal.ofReal (‖A (B (e k))‖ ^ 2) =
      ∑' i, ENNReal.ofReal (inner ℝ (b i : G) (A (B (e k))) ^ 2) := fun k => by
    have := hasSum_inner_sq b (A (B (e k)))
    rw [← this.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) this.summable]
    refine tsum_congr fun i => ?_
    rw [real_inner_comm]
  have h2 : ∀ i, ∑' k, ENNReal.ofReal (inner ℝ (b i : G) (A (B (e k))) ^ 2) =
      ENNReal.ofReal (‖ContinuousLinearMap.adjoint B (ContinuousLinearMap.adjoint A (b i))‖ ^ 2) :=
    fun i => by
      have := hasSum_inner_sq e (ContinuousLinearMap.adjoint B (ContinuousLinearMap.adjoint A (b i)))
      rw [← this.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) this.summable]
      refine tsum_congr fun k => ?_
      rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  calc ∑' k, ENNReal.ofReal (‖A (B (e k))‖ ^ 2)
      = ∑' k, ∑' i, ENNReal.ofReal (inner ℝ (b i : G) (A (B (e k))) ^ 2) := tsum_congr h1
    _ = ∑' i, ∑' k, ENNReal.ofReal (inner ℝ (b i : G) (A (B (e k))) ^ 2) := ENNReal.tsum_comm
    _ = ∑' i, ENNReal.ofReal (‖ContinuousLinearMap.adjoint B (ContinuousLinearMap.adjoint A (b i))‖ ^ 2) :=
        tsum_congr h2
    _ ≤ ∑' i, ENNReal.ofReal (‖B‖ ^ 2) * ENNReal.ofReal (‖ContinuousLinearMap.adjoint A (b i)‖ ^ 2) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := (ContinuousLinearMap.adjoint B).le_opNorm (ContinuousLinearMap.adjoint A (b i))
        rw [ContinuousLinearMap.adjoint.norm_map] at this
        calc _ ≤ (‖B‖ * ‖ContinuousLinearMap.adjoint A (b i)‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) this 2
          _ = _ := by ring
    _ = ENNReal.ofReal (‖B‖ ^ 2) * ∑' i, ENNReal.ofReal (‖ContinuousLinearMap.adjoint A (b i)‖ ^ 2) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (‖B‖ ^ 2) * ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2) := by
        congr 1
        have h3 : ∀ i, ENNReal.ofReal (‖ContinuousLinearMap.adjoint A (b i)‖ ^ 2) =
            ∑' l, ENNReal.ofReal (inner ℝ (b l : G) (ContinuousLinearMap.adjoint A (b i)) ^ 2) := fun i => by
          have := hasSum_inner_sq b (ContinuousLinearMap.adjoint A (b i))
          rw [← this.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) this.summable]
          refine tsum_congr fun l => ?_
          rw [real_inner_comm]
        have h4 : ∀ l, ENNReal.ofReal (‖A (b l)‖ ^ 2) =
            ∑' i, ENNReal.ofReal (inner ℝ (b l : G) (ContinuousLinearMap.adjoint A (b i)) ^ 2) := fun l => by
          have := hasSum_inner_sq b (A (b l))
          rw [← this.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) this.summable]
          refine tsum_congr fun i => ?_
          rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
        simp_rw [h3, h4]
        exact ENNReal.tsum_comm

end HRS.MS.FinNoise
