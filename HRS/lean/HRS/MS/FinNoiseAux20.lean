import HRS.MS.FinNoiseAux19

/-!
# S8.6 `finite_noise`: Hilbert-Schmidt calculus on a separable Hilbert space (S86, for Araki-Yamagami)

Along a fixed Hilbert basis `e` of `K` (operators `K →L K`), `hs2 A = ∑_j ‖A e_j‖²` in `ℝ≥0∞`:
* `s86_hs2_adjoint`: `hs2 A = hs2 A†`;
* `s86_hs2_comp_right`: `hs2 (A ∘ B) ≤ ‖B‖² hs2 A`;
* `s86_trace_cyclic`: `∑_j ⟨B C e_j, e_j⟩ = ∑_j ⟨C B e_j, e_j⟩` for Hilbert-Schmidt `B, C`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  {ι : Type*} (e : HilbertBasis ι ℝ K)

/-- The Hilbert-Schmidt norm squared along `e`, in `ℝ≥0∞`. -/
def hs2 (A : K →L[ℝ] K) : ℝ≥0∞ := ∑' j, ENNReal.ofReal (‖A (e j)‖ ^ 2)

theorem s86_hs2_adjoint (A : K →L[ℝ] K) : hs2 e A = hs2 e (ContinuousLinearMap.adjoint A) := by
  have h1 : ∀ j, ENNReal.ofReal (‖A (e j)‖ ^ 2) =
      ∑' k, ENNReal.ofReal (inner ℝ (e k : K) (A (e j)) ^ 2) := fun j => by
    have := hasSum_inner_sq e (A (e j))
    rw [← this.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) this.summable]
    refine tsum_congr fun k => ?_
    rw [real_inner_comm]
  have h2 : ∀ k, ENNReal.ofReal (‖ContinuousLinearMap.adjoint A (e k)‖ ^ 2) =
      ∑' j, ENNReal.ofReal (inner ℝ (e k : K) (A (e j)) ^ 2) := fun k => by
    have := hasSum_inner_sq e (ContinuousLinearMap.adjoint A (e k))
    rw [← this.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) this.summable]
    refine tsum_congr fun j => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  unfold hs2
  simp_rw [h1, h2]
  exact ENNReal.tsum_comm

theorem s86_hs2_comp_left (A B : K →L[ℝ] K) : hs2 e (B.comp A) ≤ ENNReal.ofReal (‖B‖ ^ 2) * hs2 e A := by
  unfold hs2
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := B.le_opNorm (A (e j))
  calc ‖(B.comp A) (e j)‖ ^ 2 ≤ (‖B‖ * ‖A (e j)‖) ^ 2 := by
        simpa using pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = ‖B‖ ^ 2 * ‖A (e j)‖ ^ 2 := by ring

theorem s86_hs2_comp_right (A B : K →L[ℝ] K) : hs2 e (A.comp B) ≤ ENNReal.ofReal (‖B‖ ^ 2) * hs2 e A := by
  have h1 : (A.comp B) = ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint B |>.comp
      (ContinuousLinearMap.adjoint A)) := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  rw [h1, ← s86_hs2_adjoint]
  refine (s86_hs2_comp_left e _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map, s86_hs2_adjoint e A]

theorem s86_hs2_summable {A : K →L[ℝ] K} (hA : hs2 e A ≠ ⊤) :
    Summable fun j => ‖A (e j)‖ ^ 2 := by
  have := ENNReal.summable_toReal hA
  refine this.congr fun j => ?_
  rw [ENNReal.toReal_ofReal (by positivity)]

theorem s86_hs2_ne_top_of_summable {A : K →L[ℝ] K} (hA : Summable fun j => ‖A (e j)‖ ^ 2) :
    hs2 e A ≠ ⊤ := by
  unfold hs2
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hA]
  exact ENNReal.ofReal_ne_top

theorem s86_trace_cyclic (B C : K →L[ℝ] K) (hB : hs2 e B ≠ ⊤) (hC : hs2 e C ≠ ⊤) :
    ∑' j, inner ℝ (B (C (e j))) (e j : K) = ∑' j, inner ℝ (C (B (e j))) (e j : K) := by
  have hBs := s86_hs2_summable e hB
  have hCs := s86_hs2_summable e hC
  set f : ι × ι → ℝ := fun p => inner ℝ (C (e p.1)) (e p.2 : K) * inner ℝ (B (e p.2)) (e p.1 : K)
    with hf
  have hrow : ∀ j, HasSum (fun k => f (j, k)) (inner ℝ (B (C (e j))) (e j : K)) := fun j => by
    have := e.hasSum_inner_mul_inner (C (e j)) (ContinuousLinearMap.adjoint B (e j))
    rw [ContinuousLinearMap.adjoint_inner_right] at this
    convert this using 2 with k
    simp only [hf, ContinuousLinearMap.adjoint_inner_right]
  have hcol : ∀ k, HasSum (fun j => f (j, k)) (inner ℝ (C (B (e k))) (e k : K)) := fun k => by
    have := e.hasSum_inner_mul_inner (B (e k)) (ContinuousLinearMap.adjoint C (e k))
    rw [ContinuousLinearMap.adjoint_inner_right] at this
    convert this using 2 with j
    simp only [hf, ContinuousLinearMap.adjoint_inner_right]
    ring
  have hsq : ∀ (A : K →L[ℝ] K), Summable (fun j => ‖A (e j)‖ ^ 2) →
      Summable (fun p : ι × ι => inner ℝ (A (e p.1)) (e p.2 : K) ^ 2) := fun A hA => by
    refine (summable_prod_of_nonneg (fun p => sq_nonneg _)).2 ⟨fun j => ?_, ?_⟩
    · exact (hasSum_inner_sq e (A (e j))).summable
    · exact hA.congr fun j => ((hasSum_inner_sq e (A (e j))).tsum_eq).symm
  have hs1 := hsq C hCs
  have hs2' : Summable (fun p : ι × ι => inner ℝ (B (e p.1)) (e p.2 : K) ^ 2) := hsq B hBs
  have hs2'' : Summable (fun p : ι × ι => inner ℝ (B (e p.2)) (e p.1 : K) ^ 2) :=
    (Equiv.prodComm ι ι).summable_iff.2 hs2'
  have hfs : Summable f := by
    refine Summable.of_norm_bounded ((hs1.add hs2'').mul_left (1 / 2 : ℝ)) (fun p => ?_)
    rw [Real.norm_eq_abs, hf]
    simp only
    rw [abs_mul]
    nlinarith [sq_abs (inner ℝ (C (e p.1)) (e p.2 : K)), sq_abs (inner ℝ (B (e p.2)) (e p.1 : K)),
      sq_nonneg (|inner ℝ (C (e p.1)) (e p.2 : K)| - |inner ℝ (B (e p.2)) (e p.1 : K)|),
      abs_nonneg (inner ℝ (C (e p.1)) (e p.2 : K)), abs_nonneg (inner ℝ (B (e p.2)) (e p.1 : K))]
  calc ∑' j, inner ℝ (B (C (e j))) (e j : K) = ∑' j, ∑' k, f (j, k) :=
        tsum_congr fun j => (hrow j).tsum_eq.symm
    _ = ∑' k, ∑' j, f (j, k) := (hfs.tsum_comm' (fun j => (hrow j).summable)
          (fun k => (hcol k).summable)).symm
    _ = ∑' k, inner ℝ (C (B (e k))) (e k : K) := tsum_congr fun k => (hcol k).tsum_eq

end HRS.MS.FinNoise
