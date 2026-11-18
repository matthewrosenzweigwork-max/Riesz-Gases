import HRS.MS.FinNoiseAux21

/-!
# S8.6 `finite_noise`: positivity of the Hilbert-Schmidt pairing of positive operators (S86)

`s86_pair_nonneg`: for symmetric nonnegative Hilbert-Schmidt `S, Z`, `∑_j ⟨S e_j, Z e_j⟩ ≥ 0`.
Route: basis independence of the pairing (polarisation of `s86_hs2_basis`), eigenbasis of `S + ε B₀`
(`B₀` a positive injective diagonal Hilbert-Schmidt operator; `s8p_compact_selfadjoint_basis`), termwise positivity,
`ε → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- The Hilbert-Schmidt pairing along `e`. -/
def hsPair {ι : Type*} (e : HilbertBasis ι ℝ K) (A B : K →L[ℝ] K) : ℝ :=
  ∑' j, inner ℝ (A (e j)) (B (e j))

theorem s86_hsR_basis {ι κ : Type*} (b : HilbertBasis ι ℝ K) (e : HilbertBasis κ ℝ K)
    (A : K →L[ℝ] K) (hA : Summable fun j => ‖A (e j)‖ ^ 2) :
    Summable (fun j => ‖A (b j)‖ ^ 2) ∧ ∑' j, ‖A (b j)‖ ^ 2 = ∑' k, ‖A (e k)‖ ^ 2 := by
  have hA' := s86_hs2_ne_top_of_summable e hA
  have h := s86_hs2_basis b e A
  have hb : hs2 b A ≠ ⊤ := by rw [h]; exact hA'
  refine ⟨s86_hs2_summable b hb, ?_⟩
  have h1 : hs2 b A = ENNReal.ofReal (∑' j, ‖A (b j)‖ ^ 2) := by
    unfold hs2
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (s86_hs2_summable b hb)]
  have h2 : hs2 e A = ENNReal.ofReal (∑' j, ‖A (e j)‖ ^ 2) := by
    unfold hs2
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hA]
  rw [h1, h2] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun _ => sq_nonneg _)
    (tsum_nonneg fun _ => sq_nonneg _)).1 h

theorem s86_hs_add_summable {ι : Type*} (e : HilbertBasis ι ℝ K) {A B : K →L[ℝ] K}
    (hA : Summable fun j => ‖A (e j)‖ ^ 2) (hB : Summable fun j => ‖B (e j)‖ ^ 2) :
    Summable fun j => ‖(A + B) (e j)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => ?_) ((hA.add hB).mul_left 2)
  simp only [add_apply]
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (A (e j)) (B (e j))) 2,
    sq_nonneg (‖A (e j)‖ - ‖B (e j)‖)]

theorem s86_hs_sub_summable {ι : Type*} (e : HilbertBasis ι ℝ K) {A B : K →L[ℝ] K}
    (hA : Summable fun j => ‖A (e j)‖ ^ 2) (hB : Summable fun j => ‖B (e j)‖ ^ 2) :
    Summable fun j => ‖(A - B) (e j)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => ?_) ((hA.add hB).mul_left 2)
  simp only [sub_apply]
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (A (e j)) (B (e j))) 2,
    sq_nonneg (‖A (e j)‖ - ‖B (e j)‖)]

theorem s86_hsPair_formula {ι : Type*} (e : HilbertBasis ι ℝ K) {A B : K →L[ℝ] K}
    (hA : Summable fun j => ‖A (e j)‖ ^ 2) (hB : Summable fun j => ‖B (e j)‖ ^ 2) :
    Summable (fun j => inner ℝ (A (e j)) (B (e j))) ∧
    hsPair e A B = ((∑' j, ‖(A + B) (e j)‖ ^ 2) - ∑' j, ‖(A - B) (e j)‖ ^ 2) / 4 := by
  have hp := s86_hs_add_summable e hA hB
  have hm := s86_hs_sub_summable e hA hB
  have key : ∀ j, inner ℝ (A (e j)) (B (e j)) =
      (‖(A + B) (e j)‖ ^ 2 - ‖(A - B) (e j)‖ ^ 2) / 4 := fun j => by
    simp only [add_apply, sub_apply]
    rw [norm_add_sq_real, norm_sub_sq_real]
    ring
  refine ⟨?_, ?_⟩
  · simp_rw [key]; exact (hp.sub hm).div_const 4
  · unfold hsPair
    simp_rw [key]
    rw [tsum_div_const, hp.tsum_sub hm]

theorem s86_hsPair_basis {ι κ : Type*} (b : HilbertBasis ι ℝ K) (e : HilbertBasis κ ℝ K)
    {A B : K →L[ℝ] K} (hA : Summable fun j => ‖A (e j)‖ ^ 2) (hB : Summable fun j => ‖B (e j)‖ ^ 2) :
    Summable (fun j => inner ℝ (A (b j)) (B (b j))) ∧ hsPair b A B = hsPair e A B := by
  have hAb := s86_hsR_basis b e A hA
  have hBb := s86_hsR_basis b e B hB
  have hp := s86_hsR_basis b e (A + B) (s86_hs_add_summable e hA hB)
  have hm := s86_hsR_basis b e (A - B) (s86_hs_sub_summable e hA hB)
  obtain ⟨s1, f1⟩ := s86_hsPair_formula b hAb.1 hBb.1
  obtain ⟨-, f2⟩ := s86_hsPair_formula e hA hB
  exact ⟨s1, by rw [f1, f2, hp.2, hm.2]⟩

end HRS.MS.FinNoise
