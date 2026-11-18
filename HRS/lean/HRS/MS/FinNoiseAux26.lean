import HRS.MS.FinNoiseAux25

/-!
# S8.6 `finite_noise`: the key inequality of Araki-Yamagami (S86)

For symmetric nonnegative Hilbert-Schmidt `S, S'` and a contraction `W`:
`4 ∑_j ⟨S e_j, W S' e_j⟩ ≤ ‖S‖²_HS + ‖S'‖²_HS + 2 ∑_j ⟨S e_j, S' e_j⟩` (`s86_key_ineq`).
Proof: `0 ≤ ⟨S, (1-W) S' (1-W)†⟩_HS` (`s86_pair_nonneg`), cyclicity of the trace, and AM-GM.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  {ι : Type*} (e : HilbertBasis ι ℝ K)

theorem s86_hsS_comp_left {A : K →L[ℝ] K} (hA : Summable fun j => ‖A (e j)‖ ^ 2) (B : K →L[ℝ] K) :
    Summable fun j => ‖(B.comp A) (e j)‖ ^ 2 := by
  have := s86_hs2_comp_left e A B
  have h1 := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (s86_hs2_ne_top_of_summable e hA)) this
  exact s86_hs2_summable e h1

theorem s86_hsS_comp_right {A : K →L[ℝ] K} (hA : Summable fun j => ‖A (e j)‖ ^ 2) (B : K →L[ℝ] K) :
    Summable fun j => ‖(A.comp B) (e j)‖ ^ 2 := by
  have := s86_hs2_comp_right e A B
  have h1 := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (s86_hs2_ne_top_of_summable e hA)) this
  exact s86_hs2_summable e h1

theorem s86_hsS_sum_le {A : K →L[ℝ] K} (hA : Summable fun j => ‖A (e j)‖ ^ 2) (B : K →L[ℝ] K)
    (hB : ‖B‖ ≤ 1) : ∑' j, ‖(B.comp A) (e j)‖ ^ 2 ≤ ∑' j, ‖A (e j)‖ ^ 2 := by
  refine Summable.tsum_le_tsum (fun j => ?_) (s86_hsS_comp_left e hA B) hA
  have := B.le_opNorm (A (e j))
  calc ‖(B.comp A) (e j)‖ ^ 2 ≤ (‖B‖ * ‖A (e j)‖) ^ 2 := by
        simpa using pow_le_pow_left₀ (norm_nonneg _) this 2
    _ ≤ ‖A (e j)‖ ^ 2 := by
        have h1 := norm_nonneg (A (e j))
        have h2 : ‖B‖ * ‖A (e j)‖ ≤ ‖A (e j)‖ := by nlinarith [mul_le_mul_of_nonneg_right hB h1]
        exact pow_le_pow_left₀ (by positivity) h2 2

theorem s86_hsS_sum_le_right {A : K →L[ℝ] K} (hA : Summable fun j => ‖A (e j)‖ ^ 2) (B : K →L[ℝ] K)
    (hB : ‖B‖ ≤ 1) : ∑' j, ‖(A.comp B) (e j)‖ ^ 2 ≤ ∑' j, ‖A (e j)‖ ^ 2 := by
  have h1 := s86_hs2_comp_right e A B
  have hf : hs2 e (A.comp B) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (s86_hs2_ne_top_of_summable e hA)) h1
  have hAt : hs2 e A = ENNReal.ofReal (∑' j, ‖A (e j)‖ ^ 2) := by
    unfold hs2; rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hA]
  have hBt : hs2 e (A.comp B) = ENNReal.ofReal (∑' j, ‖(A.comp B) (e j)‖ ^ 2) := by
    unfold hs2; rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (s86_hs2_summable e hf)]
  rw [hBt, hAt] at h1
  have hB2 : ENNReal.ofReal (‖B‖ ^ 2) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg B])
  have h2 : ENNReal.ofReal (∑' j, ‖(A.comp B) (e j)‖ ^ 2) ≤
      ENNReal.ofReal (∑' j, ‖A (e j)‖ ^ 2) :=
    h1.trans (by simpa using mul_le_mul' hB2 (le_refl (ENNReal.ofReal (∑' j, ‖A (e j)‖ ^ 2))))
  exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg fun _ => sq_nonneg _)).1 h2

end HRS.MS.FinNoise
