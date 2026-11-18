import HRS.MS.FinNoiseAux26

/-!
# S8.6 `finite_noise`: key inequality for the Araki-Yamagami bound (S86)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  {ι : Type*} (e : HilbertBasis ι ℝ K)

theorem s86_hsPair_summable {A B : K →L[ℝ] K} (hA : Summable fun j => ‖A (e j)‖ ^ 2)
    (hB : Summable fun j => ‖B (e j)‖ ^ 2) : Summable fun j => inner ℝ (A (e j)) (B (e j)) :=
  (s86_hsPair_formula e hA hB).1

theorem s86_hsPair_sub_right {A B C : K →L[ℝ] K} (hA : Summable fun j => ‖A (e j)‖ ^ 2)
    (hB : Summable fun j => ‖B (e j)‖ ^ 2) (hC : Summable fun j => ‖C (e j)‖ ^ 2) :
    hsPair e A (B - C) = hsPair e A B - hsPair e A C := by
  unfold hsPair
  rw [← (s86_hsPair_summable e hA hB).tsum_sub (s86_hsPair_summable e hA hC)]
  exact tsum_congr fun j => by simp [inner_sub_right]

theorem s86_hsPair_add_right {A B C : K →L[ℝ] K} (hA : Summable fun j => ‖A (e j)‖ ^ 2)
    (hB : Summable fun j => ‖B (e j)‖ ^ 2) (hC : Summable fun j => ‖C (e j)‖ ^ 2) :
    hsPair e A (B + C) = hsPair e A B + hsPair e A C := by
  unfold hsPair
  rw [← (s86_hsPair_summable e hA hB).tsum_add (s86_hsPair_summable e hA hC)]
  exact tsum_congr fun j => by simp [inner_add_right]

theorem s86_key_ineq [Countable ι] {S S' W : K →L[ℝ] K}
    (hS : ∀ x y, inner ℝ (S x) y = inner ℝ x (S y)) (hS0 : ∀ x, 0 ≤ inner ℝ (S x) x)
    (hS' : ∀ x y, inner ℝ (S' x) y = inner ℝ x (S' y)) (hS'0 : ∀ x, 0 ≤ inner ℝ (S' x) x)
    (hSs : Summable fun j => ‖S (e j)‖ ^ 2) (hS's : Summable fun j => ‖S' (e j)‖ ^ 2)
    (hW : ‖W‖ ≤ 1) :
    4 * hsPair e S (W.comp S') ≤
      (∑' j, ‖S (e j)‖ ^ 2) + (∑' j, ‖S' (e j)‖ ^ 2) + 2 * hsPair e S S' := by
  classical
  set W' : K →L[ℝ] K := ContinuousLinearMap.adjoint W with hW'
  have hW'n : ‖W'‖ ≤ 1 := by rw [hW', ContinuousLinearMap.adjoint.norm_map]; exact hW
  set A1 := S'.comp W' with hA1
  set A2 := W.comp S' with hA2
  set A3 := A2.comp W' with hA3
  have s1 : Summable fun j => ‖A1 (e j)‖ ^ 2 := s86_hsS_comp_right e hS's W'
  have s2 : Summable fun j => ‖A2 (e j)‖ ^ 2 := s86_hsS_comp_left e hS's W
  have s3 : Summable fun j => ‖A3 (e j)‖ ^ 2 := s86_hsS_comp_right e s2 W'
  set Z : K →L[ℝ] K := S' - A1 - A2 + A3 with hZ
  have sZ : Summable fun j => ‖Z (e j)‖ ^ 2 :=
    s86_hs_add_summable e (s86_hs_sub_summable e (s86_hs_sub_summable e hS's s1) s2) s3
  have hZ0 : ∀ y, 0 ≤ inner ℝ (Z y) y := fun y => by
    have h := hS0 y
    have hq : inner ℝ (Z y) y = inner ℝ (S' (y - W' y)) (y - W' y) := by
      simp only [hZ, hA1, hA2, hA3, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
        inner_add_left, inner_sub_left, inner_sub_right, map_sub]
      have e1 : inner ℝ (W (S' y)) y = inner ℝ (S' y) (W' y) := by
        rw [hW', ContinuousLinearMap.adjoint_inner_right]
      have e2 : inner ℝ (W (S' (W' y))) y = inner ℝ (S' (W' y)) (W' y) := by
        rw [hW', ContinuousLinearMap.adjoint_inner_right]
      rw [e1, e2]
      ring
    rw [hq]
    exact hS'0 _
  have hPL := s86_pair_nonneg e hS hS0 hZ0 hSs sZ
  have hexp : hsPair e S Z = hsPair e S S' - hsPair e S A1 - hsPair e S A2 + hsPair e S A3 := by
    rw [hZ, s86_hsPair_add_right e hSs (s86_hs_sub_summable e (s86_hs_sub_summable e hS's s1) s2) s3,
      s86_hsPair_sub_right e hSs (s86_hs_sub_summable e hS's s1) s2,
      s86_hsPair_sub_right e hSs hS's s1]
  have hcyc : hsPair e S A1 = hsPair e S A2 := by
    have h1 := s86_trace_cyclic e S A2 (s86_hs2_ne_top_of_summable e hSs)
      (s86_hs2_ne_top_of_summable e s2)
    have e1 : hsPair e S A2 = ∑' j, inner ℝ (S (A2 (e j))) (e j : K) := by
      unfold hsPair
      refine tsum_congr fun j => ?_
      rw [real_inner_comm, hS, real_inner_comm]
    have e2 : hsPair e S A1 = ∑' j, inner ℝ (A2 (S (e j))) (e j : K) := by
      unfold hsPair
      refine tsum_congr fun j => ?_
      simp only [hA1, hA2, ContinuousLinearMap.comp_apply]
      rw [← hS' (S (e j)) (W' (e j)), hW', ContinuousLinearMap.adjoint_inner_right]
    rw [e1, e2, h1]
  have hbound : hsPair e S A3 ≤
      ((∑' j, ‖S (e j)‖ ^ 2) + (∑' j, ‖S' (e j)‖ ^ 2)) / 2 := by
    have hb3 : ∑' j, ‖A3 (e j)‖ ^ 2 ≤ ∑' j, ‖S' (e j)‖ ^ 2 :=
      (s86_hsS_sum_le_right e s2 W' hW'n).trans (s86_hsS_sum_le e hS's W hW)
    have h1 : hsPair e S A3 ≤ ∑' j, (‖S (e j)‖ ^ 2 + ‖A3 (e j)‖ ^ 2) / 2 := by
      refine Summable.tsum_le_tsum (fun j => ?_) (s86_hsPair_summable e hSs s3)
        ((hSs.add s3).div_const 2)
      nlinarith [real_inner_le_norm (S (e j)) (A3 (e j)), sq_nonneg (‖S (e j)‖ - ‖A3 (e j)‖),
        norm_nonneg (S (e j)), norm_nonneg (A3 (e j)),
        real_inner_le_norm (S (e j)) (A3 (e j)), abs_real_inner_le_norm (S (e j)) (A3 (e j))]
    refine h1.trans ?_
    rw [tsum_div_const, hSs.tsum_add s3]
    linarith
  rw [hexp, hcyc] at hPL
  linarith

end HRS.MS.FinNoise
