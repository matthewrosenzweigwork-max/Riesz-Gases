import Mathlib

/-!
# Worker U8 aux 17: operator norm of a multilinear map on `ℝ^d` by its values on coordinate vectors
-/

noncomputable section

open Finset

namespace HRS.U8

variable {d : ℕ}

theorem u8_opnorm_le (j : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclideanSpace ℝ (Fin d)) ℝ) :
    ‖T‖ ≤ ∑ r : Fin j → Fin d, |T (fun l => EuclideanSpace.single (r l) 1)| := by
  apply ContinuousMultilinearMap.opNorm_le_bound
  · exact Finset.sum_nonneg (fun r _ => abs_nonneg _)
  · intro m
    have hm : ∀ l, m l = ∑ i : Fin d, (m l i) • (EuclideanSpace.single i (1 : ℝ)) := by
      intro l
      ext k
      simp [Pi.single_apply]
    have h1 : T m = ∑ r : Fin j → Fin d, (∏ l, m l (r l)) •
        T (fun l => EuclideanSpace.single (r l) 1) := by
      have h2 := T.toMultilinearMap.map_sum
        (fun (l : Fin j) (i : Fin d) => (m l i) • (EuclideanSpace.single i (1 : ℝ)))
      calc T m = T (fun l => ∑ i : Fin d, (m l i) • (EuclideanSpace.single i (1 : ℝ))) := by
            rw [← show m = fun l => ∑ i : Fin d, (m l i) • (EuclideanSpace.single i (1 : ℝ))
              from funext hm]
        _ = ∑ r : Fin j → Fin d, T (fun l => (m l (r l)) • (EuclideanSpace.single (r l) (1 : ℝ))) :=
            h2
        _ = _ := by
            apply Finset.sum_congr rfl
            intro r _
            exact T.toMultilinearMap.map_smul_univ _ _
    rw [h1]
    calc ‖∑ r : Fin j → Fin d, (∏ l, m l (r l)) • T (fun l => EuclideanSpace.single (r l) 1)‖
        ≤ ∑ r : Fin j → Fin d, ‖(∏ l, m l (r l)) • T (fun l => EuclideanSpace.single (r l) 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ r : Fin j → Fin d, |T (fun l => EuclideanSpace.single (r l) 1)| * ∏ l, ‖m l‖ := by
          apply Finset.sum_le_sum
          intro r _
          rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [Finset.abs_prod]
          refine Finset.prod_le_prod₀ (fun l _ => abs_nonneg _) (fun l _ => ?_)
          have := PiLp.norm_apply_le (m l) (r l)
          simpa [Real.norm_eq_abs] using this
      _ = (∑ r : Fin j → Fin d, |T (fun l => EuclideanSpace.single (r l) 1)|) * ∏ l, ‖m l‖ := by
          rw [Finset.sum_mul]

end HRS.U8
