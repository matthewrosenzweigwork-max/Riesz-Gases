import HRS.MH.AdjointRdDefs

/-!
# S.A.12 R34 (SA12X2), part A: a multilinear norm bound by the tuple partials

For a continuous `j`-linear form `T` on `ℝ^d`: `‖T‖² ≤ d^j ∑_{idx} T(e_{idx})²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators

namespace HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12x2_multi_norm_le {j : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclideanSpace ℝ (Fin d)) ℝ) :
    ‖T‖ ≤ ∑ idx : Fin j → Fin d, |T (fun l => EuclideanSpace.single (idx l) 1)| := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  intro v
  have hdec : ∀ l, v l = ∑ i : Fin d, (v l i) • EuclideanSpace.single i (1 : ℝ) := by
    intro l
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = fun l => ∑ i : Fin d, (v l i) • EuclideanSpace.single i (1 : ℝ) := funext hdec
  have hT : T v = ∑ r : Fin j → Fin d,
      (∏ l, v l (r l)) • T (fun l => EuclideanSpace.single (r l) (1 : ℝ)) := by
    conv_lhs => rw [hv]
    rw [T.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have := T.map_smul_univ (fun l => v l (r l)) (fun l => EuclideanSpace.single (r l) (1 : ℝ))
    simpa using this
  rw [hT]
  calc ‖∑ r : Fin j → Fin d, (∏ l, v l (r l)) • T (fun l => EuclideanSpace.single (r l) (1 : ℝ))‖
      ≤ ∑ r : Fin j → Fin d, ‖(∏ l, v l (r l)) • T (fun l => EuclideanSpace.single (r l) (1 : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r : Fin j → Fin d, (∏ l, ‖v l‖) * |T (fun l => EuclideanSpace.single (r l) (1 : ℝ))| := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod]
        refine mul_le_mul ?_ le_rfl (abs_nonneg _) (Finset.prod_nonneg fun l _ => norm_nonneg _)
        have h0 : ∀ l ∈ (Finset.univ : Finset (Fin j)), 0 ≤ |v l (r l)| := fun l _ => abs_nonneg _
        have h1 : ∀ l ∈ (Finset.univ : Finset (Fin j)), |v l (r l)| ≤ ‖v l‖ := fun l _ => by
          rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
        exact Finset.prod_le_prod₀ h0 h1
    _ = (∏ l, ‖v l‖) * ∑ idx : Fin j → Fin d, |T (fun l => EuclideanSpace.single (idx l) 1)| := by
        rw [Finset.mul_sum]
    _ = (∑ idx : Fin j → Fin d, |T (fun l => EuclideanSpace.single (idx l) 1)|) * ∏ i, ‖v i‖ := by
        ring

theorem sa12x2_multi_sq_le {j : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclideanSpace ℝ (Fin d)) ℝ) :
    ‖T‖ ^ 2 ≤ (d : ℝ) ^ j * ∑ idx : Fin j → Fin d, (T (fun l => EuclideanSpace.single (idx l) 1)) ^ 2 := by
  have hM := sa12x2_multi_norm_le T
  have hsq : (∑ idx : Fin j → Fin d, |T (fun l => EuclideanSpace.single (idx l) 1)|) ^ 2 ≤
      (Finset.univ : Finset (Fin j → Fin d)).card *
        ∑ idx : Fin j → Fin d, (|T (fun l => EuclideanSpace.single (idx l) 1)|) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcard : ((Finset.univ : Finset (Fin j → Fin d)).card : ℝ) = (d : ℝ) ^ j := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast; ring
  simp only [sq_abs] at hsq
  rw [hcard] at hsq
  calc ‖T‖ ^ 2 ≤ (∑ idx : Fin j → Fin d, |T (fun l => EuclideanSpace.single (idx l) 1)|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hM 2
    _ ≤ _ := hsq

end HRS.MH.AdjointRd.Phase2SA12
