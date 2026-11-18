import HRS.MS.QMulAux2

/-!
# MS-QMUL, part 3: operator norms versus coordinates, Schwartz functions are in `QOk`
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem qm_norm_le_sum {l : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin l => Euc d) ℂ) :
    ‖T‖ ≤ ∑ i : Fin l → Fin d, ‖T (fun t => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_
  intro v
  have hv : ∀ t, v t = ∑ j : Fin d, (v t j) • (EuclideanSpace.single j (1:ℝ) : Euc d) := by
    intro t
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (v t)
    simpa [EuclideanSpace.basisFun_apply] using this.symm
  have h1 : T v = ∑ p ∈ Fintype.piFinset (fun _ : Fin l => (Finset.univ : Finset (Fin d))),
      (∏ t, v t (p t)) • T (fun t => (EuclideanSpace.single (p t) (1:ℝ) : Euc d)) := by
    have e : v = fun t => ∑ j ∈ (Finset.univ : Finset (Fin d)), (v t j) • (EuclideanSpace.single j (1:ℝ) : Euc d) :=
      funext hv
    conv_lhs => rw [e]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
  rw [h1, Fintype.piFinset_univ]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [norm_smul, norm_prod, mul_comm _ (∏ t, ‖v t‖)]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun t _ => by
    simpa using PiLp.norm_apply_le (v t) (p t)

theorem qm_schwartz_QOk (m : ℕ) (f : SchwartzMap (Euc d) ℂ) : QOk m (⇑f) := by
  refine ⟨f.smooth m, fun k hk => ?_⟩
  have hc : Continuous (iteratedFDeriv ℝ k (⇑f)) :=
    (f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)
  have hI : Integrable (fun x => ‖iteratedFDeriv ℝ k (⇑f) x‖) volume := by
    simpa using f.integrable_pow_mul_iteratedFDeriv volume 0 k
  refine ⟨(integrable_norm_iff hc.aestronglyMeasurable).1 hI, ?_⟩
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  refine (hI.const_mul (SchwartzMap.seminorm ℝ 0 k f)).mono' ?_ ?_
  · exact (hc.norm.pow 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have h1 := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f k x
    rw [Real.norm_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _) |>.trans_eq (by ring)

end HRS.MS.QMul
