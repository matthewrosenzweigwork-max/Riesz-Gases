import HRS.MS.SuppU2Aux9

/-!
# U2 auxiliary 10: the kernel instance and the glue between `weightedSupE`/`decayNormE` and norms
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.Whole

variable {d : ℕ}

/-- The components of `∇g` satisfy the full kernel hypotheses with `a = s + 1`. -/
theorem u2_kerFull (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (i : Fin d) :
    U2KerFull (u2_kap d s i) (s + 1) := by
  have hsm : ∀ z : Euc d, z ≠ 0 → ContDiffAt ℝ ∞ (u2_kap d s i) z :=
    fun z hz => u2_kap_contDiffAt s i hz
  have hom : ∀ t : ℝ, 0 < t → ∀ z : Euc d, z ≠ 0 →
      u2_kap d s i (t • z) = t ^ (-(s + 1)) * u2_kap d s i z :=
    fun t ht z hz => u2_kap_hom s i ht hz
  have hD := fun j => u2_iter_bound (u2_kap d s i) (s + 1) hsm hom j
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨⟨u2_kap_measurable s i, by linarith, ?_, by omega, ?_⟩, hsm, hD⟩
  · obtain ⟨C, hC, hb⟩ := hD 0
    refine ⟨C, hC, fun z hz => ?_⟩
    have := hb z hz
    simpa using this
  · exact u2_integrableOn_ball_rpow (by omega) (by linarith) (by linarith)

/-- The operator norm of a multilinear form on `ℝ^d` is bounded by the sum of its values on the basis
tuples. -/
lemma u2_opnorm_le_sum {j : ℕ} (T : Euc d [×j]→L[ℝ] ℝ) :
    ‖T‖ ≤ ∑ I : Fin j → Fin d, |T (fun l => EuclideanSpace.single (I l) (1 : ℝ))| := by
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_
  intro v
  have hv : ∀ l, v l = ∑ i : Fin d, (v l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    intro l
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (v l)
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
  have h1 : T v = ∑ I : Fin j → Fin d, (∏ l, v l (I l)) *
      T (fun l => EuclideanSpace.single (I l) (1 : ℝ)) := by
    have := T.toMultilinearMap.map_sum (fun l (i : Fin d) => (v l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d))
    have e : v = fun l => ∑ i : Fin d, (v l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d) :=
      funext hv
    conv_lhs => rw [e]
    rw [show (T (fun l => ∑ i : Fin d, (v l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d))) =
      T.toMultilinearMap (fun l => ∑ i : Fin d, (v l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d)) from rfl,
      this]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [ContinuousMultilinearMap.coe_coe]
    rw [show (fun l => v l (I l) • (EuclideanSpace.single (I l) (1 : ℝ) : Euc d)) =
      fun l => v l (I l) • (EuclideanSpace.single (I l) (1 : ℝ) : Euc d) from rfl]
    rw [T.map_smul_univ]
    simp [smul_eq_mul]
  rw [h1]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun I _ => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod]
  have : ∏ l, |v l (I l)| ≤ ∏ l, ‖v l‖ :=
    Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun l _ => by
      simpa using PiLp.norm_apply_le (v l) (I l))
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

end HRS.Whole
