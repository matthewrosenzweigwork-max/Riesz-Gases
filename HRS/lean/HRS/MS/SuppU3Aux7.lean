import HRS.MS.SuppU3Aux6
import HRS.Whole.Adjoint

/-!
# U3, part 7: coordinate derivatives versus iterated Fréchet derivatives
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.SuppU3
open HRS.Whole

variable {d : ℕ}

theorem u3_mlin_norm_le (n : ℕ) (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i : Fin n → Fin d, |T (fun t => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))| ≤ c) :
    ‖T‖ ≤ (d : ℝ) ^ n * c := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) ?_
  intro v
  have hv : ∀ t, v t = ∑ j : Fin d, (v t j) • (EuclideanSpace.single j (1:ℝ) : Euc d) := by
    intro t
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (v t)
    simpa [EuclideanSpace.basisFun_apply] using this.symm
  have h1 : T v = ∑ p ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (Fin d))),
      (∏ t, v t (p t)) • T (fun t => (EuclideanSpace.single (p t) (1:ℝ) : Euc d)) := by
    have e : v = fun t => ∑ j ∈ (Finset.univ : Finset (Fin d)),
        (v t j) • (EuclideanSpace.single j (1:ℝ) : Euc d) := funext hv
    conv_lhs => rw [e]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
  rw [h1, Fintype.piFinset_univ]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p : Fin n → Fin d, ‖(∏ t, v t (p t)) • T (fun t => (EuclideanSpace.single (p t) (1:ℝ) : Euc d))‖
      ≤ ∑ _p : Fin n → Fin d, (c * ∏ t, ‖v t‖) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_smul, norm_prod, mul_comm c]
        refine mul_le_mul ?_ (by simpa using h _) (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun t _ => by
          simpa using PiLp.norm_apply_le (v t) (p t)
    _ = (d : ℝ) ^ n * c * ∏ t, ‖v t‖ := by
        simp [Finset.sum_const, Fintype.card_fun]; ring

theorem u3_iter_g {U : Euc d → ℝ} {k : ℕ} (hU : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) U) (j : Fin d) (x : Euc d)
    (v : Fin k → Euc d) :
    iteratedFDeriv ℝ k (fun y => fderiv ℝ U y (EuclideanSpace.single j (1:ℝ))) x v =
      iteratedFDeriv ℝ (k + 1) U x (Fin.snoc v (EuclideanSpace.single j (1:ℝ))) := by
  have hf : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ U) :=
    hU.fderiv_right (by exact_mod_cast le_rfl)
  have e : (fun y => fderiv ℝ U y (EuclideanSpace.single j (1:ℝ))) =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1:ℝ) : Euc d)) ∘ (fderiv ℝ U) := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf.contDiffAt le_rfl]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  rw [iteratedFDeriv_succ_apply_right]
  simp

theorem u3_g_bound {U : Euc d → ℝ} {k : ℕ} (hU : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) U) (j : Fin d)
    (x : Euc d) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : Fin (k + 1) → Fin d, |partialDeriv i U x| ≤ c) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ U y (EuclideanSpace.single j (1:ℝ))) x‖ ≤ (d : ℝ) ^ k * c := by
  refine u3_mlin_norm_le k _ hc (fun i => ?_)
  rw [u3_iter_g hU j x]
  have e : (Fin.snoc (fun t => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))
      (EuclideanSpace.single j (1:ℝ) : Euc d) : Fin (k + 1) → Euc d) =
      fun l => (EuclideanSpace.single ((Fin.snoc i j : Fin (k + 1) → Fin d) l) (1:ℝ) : Euc d) := by
    funext l
    refine Fin.lastCases ?_ (fun l => ?_) l
    · simp
    · simp
  rw [e]
  exact h _

theorem u3_partialDeriv_comb {p : ℕ} (i : Fin p → Fin d) {f g : Euc d → ℝ} {n : ℕ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hp : p ≤ n) (c : ℝ) (x : Euc d) :
    partialDeriv i (c • f + g) x = c * partialDeriv i f x + partialDeriv i g x := by
  unfold partialDeriv
  rw [iteratedFDeriv_add_apply (f := c • f) (g := g) ((hf.const_smul c).contDiffAt.of_le (by exact_mod_cast hp))
    (hg.contDiffAt.of_le (by exact_mod_cast hp))]
  rw [iteratedFDeriv_const_smul_apply (hf.contDiffAt.of_le (by exact_mod_cast hp))]
  simp

end HRS.MS.SuppU3
