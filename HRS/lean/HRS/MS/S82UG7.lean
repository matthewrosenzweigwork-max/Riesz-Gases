import HRS.MS.S82UG6
import HRS.Whole.MovtrAux9

/-!
# S8.2 A04 (S82U), part 7: the generator of a function `C²` off collisions is in `L²(canonicalP)`
This proves the three `L²` clauses of `GeneratorClosure` for `F`, `particleGenerator F` and `configGrad F`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82

section gen
variable {d N : ℕ}

lemma u4_matVec_neg_one (v : Euc d) : Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
  unfold Torus.matVec
  rw [map_neg]
  simp

lemma u4_riesz_cont (hd : 2 ≤ d) : ContinuousOn (rieszKernelGrad d (criticalS d)) {z : Euc d | z ≠ 0} := by
  have hnorm : ContinuousOn (fun z : Euc d => ‖z‖) {z : Euc d | z ≠ 0} := continuous_norm.continuousOn
  have hn : ContinuousOn (fun z : Euc d => ‖z‖ ^ (-criticalS d - 2)) {z : Euc d | z ≠ 0} :=
    hnorm.rpow_const (fun z hz => Or.inl (norm_ne_zero_iff.2 hz))
  have hm : ContinuousOn (fun z : Euc d => HRS.Whole.movtr_sigma (criticalS d) * ‖z‖ ^ (-criticalS d - 2))
      {z : Euc d | z ≠ 0} := continuousOn_const.mul hn
  have hc : ContinuousOn (fun z : Euc d => (-(HRS.Whole.movtr_sigma (criticalS d) * ‖z‖ ^ (-criticalS d - 2))) • z)
      {z : Euc d | z ≠ 0} := hm.neg.smul continuousOn_id
  refine hc.congr fun z hz => ?_
  exact HRS.Whole.movtr_rieszKernelGrad_eq _ hz

lemma u4_drift_eq (a beta : ℝ) (X : EucConfig d N) (i : Fin N) :
    particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i =
      -((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d (criticalS d) (X i - X j)) - a • X i := by
  unfold particleDriftW
  have hM : (quadraticGradientDyn d (criticalS d) a beta).M = -1 := rfl
  have hs : (quadraticGradientDyn d (criticalS d) a beta).s = criticalS d := rfl
  have hV : (quadraticGradientDyn d (criticalS d) a beta).V = confinement a := rfl
  rw [hM, hs, hV, movtr_gradient_confinement]
  simp only [u4_matVec_neg_one, Finset.sum_neg_distrib, smul_neg]

lemma u4_drift_norm_le (hd : 2 ≤ d) (hN : 0 < N) {a : ℝ} (ha : 0 ≤ a) (beta : ℝ) {X : EucConfig d N}
    (hX : X ∉ eucCollisionSet d N) (i : Fin N) :
    ‖particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i‖ ≤
      ∑ j ∈ Finset.univ.erase i, HRS.Whole.movtr_sigma (criticalS d) * ‖X i - X j‖ ^ (-(criticalS d + 1)) + a * ‖X‖ := by
  rw [u4_drift_eq]
  have hs0 : 0 ≤ criticalS d := (u4_crit_pos hd).le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : ‖(1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d (criticalS d) (X i - X j)‖ ≤
      ∑ j ∈ Finset.univ.erase i, HRS.Whole.movtr_sigma (criticalS d) * ‖X i - X j‖ ^ (-(criticalS d + 1)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : ‖∑ j ∈ Finset.univ.erase i, rieszKernelGrad d (criticalS d) (X i - X j)‖ ≤
        ∑ j ∈ Finset.univ.erase i, HRS.Whole.movtr_sigma (criticalS d) * ‖X i - X j‖ ^ (-(criticalS d + 1)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      have hne : X i - X j ≠ 0 := sub_ne_zero.2 (fun h => hX ⟨i, j, (Finset.ne_of_mem_erase hj).symm, h⟩)
      rw [HRS.Whole.movtr_rieszKernelGrad_norm _ hs0 hne]
      have : -criticalS d - 1 = -(criticalS d + 1) := by ring
      rw [this]
    have h3 : 0 ≤ ∑ j ∈ Finset.univ.erase i, HRS.Whole.movtr_sigma (criticalS d) * ‖X i - X j‖ ^ (-(criticalS d + 1)) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (HRS.MS.S82T.s82t_sigma_nonneg _ hs0) (Real.rpow_nonneg (norm_nonneg _) _)
    have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hN1
    calc 1 / (N : ℝ) * ‖∑ j ∈ Finset.univ.erase i, rieszKernelGrad d (criticalS d) (X i - X j)‖
        ≤ 1 * ∑ j ∈ Finset.univ.erase i, HRS.Whole.movtr_sigma (criticalS d) * ‖X i - X j‖ ^ (-(criticalS d + 1)) :=
          mul_le_mul this h2 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h4 : ‖a • X i‖ ≤ a * ‖X‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm X i) ha
  calc ‖-((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d (criticalS d) (X i - X j)) - a • X i‖
      ≤ ‖-((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d (criticalS d) (X i - X j))‖ + ‖a • X i‖ :=
        norm_sub_le _ _
    _ ≤ _ := by rw [norm_neg]; linarith

lemma u4_drift_cont (hd : 2 ≤ d) (a beta : ℝ) (i : Fin N) :
    ContinuousOn (fun X : EucConfig d N => particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
      (eucCollisionSet d N)ᶜ := by
  simp_rw [u4_drift_eq]
  refine ContinuousOn.sub (ContinuousOn.neg (ContinuousOn.smul (f := fun _ : EucConfig d N => (1 / (N : ℝ))) continuousOn_const ?_)) ?_
  · refine continuousOn_finsetSum _ fun j hj => ?_
    refine (u4_riesz_cont hd).comp ((continuous_apply i).sub (continuous_apply j)).continuousOn ?_
    intro X hX
    exact sub_ne_zero.2 (fun h => hX ⟨i, j, (Finset.ne_of_mem_erase hj).symm, h⟩)
  · exact ContinuousOn.smul (f := fun _ : EucConfig d N => a) continuousOn_const (continuous_apply i).continuousOn

lemma u4_aesm_of_contOn {E : Type*} [NormedAddCommGroup E] (hd : 2 ≤ d) {a beta : ℝ} {g : EucConfig d N → E}
    (hg : ContinuousOn g (eucCollisionSet d N)ᶜ) : AEStronglyMeasurable g (canonicalP d N a beta) := by
  have h1 := hg.aestronglyMeasurable (μ := canonicalP d N a beta) u4_coll_closed.measurableSet.compl
  have hae : ∀ᵐ X ∂(canonicalP d N a beta), X ∈ (eucCollisionSet d N)ᶜ := by
    rw [ae_iff]; simpa using u4_P_coll hd N a beta
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1

end gen

end HRS.MS.S82U
