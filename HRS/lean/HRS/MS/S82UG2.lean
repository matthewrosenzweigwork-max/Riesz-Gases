import HRS.MS.S82UG1

/-!
# S8.2 A04 (S82U), part 2: `canonicalP` is a probability measure, absolutely continuous, collision-free
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82

section gibbs
variable {d N : ℕ}

lemma u4_w_meas (d N : ℕ) (a beta : ℝ) : Measurable (u4w d N a beta) := by
  have hgm : Measurable (HRS.Whole.rieszKernel d (criticalS d)) := HRS.MP.RdRem.mrr_measurable_rieszKernel _
  unfold u4w
  refine Real.measurable_exp.comp (measurable_const.mul ?_)
  unfold HRS.Whole.canonicalHamiltonian
  refine (Finset.measurable_sum _ fun i _ => ?_).add (measurable_const.mul
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_))
  · unfold HRS.Whole.confinement
    exact ((measurable_const.mul ((measurable_pi_apply i).norm.pow_const 2)).div_const _)
  · exact hgm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

lemma u4_w_int (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) :
    Integrable (u4w d N a beta) (volume : Measure (EucConfig d N)) := by
  have hc : 0 < beta * a / 2 := by positivity
  have h1 : Integrable (fun z : Euc d => (1 + ‖z‖) ^ (0 : ℝ) * Real.exp (-(beta * a / 2) * ‖z‖ ^ 2)) :=
    u4_gauss_int1 hd hc le_rfl
  have h2 : Integrable (fun X : EucConfig d N => ∏ i, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2))
      (volume : Measure (EucConfig d N)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin N => (volume : Measure (Euc d)))
      (f := fun _ z => (1 + ‖z‖) ^ (0 : ℝ) * Real.exp (-(beta * a / 2) * ‖z‖ ^ 2)) (fun _ => h1)
    simpa [Real.rpow_zero, volume_pi] using this
  refine Integrable.mono' h2 (u4_w_meas d N a beta).aestronglyMeasurable (Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold u4w; exact (Real.exp_pos _).le)]
  exact u4_w_le hd hbeta X

lemma u4_Z_pos (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) :
    0 < HRS.Whole.canonicalPartition (rieszKernel d (criticalS d)) (confinement a) N beta := by
  unfold HRS.Whole.canonicalPartition
  have hint := u4_w_int (N := N) hd ha hbeta
  unfold u4w at hint
  have := (integral_pos_iff_support_of_nonneg (f := fun X : EucConfig d N => Real.exp (-beta *
    HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a) X))
    (fun X => (Real.exp_pos _).le) hint).2
  refine this ?_
  have hs : Function.support (fun X : EucConfig d N => Real.exp (-beta *
      HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a) X)) = Set.univ := by
    ext X; simp [Function.mem_support, (Real.exp_pos _).ne']
  rw [hs]
  haveI : NeZero (volume : Measure (EucConfig d N)) := inferInstance
  exact Measure.measure_univ_pos.2 (NeZero.ne _)

lemma u4_prob (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) :
    IsProbabilityMeasure (canonicalP d N a beta) := by
  have hZ := u4_Z_pos (N := N) hd ha hbeta
  have hint := u4_w_int (N := N) hd ha hbeta
  have hwm := u4_w_meas d N a beta
  unfold canonicalP HRS.Whole.canonicalGibbs
  refine ⟨?_⟩
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  have := ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)
  unfold HRS.Whole.canonicalPartition at hZ ⊢
  unfold u4w at this
  rw [← this]
  exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top

lemma u4_ac (d N : ℕ) (a beta : ℝ) : canonicalP d N a beta ≪ (volume : Measure (EucConfig d N)) := by
  unfold canonicalP HRS.Whole.canonicalGibbs
  exact (withDensity_absolutelyContinuous _ _).smul_left _

lemma u4_coll_null (hd : 1 ≤ d) (N : ℕ) : (volume : Measure (EucConfig d N)) (eucCollisionSet d N) = 0 := by
  have : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hset : eucCollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j),
      {X : EucConfig d N | X i = X j} := by
    ext X; simp [eucCollisionSet]
  rw [hset]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  let L : EucConfig d N →ₗ[ℝ] Euc d := (LinearMap.proj i : EucConfig d N →ₗ[ℝ] Euc d) - LinearMap.proj j
  have hk : {X : EucConfig d N | X i = X j} = (LinearMap.ker L : Set (EucConfig d N)) := by
    ext X; simp [L, sub_eq_zero]
  rw [hk]
  refine Measure.addHaar_submodule volume (LinearMap.ker L) ?_
  intro htop
  obtain ⟨v, hv⟩ := exists_ne (0 : Euc d)
  have hmem : (Pi.single i v : EucConfig d N) ∈ LinearMap.ker L := by rw [htop]; trivial
  simp only [LinearMap.mem_ker, L, LinearMap.sub_apply, LinearMap.proj_apply] at hmem
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij.symm, sub_zero] at hmem
  exact hv hmem

lemma u4_P_coll (hd : 2 ≤ d) (N : ℕ) (a beta : ℝ) : canonicalP d N a beta (eucCollisionSet d N) = 0 :=
  u4_ac d N a beta (u4_coll_null (by omega) N)

/-- Integrability against `canonicalP` from integrability of `g * w`. -/
lemma u4_int_of_w (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) {g : EucConfig d N → ℝ}
    (h : Integrable (fun X => u4w d N a beta X * g X) (volume : Measure (EucConfig d N))) :
    Integrable g (canonicalP d N a beta) := by
  unfold canonicalP HRS.Whole.canonicalGibbs
  have hm : Measurable (fun X : EucConfig d N => ENNReal.ofReal (u4w d N a beta X)) :=
    ENNReal.measurable_ofReal.comp (u4_w_meas d N a beta)
  have hZ := u4_Z_pos (N := N) hd ha hbeta
  have h1 : Integrable g ((volume : Measure (EucConfig d N)).withDensity
      fun X => ENNReal.ofReal (Real.exp (-beta *
        HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a) X))) := by
    refine (integrable_withDensity_iff_integrable_smul' hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2 ?_
    refine h.congr (Eventually.of_forall fun X => ?_)
    simp only [u4w, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  exact h1.smul_measure (ENNReal.inv_ne_top.2 (by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hZ))

end gibbs

end HRS.MS.S82U
