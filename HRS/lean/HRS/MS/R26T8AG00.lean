import HRS.MS.R26T8AG00e
import HRS.Energy.Commutator.SmearAuxB
import HRS.MS.S82RA2

/-!
# S8.2 observed-time layer, packet T8A.G00: Gibbs pole moments and collision-nullity

For the finite-`N` canonical Gibbs measure `canonicalP` with `N ≥ 2`, the pole envelope `configPoleEnvelope M` is in
`L²`, and the collision set is `canonicalP`-null.  The density is bounded off the collisions by the Gaussian majorant
of helper e; the normalizer is finite and positive (the envelope is at least one, and the integrand is positive).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_gibbs_pole_moments (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (M : ℝ) (hM : 0 ≤ M) :
    MemLp (r26t8a_configPoleEnvelope (d := d) (N := N) M) 2 (canonicalP d N a beta) ∧
    (canonicalP d N a beta) (eucCollisionSet d N) = 0 := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 < beta / (2 * (N : ℝ)) := by positivity
  obtain ⟨K, hK0, hKb⟩ := r26t8a_g00b_pair (criticalS d) M (beta / (2 * (N : ℝ))) hs0 hM hc
  set k : ℕ := ⌈2 * M⌉₊ with hkdef
  have hk : 2 * M ≤ (k : ℝ) := Nat.le_ceil _
  have hb : 0 < beta * a / 2 := by positivity
  -- the Gaussian majorant
  have hint1 : Integrable (fun X : EucConfig d N =>
      ∏ i : Fin N, ((1 + ‖X i‖) ^ k * Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2))) volume := by
    have := Integrable.fintype_prod (μ := fun _ : Fin N => (volume : Measure (Euc d)))
      (f := fun _ : Fin N => fun x : Euc d => (1 + ‖x‖) ^ k * Real.exp (-(beta * a / 2) * ‖x‖ ^ 2))
      (fun _ => HRS.Commutator.SmearAux.integrable_pow_gauss hd1 hb k)
    exact this
  have hGint : Integrable (fun X : EucConfig d N =>
      (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, K) *
        ∏ i : Fin N, ((1 + ‖X i‖) ^ k * Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2))) volume :=
    hint1.const_mul _
  -- measurability
  have hgm : Measurable (rieszKernel d (criticalS d)) := by
    have e : rieszKernel d (criticalS d) = fun x => ‖x‖ ^ (-criticalS d) :=
      funext fun x => by unfold rieszKernel; rw [if_neg hs0.ne']
    rw [e]
    exact measurable_norm.pow_const _
  have hHm : Measurable (fun X : EucConfig d N =>
      HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (HRS.Whole.confinement a) X) := by
    unfold HRS.Whole.canonicalHamiltonian
    refine Measurable.add (Finset.measurable_sum _ fun i _ => ?_) (Measurable.const_mul ?_ _)
    · unfold HRS.Whole.confinement
      exact ((measurable_norm.comp (measurable_pi_apply i)).pow_const 2).const_mul _ |>.div_const 2
    · refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
      exact hgm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  have hφm : Measurable (fun X : EucConfig d N => ENNReal.ofReal
      (Real.exp (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d))
        (HRS.Whole.confinement a) X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hHm.const_mul _))
  have hEnvm : Measurable (configPoleEnvelope M : EucConfig d N → ℝ) := by
    unfold configPoleEnvelope
    refine Measurable.mul ((measurable_const.add (measurable_norm)).pow_const M) ?_
    refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
    exact measurable_const.add
      ((measurable_norm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))).pow_const (-M))
  -- the envelope is at least one, so the exponential is dominated by the majorant
  have henv1 : ∀ X : EucConfig d N, 1 ≤ configPoleEnvelope M X := by
    intro X
    unfold configPoleEnvelope
    have h1 : (1 : ℝ) ≤ (1 + ‖X‖) ^ M := Real.one_le_rpow (by linarith [norm_nonneg X]) hM
    have h2 : (1 : ℝ) ≤ ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-M)) :=
      Finset.one_le_prod₀ fun i _ => Finset.one_le_prod₀ fun j _ =>
        by linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-M)]
    nlinarith
  have hae : ∀ᵐ X ∂(volume : Measure (EucConfig d N)), X ∉ eucCollisionSet d N := by
    rw [ae_iff]
    simpa using r26t8a_g00_coll_null d N hd1
  have hbound : ∀ᵐ X ∂(volume : Measure (EucConfig d N)),
      ‖Real.exp (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d))
          (HRS.Whole.confinement a) X) * (configPoleEnvelope M X) ^ 2‖ ≤
        (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, K) *
          ∏ i : Fin N, ((1 + ‖X i‖) ^ k * Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2)) := by
    filter_upwards [hae] with X hX
    have hpos : 0 ≤ Real.exp (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d))
        (HRS.Whole.confinement a) X) * (configPoleEnvelope M X) ^ 2 :=
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    rw [Real.norm_of_nonneg hpos]
    exact r26t8a_g00e_pt hN hs0 ha hbeta hM k hk K hK0 hKb X hX
  -- the normalizer is positive and finite
  have hexpint : Integrable (fun X : EucConfig d N => Real.exp (-beta *
      HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (HRS.Whole.confinement a) X))
      volume := by
    refine Integrable.mono' hGint (Real.measurable_exp.comp (hHm.const_mul _)).aestronglyMeasurable ?_
    filter_upwards [hbound] with X hX
    have h1 := henv1 X
    have hE := (Real.exp_pos (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d))
      (HRS.Whole.confinement a) X)).le
    rw [Real.norm_of_nonneg hE]
    calc Real.exp (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d))
          (HRS.Whole.confinement a) X)
        ≤ Real.exp (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d))
          (HRS.Whole.confinement a) X) * (configPoleEnvelope M X) ^ 2 := by
          refine le_mul_of_one_le_right hE ?_
          nlinarith
      _ ≤ _ := le_trans (Real.le_norm_self _) hX
  have hZ : 0 < HRS.Whole.canonicalPartition (rieszKernel d (criticalS d)) (HRS.Whole.confinement a) N beta := by
    unfold HRS.Whole.canonicalPartition
    rw [integral_pos_iff_support_of_nonneg (fun X => (Real.exp_pos _).le) hexpint]
    have hsupp : Function.support (fun X : EucConfig d N => Real.exp (-beta *
        HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (HRS.Whole.confinement a) X)) = Set.univ :=
      Set.eq_univ_of_forall fun X => (Real.exp_pos _).ne'
    rw [hsupp, Measure.measure_univ_pos]
    exact NeZero.ne _
  refine ⟨?_, ?_⟩
  · unfold canonicalP HRS.Whole.canonicalGibbs
    rw [memLp_two_iff_integrable_sq_norm hEnvm.aestronglyMeasurable]
    apply Integrable.smul_measure _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne')
    rw [integrable_withDensity_iff_integrable_smul' hφm (ae_of_all _ fun X => ENNReal.ofReal_lt_top)]
    refine Integrable.mono' hGint
      ((ENNReal.measurable_toReal.comp hφm |>.smul ((hEnvm.norm).pow_const 2)).aestronglyMeasurable) ?_
    filter_upwards [hbound] with X hX
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    have e2 : ‖configPoleEnvelope M X‖ ^ 2 = (configPoleEnvelope M X) ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [e2]
    exact hX
  · unfold canonicalP HRS.Whole.canonicalGibbs
    have hz : (volume.withDensity fun X : EucConfig d N => ENNReal.ofReal (Real.exp (-beta *
        HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (HRS.Whole.confinement a) X)))
        (eucCollisionSet d N) = 0 :=
      (withDensity_absolutelyContinuous _ _) (r26t8a_g00_coll_null d N hd1)
    rw [Measure.smul_apply, hz, smul_zero]

end HRS.MS.R26T8A

end
