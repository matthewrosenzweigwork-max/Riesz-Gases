import HRS.MC.E213U13j
import HRS.MS.Fp81S21WickB311

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
open HRS HRS.MC.E213U13

namespace HRS.Fp81.S21

/-- The retained first-chaos certificate places an L² class in the scalar
first-chaos closure used by the centered-product construction. -/
theorem fp81s21_firstChaos_to_InQ1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (X : Lp ℝ 2 P) (hsrc : InFirstChaos P ξ 2 (fun ω => X ω)) :
    InQ1 hξ hm (fun ω => X ω) := by
  classical
  obtain ⟨hX, n, c, hlim⟩ := hsrc
  let v : ℕ → Lp ℝ 2 P := fun m =>
    ∑ i ∈ Finset.range (n m), c m i • g1 hξ hm i
  have hv (m : ℕ) : v m ∈ Qc (K1 hξ hm) := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.le_topologicalClosure
    apply (le_iSup (K1 hξ hm) (n m))
    exact Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  have ha (m : ℕ) : (v m : Ω → ℝ) =ᵐ[P]
      fun ω => ∑ i ∈ Finset.range (n m), ξ i ω • c m i := by
    have hs : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (n m),
        (c m i • g1 hξ hm i : Lp ℝ 2 P) ω = ξ i ω • c m i := by
      rw [ae_all_iff]
      intro i
      filter_upwards [Lp.coeFn_smul (c m i) (g1 hξ hm i), coe_g1 hξ hm i] with ω h₁ h₂ hi
      simp only [h₁, Pi.smul_apply, h₂, smul_eq_mul, mul_comm]
    filter_upwards [Lp.coeFn_finsetSum (Finset.range (n m))
      (fun i => c m i • g1 hξ hm i), hs] with ω h₁ h₂
    rw [h₁]
    simpa only [Finset.sum_apply] using (Finset.sum_congr rfl fun i hi => h₂ i hi)
  have hmeas : ∀ m, AEStronglyMeasurable
      (fun ω => (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - X ω) P := by
    intro m
    exact (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (hm i).aestronglyMeasurable.smul_const _).sub hX
  have hnorm := (tendsto_lintegral_iff_eLpNorm hmeas (by norm_num : (0 : ℝ) < 2)).1 hlim
  have hconv : Tendsto v atTop (𝓝 X) := by
    rw [← Lp.toLp_coeFn X (Lp.memLp X)]
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm v (fun ω => X ω) (Lp.memLp X)).2
    have hh : Tendsto (fun m => eLpNorm (fun ω =>
        (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - X ω) 2 P) atTop (𝓝 0) := by
      simpa using hnorm
    refine hh.congr fun m => eLpNorm_congr_ae ?_
    filter_upwards [ha m] with ω hω
    simp only [Pi.sub_apply, hω]
  refine ⟨Lp.memLp X, ?_⟩
  rw [Lp.toLp_coeFn]
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hconv (Eventually.of_forall hv)

/-- A centered product of retained first-chaos L² classes is in the scalar
second-chaos closure for the same sequence. -/
theorem fp81s21_firstChaos_centered_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (X Y : Lp ℝ 2 P) (hX : InFirstChaos P ξ 2 (fun ω => X ω))
    (hY : InFirstChaos P ξ 2 (fun ω => Y ω)) :
    InQ2 hξ (fun ω => X ω * Y ω - ∫ ω', X ω' * Y ω' ∂P) :=
  InQ2.mul_centered hξ hm (fp81s21_firstChaos_to_InQ1 hξ hm X hX)
    (fp81s21_firstChaos_to_InQ1 hξ hm Y hY)

/-- Every finite half-Wick polynomial formed from the retained first-chaos
source belongs to the scalar second-chaos closure. -/
theorem fp81s21_finite_halfWick_InQ2
    {d m : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (hsrc : ∀ f, InFirstChaos P ξ 2 (fun ω => (L f) ω))
    (u : Fin m → HRS.Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ) :
    InQ2 hξ (fp81s21_wickG_finite_rank_polynomial L u hu c) := by
  classical
  apply InQ2.const_mul
  apply InQ2.sum
  intro i hi
  apply InQ2.sum
  intro j hj
  exact InQ2.const_mul _ (fp81s21_firstChaos_centered_product hξ hm
    (L ((hu i).toLp (u i))) (L ((hu j).toLp (u j))) (hsrc _) (hsrc _))

/-- The supplied half-Wick operator maps every product L² kernel into the
second-chaos L² closure of the same retained standard Gaussian sequence. -/
theorem fp81s21_wick_operator_InQ2
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ) (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (hsrc : ∀ f, InFirstChaos P ξ 2 (fun ω => (L f) ω))
    (k : Lp ℝ 2 (μ.prod μ)) :
    InQ2 hξ (fun ω => fp81s21_wickG_operator L Kstar hL hJoint k ω) := by
  let E := (fp81s21_wickB39_linear L Kstar hL hJoint).extendOfNorm
    (fp81s21_wickB310_inclusion (μ := μ))
  have hclosed : ∀ y : fp81s21_wickB32_symmetricSubmodule μ, E y ∈ Qc (K2 hξ) := by
    apply isClosed_property fp81s21_wickB310_dense
      ((Submodule.isClosed_topologicalClosure (⨆ n, K2 hξ n)).preimage E.continuous)
    intro x
    rw [show E (fp81s21_wickB310_inclusion x) = _ from
      fp81s21_wickB311_extension_eq L Kstar hL hJoint x]
    let r := fp81s21_wickB38_choose μ x
    have hq := fp81s21_finite_halfWick_InQ2 hξ hm L hsrc r.u r.hu r.c
    obtain ⟨hqmem, hqclass⟩ := hq
    change fp81s21_wickB22_polynomialLp L Kstar hL hJoint r.u r.hu r.c ∈ Qc (K2 hξ)
    have heq : fp81s21_wickB22_polynomialLp L Kstar hL hJoint r.u r.hu r.c =
        hqmem.toLp (fp81s21_wickG_finite_rank_polynomial L r.u r.hu r.c) := by
      apply MemLp.toLp_congr
      exact Filter.EventuallyEq.rfl
    rw [heq]
    exact hqclass
  refine ⟨Lp.memLp _, ?_⟩
  rw [Lp.toLp_coeFn]
  exact hclosed (fp81s21_wickB310_symmetrize k)

#print axioms fp81s21_firstChaos_to_InQ1
#print axioms fp81s21_firstChaos_centered_product
#print axioms fp81s21_finite_halfWick_InQ2
#print axioms fp81s21_wick_operator_InQ2

end HRS.Fp81.S21
end
