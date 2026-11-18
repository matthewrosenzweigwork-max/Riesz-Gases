import HRS.MS.S21G2_S12A
import HRS.Prob.Metrics

/-!
# S21G2 S12 (part B) -- vector CLT for the i.i.d. coordinates via Cramer-Wold (R26-T3.S12)

For `ψ : E → ℝ^ι` measurable with mean-zero `L²` components and a centred Gaussian vector `Z'` with the same second moments,
`(√N)⁻¹ ∑_{k<N} ψ(ω_k) → Z'` in distribution.  Helper names carry the prefix `s21g2_s12_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3

theorem s21g2_s12_vclt {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {ψ : E → EuclideanSpace ℝ ι} (hψ : Measurable ψ)
    (h2 : ∀ i, MemLp (fun x => ψ x i) 2 μ) (h0 : ∀ i, ∫ x, ψ x i ∂μ = 0)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z' : Ω' → EuclideanSpace ℝ ι} (hZ : AEMeasurable Z' P')
    (hG : HRS.IsCenteredGaussian (P'.map Z'))
    (hcov : ∀ t : EuclideanSpace ℝ ι, ∫ ω, ⟪Z' ω, t⟫ ^ 2 ∂P' = ∫ x, ⟪ψ x, t⟫ ^ 2 ∂μ) :
    TendstoInDistribution (fun (N : ℕ) (ω : ℕ → E) => (Real.sqrt N)⁻¹ • ∑ k ∈ Finset.range N, ψ (ω k))
      atTop Z' (fun _ => Measure.infinitePi fun _ : ℕ => μ) P' := by
  have hm : ∀ N : ℕ, AEMeasurable (fun ω : ℕ → E => (Real.sqrt N)⁻¹ • ∑ k ∈ Finset.range N, ψ (ω k))
      (Measure.infinitePi fun _ : ℕ => μ) := fun N => by
    have hs : Measurable (fun ω : ℕ → E => ∑ k ∈ Finset.range N, ψ (ω k)) :=
      Finset.measurable_sum _ fun k _ => hψ.comp (measurable_pi_apply k)
    exact (hs.const_smul (Real.sqrt N)⁻¹).aemeasurable
  refine (tendstoInDistribution_iff_tendstoInDistribution_inner hZ hm).2 fun t => ?_
  set g : E → ℝ := fun x => ⟪ψ x, t⟫ with hg
  have hgm : Measurable g := hψ.inner measurable_const
  have hgl : ∀ x, g x = ∑ i, t i * ψ x i := fun x => by
    simp only [hg, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]; simp [mul_comm]
  have hg2 : MemLp g 2 μ := by
    have : g = fun x => ∑ i, t i * ψ x i := funext hgl
    rw [this]
    exact memLp_finsetSum (f := fun i x => t i * ψ x i) _ fun i _ => (h2 i).const_mul _
  have hg0 : ∫ x, g x ∂μ = 0 := by
    have : g = fun x => ∑ i, t i * ψ x i := funext hgl
    rw [this, integral_finsetSum _ fun i _ => ((h2 i).integrable one_le_two).const_mul _]
    simp [integral_const_mul, h0]
  have hY : HasLaw (fun ω => ⟪Z' ω, t⟫) (gaussianReal 0 (Real.toNNReal (∫ x, g x ^ 2 ∂μ))) P' := by
    have hGa := hG.1
    have hmap := hGa.map_eq_gaussianReal (innerSL ℝ t)
    have hmean : ∫ z, (innerSL ℝ t) z ∂(P'.map Z') = 0 := hG.2 _
    have hZi : AEMeasurable (fun ω => ⟪Z' ω, t⟫) P' := hZ.inner aemeasurable_const
    refine ⟨hZi, ?_⟩
    have hmm : P'.map (fun ω => ⟪Z' ω, t⟫) = (P'.map Z').map (innerSL ℝ t) :=
      by rw [AEMeasurable.map_map_of_aemeasurable (innerSL ℝ t).continuous.measurable.aemeasurable hZ]
         congr 1; funext ω; simp [real_inner_comm]
    have hL : ∀ z, (innerSL ℝ t) z = ⟪z, t⟫ := fun z => by simp [real_inner_comm]
    have hvar : Var[fun z => (innerSL ℝ t) z; P'.map Z'] = ∫ x, g x ^ 2 ∂μ := by
      rw [variance_of_integral_eq_zero (innerSL ℝ t).continuous.measurable.aemeasurable hmean]
      have := integral_map (μ := P') (φ := Z') (f := fun z => ((innerSL ℝ t) z) ^ 2) hZ
        ((innerSL ℝ t).continuous.measurable.pow_const 2).aestronglyMeasurable
      rw [this]
      simp_rw [hL]
      exact hcov t
    rw [hmm, hmap, hmean]
    congr 2
  have := s21g2_s12_clt μ hgm hg2 hg0 hY
  refine TendstoInDistribution.congr (fun N => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl) this
  simp only [inner_smul_left, sum_inner, hg]
  simp

end HRS.MS.R26T3
