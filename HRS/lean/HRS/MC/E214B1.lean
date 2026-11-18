import HRS.MC.E214B

/-!
# Packet e214b (part 1): the expansion instantiated at one system, and `E cos (t Y) → 1`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E214B

open HRS HRS.Main

variable {d : ℕ}

/-- The integral identity: pairing the constant direction with a tensor pulls the tensor out. -/
theorem integral_tensor_iteratedFDeriv_sin {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Dv : TensorDual B 3) (L : StrongDual ℝ B)
    (c : ℝ) (f : Ω → B) :
    ∫ ω, Dv (iteratedFDeriv ℝ 3 (fun z => c * Real.sin (L z)) (f ω)) ∂P =
      Dv (trilin ![L, L, L]) * ∫ ω, -(c * Real.cos (L (f ω))) ∂P := by
  simp_rw [iteratedFDeriv_three_const_mul_sin, map_smul, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext ω; ring

/-- `E cos (t Y) → 1` as `t → 0`. -/
theorem tendsto_integral_cos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) :
    Tendsto (fun t : ℝ => ∫ ω, Real.cos (t * Y ω) ∂P) (𝓝 0) (𝓝 1) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := 𝓝 (0 : ℝ))
    (F := fun (t : ℝ) ω => Real.cos (t * Y ω)) (f := fun _ => (1 : ℝ)) (bound := fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun t =>
      (Real.measurable_cos.comp_aemeasurable (aemeasurable_const.mul hY)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun ω => by
      simpa using Real.abs_cos_le_one _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun ω => by
      have : Continuous fun t : ℝ => Real.cos (t * Y ω) :=
        Real.continuous_cos.comp (continuous_id.mul continuous_const)
      simpa using this.tendsto 0)
  simpa using h

/-- The window of a prepared linear solution is a.e. measurable. -/
theorem windowPath_aemeasurable (S : PreparedData d) (m T a : ℝ) (ha : 0 ≤ a)
    (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsPreparedLinear S m (a + T) ν P' Z₀ Z) :
    AEMeasurable (windowPath m T a Z) P' := by
  refine HRS.AdjK.adjk_toPath_aemeasurable_proof P' m T (fun t => Z (a + t))
    (fun t => hZ.sol.meas (a + t)) ?_
  filter_upwards [hZ.sol.cont] with ω hω
  refine hω.comp (continuous_const.add continuous_id).continuousOn ?_
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

end HRS.MC.E214B
