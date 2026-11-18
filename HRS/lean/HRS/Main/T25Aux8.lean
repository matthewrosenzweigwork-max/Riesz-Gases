import HRS.Main.T25Aux1

/-!
# T25-IN, part 8: smooth distance and convolution with a fixed law (LIN-LAW, measure-theoretic half)

For the third conjunct of `prepared_fluctuations` (flag 1, TeX L781-782): the window law of a linear solution with initial law `ν` is
`Φ_*(ν ⊗ γ_a)`, `Φ(x,z) = V^{a+·,0}x + z`, with the SAME centred Gaussian `γ_a` for every `ν`.  Hence

`d₂(Φ_*(ν⊗γ), Φ_*(ν'⊗γ)) ≤ max(1,‖V^{a+·,0}‖²) d₂(ν,ν')`

from `t25_smoothDist_conv_le` (convolution with a fixed probability law does not increase `d₂`: Fubini + translation invariance of the
`C_b²` ball, `cbUnitBall_translate`) and `smoothDist_map_clm_le` (the contraction `Headline.lean:461`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace T25

/-- Convolution with a fixed probability law does not increase the smooth distance `d_2`. -/
theorem t25_smoothDist_conv_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (P Q γ : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure γ] :
    smoothDist 2 ((P.prod γ).map (fun p : B × B => p.1 + p.2))
        ((Q.prod γ).map (fun p : B × B => p.1 + p.2)) ≤ smoothDist 2 P Q := by
  have : Nonempty (CbUnitBall B 2) := ⟨⟨0, zero_mem_cbUnitBall 2⟩⟩
  refine Real.iSup_le (fun Φ => ?_) (smoothDist_nonneg 2 P Q)
  have hΦ : Φ.1 ∈ CbUnitBall B 2 := Φ.2
  have hc : Continuous Φ.1 := hΦ.1.continuous
  have hb : ∀ z, |Φ.1 z| ≤ 1 := fun z => abs_apply_le_of_mem hΦ z
  have hadd : Measurable (fun p : B × B => p.1 + p.2) := measurable_fst.add measurable_snd
  have hcomp : Continuous (fun p : B × B => Φ.1 (p.1 + p.2)) := hc.comp continuous_add
  have hint : ∀ (R : Measure B) [IsProbabilityMeasure R],
      Integrable (fun p : B × B => Φ.1 (p.1 + p.2)) (R.prod γ) := fun R _ =>
    Integrable.of_bound hcomp.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hb _)
  have e : ∀ (R : Measure B) [IsProbabilityMeasure R],
      ∫ z, Φ.1 z ∂((R.prod γ).map (fun p : B × B => p.1 + p.2)) =
        MeasureTheory.integral γ (fun y : B => MeasureTheory.integral R (fun x : B => Φ.1 (x + y))) := fun R _ => by
    rw [integral_map hadd.aemeasurable hc.aestronglyMeasurable]
    exact integral_prod_symm (fun p : B × B => Φ.1 (p.1 + p.2)) (hint R)
  rw [e P, e Q, ← integral_sub (Integrable.integral_prod_right (hint P))
    (Integrable.integral_prod_right (hint Q))]
  have hbd : ∀ y : B, ‖∫ (x : B), Φ.1 (x + y) ∂P - ∫ (x : B), Φ.1 (x + y) ∂Q‖ ≤ smoothDist 2 P Q := fun y => by
    rw [Real.norm_eq_abs]
    exact abs_integral_sub_le_smoothDist (cbUnitBall_translate hΦ y) P Q
  have := norm_integral_le_of_norm_le_const (μ := γ)
    (f := fun y : B => ∫ (x : B), Φ.1 (x + y) ∂P - ∫ (x : B), Φ.1 (x + y) ∂Q) (C := smoothDist 2 P Q)
    (Filter.Eventually.of_forall hbd)
  simpa [Real.norm_eq_abs] using this

/-- `Φ(x,z) = L x + z`: `d₂(Φ_*(ν⊗γ), Φ_*(ν'⊗γ)) ≤ max(1, ‖L‖²) d₂(ν, ν')` for a bounded linear `L : B' → B`. -/
theorem t25_smoothDist_affine_le {B' B : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B']
    [MeasurableSpace B'] [BorelSpace B'] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (L : B' →L[ℝ] B) (ν ν' : Measure B') (γ : Measure B) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] [IsProbabilityMeasure γ] :
    smoothDist 2 ((ν.prod γ).map (fun p : B' × B => L p.1 + p.2))
        ((ν'.prod γ).map (fun p : B' × B => L p.1 + p.2)) ≤ max 1 (‖L‖ ^ 2) * smoothDist 2 ν ν' := by
  have hLm : Measurable L := L.continuous.measurable
  have e : ∀ (R : Measure B') [IsProbabilityMeasure R],
      (R.prod γ).map (fun p : B' × B => L p.1 + p.2) =
        ((R.map L).prod γ).map (fun p : B × B => p.1 + p.2) := fun R _ => by
    have h1 : (R.map L).prod γ = (R.prod γ).map (Prod.map L id) := by
      rw [← Measure.map_prod_map R γ hLm measurable_id]
      simp
    have hadd : Measurable (fun p : B × B => p.1 + p.2) := measurable_fst.add measurable_snd
    rw [h1, Measure.map_map hadd (hLm.prodMap measurable_id)]
    rfl
  rw [e ν, e ν']
  haveI : IsProbabilityMeasure (ν.map L) := (Measure.isProbabilityMeasure_map_iff hLm.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (ν'.map L) := (Measure.isProbabilityMeasure_map_iff hLm.aemeasurable).2 inferInstance
  exact (t25_smoothDist_conv_le (ν.map L) (ν'.map L) γ).trans (HRS.Main.smoothDist_map_clm_le L 2 ν ν')

end T25

end HRS

end
