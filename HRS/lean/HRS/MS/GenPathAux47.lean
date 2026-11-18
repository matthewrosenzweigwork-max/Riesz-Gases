import HRS.MS.GenPathAux46

/-!
# S5.6 packet P8f: laws of coordinate arrays from finite-dimensional laws; the oscillator test functions
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.Uniform.Q54c

variable {d : ℕ}

/-- The laws of two coordinate arrays agree if all finite subfamilies (indexed by `Fin p`) have the same law. -/
theorem s56_seq_law_eq {ι : Type*} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Ψ : Ω → (ι → ℝ)) (Ψ' : Ω' → (ι → ℝ)) (hm : AEMeasurable Ψ P) (hm' : AEMeasurable Ψ' P')
    (h : ∀ (p : ℕ) (f : Fin p → ι), Function.Injective f →
      P.map (fun ζ => (WithLp.toLp 2 fun a => Ψ ζ (f a) : EuclideanSpace ℝ (Fin p))) =
        P'.map (fun ζ => (WithLp.toLp 2 fun a => Ψ' ζ (f a) : EuclideanSpace ℝ (Fin p)))) :
    P.map Ψ = P'.map Ψ' := by
  refine measure_ext_of_restrict fun J => ?_
  have hr : Measurable (J.restrict : (ι → ℝ) → (J → ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply (i : ι)
  rw [AEMeasurable.map_map_of_aemeasurable hr.aemeasurable hm,
    AEMeasurable.map_map_of_aemeasurable hr.aemeasurable hm']
  classical
  let e : J ≃ Fin J.card := J.equivFin
  set f : Fin J.card → ι := fun a => ((e.symm a : J) : ι) with hf
  have hinj : Function.Injective f := fun a b hab => e.symm.injective (Subtype.ext hab)
  have hf1 := h J.card f hinj
  have hre : Measurable (fun (v : EuclideanSpace ℝ (Fin J.card)) (j : J) => v (e j)) :=
    measurable_pi_iff.2 fun j => (measurable_pi_apply (e j)).comp (PiLp.continuous_ofLp 2 _).measurable
  have hv : (J.restrict ∘ Ψ) = (fun (v : EuclideanSpace ℝ (Fin J.card)) (j : J) => v (e j)) ∘
      (fun ζ => (WithLp.toLp 2 fun a => Ψ ζ (f a) : EuclideanSpace ℝ (Fin J.card))) := by
    funext ζ j
    simp [hf, Function.comp, Finset.restrict]
  have hv' : (J.restrict ∘ Ψ') = (fun (v : EuclideanSpace ℝ (Fin J.card)) (j : J) => v (e j)) ∘
      (fun ζ => (WithLp.toLp 2 fun a => Ψ' ζ (f a) : EuclideanSpace ℝ (Fin J.card))) := by
    funext ζ j
    simp [hf, Function.comp, Finset.restrict]
  have hmv : AEMeasurable (fun ζ => (WithLp.toLp 2 fun a => Ψ ζ (f a) : EuclideanSpace ℝ (Fin J.card))) P :=
    (PiLp.continuous_toLp 2 (fun _ : Fin J.card => ℝ)).measurable.comp_aemeasurable
      (aemeasurable_pi_iff.2 fun a => (measurable_pi_apply (f a)).comp_aemeasurable hm)
  have hmv' : AEMeasurable (fun ζ => (WithLp.toLp 2 fun a => Ψ' ζ (f a) : EuclideanSpace ℝ (Fin J.card))) P' :=
    (PiLp.continuous_toLp 2 (fun _ : Fin J.card => ℝ)).measurable.comp_aemeasurable
      (aemeasurable_pi_iff.2 fun a => (measurable_pi_apply (f a)).comp_aemeasurable hm')
  rw [hv, hv', ← AEMeasurable.map_map_of_aemeasurable hre.aemeasurable hmv,
    ← AEMeasurable.map_map_of_aemeasurable hre.aemeasurable hmv', hf1]

theorem s56_isOscTest (m : ℝ) (α : MultiIndex d) : IsOscTest m (oscTestFun m α) := by
  refine ⟨contDiff_const.mul (contDiff_hermiteFunD α), ?_, ?_⟩
  · have := (memLp_hermiteFunD α).const_mul (oscEigenvalue d α ^ (-(m / 2)))
    exact this
  · refine summable_of_ne_finset_zero (s := {α}) fun β hβ => ?_
    rw [hermiteCoeff_oscTestFun, if_neg (by simpa using Ne.symm (by simpa using hβ))]
    simp

end HRS.MS.GenPath
