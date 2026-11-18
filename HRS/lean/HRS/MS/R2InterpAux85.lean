import HRS.MS.R2InterpAux84

/-!
# S10.2 (worker S10R), part 85 (packet F5e): the Itô integrand of the duality identity is bounded and progressive
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {C : WholeCoeff d}

theorem s102_prog_comp {Ω E γ : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [MeasurableSpace γ]
    {ℱ : Filtration ℝ mΩ} {V : ℝ × E → γ} (hV : Measurable V) {Xp : ℝ → Ω → E} (hXp : IsProgressive ℱ Xp) :
    IsProgressive ℱ (fun r ζ => V (r, Xp r ζ)) := by
  intro i
  exact hV.comp ((measurable_subtype_coe.comp measurable_fst).prodMk (hXp i))

/-- The integrand of the Itô integral in `DualityIdentityRd`. -/
def s102_Ig {N : ℕ} {Ω : Type*} (f : ℝ → Euc d → ℝ) (t : ℝ) (X : ℝ≥0 → Ω → EucConfig d N) :
    ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then gradComp ia.2 (f r) (X (Real.toNNReal r) ζ' ia.1) else 0

theorem s102_Ig_progressive {N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ} {t : ℝ}
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : IsProgressive ℱ (ofNNRealTime X)) : IsProgressive ℱ (s102_Ig f t X) := by
  intro i
  refine (@measurable_pi_iff _ _ _ (Subtype.instMeasurableSpace.prod (ℱ i)) _).2 fun ia => ?_
  have hXa : IsProgressive ℱ (fun r ζ => (ofNNRealTime X r ζ) ia.1) :=
    fun j => (measurable_pi_apply ia.1).comp (hX j)
  have hV : Measurable fun p : ℝ × Euc d =>
      (if p.1 ∈ Icc (0 : ℝ) t then gradient (f p.1) p.2 else 0 : Euc d) ia.2 :=
    (EuclideanSpace.proj ia.2).continuous.measurable.comp (s102_gradJoint_meas hf)
  have := s102_prog_comp (ℱ := ℱ) hV hXa i
  have e : (fun p : Set.Iic i × Ω => s102_Ig f t X p.1 p.2 ia) =
      fun p : Set.Iic i × Ω => (fun r ζ => (if (r, (ofNNRealTime X r ζ) ia.1).1 ∈ Icc (0 : ℝ) t then
        gradient (f (r, (ofNNRealTime X r ζ) ia.1).1) (r, (ofNNRealTime X r ζ) ia.1).2 else 0 : Euc d) ia.2) p.1 p.2 := by
    funext p
    simp only [s102_Ig, gradComp, ofNNRealTime_apply]
    split_ifs <;> simp
  rw [e]
  exact this

theorem s102_Ig_bdd {N : ℕ} {Ω : Type*} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (X : ℝ≥0 → Ω → EucConfig d N) :
    ∃ B : ℝ, ∀ r ζ ia, |s102_Ig f t X r ζ ia| ≤ B := by
  obtain ⟨B, hB⟩ := s102_grad_bdd hf
  refine ⟨max B 0, fun r ζ ia => ?_⟩
  unfold s102_Ig
  split_ifs with h
  · exact (hB r h _ _).trans (le_max_left _ _)
  · simp

end HRS.MS.R2Interp

end
