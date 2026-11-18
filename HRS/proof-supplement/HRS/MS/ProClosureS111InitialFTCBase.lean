import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Time measurability and Bochner FTC from an actual Banach-valued derivative.
The two endpoint values are retained explicitly; no arbitrary derivative
representative is substituted for the prescribed derivative on the interval.
-/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Topology Set

namespace HRS.MS.ProClosureS111

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem derivative_on_Icc_stronglyMeasurable
    (F G : ℝ → E) (T : ℝ)
    (hder : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt F (G t) t) :
    StronglyMeasurable (fun t : Icc (0 : ℝ) T => G t) ∧
      AEStronglyMeasurable G (volume.restrict (Icc (0 : ℝ) T)) := by
  let H : ℝ → E := fun t => if t = 0 then G 0 else if t = T then G T else deriv F t
  have hH : StronglyMeasurable H := by
    apply StronglyMeasurable.ite (measurableSet_singleton (0 : ℝ))
      stronglyMeasurable_const
    exact StronglyMeasurable.ite (measurableSet_singleton T)
      stronglyMeasurable_const (stronglyMeasurable_deriv F)
  have heq : ∀ t ∈ Icc (0 : ℝ) T, H t = G t := by
    intro t ht
    dsimp [H]
    by_cases h0 : t = 0
    · simp [h0]
    by_cases hT : t = T
    · rw [if_neg h0, if_pos hT, hT]
    simp only [h0, hT, if_false]
    exact (hder t ⟨lt_of_le_of_ne ht.1 (Ne.symm h0),
      lt_of_le_of_ne ht.2 hT⟩).deriv
  constructor
  · have hm := hH.comp_measurable (measurable_subtype_coe :
        Measurable (fun t : Icc (0 : ℝ) T => (t : ℝ)))
    have hf : (H ∘ fun t : Icc (0 : ℝ) T => (t : ℝ)) =
        (fun t : Icc (0 : ℝ) T => G t) :=
      funext fun t => heq t t.property
    rw [hf] at hm
    exact hm
  · exact hH.aestronglyMeasurable.congr
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht => heq t ht)

theorem bounded_derivative_Icc_FTC
    (F G : ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn F (Icc (0 : ℝ) T))
    (hder : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt F (G t) t)
    (B : ℝ) (hbound : ∀ t ∈ Icc (0 : ℝ) T, ‖G t‖ ≤ B) :
    StronglyMeasurable (fun t : Icc (0 : ℝ) T => G t) ∧
      IntegrableOn G (Icc (0 : ℝ) T) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        F t = F 0 + ∫ v in Icc (0 : ℝ) t, G v := by
  obtain ⟨hsm, haesm⟩ := derivative_on_Icc_stronglyMeasurable F G T hder
  have hint : IntegrableOn G (Icc (0 : ℝ) T) := by
    refine (integrable_const B).mono' haesm ?_
    exact (ae_restrict_mem measurableSet_Icc).mono fun t ht => hbound t ht
  refine ⟨hsm, hint, ?_⟩
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl ht.2
  have hii : IntervalIntegrable G volume 0 t := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hint.mono_set hsub
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hcont.mono hsub)
    (fun x hx => hder x ⟨hx.1, hx.2.trans_le ht.2⟩) hii
  rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc] at hFTC
  rw [hFTC]
  abel

#print axioms derivative_on_Icc_stronglyMeasurable
#print axioms bounded_derivative_Icc_FTC

end HRS.MS.ProClosureS111
