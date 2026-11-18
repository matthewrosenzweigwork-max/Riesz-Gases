import HRS.Prob.MRepAux12

/-!
# MREP, part 13: the product enlargement
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section Prod

open Classical

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type u} [Countable ι]

lemma prodFiltration_complete (P₁ : Measure Ω) [IsProbabilityMeasure P₁] (ℱ₁ : Filtration ℝ mΩ) :
    IsCompleteFiltration (P₁.prod (wMeasure ι))
      (prodFiltration P₁ (wMeasure ι) ℱ₁ (wFiltration ι)) := by
  intro t S hS hP
  have h1 : MeasurableSet[nullSets (P₁.prod (wMeasure ι))] S :=
    MeasurableSpace.measurableSet_generateFrom ⟨hS, hP⟩
  exact (le_sup_right : nullSets (P₁.prod (wMeasure ι)) ≤
    prodFiltration P₁ (wMeasure ι) ℱ₁ (wFiltration ι) t) S h1

/-- A martingale of the base space is a martingale of the product. -/
lemma martingale_fst {ℱ₁ : Filtration ℝ mΩ} {F : ℝ → Ω → ℝ} (hF : Martingale F ℱ₁ P) :
    Martingale (fun t (p : Ω × (ι → WienerSeq)) => F t p.1)
      (prodFiltration P (wMeasure ι) ℱ₁ (wFiltration ι)) (P.prod (wMeasure ι)) := by
  have := martingale_mul_prod (P₁ := P) (P₂ := wMeasure ι) ℱ₁ (wFiltration ι) hF
    (martingale_const (wFiltration ι) (wMeasure ι) (1 : ℝ))
  convert this using 2 with t p
  simp

/-- The product of a base martingale with a Wiener coordinate. -/
lemma martingale_fst_mul_wiener {ℱ₁ : Filtration ℝ mΩ} {F : ℝ → Ω → ℝ} (hF : Martingale F ℱ₁ P)
    (j : ι) :
    Martingale (fun t (p : Ω × (ι → WienerSeq)) =>
      F t p.1 * ofNNRealTime (fun t (p : Ω × (ι → WienerSeq)) (i : ι) => wienerPath t (p.2 i)) t p j)
      (prodFiltration P (wMeasure ι) ℱ₁ (wFiltration ι)) (P.prod (wMeasure ι)) := by
  have hW₂ : IsCylindricalBrownian (wMeasure ι) (wFiltration ι)
      (fun t (ω : ι → WienerSeq) (i : ι) => wienerPath t (ω i)) :=
    fun F => isBrownianFiltration_wFiltration F
  have := martingale_mul_prod (P₁ := P) (P₂ := wMeasure ι) ℱ₁ (wFiltration ι) hF
    (hW₂.martingale_coord j)
  convert this using 2 with t p
  simp [ofNNRealTime_apply]

/-- The Wiener coordinates form a cylindrical Brownian motion for the product filtration. -/
theorem isCylindricalBrownian_wiener_prod (ℱ₁ : Filtration ℝ mΩ) :
    IsCylindricalBrownian (P.prod (wMeasure ι))
      (prodFiltration P (wMeasure ι) ℱ₁ (wFiltration ι))
      (fun t (p : Ω × (ι → WienerSeq)) (i : ι) => wienerPath t (p.2 i)) := by
  have hW₂ : IsCylindricalBrownian (wMeasure ι) (wFiltration ι)
      (fun t (ω : ι → WienerSeq) (i : ι) => wienerPath t (ω i)) :=
    fun F => isBrownianFiltration_wFiltration F
  refine isCylindricalBrownian_of_coords (prodFiltration_complete P ℱ₁) (fun t k => ?_)
    (fun p k => ?_) (fun p k => ?_) (fun k => ?_) (fun k l => ?_)
  · exact comap_snd_le_prod (P₁ := P) (P₂ := wMeasure ι) (ℱ₁ := ℱ₁) (ℱ₂ := wFiltration ι)
      (f := fun ω : ι → WienerSeq => wienerPath t (ω k)) (t := t) (hW₂.measurable_coord t k) |>
      fun h => Measurable.of_comap_le h
  · exact congrFun ((hW₂ {k}).zero p.2) ⟨k, by simp⟩
  · exact (continuous_apply (⟨k, by simp⟩ : ({k} : Finset ι))).comp ((hW₂ {k}).cont p.2)
  · have := martingale_fst_mul_wiener (P := P) (ℱ₁ := ℱ₁) (martingale_const ℱ₁ P (1 : ℝ)) k
    convert this using 2 with t p
    simp
  · have := martingale_mul_prod (P₁ := P) (P₂ := wMeasure ι) ℱ₁ (wFiltration ι)
      (martingale_const ℱ₁ P (1 : ℝ)) (hW₂.martingale_mul_sub k l)
    convert this using 2 with t p
    simp [ofNNRealTime_apply]

end Prod

end HRS.MRep
