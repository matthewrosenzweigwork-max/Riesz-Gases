import HRS.MS.R26T8AB00m

/-!
# S8.2 observed-time layer, packet T8A.B00a (helper a): a.e. Fubini transfer of the fundamental theorem of calculus

From the almost-everywhere-on-the-product statement `hFTC`, for almost every `w` the identity holds for almost every `r`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b00a_ae_ftc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] (l h T : ℝ)
    (V Vd : ℝ → ℝ → Ω → ℝ)
    (hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc l h)).prod P),
      IntegrableOn (fun v => Vd v p.1 p.2) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, V t p.1 p.2 = V 0 p.1 p.2 + ∫ v in Set.Icc 0 t, Vd v p.1 p.2) :
    ∀ᵐ w ∂P, ∀ᵐ r ∂(volume.restrict (Set.Icc l h)),
      IntegrableOn (fun v => Vd v r w) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, V t r w = V 0 r w + ∫ v in Set.Icc 0 t, Vd v r w := by
  have hsw := (Measure.measurePreserving_swap (μ := P) (ν := volume.restrict (Set.Icc l h))).quasiMeasurePreserving.ae hFTC
  exact Measure.ae_ae_of_ae_prod hsw

end HRS.MS.R26T8A

end
