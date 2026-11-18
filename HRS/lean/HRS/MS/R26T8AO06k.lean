import HRS.MS.R26T8AO06j

/-!
# S8.2 T8A O06 (part k): additivity of closed-interval integrals
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
namespace HRS.MS.R26T8A

theorem r26t8a_o06_icc_split {f : ℝ → ℝ} {l h : ℝ} (hl : 0 ≤ l) (hlh : l ≤ h)
    (hf : IntegrableOn f (Set.Icc 0 h)) :
    ∫ s in Set.Icc 0 h, f s = (∫ s in Set.Icc 0 l, f s) + ∫ s in Set.Icc l h, f s := by
  have hsub1 : Set.Icc 0 l ⊆ Set.Icc 0 h := Set.Icc_subset_Icc_right hlh
  have hsub2 : Set.Icc l h ⊆ Set.Icc 0 h := Set.Icc_subset_Icc_left hl
  have hu : Set.Icc 0 h = Set.Icc 0 l ∪ Set.Ioc l h := (Set.Icc_union_Ioc_eq_Icc hl hlh).symm
  have hd : Disjoint (Set.Icc (0 : ℝ) l) (Set.Ioc l h) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.2 hx'.1)
  rw [hu, setIntegral_union hd measurableSet_Ioc (hf.mono_set hsub1) (hf.mono_set (Set.Ioc_subset_Icc_self.trans hsub2))]
  rw [integral_Icc_eq_integral_Ioc (f := f) (x := l) (y := h)]

end HRS.MS.R26T8A

end
