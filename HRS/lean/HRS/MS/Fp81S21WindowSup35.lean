import HRS.MS.Fp81S21WindowSup34

/-! Fubini integrability on restricted time intervals. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
namespace HRS.Fp81.S21

/-- A measurable extension with uniform sixth moments gives product and mean
integrability for the original family on every subinterval. -/
theorem fp81s21_fubini_on_interval_of_sixth
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T)
    (F G : ℝ × Ω → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hSix : ∀ u : ℝ, SixthBound P (fun ω => F (u, ω)) M)
    (hEq : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, F (u, ω) = G (u, ω)) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      Integrable (fun z : Ω × ℝ => G (z.2, z.1))
        (P.prod (volume.restrict (Ioc (0 : ℝ) τ))) ∧
      IntervalIntegrable (fun u => ∫ ω, G (u, ω) ∂P) volume 0 τ := by
  have hprod : Integrable F ((volume.restrict (Icc (0 : ℝ) T)).prod P) :=
    fp81s21_sixth_slices_product_integrable _ P F hF M hM hSix
  intro τ hτ
  have hmono : (volume.restrict (Icc (0 : ℝ) τ)).prod P ≤
      (volume.restrict (Icc (0 : ℝ) T)).prod P :=
    Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc_right hτ.2) le_rfl) le_rfl
  have hae : F =ᵐ[(volume.restrict (Icc (0 : ℝ) τ)).prod P] G := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
    exact hEq z.1 ⟨hz.1, hz.2.trans hτ.2⟩ z.2
  have hraw : Integrable G ((volume.restrict (Icc (0 : ℝ) τ)).prod P) :=
    (hprod.mono_measure hmono).congr hae
  constructor
  · have hIoc : Integrable G ((volume.restrict (Ioc (0 : ℝ) τ)).prod P) :=
      hraw.mono_measure (Measure.prod_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) le_rfl)
    exact hIoc.swap
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1).2
    exact hraw.integral_prod_left

#print axioms fp81s21_fubini_on_interval_of_sixth
end HRS.Fp81.S21
end
