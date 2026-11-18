import HRS.MS.Fp81S21CovCumulative2

/-! The horizon extension preserves each physical covariance specification. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- An interval covariance specified using a field is also specified using its
zero extension outside the horizon. The tensor itself is unchanged. -/
theorem fp81s21_JValue_horizonFieldExtension {d : ℕ} {m H : ℝ}
    (C : WholeCoeff d) (z : ℝ → (Euc d → ℝ) → ℝ) (I : Set ℝ)
    {J : TensorDual (OscPath d m H) 2}
    (hJ : IsR2JValue C m H z I J) :
    IsR2JValue C m H (fp81s21_horizonFieldExtension H z) I J := by
  refine ⟨hJ.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  have hInt :
      (∫ u in I ∩ Icc (0 : ℝ) (min ta tb),
        fp81s21_horizonFieldExtension H z u (fun x => inner ℝ
          (gradient (propagatorW C u ta φa) x)
          (gradient (propagatorW C u tb φb) x))) =
      ∫ u in I ∩ Icc (0 : ℝ) (min ta tb),
        z u (fun x => inner ℝ
          (gradient (propagatorW C u ta φa) x)
          (gradient (propagatorW C u tb φb) x)) := by
    apply integral_congr_ae
    have hmem : ∀ᵐ u ∂volume.restrict (I ∩ Icc (0 : ℝ) (min ta tb)),
        u ∈ Icc (0 : ℝ) (min ta tb) :=
      ae_mono (Measure.restrict_mono inter_subset_right le_rfl)
        (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hmem] with u hu
    exact fp81s21_horizonFieldExtension_eq H z
      ⟨hu.1, hu.2.trans ((min_le_left _ _).trans hta.2)⟩ _
  rw [hInt]
  exact hJ.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_JValue_horizonFieldExtension
