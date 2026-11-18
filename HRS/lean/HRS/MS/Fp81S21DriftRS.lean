import HRS.MS.Fp81S21RSValue4
import HRS.MS.R2InterpAux23

/-! Literal scalar measurability for derivative kernels and measurable sections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
namespace HRS.Fp81.S21

/-- A derivative kernel has measurable scalar evaluations at all real times.
Strong measurability of the sections avoids requiring the operator dual to be
separable. -/
theorem fp81s21_derivative_increment_measurable
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ → E → ℝ) (Y F : Ω → ℝ → E)
    (hu : ∀ τ, ContDiff ℝ 1 (u τ))
    (hY : ∀ τ, StronglyMeasurable (fun ω => Y ω τ))
    (hF : ∀ t, StronglyMeasurable (fun ω => F ω t)) :
    ∀ τ a b, Measurable (fun ω => fderiv ℝ (u τ) (Y ω τ) (F ω b - F ω a)) := by
  intro τ a b
  have hD : Continuous (fderiv ℝ (u τ)) :=
    (hu τ).continuous_fderiv (by norm_num)
  have hC : Continuous (fun z : E × E => fderiv ℝ (u τ) z.1 z.2) :=
    (hD.comp continuous_fst).clm_apply continuous_snd
  exact (hC.comp_stronglyMeasurable ((hY τ).prodMk ((hF b).sub (hF a)))).measurable

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_derivative_increment_measurable
