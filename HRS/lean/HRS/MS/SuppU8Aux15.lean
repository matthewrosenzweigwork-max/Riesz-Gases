import HRS.MS.SuppU8Aux14
import HRS.MS.SuppU8Aux8

/-!
# Worker U8 aux 15: the core theorem (existence of the fractional derivative of a decaying function)
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HRS.U8

variable {d : ℕ}

theorem u8_Lam_aesm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) (α : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → E) (hu : Continuous u) :
    AEStronglyMeasurable (fun x => ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) u x) := by
  have hKm : Measurable (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ (-((d : ℝ) + α))) :=
    measurable_norm.pow_const _
  have hc : Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      u8_fd (u8_L m p.2) u p.1) := (u8_L_cont_joint m hu).comp continuous_swap
  have hm : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ‖p.2‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m p.2) u p.1)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) :=
    (hKm.comp measurable_snd).aestronglyMeasurable.smul hc.aestronglyMeasurable
  exact hm.integral_prod_right'

/-- Constants for a Schwartz test function. -/
theorem u8_d_param (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    ∃ b'' : ℝ, 0 < b'' ∧ b'' < d ∧ (d : ℝ) < b'' + α := by
  refine ⟨(d : ℝ) - min α d / 2, ?_, ?_, ?_⟩
  · have : (0 : ℝ) < d := by exact_mod_cast hd
    have h1 : min α d ≤ d := min_le_right _ _
    linarith
  · have h1 : 0 < min α (d : ℝ) := lt_min hα (by exact_mod_cast hd)
    linarith
  · have h1 : min α (d : ℝ) ≤ α := min_le_left _ _
    have h2 : 0 < min α (d : ℝ) := lt_min hα (by exact_mod_cast hd)
    linarith

end HRS.U8
