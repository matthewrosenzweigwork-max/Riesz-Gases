import HRS.MS.S11Q2C5
import HRS.MS.S11Q2C4
import HRS.Whole.MovingDyn

/-!
# S11.3 Liouville (worker S11Q2), C6: path-space facts for the particle setup
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S11Q2

open HRS HRS.Whole

variable {d N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The noise values on the dyadic grids of `[0,t]`. -/
def s11q2_Vq (W : ℝ≥0 → Ω → (Fin N → Euc d)) (t : ℝ) (ζ : Ω) : ℕ × ℕ → EucConfig d N :=
  fun jk => W (((jk.1 : ℝ) * (t / 2 ^ jk.2)).toNNReal) ζ

theorem s11q2_W_cont {P : Measure Ω} {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hB : IsVectorBrownian P W) :
    ∀ᵐ ζ ∂P, Continuous fun t : ℝ≥0 => W t ζ := by
  have h1 : ∀ i j, ∀ᵐ ζ ∂P, Continuous fun t : ℝ≥0 => W t ζ i j := fun i j => (hB.1 i j).cont
  have h2 : ∀ᵐ ζ ∂P, ∀ i j, Continuous fun t : ℝ≥0 => W t ζ i j := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact h1 i
  filter_upwards [h2] with ζ hζ
  refine continuous_pi fun i => ?_
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => hζ i j) 

theorem s11q2_W_aemeasurable {P : Measure Ω} {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hB : IsVectorBrownian P W) (r : ℝ≥0) :
    AEMeasurable (W r) P := by
  refine aemeasurable_pi_iff.2 fun i => ?_
  have : AEMeasurable (fun ζ => fun j : Fin d => W r ζ i j) P :=
    aemeasurable_pi_iff.2 fun j => (hB.1 i j).toIsPreBrownianReal.aemeasurable r
  exact (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp_aemeasurable this

theorem s11q2_Vq_aemeasurable {P : Measure Ω} {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hB : IsVectorBrownian P W) (t : ℝ) :
    AEMeasurable (s11q2_Vq W t) P :=
  aemeasurable_pi_iff.2 fun jk => s11q2_W_aemeasurable hB _

theorem s11q2_indep {P : Measure Ω} [IsProbabilityMeasure P] {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → EucConfig d N} (hind : IndepFun X₀ (fun ζ t => W t ζ) P) (hinit : X 0 =ᵐ[P] X₀) (t : ℝ) :
    IndepFun (X 0) (s11q2_Vq W t) P := by
  have h1 := hind.congr hinit.symm (Filter.EventuallyEq.refl _ _)
  have hψ : Measurable (fun (w : ℝ≥0 → EucConfig d N) (jk : ℕ × ℕ) => w (((jk.1 : ℝ) * (t / 2 ^ jk.2)).toNNReal)) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  exact h1.comp measurable_id hψ

end HRS.MS.S11Q2

end
