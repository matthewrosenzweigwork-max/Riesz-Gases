import HRS.Uniform.Q45Lim2

/-!
# Q45: generic estimates for `C_b²` test functions on path-valued random variables
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-- Test functions of the `C_b²` unit ball are `1`-Lipschitz. -/
lemma cbUnit_lipschitz {Φ : W → ℝ} (hΦ : Φ ∈ CbUnitBall W 2) (a b : W) : |Φ a - Φ b| ≤ ‖a - b‖ := by
  obtain ⟨hc, -, hd, -⟩ := cbUnit_bounds hΦ
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := Φ) (𝕜 := ℝ) (s := Set.univ)
    (fun x _ => (hc.differentiable (by norm_num)) x) (fun x _ => hd x) convex_univ
    (Set.mem_univ b) (Set.mem_univ a)
  rw [Real.norm_eq_abs, one_mul] at this
  exact this

lemma integrable_cb_comp {Φ : W → ℝ} (hΦ : Φ ∈ CbUnitBall W 2) {F : Ω → W} (hF : AEMeasurable F P) :
    Integrable (fun ω => Φ (F ω)) P := by
  obtain ⟨hc, hb, -, -⟩ := cbUnit_bounds hΦ
  exact Integrable.of_bound (hc.continuous.measurable.comp_aemeasurable hF).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb _)

/-- Two path-valued random variables that are close in `L¹` have close `C_b²` expectations. -/
lemma cb_integral_diff_le {Φ : W → ℝ} (hΦ : Φ ∈ CbUnitBall W 2) {F₁ F₂ : Ω → W}
    (h₁ : AEMeasurable F₁ P) (h₂ : AEMeasurable F₂ P)
    (hfin : ∫⁻ ω, ‖F₁ ω - F₂ ω‖ₑ ∂P ≠ ⊤) :
    |∫ ω, Φ (F₁ ω) ∂P - ∫ ω, Φ (F₂ ω) ∂P| ≤ (∫⁻ ω, ‖F₁ ω - F₂ ω‖ₑ ∂P).toReal := by
  have i1 := integrable_cb_comp P hΦ h₁
  have i2 := integrable_cb_comp P hΦ h₂
  rw [← integral_sub i1 i2]
  refine (abs_integral_le_integral_abs).trans ?_
  have hm : AEStronglyMeasurable (fun ω => |Φ (F₁ ω) - Φ (F₂ ω)|) P :=
    ((i1.sub i2).aestronglyMeasurable).norm
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => abs_nonneg _) hm]
  refine ENNReal.toReal_mono hfin (lintegral_mono fun ω => ?_)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (by simpa using cbUnit_lipschitz hΦ (F₁ ω) (F₂ ω))

end HRS.Uniform.Q45
