import HRS.MS.S82RN17

/-!
# S8.2 R02 (S82R), N18: the absorption lemma for the sup norm
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82R

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- If `log p = c + Err` with `|Err| <= A δ + e/1000` whenever `|p - 1| <= e` a.e., and `p <= 3`, then
`||p - 1||_∞ <= 5 A δ` (for `A δ <= 1/8`). -/
lemma s82r_absorb {p Err : E → ℝ} (hpm : Measurable p) (hp0 : ∀ᵐ x ∂μ, 0 < p x)
    (hp1 : ∫ x, p x ∂μ = 1) (hpi : Integrable p μ) (hp3 : ∀ᵐ x ∂μ, p x ≤ 3) {c A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hsm : A * δ ≤ 1 / 8)
    (hlog : ∀ᵐ x ∂μ, Real.log (p x) = c - 0 + Err x)
    (hE : ∀ e : ℝ, 0 ≤ e → (∀ᵐ x ∂μ, |p x - 1| ≤ e) → ∀ᵐ x ∂μ, |Err x| ≤ A * δ + e / 1000) :
    eLpNorm (fun x => p x - 1) ∞ μ ≤ ENNReal.ofReal (5 * A * δ) := by
  have hfm : Measurable (fun x => p x - 1) := hpm.sub_const 1
  have h3 : ∀ᵐ x ∂μ, |p x - 1| ≤ 3 := by
    filter_upwards [hp0, hp3] with x h0 h3
    rw [abs_le]; constructor <;> linarith
  have hX3 : eLpNorm (fun x => p x - 1) ∞ μ ≤ ENNReal.ofReal 3 := s82r_top_le hfm h3
  have hXfin : eLpNorm (fun x => p x - 1) ∞ μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hX3
  set e : ℝ := (eLpNorm (fun x => p x - 1) ∞ μ).toReal with he
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  have he3 : e ≤ 3 := ENNReal.toReal_le_of_le_ofReal (by norm_num) hX3
  have hXe : eLpNorm (fun x => p x - 1) ∞ μ = ENNReal.ofReal e := by
    rw [he, ENNReal.ofReal_toReal hXfin]
  have hae : ∀ᵐ x ∂μ, |p x - 1| ≤ e := s82r_ae_le_top hfm he0 hXe
  have hEb := hE e he0 hae
  have hAδ0 : 0 ≤ A * δ := mul_nonneg hA hδ
  have hnear := HRS.PinAux.p_near_one (μ := μ) (p := p) (T := fun _ => (0 : ℝ)) (E := Err) (c := c)
    (τ := 0) (ε := A * δ + e / 1000) hp0 hp1 hpi hlog (ae_of_all _ fun x => by simp) hEb
    (by linarith)
  have hX : eLpNorm (fun x => p x - 1) ∞ μ ≤ ENNReal.ofReal (4 * (0 + (A * δ + e / 1000))) :=
    s82r_top_le hfm hnear
  have he4 : e ≤ 4 * (0 + (A * δ + e / 1000)) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have he5 : e ≤ 5 * A * δ := by nlinarith
  rw [hXe]
  exact ENNReal.ofReal_le_ofReal he5

end HRS.MS.S82R

end
