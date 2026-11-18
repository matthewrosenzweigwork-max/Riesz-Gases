import HRS.Energy.PressureDV

/-!
# HRS.MS.WrEntAux1 -- exponential moments and the variational inequality (WR-9, part 1)

Packet WR-9 of `docs/SUPP_FOUND_PACKETS.md` (Track D), namespace `HRS.MS.Wr`.  Purely measure-theoretic
infrastructure (no Euclidean content), generic in the measurable space `α`.

* `wr9_exp_abs_le`: `e^{|x|} ≤ e^x + e^{-x}`.
* `wr9_lintegral_exp_abs`: two-sided exponential moments of `Ψ` give the moment of `e^{c|Ψ|}`.
* `wr9_dv_abs`: Donsker--Varadhan for `c |Ψ|` (from `HRS.dv_lintegral`), with integrability of `|Ψ|` under `f`.
* `wr9_moments`: the two displays of `euclidean_pair_entropy` for an abstract probability measure `Q` and
  a measurable statistic `Ψ`, from `∫ e^{±cΨ} dQ ≤ e^{2 C₀ T}` (`T ≥ 1`).

No hypothesis is weakened: the Bochner integrals are of integrable functions (integrability is proved).
Helper lemmas carry the prefix `wr9_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

theorem wr9_exp_abs_le (x : ℝ) : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · have := Real.exp_pos (-x); linarith
  · have := Real.exp_pos x; linarith

section

variable {α : Type*} [MeasurableSpace α]

theorem wr9_lintegral_exp_abs (Q : Measure α) {Ψ : α → ℝ} (hΨ : Measurable Ψ) {c : ℝ} (hc : 0 < c) {A : ℝ}
    (hp : ∫⁻ x, ENNReal.ofReal (Real.exp (c * Ψ x)) ∂Q ≤ ENNReal.ofReal (Real.exp A))
    (hm : ∫⁻ x, ENNReal.ofReal (Real.exp (-(c * Ψ x))) ∂Q ≤ ENNReal.ofReal (Real.exp A)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * |Ψ x|)) ∂Q ≤ ENNReal.ofReal (2 * Real.exp A) := by
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (c * |Ψ x|)) ≤
      ENNReal.ofReal (Real.exp (c * Ψ x)) + ENNReal.ofReal (Real.exp (-(c * Ψ x))) := by
    intro x
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : c * |Ψ x| = |c * Ψ x| := by rw [abs_mul, abs_of_pos hc]
    rw [this]
    exact wr9_exp_abs_le _
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (c * |Ψ x|)) ∂Q
      ≤ ∫⁻ x, (ENNReal.ofReal (Real.exp (c * Ψ x)) + ENNReal.ofReal (Real.exp (-(c * Ψ x)))) ∂Q :=
        lintegral_mono hpt
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (c * Ψ x)) ∂Q + ∫⁻ x, ENNReal.ofReal (Real.exp (-(c * Ψ x))) ∂Q :=
        lintegral_add_left (ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp (measurable_const.mul hΨ))) _
    _ ≤ ENNReal.ofReal (Real.exp A) + ENNReal.ofReal (Real.exp A) := add_le_add hp hm
    _ = ENNReal.ofReal (2 * Real.exp A) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1; ring

theorem wr9_dv_abs (Q f : Measure α) [IsProbabilityMeasure Q] [IsProbabilityMeasure f]
    (hKL : InformationTheory.klDiv f Q ≠ ∞) {Ψ : α → ℝ} (hΨ : Measurable Ψ) {c : ℝ} (hc : 0 < c)
    {K : ℝ} (hK : 0 ≤ K)
    (hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (c * |Ψ x|)) ∂Q ≤ ENNReal.ofReal (Real.exp K)) :
    Integrable (fun x => |Ψ x|) f ∧
      ∫ x, |Ψ x| ∂f ≤ c⁻¹ * ((InformationTheory.klDiv f Q).toReal + K) := by
  have hFm : Measurable (fun x => c * |Ψ x|) := measurable_const.mul hΨ.abs
  have hF0 : ∀ x, 0 ≤ c * |Ψ x| := fun x => by positivity
  have hdv := HRS.dv_lintegral Q f hKL hFm hF0 hK hZ
  have hfin : ∫⁻ x, ENNReal.ofReal (c * |Ψ x|) ∂f ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hKL, ENNReal.ofReal_ne_top⟩) hdv
  have hint : Integrable (fun x => c * |Ψ x|) f :=
    (lintegral_ofReal_ne_top_iff_integrable hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall hF0)).1 hfin
  refine ⟨?_, ?_⟩
  · have := hint.const_mul c⁻¹
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  · have h1 : ∫ x, c * |Ψ x| ∂f = (∫⁻ x, ENNReal.ofReal (c * |Ψ x|) ∂f).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0) hFm.aestronglyMeasurable
    have h2 : (∫⁻ x, ENNReal.ofReal (c * |Ψ x|) ∂f).toReal ≤
        (InformationTheory.klDiv f Q).toReal + K := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hKL, ENNReal.ofReal_ne_top⟩) hdv
      rwa [ENNReal.toReal_add hKL ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hK] at this
    rw [integral_const_mul] at h1
    rw [le_inv_mul_iff₀ hc]
    linarith

/-- The two displays of `euclidean_pair_entropy` for an abstract law. -/
theorem wr9_moments (Q : Measure α) [IsProbabilityMeasure Q] {Ψ : α → ℝ} (hΨ : Measurable Ψ)
    {c C0 T : ℝ} (hc : 0 < c) (hC0 : 0 ≤ C0) (hT : 1 ≤ T)
    (hp : ∫⁻ x, ENNReal.ofReal (Real.exp (c * Ψ x)) ∂Q ≤ ENNReal.ofReal (Real.exp (2 * C0 * T)))
    (hm : ∫⁻ x, ENNReal.ofReal (Real.exp (-(c * Ψ x))) ∂Q ≤ ENNReal.ofReal (Real.exp (2 * C0 * T))) :
    (Integrable (fun x => Real.exp (c * |Ψ x|)) Q ∧
        Real.log (∫ x, Real.exp (c * |Ψ x|) ∂Q) ≤ (2 * C0 + 1) * T) ∧
      ∀ f : Measure α, IsProbabilityMeasure f → InformationTheory.klDiv f Q ≠ ∞ →
        Integrable (fun x => |Ψ x|) f ∧
          ∫ x, |Ψ x| ∂f ≤ c⁻¹ * (2 * C0 + 1) * ((InformationTheory.klDiv f Q).toReal + T) := by
  have hK0 : 0 ≤ (2 * C0 + 1) * T := by positivity
  have h2 : (2 : ℝ) ≤ Real.exp T := by
    have h1 := Real.add_one_le_exp (1 : ℝ)
    have h3 : Real.exp 1 ≤ Real.exp T := Real.exp_le_exp.2 hT
    linarith
  have hZ' := wr9_lintegral_exp_abs Q hΨ hc hp hm
  have hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (c * |Ψ x|)) ∂Q ≤
      ENNReal.ofReal (Real.exp ((2 * C0 + 1) * T)) := by
    refine hZ'.trans (ENNReal.ofReal_le_ofReal ?_)
    have h4 : Real.exp ((2 * C0 + 1) * T) = Real.exp (2 * C0 * T) * Real.exp T := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h4]
    have := Real.exp_pos (2 * C0 * T)
    nlinarith
  have hexpm : Measurable (fun x => Real.exp (c * |Ψ x|)) :=
    Real.measurable_exp.comp (measurable_const.mul hΨ.abs)
  have hint : Integrable (fun x => Real.exp (c * |Ψ x|)) Q :=
    (lintegral_ofReal_ne_top_iff_integrable hexpm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZ)
  refine ⟨⟨hint, ?_⟩, fun f hf hKL => ?_⟩
  · have hpos : 0 < ∫ x, Real.exp (c * |Ψ x|) ∂Q := integral_exp_pos hint
    have h1 : ∫ x, Real.exp (c * |Ψ x|) ∂Q ≤ Real.exp ((2 * C0 + 1) * T) := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
        hexpm.aestronglyMeasurable]
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hZ
      rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
    calc Real.log (∫ x, Real.exp (c * |Ψ x|) ∂Q) ≤ Real.log (Real.exp ((2 * C0 + 1) * T)) :=
          Real.log_le_log hpos h1
      _ = (2 * C0 + 1) * T := Real.log_exp _
  · obtain ⟨hi, hb⟩ := wr9_dv_abs Q f hKL hΨ hc hK0 hZ
    refine ⟨hi, hb.trans ?_⟩
    have hH : 0 ≤ (InformationTheory.klDiv f Q).toReal := ENNReal.toReal_nonneg
    have hc' : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    have : (InformationTheory.klDiv f Q).toReal + (2 * C0 + 1) * T ≤
        (2 * C0 + 1) * ((InformationTheory.klDiv f Q).toReal + T) := by nlinarith
    calc c⁻¹ * ((InformationTheory.klDiv f Q).toReal + (2 * C0 + 1) * T)
        ≤ c⁻¹ * ((2 * C0 + 1) * ((InformationTheory.klDiv f Q).toReal + T)) :=
          mul_le_mul_of_nonneg_left this hc'
      _ = c⁻¹ * (2 * C0 + 1) * ((InformationTheory.klDiv f Q).toReal + T) := by ring

end

end HRS.MS.Wr
