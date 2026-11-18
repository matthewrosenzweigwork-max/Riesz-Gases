import HRS.MS.CzPvAux3
import HRS.Commutator.Whole.XLIAux23

/-!
# ELEM-A, part 1: Young's inequality in `eLpNorm` form, `L¹` kernel majorants, `C_b¹` data

Packet ELEM-A (CZ development), namespace `HRS.CZ.ElemA`.  Helper lemmas are prefixed `elema_`.

* `elema_young`: if `‖F x‖ₑ ≤ ∫⁻ ofReal(k z) ‖g(x-z)‖ₑ dz` for all `x` (`k ≥ 0` measurable, `g` measurable) then
  `‖F‖_p ≤ (∫⁻ ofReal k) ‖g‖_p`, `1 ≤ p < ∞` (`young_lintegral` of `XLIAux23`; no measurability of `F` is needed
  `F` a.e. strongly measurable: the `eLpNorm` of a non-a.e.-strongly-measurable function is `∞`).
* `elema_cb1_data`: from `MemCb 1 a` the global bound `|a| ≤ sup|a|` and Lipschitz constant `sup‖Da‖`
  with `cbNorm 1 a = sup|a| + sup‖Da‖`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.ElemA

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Young's inequality in `eLpNorm` form -/
lemma elema_young {k : 𝔼 → ℝ} (hk : Measurable k) {g : 𝔼 → ℝ} (hg : Measurable g) {F : 𝔼 → ℝ} {p : ℝ}
    (hFm : AEStronglyMeasurable F volume) (hp : 1 ≤ p) (hF : ∀ x, ‖F x‖ₑ ≤ ∫⁻ z, ENNReal.ofReal (k z) * ‖g (x - z)‖ₑ) :
    eLpNorm F (ENNReal.ofReal p) volume ≤
      (∫⁻ z, ENNReal.ofReal (k z)) * eLpNorm g (ENNReal.ofReal p) volume := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hnetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hnetop hFm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hnetop hg.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  have hy := HRS.Commutator.Whole.XLI.young_lintegral (d := d)
    (a := fun z => ENNReal.ofReal (k z)) (b := fun z => ‖g z‖ₑ) (ENNReal.measurable_ofReal.comp hk)
    hg.enorm hp
  have h1 : ∫⁻ x, ‖F x‖ₑ ^ p ≤ ∫⁻ x, (∫⁻ z, ENNReal.ofReal (k z) * ‖g (x - z)‖ₑ) ^ p :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (hF x) hp0.le
  have h2 := h1.trans hy
  calc (∫⁻ x, ‖F x‖ₑ ^ p) ^ (1 / p) ≤ ((∫⁻ z, ENNReal.ofReal (k z)) ^ p * ∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h2 (by positivity)
    _ = (∫⁻ z, ENNReal.ofReal (k z)) * (∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        congr 2
        field_simp
        simp

/-- global bounds from `MemCb 1` -/
lemma elema_cb1_data {a : 𝔼 → ℝ} (ha : HRS.MemCb 1 a) :
    ∃ Ba La : ℝ, 0 ≤ Ba ∧ 0 ≤ La ∧ HRS.cbNorm 1 a = Ba + La ∧ (∀ y, |a y| ≤ Ba) ∧
      (∀ x y, |a x - a y| ≤ La * ‖x - y‖) := by
  have hc : ContDiff ℝ 1 a := by simpa using ha.1
  have h0 := ha.2 0 (by norm_num)
  have h1 := ha.2 1 le_rfl
  refine ⟨⨆ z : 𝔼, ‖iteratedFDeriv ℝ 0 a z‖, ⨆ z : 𝔼, ‖iteratedFDeriv ℝ 1 a z‖,
    Real.iSup_nonneg fun z => norm_nonneg _, Real.iSup_nonneg fun z => norm_nonneg _, ?_, fun y => ?_,
    fun x y => ?_⟩
  · unfold HRS.cbNorm
    simp [Finset.sum_range_succ]
  · have := le_ciSup h0 y
    simpa [Real.norm_eq_abs] using this
  · refine HRS.CZ.Pv.pvapi_lip_of_fderiv (hc.differentiable one_ne_zero) (fun z => ?_) x y
    have := le_ciSup h1 z
    simpa using this

end HRS.CZ.ElemA
