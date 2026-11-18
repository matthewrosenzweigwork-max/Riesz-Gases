import HRS.MS.EucRegAux2

/-!
# C-REG-e (part 3): thermal data for `0 < s`, `s + 1 < d`, and integrability of the weighted derivatives

Namespace `HRS.MS.Thm`, helper prefix `rege_`.

* `rege_data`: `ρ = thermalDensity d s a β` is a measurable nonnegative function solving
  `ρ = exp(-β (a‖x‖²/2 + U)) / Z` with `Z > 0`, `U = rege_U s ρ`, `ρ ≤ C₀ e^{-βa‖x‖²/2}`, and
  `g * μ_β = U` (all from `can2_isThermalDensity_pos` and `cb_thermal_two_sided`).
* `rege_U_bound`: `|U| ≤ C₀' lreg_A d s` for a rapidly decaying density.
* `rege_weighted_integrable`: from a Gaussian envelope `‖F x‖ ≤ K (1+‖x‖)^j e^{-βa‖x‖²/2}` one gets
  integrability of `‖x‖^p ‖F x‖` for every `p ≥ 0` and boundedness of `‖F‖`.
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.Thm

open HRS HRS.Whole HRS.MS.LogReg HRS.MS.Can2

variable {d : ℕ}

lemma rege_rieszKernel_eq {s : ℝ} (hs : 0 < s) (z : Euc d) : rieszKernel d s z = ‖z‖ ^ (-s) := by
  unfold rieszKernel
  simp [hs.ne']

/-- Thermal data for the pointwise representative `thermalDensity`. -/
theorem rege_data (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ Z C0 : ℝ, 0 < Z ∧ 0 ≤ C0 ∧ (∀ x, 0 ≤ thermalDensity d s a β x) ∧
      Measurable (thermalDensity d s a β) ∧
      (∀ x, thermalDensity d s a β x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 +
        rege_U s (thermalDensity d s a β) x)) / Z) ∧
      (∀ x, thermalDensity d s a β x ≤ C0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) ∧
      (∀ x, HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x =
        rege_U s (thermalDensity d s a β) x) := by
  have hd1 : 1 ≤ d := by omega
  have hth := can2_isThermalDensity_pos hd hs0 hsd ha hβ
  obtain ⟨hP, c, C, hc, hC, hbd⟩ := cb_thermal_two_sided hd1 hs0 hsd ha hβ
  set ρ := thermalDensity d s a β with hρ
  have hU : ∀ x, HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x =
      rege_U s ρ x := by
    intro x
    unfold thermalMeasure
    rw [convMeasure_withDensityReal _ hP.measurable hP.nonneg x]
    unfold rege_U
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [rege_rieszKernel_eq hs0]
  have hZpos := HRS.MS.Canon.cn_Z_pos _ _ β ρ hth
  set Z : ℝ := ∫ y, Real.exp (-β * (HRS.Whole.confinement a y + HRS.Whole.convMeasure (rieszKernel d s)
    (HRS.Whole.withDensityReal ρ) y)) with hZ
  have heq : ∀ x, ρ x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + rege_U s ρ x)) / Z := by
    intro x
    rw [hth.2 x]
    have := hU x
    unfold thermalMeasure at this
    rw [this]
    rfl
  refine ⟨Z, C * (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2), hZpos, by positivity, hP.nonneg, hP.measurable,
    heq, fun x => ?_, hU⟩
  have := (hbd x).2
  unfold gaussianComparison at this
  calc ρ x ≤ C * ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) := this
    _ = _ := by ring

/-- Boundedness of the potential of a rapidly decaying density. -/
lemma rege_U_bound {s : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) {F : Euc d → ℝ}
    (hm : AEStronglyMeasurable F volume) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, ‖F y‖ ≤ C * lreg_phi d y)
    (x : Euc d) : ‖rege_U s F x‖ ≤ C * lreg_A d s := by
  obtain ⟨hK, hKi⟩ := lreg_K_dom_y hd1 hsd hs.le hC hm hb x
  have hmeasg : Measurable (fun y : Euc d => ‖x - y‖ ^ (-s)) :=
    (measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _
  have hbd : ∀ y, ‖‖x - y‖ ^ (-s) * F y‖ ≤ ‖x - y‖ ^ (-s) * ‖F y‖ := fun y => by
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  calc ‖rege_U s F x‖ ≤ ∫ y, ‖x - y‖ ^ (-s) * ‖F y‖ :=
        norm_integral_le_of_norm_le hK (ae_of_all _ hbd)
    _ ≤ C * lreg_A d s := hKi

/-- Weighted integrability and boundedness from a Gaussian envelope. -/
lemma rege_weighted_integrable {b : ℝ} (hb : 0 < b) {j : ℕ} {K : ℝ}
    {E : Type*} [NormedAddCommGroup E] {G : Euc d → E} (hGm : AEStronglyMeasurable G volume)
    (h : ∀ x, ‖G x‖ ≤ K * (1 + ‖x‖) ^ j * Real.exp (-b * ‖x‖ ^ 2)) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun x => ‖x‖ ^ p * ‖G x‖) := by
  obtain ⟨n, hn⟩ := exists_nat_ge p
  have hI := (rege_poly_gauss_integrable (d := d) hb (n + j)).const_mul K
  refine hI.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact ((measurable_norm.pow_const p).aestronglyMeasurable).mul hGm.norm
  · have h0 : 0 ≤ ‖x‖ ^ p * ‖G x‖ := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    rw [Real.norm_of_nonneg h0]
    have h1 : ‖x‖ ^ p ≤ (1 + ‖x‖) ^ n := by
      calc ‖x‖ ^ p ≤ (1 + ‖x‖) ^ p :=
            Real.rpow_le_rpow (norm_nonneg _) (by linarith) hp
        _ ≤ (1 + ‖x‖) ^ (n : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) hn
        _ = (1 + ‖x‖) ^ n := Real.rpow_natCast _ _
    calc ‖x‖ ^ p * ‖G x‖ ≤ (1 + ‖x‖) ^ n * (K * (1 + ‖x‖) ^ j * Real.exp (-b * ‖x‖ ^ 2)) :=
          mul_le_mul h1 (h x) (norm_nonneg _) (by positivity)
      _ = K * ((1 + ‖x‖) ^ (n + j) * Real.exp (-b * ‖x‖ ^ 2)) := by rw [pow_add]; ring

end HRS.MS.Thm

end
