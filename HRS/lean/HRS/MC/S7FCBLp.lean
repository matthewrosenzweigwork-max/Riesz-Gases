import HRS.MC.S7FCBEnv

/-!
# FC-B, part 6: the averaging operator and its `L^p` contraction

`fcbT n f (x,y) = ∫ K_n(x - q₁) K_n(y - q₂) f(q) dq` on `Torus d × Torus d`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS HRS.KernelAux

variable {d : ℕ}

local instance fcb_borel_prod2 : BorelSpace (Torus d × Torus d) := Prod.borelSpace
local instance fcb_open_prod4 : OpensMeasurableSpace ((Torus d × Torus d) × Torus d × Torus d) :=
  Prod.opensMeasurableSpace

/-- the two-variable kernel `κ(u) = K(u₁) K(u₂)` -/
def fcbKap (d n : ℕ) (u : Torus d × Torus d) : ℝ := fcbK d n u.1 * fcbK d n u.2

/-- the averaging operator -/
def fcbT (d n : ℕ) (f : Torus d × Torus d → ℝ) (p : Torus d × Torus d) : ℝ :=
  ∫ q, fcbKap d n (p - q) * f q ∂(volume.prod volume)

theorem fcbKap_nonneg (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (u : Torus d × Torus d) : 0 ≤ fcbKap d n u :=
  mul_nonneg (fcbK_nonneg hd hn _) (fcbK_nonneg hd hn _)

theorem fcbKap_continuous (n : ℕ) : Continuous (fcbKap d n) :=
  ((fcbK_continuous n).comp continuous_fst).mul ((fcbK_continuous n).comp continuous_snd)

theorem fcbKap_lintegral (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) :
    ∫⁻ u : Torus d × Torus d, ENNReal.ofReal (fcbKap d n u) ∂(volume.prod volume) = 1 := by
  have hK1 : ∫⁻ a, ENNReal.ofReal (fcbK d n a) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (fcbK_integrable n)
      (Eventually.of_forall fun a => fcbK_nonneg hd hn a), fcbK_integral hd hn]
    simp
  have hKe : Measurable fun a => ENNReal.ofReal (fcbK d n a) :=
    ENNReal.measurable_ofReal.comp (fcbK_continuous n).measurable
  have : ∀ u : Torus d × Torus d, ENNReal.ofReal (fcbKap d n u) =
      ENNReal.ofReal (fcbK d n u.1) * ENNReal.ofReal (fcbK d n u.2) := fun u =>
    ENNReal.ofReal_mul (fcbK_nonneg hd hn _)
  simp_rw [this]
  rw [lintegral_prod_mul hKe.aemeasurable hKe.aemeasurable, hK1, one_mul]

/-- Jensen for a probability measure in `ℝ≥0∞`. -/
theorem fcb_jensen {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {h : α → ℝ≥0∞} (hm : Measurable h) {p : ℝ} (hp : 1 < p) :
    (∫⁻ a, h a ∂ν) ^ p ≤ ∫⁻ a, h a ^ p ∂ν := by
  obtain ⟨q, hpq⟩ : ∃ q : ℝ, p.HolderConjugate q := ⟨p.conjExponent, .conjExponent hp⟩
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hm.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h1
  have hp0 : 0 < p := by linarith
  calc (∫⁻ a, h a ∂ν) ^ p ≤ ((∫⁻ a, h a ^ p ∂ν) ^ (1 / p) * 1) ^ p := by
        rw [mul_one]; gcongr
    _ = ∫⁻ a, h a ^ p ∂ν := by
        rw [mul_one, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]

theorem fcb_mp_sub_right (q : Torus d × Torus d) :
    MeasurePreserving (fun x : Torus d × Torus d => x - q) (volume.prod volume) (volume.prod volume) :=
  (measurePreserving_sub_right volume q.1).prod (measurePreserving_sub_right volume q.2)

theorem fcb_mp_sub_left (q : Torus d × Torus d) :
    MeasurePreserving (fun x : Torus d × Torus d => q - x) (volume.prod volume) (volume.prod volume) :=
  (Measure.measurePreserving_sub_left volume q.1).prod (Measure.measurePreserving_sub_left volume q.2)

theorem fcbKap_measurable (n : ℕ) : Measurable (fcbKap d n) := (fcbKap_continuous n).measurable

theorem fcbKap_lintegral_sub_left (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (x : Torus d × Torus d) :
    ∫⁻ q, ENNReal.ofReal (fcbKap d n (x - q)) ∂(volume.prod volume) = 1 := by
  rw [(fcb_mp_sub_left x).lintegral_comp (f := fun u => ENNReal.ofReal (fcbKap d n u))
    (ENNReal.measurable_ofReal.comp (fcbKap_measurable n))]
  exact fcbKap_lintegral hd hn

theorem fcbKap_lintegral_sub_right (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (q : Torus d × Torus d) :
    ∫⁻ x, ENNReal.ofReal (fcbKap d n (x - q)) ∂(volume.prod volume) = 1 := by
  rw [(fcb_mp_sub_right q).lintegral_comp (f := fun u => ENNReal.ofReal (fcbKap d n u))
    (ENNReal.measurable_ofReal.comp (fcbKap_measurable n))]
  exact fcbKap_lintegral hd hn

theorem fcbT_enorm_le (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (f : Torus d × Torus d → ℝ)
    (x : Torus d × Torus d) :
    ‖fcbT d n f x‖ₑ ≤ ∫⁻ q, ENNReal.ofReal (fcbKap d n (x - q)) * ‖f q‖ₑ ∂(volume.prod volume) := by
  unfold fcbT
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun q => ?_))
  rw [enorm_mul, Real.enorm_of_nonneg (fcbKap_nonneg hd hn _)]

theorem fcbT_pointwise_pow_le (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 1 < p)
    {f : Torus d × Torus d → ℝ} (hfm : Measurable f) (x : Torus d × Torus d) :
    ‖fcbT d n f x‖ₑ ^ p ≤ ∫⁻ q, ENNReal.ofReal (fcbKap d n (x - q)) * ‖f q‖ₑ ^ p ∂(volume.prod volume) := by
  set dens : Torus d × Torus d → ℝ≥0∞ := fun q => ENNReal.ofReal (fcbKap d n (x - q)) with hdens
  have hdm : Measurable dens :=
    ENNReal.measurable_ofReal.comp
      ((fcbKap_continuous n).comp (continuous_const.sub continuous_id)).measurable
  have : IsProbabilityMeasure ((volume.prod volume : Measure (Torus d × Torus d)).withDensity dens) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        exact fcbKap_lintegral_sub_left hd hn x⟩
  have hfe : Measurable fun q => ‖f q‖ₑ := hfm.enorm
  have h1 := fcb_jensen ((volume.prod volume : Measure (Torus d × Torus d)).withDensity dens) hfe hp
  rw [lintegral_withDensity_eq_lintegral_mul _ hdm hfe,
    lintegral_withDensity_eq_lintegral_mul _ hdm (hfe.pow_const p)] at h1
  calc ‖fcbT d n f x‖ₑ ^ p ≤ (∫⁻ q, ENNReal.ofReal (fcbKap d n (x - q)) * ‖f q‖ₑ ∂(volume.prod volume)) ^ p := by
        gcongr; exact fcbT_enorm_le hd hn f x
    _ ≤ _ := h1

theorem fcbT_lintegral_le (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 1 < p)
    {f : Torus d × Torus d → ℝ} (hfm : Measurable f) :
    ∫⁻ x, ‖fcbT d n f x‖ₑ ^ p ∂(volume.prod volume) ≤ ∫⁻ q, ‖f q‖ₑ ^ p ∂(volume.prod volume) := by
  calc ∫⁻ x, ‖fcbT d n f x‖ₑ ^ p ∂(volume.prod volume)
      ≤ ∫⁻ x, ∫⁻ q, ENNReal.ofReal (fcbKap d n (x - q)) * ‖f q‖ₑ ^ p ∂(volume.prod volume) ∂(volume.prod volume) :=
        lintegral_mono fun x => fcbT_pointwise_pow_le hd hn hp hfm x
    _ = ∫⁻ q, ∫⁻ x, ENNReal.ofReal (fcbKap d n (x - q)) * ‖f q‖ₑ ^ p ∂(volume.prod volume) ∂(volume.prod volume) := by
        refine lintegral_lintegral_swap ?_
        exact ((ENNReal.measurable_ofReal.comp ((fcbKap_continuous n).comp
          (continuous_fst.sub continuous_snd)).measurable).mul
            ((hfm.enorm.pow_const p).comp measurable_snd)).aemeasurable
    _ = ∫⁻ q, ‖f q‖ₑ ^ p ∂(volume.prod volume) := by
        refine lintegral_congr fun q => ?_
        have hm : Measurable fun x : Torus d × Torus d => ENNReal.ofReal (fcbKap d n (x - q)) :=
          ENNReal.measurable_ofReal.comp ((fcbKap_continuous n).comp (continuous_id.sub continuous_const)).measurable
        rw [lintegral_mul_const _ hm, fcbKap_lintegral_sub_right hd hn q, one_mul]

end HRS.MC.Sec7.FCB
