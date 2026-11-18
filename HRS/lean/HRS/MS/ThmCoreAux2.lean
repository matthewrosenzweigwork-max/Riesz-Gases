import HRS.MS.ThmCoreAux1

/-!
# THM-2: the Euler map `Tmap` preserves probability densities and satisfies `T μ ≤ exp(βB) r`

Namespace `HRS.MS.Thm`; helper lemmas carry the prefix `t012_`.  Setting: `hS : ThmSetting K r B`, `0 ≤ β`,
`μ` a probability density.  Main statements:

* `Tmap_isProbDensity_le`: `IsProbDensity (Tmap K r β μ) ∧ ∀ x, Tmap K r β μ x ≤ exp (β B) * r x`
  (Jensen's inequality for `exp` is replaced by the tangent-line bound `exp t ≥ exp c (1 + t - c)`, and
  Tonelli gives `∫ r (K * μ) ≤ B`);
* `Tmap_pos`: `0 < Tmap K r β μ x`; `Tmap_mem_Cset`: `Tmap K r β μ ∈ Cset r M` when `exp (β B) ≤ M`.

The normaliser `Z = ∫ r e^{-β K * μ}` is a genuine (integrable) integral: `K * μ ≥ 0` so the integrand is
`≤ r`; the pointwise values `K * μ (x)` may be junk `0` only on a null set where the inner integral diverges,
and the bound `∫ r (K * μ) ≤ B` is proved for the Bochner integral directly.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- The normaliser `Z_μ = ∫ r e^{-β K * μ}` of the Euler map. -/
def t012_Z (K : Euc d → Euc d → ℝ) (r : Euc d → ℝ) (β : ℝ) (μ : Euc d → ℝ) : ℝ :=
  ∫ z, r z * Real.exp (-β * ∫ y, K z y * μ y)

theorem t012_Tmap_eq (K : Euc d → Euc d → ℝ) (r : Euc d → ℝ) (β : ℝ) (μ : Euc d → ℝ) (x : Euc d) :
    Tmap K r β μ x = r x * Real.exp (-β * ∫ y, K x y * μ y) / t012_Z K r β μ := rfl

variable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B : ℝ}

theorem t012_u_nonneg (hS : ThmSetting K r B) (μ : Euc d → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : Euc d) :
    0 ≤ ∫ y, K x y * μ y :=
  integral_nonneg fun y => mul_nonneg (hS.nonneg x y) (hμ y)

theorem t012_u_meas (hS : ThmSetting K r B) {μ : Euc d → ℝ} (hμ : Measurable μ) :
    Measurable fun x => ∫ y, K x y * μ y :=
  t012_measurable_conv hS.meas hμ

theorem t012_r_meas (hS : ThmSetting K r B) : Measurable r := hS.r_prob.measurable

theorem t012_r_integrable (hS : ThmSetting K r B) : Integrable r :=
  Integrable.of_integral_ne_zero (by rw [hS.r_prob.integral_one]; norm_num)

theorem t012_B_nonneg (hS : ThmSetting K r B) : 0 ≤ B :=
  le_trans (integral_nonneg fun y => mul_nonneg (hS.nonneg 0 y) (hS.r_prob.nonneg y)) (hS.k1 0).2

/-- Tonelli: `∫ r (K * μ) ≤ B` for a probability density `μ`, with integrability. -/
theorem t012_r_mul_u (hS : ThmSetting K r B) {μ : Euc d → ℝ} (hμ : HRS.Whole.IsProbDensity μ) :
    Integrable (fun x => r x * ∫ y, K x y * μ y) ∧ ∫ x, r x * ∫ y, K x y * μ y ≤ B := by
  have hrm := t012_r_meas hS
  have hB := t012_B_nonneg hS
  have hμi : Integrable μ := Integrable.of_integral_ne_zero (by rw [hμ.integral_one]; norm_num)
  set F : Euc d × Euc d → ℝ := fun p => K p.1 p.2 * r p.1 * μ p.2 with hF
  have hFm : Measurable F := (hS.meas.mul (hrm.comp measurable_fst)).mul (hμ.measurable.comp measurable_snd)
  have hF0 : ∀ p, 0 ≤ F p := fun p =>
    mul_nonneg (mul_nonneg (hS.nonneg _ _) (hS.r_prob.nonneg _)) (hμ.nonneg _)
  have hlin : ∫⁻ p, ENNReal.ofReal (F p) ∂((volume : Measure (Euc d)).prod volume) ≤ ENNReal.ofReal B := by
    rw [lintegral_prod_symm _ hFm.ennreal_ofReal.aemeasurable]
    have hinner : ∀ y, ∫⁻ x, ENNReal.ofReal (F (x, y)) ≤ ENNReal.ofReal (μ y) * ENNReal.ofReal B := by
      intro y
      have h1 : ∀ x, ENNReal.ofReal (F (x, y)) = ENNReal.ofReal (μ y) * ENNReal.ofReal (K y x * r x) := by
        intro x
        rw [← ENNReal.ofReal_mul (hμ.nonneg y)]
        simp only [hF]
        rw [hS.symm x y]; congr 1; ring
      simp_rw [h1]
      rw [lintegral_const_mul _ (by
        have : Measurable fun x : Euc d => K y x * r x :=
          (t012_measurable_K_left hS.meas y).mul hrm
        exact this.ennreal_ofReal)]
      gcongr
      have hint := (hS.k1 y).1
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x =>
        mul_nonneg (hS.nonneg y x) (hS.r_prob.nonneg x))]
      exact ENNReal.ofReal_le_ofReal (hS.k1 y).2
    calc ∫⁻ y, ∫⁻ x, ENNReal.ofReal (F (x, y)) ≤ ∫⁻ y, ENNReal.ofReal (μ y) * ENNReal.ofReal B :=
          lintegral_mono hinner
      _ = ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal (μ y) := by
          rw [lintegral_mul_const _ hμ.measurable.ennreal_ofReal, mul_comm]
      _ = ENNReal.ofReal B := by
          rw [← ofReal_integral_eq_lintegral_ofReal hμi (ae_of_all _ hμ.nonneg), hμ.integral_one]
          simp
  obtain ⟨hFi, hFle⟩ := t012_int_of_lintegral_le hFm hF0 hB hlin
  have heq : ∀ x, ∫ y, F (x, y) = r x * ∫ y, K x y * μ y := fun x => by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hF]; ring
  refine ⟨?_, ?_⟩
  · exact (hFi.integral_prod_left).congr (ae_of_all _ heq)
  · calc ∫ x, r x * ∫ y, K x y * μ y = ∫ x, ∫ y, F (x, y) := by simp_rw [heq]
      _ = ∫ p, F p ∂((volume : Measure (Euc d)).prod volume) := (integral_prod F hFi).symm
      _ ≤ B := hFle

/-- Integrability of the Euler integrand: `r e^{-β K * μ} ≤ r`. -/
theorem t012_Z_integrand_integrable (hS : ThmSetting K r B) {β : ℝ} (hβ : 0 ≤ β)
    {μ : Euc d → ℝ} (hμ : HRS.Whole.IsProbDensity μ) :
    Integrable fun z => r z * Real.exp (-β * ∫ y, K z y * μ y) := by
  refine Integrable.mono' (t012_r_integrable hS)
    ((t012_r_meas hS).mul (Real.measurable_exp.comp
      (measurable_const.mul (t012_u_meas hS hμ.measurable)))).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  have hu := t012_u_nonneg hS μ hμ.nonneg z
  have hr := hS.r_prob.nonneg z
  have he : Real.exp (-β * ∫ y, K z y * μ y) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr (Real.exp_pos _).le)]
  calc r z * Real.exp (-β * ∫ y, K z y * μ y) ≤ r z * 1 := mul_le_mul_of_nonneg_left he hr
    _ = r z := mul_one _

/-- Jensen-type lower bound for the normaliser: `Z_μ ≥ exp (-β B)`. -/
theorem t012_Z_ge (hS : ThmSetting K r B) {β : ℝ} (hβ : 0 ≤ β)
    {μ : Euc d → ℝ} (hμ : HRS.Whole.IsProbDensity μ) :
    Real.exp (-β * B) ≤ t012_Z K r β μ := by
  obtain ⟨hrui, hruB⟩ := t012_r_mul_u hS hμ
  set u : Euc d → ℝ := fun x => ∫ y, K x y * μ y with hu
  set c : ℝ := ∫ x, r x * u x with hc
  have hri := t012_r_integrable hS
  have hZi := t012_Z_integrand_integrable hS hβ hμ
  have key : ∀ x, Real.exp (-β * c) * (r x - β * (r x * u x) + β * c * r x) ≤
      r x * Real.exp (-β * u x) := by
    intro x
    have h1 : Real.exp (-β * u x) = Real.exp (-β * c) * Real.exp (-β * (u x - c)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : 1 + (-β * (u x - c)) ≤ Real.exp (-β * (u x - c)) := by
      have := Real.add_one_le_exp (-β * (u x - c)); linarith
    have hr := hS.r_prob.nonneg x
    have hE := (Real.exp_pos (-β * c)).le
    rw [h1]
    calc Real.exp (-β * c) * (r x - β * (r x * u x) + β * c * r x)
        = r x * (Real.exp (-β * c) * (1 + (-β * (u x - c)))) := by ring
      _ ≤ r x * (Real.exp (-β * c) * Real.exp (-β * (u x - c))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hE) hr
  have hint : ∫ x, Real.exp (-β * c) * (r x - β * (r x * u x) + β * c * r x) =
      Real.exp (-β * c) := by
    rw [integral_const_mul]
    have h1 : Integrable fun x => r x - β * (r x * u x) := hri.sub (hrui.const_mul β)
    have h2 : Integrable fun x => β * c * r x := hri.const_mul _
    have hrui' : Integrable fun x => r x * u x := hrui
    have : ∫ x, (r x - β * (r x * u x) + β * c * r x) = 1 - β * c + β * c := by
      rw [integral_add h1 h2, integral_sub hri (hrui'.const_mul β), integral_const_mul,
        integral_const_mul, hS.r_prob.integral_one]
      simp [hc]
    rw [this]; ring
  have hle : ∫ x, Real.exp (-β * c) * (r x - β * (r x * u x) + β * c * r x) ≤ t012_Z K r β μ := by
    refine integral_mono ?_ hZi key
    have h1 : Integrable fun x => r x - β * (r x * u x) := hri.sub (hrui.const_mul β)
    exact (h1.add (hri.const_mul (β * c))).const_mul _
  rw [hint] at hle
  refine le_trans ?_ hle
  rw [Real.exp_le_exp]
  nlinarith [hruB]

theorem t012_Z_pos (hS : ThmSetting K r B) {β : ℝ} (hβ : 0 ≤ β)
    {μ : Euc d → ℝ} (hμ : HRS.Whole.IsProbDensity μ) : 0 < t012_Z K r β μ :=
  lt_of_lt_of_le (Real.exp_pos _) (t012_Z_ge hS hβ hμ)

theorem Tmap_pos (hS : ThmSetting K r B) {β : ℝ} (hβ : 0 ≤ β)
    {μ : Euc d → ℝ} (hμ : HRS.Whole.IsProbDensity μ) (x : Euc d) : 0 < Tmap K r β μ x := by
  rw [t012_Tmap_eq]
  exact div_pos (mul_pos (hS.r_pos x) (Real.exp_pos _)) (t012_Z_pos hS hβ hμ)

/-- THM-2: the Euler map sends probability densities to probability densities, bounded by `exp (β B) r`. -/
theorem Tmap_isProbDensity_le (hS : ThmSetting K r B) {β : ℝ} (hβ : 0 ≤ β)
    {μ : Euc d → ℝ} (hμ : HRS.Whole.IsProbDensity μ) :
    HRS.Whole.IsProbDensity (Tmap K r β μ) ∧ ∀ x, Tmap K r β μ x ≤ Real.exp (β * B) * r x := by
  have hZ := t012_Z_pos hS hβ hμ
  refine ⟨⟨fun x => (Tmap_pos hS hβ hμ x).le, ?_, ?_⟩, fun x => ?_⟩
  · exact ((t012_r_meas hS).mul (Real.measurable_exp.comp
      (measurable_const.mul (t012_u_meas hS hμ.measurable)))).div_const _
  · simp_rw [t012_Tmap_eq]
    rw [integral_div]
    exact div_self hZ.ne'
  · rw [t012_Tmap_eq]
    have hu := t012_u_nonneg hS μ hμ.nonneg x
    have he : Real.exp (-β * ∫ y, K x y * μ y) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hr := hS.r_prob.nonneg x
    have hZge := t012_Z_ge hS hβ hμ
    rw [div_le_iff₀ hZ]
    calc r x * Real.exp (-β * ∫ y, K x y * μ y) ≤ r x * 1 := mul_le_mul_of_nonneg_left he hr
      _ = Real.exp (β * B) * r x * Real.exp (-β * B) := by
          rw [mul_comm (Real.exp (β * B)) (r x), mul_assoc, ← Real.exp_add]; simp
      _ ≤ Real.exp (β * B) * r x * t012_Z K r β μ :=
          mul_le_mul_of_nonneg_left hZge (mul_nonneg (Real.exp_pos _).le hr)

theorem Tmap_mem_Cset (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 ≤ β) (hM : Real.exp (β * B) ≤ M)
    {μ : Euc d → ℝ} (hμ : HRS.Whole.IsProbDensity μ) : Tmap K r β μ ∈ Cset r M := by
  obtain ⟨h1, h2⟩ := Tmap_isProbDensity_le hS hβ hμ
  refine ⟨h1, fun x => (h2 x).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hM (hS.r_prob.nonneg x)

end HRS.MS.Thm

end
