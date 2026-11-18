import HRS.MS.ThmSpec
import HRS.MS.Canon

/-!
# TC-U1 (part 1): uniform a priori thermal bounds for `0 < s < d`

Namespace `HRS.MS.TcU`; helper lemmas carry the prefix `tcu1_`.

The merged existence proof `thermalDensity_eq_thermalRep` (`ThmSpec.lean`) produces the bound
`thermalDensity ≤ M γ`, `γ = gaussianComparison d a β`, `M = max 1 (exp (β B))`, but `B` is an existential
constant (`riesz_conv_gaussian_bound` returns `∃ B`).  Here the (K1) bound of `ThmCoreAux1` is re-proved with the
EXPLICIT constant `tcuB d s c' = c' * sphereArea d / (d - s) + 1`, valid for every `c' ≥ c_γ = (βa/2π)^{d/2}`;
the abstract setting `ThmSetting (t5K d s) γ (tcuB d s c')` is then assembled from `t5_setting` (all other fields do
not depend on `B`), and the proof of `thermalDensity_eq_thermalRep` is repeated verbatim with this `B`.  This
gives, for `a ∈ [am, ap]`, `β ∈ [βm, βp]`, constants depending only on `d, s, am, ap, βm, βp`:

* `thermalDensity ≤ M₀ exp (-c ‖x‖²)`,   `c = βm am / 2`;
* `0 ≤ g * μ ≤ UB` (the interaction potential `U`);
* `z₀ ≤ Z` (the normaliser of the thermal equation), by evaluating the thermal equation at `x = 0`
  (no free-energy trial argument is needed: the constrained-class bound `ρ ≤ M γ` already gives it);
* `∫ ‖x‖² ρ ≤ m₂`.

Main exports: `tcu_apriori_pos`, with the normaliser `tcuZ`.  No existing file is edited.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.TcU

open HRS.Whole HRS.MS.Thm

variable {d : ℕ}

/-- The explicit (K1) constant: `c' * |S^{d-1}| / (d - s) + 1`. -/
def tcuB (d : ℕ) (s c' : ℝ) : ℝ := c' * sphereArea d / ((d : ℝ) - s) + 1

/-- The normaliser of the thermal equation `ρ = Z⁻¹ exp (-β (V + g * μ))`:
`Z = ∫ exp (-β (V + g * μ))`. -/
def tcuZ (d : ℕ) (s a β : ℝ) : ℝ :=
  ∫ y : Euc d, Real.exp (-β * (confinement a y +
    HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) y))

lemma tcu1_B_nonneg (hd : 1 ≤ d) {s c' : ℝ} (hsd : s < d) (hc0 : 0 ≤ c') : 0 ≤ tcuB d s c' := by
  have hsa : 0 ≤ sphereArea d := Q34.sphereArea_nonneg hd
  have hds : 0 < (d : ℝ) - s := by linarith
  unfold tcuB
  positivity

/-- (K1) for the Riesz kernel against the Gaussian comparison density with an explicit constant. -/
theorem tcu1_k1 (hd : 1 ≤ d) {s a β c' : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β)
    (hc' : t5c d a β ≤ c') (x : Euc d) :
    Integrable (fun y => rieszKernel d s (x - y) * gaussianComparison d a β y) ∧
      ∫ y, rieszKernel d s (x - y) * gaussianComparison d a β y ≤ tcuB d s c' := by
  have hγ := gaussianComparison_isProbDensity (d := d) ha hβ
  have hc0 : 0 ≤ c' := (t5c_pos (d := d) ha hβ).le.trans hc'
  have hB0 := tcu1_B_nonneg hd hsd hc0
  have hmeasK := t012_rieszK_measurable (d := d) hs0.ne'
  have hm : Measurable fun y => rieszKernel d s (x - y) * gaussianComparison d a β y :=
    (hmeasK.comp (measurable_const.prodMk measurable_id)).mul (gaussianComparison_measurable a β)
  have hle : ∀ y, gaussianComparison d a β y ≤ c' := fun y =>
    (gaussianComparison_le ha hβ y).trans hc'
  have hlin := Q34.lintegral_kernel_le hd hs0 hsd hγ (M := c') hle x
  have hconv : ∫⁻ z, ENNReal.ofReal (‖x - z‖ ^ (-s)) ∂(HRS.Whole.withDensityReal (gaussianComparison d a β)) =
      ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y) * gaussianComparison d a β y) := by
    rw [Q34.lintegral_nu hγ _ (by
      have : Measurable fun z : Euc d => ‖x - z‖ ^ (-s) :=
        ((measurable_const.sub measurable_id).norm).pow_const _
      exact this.ennreal_ofReal)]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_mul (gaussianComparison_pos ha hβ y).le, t012_rieszK_eq hs0.ne', mul_comm]
  rw [hconv] at hlin
  exact t012_int_of_lintegral_le hm
    (fun y => mul_nonneg (t012_rieszK_nonneg hs0.ne' x y) (gaussianComparison_pos ha hβ y).le)
    hB0 hlin

/-- The abstract setting with the explicit constant. -/
theorem tcu1_setting (hd : 1 ≤ d) {s a β c' : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) (hc' : t5c d a β ≤ c') :
    ThmSetting (t5K d s) (gaussianComparison d a β) (tcuB d s c') := by
  obtain ⟨B, hS⟩ := t5_setting hd hs0 hsd ha hβ
  exact { hS with k1 := fun x => tcu1_k1 hd hs0 hsd ha hβ hc' x }

/-- `thermalDensity` is a thermal equilibrium, bounded by `M γ` with the explicit
`M = max 1 (exp (β B))`, `B = tcuB d s c'`. -/
theorem tcu1_rep (hd : 1 ≤ d) {s a β c' : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) (hc' : t5c d a β ≤ c') :
    HRS.Whole.IsThermalEquilibrium d s a β (thermalDensity d s a β) ∧
      ∀ x, thermalDensity d s a β x ≤
        max 1 (Real.exp (β * tcuB d s c')) * gaussianComparison d a β x := by
  have hS := tcu1_setting hd hs0 hsd ha hβ hc'
  have hM : 1 ≤ max 1 (Real.exp (β * tcuB d s c')) := le_max_left _ _
  have hexp : Real.exp (β * tcuB d s c') ≤ max 1 (Real.exp (β * tcuB d s c')) := le_max_right _ _
  obtain ⟨μ, hμ, hmin⟩ := exists_min_Cset hS hM hβ
  have hfix := fixedpoint_of_min hS hβ hM hexp hμ hmin
  have hρC := thermalRep_mem_Cset hS hβ.le hexp hμ.1
  have hρfix := thermalRep_fixed hfix
  have hEq := t5_equilibrium_of_fixed hd hs0 hsd ha hβ hM hS hρC hρfix
  have hex : ∃ ρ, HRS.Whole.IsThermalEquilibrium d s a β ρ := ⟨_, hEq⟩
  have hτ : HRS.Whole.IsThermalEquilibrium d s a β (thermalDensity d s a β) := by
    unfold thermalDensity
    rw [dif_pos hex]
    exact hex.choose_spec
  have hae := t5_minimizer_ae_eq hd hs0 hsd ha hβ hM hS hρC hρfix hτ.1
  have hpt : ∀ x, thermalDensity d s a β x =
      thermalRep (t5K d s) (gaussianComparison d a β) β μ x :=
    thermalDensity_eq_pointwise hτ.2 hEq.2 hae
  exact ⟨hτ, fun x => by rw [hpt x]; exact hρC.2 x⟩

/-- `0 ≤ g * μ ≤ M B` for the thermal measure. -/
theorem tcu1_conv_bound (hd : 1 ≤ d) {s a β c' : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) (hc' : t5c d a β ≤ c') (x : Euc d) :
    0 ≤ HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x ∧
      HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x ≤
        max 1 (Real.exp (β * tcuB d s c')) * tcuB d s c' := by
  obtain ⟨hτ, hle⟩ := tcu1_rep hd hs0 hsd ha hβ hc'
  have hS := tcu1_setting hd hs0 hsd ha hβ hc'
  have hρ := hτ.1.1
  have hM0 : 0 ≤ max 1 (Real.exp (β * tcuB d s c')) := (zero_le_one).trans (le_max_left _ _)
  obtain ⟨-, h2, h3⟩ := conv_bound_of_le hS.meas hS.nonneg hS.k1 hρ.measurable hρ.nonneg hM0 hle x
  have e : HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x =
      ∫ y, rieszKernel d s (x - y) * thermalDensity d s a β y :=
    convMeasure_withDensityReal _ hρ.measurable hρ.nonneg x
  rw [e]
  exact ⟨h2, h3⟩

/-- The thermal equation, multiplied out: `ρ x * Z = exp (-β (V x + g * μ x))`, and `Z > 0`. -/
theorem tcu1_eq {s a β : ℝ}
    (hτ : HRS.Whole.IsThermalEquilibrium d s a β (thermalDensity d s a β)) (x : Euc d) :
    0 < tcuZ d s a β ∧ thermalDensity d s a β x * tcuZ d s a β =
      Real.exp (-β * (confinement a x +
        HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x)) := by
  have hZ : 0 < tcuZ d s a β := HRS.MS.Canon.cn_Z_pos _ _ β _ hτ.2
  refine ⟨hZ, ?_⟩
  have h := hτ.2.2 x
  have h' : thermalDensity d s a β x = Real.exp (-β * (confinement a x +
        HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x)) / tcuZ d s a β := h
  rw [h']
  exact div_mul_cancel₀ _ hZ.ne'

/-- **TC-U1 (`0 < s < d`).**  Uniform a priori bounds for the thermal density, for `a ∈ [am, ap]`,
`β ∈ [βm, βp]`: Gaussian upper bound, bounds for the interaction potential `U = g * μ`, lower bound of the
normaliser `Z` and second moment. -/
theorem tcu_apriori_pos (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {am ap βm βp : ℝ}
    (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) :
    ∃ c M₀ z₀ m₂ UB : ℝ, 0 < c ∧ 0 < M₀ ∧ 0 < z₀ ∧
      ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
        z₀ ≤ tcuZ d s a β ∧
        (∀ x : Euc d, thermalDensity d s a β x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) ∧
        Integrable (fun x : Euc d => ‖x‖ ^ 2 * thermalDensity d s a β x) ∧
        (∫ x : Euc d, ‖x‖ ^ 2 * thermalDensity d s a β x) ≤ m₂ ∧
        ∀ x : Euc d, 0 ≤ HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x ∧
          HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x ≤ UB := by
  have hap0 : 0 < ap := ham.trans_le hap
  have hβp0 : 0 < βp := hβm.trans_le hβp
  set c' : ℝ := (βp * ap / (2 * Real.pi)) ^ ((d : ℝ) / 2) with hc'def
  have hc'pos : 0 < c' := by positivity
  set B0 : ℝ := tcuB d s c' with hB0def
  have hB0 : 0 ≤ B0 := tcu1_B_nonneg hd hsd hc'pos.le
  set Mu : ℝ := max 1 (Real.exp (βp * B0)) with hMu
  have hMu1 : 1 ≤ Mu := le_max_left _ _
  set c : ℝ := βm * am / 2 with hcdef
  have hcpos : 0 < c := by positivity
  set M₀ : ℝ := Mu * c' with hM₀def
  have hM₀pos : 0 < M₀ := by positivity
  have hint : Integrable (fun x : Euc d => ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2)) :=
    t012_integrable_sq_mul_exp hcpos
  refine ⟨c, M₀, Real.exp (-(βp * (Mu * B0))) / M₀, M₀ * ∫ x : Euc d, ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2),
    Mu * B0, hcpos, hM₀pos, by positivity, fun a β ha1 ha2 hβ1 hβ2 => ?_⟩
  have ha : 0 < a := ham.trans_le ha1
  have hβ : 0 < β := hβm.trans_le hβ1
  have hc'le : t5c d a β ≤ c' := by
    unfold t5c
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    have : β * a ≤ βp * ap := mul_le_mul hβ2 ha2 ha.le hβp0.le
    exact div_le_div_of_nonneg_right this (by positivity)
  obtain ⟨hτ, hle⟩ := tcu1_rep hd hs0 hsd ha hβ hc'le
  -- the factor `M = max 1 (exp (β B0)) ≤ Mu`
  have hMle : max 1 (Real.exp (β * B0)) ≤ Mu := by
    refine max_le_max le_rfl (Real.exp_le_exp.2 ?_)
    exact mul_le_mul_of_nonneg_right hβ2 hB0
  have hM1 : (0 : ℝ) ≤ max 1 (Real.exp (β * B0)) := (zero_le_one).trans (le_max_left _ _)
  -- Gaussian bound
  have hgauss : ∀ x : Euc d, thermalDensity d s a β x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2) := by
    intro x
    refine (hle x).trans ?_
    rw [gaussianComparison_eq]
    have h1 : Real.exp (-(β * a / 2) * ‖x‖ ^ 2) ≤ Real.exp (-c * ‖x‖ ^ 2) := by
      apply Real.exp_le_exp.2
      have : c ≤ β * a / 2 := by
        rw [hcdef]
        have := mul_le_mul hβ1 ha1 ham.le hβ.le
        linarith
      nlinarith [sq_nonneg ‖x‖]
    have hcg : (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) ≤ c' := hc'le
    calc max 1 (Real.exp (β * tcuB d s c')) *
          ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) * Real.exp (-(β * a / 2) * ‖x‖ ^ 2))
        ≤ Mu * (c' * Real.exp (-c * ‖x‖ ^ 2)) := by
          refine mul_le_mul hMle ?_ (by positivity) (by positivity)
          exact mul_le_mul hcg h1 (Real.exp_pos _).le hc'pos.le
      _ = M₀ * Real.exp (-c * ‖x‖ ^ 2) := by rw [hM₀def]; ring
  -- potential
  have hU : ∀ x : Euc d, 0 ≤ HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x ∧
      HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) x ≤ Mu * B0 := by
    intro x
    obtain ⟨h1, h2⟩ := tcu1_conv_bound hd hs0 hsd ha hβ hc'le x
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hMle hB0)⟩
  -- second moment
  have hρ := hτ.1.1
  have hmeas : Measurable fun x : Euc d => ‖x‖ ^ 2 * thermalDensity d s a β x :=
    (measurable_norm.pow_const 2).mul hρ.measurable
  have hmaj : Integrable (fun x : Euc d => M₀ * (‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2))) := hint.const_mul M₀
  have hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2 * thermalDensity d s a β x) := by
    refine Integrable.mono' hmaj hmeas.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hρ.nonneg x))]
    calc ‖x‖ ^ 2 * thermalDensity d s a β x ≤ ‖x‖ ^ 2 * (M₀ * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hgauss x) (by positivity)
      _ = M₀ * (‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2)) := by ring
  have hm2 : (∫ x : Euc d, ‖x‖ ^ 2 * thermalDensity d s a β x) ≤
      M₀ * ∫ x : Euc d, ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2) := by
    rw [← integral_const_mul]
    refine integral_mono hint2 hmaj fun x => ?_
    calc ‖x‖ ^ 2 * thermalDensity d s a β x ≤ ‖x‖ ^ 2 * (M₀ * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hgauss x) (by positivity)
      _ = M₀ * (‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2)) := by ring
  -- normaliser
  have hZ : Real.exp (-(βp * (Mu * B0))) / M₀ ≤ tcuZ d s a β := by
    obtain ⟨hZpos, heq⟩ := tcu1_eq hτ (0 : Euc d)
    have hV0 : confinement a (0 : Euc d) = 0 := by simp [confinement]
    rw [hV0, zero_add] at heq
    obtain ⟨hU0, hU1⟩ := hU 0
    have h0 : thermalDensity d s a β 0 ≤ M₀ := by
      have := hgauss 0
      simpa using this
    have hexp : Real.exp (-(βp * (Mu * B0))) ≤
        Real.exp (-β * HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) 0) := by
      apply Real.exp_le_exp.2
      have h1 : β * HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) 0 ≤ β * (Mu * B0) :=
        mul_le_mul_of_nonneg_left hU1 hβ.le
      have h2 : β * (Mu * B0) ≤ βp * (Mu * B0) :=
        mul_le_mul_of_nonneg_right hβ2 (by positivity)
      linarith
    rw [div_le_iff₀ hM₀pos]
    calc Real.exp (-(βp * (Mu * B0))) ≤
          Real.exp (-β * HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) 0) := hexp
      _ = thermalDensity d s a β 0 * tcuZ d s a β := heq.symm
      _ ≤ M₀ * tcuZ d s a β := mul_le_mul_of_nonneg_right h0 hZpos.le
      _ = tcuZ d s a β * M₀ := mul_comm _ _
  exact ⟨hZ, hgauss, hint2, hm2, hU⟩

end HRS.MS.TcU

end
