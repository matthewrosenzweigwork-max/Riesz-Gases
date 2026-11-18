import HRS.MS.ThmSpec

/-!
# C-B (part 1): two-sided Gaussian comparison for `thermalDensity` (`0 < s < d`)

From the THM-5 export `thermalDensity_eq_thermalRep` (`thermalDensity = thermalRep μ = Tmap μ` pointwise, `μ ∈ Cset γ M`)
we get, with `B` the (K1) constant of the Riesz kernel against `γ` and `M ≥ 1`:

* `thermalDensity` is a probability density (`cb_thermal_isProbDensity`);
* `thermalDensity x ≤ M γ x` and `exp (-β M B) γ x ≤ thermalDensity x` for every `x`
  (`Tmap μ x = γ x e^{-β (K*μ)(x)} / Z`, `0 ≤ K*μ ≤ M B`, `Z ≤ ∫ γ = 1`)
  (`cb_thermal_two_sided`).

These are the first half of `W:eq:euc-thermal-bounds` (S lines 1357-1362); the Poincare half is not in this file.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- `Z_μ ≤ 1` for a probability density `μ` (since `r e^{-β K*μ} ≤ r`). -/
lemma cb_Z_le_one {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B : ℝ} (hS : ThmSetting K r B) {β : ℝ}
    (hβ : 0 ≤ β) {μ : Euc d → ℝ} (hμ : HRS.Whole.IsProbDensity μ) : t012_Z K r β μ ≤ 1 := by
  have h1 : t012_Z K r β μ ≤ ∫ z, r z := by
    refine integral_mono (t012_Z_integrand_integrable hS hβ hμ) (t012_r_integrable hS) fun z => ?_
    have hu := t012_u_nonneg hS μ hμ.nonneg z
    have he : Real.exp (-β * ∫ y, K z y * μ y) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hr := hS.r_prob.nonneg z
    calc r z * Real.exp (-β * ∫ y, K z y * μ y) ≤ r z * 1 := mul_le_mul_of_nonneg_left he hr
      _ = r z := mul_one _
  rwa [hS.r_prob.integral_one] at h1

/-- Pointwise lower bound for the Euler map: `Tμ x ≥ e^{-β M B} r x` for `0 ≤ μ ≤ M r`. -/
lemma cb_Tmap_ge {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B M : ℝ} (hS : ThmSetting K r B) {β : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M) {μ : Euc d → ℝ} (hμ : μ ∈ Cset r M) (x : Euc d) :
    Real.exp (-(β * (M * B))) * r x ≤ Tmap K r β μ x := by
  have hZ := t012_Z_pos hS hβ hμ.1
  have hZ1 := cb_Z_le_one hS hβ hμ.1
  have hu := (conv_bound_of_le hS.meas hS.nonneg hS.k1 hμ.1.measurable hμ.1.nonneg hM hμ.2 x).2.2
  have hr := hS.r_prob.nonneg x
  rw [t012_Tmap_eq, le_div_iff₀ hZ]
  have he : Real.exp (-(β * (M * B))) ≤ Real.exp (-β * ∫ y, K x y * μ y) := by
    rw [Real.exp_le_exp]; nlinarith
  calc Real.exp (-(β * (M * B))) * r x * t012_Z K r β μ
      ≤ Real.exp (-(β * (M * B))) * r x * 1 :=
        mul_le_mul_of_nonneg_left hZ1 (mul_nonneg (Real.exp_pos _).le hr)
    _ = Real.exp (-(β * (M * B))) * r x := mul_one _
    _ ≤ Real.exp (-β * ∫ y, K x y * μ y) * r x := mul_le_mul_of_nonneg_right he hr
    _ = r x * Real.exp (-β * ∫ y, K x y * μ y) := mul_comm _ _

/-- The thermal density is a probability density, with two-sided Gaussian comparison.
`c = e^{-β M B}`, `C = M` for the data `(B, M)` of `thermalDensity_eq_thermalRep`. -/
theorem cb_thermal_two_sided (hd : 1 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) :
    HRS.Whole.IsProbDensity (thermalDensity d s a β) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x,
        c * gaussianComparison d a β x ≤ thermalDensity d s a β x ∧
          thermalDensity d s a β x ≤ C * gaussianComparison d a β x := by
  obtain ⟨B, M, μ, hS, hM, hμ, hfix, hEq, hpt, hle, hmin⟩ :=
    thermalDensity_eq_thermalRep hd hs0 hsd ha hβ
  have hM0 : 0 ≤ M := by linarith
  refine ⟨?_, Real.exp (-(β * (M * B))), M, Real.exp_pos _, by linarith, fun x => ⟨?_, hle x⟩⟩
  · have h := (Tmap_isProbDensity_le hS hβ.le hμ.1).1
    have hfun : thermalDensity d s a β = Tmap (t5K d s) (gaussianComparison d a β) β μ :=
      funext hpt
    rw [hfun]; exact h
  · rw [hpt x]
    exact cb_Tmap_ge hS hβ.le hM0 hμ x

end HRS.MS.Thm

end
