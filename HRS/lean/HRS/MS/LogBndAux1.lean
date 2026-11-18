import HRS.MS.ThmLog

/-!
# C-LB (part 1): two-sided pointwise bounds for the thermal representative, and `thermalDensity = thermalRep` for `s = 0`

Namespace `HRS.MS.Thm`; helper declarations carry the prefix `clb_`.

* `clb_rep_bounds` (abstract `ThmSetting`): an everywhere Euler fixed point `ρ ∈ Cset r M` satisfies
  `exp (-β M B) r ≤ ρ ≤ exp (β B) r` pointwise.  Upper bound: `ThmCoreAux2.Tmap_isProbDensity_le`.  Lower bound:
  `0 ≤ K * ρ ≤ M B` (`conv_bound_of_le`) and `Z = ∫ r e^{-β K * ρ} ≤ ∫ r = 1`.
* `clb_thermalDensity_eq_rep` (`s = 0`): exactly as `ThmSpec.thermalDensity_eq_thermalRep` for `s > 0`, there are
  `B, M, μ` with `ThmSetting (t67K d) (t67gammaBar d a β) B`, `1 ≤ M`, and `thermalDensity d 0 a β x = thermalRep ... μ x`
  for every `x`, where `thermalRep μ ∈ Cset γ̄ M` is an everywhere Euler fixed point.

The kernel `K̃ = g + ½ l(x) + ½ l(y) + ½ log 2` of the Euler map enters only through the bound `0 ≤ K̃ * ρ ≤ M B`
(K1 for `K̃`); its difference from `g` is absorbed in the explicit weight `γ̄ ∝ (1+|x|²)^{β/2} e^{-β a |x|²/2}`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- Two-sided pointwise bound for an everywhere Euler fixed point in `C_M`. -/
theorem clb_rep_bounds {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B : ℝ} (hS : ThmSetting K r B)
    {β M : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M) {ρ : Euc d → ℝ} (hρ : ρ ∈ Cset r M)
    (hfix : ∀ x, ρ x = Tmap K r β ρ x) (x : Euc d) :
    Real.exp (-β * (M * B)) * r x ≤ ρ x ∧ ρ x ≤ Real.exp (β * B) * r x := by
  refine ⟨?_, ?_⟩
  · have hZ := t012_Z_pos hS hβ hρ.1
    have hZ1 : t012_Z K r β ρ ≤ 1 := by
      unfold t012_Z
      have h : ∫ z, r z * Real.exp (-β * ∫ y, K z y * ρ y) ≤ ∫ z, r z :=
        integral_mono (t012_Z_integrand_integrable hS hβ hρ.1) (t012_r_integrable hS) (fun z => by
          have hu := t012_u_nonneg hS ρ hρ.1.nonneg z
          have he : Real.exp (-β * ∫ y, K z y * ρ y) ≤ 1 := by
            rw [Real.exp_le_one_iff]; nlinarith
          calc r z * Real.exp (-β * ∫ y, K z y * ρ y) ≤ r z * 1 :=
                mul_le_mul_of_nonneg_left he (hS.r_prob.nonneg z)
            _ = r z := mul_one _)
      rwa [hS.r_prob.integral_one] at h
    have hu := (conv_bound_of_le hS.meas hS.nonneg hS.k1 hρ.1.measurable hρ.1.nonneg hM hρ.2 x).2.2
    have he : Real.exp (-β * (M * B)) ≤ Real.exp (-β * ∫ y, K x y * ρ y) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hr := hS.r_prob.nonneg x
    rw [hfix x, t012_Tmap_eq, le_div_iff₀ hZ]
    calc Real.exp (-β * (M * B)) * r x * t012_Z K r β ρ
        ≤ Real.exp (-β * (M * B)) * r x * 1 :=
          mul_le_mul_of_nonneg_left hZ1 (mul_nonneg (Real.exp_pos _).le hr)
      _ = r x * Real.exp (-β * (M * B)) := by ring
      _ ≤ r x * Real.exp (-β * ∫ y, K x y * ρ y) := mul_le_mul_of_nonneg_left he hr
  · rw [hfix x]
    exact (Tmap_isProbDensity_le hS hβ hρ.1).2 x

/-- `s = 0`: `thermalDensity d 0 a β` is, at every point, the Euler representative of an a.e. fixed point `μ ∈ C_M`. -/
theorem clb_thermalDensity_eq_rep (hd : 1 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ (B M : ℝ) (μ : Euc d → ℝ), ThmSetting (t67K d) (t67gammaBar d a β) B ∧ 1 ≤ M ∧
      thermalRep (t67K d) (t67gammaBar d a β) β μ ∈ Cset (t67gammaBar d a β) M ∧
      (∀ x, thermalRep (t67K d) (t67gammaBar d a β) β μ x =
        Tmap (t67K d) (t67gammaBar d a β) β (thermalRep (t67K d) (t67gammaBar d a β) β μ) x) ∧
      ∀ x, thermalDensity d 0 a β x = thermalRep (t67K d) (t67gammaBar d a β) β μ x := by
  obtain ⟨B, M, μ, hS, hM, hexp, hμ, hfix⟩ := t67_exists_fixed hd ha hβ
  have hρC := thermalRep_mem_Cset hS hβ.le hexp hμ.1
  have hρfix := thermalRep_fixed hfix
  have hEq := t67_equilibrium_of_fixed hS ha hβ hM hρC hρfix
  have hex : ∃ ρ, HRS.Whole.IsThermalEquilibrium d 0 a β ρ := ⟨_, hEq⟩
  have hτ : HRS.Whole.IsThermalEquilibrium d 0 a β (thermalDensity d 0 a β) := by
    unfold thermalDensity
    rw [dif_pos hex]
    exact hex.choose_spec
  have hae := t67_minimizer_ae_eq hS ha hβ hM hρC hρfix hτ.1
  exact ⟨B, M, μ, hS, hM, hρC, hρfix, fun x => thermalDensity_eq_pointwise hτ.2 hEq.2 hae x⟩

end HRS.MS.Thm

end
