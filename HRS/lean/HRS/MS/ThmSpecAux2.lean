import HRS.MS.ThmSpecAux1

/-!
# THM-5 (part 2): fixed points of the Euler map are thermal equilibria; rigidity

Setting: `K = t5K d s`, `r = γ = gaussianComparison d a β`, `V = confinement a`, `0 < s < d`, `a, β > 0`,
`hS : ThmSetting (t5K d s) γ B`, `M ≥ 1`.

* `t5_thermalDensity_of_fixed`: an everywhere fixed point of `Tmap` that is a probability density satisfies the pointwise
  thermal equation (`γ = c_γ e^{-βV}`, so `γ e^{-β K*ρ} = c_γ e^{-β(V + K*ρ)}` and `c_γ` cancels).
* `t5_equilibrium_of_fixed`: such a fixed point in `Cset γ M` is an `IsThermalEquilibrium` (finite free energy from
  `hasFiniteFreeEnergy_of_le`; minimality from `minimizer_of_fixedpoint` and the translation).
* `t5_minimizer_ae_eq`: every free-energy minimiser is a.e. equal to the fixed point.
* `thermalDensity_eq_pointwise`: two `IsThermalDensity` agreeing a.e. agree at every point (`convMeasure` only sees
  the a.e. class).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- Pointwise rigidity: two thermal densities (for the same `g, V, β`) that agree a.e. agree everywhere. -/
theorem thermalDensity_eq_pointwise {g V : Euc d → ℝ} {β : ℝ} {ρ₁ ρ₂ : Euc d → ℝ}
    (h₁ : HRS.Whole.IsThermalDensity g V β ρ₁) (h₂ : HRS.Whole.IsThermalDensity g V β ρ₂) (hae : ρ₁ =ᵐ[volume] ρ₂)
    (x : Euc d) : ρ₁ x = ρ₂ x := by
  have hc : ∀ z, HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ₁) z = HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ₂) z :=
    convMeasure_congr_ae g hae
  rw [h₁.2 x, h₂.2 x]
  simp_rw [hc]

/-- An everywhere fixed point of the Euler map which is a probability density satisfies the thermal equation. -/
theorem t5_thermalDensity_of_fixed {s a β B : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hS : ThmSetting (t5K d s) (gaussianComparison d a β) B) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ)
    (hfix : ∀ x, ρ x = Tmap (t5K d s) (gaussianComparison d a β) β ρ x) :
    HRS.Whole.IsThermalDensity (rieszKernel d s) (confinement a) β ρ := by
  refine ⟨hρ, fun x => ?_⟩
  have hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) z =
      ∫ y, rieszKernel d s (z - y) * ρ y := fun z =>
    convMeasure_withDensityReal _ hρ.measurable hρ.nonneg z
  simp_rw [hconv]
  have hc := t5c_pos (d := d) ha hβ
  have key : ∀ z, gaussianComparison d a β z *
      Real.exp (-β * ∫ y, rieszKernel d s (z - y) * ρ y) =
      t5c d a β * Real.exp (-β * (confinement a z + ∫ y, rieszKernel d s (z - y) * ρ y)) := by
    intro z
    rw [t5_gamma_eq, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hfix x]
  unfold Tmap
  simp only [t5K]
  simp_rw [key]
  rw [integral_const_mul, mul_div_mul_left _ _ hc.ne']

/-- A fixed point of the Euler map in `C_M` is a thermal equilibrium (existence part). -/
theorem t5_equilibrium_of_fixed (hd : 1 ≤ d) {s a β B M : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) (hM : 1 ≤ M) (hS : ThmSetting (t5K d s) (gaussianComparison d a β) B)
    {ρ : Euc d → ℝ} (hρ : ρ ∈ Cset (gaussianComparison d a β) M)
    (hfix : ∀ x, ρ x = Tmap (t5K d s) (gaussianComparison d a β) β ρ x) :
    HRS.Whole.IsThermalEquilibrium d s a β ρ := by
  refine ⟨⟨hρ.1, hasFiniteFreeEnergy_of_le hd hs0 hsd ha hβ hρ.1 hρ.2, ?_⟩,
    t5_thermalDensity_of_fixed ha hβ hS hρ.1 hfix⟩
  intro ρ' hρ' hfin'
  have hfae : ρ =ᵐ[volume] Tmap (t5K d s) (gaussianComparison d a β) β ρ := ae_of_all _ hfix
  have hfin := hasFiniteFreeEnergy_of_le hd hs0 hsd ha hβ hρ.1 hρ.2
  have hmin := (minimizer_of_fixedpoint hS hβ hM hρ hfae).1 ρ' hρ'
    (t5_ent_integrable ha hβ hρ' hfin') hfin'.2.2
  rw [freeEnergy_eq_Gfun_add ha hβ hρ.1 hfin, freeEnergy_eq_Gfun_add ha hβ hρ' hfin']
  linarith

/-- Every free-energy minimiser is a.e. equal to the fixed point `ρ ∈ C_M` of the Euler map. -/
theorem t5_minimizer_ae_eq (hd : 1 ≤ d) {s a β B M : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) (hM : 1 ≤ M) (hS : ThmSetting (t5K d s) (gaussianComparison d a β) B)
    {ρ : Euc d → ℝ} (hρ : ρ ∈ Cset (gaussianComparison d a β) M)
    (hfix : ∀ x, ρ x = Tmap (t5K d s) (gaussianComparison d a β) β ρ x)
    {l : Euc d → ℝ} (hl : HRS.Whole.IsFreeEnergyMinimizer (rieszKernel d s) (confinement a) β l) :
    l =ᵐ[volume] ρ := by
  have hfae : ρ =ᵐ[volume] Tmap (t5K d s) (gaussianComparison d a β) β ρ := ae_of_all _ hfix
  have hfin := hasFiniteFreeEnergy_of_le hd hs0 hsd ha hβ hρ.1 hρ.2
  obtain ⟨hlp, hlfin, hlmin⟩ := hl
  have h1 := hlmin ρ hρ.1 hfin
  rw [freeEnergy_eq_Gfun_add ha hβ hρ.1 hfin, freeEnergy_eq_Gfun_add ha hβ hlp hlfin] at h1
  have hent := t5_ent_integrable ha hβ hlp hlfin
  obtain ⟨hA, hB⟩ := minimizer_of_fixedpoint hS hβ hM hρ hfae
  have h2 := hA l hlp hent hlfin.2.2
  have h3 : Gfun (t5K d s) (gaussianComparison d a β) β l =
      Gfun (t5K d s) (gaussianComparison d a β) β ρ := by
    exact le_antisymm (by linarith) h2
  exact hB l hlp hent hlfin.2.2 h3

end HRS.MS.Thm

end
