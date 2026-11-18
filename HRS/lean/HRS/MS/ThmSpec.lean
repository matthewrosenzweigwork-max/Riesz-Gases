import HRS.MS.ThmSpecAux2

/-!
# THM-5: proof of `HRS.Whole.thermalDensity_spec` (the `s > 0` thermal equilibrium)

Instantiate `ThmSetting` with `K x y = rieszKernel d s (x - y)`, `r = γ = gaussianComparison d a β`
(`ThmSpecAux1.t5_setting`), take `M = max 1 (exp (β B))`, a minimiser `μ` of `G` on `Cset γ M` (THM-3) which is an a.e.
fixed point of the Euler map (THM-4), and its pointwise representative `ρ₀ = thermalRep μ = Tmap μ`.  Then `ρ₀` is a
thermal equilibrium bounded by `M c_γ` (`ThmSpecAux2`), every free-energy minimiser equals `ρ₀` a.e. (translation
`F = G + β⁻¹ log c_γ`), and `thermalDensity` equals `ρ₀` at every point (pointwise rigidity of the thermal equation).

Exports: `thermalDensity_eq_thermalRep` (`thermalDensity x = thermalRep μ x` for all `x`, and `thermalDensity ≤ M γ`).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- The data produced by THM-3/THM-4 for the Riesz kernel and the Gaussian comparison density. -/
theorem t5_exists_fixed (hd : 1 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β) :
    ∃ (B M : ℝ) (μ : Euc d → ℝ), ThmSetting (t5K d s) (gaussianComparison d a β) B ∧ 1 ≤ M ∧
      Real.exp (β * B) ≤ M ∧ μ ∈ Cset (gaussianComparison d a β) M ∧
      μ =ᵐ[volume] Tmap (t5K d s) (gaussianComparison d a β) β μ := by
  obtain ⟨B, hS⟩ := t5_setting hd hs0 hsd ha hβ
  have hM : 1 ≤ max 1 (Real.exp (β * B)) := le_max_left _ _
  have hexp : Real.exp (β * B) ≤ max 1 (Real.exp (β * B)) := le_max_right _ _
  obtain ⟨μ, hμ, hmin⟩ := exists_min_Cset hS hM hβ
  exact ⟨B, _, μ, hS, hM, hexp, hμ, fixedpoint_of_min hS hβ hM hexp hμ hmin⟩

/-- Everything about `thermalDensity` for `0 < s < d`: it is the pointwise representative `thermalRep μ` of an a.e.
Euler fixed point `μ ∈ Cset γ M` minimising `G`, and `thermalDensity ≤ M γ`. -/
theorem thermalDensity_eq_thermalRep (hd : 1 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) :
    ∃ (B M : ℝ) (μ : Euc d → ℝ), ThmSetting (t5K d s) (gaussianComparison d a β) B ∧ 1 ≤ M ∧
      μ ∈ Cset (gaussianComparison d a β) M ∧
      μ =ᵐ[volume] Tmap (t5K d s) (gaussianComparison d a β) β μ ∧
      HRS.Whole.IsThermalEquilibrium d s a β (thermalRep (t5K d s) (gaussianComparison d a β) β μ) ∧
      (∀ x, thermalDensity d s a β x = thermalRep (t5K d s) (gaussianComparison d a β) β μ x) ∧
      (∀ x, thermalDensity d s a β x ≤ M * gaussianComparison d a β x) ∧
      (∀ l : Euc d → ℝ, HRS.Whole.IsFreeEnergyMinimizer (rieszKernel d s) (confinement a) β l →
        l =ᵐ[volume] thermalRep (t5K d s) (gaussianComparison d a β) β μ) := by
  obtain ⟨B, M, μ, hS, hM, hexp, hμ, hfix⟩ := t5_exists_fixed hd hs0 hsd ha hβ
  have hρC := thermalRep_mem_Cset hS hβ.le hexp hμ.1
  have hρfix := thermalRep_fixed hfix
  have hEq := t5_equilibrium_of_fixed hd hs0 hsd ha hβ hM hS hρC hρfix
  have hex : ∃ ρ, HRS.Whole.IsThermalEquilibrium d s a β ρ := ⟨_, hEq⟩
  have hτ : HRS.Whole.IsThermalEquilibrium d s a β (thermalDensity d s a β) := by
    unfold thermalDensity
    rw [dif_pos hex]
    exact hex.choose_spec
  have hae := t5_minimizer_ae_eq hd hs0 hsd ha hβ hM hS hρC hρfix hτ.1
  have hpt : ∀ x, thermalDensity d s a β x = thermalRep (t5K d s) (gaussianComparison d a β) β μ x :=
    thermalDensity_eq_pointwise hτ.2 hEq.2 hae
  exact ⟨B, M, μ, hS, hM, hμ, hfix, hEq, hpt, fun x => (hpt x).symm ▸ hρC.2 x,
    fun l hl => t5_minimizer_ae_eq hd hs0 hsd ha hβ hM hS hρC hρfix hl⟩

/-- **THM-5.**  The thermal equilibrium of the `s > 0` Riesz gas in a quadratic confinement exists, is bounded,
is the unique free-energy minimiser (a.e.), and is `thermalDensity`. -/
theorem thermalDensity_spec_proof : type_of% @HRS.Whole.thermalDensity_spec := by
  intro d s hd hs0 hsd a β ha hβ
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, M, μ, hS, hM, hμ, hfix, hEq, hpt, hle, hmin⟩ := thermalDensity_eq_thermalRep hd1 hs0 hsd ha hβ
  have hbd : ∃ C : ℝ, ∀ x, thermalRep (t5K d s) (gaussianComparison d a β) β μ x ≤ C := by
    refine ⟨M * t5c d a β, fun x => ?_⟩
    have h1 : thermalRep (t5K d s) (gaussianComparison d a β) β μ x ≤ M * gaussianComparison d a β x := by
      rw [← hpt x]; exact hle x
    exact h1.trans (mul_le_mul_of_nonneg_left (gaussianComparison_le ha hβ x) (by linarith))
  refine ⟨⟨_, hEq, hbd⟩, ?_, ?_⟩
  · intro ρ ρ' h h'
    exact (hmin ρ h).trans (hmin ρ' h').symm
  · intro ρ h
    refine (hmin ρ h).trans (Filter.EventuallyEq.symm ?_)
    exact ae_of_all _ fun x => hpt x

end HRS.MS.Thm

end
