import HRS.MS.S111X1Aux6

/-!
# S11.1 X1, part 7: the covariance functional is linear and `L²(μ)`-bounded on oscillator tests
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ} {s a β γ : ℝ} {ρ : Euc d → ℝ}

/-- the covariance functional `ψ ↦ Cov(Z^r(ψ), Z^t(φ))` -/
def Fcov (d : ℕ) (s a β γ : ℝ) (ρ : Euc d → ℝ) (r t : ℝ) (φ ψ : Euc d → ℝ) : ℝ :=
  HRS.Whole.linearGaussianCov (x1C d s a β ρ) β⁻¹
    (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ) r t ψ φ

theorem X1Input.F_lin (h : X1Input d s a β γ ρ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    {φ ψ₁ ψ₂ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d : ℝ) φ)
    (h₁ : IsOscTest (wholeSpaceIndex d : ℝ) ψ₁) (h₂ : IsOscTest (wholeSpaceIndex d : ℝ) ψ₂) (c : ℝ) :
    Fcov d s a β γ ρ r t φ (fun x => ψ₁ x + c * ψ₂ x) =
      Fcov d s a β γ ρ r t φ ψ₁ + c * Fcov d s a β γ ρ r t φ ψ₂ := by
  haveI := h.finite
  have c₁ := x1_prop_classical (h.exist r hr ψ₁ h₁)
  have c₂ := x1_prop_classical (h.exist r hr ψ₂ h₂)
  have cφ := x1_prop_classical (h.exist t ht φ hφ)
  have hr0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) r := ⟨le_rfl, hr⟩
  unfold Fcov HRS.Whole.linearGaussianCov
  -- first term
  have e1 := h.prop_lin hr h₁ h₂ c 0 hr0
  rw [e1, x1_suscept_lin (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ
    (x1_classical_memLp c₁ hr0 _) (x1_classical_memLp c₂ hr0 _) c]
  -- second term
  unfold HRS.Whole.noiseCovW
  have e2 : ∀ u ∈ Set.Icc (0 : ℝ) (min r t),
      (∫ x, inner ℝ (gradient (propagatorW (x1C d s a β ρ) u r (fun x => ψ₁ x + c * ψ₂ x)) x)
        (gradient (propagatorW (x1C d s a β ρ) u t φ) x) * (x1C d s a β ρ).ρ u x) =
      ∫ x, inner ℝ (gradient (fun y => propagatorW (x1C d s a β ρ) u r ψ₁ y +
          c * propagatorW (x1C d s a β ρ) u r ψ₂ y) x)
        (gradient (propagatorW (x1C d s a β ρ) u t φ) x) * ρ x := by
    intro u hu
    rw [h.prop_lin hr h₁ h₂ c u ⟨hu.1, hu.2.trans (min_le_left _ _)⟩]
    rfl
  rw [setIntegral_congr_fun measurableSet_Icc e2]
  have e3 := x1_pair_lin c₁ c₂ cφ h.int h.nonneg c
  have e4 : ∀ f : ℝ → Euc d → ℝ, (∫ u in Set.Icc (0 : ℝ) (min r t), ∫ x,
      inner ℝ (gradient (f u) x) (gradient (propagatorW (x1C d s a β ρ) u t φ) x) *
        (x1C d s a β ρ).ρ u x) = ∫ u in Set.Icc (0 : ℝ) (min r t), ∫ x,
      inner ℝ (gradient (f u) x) (gradient (propagatorW (x1C d s a β ρ) u t φ) x) * ρ x :=
    fun f => rfl
  rw [e4 (fun u => propagatorW (x1C d s a β ρ) u r ψ₁), e4 (fun u => propagatorW (x1C d s a β ρ) u r ψ₂)]
  rw [e3]
  ring

end HRS.MS.S111X1
