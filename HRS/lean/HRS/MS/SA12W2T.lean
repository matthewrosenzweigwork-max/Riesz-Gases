import HRS.MS.SA12W2S

/-!
# S.A.12 C5 (SA12W2 worker), part T: unit-torus generator conjugacy (`R26-T5.T05`)

`sa12w2_torus_generator` is the contract `r26t5_torus_generator`: for the rescaled torus data `D₁` and density `ρ`,
the unit-torus backward generator at `x/L` is the physical operator `ν Δ + ⟨b,∇⟩ - 𝒢_L` evaluated at `x`, for every
`τ ∈ [0,t]`.  It is the pointwise identity `sa12w2_key` (part Q) with the density `ρ (t-τ)` identified by its lift.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12w2_torus_generator (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (T L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ)
    (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d)
    (hP : PerSmooth s T L γ M ν μ V b) (hTime : PeriodicTimeSmooth T μ)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (D₁ : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hDs : D₁.s = s) (hDM : D₁.M = (L ^ (-s - 2)) • M) (hDν : D₁.invβ = ν / L ^ 2)
    (hDV : Torus.lift D₁.V = fun y => V (L • y) / L ^ 2)
    (hρ : ∀ r ∈ Icc (0 : ℝ) T, Torus.lift (ρ r) = fun y => L ^ d * μ (max (t - r) 0) (L • y))
    (f : Torus d → ℝ) (hf : ContDiff ℝ ∞ (Torus.lift f)) :
    ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d,
      backwardGenerator D₁ (ρ (t - τ)) f (Torus.mk (L⁻¹ • x)) =
        ν * Laplacian.laplacian (fun y => Torus.lift f (L⁻¹ • y)) x +
        inner ℝ (b τ x) (gradient (fun y => Torus.lift f (L⁻¹ • y)) x) -
        perNonlocal L γ M (μ τ) (fun y => Torus.lift f (L⁻¹ • y)) x := by
  intro τ hτ x
  have hL : 0 < L := by linarith [hP.hL]
  have hT : t ≤ T := ht.2
  have ht0 : 0 < t := ht.1
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans hT⟩
  have hr : t - τ ∈ Icc (0 : ℝ) T := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hper := hP.μ_periodic τ hτT
  have hρeq : ρ (t - τ) = sa12w2_dens L (μ τ) := by
    apply sa12w2_eq_of_lift
    funext y
    rw [hρ (t - τ) hr, sa12w2_dens_lift (fun x z => hper x z) y]
    have hmax : max (t - (t - τ)) 0 = τ := by
      rw [sub_sub_cancel]
      exact max_eq_left hτ.1
    rw [hmax]
  have hkey := sa12w2_key hd hs0 hsd hL hP hτT D₁ hDs hDM hDν hDV f hf x
  rw [hρeq]
  exact hkey.symm

end HRS.PDE.SA12W2
