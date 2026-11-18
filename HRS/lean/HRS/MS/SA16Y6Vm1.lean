import HRS.MS.SA16Y5Vg3
import HRS.MS.SA16RDuh1

/-!
# S.A.16 (SA16Y6) Vm1: Volterra existence and uniqueness for a kernel with a `1/2`-singular part and a `γ`-singular part (B8, part 1)

`sa16y6_volt_exists_unique_add`: if `P₁` is a `VoltKer` (`‖P₁ τ s‖ ≤ C₁ s^{-1/2}`) and `Q` is a `VoltKerG γ` (`1/2 ≤ γ < 1`), then
`u = f0 + voltOp (P₁ + Q) u` has a unique continuous solution on `[0,T]`.  Used with `P₁ = gainKer Γ K` (drift and bounded part) and
`Q = -Γ_s 𝒢` (the fractional nonlocal part, `‖Γ_s 𝒢‖ ≤ C s^{-θ'/2}`, `θ'/2 ∈ [1/2,1)`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

section Vm1
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {γ : ℝ}

lemma sa16y6_VoltKer_toG {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (h : VoltKer T C P) (hC : 0 ≤ C)
    (hγ0 : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hT : 0 < T) : VoltKerG γ T (C * T ^ (γ - 1 / 2)) P where
  γ0 := by linarith
  γ1 := hγ1
  bound := fun τ s hs hsτ hτ => by
    refine (h.bound τ s hs hsτ hτ).trans ?_
    have hsT : s ≤ T := hsτ.trans hτ
    have h1 : s ^ (-(1 / 2 : ℝ)) = s ^ (-γ) * s ^ (γ - 1 / 2) := by
      rw [← Real.rpow_add hs]; ring_nf
    have h2 : s ^ (γ - 1 / 2) ≤ T ^ (γ - 1 / 2) := Real.rpow_le_rpow hs.le hsT (by linarith)
    rw [h1]
    have h3 : 0 ≤ s ^ (-γ) := Real.rpow_nonneg hs.le _
    calc C * (s ^ (-γ) * s ^ (γ - 1 / 2)) = (C * s ^ (-γ)) * s ^ (γ - 1 / 2) := by ring
      _ ≤ (C * s ^ (-γ)) * T ^ (γ - 1 / 2) := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC h3)
      _ = C * T ^ (γ - 1 / 2) * s ^ (-γ) := by ring
  cont := h.cont

lemma sa16y6_VoltKerG_add {T C₁ C₂ : ℝ} {P₁ P₂ : ℝ → ℝ → X →L[ℝ] X} (h₁ : VoltKerG γ T C₁ P₁)
    (h₂ : VoltKerG γ T C₂ P₂) : VoltKerG γ T (C₁ + C₂) (fun τ s => P₁ τ s + P₂ τ s) where
  γ0 := h₁.γ0
  γ1 := h₁.γ1
  bound := fun τ s hs hsτ hτ => by
    refine (norm_add_le _ _).trans ?_
    have := add_le_add (h₁.bound τ s hs hsτ hτ) (h₂.bound τ s hs hsτ hτ)
    linarith
  cont := fun x => by
    have := (h₁.cont x).add (h₂.cont x)
    refine this.congr fun q _ => ?_
    simp [ContinuousLinearMap.add_apply]

theorem sa16y6_volt_exists_unique_add {T C₁ C₂ : ℝ} {P₁ Q : ℝ → ℝ → X →L[ℝ] X} (h₁ : VoltKer T C₁ P₁)
    (hC₁ : 0 ≤ C₁) (hγ0 : 1 / 2 ≤ γ) (hQ : VoltKerG γ T C₂ Q) (hT : 0 < T)
    {f0 : ℝ → X} (hf0 : ContinuousOn f0 (Icc 0 T)) :
    ∃ u : ℝ → X, ContinuousOn u (Icc 0 T) ∧
      (∀ τ ∈ Icc (0 : ℝ) T, u τ = f0 τ + voltOp (fun τ s => P₁ τ s + Q τ s) u τ) ∧
      ∀ v : ℝ → X, ContinuousOn v (Icc 0 T) →
        (∀ τ ∈ Icc (0 : ℝ) T, v τ = f0 τ + voltOp (fun τ s => P₁ τ s + Q τ s) v τ) →
        ∀ τ ∈ Icc (0 : ℝ) T, v τ = u τ :=
  sa16y5g_volt_exists_unique (sa16y6_VoltKerG_add (sa16y6_VoltKer_toG h₁ hC₁ hγ0 hQ.γ1 hT) hQ) hT hf0

end Vm1

end HRS.Whole.AppendixA.Phase2SA16R
