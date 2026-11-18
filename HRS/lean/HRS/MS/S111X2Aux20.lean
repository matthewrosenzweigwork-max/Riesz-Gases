import HRS.MS.S111X2Aux2
import HRS.MS.S111BDAux4
import HRS.Whole.Window

/-!
# S11.1 X2, clause (a): assembly from the finite-projection covariance bound H02

`S11X2H02` is the exact interface of packet H02 (the finite-projection covariance comparison of the two shifted
windows, with the rate `e^{-2(λ/β)u}`).  `s111x2_clauseA_of_H02` derives clause (a) of `r2_tensor_relaxation` from it,
by the Gaussian second moments `S111BD.s111_shifted_window_gaussian` (preserved packet G2) and the projection removal
`s111x2_covariance_projection_limit` (H03).  No coupling of the two realizations is needed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S111X2

open HRS.Whole
open HRS (Euc)

/-- Interface of H02: the projected window covariances are `B e^{-2(λ/β)u}` close (all realizations). -/
def S11X2H02 (d : ℕ) (s a β γ T lam : ℝ) (hT : 0 < T) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
    IsR2Poincare (HRS.Whole.withDensityReal ρβ) lam →
    ∀ {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
      [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
      (Z₁ : ℝ → Ω₁ → OscDual d (wholeSpaceIndex d : ℝ)) (Z₂ : ℝ → Ω₂ → OscDual d (wholeSpaceIndex d : ℝ)),
      (∀ T' : ℝ, IsLinearGaussianEvolutionW P₁ ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
        (wholeSpaceIndex d) β⁻¹ T' (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρβ) γ) Z₁) →
      (∀ T' : ℝ, IsLinearGaussianEvolutionW P₂ ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
        (wholeSpaceIndex d) β⁻¹ T' (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρβ) β) Z₂) →
      ∀ u : ℝ, 0 ≤ u → ∀ n : ℕ, ∀ M : (R2X d T) [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
        |∫ ζ, M ![HRS.MS.R2Interp.s102_Pj (d := d) (m := (wholeSpaceIndex d : ℝ)) T hT n
            (processWindow (wholeSpaceIndex d) T u Z₁ ζ),
            HRS.MS.R2Interp.s102_Pj (d := d) (m := (wholeSpaceIndex d : ℝ)) T hT n
            (processWindow (wholeSpaceIndex d) T u Z₁ ζ)] ∂P₁ -
          ∫ ζ, M ![HRS.MS.R2Interp.s102_Pj (d := d) (m := (wholeSpaceIndex d : ℝ)) T hT n
            (processWindow (wholeSpaceIndex d) T 0 Z₂ ζ),
            HRS.MS.R2Interp.s102_Pj (d := d) (m := (wholeSpaceIndex d : ℝ)) T hT n
            (processWindow (wholeSpaceIndex d) T 0 Z₂ ζ)] ∂P₂| ≤
          B * Real.exp (-2 * (lam / β) * u)

/-- Clause (a) of `r2_tensor_relaxation` (law-only statement), for a fixed thermal reference and constant `C`. -/
def S11X2ClauseA (d : ℕ) (s a β γ T lam : ℝ) (C : ℝ) (ρβ : Euc d → ℝ) : Prop :=
  ∀ {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] (Z₁ : ℝ → Ω₁ → OscDual d (wholeSpaceIndex d : ℝ))
    (Z₂ : ℝ → Ω₂ → OscDual d (wholeSpaceIndex d : ℝ)),
    (∀ T' : ℝ, IsLinearGaussianEvolutionW P₁ ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
      (wholeSpaceIndex d) β⁻¹ T' (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρβ) γ) Z₁) →
    (∀ T' : ℝ, IsLinearGaussianEvolutionW P₂ ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
      (wholeSpaceIndex d) β⁻¹ T' (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρβ) β) Z₂) →
    ∀ u : ℝ, 0 ≤ u → ∀ M : (R2X d T) [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
      |∫ ζ, M ![processWindow (wholeSpaceIndex d) T u Z₁ ζ, processWindow (wholeSpaceIndex d) T u Z₁ ζ] ∂P₁ -
        ∫ ζ, M ![processWindow (wholeSpaceIndex d) T 0 Z₂ ζ, processWindow (wholeSpaceIndex d) T 0 Z₂ ζ] ∂P₂| ≤
        C * Real.exp (-2 * (lam / β) * u)

/-- Clause (b) of `r2_tensor_relaxation`, for a fixed thermal reference and constants `c, C`. -/
def S11X2ClauseB (d : ℕ) (s a β γ T : ℝ) (c C : ℝ) (ρβ : Euc d → ℝ) : Prop :=
  ∀ u : ℝ, 0 ≤ u → ∀ κu κβ : projTensor (R2X d T) 3,
    IsR2PathCubic d s a β γ ρβ T u κu → IsR2PathCubic d s a β β ρβ T 0 κβ →
    ‖κu - κβ‖ ≤ C * Real.exp (-c * u)

/-- **Clause (a) of `r2_tensor_relaxation` from H02.** -/
theorem s111x2_clauseA_of_H02 (d : ℕ) (s a β γ T lam : ℝ) (hT : 0 < T) (h02 : S11X2H02 d s a β γ T lam hT) :
    ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      IsR2Poincare (HRS.Whole.withDensityReal ρβ) lam → S11X2ClauseA d s a β γ T lam C ρβ := by
  obtain ⟨B, -, hB⟩ := h02
  refine ⟨B, fun ρβ hρ hP Ω₁ Ω₂ _ _ P₁ P₂ _ _ Z₁ Z₂ hZ₁ hZ₂ u hu M hM => ?_⟩
  have hG₁ := HRS.MS.S111BD.s111_shifted_window_gaussian d P₁
    ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) (wholeSpaceIndex d : ℝ) β⁻¹ T u (u + T)
    (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρβ) γ) Z₁ (hZ₁ (u + T)) hT hu le_rfl
  have hG₂ := HRS.MS.S111BD.s111_shifted_window_gaussian d P₂
    ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) (wholeSpaceIndex d : ℝ) β⁻¹ T 0 T
    (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρβ) β) Z₂ (hZ₂ T) hT le_rfl (by linarith)
  have hproj := HRS.MS.R2Interp.s102_projection_strong (d := d) (wholeSpaceIndex d : ℝ) T hT
  exact s111x2_covariance_projection_limit P₁ P₂ _ _ hG₁.2.2 hG₂.2.2
    (fun n => HRS.MS.R2Interp.s102_Pj (d := d) (m := (wholeSpaceIndex d : ℝ)) T hT n)
    hproj.1 hproj.2.1 (B * Real.exp (-2 * (lam / β) * u))
    (fun n M' hM' => hB ρβ hρ hP P₁ P₂ Z₁ Z₂ hZ₁ hZ₂ u hu n M' hM') M hM

theorem S11X2ClauseA.mono {d : ℕ} {s a β γ T lam : ℝ} {C C' : ℝ} {ρβ : Euc d → ℝ} (h : C ≤ C')
    (hA : S11X2ClauseA d s a β γ T lam C ρβ) : S11X2ClauseA d s a β γ T lam C' ρβ := by
  intro Ω₁ Ω₂ _ _ P₁ P₂ _ _ Z₁ Z₂ hZ₁ hZ₂ u hu M hM
  exact (hA P₁ P₂ Z₁ Z₂ hZ₁ hZ₂ u hu M hM).trans
    (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le)

/-- **Assembly of `r2_tensor_relaxation` from its two clauses.**  The conclusion is literally the type of the frozen
theorem, so a mismatch of the clause statements would be rejected by the elaborator. -/
theorem s111x2_tensor_relaxation_of_parts {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (a β γ : ℝ) (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hlam : 0 < lam)
    (hA : ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      IsR2Poincare (HRS.Whole.withDensityReal ρβ) lam → S11X2ClauseA d s a β γ T lam C ρβ)
    (hB : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      IsR2Poincare (HRS.Whole.withDensityReal ρβ) lam → S11X2ClauseB d s a β γ T c C ρβ) :
    type_of% (r2_tensor_relaxation hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam) := by
  obtain ⟨CA, hA⟩ := hA
  obtain ⟨c, hc, CB, hB⟩ := hB
  refine ⟨c, hc, max CA CB, fun ρβ hρ hP => ⟨S11X2ClauseA.mono (le_max_left _ _) (hA ρβ hρ hP), ?_⟩⟩
  intro u hu κu κβ h1 h2
  exact (hB ρβ hρ hP u hu κu κβ h1 h2).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

end HRS.MS.S111X2
