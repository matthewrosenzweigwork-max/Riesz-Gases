import HRS.MC.L2C3Aux7

/-!
# Packet L2C-3, helper 8: stage 1 -- decay and weighted energy of `Q_β U^{t-τ,t} φ` (`S = 0`)

For the zero path `S = 0`, the Lyapunov inequality `L2C3Lyap` is closed by AM-GM and the weighted Poincaré
inequality; Grönwall gives the exponential decay of `Fv`, and the weighted energy estimate gives
`ν ∫₀^τ e^{aσ/2} ∫ρ_β|∇F(t-σ)|² dσ ≲ ‖Qφ‖²`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C3

variable {d : ℕ}

/-- The decay rate `a = ν c_P / κ₂`. -/
def l2c3_rate (R : Regime d) (Cx : Ctx R) : ℝ := R.β⁻¹ * Cx.cP / Cx.κ₂

theorem l2c3_rate_pos (R : Regime d) (Cx : Ctx R) : 0 < l2c3_rate R Cx := by
  have := R.hβ
  have := Cx.hcP
  have := Cx.hκ₂
  unfold l2c3_rate
  positivity

theorem l2c3_rate_mul (R : Regime d) (Cx : Ctx R) :
    l2c3_rate R Cx * Cx.κ₂ = R.β⁻¹ * Cx.cP := by
  have := Cx.hκ₂
  unfold l2c3_rate
  field_simp

theorem l2c3_Ev_zero (R : Regime d) (t : ℝ) (F : ℝ → Torus d → ℝ) (τ : ℝ) :
    l2c3_Ev R t F (fun _ _ => 0) τ = l2c3_E1 R t F τ := by
  simp only [l2c3_Ev, l2c3_E1, sub_zero, MFSemigroup.grad_projMean]

theorem l2c3_zero_hyps (R : Regime d) (t : ℝ) :
    (∀ τ ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 2 (((fun _ _ => 0) : ℝ → Torus d → ℝ) τ)) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) t, pair (withDensityReal R.ρβ) (((fun _ _ => 0) : ℝ → Torus d → ℝ) τ) = 0) ∧
    (Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => (((fun _ _ => 0) : ℝ → Torus d → ℝ) p.1 p.2)) ∧
    (Continuous fun p : Set.Icc (0 : ℝ) t × Torus d =>
        equilibriumGen d R.D.s R.ρβ R.β⁻¹ (((fun _ _ => 0) : ℝ → Torus d → ℝ) p.1) p.2) ∧
    (∀ x : Torus d, ∀ τ ∈ Set.Ioo (0 : ℝ) t,
        HasDerivAt (fun τ' => (((fun _ _ => 0) : ℝ → Torus d → ℝ) τ') x)
          (equilibriumGen d R.D.s R.ρβ R.β⁻¹ (((fun _ _ => 0) : ℝ → Torus d → ℝ) τ) x) τ) := by
  have hz := l2c3_eqGen_zero (d := d) R.D.s R.ρβ R.β⁻¹
  refine ⟨fun τ _ => ?_, fun τ _ => ?_, continuous_const, ?_, fun x τ _ => ?_⟩
  · exact (contDiff_const : ContDiff ℝ 2 fun _ : Euc d => (0 : ℝ))
  · simp [pair]
  · simp only [hz]; exact continuous_const
  · simp only [hz]; exact hasDerivAt_const _ _

theorem l2c3_Nn_nonneg (R : Regime d) (t : ℝ) (F : ℝ → Torus d → ℝ) (τ : ℝ) :
    0 ≤ l2c3_Nn R t F τ :=
  integral_nonneg fun x => sq_nonneg _

theorem l2c3_Nn_le (R : Regime d) (Cx : Ctx R) {t : ℝ} {F : ℝ → Torus d → ℝ} {τ : ℝ}
    (hF1 : Torus.IsCk 1 (F (t - τ))) :
    Cx.c₀ * l2c3_Nn R t F τ ≤ l2c3_E1 R t F τ := by
  have hc : Continuous fun x => ‖Torus.grad (F (t - τ)) x‖ ^ 2 := (continuous_grad hF1).norm.pow 2
  unfold l2c3_Nn l2c3_E1
  rw [← integral_const_mul]
  refine integral_mono (l2c3_integrable (hc.const_mul _)) (l2c3_integrable (Cx.hρc.mul hc)) fun x => ?_
  exact mul_le_mul_of_nonneg_right (Cx.hlow' x) (sq_nonneg _)

end HRS.MC.L2C3
