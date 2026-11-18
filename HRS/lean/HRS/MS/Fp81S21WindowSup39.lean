import HRS.MS.Fp81S21WindowSup38

/-! Integrability of a fixed frozen-source raw orbit slice. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.S53

/-- A sixth moment gives integrability of each raw frozen-source orbit slice. -/
theorem fp81s21_frozen_raw_slice_integrable
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {σ T : ℝ} {ρ : Euc d → ℝ} (hT : 0 ≤ T)
    (hρ : HRS.Whole.IsProbDensity ρ) (G : ℝ → Euc d → ℝ)
    (hG : ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (G τ)) (hc : S53Cont T G)
    (X : Ω → EucConfig d N) (hX : Measurable X) (M : ℝ)
    (hSix : ∀ τ ∈ Icc (0 : ℝ) T, SixthBound P
      (fun ω => fp81s21_frozen_raw_field σ ρ G X (τ, ω)) M) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      Integrable (fun ω => fp81s21_frozen_raw_field σ ρ G X (τ, ω)) P := by
  let raw : ℝ × Ω → ℝ := fp81s21_frozen_raw_field σ ρ G X
  let F : ℝ × Ω → ℝ := fun z => raw (s53_clamp T z.1, z.2)
  have hF : Measurable F := by
    change Measurable (fun z : ℝ × Ω => (N : ℝ) / 2 *
      s53_Dk σ ρ (G (s53_clamp T z.1)) (X z.2))
    exact fp81s21_frozen_raw_s53_joint_meas hT hρ G hG hc X hX
  intro τ hτ
  have hSec := fp81s21_measurable_parameter_section F hF τ
  have heq : (fun ω => F (τ, ω)) = fun ω => raw (τ, ω) := by
    funext ω
    change raw (s53_clamp T τ, ω) = raw (τ, ω)
    rw [s53_clamp_of_mem hτ]
  rw [heq] at hSec
  exact fp81s21_integrable_of_sixth P (fun ω => raw (τ, ω)) hSec M (hSix τ hτ)

#print axioms fp81s21_frozen_raw_slice_integrable
end HRS.Fp81.S21
end
