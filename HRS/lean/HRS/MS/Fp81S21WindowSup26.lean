import HRS.MS.Fp81S21WindowSup25

/-! Joint measurability of a centered parameterized pair energy. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole

/-- Jointly measurable densities, kernels and configurations yield a jointly
measurable actual-law centered pair-energy field. -/
theorem fp81s21_param_centered_pairEnergy_joint_meas
    {S Ω : Type} [MeasurableSpace S] [MeasurableSpace Ω]
    {d N : ℕ} (P : Measure Ω) [SFinite P]
    {ρ : S → Euc d → ℝ} {k : S → Euc d → Euc d → ℝ}
    (X : S × Ω → EucConfig d N)
    (hρ : Measurable (fun q : S × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ a x, 0 ≤ ρ a x)
    (hk : Measurable (fun q : S × Euc d × Euc d => k q.1 q.2.1 q.2.2))
    (hX : Measurable X) :
    Measurable (fun z : S × Ω => (N : ℝ) *
      (pairEnergy (k z.1) (X z) (HRS.Whole.withDensityReal (ρ z.1)) -
       ∫ ω, pairEnergy (k z.1) (X (z.1, ω)) (HRS.Whole.withDensityReal (ρ z.1)) ∂P)) := by
  let F : S × EucConfig d N → ℝ := fun z =>
    pairEnergy (k z.1) z.2 (HRS.Whole.withDensityReal (ρ z.1))
  have hF : Measurable F := fp81s21_param_pairEnergy_joint_meas hρ hρ0 hk
  exact fp81s21_param_centered_comp_meas P F X hF hX (N : ℝ)

#print axioms fp81s21_param_centered_pairEnergy_joint_meas
end HRS.Fp81.S21
end
