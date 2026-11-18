import HRS.MS.Fp81S21WindowSup26
import HRS.MS.R2S11Aux10

/-! A single full-measure event transfers the centered field to the original particle path. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole

/-- A measurable modification of a continuous particle path gives a jointly
measurable centered field equal to the original field at all parameters on one
event of full measure. -/
theorem fp81s21_param_centered_pairEnergy_particle_modification
    {S Ω : Type} [MeasurableSpace S] [MeasurableSpace Ω]
    {d N : ℕ} (P : Measure Ω) [SFinite P]
    (X : ℝ≥0 → Ω → EucConfig d N)
    (hm : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i)
    (a : S → ℝ) (ha : Measurable a)
    (ρ : S → Euc d → ℝ) (k : S → Euc d → Euc d → ℝ)
    (hρ : Measurable (fun q : S × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ z x, 0 ≤ ρ z x)
    (hk : Measurable (fun q : S × Euc d × Euc d => k q.1 q.2.1 q.2.2)) :
    ∃ G : S × Ω → ℝ, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ z : S,
        G (z, ω) = (N : ℝ) *
          (pairEnergy (k z) (X (a z).toNNReal ω) (HRS.Whole.withDensityReal (ρ z)) -
           ∫ ω', pairEnergy (k z) (X (a z).toNNReal ω')
             (HRS.Whole.withDensityReal (ρ z)) ∂P) := by
  obtain ⟨X', hX', hXae⟩ := HRS.MS.R2S11.s11_X_joint hm hc
  let Y : S × Ω → EucConfig d N := fun z => X' (a z.1, z.2)
  have hY : Measurable Y := hX'.comp ((ha.comp measurable_fst).prodMk measurable_snd)
  let G : S × Ω → ℝ := fun z => (N : ℝ) *
    (pairEnergy (k z.1) (Y z) (HRS.Whole.withDensityReal (ρ z.1)) -
      ∫ ω, pairEnergy (k z.1) (Y (z.1, ω)) (HRS.Whole.withDensityReal (ρ z.1)) ∂P)
  refine ⟨G, fp81s21_param_centered_pairEnergy_joint_meas P Y hρ hρ0 hk hY, ?_⟩
  filter_upwards [hXae] with ω hω z
  have hInt : (∫ ω', pairEnergy (k z) (Y (z, ω')) (HRS.Whole.withDensityReal (ρ z)) ∂P) =
      ∫ ω', pairEnergy (k z) (X (a z).toNNReal ω') (HRS.Whole.withDensityReal (ρ z)) ∂P := by
    apply integral_congr_ae
    filter_upwards [hXae] with ω' hω'
    rw [show Y (z, ω') = X (a z).toNNReal ω' from hω' (a z)]
  dsimp [G]
  rw [show Y (z, ω) = X (a z).toNNReal ω from hω (a z), hInt]

#print axioms fp81s21_param_centered_pairEnergy_particle_modification
end HRS.Fp81.S21
end
