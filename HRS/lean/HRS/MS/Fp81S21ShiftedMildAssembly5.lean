import HRS.MS.Fp81S21ShiftedMildAssembly4

/-! Package the per-mode 10c certificates into the common event required by
rational-time transfer and the all-time continuity extension. -/
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MP.RdRem

/-- The all-time shifted mild identity follows from the per-mode drift
certificates; countability of the oscillator modes supplies one common event. -/
theorem fp81s21_shifted_mild_coord_all_times_of_per_mode_certificate
    (p : Parameters) {δ b H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hb : 0 ≤ b) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A (b + H))
    (G : A.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H)
    (hNoise : fp81s21_NoiseMatch p R A F hH b G)
    {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hData : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (b + H) r c)
    (hcert : ∀ α : MultiIndex p.d, ∀ᵐ ω ∂A.P,
      (∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ b + H →
        IntervalIntegrable
          (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t) ∧
      ContinuousOn
        (fun t => fp81s21_shiftedModeDrift p R A α b t ω)
        (Icc b (b + H))) :
    ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d, ∀ t ∈ Icc b (b + H),
      OscDual.coord
          (fp81s21_particleZeta p R A t ω -
            fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)) α =
        fp81s21_shiftedModeInitial p R A α b t ω -
          (Real.sqrt (N : ℝ))⁻¹ *
            fp81s21_shiftedModeDrift p R A α b t ω := by
  have hcertAll : ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d,
      (∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ b + H →
        IntervalIntegrable
          (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t) ∧
      ContinuousOn
        (fun t => fp81s21_shiftedModeDrift p R A α b t ω)
        (Icc b (b + H)) := by
    apply ae_all_iff.2
    intro α
    exact hcert α
  exact fp81s21_shifted_mild_coord_all_times p R hδ hδh hb hH hN A F
    hphys G hNoise hData hcertAll

#print axioms HRS.Fp81.S21.fp81s21_shifted_mild_coord_all_times_of_per_mode_certificate

end HRS.Fp81.S21

end
