import HRS.MS.Fp81S21WindowSup47

/-! Measurable zero extension of the physical terminal quadratic field. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr

/-- The terminal-generator quadratic field has a jointly measurable
zero extension agreeing with the particle field simultaneously on the
physical time triangle on one full-measure event. -/
theorem fp81s21_terminal_quad_zero_extension
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hT : 0 < T)
    {N : ℕ} (A : Particle R N) (φ : Euc p.d → ℝ)
    (horb : S104nOrbit (r26t3_coeff R) φ T) :
    ∃ K : (ℝ × ℝ) × A.Ω → ℝ, Measurable K ∧
      (∀ᵐ ω ∂A.P, ∀ v s : ℝ, 0 ≤ v → v ≤ s → s ≤ T →
        K ((v, s), ω) = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v s (generatorW (r26t3_coeff R) s φ))) ∧
      (∀ z, ¬ (0 ≤ z.1.1 ∧ z.1.1 ≤ z.1.2 ∧ z.1.2 ≤ T) → K z = 0) := by
  let B : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ T}
  have hB : MeasurableSet B := by
    exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
  obtain ⟨g, hg, hge⟩ := fp81s21_terminal_quad_particle_joint_modification
    p R hδ hδh hT A φ horb
  obtain ⟨K, hK, hKe, hKzero⟩ := fp81s21_param_measurable_zero_extension hB g hg
  refine ⟨K, hK, ?_, ?_⟩
  · filter_upwards [hge] with ω hω v s hv hvs hs
    let z : B := ⟨(v, s), ⟨hv, hvs, hs⟩⟩
    exact (hKe z ω).trans (hω z)
  · exact hKzero

#print axioms fp81s21_terminal_quad_zero_extension
end HRS.Fp81.S21
end
