import HRS.MS.Fp81S21WindowSup48

/-! Measurable baseline quadratic field for a fixed test. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- A fixed measurable commutator kernel gives a jointly measurable baseline
quadratic field on the physical interval, with one full-measure transfer event. -/
theorem fp81s21_baseline_quad_zero_extension
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hT : 0 < T)
    {N : ℕ} (A : Particle R N) (φ : Euc p.d → ℝ)
    (hkernel : Measurable (fun z : Euc p.d × Euc p.d =>
      commutatorKernel p.d p.s (gradient φ) z.1 z.2)) :
    ∃ Q : ℝ × A.Ω → ℝ, Measurable Q ∧
      (∀ᵐ ω ∂A.P, ∀ v ∈ Icc (0 : ℝ) T,
        Q (v, ω) = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ) ∧
      (∀ z, z.1 ∉ Icc (0 : ℝ) T → Q z = 0) := by
  let S := Icc (0 : ℝ) T
  let ρ : S → Euc p.d → ℝ := fun v x => R.ρ v.1 x
  let k : S → Euc p.d → Euc p.d → ℝ := fun _ => commutatorKernel p.d p.s (gradient φ)
  let a : S → ℝ := fun v => v.1
  have ha : Measurable a := measurable_subtype_coe
  have hρ : Measurable (fun z : S × Euc p.d => ρ z.1 z.2) :=
    fp81s21_moving_density_joint_meas p R hδ hδh
  have hρ0 : ∀ v x, 0 ≤ ρ v x := by
    intro v x
    exact ((R.resulting.global T).density v.1 v.2).nonneg x
  have hk : Measurable (fun z : S × Euc p.d × Euc p.d => k z.1 z.2.1 z.2.2) :=
    hkernel.comp measurable_snd
  obtain ⟨q, hq, hqe⟩ := fp81s21_param_centered_pairEnergy_particle_modification
    A.P A.X (fun t => (A.strong T).adapted t) (A.strong T).cont a ha ρ k hρ hρ0 hk
  obtain ⟨Q, hQ, hQe, hQzero⟩ :=
    fp81s21_param_measurable_zero_extension measurableSet_Icc q hq
  refine ⟨Q, hQ, ?_, hQzero⟩
  filter_upwards [hqe] with ω hω v hv
  let z : S := ⟨v, hv⟩
  rw [hQe z ω, hω z]
  rfl

#print axioms fp81s21_baseline_quad_zero_extension
end HRS.Fp81.S21
end
