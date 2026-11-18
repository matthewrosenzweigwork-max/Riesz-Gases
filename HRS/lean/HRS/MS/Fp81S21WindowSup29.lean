import HRS.MS.Fp81S21WindowSup28
import HRS.MS.Fp81S21MovingMeas

/-! Two-time measurable version of the physical terminal-derivative field. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr

/-- On the physical time triangle the terminal-derivative quadratic field has
one jointly measurable version agreeing at all parameters almost surely. -/
theorem fp81s21_terminal_quad_particle_joint_modification
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hT : 0 < T)
    {N : ℕ} (A : Particle R N) (φ : Euc p.d → ℝ)
    (horb : S104nOrbit (r26t3_coeff R) φ T) :
    let S := {z : ℝ × ℝ // 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ T}
    ∃ G : S × A.Ω → ℝ, Measurable G ∧ ∀ᵐ ω ∂A.P, ∀ z : S,
      G (z, ω) = r2QuadField p.s (r26t3_mu R z.1.1) A.P A.X z.1.1 ω
        (propagatorW (r26t3_coeff R) z.1.1 z.1.2
          (generatorW (r26t3_coeff R) z.1.2 φ)) := by
  let S := {z : ℝ × ℝ // 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ T}
  obtain ⟨V, hV, hVe⟩ := fp81s21_window_terminal_derivative_gradient_joint_meas
    (r26t3_coeff R) φ horb
  let ρ : S → Euc p.d → ℝ := fun z x => R.ρ z.1.1 x
  let a : S → ℝ := fun z => z.1.1
  have ha : Measurable a := continuous_subtype_val.fst.measurable
  have hρ : Measurable (fun q : S × Euc p.d => ρ q.1 q.2) := by
    have h0 := fp81s21_moving_density_joint_meas p (H := T) R hδ hδh
    have hm : Measurable (fun q : S × Euc p.d =>
        ((⟨q.1.1.1, ⟨q.1.2.1, q.1.2.2.1.trans q.1.2.2.2⟩⟩ : Icc (0 : ℝ) T), q.2)) := by
      exact (ha.comp measurable_fst |>.subtype_mk).prodMk measurable_snd
    exact h0.comp hm
  have hρ0 : ∀ z x, 0 ≤ ρ z x := by
    intro z x
    exact ((R.resulting.global T).density z.1.1
      ⟨z.2.1, z.2.2.1.trans z.2.2.2⟩).nonneg x
  let K : (ℝ × ℝ) × (Euc p.d × Euc p.d) → ℝ := fun q =>
    commutatorKernel p.d p.s (V q.1) q.2.1 q.2.2
  have hK : Measurable K := fp81s21_param_commutator_kernel_joint_meas p.s hV
  let k : S → Euc p.d → Euc p.d → ℝ := fun z x y => K (z.1, (x, y))
  have hk : Measurable (fun q : S × Euc p.d × Euc p.d => k q.1 q.2.1 q.2.2) := by
    change Measurable (fun q : S × (Euc p.d × Euc p.d) => K (q.1.1, q.2))
    exact fp81s21_measurable_restrict_parameter hK
  obtain ⟨G, hG, hGe⟩ := fp81s21_param_centered_pairEnergy_particle_modification
    A.P A.X (fun t => (A.strong T).adapted t) (A.strong T).cont
    a ha ρ k hρ hρ0 hk
  refine ⟨G, hG, ?_⟩
  filter_upwards [hGe] with ω hω z
  rw [hω z]
  have hkernel : k z = commutatorKernel p.d p.s
      (gradient (propagatorW (r26t3_coeff R) z.1.1 z.1.2
        (generatorW (r26t3_coeff R) z.1.2 φ))) := by
    have hVeq : V z.1 = gradient (propagatorW (r26t3_coeff R) z.1.1 z.1.2
        (generatorW (r26t3_coeff R) z.1.2 φ)) := by
      funext x
      exact hVe z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2 x
    simp only [k, K, hVeq]
  simp only [a, ρ, r26t3_mu, r2QuadField, hkernel]

#print axioms fp81s21_terminal_quad_particle_joint_modification
end HRS.Fp81.S21
end
