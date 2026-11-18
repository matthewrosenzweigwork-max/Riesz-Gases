import HRS.MS.Fp81S21WindowSup42

/-! Centered frozen-source FTC for oscillator coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

/-- On every nonnegative time triangle, the physical oscillator-coordinate
quadratic field obeys the actual-law centered frozen-source FTC. -/
theorem fp81s21_window_mode_quad_frozen_ftc (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∀ T v : ℝ, 0 ≤ v → v ≤ T → ∀ α : MultiIndex p.d,
      ∀ τ ∈ Icc (0 : ℝ) (T - v), ∀ ω,
        r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v (v + τ)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) =
        r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α) +
        ∫ u in (0 : ℝ)..τ, r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v (v + u)
            (generatorW (r26t3_coeff R) (v + u)
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) := by
  obtain ⟨δa, hδa, hδah, hFTC⟩ := fp81s21_particle_quad_frozen_ftc p
  obtain ⟨δb, hδb, hδbh, hKernel⟩ := fp81s21_window_terminal_kernel_envelopes p
  obtain ⟨δc, Co, co, hδc, hδch, hco, hCommon⟩ := fp81s21_common_radius p
  let δ0 := min δa (min δb δc)
  have hδ0 : 0 < δ0 := lt_min hδa (lt_min hδb hδc)
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδah
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R N hN A T v hv hvT α τ hτ ω
  have hδa' : δ ≤ δa := hδle.trans (min_le_left _ _)
  have hδb' : δ ≤ δb := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδc' : δ ≤ δc := hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨_, _, hTerm, _⟩ := hCommon δ hδ hδc' R.ρβ R.thermal
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  have horb : S104nOrbit (r26t3_coeff R) φ T :=
    s104b_orbit_of_termRegGen hTerm R.admissible R.resulting α T (by linarith)
  obtain ⟨B, hB, hEn⟩ := hKernel δ hδ hδb' R
  let K : ℝ := max p.s 1 * Real.toNNReal (B * s104_b p.d α)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hK0 : ∀ u ∈ Icc (0 : ℝ) (T - v), IsBoundedPairKernel p.s K
      (commutatorKernel p.d p.s (gradient (propagatorW (r26t3_coeff R) v (v + u) φ))) := by
    intro u hu
    exact (hEn v (v + u) hv (by linarith [hu.1]) α).1
  have hK1 : ∀ u ∈ Icc (0 : ℝ) (T - v), IsBoundedPairKernel p.s K
      (commutatorKernel p.d p.s (gradient (propagatorW (r26t3_coeff R) v (v + u)
        (generatorW (r26t3_coeff R) (v + u) φ)))) := by
    intro u hu
    exact (hEn v (v + u) hv (by linarith [hu.1]) α).2
  have hdiag : propagatorW (r26t3_coeff R) v v φ = φ :=
    (HRS.MS.Fcau.propagatorW_isClassical (horb.ex0 v ⟨hv, hvT⟩)).terminal
  have h := hFTC δ hδ hδa' R N hN A T v hv hvT φ horb K hK hK0 hK1 τ hτ ω
  simpa only [hdiag, φ] using h

#print axioms fp81s21_window_mode_quad_frozen_ftc
end HRS.Fp81.S21
end
