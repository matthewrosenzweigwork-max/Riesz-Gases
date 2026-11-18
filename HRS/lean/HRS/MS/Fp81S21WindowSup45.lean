import HRS.MS.Fp81S21WindowSup44

/-! Uniform sixth-root estimates for physical quadratic slices. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

/-- Both propagated oscillator and terminal-generator quadratic slices have
uniform sixth-root bounds with one oscillator amplitude. -/
theorem fp81s21_window_quad_slices_sixth_root (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∀ v t : ℝ, 0 ≤ v → v ≤ t → ∀ α : MultiIndex p.d,
      (∫⁻ ω, ENNReal.ofReal |r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
        (propagatorW (r26t3_coeff R) v t (oscTestFun (wholeSpaceIndex p.d : ℝ) α))| ^
          (6 : ℝ) ∂A.P) ^ (1 / 6 : ℝ) ≤ ENNReal.ofReal (C * s104_b p.d α) ∧
      (∫⁻ ω, ENNReal.ofReal |r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
        (propagatorW (r26t3_coeff R) v t (generatorW (r26t3_coeff R) t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))| ^
          (6 : ℝ) ∂A.P) ^ (1 / 6 : ℝ) ≤ ENNReal.ofReal (C * s104_b p.d α) := by
  obtain ⟨δa, hδa, hδah, hSix⟩ := fp81s21_particle_sixth_quadField p
  obtain ⟨δb, hδb, hδbh, hKernel⟩ := fp81s21_window_terminal_kernel_envelopes p
  obtain ⟨δc, Co, co, hδc, hδch, hco, hCommon⟩ := fp81s21_common_radius p
  let δ0 := min δa (min δb δc)
  have hδ0 : 0 < δ0 := lt_min hδa (lt_min hδb hδc)
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδah
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R
  have hδa' : δ ≤ δa := hδle.trans (min_le_left _ _)
  have hδb' : δ ≤ δb := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδc' : δ ≤ δc := hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Cq, hCq, hMom⟩ := hSix δ hδ hδa' R
  obtain ⟨B, hB, hEn⟩ := hKernel δ hδ hδb' R
  obtain ⟨_, _, hTerm, _⟩ := hCommon δ hδ hδc' R.ρβ R.thermal
  let L : ℝ := max p.s 1 * B
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let C : ℝ := Cq ^ (1 / 6 : ℝ) * L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN A v t hv hvt α
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let W : WholeCoeff p.d := r26t3_coeff R
  let a : ℝ := s104_b p.d α
  have ha : 0 ≤ a := s104_b_nonneg α
  have ht : 0 ≤ t := hv.trans hvt
  have horb : S104nOrbit W φ (t + 1) :=
    s104b_orbit_of_termRegGen hTerm R.admissible R.resulting α (t + 1) (by linarith)
  have hv' : v ∈ Icc (0 : ℝ) (t + 1) := ⟨hv, by linarith⟩
  have hτ : t - v ∈ Icc (0 : ℝ) (t + 1 - v) := by constructor <;> linarith
  have hUmeas : Measurable (propagatorW W v t φ) := by
    have h := (horb.cb0 hv' hτ).1.continuous.measurable
    simpa only [add_sub_cancel] using h
  have hDmeas : Measurable (propagatorW W v t (generatorW W t φ)) := by
    have h := (horb.cb1 hv' hτ).1.continuous.measurable
    simpa only [add_sub_cancel] using h
  let K : ℝ := L * a
  have hK : 0 ≤ K := mul_nonneg hL ha
  have heq : max p.s 1 * (Real.toNNReal (B * s104_b p.d α) : ℝ) = K := by
    rw [Real.coe_toNNReal _ (mul_nonneg hB ha)]
    dsimp [K, L, a]
    ring
  have hEnv := hEn v t hv hvt α
  have hUenv : IsBoundedPairKernel p.s K
      (commutatorKernel p.d p.s (gradient (propagatorW W v t φ))) := by
    simpa only [heq, W, φ] using hEnv.1
  have hDenv : IsBoundedPairKernel p.s K
      (commutatorKernel p.d p.s (gradient (propagatorW W v t (generatorW W t φ)))) := by
    simpa only [heq, W, φ] using hEnv.2
  have hU := (hMom N hN A v hv K hK _ hUmeas hUenv).1
  have hD := (hMom N hN A v hv K hK _ hDmeas hDenv).1
  have hroot : (Cq * K ^ 6) ^ (1 / 6 : ℝ) = C * a := by
    dsimp [K, C]
    rw [fp81s21_real_sixth_root_product hCq hL ha]
  constructor
  · simpa only [hroot, C, a, W, φ] using
      (fp81s21_sixthBound_lintegral_root A.P _ (mul_nonneg hCq (pow_nonneg hK 6)) hU)
  · simpa only [hroot, C, a, W, φ] using
      (fp81s21_sixthBound_lintegral_root A.P _ (mul_nonneg hCq (pow_nonneg hK 6)) hD)

#print axioms fp81s21_window_quad_slices_sixth_root
end HRS.Fp81.S21
end
