import HRS.MS.Fp81S21WindowSup41

/-! Direct modewise envelopes for both terminal-orbit kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr
open HRS.MS.R2WinOrb HRS.MS.R2WinOrbNL

/-- Uniform Hessian kernel envelopes for a propagated mode and its terminal
`U^{v,t} L_t` derivative, valid at both endpoints. -/
theorem fp81s21_window_terminal_kernel_envelopes (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ v t : ℝ, 0 ≤ v → v ≤ t →
      ∀ α : MultiIndex p.d,
        IsBoundedPairKernel p.s (max p.s 1 * Real.toNNReal (B * s104_b p.d α))
          (commutatorKernel p.d p.s (gradient (propagatorW (r26t3_coeff R) v t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) ∧
        IsBoundedPairKernel p.s (max p.s 1 * Real.toNNReal (B * s104_b p.d α))
          (commutatorKernel p.d p.s (gradient (propagatorW (r26t3_coeff R) v t
            (generatorW (r26t3_coeff R) t (oscTestFun (wholeSpaceIndex p.d : ℝ) α))))) := by
  obtain ⟨δ0, Co, co, hδ0, hδh, hco, hCommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hδh, ?_⟩
  intro δ hδ hδle R
  obtain ⟨hClaims, _, hTerm, _⟩ := hCommon δ hδ hδle R.ρβ R.thermal
  refine ⟨|Co|, abs_nonneg _, ?_⟩
  intro v t hv hvt α
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let C : WholeCoeff p.d := r26t3_coeff R
  let a : ℝ := |Co| * s103_b p.d α
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg _) (s103_b_nonneg α)
  have ht : 0 ≤ t := hv.trans hvt
  have horb : S104nOrbit C φ (t + 1) :=
    s104b_orbit_of_termRegGen hTerm R.admissible R.resulting α (t + 1) (by linarith)
  have ht' : t ∈ Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  obtain ⟨f0, hf0⟩ := horb.ex0 t ht'
  obtain ⟨f1, hf1⟩ := horb.ex1 t ht'
  have hs := hClaims R.ε R.ψ R.ρ R.admissible R.resulting α t ht
  have hca : Co * s103_b p.d α ≤ a :=
    mul_le_mul_of_nonneg_right (le_abs_self Co) (s103_b_nonneg α)
  have ho0 : R2OrbitSup C (4 * p.d + 42) t φ a :=
    s103_orbitSup_mono hs.1 hca
  have ho1 : R2OrbitSup C (4 * p.d + 42) t (generatorW C t φ) a :=
    s103_orbitSup_mono hs.2.2.1 hca
  have hU := ho0 (fun z => propagatorW C z t φ)
    (HRS.MS.Fcau.propagatorW_isClassical ⟨f0, hf0⟩) v ⟨hv, hvt⟩
  have hD := ho1 (fun z => propagatorW C z t (generatorW C t φ))
    (HRS.MS.Fcau.propagatorW_isClassical ⟨f1, hf1⟩) v ⟨hv, hvt⟩
  have hA : a = |Co| * s104_b p.d α := by rfl
  have huSmooth : ContDiff ℝ 2 (propagatorW C v t φ) :=
    hU.1.of_le (by norm_cast; omega)
  have hdSmooth : ContDiff ℝ 2 (propagatorW C v t (generatorW C t φ)) :=
    hD.1.of_le (by norm_cast; omega)
  have huHess : ∀ x, ‖iteratedFDeriv ℝ 2 (propagatorW C v t φ) x‖ ≤ a :=
    s103c_jets_of_r2cb ha hU.2 2 (by omega)
  have hdHess : ∀ x, ‖iteratedFDeriv ℝ 2
      (propagatorW C v t (generatorW C t φ)) x‖ ≤ a :=
    s103c_jets_of_r2cb ha hD.2 2 (by omega)
  constructor
  · simpa [C, φ, hA] using fp81s21_comm_kernel_of_hessian_bound p.hs0 ha huSmooth huHess
  · simpa [C, φ, hA] using fp81s21_comm_kernel_of_hessian_bound p.hs0 ha hdSmooth hdHess

#print axioms fp81s21_window_terminal_kernel_envelopes
end HRS.Fp81.S21
end
