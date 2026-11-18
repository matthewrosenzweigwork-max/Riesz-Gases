import HRS.MS.Fp81S21WindowSup17
import HRS.MS.Fp81S21Uniform2

/-!
# S2.1(iii), packet 9d: uniform modewise kernel envelopes

The common-radius producer supplies `S101Data` on every finite horizon with a
coefficient independent of the horizon. Its `bddU` and `bddD` clauses through
order two give Hessian bounds for the propagated coordinate and its compiled
terminal derivative. File 17 turns those bounds into the exact weighted
`IsBoundedPairKernel` envelopes used by the particle sixth-moment clause.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.CovMeas HRS.MS.R26T3 HRS.MS.R2WinOrb HRS.MS.R2WinErr
open Set

namespace HRS.Fp81.S21

/-- Uniform weighted pair-kernel envelopes for the propagated mode and its
terminal derivative, with the coefficient selected before the window and
mode. -/
theorem fp81s21_window_commutator_kernel_envelopes (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ b : ℝ, 0 ≤ b → ∀ H : ℝ, 0 < H → ∀ α : MultiIndex p.d,
          ∀ t ∈ Icc b (b + H),
            IsBoundedPairKernel p.s
              (max p.s 1 * Real.toNNReal (B * s104_b p.d α))
              (commutatorKernel p.d p.s (fun x => gradient
                (propagatorW (r26t3_coeff R) b t
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)) ∧
            IsBoundedPairKernel p.s
              (max p.s 1 * Real.toNNReal (B * s104_b p.d α))
              (commutatorKernel p.d p.s (fun x => gradient
                (fun x => s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                  (b + H) b t α x) x)) := by
  obtain ⟨δ0, hδ0, hδ0half, hOrbit⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Co, co, hco, hsum, hData⟩ := hOrbit δ hδ hδle R
  let B : ℝ := (p.d : ℝ) ^ ((2 * p.d + 8) + 1) * |Co|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro b hb H hH α t ht
  let T0 : ℝ := b + H
  have hT0 : 0 < T0 := by dsimp [T0]; linarith
  have hDataAt := hData T0 hT0
  have hbT0 : b ∈ Icc (0 : ℝ) T0 := by
    constructor
    · exact hb
    · dsimp [T0]
      linarith
  have htT0 : t ∈ Icc b T0 := by
    simpa [T0] using ht
  have hCoef : fp81s21_uniform_orbit_coefficient p Co α = B * s104_b p.d α := by
    unfold fp81s21_uniform_orbit_coefficient B HRS.MS.R2WinOrb.s103_b s104_b
    ring
  have hU : ContDiff ℝ 2
      (propagatorW (r26t3_coeff R) b t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) :=
    (hDataAt.smoothU α b hbT0 t htT0).of_le (by norm_cast; omega)
  have hD : ContDiff ℝ 2
      (fun x => s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) T0 b t α x) :=
    (hDataAt.smoothD α b hbT0 t htT0).of_le (by norm_cast; omega)
  have hUhess : ∀ x, ‖iteratedFDeriv ℝ 2
      (propagatorW (r26t3_coeff R) b t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ ≤ B * s104_b p.d α := by
    intro x
    have h := hDataAt.bddU α b hbT0 t htT0 2 (by omega) x
    simpa [hCoef] using h
  have hDhess : ∀ x, ‖iteratedFDeriv ℝ 2
      (fun x => s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) T0 b t α x) x‖ ≤
        B * s104_b p.d α := by
    intro x
    have h := hDataAt.bddD α b hbT0 t htT0 2 (by omega) x
    simpa [hCoef] using h
  have hAmp : 0 ≤ B * s104_b p.d α :=
    mul_nonneg hB (s104_b_nonneg α)
  constructor
  · exact fp81s21_comm_kernel_of_hessian_bound p.hs0 hAmp hU hUhess
  · simpa [T0] using
      fp81s21_comm_kernel_of_hessian_bound p.hs0 hAmp hD hDhess

#print axioms fp81s21_window_commutator_kernel_envelopes

end HRS.Fp81.S21

end
