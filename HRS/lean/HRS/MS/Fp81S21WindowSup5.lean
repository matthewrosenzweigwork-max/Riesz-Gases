import HRS.MS.Fp81S21WindowSup4
import HRS.MS.Fp81S21Uniform2

/-!
# HRS S2.1(iii), SOL40 packet 9d: zero-order orbit envelope adapter

`S101Data` defines `s101Dt` as the within-interval terminal-time derivative of
`propagatorW`. `S104nOrbit.diff01` identifies this derivative with
`propagatorW C v t (generatorW C t φ)`. This adapter extracts the zero-order
envelopes for the propagated test and its terminal derivative from the
compiled `fp81s21_uniform_orbit_amplitudes` claim; the oscillator factor is
exactly `s104_b` and is not inserted again into the coordinate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS.MS.R26T3 HRS.Whole HRS.MS.CovMeas HRS.MS.R2WinErr HRS.MS.R2WinOrb

/-- Uniform zero-order bounds for `U^{b,t} φ_α` and its terminal derivative on
the shifted observation window. The amplitude constant is chosen before the
window start, mode, spatial point, and terminal time. -/
theorem fp81s21_window_zero_order_orbit_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ b : ℝ, 0 ≤ b → ∀ α : MultiIndex p.d,
          ∀ t ∈ Set.Icc b (b + p.T), ∀ x,
            |propagatorW (r26t3_coeff R) b t
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x| ≤
                B * s104_b p.d α ∧
            |s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                (b + p.T) b t α x| ≤ B * s104_b p.d α := by
  obtain ⟨δ0, hδ0, hδ0half, hOrbit⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Co, _, _, _, hData⟩ := hOrbit δ hδ hδle R
  let B : ℝ := (p.d : ℝ) ^ ((2 * p.d + 8) + 1) * |Co|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro b hb α t ht x
  let H : ℝ := b + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, hb]
  have hDataAt := hData H hH
  have hbH : b ∈ Icc (0 : ℝ) H := by
    constructor
    · exact hb
    · dsimp [H]
      linarith [p.hT]
  have htH : t ∈ Icc b H := by
    simpa [H] using ht
  have hU := hDataAt.bddU α b hbH t htH 0 (by omega) x
  have hD := hDataAt.bddD α b hbH t htH 0 (by omega) x
  have hU' : |propagatorW (r26t3_coeff R) b t
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x| ≤
        fp81s21_uniform_orbit_coefficient p Co α := by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hU
  have hD' : |s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H b t α x| ≤ fp81s21_uniform_orbit_coefficient p Co α := by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hD
  have hcoef : fp81s21_uniform_orbit_coefficient p Co α = B * s104_b p.d α := by
    unfold fp81s21_uniform_orbit_coefficient B HRS.MS.R2WinOrb.s103_b s104_b
    ring
  constructor
  · simpa [H, hcoef] using hU'
  · simpa [H, hcoef] using hD'

#print axioms fp81s21_window_zero_order_orbit_bound

end HRS.Fp81.S21

end
