import HRS.MS.Fp81S21WindowSup5

/-!
# HRS S2.1(iii), SOL40 packet 9d: all-horizon zero-order orbit envelope

The coefficient from `fp81s21_uniform_orbit_amplitudes` is independent of the
horizon. This adapter records the zero-order envelopes on every finite shifted
window `[b,b+H]`, including the terminal-time derivative `s101Dt`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS.MS.R26T3 HRS.Whole HRS.MS.CovMeas HRS.MS.R2WinErr HRS.MS.R2WinOrb

/-- A single zero-order amplitude bounds both the adjoint orbit and its
terminal-time derivative on every finite shifted window. The amplitude is
chosen before the window length and start, mode, spatial point, and terminal
time. -/
theorem fp81s21_window_zero_order_orbit_bound_all_horizons (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ H : ℝ, 0 < H → ∀ b : ℝ, 0 ≤ b →
          ∀ α : MultiIndex p.d, ∀ t ∈ Set.Icc b (b + H), ∀ x,
            |propagatorW (r26t3_coeff R) b t
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x| ≤
                B * s104_b p.d α ∧
            |s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                (b + H) b t α x| ≤ B * s104_b p.d α := by
  obtain ⟨δ0, hδ0, hδ0half, hOrbit⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Co, _, _, _, hData⟩ := hOrbit δ hδ hδle R
  let B : ℝ := (p.d : ℝ) ^ ((2 * p.d + 8) + 1) * |Co|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro H hH b hb α t ht x
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
  have hU := hDataAt.bddU α b hbT0 t htT0 0 (by omega) x
  have hD := hDataAt.bddD α b hbT0 t htT0 0 (by omega) x
  have hU' : |propagatorW (r26t3_coeff R) b t
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x| ≤
        fp81s21_uniform_orbit_coefficient p Co α := by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hU
  have hD' : |s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      T0 b t α x| ≤ fp81s21_uniform_orbit_coefficient p Co α := by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hD
  have hcoef : fp81s21_uniform_orbit_coefficient p Co α = B * s104_b p.d α := by
    unfold fp81s21_uniform_orbit_coefficient B HRS.MS.R2WinOrb.s103_b s104_b
    ring
  constructor
  · simpa [T0, hcoef] using hU'
  · simpa [T0, hcoef] using hD'

#print axioms fp81s21_window_zero_order_orbit_bound_all_horizons

end HRS.Fp81.S21

end
