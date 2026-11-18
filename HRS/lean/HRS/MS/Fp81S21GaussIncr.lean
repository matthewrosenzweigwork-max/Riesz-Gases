import HRS.MS.Fp81S21Uniform2
import HRS.MS.Fp81S21WindowFeature5

/-!
# HRS S2.1(iii), SOL71: scalar all-horizon terminal derivative envelope

This file exports the zero-order derivative estimate in a form uniform over
every shifted finite physical interval.  It also records the identity between
the S101 derivative and propagation of the generator terminal input.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas HRS.MS.R26T3 HRS.MS.R2WinErr

/-- The S101 terminal derivative has a modewise envelope on every shifted
finite interval.  The equality identifies it with the propagated generator
input, so the bound is uniform in both the interval start and its length. -/
theorem fp81s21_gauss_incr_scalar_terminal_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ H : ℝ, 0 < H → ∀ b : ℝ, 0 ≤ b →
            ∀ α : MultiIndex p.d, ∀ t ∈ Icc b (b + H), ∀ x : Euc p.d,
              |s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                  (b + H) b t α x| ≤ B * s104_b p.d α ∧
              s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                  (b + H) b t α x =
                propagatorW (r26t3_coeff R) b t
                  (generatorW (r26t3_coeff R) t
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := by
  obtain ⟨δu, hδu, hδuhalf, huniform⟩ :=
    fp81s21_uniform_orbit_amplitudes p
  obtain ⟨δc, Co, co, hδc, hδchalf, hco, hcommon⟩ :=
    fp81s21_common_radius p
  let δ0 : ℝ := min δu δc
  have hδ0 : 0 < δ0 := lt_min hδu hδc
  have hδ0half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδuhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨CoR, coR, hcoR, hsumR, hdata⟩ :=
    huniform δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨hclaims, -, hterm, -⟩ :=
    hcommon δ hδ (hδle.trans (min_le_right _ _)) R.ρβ R.thermal
  let B : ℝ := (p.d : ℝ) ^ ((2 * p.d + 8) + 1) * |CoR|
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hcoef : ∀ α : MultiIndex p.d,
      fp81s21_uniform_orbit_coefficient p CoR α = B * s104_b p.d α := by
    intro α
    simp [fp81s21_uniform_orbit_coefficient, B,
      HRS.MS.R2WinOrb.s103_b, HRS.MS.R2WinErr.s104_b]
    ring
  refine ⟨B, hB, ?_⟩
  intro H hH b hb α t ht x
  have htotal : 0 < b + H := by linarith
  have hbtotal : b ∈ Icc (0 : ℝ) (b + H) := by
    constructor
    · exact hb
    · linarith
  have hdataH := hdata (b + H) htotal
  have hderBound := hdataH.bddD α b hbtotal t ht 0 (by omega) x
  have hbound : |s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (b + H) b t α x| ≤ B * s104_b p.d α := by
    calc
      |s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (b + H) b t α x|
        ≤ fp81s21_uniform_orbit_coefficient p CoR α := by
          simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hderBound
      _ = B * s104_b p.d α := hcoef α
  have hend : b < b + H := by linarith
  have hid := fp81s21_window_s101Dt_eq_generator p R hH hb hbtotal hend hterm
  exact ⟨hbound, hid t ht α x⟩

#print axioms fp81s21_gauss_incr_scalar_terminal_bound

end HRS.Fp81.S21

end
