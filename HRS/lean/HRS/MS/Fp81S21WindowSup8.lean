import HRS.MS.Fp81S21WindowSup7

/-!
# HRS S2.1(iii), SOL40 packet 9d: shifted-window orbit FTC

The compiled definitions used here are `s101Dt C m T τ t α x :=
derivWithin (fun t' => propagatorW C τ t' (oscTestFun m α) x) (Icc τ T) t`
and `s101Th C m T τ s α x := if τ < s ∧ s ≤ T then s101Dt ... else 0`.
The `S101Data` adapter `s101_ftc` states the orbit increment equals the
interval integral of this endpoint-cutoff derivative. This theorem merely
places that exact compiled identity in the shifted-window namespace and
records its full interval hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open HRS.Whole HRS.MS.CovMeas HRS.MS.Go

namespace HRS.Fp81.S21

/-- Pointwise terminal-time FTC for an adjoint orbit on a shifted window.
The integral uses `s101Th`, the compiled derivative with its endpoint cutoff.
-/
theorem fp81s21_window_orbit_ftc
    {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} (hD : S101Data C m T r c)
    {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc b T)
    (α : MultiIndex d) (x : Euc d) :
    propagatorW C b t (oscTestFun m α) x =
      propagatorW C b b (oscTestFun m α) x +
        ∫ s in b..t, s101Th C m T b s α x := by
  have h := HRS.MS.CovMeas.s101_ftc hD hb ht α x
  linarith

#print axioms fp81s21_window_orbit_ftc

end HRS.Fp81.S21

end
