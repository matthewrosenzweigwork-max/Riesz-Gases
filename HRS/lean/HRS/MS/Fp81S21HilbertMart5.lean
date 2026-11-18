import HRS.MS.Fp81S21HilbertMart4

/-!
# HRS S2.1(iii), B6-i: package the strengthened constructor in the contract

The constructor's single all-horizon process immediately supplies the original
horizon-indexed bracket contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.MS.R26T3 HRS.MS.R26T6

/-- The all-horizon Hilbert-Itô construction satisfies the original B6-i
martingale/bracket contract. -/
theorem fp81s21_b6i_hilbertMartingaleIto_satisfies_contract
    (p : Parameters)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    fp81s21_b6iHilbertMartingaleBracketContract p E := by
  obtain ⟨δstar, hδstar, hδhalf, hrest⟩ :=
    fp81s21_b6i_hilbertMartingaleIto p E
  refine ⟨δstar, hδstar, hδhalf, ?_⟩
  intro δ hδ hδle R N hN A Fp H hH
  obtain ⟨Cweight, hCweight, hrest⟩ := hrest δ hδ hδle R
  obtain ⟨m, hm, hZ, hIto, hHM, hzero, hformula, hcoord⟩ :=
    hrest N hN A Fp
  refine ⟨m, fp81s21_b6i_gradientNoise p E A Fp, hm, hHM H, hzero, ?_⟩
  intro u ω i k
  exact hformula u ω i k

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_b6i_hilbertMartingaleIto_satisfies_contract
