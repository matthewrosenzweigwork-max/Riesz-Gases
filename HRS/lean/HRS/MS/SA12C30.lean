import HRS.MS.SA12C29

/-!
# S.A.12(c), packet E7.05 (part 2): exact averaging of the cell functionals over the centres

`∫_{c ∈ Q_L} jetPair/jetSq/dissipSq (χ(· - (c+p))) = (∫ χ²) · box functional`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12c_chi_support {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) (u : Euc d) (hu : 2 ≤ ‖u‖) : χ u = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := hχ.1.2.2.1 hmem
  rw [Metric.mem_ball, dist_zero_right] at this
  linarith

/-- `∫_{c ∈ Q} ∫ χ(x-(c+p))² h(x) dx dc = (∫ χ²) ∫_Q h` for continuous periodic `h`. -/
theorem sa12c_avg_shift {L : ℝ} (hL : 0 < L) {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) {h : Euc d → ℝ}
    (hh : Continuous h) (hp : ∀ (x : Euc d) (k : Fin d → ℤ), h (x + L • latticePt k) = h x) (p : Euc d) :
    ∫ c in periodBox d L, ∫ x, χ (x - (c + p)) ^ 2 * h x = (∫ v, χ v ^ 2) * ∫ x in periodBox d L, h x := by
  set Φ : Euc d → ℝ := fun c => ∫ x, χ (x - c) ^ 2 * h x with hΦ
  have hΦp : ∀ (c : Euc d) (k : Fin d → ℤ), Φ (c + L • latticePt k) = Φ c := by
    intro c k
    simp only [hΦ]
    rw [← integral_add_right_eq_self (fun x => χ (x - (c + L • latticePt k)) ^ 2 * h x) (L • latticePt k)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [hp x k, show x + L • latticePt k - (c + L • latticePt k) = x - c by abel]
  have hsh := sa12k_box_shift L hL hΦp (-p)
  simp only [sub_neg_eq_add] at hsh
  have hmain : ∫ c in periodBox d L, Φ c = (∫ v, χ v ^ 2) * ∫ x in periodBox d L, h x := by
    have := sa12c_avg_scalar (d := d) hL (w := fun v => χ v ^ 2) (h := h) (hχ.1.1.continuous.pow 2) hh hp
      (R := 2) (fun v hv => by simp [sa12c_chi_support hχ v hv.le])
    exact this
  show ∫ c in periodBox d L, Φ (c + p) = _
  rw [hsh]
  exact hmain

end HRS.MH.AdjointRd.Phase2SA12C
