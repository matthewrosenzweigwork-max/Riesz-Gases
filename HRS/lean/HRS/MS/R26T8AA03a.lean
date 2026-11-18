import HRS.MS.R26T8AA02

/-!
# S8.2 T8A A03 (part a): a `PairCorrector` has `A ≥ 0` and is conormal with a nonnegative weight exponent
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a03_A_nonneg (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) : 0 ≤ A := by
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Euc d)
  have h := hQ.value x y hxy
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hr : 0 ≤ smallRadius x y ^ (2 - criticalS d) :=
    Real.rpow_nonneg (le_min zero_le_one hn.le) _
  have hl : 0 ≤ (if d = 4 then |Real.log (smallRadius x y)| else 0) := by split_ifs <;> positivity
  have hpw : 0 < HRS.MS.Phase2S82.pairWeight M x y :=
    mul_pos (Real.rpow_pos_of_pos (s83_jb_pos x) _) (Real.rpow_pos_of_pos (s83_jb_pos y) _)
  have hb : 0 < 1 + smallRadius x y ^ (2 - criticalS d) + (if d = 4 then |Real.log (smallRadius x y)| else 0) := by
    linarith
  by_contra hA
  push Not at hA
  have : A * HRS.MS.Phase2S82.pairWeight M x y *
      (1 + smallRadius x y ^ (2 - criticalS d) + (if d = 4 then |Real.log (smallRadius x y)| else 0)) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hA hpw) hb
  linarith [abs_nonneg (Q x y)]

theorem r26t8a_a03_conormal_pos (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) :
    Conormal (4 + 2) 1 (max M 0) (criticalS d - 2) A Q :=
  r26t8a_f23_conormal_M_mono (le_max_left _ _) (r26t8a_a03_A_nonneg hd hQ) hQ.tangential

end HRS.MS.R26T8A
