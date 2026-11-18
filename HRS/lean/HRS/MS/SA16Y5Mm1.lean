import HRS.MS.SA16Y5Ip1
import HRS.MS.SA16Y3Dy1

/-!
# S.A.16 (SA16Y5) Mm1: the jets of `P_μ φ` lie in `L^p` (order-one range)

`sa16y5_pd_P_memLp`: `∂^idx (P_μ φ) ∈ L^p` for `φ ∈ C_c^∞`, `μ` smooth with `Dec (j+1) W` (from `∂^idx P_μ φ = Rem + C1 + P_μ ∂^idxφ`);
`sa16y5_S_memLp`: `sa16j_S d m (P_μ φ) ∈ L^p` (so that `P_μ φ ∈ sa16r_S d m p` and `sa16r_J_coe` applies).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Mm1
variable {d : ℕ} {s : ℝ}

theorem sa16y5_pd_P_memLp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s < (d : ℝ) - 1) {p : ℝ} (hp : 2 ≤ p)
    (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ)
    (hφ : IsCcInfty φ) {j : ℕ} (hdec : sa16y5_Dec (j + 1) W μ) (idx : Fin j → Fin d) :
    MemLp (partialDeriv idx (sa16z_P s μ φ)) (ENNReal.ofReal p) volume := by
  haveI : Fact (2 ≤ p) := ⟨hp⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  obtain ⟨C1, hC1, hRem⟩ := sa16y5_Rem_bound hd hs0 hsd hs1 hp hfar hW
  obtain ⟨CC, hCC0, hCC⟩ := sa16y5_C1_bound hd hs0 hs1 hp hfar hW
  obtain ⟨KP, hKP0, hKP⟩ := sa16y5_P_jet hd hs0 hs1 hp hfar hW
  obtain ⟨KR, hKR0, hKR⟩ := hRem j
  have hPs : ContDiff ℝ ∞ (sa16z_P s μ φ) := sa16z_P_smooth hs0 hsd hμ hφ
  have hSj : sa16z_S p φ j < ⊤ := sa16y3_S_lt_top hφ j
  have hSj1 : sa16z_S p φ (j + 1) < ⊤ := sa16y3_S_lt_top hφ (j + 1)
  have e1 : eLpNorm (fun x => sa16z_Rem s μ φ j idx x) (ENNReal.ofReal p) volume < ⊤ :=
    lt_of_le_of_lt (hKR hμ hφ hdec idx) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSj)
  have e2 : eLpNorm (fun x => sa16z_C1 s μ φ j idx x) (ENNReal.ofReal p) volume < ⊤ := by
    cases j with
    | zero =>
      have : (fun x => sa16z_C1 s μ φ 0 idx x) = 0 := rfl
      rw [this, eLpNorm_zero]; exact ENNReal.zero_lt_top
    | succ n =>
      exact lt_of_le_of_lt (hCC hμ hφ (sa16y5_Dec_mono (by omega) hdec) n idx)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSj)
  have e3 : eLpNorm (sa16z_P s μ (partialDeriv idx φ)) (ENNReal.ofReal p) volume < ⊤ :=
    lt_of_le_of_lt (hKP hμ (sa16y5_Dec_mono (by omega) hdec) hφ idx)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSj1)
  have hfun : partialDeriv idx (sa16z_P s μ φ) = (fun x => sa16z_Rem s μ φ j idx x) +
      (fun x => sa16z_C1 s μ φ j idx x) + sa16z_P s μ (partialDeriv idx φ) := by
    funext x
    simp only [Pi.add_apply, sa16z_Rem]
    ring
  have hlt : eLpNorm (partialDeriv idx (sa16z_P s μ φ)) (ENNReal.ofReal p) volume < ⊤ := by
    rw [hfun]
    refine lt_of_le_of_lt (eLpNorm_add_le hp1) (ENNReal.add_lt_top.2 ⟨?_, e3⟩)
    exact lt_of_le_of_lt (eLpNorm_add_le hp1) (ENNReal.add_lt_top.2 ⟨e1, e2⟩)
  exact hlt

theorem sa16y5_S_memLp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s < (d : ℝ) - 1) {p : ℝ} (hp : 2 ≤ p)
    (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ)
    (hφ : IsCcInfty φ) (m : ℕ) (hdec : sa16y5_Dec (m + 1) W μ) :
    MemLp (sa16j_S d m (sa16z_P s μ φ)) (ENNReal.ofReal p) volume := by
  have hPs : ContDiff ℝ ∞ (sa16z_P s μ φ) := sa16z_P_smooth hs0 hsd hμ hφ
  have hg : MemLp (fun x => ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
      ‖partialDeriv idx (sa16z_P s μ φ) x‖) (ENNReal.ofReal p) volume := by
    refine memLp_finsetSum _ fun j hj => memLp_finsetSum _ fun idx _ => ?_
    exact (sa16y5_pd_P_memLp hd hs0 hsd hs1 hp hfar hW hμ hφ
      (sa16y5_Dec_mono (by have := Finset.mem_range.1 hj; omega) hdec) idx).norm
  refine hg.mono' (sa16j_S_cont hPs m).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d m _ x)]
  simpa [Real.norm_eq_abs] using sa16j_S_le m (sa16z_P s μ φ) x

end Mm1

end HRS.Whole.AppendixA.Phase2SA16R
