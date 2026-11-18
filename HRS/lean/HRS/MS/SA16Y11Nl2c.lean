import HRS.MS.SA16Y11Nl1c
import HRS.MS.SA16Y11Nl2

/-!
# S.A.16 (SA16Y11) Nl2c: critical copy of `Nl2` (`s = d-1`)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Nl2c
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 3200000 in
theorem sa16y11c_NInt_diff (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs1 : s = (d : ℝ) - 1) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) →
      ∀ (t : ℝ), 0 < t → ∀ μ1 μ2 : ℝ → Euc d → ℝ,
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ1 r)) →
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ2 r)) →
      ∀ δ : ℝ, 0 ≤ δ → (∀ r ∈ Icc (0 : ℝ) t, sa16y5_Dec (m + 2) δ (fun y => μ1 r y - μ2 r y)) →
      ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t, ∀ y : WmpSpace d (m + 1 + 1) p,
        ‖sa16r_iota d m p ((sa16y5_NInt d m N p s M t μ1 σ - sa16y5_NInt d m N p s M t μ2 σ) y)‖ ≤ C * δ * ‖y‖ := by
  obtain ⟨Wd, hWd0, hdens⟩ := sa16y5_density_data hd m Λ
  obtain ⟨C0, hC0, hG⟩ := sa16y11c_Gop_diff d m hd s p MB hs0 hs1 hfar Wd hWd0
  set cm : ℝ := (d : ℝ) ^ (m + 2) * 2 ^ (d + 3) with hcm
  have hcm0 : 0 < cm := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    rw [hcm]; positivity
  refine ⟨C0 * cm, by positivity, fun M hM t ht μ1 μ2 h1 h2 δ hδ hDd N hN σ hσ y => ?_⟩
  have hnode := fun i (hi : i ∈ Finset.range (N + 1)) => sa16y4_node_mem hN ht hi
  have hterm : ∀ i ∈ Finset.range (N + 1),
      ‖sa16r_iota d m p ((sa16y5_Gop d m p s M (sa16q_mol N (μ1 (t - (i : ℝ) * t / N))) -
        sa16y5_Gop d m p s M (sa16q_mol N (μ2 (t - (i : ℝ) * t / N)))) y)‖ ≤ C0 * (cm * δ) * ‖y‖ := by
    intro i hi
    set r := t - (i : ℝ) * t / N with hr
    have hrm : r ∈ Icc (0 : ℝ) t := hnode i hi
    obtain ⟨-, hS1⟩ := hdens (μ1 r) (h1 r hrm)
    obtain ⟨-, hS2⟩ := hdens (μ2 r) (h2 r hrm)
    obtain ⟨hSB1, hDec1, -⟩ := hS1 N
    obtain ⟨hSB2, hDec2, -⟩ := hS2 N
    have hc1 : Continuous (μ1 r) := (h1 r hrm).1.continuous
    have hc2 : Continuous (μ2 r) := (h2 r hrm).1.continuous
    have hdiff : ContDiff ℝ (m + 2 : ℕ) (fun y => μ1 r y - μ2 r y) :=
      ((h1 r hrm).1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3))).sub
        ((h2 r hrm).1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3)))
    have hmD := sa16y11_mol_Dec N hd hdiff (hDd r hrm)
    rw [← sa16y11_mol_sub N hc1 hc2] at hmD
    have := hG M hM _ _ hSB1 hSB2 hDec1 hDec2 _ (by positivity) hmD y
    refine this.trans (le_of_eq ?_)
    rw [hcm]; ring
  have hy : (sa16y5_NInt d m N p s M t μ1 σ - sa16y5_NInt d m N p s M t μ2 σ) y =
      ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ •
        ((sa16y5_Gop d m p s M (sa16q_mol N (μ1 (t - (i : ℝ) * t / N))) -
          sa16y5_Gop d m p s M (sa16q_mol N (μ2 (t - (i : ℝ) * t / N)))) y) := by
    unfold sa16y5_NInt
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_sub, Finset.sum_sub_distrib]
  rw [hy, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have hsum := sa16y4_hat_sum hN ht hσ
  calc ∑ i ∈ Finset.range (N + 1), ‖sa16r_iota d m p (sa16y4_hat N t i σ •
        ((sa16y5_Gop d m p s M (sa16q_mol N (μ1 (t - (i : ℝ) * t / N))) -
          sa16y5_Gop d m p s M (sa16q_mol N (μ2 (t - (i : ℝ) * t / N)))) y))‖
      ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * (C0 * (cm * δ) * ‖y‖) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sa16y4_hat_nonneg N t i σ)]
        exact mul_le_mul_of_nonneg_left (hterm i hi) (sa16y4_hat_nonneg N t i σ)
    _ = C0 * cm * δ * ‖y‖ := by
        rw [← Finset.sum_mul, hsum]; ring

end Nl2c

end HRS.Whole.AppendixA.Phase2SA16R

end
