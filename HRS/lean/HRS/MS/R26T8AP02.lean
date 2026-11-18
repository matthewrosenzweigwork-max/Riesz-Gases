import HRS.MS.R26T8AP00
import HRS.MS.Ker1Aux4
import HRS.Kernel.SymbolClass

/-!
# S8.2 local Newton layer, packet T8A.P02: Newton kernel derivative bounds away from zero
`newtonKernel d nu` is a constant multiple of `-log |z|` (d = 2) or `|z|^(2-d)` (d >= 3); the jets come from
the merged `ker1_norm_iteratedFDeriv_log_le` and `norm_iteratedFDeriv_rpow_norm_le`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_p02_const_mul {d : ℕ} {f : Euc d → ℝ} {z : Euc d} (c : ℝ) (hf : ContDiffAt ℝ ∞ f z) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun w => c * f w) z‖ = |c| * ‖iteratedFDeriv ℝ j f z‖ := by
  have h := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := c) (i := j)
    (hf.of_le (by exact_mod_cast le_top))
  simp only [smul_eq_mul] at h
  rw [h, norm_smul, Real.norm_eq_abs]

theorem r26t8a_p02_jet (d : ℕ) (hd : 2 ≤ d) (nu : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Euc d, z ≠ 0 →
      ‖iteratedFDeriv ℝ j (newtonKernel d nu) z‖ ≤
        C * ‖z‖ ^ (2 - (d : ℝ) - j) * (if d = 2 ∧ j = 0 then 1 + |Real.log ‖z‖| else 1) := by
  by_cases h2 : d = 2
  · subst h2
    set c : ℝ := (2 * nu * sphereArea 2)⁻¹ with hc
    have hfun : newtonKernel 2 nu = fun z : Euc 2 => c * (-Real.log ‖z‖) := by
      funext z; simp [newtonKernel, hc, div_eq_inv_mul]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · refine ⟨|c|, abs_nonneg _, fun z hz => ?_⟩
      rw [hfun, r26t8a_p02_const_mul c (HRS.MS.Ker1.ker1_contDiffAt_log_norm hz), norm_iteratedFDeriv_zero]
      simp only [Real.norm_eq_abs, abs_neg, true_and, if_true]
      norm_num
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    · obtain ⟨C, hC0, hC⟩ := HRS.MS.Ker1.ker1_norm_iteratedFDeriv_log_le (d := 2) (m := j) hj
      refine ⟨|c| * C, by positivity, fun z hz => ?_⟩
      rw [hfun, r26t8a_p02_const_mul c (HRS.MS.Ker1.ker1_contDiffAt_log_norm hz)]
      have h0 : ¬ (2 = 2 ∧ j = 0) := fun h => by omega
      rw [if_neg h0, mul_one]
      have := hC z hz
      calc |c| * ‖iteratedFDeriv ℝ j (fun x : Euc 2 => -Real.log ‖x‖) z‖ ≤ |c| * (C * ‖z‖ ^ (-(j : ℝ))) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = |c| * C * ‖z‖ ^ (2 - ((2 : ℕ) : ℝ) - j) := by
            rw [show (2 - ((2 : ℕ) : ℝ) - j) = -(j : ℝ) by push_cast; ring]; ring
  · have hd3 : (2 : ℝ) < d := by
      have : 3 ≤ d := by omega
      exact_mod_cast this
    set c : ℝ := (2 * nu * ((d : ℝ) - 2) * sphereArea d)⁻¹ with hc
    have hfun : newtonKernel d nu = fun z : Euc d => c * ‖z‖ ^ (2 - (d : ℝ)) := by
      funext z; simp [newtonKernel, h2, hc, div_eq_inv_mul]
    obtain ⟨C, hC0, hC⟩ := HRS.norm_iteratedFDeriv_rpow_norm_le (V := Euc d) (2 - (d : ℝ)) j
    refine ⟨|c| * C, by positivity, fun z hz => ?_⟩
    rw [hfun, r26t8a_p02_const_mul c (HRS.contDiffAt_rpow_norm _ hz)]
    have h0 : ¬ (d = 2 ∧ j = 0) := fun h => h2 h.1
    rw [if_neg h0, mul_one]
    calc |c| * ‖iteratedFDeriv ℝ j (fun x : Euc d => ‖x‖ ^ (2 - (d : ℝ))) z‖ ≤
          |c| * (C * ‖z‖ ^ (2 - (d : ℝ) - j)) := mul_le_mul_of_nonneg_left (hC z hz) (abs_nonneg _)
      _ = |c| * C * ‖z‖ ^ (2 - (d : ℝ) - j) := by ring

theorem r26t8a_newton_kernel_jets (d : ℕ) (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ContDiffOn ℝ ∞ (newtonKernel d nu) {z | z ≠ 0} ∧
      ∀ j : ℕ, j ≤ k → ∀ z : Euc d, z ≠ 0 →
        ‖iteratedFDeriv ℝ j (newtonKernel d nu) z‖ ≤
          C * ‖z‖^(2-(d:ℝ)-j) * (if d=2 ∧ j=0 then 1+|Real.log ‖z‖| else 1) := by
  choose Cj hCj0 hCj using fun j => r26t8a_p02_jet d hd nu j
  refine ⟨∑ j ∈ Finset.range (k + 1), Cj j, Finset.sum_nonneg fun j _ => hCj0 j, ?_, ?_⟩
  · by_cases h2 : d = 2
    · subst h2
      have hfun : newtonKernel 2 nu = fun z : Euc 2 =>
          (2 * nu * sphereArea 2)⁻¹ * (-Real.log ‖z‖) := by
        funext z; simp [newtonKernel, div_eq_inv_mul]
      rw [hfun]
      exact fun z hz => ((HRS.MS.Ker1.ker1_contDiffAt_log_norm hz).const_smul
        (2 * nu * sphereArea 2)⁻¹).contDiffWithinAt
    · have hfun : newtonKernel d nu = fun z : Euc d =>
          (2 * nu * ((d : ℝ) - 2) * sphereArea d)⁻¹ * ‖z‖ ^ (2 - (d : ℝ)) := by
        funext z; simp [newtonKernel, h2, div_eq_inv_mul]
      rw [hfun]
      exact fun z hz => ((HRS.contDiffAt_rpow_norm (V := Euc d) (2 - (d : ℝ)) hz).const_smul
        (2 * nu * ((d : ℝ) - 2) * sphereArea d)⁻¹).contDiffWithinAt
  · intro j hj z hz
    have h1 : Cj j ≤ ∑ j ∈ Finset.range (k + 1), Cj j :=
      Finset.single_le_sum (f := Cj) (fun j _ => hCj0 j) (Finset.mem_range.2 (by omega))
    refine (hCj j z hz).trans ?_
    have hfac : 0 ≤ ‖z‖ ^ (2 - (d : ℝ) - j) * (if d = 2 ∧ j = 0 then 1 + |Real.log ‖z‖| else 1) := by
      refine mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) ?_
      split_ifs
      · positivity
      · exact zero_le_one
    nlinarith
