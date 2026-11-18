import HRS.MS.S21H2_S02
import HRS.MS.S21E_Kappa0
import HRS.MS.R2SeAux42

/-!
# S21H2, packet R26-T3.S09: initial response feature and cubic tensor are Bochner objects

`r26t3_ell R q x = ℓ²-vector (a_j(x))_j` with `a_j = r26t3_a R (q j)`. The coordinate bound
`|a_j x| ≤ C ‖q_j‖_{C_b^J}` (from `r26t3_response_smooth`) and the summability of `‖q_j‖` give a
uniform Weierstrass bound on the `ℓ²`-valued series `∑_j a_j(x) e_j`, hence continuity, a uniform
norm bound, and (probability reference) integrability of the cube; the merged Bochner membership
`s21e_kappa0_mem` then applies. Helper names carry the prefix `s21h2_s09_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS HRS.Whole

theorem s21h2_s09_cbNorm_nonneg {d k : ℕ} (Φ : Euc d → ℝ) : 0 ≤ cbNorm k Φ := by
  unfold cbNorm
  exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _

theorem s21h2_s09_abs_le {d k : ℕ} {Φ : Euc d → ℝ} (h : MemCb k Φ) (x : Euc d) :
    |Φ x| ≤ cbNorm k Φ := by
  have hb : BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ 0 Φ z‖) := h.2 0 (Nat.zero_le k)
  have h0 : ‖iteratedFDeriv ℝ 0 Φ x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ 0 Φ z‖ := le_ciSup hb x
  have hsum : (⨆ z, ‖iteratedFDeriv ℝ 0 Φ z‖) ≤ cbNorm k Φ := by
    unfold cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖)
      (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.succ_pos k))
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
  linarith

theorem s21h2_s09_prob {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (R : Trajectory p δ) : IsProbabilityMeasure (r26t3_mu R 0) := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  exact hP

theorem s21h2_s09_ofSeq_eq {c : ℕ → ℝ} (h : Memℓp c 2) :
    (SeqL2.ofSeq c : lp (fun _ : ℕ => ℝ) 2) = ⟨c, h⟩ := by
  unfold SeqL2.ofSeq
  exact dif_pos h

theorem r26t3_static_tensor {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) (q : ℕ → Euc p.d → ℝ)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) q) :
    Continuous (r26t3_ell R q) ∧ (∃ C : ℝ, ∀ x, ‖r26t3_ell R q x‖ ≤ C) ∧
      Integrable (fun x => ‖r26t3_ell R q x‖^3) (r26t3_mu R 0) ∧
      HRS.MS.S21E.s21eKappa0 (r26t3_mu R 0) (r26t3_ell R q) ∈ projTensor SeqL2 3 := by
  haveI := s21h2_s09_prob hδ hδh R
  obtain ⟨C, hC0, hR⟩ := r26t3_response_smooth hδ hδh R hγ
  -- coordinatewise bounds and smoothness
  have hbd : ∀ j x, |r26t3_a R (q j) x| ≤ C * cbNorm (r26t3_J p.d) (q j) := fun j x =>
    (s21h2_s09_abs_le (hR (q j) (hq.1 j)).1 x).trans (hR (q j) (hq.1 j)).2.1
  have hcont_j : ∀ j, Continuous (r26t3_a R (q j)) := fun j =>
    (hR (q j) (hq.1 j)).1.1.continuous
  have hu : Summable fun j => C * cbNorm (r26t3_J p.d) (q j) := hq.2.mul_left C
  have hnn : ∀ j, 0 ≤ C * cbNorm (r26t3_J p.d) (q j) := fun j =>
    mul_nonneg hC0 (s21h2_s09_cbNorm_nonneg _)
  have hle : ∀ j, C * cbNorm (r26t3_J p.d) (q j) ≤
      ∑' k, C * cbNorm (r26t3_J p.d) (q k) := fun j =>
    hu.le_tsum j (fun k _ => hnn k)
  -- the coefficient vector lies in ℓ²
  have hmem : ∀ x, Memℓp (fun j => r26t3_a R (q j) x) 2 := by
    intro x
    refine memℓp_gen ?_
    have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    simp only [e2]
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      (hu.mul_left (∑' k, C * cbNorm (r26t3_J p.d) (q k)))
    rw [Real.rpow_two, Real.norm_eq_abs]
    have h0 := hbd j x
    have hnj := hnn j
    calc |r26t3_a R (q j) x| ^ 2 = |r26t3_a R (q j) x| * |r26t3_a R (q j) x| := sq _
      _ ≤ (C * cbNorm (r26t3_J p.d) (q j)) * (C * cbNorm (r26t3_J p.d) (q j)) :=
          mul_le_mul h0 h0 (abs_nonneg _) hnj
      _ ≤ (∑' k, C * cbNorm (r26t3_J p.d) (q k)) * (C * cbNorm (r26t3_J p.d) (q j)) :=
          mul_le_mul_of_nonneg_right (hle j) hnj
  -- the ℓ²-valued series representation
  have hell : ∀ x, r26t3_ell R q x =
      ∑' j, (lp.single 2 j (r26t3_a R (q j) x) : lp (fun _ : ℕ => ℝ) 2) := by
    intro x
    have hm := hmem x
    have hs := lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by norm_num)
      (⟨fun j => r26t3_a R (q j) x, hm⟩ : lp (fun _ : ℕ => ℝ) 2)
    exact (s21h2_s09_ofSeq_eq hm).trans hs.tsum_eq.symm
  have hcont : Continuous fun x =>
      ∑' j, (lp.single 2 j (r26t3_a R (q j) x) : lp (fun _ : ℕ => ℝ) 2) := by
    refine continuous_tsum (fun j => ?_) hu (fun j x => ?_)
    · exact ((lp.isometry_single (E := fun _ : ℕ => ℝ) (p := 2) j).continuous).comp (hcont_j j)
    · rw [lp.norm_single (by norm_num)]
      exact (Real.norm_eq_abs _).le.trans (hbd j x)
  have hell_cont : Continuous (r26t3_ell R q) := by
    have e : r26t3_ell R q = fun x =>
        ∑' j, (lp.single 2 j (r26t3_a R (q j) x) : lp (fun _ : ℕ => ℝ) 2) :=
      funext hell
    rw [e]
    exact hcont
  -- uniform bound
  have hsn : ∀ x, Summable fun j => ‖(lp.single 2 j (r26t3_a R (q j) x) : lp (fun _ : ℕ => ℝ) 2)‖ := by
    intro x
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hu
    rw [lp.norm_single (by norm_num)]
    exact (Real.norm_eq_abs _).le.trans (hbd j x)
  have hbound : ∀ x, ‖r26t3_ell R q x‖ ≤ ∑' j, C * cbNorm (r26t3_J p.d) (q j) := by
    intro x
    rw [hell x]
    refine (norm_tsum_le_tsum_norm (hsn x)).trans ?_
    refine Summable.tsum_le_tsum (fun j => ?_) (hsn x) hu
    rw [lp.norm_single (by norm_num)]
    exact (Real.norm_eq_abs _).le.trans (hbd j x)
  -- integrability of the cube under the probability reference
  have hmeas : AEStronglyMeasurable (fun x => ‖r26t3_ell R q x‖^3) (r26t3_mu R 0) :=
    ((hell_cont.norm).pow 3).aestronglyMeasurable
  have hint : Integrable (fun x => ‖r26t3_ell R q x‖^3) (r26t3_mu R 0) := by
    refine Integrable.of_bound hmeas ((∑' j, C * cbNorm (r26t3_J p.d) (q j))^3)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound x) 3
  have hsm : AEStronglyMeasurable (r26t3_ell R q) (r26t3_mu R 0) :=
    hell_cont.aestronglyMeasurable
  have hi' : Integrable (fun x => ‖r26t3_ell R q x‖ * ‖r26t3_ell R q x‖ * ‖r26t3_ell R q x‖)
      (r26t3_mu R 0) :=
    hint.congr (Eventually.of_forall fun x => by simp only [pow_three, mul_assoc])
  exact ⟨hell_cont, ⟨_, hbound⟩, hint, HRS.MS.S21E.s21e_kappa0_mem (μ := r26t3_mu R 0) hsm hi'⟩

end HRS.MS.R26T3
