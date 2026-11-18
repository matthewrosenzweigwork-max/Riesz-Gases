import HRS.MS.SA12Z3NearN5B

/-!
# S.A.12 N5 (SA12Z3), part C: direction bound and the algebra of the symbols
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution Matrix

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MS.UniqN3a HRS.MS.UniqN3c
  HRS.PDE.ToolboxRd

variable {d : ℕ}

/-- For one direction `q`: the weighted symmetrization error is bounded by `C ‖a‖_{C²_b} ‖u‖²`. -/
theorem sa12z3_dir_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d)
    {c : ℝ} (hc : 0 < c) (q : Euc d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a u : Euc d → ℝ), MemCb 2 a → (∀ x, 0 ≤ a x) → MemCb 2 u →
      HasCompactSupport u →
      |symbolForm (mq c s q) (fun x => a x * u x) u -
        symbolForm (mq c s q) (fun x => Real.sqrt (a x) * u x) (fun x => Real.sqrt (a x) * u x)| ≤
        C * cbNorm 2 a * ∫ x, u x ^ 2 := by
  have hθ0 : 0 < s + 2 - d := by linarith
  have hθ2 : s + 2 - d < 2 := by linarith
  have hm : IsHomogSymbol (s + 2 - d) (mq c s q) := n3c_mq_homog hd hs0 hs1 hsd hc q
  obtain ⟨k, hk⟩ := quadratic_toolbox_kernel hd _ hθ0 hθ2 _ hm
  obtain ⟨C, hC⟩ := quadratic_toolbox_weighted hd _ hθ0 hθ2 _ hm k hk
  refine ⟨2 * max C 0, by positivity, fun a u ha h0 hu huc => ?_⟩
  obtain ⟨⟨Lw, hLw⟩, hH1⟩ := sa12z3_u_facts hu huc
  obtain ⟨_, _, hE⟩ := hC (cbNorm 2 a) (cbNorm 2 a) (Real.sqrt (cbNorm 2 a)) Lw a u h0
    (sa12z3_a_c11 ha) (sa12z3_a_lip ha) (sa12z3_sqrt_lip ha h0) hLw hH1
  have hcb0 := sa12z3_cb_nonneg ha
  have hLm : (Real.sqrt (cbNorm 2 a)) ^ 2 = cbNorm 2 a := Real.sq_sqrt hcb0
  have hsup : (⨆ x, |Real.sqrt (a x)|) ^ 2 ≤ cbNorm 2 a := by
    have h1 : (⨆ x, |Real.sqrt (a x)|) ≤ Real.sqrt (cbNorm 2 a) := by
      refine ciSup_le fun x => ?_
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (le_trans (le_abs_self _) (sa12z3_cb2_bounds ha x).1)
    have h2 : 0 ≤ ⨆ x, |Real.sqrt (a x)| := Real.iSup_nonneg fun x => abs_nonneg _
    calc _ ≤ (Real.sqrt (cbNorm 2 a)) ^ 2 := pow_le_pow_left₀ h2 h1 2
      _ = cbNorm 2 a := hLm
  have hI0 : 0 ≤ ∫ x, u x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hX0 : 0 ≤ (Real.sqrt (cbNorm 2 a)) ^ 2 + (⨆ x, |Real.sqrt (a x)|) ^ 2 := by positivity
  have hX : (Real.sqrt (cbNorm 2 a)) ^ 2 + (⨆ x, |Real.sqrt (a x)|) ^ 2 ≤ cbNorm 2 a + cbNorm 2 a := by
    rw [hLm]; linarith
  have hE' : |symbolForm (mq c s q) (fun x => a x * u x) u -
        symbolForm (mq c s q) (fun x => Real.sqrt (a x) * u x) (fun x => Real.sqrt (a x) * u x)| ≤
      C * ((Real.sqrt (cbNorm 2 a)) ^ 2 + (⨆ x, |Real.sqrt (a x)|) ^ 2) * ∫ x, u x ^ 2 := hE
  refine hE'.trans ?_
  have h1 : C * ((Real.sqrt (cbNorm 2 a)) ^ 2 + (⨆ x, |Real.sqrt (a x)|) ^ 2) ≤
      max C 0 * (cbNorm 2 a + cbNorm 2 a) :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hX0).trans
      (mul_le_mul_of_nonneg_left hX (le_max_right C 0))
  calc C * ((Real.sqrt (cbNorm 2 a)) ^ 2 + (⨆ x, |Real.sqrt (a x)|) ^ 2) * ∫ x, u x ^ 2
      ≤ max C 0 * (cbNorm 2 a + cbNorm 2 a) * ∫ x, u x ^ 2 :=
        mul_le_mul_of_nonneg_right h1 hI0
    _ = 2 * max C 0 * cbNorm 2 a * ∫ x, u x ^ 2 := by ring

/-- `ξᵀ M ξ ≤ 0` for `Sym M ≤ 0`. -/
theorem sa12z3_quad_nonpos {M : Matrix (Fin d) (Fin d) ℝ} (hM : Torus.SymNonpos M) (ξ : Euc d) :
    ∑ i, ∑ j, M j i * (ξ i * ξ j) ≤ 0 := by
  have h := hM.dotProduct_mulVec_nonneg (fun i => ξ i)
  have hsw : ∑ i, ∑ j, M i j * (ξ i * ξ j) = ∑ i, ∑ j, M j i * (ξ i * ξ j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e : (star (fun i => ξ i) ⬝ᵥ ((-(Torus.symPart M)) *ᵥ (fun i => ξ i))) =
      -∑ i, ∑ j, M j i * (ξ i * ξ j) := by
    simp only [dotProduct, Matrix.mulVec, Torus.symPart, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul, Pi.star_apply, star_trivial]
    have : ∀ i, (ξ i * ∑ j, -(1 / 2 * (M i j + M j i)) * ξ j) =
        -(1 / 2) * (∑ j, M i j * (ξ i * ξ j) + ∑ j, M j i * (ξ i * ξ j)) := by
      intro i
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [this]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hsw]
    ring
  rw [e] at h
  linarith

/-- Polarization of the symbols. -/
theorem sa12z3_mq_polar (c s : ℝ) (i j : Fin d) (ξ : Euc d) :
    (1 / 4 : ℝ) * (mq c s (sa12z3_dp d i j) ξ - mq c s (sa12z3_dm d i j) ξ) =
      c * (2 * Real.pi) ^ 2 * ‖ξ‖ ^ (s - d) * (ξ i * ξ j) := by
  unfold mq sa12z3_dp sa12z3_dm
  rw [inner_add_right, inner_sub_right]
  simp only [EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  ring

end HRS.MH.AdjointRd.Phase2SA12Near
