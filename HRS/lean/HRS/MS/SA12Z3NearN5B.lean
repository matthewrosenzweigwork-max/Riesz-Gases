import HRS.MS.SA12Z3NearN5A

/-!
# S.A.12 N5 (SA12Z3), part B: the weighted symmetrization for one direction

For `a ≥ 0` in `C²_b` and `u ∈ C²_c`: `|B_q(a u, u) - B_q(√a u, √a u)| ≤ C_q ‖a‖_{C²_b} ‖u‖²`, from
`quadratic_toolbox_weighted` with the Glaeser bound `Lip √a ≤ √‖a‖_{C²_b}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MS.UniqN3a HRS.MS.UniqN3c
  HRS.PDE.ToolboxRd

variable {d : ℕ}

theorem sa12z3_single_le_cb {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) {j : ℕ} (hj : j ≤ k)
    (x : Euc d) : ‖iteratedFDeriv ℝ j f x‖ ≤ cbNorm k f := by
  unfold cbNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  exact le_ciSup (hf.2 j hj) x

theorem sa12z3_cb_nonneg {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) : 0 ≤ cbNorm k f :=
  (norm_nonneg _).trans (sa12z3_single_le_cb hf (Nat.zero_le k) 0)

/-- The three bounds extracted from `MemCb 2`. -/
theorem sa12z3_cb2_bounds {a : Euc d → ℝ} (ha : MemCb 2 a) (x : Euc d) :
    |a x| ≤ cbNorm 2 a ∧ ‖fderiv ℝ a x‖ ≤ cbNorm 2 a ∧
      ‖fderiv ℝ (fderiv ℝ a) x‖ ≤ cbNorm 2 a := by
  refine ⟨?_, ?_, ?_⟩
  · have := sa12z3_single_le_cb ha (Nat.zero_le 2) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := sa12z3_single_le_cb ha (by norm_num : 1 ≤ 2) x
    rwa [norm_iteratedFDeriv_one] at this
  · have := sa12z3_single_le_cb ha (le_refl 2) x
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at this

/-- `√a` is Lipschitz with constant `√‖a‖_{C²_b}`. -/
theorem sa12z3_sqrt_lip {a : Euc d → ℝ} (ha : MemCb 2 a) (h0 : ∀ x, 0 ≤ a x) :
    IsLipschitz (Real.sqrt (cbNorm 2 a)) (fun x => Real.sqrt (a x)) := by
  have hcb0 := sa12z3_cb_nonneg ha
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  rcases hcb0.eq_or_lt with h | h
  · have hz : ∀ x, a x = 0 := fun x => by
      have := (sa12z3_cb2_bounds ha x).1
      rw [← h] at this
      exact abs_nonpos_iff.1 this
    intro x y
    simp [hz]
    positivity
  · have := HRS.MS.UniqN3c.n3c_sqrt_lip (φ := fun x => a x / cbNorm 2 a) (B := 1)
      (ha2.div_const _) (fun x => div_nonneg (h0 x) h.le) (fun x => ?_)
    · intro x y
      have h1 := this x y
      simp only at h1 ⊢
      have e : ∀ z, Real.sqrt (a z) = Real.sqrt (cbNorm 2 a) * Real.sqrt (a z / cbNorm 2 a) := by
        intro z
        rw [← Real.sqrt_mul h.le, mul_div_cancel₀ _ h.ne']
      have h2 : Real.sqrt ((1 + 1) / 2 : ℝ) = 1 := by norm_num
      rw [h2, one_mul] at h1
      rw [e x, e y, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt (cbNorm 2 a) * |Real.sqrt (a x / cbNorm 2 a) - Real.sqrt (a y / cbNorm 2 a)|
          ≤ Real.sqrt (cbNorm 2 a) * (1 * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left (by rw [one_mul]; exact h1) (Real.sqrt_nonneg _)
        _ = _ := by ring
    · have hfd : fderiv ℝ (fun x => a x / cbNorm 2 a) = fun x => (cbNorm 2 a)⁻¹ • fderiv ℝ a x := by
        funext z
        rw [show (fun x => a x / cbNorm 2 a) = fun x => (cbNorm 2 a)⁻¹ * a x from by
          funext w; rw [div_eq_inv_mul]]
        rw [fderiv_const_mul ((ha2.differentiable (by norm_num)) z)]
      rw [hfd]
      have hd2 : DifferentiableAt ℝ (fderiv ℝ a) x :=
        ((ha2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
      show ‖fderiv ℝ (fun x => (cbNorm 2 a)⁻¹ • fderiv ℝ a x) x‖ ≤ 1
      rw [show (fun x => (cbNorm 2 a)⁻¹ • fderiv ℝ a x) = (cbNorm 2 a)⁻¹ • fderiv ℝ a from rfl,
        fderiv_const_smul hd2]
      refine (ContinuousLinearMap.opNorm_smul_le ((cbNorm 2 a)⁻¹) (fderiv ℝ (fderiv ℝ a) x)).trans ?_
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 h)]
      calc (cbNorm 2 a)⁻¹ * ‖fderiv ℝ (fderiv ℝ a) x‖ ≤ (cbNorm 2 a)⁻¹ * cbNorm 2 a := by
            gcongr; exact (sa12z3_cb2_bounds ha x).2.2
        _ = 1 := inv_mul_cancel₀ h.ne'

/-- Lipschitz bound of `a` itself. -/
theorem sa12z3_a_lip {a : Euc d → ℝ} (ha : MemCb 2 a) : IsLipschitz (cbNorm 2 a) a := by
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  have hl : LipschitzWith (Real.toNNReal (cbNorm 2 a)) a :=
    lipschitzWith_of_nnnorm_fderiv_le (ha2.differentiable (by norm_num)) (fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (sa12z3_cb_nonneg ha)]
      exact (sa12z3_cb2_bounds ha x).2.1)
  intro x y
  have := hl.dist_le_mul x y
  rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (sa12z3_cb_nonneg ha)] at this

theorem sa12z3_a_c11 {a : Euc d → ℝ} (ha : MemCb 2 a) : IsC11 (cbNorm 2 a) a := by
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  refine ⟨ha2.of_le (by norm_num), ⟨cbNorm 2 a, fun x => (sa12z3_cb2_bounds ha x).1⟩,
    ⟨cbNorm 2 a, fun x => (sa12z3_cb2_bounds ha x).2.1⟩, ?_⟩
  refine lipschitzWith_of_nnnorm_fderiv_le
    ((ha2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) (fun x => ?_)
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (sa12z3_cb_nonneg ha)]
  exact (sa12z3_cb2_bounds ha x).2.2

/-- A `C²` function with compact support is Lipschitz and in `H¹`. -/
theorem sa12z3_u_facts {u : Euc d → ℝ} (hu : MemCb 2 u) (huc : HasCompactSupport u) :
    (∃ L, HRS.PDE.ToolboxRd.IsLipschitz L u) ∧ HRS.PDE.ToolboxRd.MemSobolev 1 u := by
  have hu2 : ContDiff ℝ 2 u := by simpa using hu.1
  obtain ⟨K, hK⟩ := hu2.lipschitzWith_of_hasCompactSupport (hf := huc) (by norm_num)
  have hL : IsLipschitz K u := fun x y => by
    have := hK.dist_le_mul x y
    rwa [Real.dist_eq, dist_eq_norm] at this
  exact ⟨⟨K, hL⟩, HRS.MS.UniqT1.t1_memSobolev_one hL huc⟩

end HRS.MH.AdjointRd.Phase2SA12Near
