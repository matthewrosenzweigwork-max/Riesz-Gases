import HRS.MS.SuppA0Aux1

/-!
# A0 auxiliary 2: the shifted time-dependent test functions `f r x = ψ(x + a_r)` and `VHypRd` for `V = q|x|²/2`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.A0

open HRS.Whole HRS.MH.DualityRd HRS.Whole.AppendixA

variable {d : ℕ}

/-- The shifted test `f r x = ψ(x + a_r)`. -/
def a0_f (ψ : Euc d → ℝ) (q : ℝ) (a₀ : Euc d) (r : ℝ) (x : Euc d) : ℝ := ψ (x + movShift q a₀ r)

/-- Its time derivative `ft r x = ⟨∇ψ(x + a_r), -q a_r⟩`. -/
def a0_ft (ψ : Euc d → ℝ) (q : ℝ) (a₀ : Euc d) (r : ℝ) (x : Euc d) : ℝ :=
  inner ℝ (gradient ψ (x + movShift q a₀ r)) ((-q) • movShift q a₀ r)

lemma a0_continuous_movShift (q : ℝ) (a₀ : Euc d) : Continuous (movShift q a₀) := by
  unfold movShift
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul continuous_const

lemma a0_movShift_hasDerivAt (q : ℝ) (a₀ : Euc d) (r : ℝ) :
    HasDerivAt (fun r => movShift q a₀ r) ((-q) • movShift q a₀ r) r := by
  unfold movShift
  have h : HasDerivAt (fun r : ℝ => Real.exp (-q * r)) (Real.exp (-q * r) * (-q)) r := by
    have := ((hasDerivAt_id r).const_mul (-q)).exp
    simpa using this
  have h2 := h.smul_const a₀
  convert h2 using 1
  rw [smul_smul]
  congr 1
  ring

lemma a0_norm_movShift_le {q : ℝ} (hq : 0 ≤ q) (a₀ : Euc d) {r : ℝ} (hr : 0 ≤ r) :
    ‖movShift q a₀ r‖ ≤ ‖a₀‖ := by
  unfold movShift
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have : Real.exp (-q * r) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  exact mul_le_of_le_one_left (norm_nonneg _) this

lemma a0_norm_fderiv_eq (ψ : Euc d → ℝ) (z : Euc d) :
    ‖fderiv ℝ ψ z‖ = ‖iteratedFDeriv ℝ 1 ψ z‖ := by
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := ψ) (x := z) (n := 0)
  rw [norm_iteratedFDeriv_zero] at this
  simpa using this

theorem a0_isC12 {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) {q : ℝ} (hq : 0 ≤ q) (a₀ : Euc d) (t : ℝ) :
    IsC12TestRd t (a0_f ψ q a₀) (a0_ft ψ q a₀) := by
  have hψ2 : ContDiff ℝ 2 ψ := by simpa using hψ.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r _
    exact hψ2.comp (contDiff_id.add contDiff_const)
  · intro j hj
    obtain ⟨B, hB⟩ := hψ.2 j hj
    refine ⟨B, fun r _ x => ?_⟩
    show ‖iteratedFDeriv ℝ j (fun y => ψ (y + movShift q a₀ r)) x‖ ≤ B
    rw [iteratedFDeriv_comp_add_right]
    exact hB (Set.mem_range_self _)
  · intro j hj
    have hc : Continuous (iteratedFDeriv ℝ j ψ) := hψ2.continuous_iteratedFDeriv (by exact_mod_cast hj)
    have : (fun p : Set.Icc (0 : ℝ) t × Euc d => iteratedFDeriv ℝ j (a0_f ψ q a₀ p.1) p.2) =
        fun p => iteratedFDeriv ℝ j ψ (p.2 + movShift q a₀ p.1.1) := by
      funext p
      exact iteratedFDeriv_comp_add_right j _ _
    rw [this]
    exact hc.comp (continuous_snd.add
      ((a0_continuous_movShift q a₀).comp (continuous_subtype_val.comp continuous_fst)))
  · intro x r _
    have h1 : HasFDerivAt ψ (fderiv ℝ ψ (x + movShift q a₀ r)) (x + movShift q a₀ r) :=
      (hψ2.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have h2 : HasDerivAt (fun r' => x + movShift q a₀ r') ((-q) • movShift q a₀ r) r :=
      (a0_movShift_hasDerivAt q a₀ r).const_add x
    have := h1.comp_hasDerivAt r h2
    unfold a0_ft
    rw [a0_inner_gradient]
    exact this
  · have hg := a0_continuous_gradient hψ2
    have : (fun p : Set.Icc (0 : ℝ) t × Euc d => a0_ft ψ q a₀ p.1 p.2) =
        fun p => inner ℝ (gradient ψ (p.2 + movShift q a₀ p.1.1)) ((-q) • movShift q a₀ p.1.1) := rfl
    rw [this]
    have hs : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => movShift q a₀ p.1.1 :=
      (a0_continuous_movShift q a₀).comp (continuous_subtype_val.comp continuous_fst)
    exact (hg.comp (continuous_snd.add hs)).inner (hs.const_smul (-q))
  · obtain ⟨B1, hB1⟩ := hψ.2 1 (by norm_num)
    have hB1nn : 0 ≤ B1 := le_trans (norm_nonneg _) (hB1 (Set.mem_range_self 0))
    refine ⟨B1 * (q * ‖a₀‖), fun r hr x => ?_⟩
    have hB : 0 ≤ B1 * (q * ‖a₀‖) := by positivity
    have h1 : ‖gradient ψ (x + movShift q a₀ r)‖ ≤ B1 := by
      rw [a0_norm_gradient, a0_norm_fderiv_eq]
      exact hB1 (Set.mem_range_self _)
    have h2 : ‖(-q) • movShift q a₀ r‖ ≤ q * ‖a₀‖ := by
      rw [norm_smul, norm_neg, Real.norm_of_nonneg hq]
      exact mul_le_mul_of_nonneg_left (a0_norm_movShift_le hq a₀ hr.1) hq
    calc |a0_ft ψ q a₀ r x| ≤ ‖gradient ψ (x + movShift q a₀ r)‖ * ‖(-q) • movShift q a₀ r‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ B1 * (q * ‖a₀‖) := mul_le_mul h1 h2 (norm_nonneg _) hB1nn
      _ ≤ B1 * (q * ‖a₀‖) * (1 + ‖x‖) :=
          le_mul_of_one_le_right hB (by linarith [norm_nonneg x])

/-- The drift test function of the shifted test is the generator applied to `ψ`, shifted by `a_r`. -/
lemma a0_driftTest (s q β : ℝ) (ψ : Euc d → ℝ) (a₀ : Euc d) (r : ℝ) (x : Euc d) :
    driftTestRd (quadraticGradientDyn d s q β) (a0_f ψ q a₀) (a0_ft ψ q a₀) r x =
      β⁻¹ * Laplacian.laplacian ψ (x + movShift q a₀ r) -
        inner ℝ (gradient (confinement q) (x + movShift q a₀ r)) (gradient ψ (x + movShift q a₀ r)) := by
  unfold driftTestRd a0_ft
  have e1 : a0_f ψ q a₀ r = fun y => ψ (y + movShift q a₀ r) := rfl
  simp only [quadraticGradientDyn]
  rw [e1, a0_laplacian_comp_add, a0_gradient_comp_add, movtr_gradient_confinement,
    movtr_gradient_confinement]
  rw [real_inner_comm (gradient ψ _), real_inner_comm (gradient ψ _)]
  simp only [inner_smul_right, inner_add_right]
  ring

lemma a0_vhyp (q : ℝ) : ∃ ΛV : ℝ, VHypRd 2 ΛV 0 (confinement (d := d) q) := by
  have hV : (confinement (d := d) q) = fun x => q * ‖x‖ ^ 2 / 2 := by
    funext y; unfold confinement; rfl
  let I : Euc d →L[ℝ] Euc d →L[ℝ] ℝ := innerSL ℝ
  let L : Euc d →L[ℝ] Euc d →L[ℝ] ℝ := q • I
  have hF : fderiv ℝ (confinement (d := d) q) = ⇑L := by
    funext y
    have hg : gradient (confinement (d := d) q) y = q • y := movtr_gradient_confinement q y
    unfold gradient at hg
    have := (InnerProductSpace.toDual ℝ (Euc d)).apply_symm_apply (fderiv ℝ (confinement (d := d) q) y)
    rw [hg] at this
    rw [← this]
    ext v
    simp only [L, I, InnerProductSpace.toDual_apply_apply, inner_smul_left, smul_apply,
      RCLike.conj_to_real, smul_eq_mul]
    rfl
  refine ⟨‖L‖, ?_, ?_, ?_⟩
  · rw [hV]
    exact ((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2)
  · intro j h1 h2
    obtain rfl : j = 2 := le_antisymm h2 h1
    intro x
    have e1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := confinement (d := d) q) (x := x) (n := 1)
    rw [hF] at e1
    have e2 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := ⇑L) (x := x) (n := 0)
    rw [norm_iteratedFDeriv_zero, ContinuousLinearMap.fderiv] at e2
    rw [← e1]
    simpa using e2.symm.le
  · rw [movtr_gradient_confinement]
    simp

end HRS.MS.A0
