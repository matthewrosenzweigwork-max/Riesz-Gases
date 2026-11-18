import HRS.MS.Mov63CAux7

/-!
# S6.3, uniqueness chain (N3b, part 3): cutoffs and the extension to non-compactly supported tests

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.
Cutoffs `χ_n = χ(·/(n+1))`; `S_0(χ_nφ) = χ_nS_0φ - ν(2⟨∇χ_n,∇φ⟩ + φΔχ_n)`; hence `‖S_0(φ-χ_nφ)‖_{L¹} → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

/-- The fixed bump. -/
def mnc_bump (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `χ_n = χ(·/(n+1))`. -/
def mnc_cut (d : ℕ) (n : ℕ) (x : Euc d) : ℝ := mnc_bump d (((n : ℝ) + 1)⁻¹ • x)

lemma mnc_cut_smooth (n : ℕ) : ContDiff ℝ ∞ (mnc_cut d n) :=
  (mnc_bump d).contDiff.comp (contDiff_const_smul _)

lemma mnc_cut_cs (n : ℕ) : HasCompactSupport (mnc_cut d n) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) (2 * ((n : ℝ) + 1))) ?_
  intro x hx
  by_contra hxn
  apply hx
  unfold mnc_cut
  refine (mnc_bump d).zero_of_le_dist ?_
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hxn
  have hpos : 0 < ((n : ℝ) + 1) := by positivity
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos]
  show 2 ≤ _
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith

lemma mnc_cut_nonneg (n : ℕ) (x : Euc d) : 0 ≤ mnc_cut d n x := (mnc_bump d).nonneg

lemma mnc_cut_le_one (n : ℕ) (x : Euc d) : mnc_cut d n x ≤ 1 := (mnc_bump d).le_one

lemma mnc_cut_one (n : ℕ) {x : Euc d} (hx : ‖x‖ ≤ (n : ℝ) + 1) : mnc_cut d n x = 1 := by
  unfold mnc_cut
  refine (mnc_bump d).one_of_mem_closedBall ?_
  have hpos : 0 < ((n : ℝ) + 1) := by positivity
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos, inv_mul_le_iff₀ hpos]
  have : (mnc_bump d).rIn = 1 := rfl
  rw [this]
  linarith

lemma mnc_norm_gradient (u : Euc d → ℝ) (x : Euc d) : ‖gradient u x‖ = ‖fderiv ℝ u x‖ := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _

lemma mnc_cut_grad_bound : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (n : ℕ) (x : Euc d), ‖gradient (mnc_cut d n) x‖ ≤ Cg / ((n : ℝ) + 1) := by
  have hf := (mnc_bump d).contDiff (n := ⊤)
  have h1 : Continuous fun y => ‖fderiv ℝ (mnc_bump d) y‖ :=
    (hf.continuous_fderiv (by simp)).norm
  have h2 : HasCompactSupport fun y => ‖fderiv ℝ (mnc_bump d) y‖ := ((mnc_bump d).hasCompactSupport.fderiv (𝕜 := ℝ)).norm
  obtain ⟨Cg, hCg⟩ := h1.bddAbove_range_of_hasCompactSupport h2
  have hCg' : ∀ y, ‖fderiv ℝ (mnc_bump d) y‖ ≤ Cg := fun y => hCg ⟨y, rfl⟩
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg' 0)
  refine ⟨Cg, hCg0, fun n x => ?_⟩
  have hpos : 0 < ((n : ℝ) + 1) := by positivity
  set l : ℝ := ((n : ℝ) + 1)⁻¹ with hl
  have hd : HasFDerivAt (mnc_cut d n) ((fderiv ℝ (mnc_bump d) (l • x)).comp (l • ContinuousLinearMap.id ℝ (Euc d))) x := by
    have h3 : HasFDerivAt (fun y : Euc d => l • y) (l • ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).const_smul l
    exact ((((mnc_bump d).contDiff (n := 1)).differentiable one_ne_zero) (l • x)).hasFDerivAt.comp x h3
  rw [mnc_norm_gradient, hd.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have : ‖l • ContinuousLinearMap.id ℝ (Euc d)‖ ≤ l := by
    refine (ContinuousLinearMap.opNorm_smul_le l _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (ContinuousLinearMap.norm_id_le)
  calc ‖fderiv ℝ (mnc_bump d) (l • x)‖ * ‖l • ContinuousLinearMap.id ℝ (Euc d)‖ ≤ Cg * l :=
        mul_le_mul (hCg' _) this (norm_nonneg _) hCg0
    _ = Cg / ((n : ℝ) + 1) := by rw [hl]; ring

lemma mnc_cut_lap_bound : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ (n : ℕ) (x : Euc d),
    |Laplacian.laplacian (mnc_cut d n) x| ≤ Cl / ((n : ℝ) + 1) ^ 2 := by
  have h1 : Continuous fun y => |Laplacian.laplacian (⇑(mnc_bump d)) y| := (mnc_lap_cont (mnc_bump d).contDiff).abs
  have h2 : HasCompactSupport fun y => |Laplacian.laplacian (⇑(mnc_bump d)) y| :=
    (mnc_lap_cs (mnc_bump d).hasCompactSupport).abs
  obtain ⟨Cl, hCl⟩ := h1.bddAbove_range_of_hasCompactSupport h2
  have hCl' : ∀ y, |Laplacian.laplacian (⇑(mnc_bump d)) y| ≤ Cl := fun y => hCl ⟨y, rfl⟩
  have hCl0 : 0 ≤ Cl := (abs_nonneg _).trans (hCl' 0)
  refine ⟨Cl, hCl0, fun n x => ?_⟩
  have hpos : 0 < ((n : ℝ) + 1) := by positivity
  have := mov2b_laplacian_comp_smul (u := mnc_bump d) ((mnc_bump d).contDiff (n := 2)) (((n : ℝ) + 1)⁻¹) x
  have e : Laplacian.laplacian (mnc_cut d n) x = (((n : ℝ) + 1)⁻¹) ^ 2 *
      Laplacian.laplacian (⇑(mnc_bump d)) ((((n : ℝ) + 1)⁻¹) • x) := this
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  calc (((n : ℝ) + 1)⁻¹) ^ 2 * |Laplacian.laplacian (⇑(mnc_bump d)) ((((n : ℝ) + 1)⁻¹) • x)| ≤
        (((n : ℝ) + 1)⁻¹) ^ 2 * Cl := mul_le_mul_of_nonneg_left (hCl' _) (by positivity)
    _ = Cl / ((n : ℝ) + 1) ^ 2 := by field_simp


lemma mnc_S0_mul {χ φ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ) (x : Euc d) :
    mov_S0 d β q (fun y => χ y * φ y) x = χ x * mov_S0 d β q φ x -
      β⁻¹ * (2 * inner ℝ (gradient χ x) (gradient φ x) + φ x * Laplacian.laplacian χ x) := by
  have h := HRS.MD.DOMProof.domp_lap_mul (x := x) (f := χ) (g := φ) (hχ.contDiffAt.of_le (by simp))
    (hφ.contDiffAt.of_le (by simp))
  unfold mov_S0
  rw [h]
  ring

lemma mnc_tail_tendsto {F : Euc d → ℝ} (hF : Integrable F) :
    Tendsto (fun n : ℕ => ∫ x, (1 - mnc_cut d n x) * |F x|) atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun x => (1 - mnc_cut d n x) * |F x|) volume := fun n =>
    (((continuous_const.sub (mnc_cut_smooth n).continuous)).aestronglyMeasurable).mul hF.aestronglyMeasurable.norm
  have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (Euc d)))
    (F := fun (n : ℕ) x => (1 - mnc_cut d n x) * |F x|) (f := fun _ => (0 : ℝ)) (bound := fun x => |F x|)
    hmeas hF.abs ?_ ?_
  · simpa using this
  · refine fun n => Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.2 (mnc_cut_le_one n x))]
    have : 1 - mnc_cut d n x ≤ 1 := by linarith [mnc_cut_nonneg n x]
    nlinarith [abs_nonneg (F x), abs_abs (F x), abs_nonneg (F x)]
  · refine Filter.Eventually.of_forall fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨⌈‖x‖⌉₊, fun n hn => ?_⟩
    have : ‖x‖ ≤ (n : ℝ) + 1 := by
      have h1 := Nat.le_ceil ‖x‖
      have h2 : ((⌈‖x‖⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    simp [mnc_cut_one n this]

end HRS.MS.Mov63
