import HRS.MS.Mov63CAux8

/-!
# S6.3, uniqueness chain (N3b, part 4): the linear weak identity for non-compactly supported tests

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.
`mnc_Psi_good_zero`: `Ψ_t(φ) = 0` for every good test function `φ` with `∇φ ∈ L¹`, by `Ψ(φ) = Ψ(φ - χ_nφ)` (N3a gives
`Ψ(χ_nφ) = 0`), the `L¹` bound, and `‖φ - χ_nφ‖_{L¹} + ‖S_0(φ - χ_nφ)‖_{L¹} → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

lemma mnc_Good_cut_mul {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hβ : 0 < β) (n : ℕ) :
    mnc_Good d β q (fun x => mnc_cut d n x * φ x) := by
  have hs : ContDiff ℝ ∞ (fun x => mnc_cut d n x * φ x) := (mnc_cut_smooth n).mul hφ
  have hc : HasCompactSupport (fun x => mnc_cut d n x * φ x) := (mnc_cut_cs n).mul_right (f' := φ)
  refine ⟨hs, hs.continuous.memLp_of_hasCompactSupport hc, hs.continuous.integrable_of_hasCompactSupport hc, ?_, ?_⟩
  · exact (mnc_S0_cont hβ hs).memLp_of_hasCompactSupport (mnc_S0_cs hc)
  · exact (mnc_S0_cont hβ hs).integrable_of_hasCompactSupport (mnc_S0_cs hc)

theorem mnc_Psi_good_zero (H : Mov2dTh d s β q ρ) {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) {P : ℝ → Euc d → ℝ}
    {r c₀ : ℝ} {f0 : Euc d → ℝ} (hcls : MovInSmallClass d s q β ρ m r c₀ f0 P) {t : ℝ} (ht : 0 ≤ t)
    {φ : Euc d → ℝ} (hφ : mnc_Good d β q φ) (hgrad : Integrable (fun x => ‖gradient φ x‖)) :
    mnc_Psi (β := β) H hm P t φ = 0 := by
  have hβ := H.hβ
  obtain ⟨C, hC0, hC⟩ := mnc_Psi_bound H hm hcls ht
  obtain ⟨Cg, hCg0, hCg⟩ := mnc_cut_grad_bound (d := d)
  obtain ⟨Cl, hCl0, hCl⟩ := mnc_cut_lap_bound (d := d)
  set K0 : ℝ := β⁻¹ * (2 * Cg * (∫ x, ‖gradient φ x‖) + Cl * (∫ x, |φ x|)) with hK0
  have hβi : 0 ≤ β⁻¹ := (inv_pos.2 hβ).le
  have hφabs : Integrable (fun x => |φ x|) := hφ.l1.abs
  have hSabs : Integrable (fun x => |mov_S0 d β q φ x|) := hφ.s1.abs
  have hzero : ∀ n : ℕ, mnc_Psi (β := β) H hm P t (fun x => mnc_cut d n x * φ x) = 0 := by
    intro n
    have hs : ContDiff ℝ ∞ (fun x => mnc_cut d n x * φ x) := (mnc_cut_smooth n).mul hφ.smooth
    have hc : HasCompactSupport (fun x => mnc_cut d n x * φ x) := (mnc_cut_cs n).mul_right (f' := φ)
    have := mnc_weak_linear H hm hcls hs hc ht
    unfold mnc_Psi mnc_F
    exact sub_eq_zero.2 this
  have hbound : ∀ n : ℕ, |mnc_Psi (β := β) H hm P t φ| ≤
      C * ((∫ x, (1 - mnc_cut d n x) * |φ x|) + (∫ x, (1 - mnc_cut d n x) * |mov_S0 d β q φ x|) +
        K0 / ((n : ℝ) + 1)) := by
    intro n
    have hg := mnc_Good_cut_mul (β := β) (q := q) hφ.smooth hβ n
    have hsub := hφ.sub hg
    have hPsi : mnc_Psi (β := β) H hm P t (fun y => φ y - mnc_cut d n y * φ y) =
        mnc_Psi (β := β) H hm P t φ := by
      rw [mnc_Psi_sub H hm hcls ht hφ hg, hzero n, sub_zero]
    have h1 := hC _ hsub
    rw [hPsi] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have hpos : 0 < ((n : ℝ) + 1) := by positivity
    -- first integral
    have e1 : (∫ y, |φ y - mnc_cut d n y * φ y|) = ∫ x, (1 - mnc_cut d n x) * |φ x| := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      have : φ x - mnc_cut d n x * φ x = (1 - mnc_cut d n x) * φ x := by ring
      rw [this, abs_mul, abs_of_nonneg (sub_nonneg.2 (mnc_cut_le_one n x))]
    -- second integral
    have hpt : ∀ x, |mov_S0 d β q (fun y => φ y - mnc_cut d n y * φ y) x| ≤
        (1 - mnc_cut d n x) * |mov_S0 d β q φ x| +
          β⁻¹ * ((1 / ((n : ℝ) + 1)) * (2 * Cg * ‖gradient φ x‖ + Cl * |φ x|)) := by
      intro x
      rw [mnc_S0_sub hφ.smooth ((mnc_cut_smooth n).mul hφ.smooth), mnc_S0_mul (mnc_cut_smooth n) hφ.smooth]
      have hc1 := mnc_cut_le_one n x
      have hg1 := hCg n x
      have hl1 := hCl n x
      have hinner : |inner ℝ (gradient (mnc_cut d n) x) (gradient φ x)| ≤ Cg / ((n : ℝ) + 1) * ‖gradient φ x‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hg1 (norm_nonneg _))
      have hlap : |Laplacian.laplacian (mnc_cut d n) x| ≤ Cl / ((n : ℝ) + 1) := by
        refine hl1.trans ?_
        rw [div_le_div_iff₀ (by positivity) hpos]
        nlinarith [mul_nonneg hCl0 hpos.le, sq_nonneg ((n : ℝ) + 1)]
      set a := mov_S0 d β q φ x
      set i1 := inner ℝ (gradient (mnc_cut d n) x) (gradient φ x)
      set l1 := Laplacian.laplacian (mnc_cut d n) x
      have e : a - (mnc_cut d n x * a - β⁻¹ * (2 * i1 + φ x * l1)) =
          (1 - mnc_cut d n x) * a + β⁻¹ * (2 * i1 + φ x * l1) := by ring
      have hmid : |2 * i1 + φ x * l1| ≤ (1 / ((n : ℝ) + 1)) * (2 * Cg * ‖gradient φ x‖ + Cl * |φ x|) := by
        calc |2 * i1 + φ x * l1| ≤ 2 * |i1| + |φ x| * |l1| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul]; norm_num
          _ ≤ 2 * (Cg / ((n : ℝ) + 1) * ‖gradient φ x‖) + |φ x| * (Cl / ((n : ℝ) + 1)) := by
              gcongr
          _ = (1 / ((n : ℝ) + 1)) * (2 * Cg * ‖gradient φ x‖ + Cl * |φ x|) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (sub_nonneg.2 hc1), abs_mul, abs_of_nonneg hβi]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hmid hβi)
    have hintA : Integrable (fun x => (1 - mnc_cut d n x) * |mov_S0 d β q φ x|) := by
      have hc : Continuous fun x => (1 - mnc_cut d n x) := continuous_const.sub (mnc_cut_smooth n).continuous
      refine Integrable.bdd_mul (c := 1) hSabs hc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (mnc_cut_le_one n x))]
      linarith [mnc_cut_nonneg n x]
    have hintB : Integrable (fun x => β⁻¹ * ((1 / ((n : ℝ) + 1)) *
        (2 * Cg * ‖gradient φ x‖ + Cl * |φ x|))) :=
      (((hgrad.const_mul (2 * Cg)).add (hφabs.const_mul Cl)).const_mul _).const_mul _
    have e2 : (∫ y, |mov_S0 d β q (fun y => φ y - mnc_cut d n y * φ y) y|) ≤
        (∫ x, (1 - mnc_cut d n x) * |mov_S0 d β q φ x|) + K0 / ((n : ℝ) + 1) := by
      have hl : Integrable (fun y => |mov_S0 d β q (fun y => φ y - mnc_cut d n y * φ y) y|) := hsub.s1.abs
      refine (integral_mono hl (hintA.add hintB) hpt).trans (le_of_eq ?_)
      have eB : ∫ x, β⁻¹ * ((1 / ((n : ℝ) + 1)) * (2 * Cg * ‖gradient φ x‖ + Cl * |φ x|)) =
          K0 / ((n : ℝ) + 1) := by
        rw [integral_const_mul, integral_const_mul,
          integral_add (hgrad.const_mul (2 * Cg)) (hφabs.const_mul Cl), integral_const_mul, integral_const_mul, hK0]
        ring
      simp only [Pi.add_apply]
      rw [integral_add hintA hintB, eB]
    rw [e1]
    linarith
  -- pass to the limit
  have hlim : Tendsto (fun n : ℕ => C * ((∫ x, (1 - mnc_cut d n x) * |φ x|) +
      (∫ x, (1 - mnc_cut d n x) * |mov_S0 d β q φ x|) + K0 / ((n : ℝ) + 1))) atTop (𝓝 (C * (0 + 0 + 0))) := by
    refine Tendsto.const_mul C ((( mnc_tail_tendsto hφ.l1).add (mnc_tail_tendsto hφ.s1)).add ?_)
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul K0
    simpa [div_eq_mul_inv, mul_one_div] using this
  have hle := ge_of_tendsto' hlim hbound
  simp only [add_zero, mul_zero] at hle
  exact abs_nonpos_iff.1 hle

end HRS.MS.Mov63
