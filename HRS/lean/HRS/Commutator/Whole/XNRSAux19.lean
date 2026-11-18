import HRS.Commutator.Whole.XNRSAux18

/-!
# Packet X-NRS, part 19: Fourier cutoffs
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- The even bump `1` on `B(0,1)`, supported in `B(0,2)`. -/
def xbump (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The profile `χ`. -/
def xchi (ξ : Euc d) : ℝ := xbump d ξ

lemma xchi_smooth : ContDiff ℝ ∞ (xchi : Euc d → ℝ) := (xbump d).contDiff

lemma xchi_cpt : HasCompactSupport (xchi : Euc d → ℝ) := (xbump d).hasCompactSupport

lemma xchi_nonneg (ξ : Euc d) : 0 ≤ xchi ξ := (xbump d).nonneg

lemma xchi_le_one (ξ : Euc d) : xchi ξ ≤ 1 := (xbump d).le_one

lemma xchi_neg (ξ : Euc d) : xchi (-ξ) = xchi ξ := (xbump d).neg ξ

lemma xchi_one {ξ : Euc d} (h : ‖ξ‖ ≤ 1) : xchi ξ = 1 :=
  (xbump d).one_of_mem_closedBall (by simpa [xbump] using h)

lemma xchi_zero {ξ : Euc d} (h : 2 ≤ ‖ξ‖) : xchi ξ = 0 :=
  (xbump d).zero_of_le_dist (by simpa [xbump] using h)

/-- `χ(ξ/R)(1-χ(rξ))`. -/
def xcut (R r : ℝ) (ξ : Euc d) : ℝ := xchi (R⁻¹ • ξ) * (1 - xchi (r • ξ))

lemma xcut_good {R r : ℝ} (hR : 0 < R) (hr : 0 < r) : XGoodCut (xcut R r : Euc d → ℝ) := by
  refine ⟨?_, ?_, ⟨1 / r, by positivity, fun ξ hξ => ?_⟩⟩
  · exact (xchi_smooth.comp (contDiff_const_smul _)).mul
      (contDiff_const.sub (xchi_smooth.comp (contDiff_const_smul _)))
  · refine HasCompactSupport.mul_right ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (2 * R)) fun ξ hξ => ?_
    apply xchi_zero
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
    have : 2 * R < ‖ξ‖ := by simpa using hξ
    rw [le_inv_mul_iff₀ hR]; linarith
  · have h1 : xchi (r • ξ) = 1 := by
      apply xchi_one
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have : ‖ξ‖ < 1 / r := hξ
      rw [lt_div_iff₀ hr] at this
      linarith
    simp [xcut, h1]

lemma xcut_nonneg (R r : ℝ) (ξ : Euc d) : 0 ≤ xcut R r ξ :=
  mul_nonneg (xchi_nonneg _) (sub_nonneg.2 (xchi_le_one _))

lemma xcut_le_one (R r : ℝ) (ξ : Euc d) : xcut R r ξ ≤ 1 := by
  unfold xcut
  have h1 := xchi_le_one (R⁻¹ • ξ)
  have h2 := xchi_nonneg (R⁻¹ • ξ)
  have h3 := xchi_nonneg (r • ξ)
  nlinarith

lemma xcut_neg (R r : ℝ) (ξ : Euc d) : xcut R r (-ξ) = xcut R r ξ := by
  unfold xcut
  rw [smul_neg, smul_neg, xchi_neg, xchi_neg]

lemma xcut_eq_one {R r : ℝ} (hR : 0 < R) (hr : 0 < r) {ξ : Euc d} (h1 : ‖ξ‖ ≤ R)
    (h2 : 2 / r ≤ ‖ξ‖) : xcut R r ξ = 1 := by
  unfold xcut
  rw [xchi_one, xchi_zero]
  · norm_num
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [div_le_iff₀ hr] at h2
    linarith
  · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
    rw [inv_mul_le_iff₀ hR]; linarith

lemma xcut_ne_zero {R r : ℝ} (hR : 0 < R) (hr : 0 < r) {ξ : Euc d} (h : xcut R r ξ ≠ 0) :
    ‖ξ‖ < 2 * R ∧ 1 / r < ‖ξ‖ := by
  unfold xcut at h
  have h1 : xchi (R⁻¹ • ξ) ≠ 0 := left_ne_zero_of_mul h
  have h2 : 1 - xchi (r • ξ) ≠ 0 := right_ne_zero_of_mul h
  constructor
  · by_contra hc
    push Not at hc
    apply h1
    apply xchi_zero
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
    rw [le_inv_mul_iff₀ hR]; linarith
  · by_contra hc
    push Not at hc
    apply h2
    rw [xchi_one, sub_self]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [le_div_iff₀ hr] at hc
    linarith

/-- `σ_n = χ(ξ/n)(1-χ(nξ))`. -/
def xσ (n : ℝ) : Euc d → ℝ := xcut n n

/-- `ρ_n = χ(ξ/(2n))(1-χ(2nξ))`. -/
def xρ (n : ℝ) : Euc d → ℝ := xcut (2 * n) (2 * n)

lemma xρ_mul_xσ {n : ℝ} (hn : 0 < n) (ξ : Euc d) : xρ n ξ * xσ n ξ = xσ n ξ := by
  by_cases h : xσ n ξ = 0
  · simp [h]
  · obtain ⟨h1, h2⟩ := xcut_ne_zero hn hn h
    have : xρ n ξ = 1 := by
      refine xcut_eq_one (by positivity) (by positivity) (by linarith) ?_
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hn] at h2
      nlinarith
    rw [this, one_mul]

lemma eventually_xσ_eq_one {ξ : Euc d} (hξ : ξ ≠ 0) : ∀ᶠ n : ℝ in atTop, xσ n ξ = 1 := by
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  filter_upwards [eventually_ge_atTop (‖ξ‖), eventually_ge_atTop (2 / ‖ξ‖),
    eventually_gt_atTop (0 : ℝ)] with n h1 h2 h3
  refine xcut_eq_one h3 h3 h1 ?_
  rw [div_le_iff₀ h3]
  rw [div_le_iff₀ hpos] at h2
  linarith

end HRS.Commutator.Whole.XNRS
