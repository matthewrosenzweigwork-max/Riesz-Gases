import HRS.Commutator.Whole.XNRSAux6

/-!
# Packet X-NRS, part 7: the damped kernel `K_δ(z) = N_δ(z)/(1+δ|z|²)`

`K_δ` is a continuous even integrable positive kernel with `‖z‖ K_δ ≤ (2√δ)⁻¹ N_δ`,
`∇K_δ(z) = -Q_δ(z) z` with `Q_δ ≥ 0`, `|z|² Q_δ ≤ (d+2σ+2) K_δ`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- `Φ_δ(z) = (1+δ|z|²)⁻¹`. -/
def xPhi (δ : ℝ) (z : Euc d) : ℝ := (1 + δ * ‖z‖ ^ 2)⁻¹

/-- `K_δ = N_δ Φ_δ`. -/
def xK (d : ℕ) (σ δ : ℝ) (z : Euc d) : ℝ := xN d σ δ z * xPhi δ z

/-- `Q_δ = Φ_δ (e P_δ + 2δ Φ_δ N_δ)`, `e = d+2σ`. -/
def xQ (d : ℕ) (σ δ : ℝ) (z : Euc d) : ℝ :=
  xPhi δ z * (((d : ℝ) + 2 * σ) * xP d σ δ z + 2 * δ * xPhi δ z * xN d σ δ z)

lemma xPhi_pos {δ : ℝ} (hδ : 0 < δ) (z : Euc d) : 0 < xPhi δ z := by
  unfold xPhi; positivity

lemma xPhi_le_one {δ : ℝ} (hδ : 0 < δ) (z : Euc d) : xPhi δ z ≤ 1 := by
  unfold xPhi
  apply inv_le_one_of_one_le₀
  nlinarith [sq_nonneg ‖z‖]

lemma continuous_xPhi {δ : ℝ} (hδ : 0 < δ) : Continuous (xPhi (d := d) δ) := by
  unfold xPhi
  exact Continuous.inv₀ (by fun_prop) (fun z => by positivity)

lemma xK_pos {σ δ : ℝ} (hδ : 0 < δ) (z : Euc d) : 0 < xK d σ δ z :=
  mul_pos (xN_pos hδ z) (xPhi_pos hδ z)

lemma xK_le_xN {σ δ : ℝ} (hδ : 0 < δ) (z : Euc d) : xK d σ δ z ≤ xN d σ δ z := by
  unfold xK
  exact mul_le_of_le_one_right (xN_pos hδ z).le (xPhi_le_one hδ z)

lemma xQ_nonneg {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (z : Euc d) : 0 ≤ xQ d σ δ z := by
  unfold xQ
  have := xPhi_pos hδ z
  have := xP_pos (σ := σ) hδ z
  have := xN_pos (σ := σ) hδ z
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  positivity

/-- `‖z‖ Φ_δ ≤ (2√δ)⁻¹`. -/
lemma xPhi_mul_norm_le {δ : ℝ} (hδ : 0 < δ) (z : Euc d) :
    ‖z‖ * xPhi δ z ≤ (2 * Real.sqrt δ)⁻¹ := by
  unfold xPhi
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have h1 : 2 * Real.sqrt δ * ‖z‖ ≤ 1 + δ * ‖z‖ ^ 2 := by
    have := Real.sq_sqrt hδ.le
    nlinarith [sq_nonneg (1 - Real.sqrt δ * ‖z‖)]
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma xN_norm_mul_xPhi_le {σ δ : ℝ} (hδ : 0 < δ) (z : Euc d) :
    ‖z‖ * xK d σ δ z ≤ (2 * Real.sqrt δ)⁻¹ * xN d σ δ z := by
  unfold xK
  have := xPhi_mul_norm_le hδ z
  have h0 := xN_pos (σ := σ) hδ z
  calc ‖z‖ * (xN d σ δ z * xPhi δ z) = xN d σ δ z * (‖z‖ * xPhi δ z) := by ring
    _ ≤ xN d σ δ z * (2 * Real.sqrt δ)⁻¹ := mul_le_mul_of_nonneg_left this h0.le
    _ = _ := by ring

lemma xQ_mul_sq_le {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (z : Euc d) :
    ‖z‖ ^ 2 * xQ d σ δ z ≤ ((d : ℝ) + 2 * σ + 2) * xK d σ δ z := by
  unfold xQ xK
  have h1 := xP_mul_sq_le (σ := σ) hδ z
  have h2 : 2 * δ * ‖z‖ ^ 2 * xPhi δ z ≤ 2 := by
    unfold xPhi
    rw [mul_assoc, ← div_eq_mul_inv, ← mul_div_assoc]
    have : 0 < 1 + δ * ‖z‖ ^ 2 := by positivity
    rw [div_le_iff₀ this]
    nlinarith [sq_nonneg ‖z‖]
  have hN := xN_pos (σ := σ) hδ z
  have hΦ := xPhi_pos hδ z
  have he : (0 : ℝ) ≤ (d : ℝ) + 2 * σ := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  calc ‖z‖ ^ 2 * (xPhi δ z * (((d : ℝ) + 2 * σ) * xP d σ δ z + 2 * δ * xPhi δ z * xN d σ δ z))
      = xPhi δ z * (((d : ℝ) + 2 * σ) * (‖z‖ ^ 2 * xP d σ δ z) +
          (2 * δ * ‖z‖ ^ 2 * xPhi δ z) * xN d σ δ z) := by ring
    _ ≤ xPhi δ z * (((d : ℝ) + 2 * σ) * xN d σ δ z + 2 * xN d σ δ z) := by
        gcongr
    _ = ((d : ℝ) + 2 * σ + 2) * (xN d σ δ z * xPhi δ z) := by ring

lemma xKer_xK {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) : XKer (xK d σ δ) where
  nonneg z := (xK_pos hδ z).le
  cont := (continuous_xN σ δ hδ).mul (continuous_xPhi hδ)
  integrable := by
    refine (integrable_xN hσ hδ).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((continuous_xN σ δ hδ).mul (continuous_xPhi hδ)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (xK_pos hδ z).le]; exact xK_le_xN hδ z
  even z := by simp [xK, xPhi, xN_neg]

lemma hasFDerivAt_xPhi {δ : ℝ} (hδ : 0 < δ) (z : Euc d) :
    HasFDerivAt (xPhi (d := d) δ)
      ((-(2 * δ * (xPhi δ z) ^ 2)) • innerSL ℝ z) z := by
  have hne : (1 + δ * ‖z‖ ^ 2) ≠ 0 := by positivity
  have hc : HasDerivAt (fun t : ℝ => 1 + δ * t) δ (‖z‖ ^ 2) := by
    simpa using ((hasDerivAt_id (‖z‖ ^ 2)).const_mul δ).const_add 1
  have hu := hc.inv hne
  have h2 := hu.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h3 : (-(2 * δ * (xPhi δ z) ^ 2)) • innerSL ℝ z =
      (-δ / (1 + δ * ‖z‖ ^ 2) ^ 2) • ((2 : ℕ) • innerSL ℝ z) := by
    ext u
    simp only [xPhi, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    field_simp
  rw [h3]
  exact h2

lemma hasFDerivAt_xK {σ δ : ℝ} (hδ : 0 < δ) (z : Euc d) :
    HasFDerivAt (xK d σ δ) ((-xQ d σ δ z) • innerSL ℝ z) z := by
  have hN := hasFDerivAt_xN (σ := σ) hδ z
  have hΦ := hasFDerivAt_xPhi hδ z
  have h := hN.mul hΦ
  have h3 : (-xQ d σ δ z) • innerSL ℝ z =
      xN d σ δ z • ((-(2 * δ * (xPhi δ z) ^ 2)) • innerSL ℝ z) +
        (xPhi δ z) • ((-((d : ℝ) + 2 * σ) * xP d σ δ z) • innerSL ℝ z) := by
    ext u
    simp only [xQ, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      innerSL_apply_apply, smul_eq_mul]
    ring
  rw [h3]
  exact h

end HRS.Commutator.Whole.XNRS
