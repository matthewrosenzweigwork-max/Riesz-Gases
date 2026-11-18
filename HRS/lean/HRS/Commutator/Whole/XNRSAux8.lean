import HRS.Commutator.Whole.XNRSAux7

/-!
# Packet X-NRS, part 8: bounds for the integration by parts at fixed `y`

Lipschitz facts for the temperate field `v`, integrable majorants, and the line derivative of
`g_c(x) = v_c(x) K_δ(x-y)`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- `v` is `L`-Lipschitz. -/
def XLip (v : Euc d → Euc d) (L : ℝ) : Prop := ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖

lemma xw_le {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L)
    (a c : Fin d) (x : Euc d) : |xw v a c x| ≤ L := by
  have hlip : LipschitzWith (Real.toNNReal L) (fun y => v y c) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [Real.dist_eq, dist_eq_norm]
    have h1 : |v y c - v z c| ≤ ‖v y - v z‖ := by
      have := PiLp.norm_apply_le (v y - v z) c
      simpa [Real.norm_eq_abs] using this
    refine h1.trans ?_
    refine (hL y z).trans ?_
    rw [Real.coe_toNNReal _ hL0]
  have hd := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
  rw [xw_eq_fderiv v a c hv x]
  have h2 : ‖fderiv ℝ (fun y => v y c) x (xe a)‖ ≤ (Real.toNNReal L : ℝ) * ‖xe a‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  have h3 : ‖xe a‖ = 1 := by simp [xe]
  rw [h3, mul_one, Real.coe_toNNReal _ hL0] at h2
  rw [← Real.norm_eq_abs]
  exact h2

lemma xv_growth {v : Euc d → Euc d} {L : ℝ} (hL : XLip v L) (x : Euc d) :
    ‖v x‖ ≤ ‖v 0‖ + L * ‖x‖ := by
  have := hL x 0
  simp only [sub_zero] at this
  calc ‖v x‖ = ‖v 0 + (v x - v 0)‖ := by simp
    _ ≤ ‖v 0‖ + ‖v x - v 0‖ := norm_add_le _ _
    _ ≤ _ := by linarith


lemma xQ_norm_le {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (z : Euc d) :
    ‖z‖ * xQ d σ δ z ≤ ((d : ℝ) + 2 * σ) * (‖z‖ * xP d σ δ z) + Real.sqrt δ * xN d σ δ z := by
  unfold xQ
  have hΦ0 := xPhi_pos hδ z
  have hΦ1 := xPhi_le_one hδ z
  have hP := xP_pos (σ := σ) hδ z
  have hN := xN_pos (σ := σ) hδ z
  have hz := xPhi_mul_norm_le hδ z
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hss := Real.sq_sqrt hδ.le
  have he : (0 : ℝ) ≤ (d : ℝ) + 2 * σ := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have e1 : ‖z‖ * (xPhi δ z * (((d : ℝ) + 2 * σ) * xP d σ δ z + 2 * δ * xPhi δ z * xN d σ δ z)) =
      ((d : ℝ) + 2 * σ) * (xPhi δ z * (‖z‖ * xP d σ δ z)) +
        2 * δ * xPhi δ z * ((‖z‖ * xPhi δ z) * xN d σ δ z) := by ring
  rw [e1]
  have h2 : 2 * δ * xPhi δ z * ((‖z‖ * xPhi δ z) * xN d σ δ z) ≤ Real.sqrt δ * xN d σ δ z := by
    have : 2 * δ * (2 * Real.sqrt δ)⁻¹ = Real.sqrt δ := by
      field_simp
      nlinarith
    calc 2 * δ * xPhi δ z * ((‖z‖ * xPhi δ z) * xN d σ δ z)
        ≤ 2 * δ * 1 * ((2 * Real.sqrt δ)⁻¹ * xN d σ δ z) := by gcongr
      _ = (2 * δ * (2 * Real.sqrt δ)⁻¹) * xN d σ δ z := by ring
      _ = Real.sqrt δ * xN d σ δ z := by rw [this]
  have h1 : ((d : ℝ) + 2 * σ) * (xPhi δ z * (‖z‖ * xP d σ δ z)) ≤
      ((d : ℝ) + 2 * σ) * (‖z‖ * xP d σ δ z) := by
    apply mul_le_mul_of_nonneg_left _ he
    exact mul_le_of_le_one_left (by positivity) hΦ1
  linarith

lemma xint_dom {F : Euc d → ℂ} (hF : AEStronglyMeasurable F volume) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (y : Euc d) (A B : ℝ)
    (hb : ∀ x, ‖F x‖ ≤ A * xN d σ δ (x - y) + B * (‖x - y‖ * xP d σ δ (x - y))) :
    Integrable F := by
  have h1 : Integrable (fun x : Euc d => xN d σ δ (x - y)) := (integrable_xN hσ hδ).comp_sub_right y
  have h2 : Integrable (fun x : Euc d => ‖x - y‖ * xP d σ δ (x - y)) :=
    (integrable_norm_xP hσ hδ).comp_sub_right y
  exact ((h1.const_mul A).add (h2.const_mul B)).mono' hF
    (Eventually.of_forall fun x => hb x)


/-- `g_c(x) = v_c(x) K_δ(x-y)`. -/
def xg (v : Euc d → Euc d) (σ δ : ℝ) (y : Euc d) (c : Fin d) (x : Euc d) : ℝ :=
  v x c * xK d σ δ (x - y)

/-- `∂_c g_c(x) = (∂_c v_c) K_δ(x-y) - v_c(x) (x-y)_c Q_δ(x-y)`. -/
def xg' (v : Euc d → Euc d) (σ δ : ℝ) (y : Euc d) (c : Fin d) (x : Euc d) : ℝ :=
  xw v c c x * xK d σ δ (x - y) - v x c * ((x - y) c * xQ d σ δ (x - y))

/-- `G_y = ∑_c ∂_c g_c`. -/
def xGy (v : Euc d → Euc d) (σ δ : ℝ) (y : Euc d) (x : Euc d) : ℝ := ∑ c, xg' v σ δ y c x

lemma hasFDerivAt_xg {v : Euc d → Euc d} (hv : XTVF v) {σ δ : ℝ} (hδ : 0 < δ) (y : Euc d)
    (c : Fin d) (x : Euc d) :
    HasFDerivAt (xg v σ δ y c)
      ((v x c) • ((-xQ d σ δ (x - y)) • innerSL ℝ (x - y)) +
        xK d σ δ (x - y) • fderiv ℝ (fun x : Euc d => v x c) x) x := by
  have h1 : HasFDerivAt (fun x : Euc d => v x c) (fderiv ℝ (fun x : Euc d => v x c) x) x :=
    (((hv c).1.differentiable (by simp)) x).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Euc d => xK d σ δ (x - y))
      ((-xQ d σ δ (x - y)) • innerSL ℝ (x - y)) x := by
    have := (hasFDerivAt_xK (σ := σ) hδ (x - y)).comp x ((hasFDerivAt_id x).sub_const y)
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have h3 := h1.mul h2
  have hg : xg v σ δ y c = (fun x : Euc d => v x c) * (fun x : Euc d => xK d σ δ (x - y)) := by
    funext x; rfl
  rw [hg]
  exact h3

lemma xg'_eq_fderiv {v : Euc d → Euc d} (hv : XTVF v) {σ δ : ℝ} (y : Euc d) (c : Fin d)
    (x : Euc d) :
    xg' v σ δ y c x =
      (((v x c) • ((-xQ d σ δ (x - y)) • innerSL ℝ (x - y)) +
        xK d σ δ (x - y) • fderiv ℝ (fun x : Euc d => v x c) x) (xe c)) := by
  simp only [xg', ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  rw [← xw_eq_fderiv v c c hv x]
  have : inner ℝ (x - y) (xe c) = (x - y) c := by
    simp [xe, EuclideanSpace.inner_single_right]
  rw [this]
  ring

lemma hasFDerivAt_xgC {v : Euc d → Euc d} (hv : XTVF v) {σ δ : ℝ} (hδ : 0 < δ) (y : Euc d)
    (c : Fin d) (x : Euc d) :
    HasFDerivAt (fun x => ((xg v σ δ y c x : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((v x c) • ((-xQ d σ δ (x - y)) • innerSL ℝ (x - y)) +
        xK d σ δ (x - y) • fderiv ℝ (fun x : Euc d => v x c) x)) x :=
  Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_xg hv hδ y c x)

lemma xlipbound {v : Euc d → Euc d} {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) (y x : Euc d) :
    ‖v x‖ ≤ (‖v 0‖ + L * ‖y‖) + L * ‖x - y‖ := by
  have h := xv_growth hL x
  have : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    calc ‖x‖ = ‖y + (x - y)‖ := by simp
      _ ≤ _ := norm_add_le _ _
  nlinarith

lemma xg_bound {v : Euc d → Euc d} {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (y : Euc d) (c : Fin d) (x : Euc d) :
    |xg v σ δ y c x| ≤ ((‖v 0‖ + L * ‖y‖) + L * (2 * Real.sqrt δ)⁻¹) * xN d σ δ (x - y) := by
  unfold xg
  set z := x - y with hz
  have hK := xK_pos (σ := σ) hδ z
  have h1 : |v x c| ≤ ‖v x‖ := by
    have := PiLp.norm_apply_le (v x) c
    simpa [Real.norm_eq_abs] using this
  have h2 := xlipbound hL0 hL y x
  have h3 := xN_norm_mul_xPhi_le (σ := σ) hδ z
  have h4 := xK_le_xN (σ := σ) hδ z
  have ha : 0 ≤ ‖v 0‖ + L * ‖y‖ := by positivity
  rw [abs_mul, abs_of_pos hK]
  calc |v x c| * xK d σ δ z ≤ ((‖v 0‖ + L * ‖y‖) + L * ‖z‖) * xK d σ δ z :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hK.le
    _ = (‖v 0‖ + L * ‖y‖) * xK d σ δ z + L * (‖z‖ * xK d σ δ z) := by ring
    _ ≤ (‖v 0‖ + L * ‖y‖) * xN d σ δ z + L * ((2 * Real.sqrt δ)⁻¹ * xN d σ δ z) := by
        gcongr
    _ = _ := by ring

lemma xg'_bound {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L)
    {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (y : Euc d) (c : Fin d) (x : Euc d) :
    |xg' v σ δ y c x| ≤
      (L + (‖v 0‖ + L * ‖y‖) * Real.sqrt δ + L * ((d : ℝ) + 2 * σ + 2)) * xN d σ δ (x - y) +
      ((‖v 0‖ + L * ‖y‖) * ((d : ℝ) + 2 * σ)) * (‖x - y‖ * xP d σ δ (x - y)) := by
  unfold xg'
  set z := x - y with hz
  have hK := xK_pos (σ := σ) hδ z
  have hN := xN_pos (σ := σ) hδ z
  have hQ := xQ_nonneg hσ hδ z
  have h1 : |v x c| ≤ ‖v x‖ := by
    have := PiLp.norm_apply_le (v x) c
    simpa [Real.norm_eq_abs] using this
  have h2 := xlipbound hL0 hL y x
  have h4 := xK_le_xN (σ := σ) hδ z
  have h5 := xQ_norm_le hσ hδ z
  have h6 := xQ_mul_sq_le hσ hδ z
  have h7 : |z c| ≤ ‖z‖ := by
    have := PiLp.norm_apply_le z c
    simpa [Real.norm_eq_abs] using this
  have hw := xw_le hv hL0 hL c c x
  have ha : 0 ≤ ‖v 0‖ + L * ‖y‖ := by positivity
  have hP := xP_pos (σ := σ) hδ z
  have he : (0 : ℝ) ≤ (d : ℝ) + 2 * σ := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hT : |v x c * (z c * xQ d σ δ z)| ≤
      ((‖v 0‖ + L * ‖y‖) + L * ‖z‖) * (‖z‖ * xQ d σ δ z) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hQ]
    have : |z c| * xQ d σ δ z ≤ ‖z‖ * xQ d σ δ z := mul_le_mul_of_nonneg_right h7 hQ
    exact mul_le_mul (h1.trans h2) this (by positivity) (by positivity)
  have hT2 : ((‖v 0‖ + L * ‖y‖) + L * ‖z‖) * (‖z‖ * xQ d σ δ z) ≤
      (‖v 0‖ + L * ‖y‖) * (((d : ℝ) + 2 * σ) * (‖z‖ * xP d σ δ z) + Real.sqrt δ * xN d σ δ z) +
        L * (((d : ℝ) + 2 * σ + 2) * xN d σ δ z) := by
    have e1 : ((‖v 0‖ + L * ‖y‖) + L * ‖z‖) * (‖z‖ * xQ d σ δ z) =
        (‖v 0‖ + L * ‖y‖) * (‖z‖ * xQ d σ δ z) + L * (‖z‖ ^ 2 * xQ d σ δ z) := by ring
    rw [e1]
    have h8 : ‖z‖ ^ 2 * xQ d σ δ z ≤ ((d : ℝ) + 2 * σ + 2) * xN d σ δ z :=
      h6.trans (mul_le_mul_of_nonneg_left h4 (by linarith))
    gcongr
  have hA : |xw v c c x * xK d σ δ z| ≤ L * xN d σ δ z := by
    rw [abs_mul, abs_of_pos hK]
    exact (mul_le_mul_of_nonneg_right hw hK.le).trans (mul_le_mul_of_nonneg_left h4 hL0)
  have hB := hT.trans hT2
  have hC := add_le_add hA hB
  have hD := abs_sub (xw v c c x * xK d σ δ z) (v x c * (z c * xQ d σ δ z))
  have hE := hD.trans hC
  refine hE.trans (le_of_eq ?_)
  ring

end HRS.Commutator.Whole.XNRS
