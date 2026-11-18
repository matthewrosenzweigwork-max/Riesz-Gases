import HRS.MS.LogRegAux2

/-!
# C-REG-e (part 1): the Riesz potential `x ↦ ∫ ‖x - y‖^{-s} F y dy` is `C¹` for rapidly decaying measurable `F`

(`s > 0`, `s + 1 < d`.)  Namespace `HRS.MS.Thm`, helper prefix `rege_`.  This is the exact analogue of
`HRS.MS.LogReg.lreg_potential` (logarithmic case) for the power kernel `g(z) = ‖z‖^{-s}`:
smooth regularisation `g_ε(z) = (ε² + ‖z‖²)^{-s/2}`, `∇g_ε = -s (ε² + ‖z‖²)^{-s/2-1} z`, and the uniform estimates
`|g - g_ε| ≤ c ε^θ ‖z‖^{-(s+θ)}`, `‖κ_ε - κ‖ ≤ c ε^θ ‖z‖^{-(s+1+θ)}` (with `κ(z) = ‖z‖^{-(s+2)} z`,
`∇g = -s κ`), where `0 < θ ≤ 1` and `s + 1 + θ < d` (so all kernels are locally integrable).
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.Thm

open HRS HRS.Whole HRS.MS.LogReg

variable {d : ℕ}

/-- `κ_s(z) = ‖z‖^{-(s+2)} z`; `∇ ‖z‖^{-s} = -s κ_s(z)`. -/
def rege_kap (s : ℝ) (z : Euc d) : Euc d := (‖z‖ ^ (-(s + 2))) • z

/-- Regularised kernel. -/
def rege_gE (s ε : ℝ) (z : Euc d) : ℝ := (ε ^ 2 + ‖z‖ ^ 2) ^ (-(s / 2))

/-- Regularised `κ_s`. -/
def rege_kE (s ε : ℝ) (z : Euc d) : Euc d := ((ε ^ 2 + ‖z‖ ^ 2) ^ (-(s / 2 + 1))) • z

/-- The potential `∫ ‖x - y‖^{-s} F y dy`. -/
def rege_U (s : ℝ) (F : Euc d → ℝ) (x : Euc d) : ℝ := ∫ y, ‖x - y‖ ^ (-s) * F y

/-- `∫ F y κ_s(x - y) dy`. -/
def rege_W (s : ℝ) (F : Euc d → ℝ) (x : Euc d) : Euc d := ∫ y, F y • rege_kap s (x - y)

/-! ### Scalar inequalities -/

/-- `0 ≤ 1 - (1+t²)^{-q} ≤ max 1 q · t^θ` for `0 < θ ≤ 2`. -/
lemma rege_one_sub_le {q t θ : ℝ} (hq : 0 < q) (ht : 0 < t) (hθ0 : 0 < θ) (hθ2 : θ ≤ 2) :
    0 ≤ 1 - (1 + t ^ 2) ^ (-q) ∧ 1 - (1 + t ^ 2) ^ (-q) ≤ max 1 q * t ^ θ := by
  have hu : 0 < t ^ 2 := by positivity
  have h1 : (1 + t ^ 2) ^ (-q) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  refine ⟨by linarith, ?_⟩
  have h2 : 1 - q * t ^ 2 ≤ (1 + t ^ 2) ^ (-q) := by
    rw [Real.rpow_def_of_pos (by positivity), mul_comm (Real.log _) (-q)]
    have h3 := Real.add_one_le_exp (-q * Real.log (1 + t ^ 2))
    have h4 := Real.log_le_sub_one_of_pos (show 0 < 1 + t ^ 2 by positivity)
    nlinarith
  have hpos : 0 < (1 + t ^ 2) ^ (-q) := by positivity
  rcases le_or_gt t 1 with h | h
  · have h5 : t ^ 2 ≤ t ^ θ := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_ge ht h hθ2
    have h6 : 0 ≤ t ^ θ := (Real.rpow_pos_of_pos ht θ).le
    calc 1 - (1 + t ^ 2) ^ (-q) ≤ q * t ^ 2 := by linarith
      _ ≤ q * t ^ θ := by gcongr
      _ ≤ max 1 q * t ^ θ := by gcongr; exact le_max_right _ _
  · have h5 : 1 ≤ t ^ θ := Real.one_le_rpow h.le hθ0.le
    calc 1 - (1 + t ^ 2) ^ (-q) ≤ 1 := by linarith
      _ ≤ 1 * t ^ θ := by linarith
      _ ≤ max 1 q * t ^ θ := by gcongr; exact le_max_left _ _

/-- `(ε² + r²)^{-p} = r^{-2p} (1 + (ε/r)²)^{-p}`. -/
lemma rege_split {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (p : ℝ) :
    (ε ^ 2 + r ^ 2) ^ (-p) = r ^ (-(2 * p)) * (1 + (ε / r) ^ 2) ^ (-p) := by
  have h1 : ε ^ 2 + r ^ 2 = r ^ 2 * (1 + (ε / r) ^ 2) := by field_simp; ring
  rw [h1, Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  congr 1
  push_cast
  ring

lemma rege_g_sub_gE_le {s ε θ : ℝ} (hs : 0 < s) (hε : 0 < ε) (hθ0 : 0 < θ) (hθ2 : θ ≤ 2)
    {z : Euc d} (hz : z ≠ 0) :
    0 ≤ ‖z‖ ^ (-s) - rege_gE s ε z ∧
      ‖z‖ ^ (-s) - rege_gE s ε z ≤ max 1 (s / 2) * ε ^ θ * ‖z‖ ^ (-(s + θ)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  set r := ‖z‖ with hrdef
  have ht : 0 < ε / r := by positivity
  have hsplit := rege_split hε hr (s / 2)
  have h2 : -(2 * (s / 2)) = -s := by ring
  rw [h2] at hsplit
  have hE : rege_gE s ε z = r ^ (-s) * (1 + (ε / r) ^ 2) ^ (-(s / 2)) := hsplit
  obtain ⟨h3, h4⟩ := rege_one_sub_le (q := s / 2) (by positivity) ht hθ0 hθ2
  have hrs : 0 < r ^ (-s) := Real.rpow_pos_of_pos hr _
  have e1 : r ^ (-s) - rege_gE s ε z = r ^ (-s) * (1 - (1 + (ε / r) ^ 2) ^ (-(s / 2))) := by
    rw [hE]; ring
  rw [e1]
  refine ⟨mul_nonneg hrs.le h3, ?_⟩
  have e2 : (ε / r) ^ θ = ε ^ θ * r ^ (-θ) := by
    rw [Real.div_rpow hε.le hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
  calc r ^ (-s) * (1 - (1 + (ε / r) ^ 2) ^ (-(s / 2))) ≤ r ^ (-s) * (max 1 (s / 2) * (ε / r) ^ θ) :=
        mul_le_mul_of_nonneg_left h4 hrs.le
    _ = max 1 (s / 2) * ε ^ θ * (r ^ (-s) * r ^ (-θ)) := by rw [e2]; ring
    _ = max 1 (s / 2) * ε ^ θ * r ^ (-(s + θ)) := by
        rw [← Real.rpow_add hr]; congr 2; ring

lemma rege_kE_sub_kap_le {s ε θ : ℝ} (hs : 0 < s) (hε : 0 < ε) (hθ0 : 0 < θ) (hθ2 : θ ≤ 2)
    {z : Euc d} (hz : z ≠ 0) :
    ‖rege_kE s ε z - rege_kap s z‖ ≤ max 1 (s / 2 + 1) * ε ^ θ * ‖z‖ ^ (-(s + 1 + θ)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  set r := ‖z‖ with hrdef
  have ht : 0 < ε / r := by positivity
  have hsplit := rege_split hε hr (s / 2 + 1)
  have h2 : -(2 * (s / 2 + 1)) = -(s + 2) := by ring
  rw [h2] at hsplit
  obtain ⟨h3, h4⟩ := rege_one_sub_le (q := s / 2 + 1) (by positivity) ht hθ0 hθ2
  have hrs : 0 < r ^ (-(s + 2)) := Real.rpow_pos_of_pos hr _
  have e1 : rege_kE s ε z - rege_kap s z =
      (-(r ^ (-(s + 2)) * (1 - (1 + (ε / r) ^ 2) ^ (-(s / 2 + 1))))) • z := by
    unfold rege_kE rege_kap
    rw [← hrdef, hsplit, ← sub_smul]
    congr 1
    ring
  rw [e1, norm_smul, norm_neg, Real.norm_of_nonneg (mul_nonneg hrs.le h3), ← hrdef]
  have e2 : (ε / r) ^ θ = ε ^ θ * r ^ (-θ) := by
    rw [Real.div_rpow hε.le hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
  have e3 : r ^ (-(s + 2)) * r = r ^ (-(s + 1)) := by
    have := Real.rpow_add hr (-(s + 2)) 1
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  calc r ^ (-(s + 2)) * (1 - (1 + (ε / r) ^ 2) ^ (-(s / 2 + 1))) * r
      = r ^ (-(s + 1)) * (1 - (1 + (ε / r) ^ 2) ^ (-(s / 2 + 1))) := by rw [← e3]; ring
    _ ≤ r ^ (-(s + 1)) * (max 1 (s / 2 + 1) * (ε / r) ^ θ) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_pos_of_pos hr _).le
    _ = max 1 (s / 2 + 1) * ε ^ θ * (r ^ (-(s + 1)) * r ^ (-θ)) := by rw [e2]; ring
    _ = max 1 (s / 2 + 1) * ε ^ θ * r ^ (-(s + 1 + θ)) := by
        rw [← Real.rpow_add hr]; congr 2; ring


/-! ### Properties of the kernels -/

lemma rege_kap_norm_le (s : ℝ) (z : Euc d) : ‖rege_kap s z‖ ≤ ‖z‖ ^ (-(s + 1)) := by
  unfold rege_kap
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  by_cases hz : z = 0
  · subst hz; rw [norm_zero, mul_zero]; exact Real.rpow_nonneg le_rfl _
  · have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
    have := Real.rpow_add hr (-(s + 2)) 1
    rw [Real.rpow_one] at this
    rw [← this]
    apply le_of_eq; congr 1; ring

lemma rege_kap_measurable (s : ℝ) : Measurable (rege_kap s : Euc d → Euc d) := by
  unfold rege_kap
  exact (measurable_norm.pow_const _).smul measurable_id

lemma rege_gE_continuous {s ε : ℝ} (hε : 0 < ε) : Continuous (rege_gE s ε : Euc d → ℝ) := by
  unfold rege_gE
  exact (continuous_const.add (continuous_norm.pow 2)).rpow_const fun z =>
    Or.inl (show ε ^ 2 + ‖z‖ ^ 2 ≠ 0 by positivity)

lemma rege_kE_continuous {s ε : ℝ} (hε : 0 < ε) : Continuous (rege_kE s ε : Euc d → Euc d) := by
  unfold rege_kE
  exact Continuous.smul ((continuous_const.add (continuous_norm.pow 2)).rpow_const fun z =>
    Or.inl (show ε ^ 2 + ‖z‖ ^ 2 ≠ 0 by positivity)) continuous_id

lemma rege_gE_le {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (z : Euc d) :
    |rege_gE s ε z| ≤ ε ^ (-s) := by
  unfold rege_gE
  have hA : 0 < ε ^ 2 + ‖z‖ ^ 2 := by positivity
  rw [abs_of_nonneg (Real.rpow_nonneg hA.le _)]
  have h1 : (ε ^ 2) ^ (-(s / 2)) ≤ ε ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    apply le_of_eq; congr 1; push_cast; ring
  refine le_trans ?_ h1
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖z‖])
    (by linarith)

lemma rege_kE_le {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (z : Euc d) :
    ‖rege_kE s ε z‖ ≤ ε ^ (-(s + 1)) := by
  unfold rege_kE
  have hA : 0 < ε ^ 2 + ‖z‖ ^ 2 := by positivity
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hA.le _)]
  set A := ε ^ 2 + ‖z‖ ^ 2 with hAdef
  have hr : ‖z‖ ≤ A ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have h1 : A ^ (-(s / 2 + 1)) * A ^ (1 / 2 : ℝ) = A ^ (-((s + 1) / 2)) := by
    rw [← Real.rpow_add hA]; congr 1; ring
  have h2 : A ^ (-((s + 1) / 2)) ≤ ε ^ (-(s + 1)) := by
    have h3 : (ε ^ 2) ^ (-((s + 1) / 2)) = ε ^ (-(s + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      congr 1; push_cast; ring
    rw [← h3]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖z‖])
      (by linarith)
  calc A ^ (-(s / 2 + 1)) * ‖z‖ ≤ A ^ (-(s / 2 + 1)) * A ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hA.le _)
    _ ≤ _ := by rw [h1]; exact h2

/-- The linear map `v ↦ -s ⟪v, ·⟫` (the gradient of `‖z‖^{-s}` is `L (κ_s z)`). -/
def rege_L (s : ℝ) : Euc d →L[ℝ] Euc d →L[ℝ] ℝ :=
  (-s) • (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)

lemma rege_L_apply (s : ℝ) (v : Euc d) : rege_L s v = (-s) • innerSL ℝ v := by
  unfold rege_L
  rw [smul_apply]

lemma rege_L_norm {s : ℝ} (hs : 0 ≤ s) (v : Euc d) : ‖rege_L s v‖ = s * ‖v‖ := by
  rw [rege_L_apply, norm_smul, innerSL_apply_norm, norm_neg, Real.norm_of_nonneg hs]

lemma rege_gE_hasFDerivAt {s ε : ℝ} (hε : 0 < ε) (y x : Euc d) :
    HasFDerivAt (fun x : Euc d => rege_gE s ε (x - y)) (rege_L s (rege_kE s ε (x - y))) x := by
  have h2 : HasFDerivAt (fun x : Euc d => x - y) (ContinuousLinearMap.id ℝ (Euc d)) x :=
    (hasFDerivAt_id x).sub_const y
  have h3 := (h2.norm_sq).const_add (ε ^ 2)
  have hne : ε ^ 2 + ‖x - y‖ ^ 2 ≠ 0 := by positivity
  have h4 := (Real.hasDerivAt_rpow_const (p := -(s / 2)) (Or.inl hne)).comp_hasFDerivAt x h3
  refine h4.congr_fderiv ?_
  ext w
  have e : -(s / 2) - 1 = -(s / 2 + 1) := by ring
  simp [rege_kE, e, rege_L_apply]
  ring


/-! ### Integrability and the regularised potential -/

lemma rege_gE_F_integrable {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) {F : Euc d → ℝ}
    (hm : AEStronglyMeasurable F volume) (hF : lreg_RDec F) (x : Euc d) :
    Integrable (fun y => rege_gE s ε (x - y) * F y) := by
  have hi0 := lreg_norm_integrable hm hF 0
  simp only [pow_zero, one_mul] at hi0
  refine (hi0.mul_const (ε ^ (-s))).mono' ?_ (ae_of_all _ fun y => ?_)
  · exact ((rege_gE_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hm
  · rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (rege_gE_le hs hε _) (norm_nonneg _) |>.trans_eq (mul_comm _ _)

lemma rege_kE_F_integrable {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) {F : Euc d → ℝ}
    (hm : AEStronglyMeasurable F volume) (hF : lreg_RDec F) (x : Euc d) :
    Integrable (fun y => F y • rege_kE s ε (x - y)) := by
  have hi0 := lreg_norm_integrable hm hF 0
  simp only [pow_zero, one_mul] at hi0
  refine (hi0.mul_const (ε ^ (-(s + 1)))).mono' ?_ (ae_of_all _ fun y => ?_)
  · exact hm.smul ((rege_kE_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (rege_kE_le hs hε _) (norm_nonneg _)

lemma rege_UE_hasFDerivAt {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) {F : Euc d → ℝ}
    (hm : AEStronglyMeasurable F volume) (hF : lreg_RDec F) (x₀ : Euc d) :
    HasFDerivAt (fun x : Euc d => ∫ y, rege_gE s ε (x - y) * F y)
      (rege_L s (∫ y, F y • rege_kE s ε (x₀ - y))) x₀ := by
  have hi0 := lreg_norm_integrable hm hF 0
  simp only [pow_zero, one_mul] at hi0
  have hint := rege_kE_F_integrable hs hε hm hF x₀
  have hcomm : (∫ y, F y • rege_L s (rege_kE s ε (x₀ - y))) =
      rege_L s (∫ y, F y • rege_kE s ε (x₀ - y)) := by
    have := ContinuousLinearMap.integral_comp_comm (rege_L s) hint
    simpa [map_smul] using this
  rw [← hcomm]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (F := fun x y => rege_gE s ε (x - y) * F y)
    (F' := fun x y => F y • rege_L s (rege_kE s ε (x - y)))
    (bound := fun y => ‖F y‖ * (s * ε ^ (-(s + 1)))) Filter.univ_mem ?_ ?_ ?_ ?_ (hi0.mul_const _) ?_
  · exact Eventually.of_forall fun x =>
      ((rege_gE_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hm
  · exact rege_gE_F_integrable hs hε hm hF x₀
  · exact hm.smul ((rege_L s).continuous.comp
      ((rege_kE_continuous hε).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine ae_of_all _ fun y x _ => ?_
    rw [norm_smul, rege_L_norm hs.le]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rege_kE_le hs hε _) hs.le)
      (norm_nonneg _)
  · exact ae_of_all _ fun y x _ => (rege_gE_hasFDerivAt hε y x).mul_const (F y)

lemma rege_U_est {s θ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hθ0 : 0 < θ) (hθ2 : θ ≤ 2)
    (hθd : s + θ < d) {F : Euc d → ℝ}
    (hm : AEStronglyMeasurable F volume) (hF : lreg_RDec F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, ‖F y‖ ≤ C * lreg_phi d y) {ε : ℝ} (hε : 0 < ε) (x : Euc d) :
    Integrable (fun y => ‖x - y‖ ^ (-s) * F y) ∧
      ‖rege_U s F x - ∫ y, rege_gE s ε (x - y) * F y‖ ≤
        ε ^ θ * (max 1 (s / 2) * (C * lreg_A d (s + θ))) := by
  have hσ : s < d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    linarith
  obtain ⟨hK, -⟩ := lreg_K_dom_y hd1 hσ hs.le hC hm hb x
  obtain ⟨hK', hKi'⟩ := lreg_K_dom_y hd1 hθd (by linarith) hC hm hb x
  have hmeasg : Measurable (fun y : Euc d => ‖x - y‖ ^ (-s)) :=
    (measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _
  have hU : Integrable (fun y => ‖x - y‖ ^ (-s) * F y) := by
    refine hK.mono' (hmeasg.aestronglyMeasurable.mul hm) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hE := rege_gE_F_integrable hs hε hm hF x
  have hbd : ∀ᵐ y : Euc d, ‖(‖x - y‖ ^ (-s) - rege_gE s ε (x - y)) * F y‖ ≤
      (max 1 (s / 2) * ε ^ θ) * (‖x - y‖ ^ (-(s + θ)) * ‖F y‖) := by
    filter_upwards [lreg_ae_ne hd1 x] with y hy
    obtain ⟨h0, h1⟩ := rege_g_sub_gE_le hs hε hθ0 hθ2 hy
    rw [norm_mul, Real.norm_of_nonneg h0]
    calc _ ≤ (max 1 (s / 2) * ε ^ θ * ‖x - y‖ ^ (-(s + θ))) * ‖F y‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = _ := by ring
  have hDm : AEStronglyMeasurable (fun y => (‖x - y‖ ^ (-s) - rege_gE s ε (x - y)) * F y) volume :=
    (hmeasg.sub ((rege_gE_continuous hε).measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable.mul hm
  have hD : Integrable (fun y => (‖x - y‖ ^ (-s) - rege_gE s ε (x - y)) * F y) :=
    (hK'.const_mul _).mono' hDm hbd
  refine ⟨hU, ?_⟩
  have : rege_U s F x - ∫ y, rege_gE s ε (x - y) * F y =
      ∫ y, (‖x - y‖ ^ (-s) - rege_gE s ε (x - y)) * F y := by
    unfold rege_U
    rw [← integral_sub hU hE]
    congr 1; ext y; ring
  rw [this]
  calc _ ≤ ∫ y, (max 1 (s / 2) * ε ^ θ) * (‖x - y‖ ^ (-(s + θ)) * ‖F y‖) :=
        norm_integral_le_of_norm_le (hK'.const_mul _) hbd
    _ = (max 1 (s / 2) * ε ^ θ) * ∫ y, ‖x - y‖ ^ (-(s + θ)) * ‖F y‖ := integral_const_mul _ _
    _ ≤ (max 1 (s / 2) * ε ^ θ) * (C * lreg_A d (s + θ)) := by
        gcongr
    _ = _ := by ring

lemma rege_W_est {s θ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hθ0 : 0 < θ) (hθ2 : θ ≤ 2)
    (hθd : s + 1 + θ < d) {F : Euc d → ℝ}
    (hm : AEStronglyMeasurable F volume) (hF : lreg_RDec F) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, ‖F y‖ ≤ C * lreg_phi d y) {ε : ℝ} (hε : 0 < ε) (x : Euc d) :
    Integrable (fun y => F y • rege_kap s (x - y)) ∧ ‖rege_W s F x‖ ≤ C * lreg_A d (s + 1) ∧
      ‖rege_W s F x - ∫ y, F y • rege_kE s ε (x - y)‖ ≤
        ε ^ θ * (max 1 (s / 2 + 1) * (C * lreg_A d (s + 1 + θ))) := by
  have hσ : s + 1 < d := by linarith
  obtain ⟨hK, hKi⟩ := lreg_K_dom_y hd1 hσ (by linarith) hC hm hb x
  obtain ⟨hK', hKi'⟩ := lreg_K_dom_y hd1 hθd (by linarith) hC hm hb x
  have hmeas : AEStronglyMeasurable (fun y => F y • rege_kap s (x - y)) volume :=
    hm.smul ((rege_kap_measurable s).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hbd1 : ∀ y : Euc d, ‖F y • rege_kap s (x - y)‖ ≤ ‖x - y‖ ^ (-(s + 1)) * ‖F y‖ := fun y => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (rege_kap_norm_le s _) (norm_nonneg _)
  have hI : Integrable (fun y => F y • rege_kap s (x - y)) :=
    hK.mono' hmeas (ae_of_all _ hbd1)
  refine ⟨hI, ?_, ?_⟩
  · calc ‖rege_W s F x‖ ≤ ∫ y, ‖x - y‖ ^ (-(s + 1)) * ‖F y‖ :=
          norm_integral_le_of_norm_le hK (ae_of_all _ hbd1)
      _ ≤ C * lreg_A d (s + 1) := hKi
  · have hE := rege_kE_F_integrable hs hε hm hF x
    have hbd : ∀ᵐ y : Euc d, ‖F y • rege_kap s (x - y) - F y • rege_kE s ε (x - y)‖ ≤
        (max 1 (s / 2 + 1) * ε ^ θ) * (‖x - y‖ ^ (-(s + 1 + θ)) * ‖F y‖) := by
      filter_upwards [lreg_ae_ne hd1 x] with y hy
      rw [← smul_sub, norm_smul, norm_sub_rev]
      calc ‖F y‖ * ‖rege_kE s ε (x - y) - rege_kap s (x - y)‖
          ≤ ‖F y‖ * (max 1 (s / 2 + 1) * ε ^ θ * ‖x - y‖ ^ (-(s + 1 + θ))) :=
            mul_le_mul_of_nonneg_left (rege_kE_sub_kap_le hs hε hθ0 hθ2 hy) (norm_nonneg _)
        _ = _ := by ring
    have : rege_W s F x - ∫ y, F y • rege_kE s ε (x - y) =
        ∫ y, (F y • rege_kap s (x - y) - F y • rege_kE s ε (x - y)) := by
      unfold rege_W
      rw [integral_sub hI hE]
    rw [this]
    calc _ ≤ ∫ y, (max 1 (s / 2 + 1) * ε ^ θ) * (‖x - y‖ ^ (-(s + 1 + θ)) * ‖F y‖) :=
          norm_integral_le_of_norm_le (hK'.const_mul _) hbd
      _ = (max 1 (s / 2 + 1) * ε ^ θ) * ∫ y, ‖x - y‖ ^ (-(s + 1 + θ)) * ‖F y‖ :=
          integral_const_mul _ _
      _ ≤ (max 1 (s / 2 + 1) * ε ^ θ) * (C * lreg_A d (s + 1 + θ)) := by
          gcongr
      _ = _ := by ring

/-- **Potential of a rapidly decaying measurable density** (`s > 0`, `s + 1 + θ < d`): `U = ∫ ‖x-y‖^{-s} F y dy`
is `C¹` with `∇U = -s ∫ F y κ_s(x - y) dy` (continuous, and bounded by `C A` if `‖F‖ ≤ C φ`). -/
theorem rege_potential {s θ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθd : s + 1 + θ < d) {F : Euc d → ℝ} (hm : AEStronglyMeasurable F volume) (hF : lreg_RDec F) :
    Continuous (rege_W s F) ∧ (∀ x, HasFDerivAt (rege_U s F) (rege_L s (rege_W s F x)) x) ∧
      ∀ C : ℝ, 0 ≤ C → (∀ y, ‖F y‖ ≤ C * lreg_phi d y) → ∀ x,
        ‖rege_W s F x‖ ≤ C * lreg_A d (s + 1) := by
  obtain ⟨C0, hC0, h0⟩ := lreg_bound_of_rdec hF 0
  have hb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using h0 y
  have hi0 := lreg_norm_integrable hm hF 0
  simp only [pow_zero, one_mul] at hi0
  have hθ2 : θ ≤ 2 := by linarith
  have hθd' : s + θ < d := by linarith
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [hεdef]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεθ : Tendsto (fun n => (ε n) ^ θ) atTop (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ0.le)).tendsto.comp hε0
    simpa [Function.comp_def, Real.zero_rpow hθ0.ne'] using h
  have hc1 : Tendsto (fun n => (ε n) ^ θ * (max 1 (s / 2) * (C0 * lreg_A d (s + θ)))) atTop (𝓝 0) := by
    simpa using hεθ.mul_const (max 1 (s / 2) * (C0 * lreg_A d (s + θ)))
  have hc2 : Tendsto (fun n => (ε n) ^ θ * (max 1 (s / 2 + 1) * (C0 * lreg_A d (s + 1 + θ)))) atTop
      (𝓝 0) := by
    simpa using hεθ.mul_const (max 1 (s / 2 + 1) * (C0 * lreg_A d (s + 1 + θ)))
  have hTUW : TendstoUniformly (fun n x => ∫ y, F y • rege_kE s (ε n) (x - y)) (rege_W s F) atTop :=
    lreg_tu hc2 fun n x => by
      rw [norm_sub_rev]; exact (rege_W_est hd1 hs hθ0 hθ2 hθd hm hF hC0 hb (hεpos n) x).2.2
  have hcontE : ∀ n, Continuous (fun x => ∫ y, F y • rege_kE s (ε n) (x - y)) := by
    intro n
    refine continuous_of_dominated (bound := fun y => ‖F y‖ * ε n ^ (-(s + 1))) (fun x => ?_)
      (fun x => ae_of_all _ fun y => ?_) (hi0.mul_const _) (ae_of_all _ fun y => ?_)
    · exact hm.smul ((rege_kE_continuous (hεpos n)).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (rege_kE_le hs (hεpos n) _) (norm_nonneg _)
    · exact (continuous_const : Continuous fun _ : Euc d => F y).smul ((rege_kE_continuous (hεpos n)).comp
        ((continuous_id (X := Euc d)).sub continuous_const))
  refine ⟨hTUW.continuous (Eventually.of_forall hcontE).frequently, fun x => ?_,
    fun C hC hCb x => (rege_W_est hd1 hs hθ0 hθ2 hθd hm hF hC hCb (hεpos 0) x).2.1⟩
  refine hasFDerivAt_of_tendstoUniformly (l := atTop)
    (f := fun n x => ∫ y, rege_gE s (ε n) (x - y) * F y)
    (f' := fun n x => rege_L s (∫ y, F y • rege_kE s (ε n) (x - y)))
    (g' := fun x => rege_L s (rege_W s F x)) ?_ (fun n x => rege_UE_hasFDerivAt hs (hεpos n) hm hF x) ?_ x
  · refine lreg_tu (c := fun n => s * ((ε n) ^ θ * (max 1 (s / 2 + 1) * (C0 * lreg_A d (s + 1 + θ)))))
      (by simpa using hc2.const_mul s) fun n x => ?_
    rw [← map_sub, rege_L_norm hs.le, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left
      (rege_W_est hd1 hs hθ0 hθ2 hθd hm hF hC0 hb (hεpos n) x).2.2 hs.le
  · intro x
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hc1)
    rw [norm_sub_rev]
    exact (rege_U_est hd1 hs hθ0 hθ2 hθd' hm hF hC0 hb (hεpos n) x).2

end HRS.MS.Thm

end
