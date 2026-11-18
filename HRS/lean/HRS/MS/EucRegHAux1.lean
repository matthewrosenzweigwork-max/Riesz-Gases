import HRS.MS.EucRegAux3

/-!
# C-REG-h (part 1): the localised Riesz kernel and power integrals

(`0 < s < d`.)  Namespace `HRS.MS.Thm`, helper prefix `regh_`.  The Riesz kernel `g(z) = ‖z‖^{-s}` is split as
`g = g₁ + k` with the smooth bounded `g₁ = (1 + ‖z‖²)^{-s/2}` (`rege_gE s 1`) and the integrable localised kernel
`k = g - g₁`, which obeys `0 ≤ k(z) ≤ c ‖z‖^{-σ}` and `‖∇k(z)‖ ≤ c ‖z‖^{-σ-1}` for every `σ ∈ [s, s+2]`
(near `0` because `g₁ ≤ 1`, near `∞` by the `ε²`-expansion of `rege_g_sub_gE_le`).
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff Pointwise

noncomputable section

namespace HRS.MS.Thm

open HRS HRS.Whole HRS.MS.LogReg

variable {d : ℕ}

/-- The localised kernel `k = ‖z‖^{-s} - (1 + ‖z‖²)^{-s/2}`. -/
def regh_k (s : ℝ) (z : Euc d) : ℝ := ‖z‖ ^ (-s) - rege_gE s 1 z

lemma regh_gE_pos (s : ℝ) (z : Euc d) : 0 < rege_gE s 1 z := by
  unfold rege_gE
  exact Real.rpow_pos_of_pos (by positivity) _

lemma regh_k_measurable (s : ℝ) : Measurable (regh_k s : Euc d → ℝ) := by
  unfold regh_k
  exact (measurable_norm.pow_const _).sub ((rege_gE_continuous (s := s) one_pos).measurable)

lemma regh_k_bound {s σ : ℝ} (hs : 0 < s) (hσs : s ≤ σ) (hσ2 : σ ≤ s + 2) {z : Euc d} (hz : z ≠ 0) :
    0 ≤ regh_k s z ∧ regh_k s z ≤ max 1 (s / 2) * ‖z‖ ^ (-σ) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨h0, h1⟩ := rege_g_sub_gE_le (d := d) (s := s) (ε := 1) (θ := 2) hs one_pos two_pos le_rfl hz
  refine ⟨h0, ?_⟩
  have hc : (1 : ℝ) ≤ max 1 (s / 2) := le_max_left _ _
  rcases le_or_gt ‖z‖ 1 with h | h
  · have : regh_k s z ≤ ‖z‖ ^ (-s) := by
      unfold regh_k; linarith [regh_gE_pos s z]
    have h2 : ‖z‖ ^ (-s) ≤ ‖z‖ ^ (-σ) :=
      Real.rpow_le_rpow_of_exponent_ge hr h (by linarith)
    have h3 : 0 ≤ ‖z‖ ^ (-σ) := Real.rpow_nonneg hr.le _
    nlinarith
  · have h2 : ‖z‖ ^ (-(s + 2)) ≤ ‖z‖ ^ (-σ) :=
      Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
    have h3 : (1 : ℝ) ^ (2 : ℝ) = 1 := Real.one_rpow _
    unfold regh_k
    calc ‖z‖ ^ (-s) - rege_gE s 1 z ≤ max 1 (s / 2) * 1 ^ (2 : ℝ) * ‖z‖ ^ (-(s + 2)) := h1
      _ = max 1 (s / 2) * ‖z‖ ^ (-(s + 2)) := by rw [h3]; ring
      _ ≤ _ := by gcongr

lemma regh_kE_norm_le {s : ℝ} (ε : ℝ) (hs : 0 < s) (hε : 0 < ε) {z : Euc d} (hz : z ≠ 0) :
    ‖rege_kE s ε z‖ ≤ ‖z‖ ^ (-(s + 1)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold rege_kE
  have hA : 0 < ε ^ 2 + ‖z‖ ^ 2 := by positivity
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hA.le _)]
  have h1 : (ε ^ 2 + ‖z‖ ^ 2) ^ (-(s / 2 + 1)) ≤ (‖z‖ ^ 2) ^ (-(s / 2 + 1)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by linarith)
  have h2 : (‖z‖ ^ 2) ^ (-(s / 2 + 1)) = ‖z‖ ^ (-(s + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  have h3 : ‖z‖ ^ (-(s + 2)) * ‖z‖ = ‖z‖ ^ (-(s + 1)) := by
    have := Real.rpow_add hr (-(s + 2)) 1
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  calc _ ≤ ‖z‖ ^ (-(s + 2)) * ‖z‖ := by rw [← h2]; gcongr
    _ = _ := h3

lemma regh_g_hasFDerivAt {s : ℝ} {z : Euc d} (hz : z ≠ 0) :
    HasFDerivAt (fun x : Euc d => ‖x‖ ^ (-s)) (rege_L s (rege_kap s z)) z := by
  have hne : ‖z‖ ^ 2 ≠ 0 := by have := norm_pos_iff.2 hz; positivity
  have h3 := (hasFDerivAt_id z).norm_sq
  have h4 := (Real.hasDerivAt_rpow_const (p := -(s / 2)) (Or.inl hne)).comp_hasFDerivAt z h3
  have h5 : (fun x : Euc d => ‖x‖ ^ (-s)) = (fun x : Euc d => (‖x‖ ^ 2) ^ (-(s / 2))) := by
    funext x
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]; congr 1; push_cast; ring
  rw [h5]
  refine h4.congr_fderiv ?_
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  ext w
  have e : (‖z‖ ^ 2) ^ (-(s / 2) - 1) = ‖z‖ ^ (-(s + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  simp [rege_L_apply, rege_kap, e]
  ring

lemma regh_k_hasFDerivAt {s : ℝ} {z : Euc d} (hz : z ≠ 0) :
    HasFDerivAt (regh_k s) (rege_L s (rege_kap s z - rege_kE s 1 z)) z := by
  have h1 := regh_g_hasFDerivAt (s := s) hz
  have h2 := rege_gE_hasFDerivAt (s := s) (ε := 1) one_pos 0 z
  simp only [sub_zero] at h2
  have := h1.sub h2
  unfold regh_k
  convert this using 1
  rw [map_sub]

lemma regh_k_grad_bound {s σ : ℝ} (hs : 0 < s) (hσs : s ≤ σ) (hσ2 : σ ≤ s + 2) {z : Euc d} (hz : z ≠ 0) :
    ‖rege_L s (rege_kap s z - rege_kE s 1 z)‖ ≤ (s * max 2 (max 1 (s / 2 + 1))) * ‖z‖ ^ (-(σ + 1)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [rege_L_norm hs.le]
  have hc : (2 : ℝ) ≤ max 2 (max 1 (s / 2 + 1)) := le_max_left _ _
  have hc1 : max 1 (s / 2 + 1) ≤ max 2 (max 1 (s / 2 + 1)) := le_max_right _ _
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hs.le
  rcases le_or_gt ‖z‖ 1 with h | h
  · have h1 : ‖rege_kap s z - rege_kE s 1 z‖ ≤ ‖z‖ ^ (-(s + 1)) + ‖z‖ ^ (-(s + 1)) :=
      (norm_sub_le _ _).trans (add_le_add (rege_kap_norm_le s z) (regh_kE_norm_le 1 hs one_pos hz))
    have h2 : ‖z‖ ^ (-(s + 1)) ≤ ‖z‖ ^ (-(σ + 1)) :=
      Real.rpow_le_rpow_of_exponent_ge hr h (by linarith)
    have h3 : 0 ≤ ‖z‖ ^ (-(σ + 1)) := Real.rpow_nonneg hr.le _
    nlinarith
  · have h1 := rege_kE_sub_kap_le (d := d) (s := s) (ε := 1) (θ := 2) hs one_pos two_pos le_rfl hz
    rw [norm_sub_rev] at h1
    have h3 : (1 : ℝ) ^ (2 : ℝ) = 1 := Real.one_rpow _
    have h2 : ‖z‖ ^ (-(s + 1 + 2)) ≤ ‖z‖ ^ (-(σ + 1)) :=
      Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
    have h4 : 0 ≤ ‖z‖ ^ (-(σ + 1)) := Real.rpow_nonneg hr.le _
    calc _ ≤ max 1 (s / 2 + 1) * 1 ^ (2 : ℝ) * ‖z‖ ^ (-(s + 1 + 2)) := h1
      _ = max 1 (s / 2 + 1) * ‖z‖ ^ (-(s + 1 + 2)) := by rw [h3]; ring
      _ ≤ max 2 (max 1 (s / 2 + 1)) * ‖z‖ ^ (-(σ + 1)) := by gcongr

/-! ### Power integrals -/

lemma regh_ball_int {q r : ℝ} (hd1 : 1 ≤ d) (hq : q < d) (_hr : 0 < r) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-q)) (ball 0 r) := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := q) (r := r) (by simpa using hd1)
    (by simpa using hq) ?_ ?_
  · exact ae_of_all _ fun x => by
      simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

lemma regh_ball_scale {q r : ℝ} (hr : 0 < r) :
    ∫ z in ball (0 : Euc d) r, ‖z‖ ^ (-q) =
      r ^ ((d : ℝ) - q) * ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-q) := by
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Euc d))
    (fun z : Euc d => ‖z‖ ^ (-q)) (ball (0 : Euc d) 1) hr
  rw [_root_.smul_ball hr.ne', smul_zero, Real.norm_of_nonneg hr.le, mul_one] at h
  have h1 : ∀ x : Euc d, ‖r • x‖ ^ (-q) = r ^ (-q) * ‖x‖ ^ (-q) := fun x => by
    rw [norm_smul, Real.norm_of_nonneg hr.le, Real.mul_rpow hr.le (norm_nonneg x)]
  simp only [h1, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at h
  rw [integral_const_mul] at h
  have hrd : (0 : ℝ) < r ^ d := pow_pos hr d
  have h2 : ∫ z in ball (0 : Euc d) r, ‖z‖ ^ (-q) = r ^ d * (r ^ (-q) * ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-q)) := by
    rw [h]; field_simp
  rw [h2, Real.rpow_sub hr, Real.rpow_natCast, div_eq_mul_inv, Real.rpow_neg hr.le]
  field_simp

lemma regh_tail_int {p r : ℝ} (hp : (d : ℝ) < p) (hr : 0 < r) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-p)) (ball 0 r)ᶜ := by
  have hI := (integrable_one_add_norm (E := Euc d) (μ := volume) (r := p) (by simpa using hp)).const_mul
    ((1 + 1 / r) ^ p)
  refine hI.integrableOn.mono' ?_ ?_
  · exact (measurable_norm.pow_const _).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_ball.compl).2 (ae_of_all _ fun z hz => ?_)
    have hz' : r ≤ ‖z‖ := by simpa using hz
    have hzp : 0 < ‖z‖ := lt_of_lt_of_le hr hz'
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), Real.rpow_neg hzp.le,
      Real.rpow_neg (by positivity)]
    have h1 : 1 + ‖z‖ ≤ (1 + 1 / r) * ‖z‖ := by
      have h2 : (1 + 1 / r) * ‖z‖ = ‖z‖ + ‖z‖ / r := by field_simp
      have h3 : 1 ≤ ‖z‖ / r := by rw [le_div_iff₀ hr]; linarith
      rw [h2]; linarith
    have hp0 : 0 ≤ p := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
    have h3 : (1 + ‖z‖) ^ p ≤ (1 + 1 / r) ^ p * ‖z‖ ^ p := by
      rw [← Real.mul_rpow (by positivity) hzp.le]
      exact Real.rpow_le_rpow (by positivity) h1 hp0
    have h4 : 0 < (1 + ‖z‖) ^ p := Real.rpow_pos_of_pos (by positivity) _
    have h5 : 0 < ‖z‖ ^ p := Real.rpow_pos_of_pos hzp _
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ h5 h4]
    linarith

lemma regh_smul_compl {r : ℝ} (hr : 0 < r) : r • (ball (0 : Euc d) 1)ᶜ = (ball (0 : Euc d) r)ᶜ := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  simp only [Set.mem_compl_iff, mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr.le, not_lt]
  rw [inv_mul_eq_div, le_div_iff₀ hr]
  constructor <;> intro h <;> linarith

lemma regh_tail_scale {p r : ℝ} (hr : 0 < r) :
    ∫ z in (ball (0 : Euc d) r)ᶜ, ‖z‖ ^ (-p) =
      r ^ ((d : ℝ) - p) * ∫ z in (ball (0 : Euc d) 1)ᶜ, ‖z‖ ^ (-p) := by
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Euc d))
    (fun z : Euc d => ‖z‖ ^ (-p)) (ball (0 : Euc d) 1)ᶜ hr
  rw [regh_smul_compl hr] at h
  have h1 : ∀ x : Euc d, ‖r • x‖ ^ (-p) = r ^ (-p) * ‖x‖ ^ (-p) := fun x => by
    rw [norm_smul, Real.norm_of_nonneg hr.le, Real.mul_rpow hr.le (norm_nonneg x)]
  simp only [h1, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at h
  rw [integral_const_mul] at h
  have hrd : (0 : ℝ) < r ^ d := pow_pos hr d
  have h2 : ∫ z in (ball (0 : Euc d) r)ᶜ, ‖z‖ ^ (-p) =
      r ^ d * (r ^ (-p) * ∫ z in (ball (0 : Euc d) 1)ᶜ, ‖z‖ ^ (-p)) := by
    rw [h]; field_simp
  rw [h2, Real.rpow_sub hr, Real.rpow_natCast, div_eq_mul_inv, Real.rpow_neg hr.le]
  field_simp

lemma regh_ae_ne (hd1 : 1 ≤ d) : ∀ᵐ z : Euc d, z ≠ 0 := by
  filter_upwards [lreg_ae_ne hd1 (0 : Euc d)] with y hy h
  exact hy (by simp [h])

lemma regh_k_integrable {s : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2) :
    Integrable (regh_k s : Euc d → ℝ) := by
  have hm : AEStronglyMeasurable (regh_k s : Euc d → ℝ) volume := (regh_k_measurable s).aestronglyMeasurable
  have h1 : IntegrableOn (regh_k s : Euc d → ℝ) (ball 0 1) := by
    refine ((regh_ball_int (q := s) hd1 hsd one_pos).const_mul (max 1 (s / 2))).mono' hm.restrict ?_
    refine (ae_restrict_iff' measurableSet_ball).2 ?_
    filter_upwards [regh_ae_ne hd1] with z hz _
    obtain ⟨h0, h2⟩ := regh_k_bound (σ := s) hs le_rfl (by linarith) hz
    rw [Real.norm_of_nonneg h0]
    exact h2
  have h2 : IntegrableOn (regh_k s : Euc d → ℝ) (ball 0 1)ᶜ := by
    refine ((regh_tail_int (p := s + 2) (by linarith) one_pos).const_mul (max 1 (s / 2))).mono'
      hm.restrict ?_
    refine (ae_restrict_iff' measurableSet_ball.compl).2 ?_
    filter_upwards [regh_ae_ne hd1] with z hz _
    obtain ⟨h0, h2⟩ := regh_k_bound (σ := s + 2) hs (by linarith) le_rfl hz
    rw [Real.norm_of_nonneg h0]
    exact h2
  have := h1.union h2
  rwa [Set.union_compl_self, integrableOn_univ] at this

/-! ### The convolution operator -/

/-- `T F (x) = ∫ ‖z‖^{-s} F(x - z) dz`. -/
def regh_T (s : ℝ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Euc d → E) (x : Euc d) : E :=
  ∫ z, ‖z‖ ^ (-s) • F (x - z)

/-- Localised part `∫ k(z) F(x - z) dz`. -/
def regh_Tk (s : ℝ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Euc d → E) (x : Euc d) : E :=
  ∫ z, regh_k s z • F (x - z)

/-- Smooth part `∫ (1+‖z‖²)^{-s/2} F(x - z) dz`. -/
def regh_T1 (s : ℝ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Euc d → E) (x : Euc d) : E :=
  ∫ z, rege_gE s 1 z • F (x - z)

section TOp

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma regh_T_integrable {s : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) {F : Euc d → E}
    (hm : AEStronglyMeasurable F volume) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, ‖F y‖ ≤ C * lreg_phi d y)
    (x : Euc d) :
    Integrable (fun z => ‖z‖ ^ (-s) • F (x - z)) ∧
      ‖regh_T s F x‖ ≤ C * lreg_A d s := by
  obtain ⟨hI, hJ⟩ := lreg_K_dom hd1 hsd hs.le hC hm hb x
  have hmeas : AEStronglyMeasurable (fun z : Euc d => ‖z‖ ^ (-s) • F (x - z)) volume :=
    (measurable_norm.pow_const _).aestronglyMeasurable.smul
      (hm.comp_measurePreserving (volume.measurePreserving_sub_left x))
  have hpt : ∀ z : Euc d, ‖‖z‖ ^ (-s) • F (x - z)‖ = ‖z‖ ^ (-s) * ‖F (x - z)‖ := fun z => by
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  refine ⟨hI.mono' hmeas (ae_of_all _ fun z => (hpt z).le), ?_⟩
  calc ‖regh_T s F x‖ ≤ ∫ z, ‖z‖ ^ (-s) * ‖F (x - z)‖ :=
        norm_integral_le_of_norm_le hI (ae_of_all _ fun z => (hpt z).le)
    _ ≤ C * lreg_A d s := hJ

lemma regh_Tk_integrable {s : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    {F : Euc d → E} (hm : AEStronglyMeasurable F volume) {B : ℝ} (hB : ∀ y, ‖F y‖ ≤ B) (x : Euc d) :
    Integrable (fun z => regh_k s z • F (x - z)) := by
  have hk := regh_k_integrable hd1 hs hsd hs2
  have hmeas : AEStronglyMeasurable (fun z : Euc d => regh_k s z • F (x - z)) volume :=
    (regh_k_measurable s).aestronglyMeasurable.smul
      (hm.comp_measurePreserving (volume.measurePreserving_sub_left x))
  refine (hk.norm.mul_const B).mono' hmeas (ae_of_all _ fun z => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

lemma regh_T1_integrable {s : ℝ} (hs : 0 < s) {F : Euc d → E}
    (hm : AEStronglyMeasurable F volume) (hI : Integrable F) (x : Euc d) :
    Integrable (fun z => rege_gE s 1 z • F (x - z)) := by
  have hmeas : AEStronglyMeasurable (fun z : Euc d => rege_gE s 1 z • F (x - z)) volume :=
    (rege_gE_continuous (s := s) one_pos).aestronglyMeasurable.smul
      (hm.comp_measurePreserving (volume.measurePreserving_sub_left x))
  refine (hI.norm.comp_sub_left x).mono' hmeas (ae_of_all _ fun z => ?_)
  rw [norm_smul]
  have h1 : ‖rege_gE s 1 z‖ ≤ 1 := by
    have := rege_gE_le (d := d) (s := s) (ε := 1) hs one_pos z
    simpa using this
  calc ‖rege_gE s 1 z‖ * ‖F (x - z)‖ ≤ 1 * ‖F (x - z)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := one_mul _

lemma regh_T_eq {s : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    {F : Euc d → E} (hm : AEStronglyMeasurable F volume) (hR : lreg_RDec F) :
    regh_T s F = fun x => regh_Tk s F x + regh_T1 s F x := by
  obtain ⟨C0, hC0, h0⟩ := lreg_bound_of_rdec hR 0
  have hb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using h0 y
  have hFi : Integrable F := lreg_integrable_of_bound hm hb
  funext x
  obtain ⟨hI, -⟩ := regh_T_integrable hd1 hs hsd hm hC0 hb x
  have hk := regh_Tk_integrable hd1 hs hsd hs2 hm (B := C0) (fun y => (hb y).trans
    (by nlinarith [lreg_phi_le_one (d := d) y])) x
  have h1 := regh_T1_integrable hs hm hFi x
  unfold regh_T regh_Tk regh_T1
  rw [← integral_add hk h1]
  refine integral_congr_ae ?_
  filter_upwards [regh_ae_ne hd1] with z hz
  unfold regh_k
  rw [← add_smul]; congr 1; ring

/-- Differentiation of `T F`: the derivative falls on `F`. -/
lemma regh_T_hasFDerivAt [CompleteSpace E] {s : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d)
    {F : Euc d → E} (hF : ContDiff ℝ 1 F) (h0 : lreg_RDec F) (h1 : lreg_RDec (fderiv ℝ F))
    (x₀ : Euc d) :
    HasFDerivAt (regh_T s F) (regh_T s (fderiv ℝ F) x₀) x₀ := by
  obtain ⟨C0, hC0, hF0⟩ := lreg_bound_of_rdec h0 0
  obtain ⟨C1, hC1, hF1⟩ := lreg_bound_of_rdec h1 0
  have hFb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using hF0 y
  have hF1b : ∀ y, ‖fderiv ℝ F y‖ ≤ C1 * lreg_phi d y := fun y => by simpa using hF1 y
  have hFc : Continuous F := hF.continuous
  have hDc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  set h : Euc d → ℝ := fun y => 2 ^ (d + 1) * C1 * lreg_phi d y with hh
  have hhm : AEStronglyMeasurable h volume :=
    (continuous_const.mul lreg_phi_continuous).aestronglyMeasurable
  have hhb : ∀ y, ‖h y‖ ≤ (2 ^ (d + 1) * C1) * lreg_phi d y := fun y => by
    rw [hh]; simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by have := lreg_phi_pos y; positivity)]
  obtain ⟨hI, -⟩ := lreg_K_dom hd1 hsd hs.le (by positivity : (0 : ℝ) ≤ 2 ^ (d + 1) * C1) hhm hhb x₀
  unfold regh_T
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := ball x₀ 1)
    (F := fun x z => ‖z‖ ^ (-s) • F (x - z))
    (F' := fun x z => ‖z‖ ^ (-s) • fderiv ℝ F (x - z))
    (bound := fun z => ‖z‖ ^ (-s) * ‖h (x₀ - z)‖) (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ hI ?_
  · exact Eventually.of_forall fun x =>
      (measurable_norm.pow_const _).aestronglyMeasurable.smul
        (hFc.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x))
  · exact (regh_T_integrable hd1 hs hsd hFc.aestronglyMeasurable hC0 hFb x₀).1
  · exact (measurable_norm.pow_const _).aestronglyMeasurable.smul
      (hDc.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x₀))
  · refine ae_of_all _ fun z x hx => ?_
    have hx' : ‖x - x₀‖ ≤ 1 := by simpa [dist_eq_norm] using (mem_ball.1 hx).le
    have hsh := lreg_phi_shift (x := x) (x₀ := x₀) z hx'
    have hz0 : 0 ≤ ‖z‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg z) _
    rw [norm_smul, Real.norm_of_nonneg hz0]
    calc ‖z‖ ^ (-s) * ‖fderiv ℝ F (x - z)‖ ≤ ‖z‖ ^ (-s) * (C1 * lreg_phi d (x - z)) :=
          mul_le_mul_of_nonneg_left (hF1b _) hz0
      _ ≤ ‖z‖ ^ (-s) * (C1 * (2 ^ (d + 1) * lreg_phi d (x₀ - z))) := by gcongr
      _ = ‖z‖ ^ (-s) * ‖h (x₀ - z)‖ := by
          rw [hh]; simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (by have := lreg_phi_pos (x₀ - z); positivity)]
          ring
  · refine ae_of_all _ fun z x _ => ?_
    have h1 : HasFDerivAt F (fderiv ℝ F (x - z)) (x - z) :=
      (hF.differentiable one_ne_zero (x - z)).hasFDerivAt
    have h2 : HasFDerivAt (fun x : Euc d => x - z) (ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).sub_const z
    have h3 := (h1.comp x h2).const_smul (‖z‖ ^ (-s))
    refine h3.congr_fderiv ?_
    ext w
    simp

end TOp

end HRS.MS.Thm

end
