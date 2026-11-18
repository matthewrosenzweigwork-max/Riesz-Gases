import HRS.MS.EucRegHAux2

/-!
# C-REG-h (part 3): the crossing `C^{0,θ} → C^{1,μ}` for the Riesz potential, `d - 1 ≤ s < d`

Namespace `HRS.MS.Thm`, helper prefix `regh_`.  For `F` bounded, rapidly decaying and `θ`-Hölder with
`θ > 1 - (d - s)`: `T F = ∫ ‖z‖^{-s} F(x - z) dz` is `C¹`, with derivative `Pk F + P1 F`, which is bounded
and Hölder continuous (`regh_cross`).
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff Pointwise

noncomputable section

namespace HRS.MS.Thm

open HRS HRS.Whole HRS.MS.LogReg

variable {d : ℕ}

lemma regh_isLittleO_pow {E : Type} [NormedAddCommGroup E] {f : Euc d → E} {C q : ℝ} (hq : 1 < q)
    (hC : 0 ≤ C) (hf : ∀ h, ‖f h‖ ≤ C * ‖h‖ ^ q) : f =o[𝓝 0] fun h => h := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have ht : Tendsto (fun h : Euc d => ‖h‖ ^ (q - 1)) (𝓝 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (q - 1) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at this
    exact this.comp (continuous_norm.tendsto' 0 0 norm_zero)
  have hev : ∀ᶠ h in 𝓝 (0 : Euc d), ‖h‖ ^ (q - 1) < c / (C + 1) :=
    ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev] with h hh
  by_cases h0 : h = 0
  · subst h0
    have := hf 0
    simp only [norm_zero, Real.zero_rpow (by linarith : q ≠ 0), mul_zero] at this ⊢
    exact this
  · have hr : 0 < ‖h‖ := norm_pos_iff.2 h0
    have e : ‖h‖ ^ q = ‖h‖ * ‖h‖ ^ (q - 1) := by
      have := Real.rpow_add hr 1 (q - 1)
      rw [Real.rpow_one] at this
      rw [← this]; congr 1; ring
    have h1 : C * ‖h‖ ^ (q - 1) ≤ c := by
      have h2 : ‖h‖ ^ (q - 1) * (C + 1) < c := by
        rwa [lt_div_iff₀ (by positivity)] at hh
      nlinarith [Real.rpow_nonneg hr.le (q - 1)]
    calc ‖f h‖ ≤ C * ‖h‖ ^ q := hf h
      _ = (C * ‖h‖ ^ (q - 1)) * ‖h‖ := by rw [e]; ring
      _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

section Cross

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma regh_Tk_hasFDerivAt {s θ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hθ0 : 0 ≤ θ) (hθa : 1 < θ + ((d : ℝ) - s)) (hθb : θ + ((d : ℝ) - s) < 2)
    {F : Euc d → E} (hm : AEStronglyMeasurable F volume) {B K : ℝ} (hB : ∀ y, ‖F y‖ ≤ B) (hK0 : 0 ≤ K)
    (hK : ∀ x h, ‖F (x + h) - F x‖ ≤ K * ‖h‖ ^ θ) (x : Euc d) :
    HasFDerivAt (regh_Tk s F) (regh_Pk s F x) x := by
  obtain ⟨C, hC0, hC⟩ := regh_Tk_remainder (d := d) hd1 hs hsd hs2 hθ0 hθa hθb
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  exact regh_isLittleO_pow hθa (mul_nonneg hC0 hK0) (fun h => hC hm hB hK0 hK x h)

/-- Interpolation: `min (a^θ) (b^θ) ≤ b^{θ-θ'} a^{θ'}`. -/
lemma regh_min_pow {a b θ θ' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ : 0 < θ) (hθ' : 0 ≤ θ') (hθθ : θ' ≤ θ) :
    min (a ^ θ) (b ^ θ) ≤ b ^ (θ - θ') * a ^ θ' := by
  have hd : 0 ≤ θ - θ' := by linarith
  have e : ∀ x : ℝ, 0 ≤ x → x ^ θ = x ^ (θ - θ') * x ^ θ' := fun x hx => by
    rw [← Real.rpow_add' hx (by linarith)]; congr 1; ring
  rcases le_total a b with hab | hab
  · refine (min_le_left _ _).trans ?_
    rw [e a ha]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha hab hd) (Real.rpow_nonneg ha _)
  · refine (min_le_right _ _).trans ?_
    rw [e b hb]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb hab hθ') (Real.rpow_nonneg hb _)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Hölder exponents may be lowered (for bounded functions). -/
lemma regh_hol_mono {θ θ' K B : ℝ} (hθ : θ' ≤ θ) (hK0 : 0 ≤ K) (hB0 : 0 ≤ B) {f : Euc d → E}
    (hB : ∀ y, ‖f y‖ ≤ B) (hK : ∀ x h, ‖f (x + h) - f x‖ ≤ K * ‖h‖ ^ θ) (hθ'0 : 0 ≤ θ') :
    ∀ x h, ‖f (x + h) - f x‖ ≤ (K + 2 * B) * ‖h‖ ^ θ' := by
  intro x h
  have hn : 0 ≤ ‖h‖ := norm_nonneg h
  rcases le_or_gt ‖h‖ 1 with hh | hh
  · have h1 : ‖h‖ ^ θ ≤ ‖h‖ ^ θ' := by
      rcases eq_or_lt_of_le hn with h0 | h0
      · rw [← h0]
        rcases eq_or_lt_of_le hθ'0 with h00 | h00
        · rw [← h00]; rcases eq_or_lt_of_le (hθ'0.trans hθ) with h01 | h01
          · rw [← h01]
          · rw [Real.zero_rpow h01.ne']; simp
        · rw [Real.zero_rpow (by linarith), Real.zero_rpow h00.ne']
      · exact Real.rpow_le_rpow_of_exponent_ge h0 hh hθ
    have h2 : 0 ≤ ‖h‖ ^ θ' := Real.rpow_nonneg hn _
    calc _ ≤ K * ‖h‖ ^ θ := hK x h
      _ ≤ K * ‖h‖ ^ θ' := mul_le_mul_of_nonneg_left h1 hK0
      _ ≤ _ := by nlinarith [mul_nonneg hB0 h2]
  · have h1 : 1 ≤ ‖h‖ ^ θ' := Real.one_le_rpow hh.le hθ'0
    have h2 : ‖f (x + h) - f x‖ ≤ 2 * B := by
      calc _ ≤ ‖f (x + h)‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hB _) (hB _)
        _ = _ := by ring
    nlinarith [mul_nonneg hK0 (le_trans zero_le_one h1), mul_nonneg hB0 (le_trans zero_le_one h1)]

lemma regh_Pk_sub {s θ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hθ0 : 0 ≤ θ) (hθ1 : s + 1 - θ < d)
    (hs3 : (d : ℝ) < s + 3) {F : Euc d → E} (hm : AEStronglyMeasurable F volume) {B K : ℝ}
    (hB : ∀ y, ‖F y‖ ≤ B) (hK0 : 0 ≤ K) (hK : ∀ x h, ‖F (x + h) - F x‖ ≤ K * ‖h‖ ^ θ) (x h : Euc d) :
    regh_Pk s F (x + h) - regh_Pk s F x = regh_Pk s (fun y => F (y + h) - F y) x := by
  obtain ⟨C₁, C₂, -, -, hPk⟩ := regh_Pk_integrable_aux (d := d) (s := s) (θ := θ) hd1 hs hθ0 hθ1 hs3
  have hE : ∀ x z, ‖F (x - z) - F x‖ ≤ K * ‖z‖ ^ θ := fun x z => by
    have := hK x (-z)
    rw [norm_neg] at this
    simpa [sub_eq_add_neg] using this
  have hI1 := (hPk hm hB hK0 (x + h) (hE _)).1
  have hI0 := (hPk hm hB hK0 x (hE _)).1
  unfold regh_Pk
  rw [← integral_sub hI1 hI0]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply]
  rw [show x - z + h = x + h - z by abel, ← smul_sub]
  congr 1; abel

theorem regh_Pk_hold {s θ θ' : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hθ : 0 < θ) (hθ'0 : 0 ≤ θ')
    (hθθ : θ' ≤ θ) (hθ'1 : s + 1 - θ' < d) (hs3 : (d : ℝ) < s + 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {F : Euc d → E}, AEStronglyMeasurable F volume → ∀ {B K : ℝ}, (∀ y, ‖F y‖ ≤ B) → 0 ≤ K →
      (∀ x h, ‖F (x + h) - F x‖ ≤ K * ‖h‖ ^ θ) →
      (∀ x, ‖regh_Pk s F x‖ ≤ C * (K + B)) ∧
      ∀ x h, ‖h‖ ≤ 1 → ‖regh_Pk s F (x + h) - regh_Pk s F x‖ ≤ C * K * ‖h‖ ^ (θ - θ') := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hPk⟩ := regh_Pk_integrable_aux (d := d) (s := s) (θ := θ') hd1 hs hθ'0 hθ'1
    hs3
  refine ⟨2 * C₁ + C₂, by positivity, ?_⟩
  intro E _ _ _ F hm B K hB hK0 hK
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hK' := regh_hol_mono hθθ hK0 hB0 hB hK hθ'0
  have hE : ∀ (G : Euc d → E) (K' : ℝ), (∀ x h, ‖G (x + h) - G x‖ ≤ K' * ‖h‖ ^ θ') →
      ∀ x z, ‖G (x - z) - G x‖ ≤ K' * ‖z‖ ^ θ' := fun G K' hG x z => by
    have := hG x (-z)
    rw [norm_neg] at this
    simpa [sub_eq_add_neg] using this
  refine ⟨fun x => ?_, fun x h hh => ?_⟩
  · refine (hPk hm hB (by positivity) x (hE F _ hK' x)).2.trans ?_
    nlinarith
  · by_cases h0 : h = 0
    · subst h0
      simp only [add_zero, sub_self, norm_zero]
      positivity
    have hρ : 0 < ‖h‖ := norm_pos_iff.2 h0
    have hsub := regh_Pk_sub (d := d) hd1 hs hθ'0 hθ'1 hs3 hm hB (K := K + 2 * B) (by positivity) hK' x h
    have hHm : AEStronglyMeasurable (fun y => F (y + h) - F y) volume :=
      (hm.comp_measurePreserving (measurePreserving_add_right volume h)).sub hm
    have hHb : ∀ y, ‖F (y + h) - F y‖ ≤ K * ‖h‖ ^ θ := fun y => hK y h
    have hHh : ∀ y w, ‖(F (y + w + h) - F (y + w)) - (F (y + h) - F y)‖ ≤
        (2 * K * ‖h‖ ^ (θ - θ')) * ‖w‖ ^ θ' := by
      intro y w
      have b1 : ‖(F (y + w + h) - F (y + w)) - (F (y + h) - F y)‖ ≤ 2 * K * ‖w‖ ^ θ := by
        have e : (F (y + w + h) - F (y + w)) - (F (y + h) - F y) =
            (F (y + h + w) - F (y + h)) - (F (y + w) - F y) := by
          rw [show y + w + h = y + h + w by abel]; abel
        rw [e]
        calc _ ≤ ‖F (y + h + w) - F (y + h)‖ + ‖F (y + w) - F y‖ := norm_sub_le _ _
          _ ≤ K * ‖w‖ ^ θ + K * ‖w‖ ^ θ := add_le_add (hK _ _) (hK _ _)
          _ = _ := by ring
      have b2 : ‖(F (y + w + h) - F (y + w)) - (F (y + h) - F y)‖ ≤ 2 * K * ‖h‖ ^ θ := by
        calc _ ≤ ‖F (y + w + h) - F (y + w)‖ + ‖F (y + h) - F y‖ := norm_sub_le _ _
          _ ≤ K * ‖h‖ ^ θ + K * ‖h‖ ^ θ := add_le_add (hK _ _) (hK _ _)
          _ = _ := by ring
      have hmin := regh_min_pow (norm_nonneg w) (norm_nonneg h) hθ hθ'0 hθθ
      have : ‖(F (y + w + h) - F (y + w)) - (F (y + h) - F y)‖ ≤ 2 * K * min (‖w‖ ^ θ) (‖h‖ ^ θ) := by
        rcases le_total (‖w‖ ^ θ) (‖h‖ ^ θ) with hle | hle
        · rw [min_eq_left hle]; exact b1
        · rw [min_eq_right hle]; exact b2
      calc _ ≤ 2 * K * min (‖w‖ ^ θ) (‖h‖ ^ θ) := this
        _ ≤ 2 * K * (‖h‖ ^ (θ - θ') * ‖w‖ ^ θ') := mul_le_mul_of_nonneg_left hmin (by positivity)
        _ = _ := by ring
    have hHh' : ∀ y w, ‖(fun y => F (y + h) - F y) (y + w) - (fun y => F (y + h) - F y) y‖ ≤
        (2 * K * ‖h‖ ^ (θ - θ')) * ‖w‖ ^ θ' := by
      intro y w
      have := hHh y w
      simp only
      rw [show F (y + w + h) - F (y + w) - (F (y + h) - F y) =
        (F (y + w + h) - F (y + w)) - (F (y + h) - F y) from rfl] at *
      convert this using 2
    have hKH : 0 ≤ 2 * K * ‖h‖ ^ (θ - θ') := by positivity
    have hBH : ∀ y, ‖F (y + h) - F y‖ ≤ K * ‖h‖ ^ θ := hHb
    have hKH2 : 0 ≤ K * ‖h‖ ^ θ := by positivity
    obtain ⟨-, hbnd⟩ := hPk hHm hBH hKH x (hE (fun y => F (y + h) - F y) _ hHh' x)
    have hpow : ‖h‖ ^ θ ≤ ‖h‖ ^ (θ - θ') := Real.rpow_le_rpow_of_exponent_ge hρ hh (by linarith)
    rw [hsub]
    refine hbnd.trans ?_
    nlinarith [mul_nonneg hK0 (Real.rpow_nonneg hρ.le θ), mul_le_mul_of_nonneg_left hpow hK0, hC₂, hC₁]

/-- Derivative of the smooth part `T1`. -/
def regh_P1 (s : ℝ) (F : Euc d → E) (x : Euc d) : Euc d →L[ℝ] E :=
  ∫ y, (rege_L s (rege_kE s 1 (x - y))).smulRight (F y)

lemma regh_T1_eq_y (s : ℝ) (F : Euc d → E) (x : Euc d) :
    regh_T1 s F x = ∫ y, rege_gE s 1 (x - y) • F y := by
  have := integral_sub_left_eq_self (fun z : Euc d => rege_gE s 1 z • F (x - z)) volume x
  simp only [sub_sub_cancel] at this
  unfold regh_T1
  rw [← this]

lemma regh_P1_integrable {s : ℝ} (hs : 0 < s) {F : Euc d → E} (hm : AEStronglyMeasurable F volume)
    (hI : Integrable F) (x : Euc d) :
    Integrable (fun y => (rege_L s (rege_kE s 1 (x - y))).smulRight (F y)) := by
  have hmeas : AEStronglyMeasurable (fun y : Euc d => (rege_L s (rege_kE s 1 (x - y))).smulRight (F y))
      volume := by
    have h1 : AEStronglyMeasurable (fun y : Euc d => rege_L s (rege_kE s 1 (x - y))) volume :=
      ((rege_L s : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).continuous.comp
        ((rege_kE_continuous (s := s) one_pos).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    exact (ContinuousLinearMap.smulRightL ℝ (Euc d) E).aestronglyMeasurable_comp₂ h1 hm
  refine (hI.norm.const_mul s).mono' hmeas (ae_of_all _ fun y => ?_)
  rw [ContinuousLinearMap.norm_smulRight_apply, rege_L_norm hs.le]
  have := rege_kE_le (d := d) hs one_pos (x - y)
  simp only [Real.one_rpow] at this
  have h2 := mul_nonneg (mul_nonneg hs.le (norm_nonneg (F y))) (sub_nonneg.2 this)
  nlinarith

lemma regh_T1_hasFDerivAt {s : ℝ} (hs : 0 < s) {F : Euc d → E} (hm : AEStronglyMeasurable F volume)
    (hI : Integrable F) (x₀ : Euc d) :
    HasFDerivAt (regh_T1 s F) (regh_P1 s F x₀) x₀ := by
  have hfun : regh_T1 s F = fun x => ∫ y, rege_gE s 1 (x - y) • F y := funext (regh_T1_eq_y s F)
  rw [hfun]
  unfold regh_P1
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (F := fun x y => rege_gE s 1 (x - y) • F y)
    (F' := fun x y => (rege_L s (rege_kE s 1 (x - y))).smulRight (F y))
    (bound := fun y => s * ‖F y‖) Filter.univ_mem ?_ ?_ ?_ ?_ (hI.norm.const_mul s) ?_
  · exact Eventually.of_forall fun x =>
      ((rege_gE_continuous (s := s) one_pos).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.smul hm
  · refine (hI.norm.mono' ?_ (ae_of_all _ fun y => ?_))
    · exact ((rege_gE_continuous (s := s) one_pos).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable.smul hm
    · rw [norm_smul]
      have h1 : ‖rege_gE s 1 (x₀ - y)‖ ≤ 1 := by
        have := rege_gE_le (d := d) (s := s) (ε := 1) hs one_pos (x₀ - y)
        simpa using this
      calc ‖rege_gE s 1 (x₀ - y)‖ * ‖F y‖ ≤ 1 * ‖F y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖F y‖ := one_mul _
  · exact (regh_P1_integrable hs hm hI x₀).aestronglyMeasurable
  · refine ae_of_all _ fun y x _ => ?_
    rw [ContinuousLinearMap.norm_smulRight_apply, rege_L_norm hs.le]
    have := rege_kE_le (d := d) hs one_pos (x - y)
    simp only [Real.one_rpow] at this
    have h2 := mul_nonneg (mul_nonneg hs.le (norm_nonneg (F y))) (sub_nonneg.2 this)
    nlinarith
  · exact ae_of_all _ fun y x _ => (rege_gE_hasFDerivAt (s := s) (ε := 1) one_pos y x).smul_const (F y)

lemma regh_kE1_lip {s : ℝ} (hs : 0 < s) (w h : Euc d) :
    ‖rege_kE s 1 (w + h) - rege_kE s 1 w‖ ≤ (s + 3) * ‖h‖ := by
  have hp : 0 ≤ s / 2 + 1 := by positivity
  have hb : ∀ z ∈ (Set.univ : Set (Euc d)), ‖regh_Dk (s / 2 + 1) 1 z‖ ≤ s + 3 := by
    intro z _
    have h1 := regh_Dk_norm_le (d := d) hp zero_le_one (z := z) (c := 1) (by positivity)
    have h2 : ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(s / 2 + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖z‖]) (by linarith)
    have e2 : 1 + 2 * (s / 2 + 1) = s + 3 := by ring
    rw [e2] at h1
    have h3 : 0 ≤ s + 3 := by positivity
    nlinarith
  have hd : ∀ z ∈ (Set.univ : Set (Euc d)),
      HasFDerivWithinAt (rege_kE s 1 : Euc d → Euc d) (regh_Dk (s / 2 + 1) 1 z) Set.univ z := by
    intro z _
    have e : (rege_kE s 1 : Euc d → Euc d) = fun w => ((1 : ℝ) + ‖w‖ ^ 2) ^ (-(s / 2 + 1)) • w := by
      funext w; simp [rege_kE]
    rw [e]
    exact (regh_kern_hasFDerivAt' (c := 1) (by positivity)).hasFDerivWithinAt
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ) (f := rege_kE s 1)
    (f' := regh_Dk (s / 2 + 1) 1) (s := Set.univ) (x := w) (y := w + h) hd hb convex_univ
    (Set.mem_univ _) (Set.mem_univ _)
  simpa [add_sub_cancel_left] using this

lemma regh_P1_bound {s : ℝ} (hs : 0 < s) {F : Euc d → E} (hm : AEStronglyMeasurable F volume)
    (hI : Integrable F) (x : Euc d) : ‖regh_P1 s F x‖ ≤ s * ∫ y, ‖F y‖ := by
  have hi := regh_P1_integrable hs hm hI x
  unfold regh_P1
  have hpt : ∀ y : Euc d, ‖(rege_L s (rege_kE s 1 (x - y))).smulRight (F y)‖ ≤ s * ‖F y‖ := by
    intro y
    rw [ContinuousLinearMap.norm_smulRight_apply, rege_L_norm hs.le]
    have := rege_kE_le (d := d) hs one_pos (x - y)
    simp only [Real.one_rpow] at this
    have h2 := mul_nonneg (mul_nonneg hs.le (norm_nonneg (F y))) (sub_nonneg.2 this)
    nlinarith
  calc _ ≤ ∫ y, s * ‖F y‖ := norm_integral_le_of_norm_le (hI.norm.const_mul s) (ae_of_all _ hpt)
    _ = _ := integral_const_mul _ _

lemma regh_P1_lip {s : ℝ} (hs : 0 < s) {F : Euc d → E} (hm : AEStronglyMeasurable F volume)
    (hI : Integrable F) (x h : Euc d) :
    ‖regh_P1 s F (x + h) - regh_P1 s F x‖ ≤ (s * (s + 3) * ‖h‖) * ∫ y, ‖F y‖ := by
  have hi1 := regh_P1_integrable hs hm hI (x + h)
  have hi0 := regh_P1_integrable hs hm hI x
  unfold regh_P1
  rw [← integral_sub hi1 hi0]
  have hpt : ∀ y : Euc d, ‖(rege_L s (rege_kE s 1 (x + h - y))).smulRight (F y) -
      (rege_L s (rege_kE s 1 (x - y))).smulRight (F y)‖ ≤ (s * (s + 3) * ‖h‖) * ‖F y‖ := by
    intro y
    have e : (rege_L s (rege_kE s 1 (x + h - y))).smulRight (F y) -
        (rege_L s (rege_kE s 1 (x - y))).smulRight (F y) =
        (rege_L s (rege_kE s 1 (x - y + h) - rege_kE s 1 (x - y))).smulRight (F y) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [sub_apply, ContinuousLinearMap.smulRight_apply, map_sub, sub_smul,
        show x + h - y = x - y + h by abel]
    rw [e, ContinuousLinearMap.norm_smulRight_apply, rege_L_norm hs.le]
    have := regh_kE1_lip hs (x - y) h
    have h2 := mul_nonneg (mul_nonneg hs.le (norm_nonneg (F y))) (sub_nonneg.2 this)
    nlinarith
  calc _ ≤ ∫ y, (s * (s + 3) * ‖h‖) * ‖F y‖ :=
        norm_integral_le_of_norm_le (hI.norm.const_mul _) (ae_of_all _ hpt)
    _ = _ := integral_const_mul _ _

/-- **Crossing**: for `F` rapidly decaying and `θ`-Hölder with `θ > 1 - (d - s)`, `T F` is `C¹` with a bounded
Hölder-`(θ - θ')` derivative. -/
theorem regh_cross {s θ θ' : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθ'0 : 0 ≤ θ') (hθθ : θ' ≤ θ) (hθ'a : 1 < θ' + ((d : ℝ) - s))
    (hθb : θ + ((d : ℝ) - s) < 2) {F : Euc d → E} (hm : AEStronglyMeasurable F volume)
    (hR : lreg_RDec F) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x h, ‖F (x + h) - F x‖ ≤ K * ‖h‖ ^ θ) :
    ∃ P : Euc d → (Euc d →L[ℝ] E), (∀ x, HasFDerivAt (regh_T s F) (P x) x) ∧
      (∃ M : ℝ, ∀ x, ‖P x‖ ≤ M) ∧
      ∃ K' : ℝ, 0 ≤ K' ∧ ∀ x h, ‖P (x + h) - P x‖ ≤ K' * ‖h‖ ^ (θ - θ') := by
  obtain ⟨C0, hC00, h0⟩ := lreg_bound_of_rdec hR 0
  have hb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using h0 y
  have hB : ∀ y, ‖F y‖ ≤ C0 := fun y => (hb y).trans (by nlinarith [lreg_phi_le_one (d := d) y])
  have hFi : Integrable F := lreg_integrable_of_bound hm hb
  have hθa : 1 < θ + ((d : ℝ) - s) := by linarith
  have hθ'1 : s + 1 - θ' < d := by linarith
  have hs3 : (d : ℝ) < s + 3 := by linarith
  obtain ⟨C, hC0, hC⟩ := regh_Pk_hold (d := d) hd1 hs hθ hθ'0 hθθ hθ'1 hs3
  obtain ⟨hPb, hPh⟩ := hC hm hB hK0 hK
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ y, ‖F y‖ := ⟨_, rfl⟩
  have hI : 0 ≤ I := by rw [hIdef]; exact integral_nonneg fun _ => norm_nonneg _
  have hP1b : ∀ x, ‖regh_P1 s F x‖ ≤ s * I := fun x => by
    rw [hIdef]; exact regh_P1_bound hs hm hFi x
  have hP1l : ∀ x h, ‖regh_P1 s F (x + h) - regh_P1 s F x‖ ≤ (s * (s + 3) * ‖h‖) * I := fun x h => by
    rw [hIdef]; exact regh_P1_lip hs hm hFi x h
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = C * (K + C0) + s * I := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  refine ⟨fun x => regh_Pk s F x + regh_P1 s F x, fun x => ?_, ⟨M, fun x => ?_⟩,
    C * K + s * (s + 3) * I + 2 * M, by positivity, fun x h => ?_⟩
  · have hT := regh_T_eq hd1 hs hsd hs2 hm hR
    rw [hT]
    exact (regh_Tk_hasFDerivAt hd1 hs hsd hs2 hθ.le hθa hθb hm hB hK0 hK x).add
      (regh_T1_hasFDerivAt hs hm hFi x)
  · exact (norm_add_le _ _).trans (by rw [hMdef]; linarith [hPb x, hP1b x])
  · have hq : (0 : ℝ) ≤ θ - θ' := by linarith
    have hsplit : regh_Pk s F (x + h) + regh_P1 s F (x + h) - (regh_Pk s F x + regh_P1 s F x) =
        (regh_Pk s F (x + h) - regh_Pk s F x) + (regh_P1 s F (x + h) - regh_P1 s F x) := by abel
    show ‖regh_Pk s F (x + h) + regh_P1 s F (x + h) - (regh_Pk s F x + regh_P1 s F x)‖ ≤ _
    rw [hsplit]
    by_cases h0 : h = 0
    · subst h0
      simp only [add_zero, sub_self, add_zero, norm_zero]
      positivity
    have hρ : 0 < ‖h‖ := norm_pos_iff.2 h0
    have hP0 : 0 ≤ ‖h‖ ^ (θ - θ') := Real.rpow_nonneg hρ.le _
    rcases le_or_gt ‖h‖ 1 with hh | hh
    · have hpow : ‖h‖ ≤ ‖h‖ ^ (θ - θ') := by
        calc ‖h‖ = ‖h‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hρ hh (by linarith)
      refine (norm_add_le _ _).trans ?_
      have h1 := hPh x h hh
      have h2 := hP1l x h
      have h3 : (s * (s + 3) * ‖h‖) * I ≤ (s * (s + 3) * I) * ‖h‖ ^ (θ - θ') := by
        nlinarith [mul_nonneg (mul_nonneg hs.le (by positivity : (0 : ℝ) ≤ s + 3)) hI]
      have h4 : 0 ≤ M * ‖h‖ ^ (θ - θ') := mul_nonneg hM0 hP0
      nlinarith
    · have hpow : 1 ≤ ‖h‖ ^ (θ - θ') := Real.one_le_rpow hh.le hq
      have h2 : ‖regh_Pk s F (x + h) + regh_P1 s F (x + h) - (regh_Pk s F x + regh_P1 s F x)‖ ≤
          2 * M := by
        calc _ ≤ ‖regh_Pk s F (x + h) + regh_P1 s F (x + h)‖ + ‖regh_Pk s F x + regh_P1 s F x‖ :=
              norm_sub_le _ _
          _ ≤ M + M := add_le_add ((norm_add_le _ _).trans (by rw [hMdef]; linarith [hPb (x + h), hP1b (x + h)]))
              ((norm_add_le _ _).trans (by rw [hMdef]; linarith [hPb x, hP1b x]))
          _ = _ := by ring
      rw [← hsplit]
      have h5 : 0 ≤ C * K * ‖h‖ ^ (θ - θ') := by positivity
      have h6 : 0 ≤ s * (s + 3) * I * ‖h‖ ^ (θ - θ') := by positivity
      nlinarith

end Cross

/-! ### The recursive class `C_b^{k,θ}` -/

/-- `regh_C d θ k E f`: `f` is `C^k`, bounded together with `D^j f` (`j ≤ k`), and `D^k f` is globally `θ`-Hölder
(defined by recursion through `fderiv`). -/
def regh_C (d : ℕ) (θ : ℝ) : ℕ → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E], (Euc d → E) → Prop
  | 0, E, _, _, f => AEStronglyMeasurable f volume ∧ (∃ B : ℝ, ∀ x, ‖f x‖ ≤ B) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x h, ‖f (x + h) - f x‖ ≤ K * ‖h‖ ^ θ
  | k + 1, E, _, _, f => Differentiable ℝ f ∧ (∃ B : ℝ, ∀ x, ‖f x‖ ≤ B) ∧
      regh_C d θ k (Euc d →L[ℝ] E) (fderiv ℝ f)

/-- Decay of `f, Df, ..., D^k f` (recursion through `fderiv`). -/
def regh_R (d : ℕ) : ℕ → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E], (Euc d → E) → Prop
  | 0, E, _, _, f => lreg_RDec f
  | k + 1, E, _, _, f => lreg_RDec f ∧ regh_R d k (Euc d →L[ℝ] E) (fderiv ℝ f)

abbrev regh_Cl (θ : ℝ) (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Euc d → E) :
    Prop := regh_C d θ k E f

abbrev regh_Rl (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Euc d → E) : Prop :=
  regh_R d k E f

section Cls

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma regh_hol_cont {q K : ℝ} (hq : 0 < q) {f : Euc d → E} (hf : ∀ x h, ‖f (x + h) - f x‖ ≤ K * ‖h‖ ^ q) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have h1 : Continuous (fun x : Euc d => K * ‖x - x₀‖ ^ q) :=
    continuous_const.mul ((continuous_norm.comp (continuous_id.sub continuous_const)).rpow_const
      (fun _ => Or.inr hq.le))
  have hg : Tendsto (fun x : Euc d => K * ‖x - x₀‖ ^ q) (𝓝 x₀) (𝓝 0) := by
    have := h1.tendsto x₀
    simpa [Real.zero_rpow hq.ne'] using this
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) hg)
  have := hf x₀ (x - x₀)
  rwa [add_sub_cancel] at this

lemma regh_Cl_cont {θ : ℝ} (hθ : 0 < θ) {k : ℕ} {f : Euc d → E} (hf : regh_Cl θ k f) : Continuous f := by
  cases k with
  | zero => obtain ⟨-, -, K, -, hK⟩ := hf; exact regh_hol_cont hθ hK
  | succ k => exact hf.1.continuous

lemma regh_Cl_bdd {θ : ℝ} {k : ℕ} {f : Euc d → E} (hf : regh_Cl θ k f) : ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B := by
  cases k with
  | zero => exact hf.2.1
  | succ k => exact hf.2.1

/-- Lowering the differentiability order. -/
lemma regh_Cl_mono_k {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E},
      regh_Cl θ (k + 1) f → regh_Cl θ k f := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f hf
    obtain ⟨hd, ⟨B, hB⟩, -, ⟨B', hB'⟩, -⟩ := hf
    have hL : ∀ x h, ‖f (x + h) - f x‖ ≤ max B' 0 * ‖h‖ ^ (1 : ℝ) := fun x h => by
      rw [Real.rpow_one]
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f) (C := max B' 0)
        (s := Set.univ) (x := x) (y := x + h) (fun y _ => hd y)
        (fun y _ => (hB' y).trans (le_max_left _ _)) convex_univ (Set.mem_univ _) (Set.mem_univ _)
      simpa using this
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    have h2 := regh_hol_mono hθ1 (le_max_right _ _) hB0 hB hL hθ0
    exact ⟨hd.continuous.aestronglyMeasurable, ⟨B, hB⟩, max B' 0 + 2 * B, by positivity, h2⟩
  | succ k ih =>
    intro E _ _ f hf
    obtain ⟨hd, hB, hf'⟩ := hf
    exact ⟨hd, hB, ih hf'⟩

lemma regh_Cl_add {θ : ℝ} :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : Euc d → E},
      regh_Cl θ k f → regh_Cl θ k g → regh_Cl θ k (fun x => f x + g x) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f g hf hg
    obtain ⟨hm1, ⟨B1, hB1⟩, K1, hK1, hH1⟩ := hf
    obtain ⟨hm2, ⟨B2, hB2⟩, K2, hK2, hH2⟩ := hg
    refine ⟨hm1.add hm2, ⟨B1 + B2, fun x => (norm_add_le _ _).trans (add_le_add (hB1 x) (hB2 x))⟩,
      K1 + K2, by positivity, fun x h => ?_⟩
    have e : f (x + h) + g (x + h) - (f x + g x) = (f (x + h) - f x) + (g (x + h) - g x) := by abel
    rw [e, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hH1 x h) (hH2 x h))
  | succ k ih =>
    intro E _ _ f g hf hg
    obtain ⟨hd1, ⟨B1, hB1⟩, hf'⟩ := hf
    obtain ⟨hd2, ⟨B2, hB2⟩, hg'⟩ := hg
    refine ⟨hd1.add hd2, ⟨B1 + B2, fun x => (norm_add_le _ _).trans (add_le_add (hB1 x) (hB2 x))⟩, ?_⟩
    have e : fderiv ℝ (fun x => f x + g x) = fun x => fderiv ℝ f x + fderiv ℝ g x :=
      funext fun x => fderiv_add (hd1 x) (hd2 x)
    rw [e]
    exact ih hf' hg'

lemma regh_Cl_smul {θ : ℝ} (c : ℝ) :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E},
      regh_Cl θ k f → regh_Cl θ k (fun x => c • f x) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f hf
    obtain ⟨hm1, ⟨B1, hB1⟩, K1, hK1, hH1⟩ := hf
    refine ⟨hm1.const_smul c, ⟨|c| * B1, fun x => ?_⟩, |c| * K1, by positivity, fun x h => ?_⟩
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hB1 x) (abs_nonneg c)
    · rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hH1 x h) (abs_nonneg c)
  | succ k ih =>
    intro E _ _ f hf
    obtain ⟨hd1, ⟨B1, hB1⟩, hf'⟩ := hf
    refine ⟨hd1.const_smul c, ⟨|c| * B1, fun x => ?_⟩, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hB1 x) (abs_nonneg c)
    · have e : fderiv ℝ (fun x => c • f x) = fun x => c • fderiv ℝ f x :=
        funext fun x => fderiv_const_smul (hd1 x) c
      rw [e]
      exact ih hf'

lemma regh_Cl_prod {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ (k : ℕ) {E1 E2 E3 : Type} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
      [NormedSpace ℝ E2] [NormedAddCommGroup E3] [NormedSpace ℝ E3] (B : E1 →L[ℝ] E2 →L[ℝ] E3)
      {f : Euc d → E1} {g : Euc d → E2}, regh_Cl θ k f → regh_Cl θ k g →
      regh_Cl θ k (fun x => B (f x) (g x)) := by
  intro k
  induction k with
  | zero =>
    intro E1 E2 E3 _ _ _ _ _ _ B f g hf hg
    obtain ⟨hm1, ⟨B1, hB1⟩, K1, hK1, hH1⟩ := hf
    obtain ⟨hm2, ⟨B2, hB2⟩, K2, hK2, hH2⟩ := hg
    have hB1' : 0 ≤ B1 := le_trans (norm_nonneg _) (hB1 0)
    have hB2' : 0 ≤ B2 := le_trans (norm_nonneg _) (hB2 0)
    refine ⟨B.aestronglyMeasurable_comp₂ hm1 hm2, ⟨‖B‖ * B1 * B2, fun x => ?_⟩,
      ‖B‖ * (K1 * B2 + B1 * K2), by positivity, fun x h => ?_⟩
    · exact (B.le_opNorm₂ _ _).trans (by gcongr; exacts [hB1 x, hB2 x])
    · have e : B (f (x + h)) (g (x + h)) - B (f x) (g x) =
          B (f (x + h) - f x) (g (x + h)) + B (f x) (g (x + h) - g x) := by
        simp only [map_sub, ContinuousLinearMap.sub_apply]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖B (f (x + h) - f x) (g (x + h))‖ ≤ ‖B‖ * (K1 * ‖h‖ ^ θ) * B2 :=
        (B.le_opNorm₂ _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hH1 x h) (norm_nonneg B))
          (hB2 _) (norm_nonneg _) (by positivity))
      have h2 : ‖B (f x) (g (x + h) - g x)‖ ≤ ‖B‖ * B1 * (K2 * ‖h‖ ^ θ) :=
        (B.le_opNorm₂ _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hB1 x) (norm_nonneg B))
          (hH2 x h) (norm_nonneg _) (by positivity))
      calc _ ≤ _ := add_le_add h1 h2
        _ = _ := by ring
  | succ k ih =>
    intro E1 E2 E3 _ _ _ _ _ _ B f g hf hg
    have hf0 := regh_Cl_mono_k hθ0 hθ1 k hf
    have hg0 := regh_Cl_mono_k hθ0 hθ1 k hg
    obtain ⟨hd1, ⟨B1, hB1⟩, hf'⟩ := hf
    obtain ⟨hd2, ⟨B2, hB2⟩, hg'⟩ := hg
    have hB1' : 0 ≤ B1 := le_trans (norm_nonneg _) (hB1 0)
    have hB2' : 0 ≤ B2 := le_trans (norm_nonneg _) (hB2 0)
    have hder : ∀ x, HasFDerivAt (fun y => B (f y) (g y))
        (B.precompR (Euc d) (f x) (fderiv ℝ g x) + B.precompL (Euc d) (fderiv ℝ f x) (g x)) x :=
      fun x => B.hasFDerivAt_of_bilinear (hd1 x).hasFDerivAt (hd2 x).hasFDerivAt
    refine ⟨fun x => (hder x).differentiableAt, ⟨‖B‖ * B1 * B2, fun x => ?_⟩, ?_⟩
    · exact (B.le_opNorm₂ _ _).trans (by gcongr; exacts [hB1 x, hB2 x])
    · have e : fderiv ℝ (fun y => B (f y) (g y)) = fun x =>
          B.precompR (Euc d) (f x) (fderiv ℝ g x) + B.precompL (Euc d) (fderiv ℝ f x) (g x) :=
        funext fun x => (hder x).fderiv
      rw [e]
      exact regh_Cl_add k (ih (B.precompR (Euc d)) hf0 hg') (ih (B.precompL (Euc d)) hf' hg0)

lemma regh_exp_lip {a b B : ℝ} (ha : a ≤ B) (hb : b ≤ B) :
    |Real.exp a - Real.exp b| ≤ Real.exp B * |a - b| := by
  have key : ∀ a b : ℝ, b ≤ a → a ≤ B → Real.exp a - Real.exp b ≤ Real.exp B * (a - b) := by
    intro a b hba haB
    have h1 := Real.add_one_le_exp (b - a)
    have h2 : Real.exp (b - a) * Real.exp a = Real.exp b := by rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp a ≤ Real.exp B := Real.exp_le_exp.2 haB
    have h4 := Real.exp_pos a
    nlinarith
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)), abs_of_nonneg (sub_nonneg.2 h)]
    exact key a b h ha
  · rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)),
      abs_of_nonneg (sub_nonneg.2 h)]
    exact key b a h hb

lemma regh_Cl_exp {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ (k : ℕ) {f : Euc d → ℝ}, regh_Cl θ k f → regh_Cl θ k (fun x => Real.exp (f x)) := by
  intro k
  induction k with
  | zero =>
    intro f hf
    obtain ⟨hm, ⟨B, hB⟩, K, hK, hH⟩ := hf
    refine ⟨Real.continuous_exp.comp_aestronglyMeasurable hm, ⟨Real.exp B, fun x => ?_⟩,
      Real.exp B * K, by positivity, fun x h => ?_⟩
    · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans (by simpa using hB x))
    · have hb : ∀ y, f y ≤ B := fun y => (le_abs_self _).trans (by simpa using hB y)
      rw [Real.norm_eq_abs]
      calc _ ≤ Real.exp B * |f (x + h) - f x| := regh_exp_lip (hb _) (hb _)
        _ ≤ Real.exp B * (K * ‖h‖ ^ θ) := by
          gcongr
          simpa using hH x h
        _ = _ := by ring
  | succ k ih =>
    intro f hf
    have hf0 := regh_Cl_mono_k hθ0 hθ1 k hf
    obtain ⟨hd, ⟨B, hB⟩, hf'⟩ := hf
    have hder : ∀ x, HasFDerivAt (fun y => Real.exp (f y)) (Real.exp (f x) • fderiv ℝ f x) x :=
      fun x => (hd x).hasFDerivAt.exp
    refine ⟨fun x => (hder x).differentiableAt, ⟨Real.exp B, fun x => ?_⟩, ?_⟩
    · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans (by simpa using hB x))
    · have e : fderiv ℝ (fun y => Real.exp (f y)) = fun x => Real.exp (f x) • fderiv ℝ f x :=
        funext fun x => (hder x).fderiv
      rw [e]
      exact regh_Cl_prod hθ0 hθ1 k (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (Euc d →L[ℝ] ℝ) →L[ℝ] (Euc d →L[ℝ] ℝ))
        (ih hf0) hf'

/-- From the class to smoothness and bounds on all iterated derivatives. -/
lemma regh_Cl_contDiff {θ : ℝ} (hθ : 0 < θ) :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E}, regh_Cl θ k f →
      ContDiff ℝ k f ∧ ∃ M : ℝ, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f hf
    have hcont : Continuous f := regh_Cl_cont hθ hf
    obtain ⟨-, ⟨B, hB⟩, -⟩ := hf
    refine ⟨by rw [Nat.cast_zero, contDiff_zero]; exact hcont, B, fun j hj x => ?_⟩
    obtain rfl : j = 0 := by omega
    rw [norm_iteratedFDeriv_zero]; exact hB x
  | succ k ih =>
    intro E _ _ f hf
    obtain ⟨hd, ⟨B, hB⟩, hf'⟩ := hf
    obtain ⟨hc, M', hM'⟩ := ih hf'
    refine ⟨?_, max B M', fun j hj x => ?_⟩
    · have hc' : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hc', contDiff_succ_iff_fderiv]
      exact ⟨hd, fun h => absurd h (by simp), hc⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [norm_iteratedFDeriv_zero]; exact (hB x).trans (le_max_left _ _)
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [← norm_iteratedFDeriv_fderiv]
        exact (hM' j' (by omega) x).trans (le_max_right _ _)

lemma regh_R_of_iter :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E},
      (∀ j ≤ k, lreg_RDec (iteratedFDeriv ℝ j f)) → regh_Rl k f := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f h
    simpa [regh_Rl, regh_R, lreg_RDec, norm_iteratedFDeriv_zero] using h 0 le_rfl
  | succ k ih =>
    intro E _ _ f h
    refine ⟨by simpa [lreg_RDec, norm_iteratedFDeriv_zero] using h 0 (Nat.zero_le _), ih fun j hj => ?_⟩
    simpa [lreg_RDec, norm_iteratedFDeriv_fderiv] using h (j + 1) (by omega)

/-- From smoothness and bounds on all iterated derivatives to the class. -/
lemma regh_Cl_of_bdd {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E},
      ContDiff ℝ (k + 1 : ℕ) f → (∀ j ≤ k + 1, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M) →
      regh_Cl θ k f := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f hf hM
    obtain ⟨M, hB⟩ := hM 0 (by omega)
    obtain ⟨M', hD⟩ := hM 1 le_rfl
    have hd : Differentiable ℝ f := hf.differentiable (by simp)
    simp only [norm_iteratedFDeriv_zero] at hB
    simp only [norm_iteratedFDeriv_one] at hD
    have hL : ∀ x h, ‖f (x + h) - f x‖ ≤ max M' 0 * ‖h‖ ^ (1 : ℝ) := fun x h => by
      rw [Real.rpow_one]
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f) (C := max M' 0)
        (s := Set.univ) (x := x) (y := x + h) (fun y _ => hd y)
        (fun y _ => (hD y).trans (le_max_left _ _)) convex_univ (Set.mem_univ _) (Set.mem_univ _)
      simpa using this
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hB 0)
    have h2 := regh_hol_mono hθ1 (le_max_right _ _) hM0 hB hL hθ0
    exact ⟨hd.continuous.aestronglyMeasurable, ⟨M, hB⟩, max M' 0 + 2 * M, by positivity, h2⟩
  | succ k ih =>
    intro E _ _ f hf hM
    have hd : Differentiable ℝ f := hf.differentiable (by simp)
    obtain ⟨M, hB⟩ := hM 0 (by omega)
    simp only [norm_iteratedFDeriv_zero] at hB
    refine ⟨hd, ⟨M, hB⟩, ih ?_ fun j hj => ?_⟩
    · exact hf.fderiv_right (by exact_mod_cast le_rfl)
    · obtain ⟨M', h'⟩ := hM (j + 1) (by omega)
      exact ⟨M', fun x => by rw [norm_iteratedFDeriv_fderiv]; exact h' x⟩

lemma regh_R_rdec {k : ℕ} {f : Euc d → E} (h : regh_Rl k f) : lreg_RDec f := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

/-- The Hölder gain, at all differentiability orders. -/
lemma regh_gain_rec {s σ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hσs : s ≤ σ) (hσ2 : σ ≤ s + 2) (hσd : σ < d) {θ : ℝ} (hθ : 0 < θ) :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : Euc d → E},
      regh_Cl θ k F → regh_Rl k F → ∀ θ' : ℝ, 0 ≤ θ' → θ' ≤ θ → θ' + ((d : ℝ) - σ) < 1 →
      regh_Cl (θ' + ((d : ℝ) - σ)) k (regh_T s F) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ F hF hR θ' hθ'0 hθ'θ hθ'a
    obtain ⟨hm, ⟨B, hB⟩, K, hK0, hK⟩ := hF
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    have hK' := regh_hol_mono hθ'θ hK0 hB0 hB hK hθ'0
    obtain ⟨⟨Bt, hBt⟩, K', hK'0, hK''⟩ := regh_T_hold hd1 hs hsd hs2 hσs hσ2 hσd hθ'0 hθ'a hm
      (regh_R_rdec hR) (by positivity) hK'
    have hpos : 0 < θ' + ((d : ℝ) - σ) := by linarith
    exact ⟨(regh_hol_cont hpos hK'').aestronglyMeasurable, ⟨Bt, hBt⟩, K', hK'0, hK''⟩
  | succ k ih =>
    intro E _ _ _ F hF hR θ' hθ'0 hθ'θ hθ'a
    have hcF : Continuous F := hF.1.continuous
    obtain ⟨hd, ⟨B, hB⟩, hF'⟩ := hF
    obtain ⟨hR0, hR'⟩ := hR
    have hcF' : Continuous (fderiv ℝ F) := regh_Cl_cont hθ hF'
    have hF1 : ContDiff ℝ 1 F := contDiff_one_iff_fderiv.2 ⟨hd, hcF'⟩
    have hT : ∀ x, HasFDerivAt (regh_T s F) (regh_T s (fderiv ℝ F) x) x := fun x =>
      regh_T_hasFDerivAt hd1 hs hsd hF1 hR0 (regh_R_rdec hR') x
    obtain ⟨C0, hC00, h0⟩ := lreg_bound_of_rdec hR0 0
    have hb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using h0 y
    refine ⟨fun x => (hT x).differentiableAt, ⟨C0 * lreg_A d s, fun x =>
      (regh_T_integrable hd1 hs hsd hcF.aestronglyMeasurable hC00 hb x).2⟩, ?_⟩
    have e : fderiv ℝ (regh_T s F) = regh_T s (fderiv ℝ F) := funext fun x => (hT x).fderiv
    rw [e]
    exact ih hF' hR' θ' hθ'0 hθ'θ hθ'a

/-- The crossing, at all differentiability orders. -/
lemma regh_cross_rec {s θ θ' : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθ'0 : 0 ≤ θ') (hθθ : θ' < θ) (hθ'a : 1 < θ' + ((d : ℝ) - s))
    (hθb : θ + ((d : ℝ) - s) < 2) :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : Euc d → E},
      regh_Cl θ k F → regh_Rl k F → regh_Cl (θ - θ') (k + 1) (regh_T s F) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ F hF hR
    obtain ⟨hm, ⟨B, hB⟩, K, hK0, hK⟩ := hF
    obtain ⟨P, hP, ⟨M, hM⟩, K', hK'0, hK'⟩ := regh_cross hd1 hs hsd hs2 hθ hθ1 hθ'0 hθθ.le hθ'a hθb hm
      (regh_R_rdec hR) hK0 hK
    obtain ⟨C0, hC00, h0⟩ := lreg_bound_of_rdec (regh_R_rdec hR) 0
    have hb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using h0 y
    refine ⟨fun x => (hP x).differentiableAt, ⟨C0 * lreg_A d s, fun x =>
      (regh_T_integrable hd1 hs hsd hm hC00 hb x).2⟩, ?_⟩
    have e : fderiv ℝ (regh_T s F) = P := funext fun x => (hP x).fderiv
    rw [e]
    exact ⟨(regh_hol_cont (sub_pos.2 hθθ) hK').aestronglyMeasurable, ⟨M, hM⟩, K', hK'0, hK'⟩
  | succ k ih =>
    intro E _ _ _ F hF hR
    have hcF : Continuous F := hF.1.continuous
    obtain ⟨hd, ⟨B, hB⟩, hF'⟩ := hF
    obtain ⟨hR0, hR'⟩ := hR
    have hcF' : Continuous (fderiv ℝ F) := regh_Cl_cont hθ hF'
    have hF1 : ContDiff ℝ 1 F := contDiff_one_iff_fderiv.2 ⟨hd, hcF'⟩
    have hT : ∀ x, HasFDerivAt (regh_T s F) (regh_T s (fderiv ℝ F) x) x := fun x =>
      regh_T_hasFDerivAt hd1 hs hsd hF1 hR0 (regh_R_rdec hR') x
    obtain ⟨C0, hC00, h0⟩ := lreg_bound_of_rdec hR0 0
    have hb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using h0 y
    refine ⟨fun x => (hT x).differentiableAt, ⟨C0 * lreg_A d s, fun x =>
      (regh_T_integrable hd1 hs hsd hcF.aestronglyMeasurable hC00 hb x).2⟩, ?_⟩
    have e : fderiv ℝ (regh_T s F) = regh_T s (fderiv ℝ F) := funext fun x => (hT x).fderiv
    rw [e]
    exact ih hF' hR'

end Cls

/-! ### The thermal profile -/

lemma regh_gauss_Cl {a β Z θ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hZ : 0 < Z) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (k : ℕ) :
    regh_Cl θ k (fun x : Euc d => Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + 0)) / Z) := by
  have hb2 : 0 < β * a / 2 := by positivity
  have hφ : ContDiff ℝ (k + 1 : ℕ) (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + (fun _ => (0 : ℝ)) x)) :=
    contDiff_const.mul (((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2).add contDiff_const)
  obtain ⟨C, hC, hD⟩ := rege_exponent_bound (d := d) a β (U := fun _ => (0 : ℝ)) (n := k + 1)
    contDiff_const (M := 0) le_rfl (fun i hi _ x => by
      simp [iteratedFDeriv_const_of_ne (by omega : i ≠ 0)])
  have hup : ∀ x : Euc d, Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + 0)) / Z ≤
      Z⁻¹ * Real.exp (-β * a * ‖x‖ ^ 2 / 2) := fun x => by
    rw [div_eq_inv_mul]; apply le_of_eq; congr 2; ring
  obtain ⟨hρk, hρD⟩ := rege_rho_deriv (d := d) (a := a) (β := β) (Z := Z) (C0 := Z⁻¹) hZ
    (ρ := fun x : Euc d => Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + 0)) / Z) (φ := fun x => -β * (a * ‖x‖ ^ 2 / 2 + (fun _ => (0 : ℝ)) x))
    (fun x => rfl) hup hφ hC hD
  refine regh_Cl_of_bdd hθ0 hθ1 k hρk fun j hj => ?_
  obtain ⟨K, hK, hKb⟩ := hρD j hj
  obtain ⟨Cb, hCb, hCbb⟩ := rege_poly_gauss_bdd hb2 j
  refine ⟨K * Cb, fun x => (hKb x).trans ?_⟩
  rw [rege_exp_form, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hCbb _ (norm_nonneg x)) hK

end HRS.MS.Thm

end
