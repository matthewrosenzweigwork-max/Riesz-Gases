import HRS.MS.EucRegHAux1

/-!
# C-REG-h (part 2): the Hölder gain `C^{0,θ} → C^{0,θ+a}` for the Riesz potential (`d - 1 < σ < d`)

Namespace `HRS.MS.Thm`, helper prefix `regh_`.  `regh_Hol θ K f` is the global Hölder condition
`‖f(x+h) - f(x)‖ ≤ K ‖h‖^θ`.  With `a = d - σ ∈ (0,1)` and `s ≤ σ ≤ s + 2` the localised kernel
`k = regh_k s` satisfies `|k(z)| ≤ c‖z‖^{-σ}` and `‖∇k(z)‖ ≤ c ‖z‖^{-σ-1}`; since `k ∈ L¹`,
`∫ (k(z+h) - k(z)) dz = 0`, hence
`T_k F(x+h) - T_k F(x) = ∫ (k(z+h) - k(z)) (F(x-z) - F(x)) dz`, which is `≲ K ‖h‖^{θ+a}` for `θ + a < 1`
(near field `‖z‖ < 2‖h‖`: power integrals; far field: mean value theorem for `k`).
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff Pointwise

noncomputable section

namespace HRS.MS.Thm

open HRS HRS.Whole HRS.MS.LogReg

variable {d : ℕ}

/-- Global Hölder condition. -/
def regh_Hol {E : Type} [NormedAddCommGroup E] (θ K : ℝ) (f : Euc d → E) : Prop :=
  ∀ x h, ‖f (x + h) - f x‖ ≤ K * ‖h‖ ^ θ

lemma regh_k_diff_far {s σ : ℝ} (hs : 0 < s) (hσs : s ≤ σ) (hσ2 : σ ≤ s + 2) {z h : Euc d}
    (hzh : 2 * ‖h‖ ≤ ‖z‖) (hh : h ≠ 0) :
    ‖regh_k s (z + h) - regh_k s z‖ ≤
      (s * max 2 (max 1 (s / 2 + 1))) * 2 ^ (σ + 1) * ‖h‖ * ‖z‖ ^ (-(σ + 1)) := by
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hzn : 0 < ‖z‖ := by linarith
  have hseg : ∀ w ∈ segment ℝ z (z + h), ‖z‖ / 2 ≤ ‖w‖ := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    simp only [add_sub_cancel_left]
    have h1 : ‖z‖ - ‖t • h‖ ≤ ‖z + t • h‖ := by
      have := norm_sub_norm_le z (-(t • h))
      simpa [sub_neg_eq_add, norm_neg] using this
    have h2 : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    linarith
  have hbd : ∀ w ∈ segment ℝ z (z + h),
      ‖rege_L s (rege_kap s w - rege_kE s 1 w)‖ ≤
        (s * max 2 (max 1 (s / 2 + 1))) * 2 ^ (σ + 1) * ‖z‖ ^ (-(σ + 1)) := by
    intro w hw
    have hw2 := hseg w hw
    have hwn : 0 < ‖w‖ := by linarith
    have hw0 : w ≠ 0 := norm_pos_iff.1 hwn
    refine (regh_k_grad_bound hs hσs hσ2 hw0).trans ?_
    have h1 : ‖w‖ ^ (-(σ + 1)) ≤ (‖z‖ / 2) ^ (-(σ + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hw2 (by linarith)
    have h2 : (‖z‖ / 2) ^ (-(σ + 1)) = 2 ^ (σ + 1) * ‖z‖ ^ (-(σ + 1)) := by
      rw [Real.div_rpow hzn.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_eq_mul_inv, inv_inv, mul_comm]
    calc (s * max 2 (max 1 (s / 2 + 1))) * ‖w‖ ^ (-(σ + 1))
        ≤ (s * max 2 (max 1 (s / 2 + 1))) * (2 ^ (σ + 1) * ‖z‖ ^ (-(σ + 1))) := by
          rw [← h2]; gcongr
      _ = (s * max 2 (max 1 (s / 2 + 1))) * 2 ^ (σ + 1) * ‖z‖ ^ (-(σ + 1)) := by ring
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ) (f := regh_k s)
    (f' := fun w => rege_L s (rege_kap s w - rege_kE s 1 w)) (s := segment ℝ z (z + h))
    (x := z) (y := z + h)
    (fun w hw => (regh_k_hasFDerivAt (s := s) (norm_pos_iff.1 (by linarith [hseg w hw] : 0 < ‖w‖))).hasFDerivWithinAt)
    hbd (convex_segment _ _) (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  simpa [add_sub_cancel_left, mul_assoc, mul_comm, mul_left_comm] using this

section Gain

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma regh_Tk_diff_eq {s : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    {F : Euc d → E} (hm : AEStronglyMeasurable F volume) {B : ℝ} (hB : ∀ y, ‖F y‖ ≤ B) (x h : Euc d) :
    regh_Tk s F (x + h) - regh_Tk s F x =
      ∫ z, (regh_k s (z + h) - regh_k s z) • (F (x - z) - F x) := by
  have hk := regh_k_integrable hd1 hs hsd hs2
  have hint1 := regh_Tk_integrable hd1 hs hsd hs2 hm hB x
  have hint0 := regh_Tk_integrable hd1 hs hsd hs2 hm hB (x + h)
  have hint2 : Integrable (fun z => regh_k s (z + h) • F (x - z)) := by
    have := hint0.comp_add_right h
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [add_sub_add_right_eq_sub]
  have e1 : regh_Tk s F (x + h) = ∫ z, regh_k s (z + h) • F (x - z) := by
    unfold regh_Tk
    rw [← integral_add_right_eq_self (μ := volume) (fun z => regh_k s z • F (x + h - z)) h]
    simp only [add_sub_add_right_eq_sub]
  have e2 : ∫ z, (regh_k s (z + h) - regh_k s z) • F x = 0 := by
    rw [integral_smul_const, integral_sub (hk.comp_add_right h) hk,
      integral_add_right_eq_self (μ := volume) (regh_k s) h, sub_self, zero_smul]
  have e3 : ∫ z, (regh_k s (z + h) - regh_k s z) • (F (x - z) - F x) =
      (∫ z, (regh_k s (z + h) - regh_k s z) • F (x - z)) -
        ∫ z, (regh_k s (z + h) - regh_k s z) • F x := by
    have hA : Integrable (fun z => (regh_k s (z + h) - regh_k s z) • F (x - z)) := by
      refine (hint2.sub hint1).congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply, sub_smul]
    have hB' : Integrable (fun z => (regh_k s (z + h) - regh_k s z) • F x) :=
      ((hk.comp_add_right h).sub hk).smul_const _
    have : (fun z => (regh_k s (z + h) - regh_k s z) • (F (x - z) - F x)) =
        fun z => (regh_k s (z + h) - regh_k s z) • F (x - z) - (regh_k s (z + h) - regh_k s z) • F x := by
      funext z; simp only [smul_sub]
    rw [this]
    exact integral_sub hA hB'
  rw [e3, e2, sub_zero, e1]
  unfold regh_Tk
  rw [← integral_sub hint2 hint1]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [sub_smul]

/-- Indicator of a ball times a power. -/
def regh_ind1 (σ r : ℝ) : Euc d → ℝ := (ball (0 : Euc d) r).indicator fun w => ‖w‖ ^ (-σ)

/-- Indicator of the complement of a ball times a power. -/
def regh_ind2 (p r : ℝ) : Euc d → ℝ := ((ball (0 : Euc d) r)ᶜ).indicator fun w => ‖w‖ ^ (-p)

lemma regh_ind1_nonneg (σ r : ℝ) (z : Euc d) : 0 ≤ regh_ind1 σ r z :=
  Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg w) _) _

lemma regh_ind2_nonneg (σ r : ℝ) (z : Euc d) : 0 ≤ regh_ind2 σ r z :=
  Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg w) _) _

lemma regh_ind1_of_lt {σ r : ℝ} {z : Euc d} (h : ‖z‖ < r) : regh_ind1 σ r z = ‖z‖ ^ (-σ) := by
  unfold regh_ind1
  rw [Set.indicator_of_mem (by simpa using h)]

lemma regh_ind2_of_le {σ r : ℝ} {z : Euc d} (h : r ≤ ‖z‖) : regh_ind2 σ r z = ‖z‖ ^ (-σ) := by
  unfold regh_ind2
  rw [Set.indicator_of_mem (by simpa using h)]

lemma regh_ind1_integrable {σ r : ℝ} (hd1 : 1 ≤ d) (hσ : σ < d) (hr : 0 < r) :
    Integrable (regh_ind1 σ r : Euc d → ℝ) :=
  (regh_ball_int hd1 hσ hr).integrable_indicator measurableSet_ball

lemma regh_ind2_integrable {p r : ℝ} (hp : (d : ℝ) < p) (hr : 0 < r) :
    Integrable (regh_ind2 p r : Euc d → ℝ) :=
  (regh_tail_int hp hr).integrable_indicator measurableSet_ball.compl

lemma regh_ind1_integral {σ r : ℝ} (hr : 0 < r) :
    ∫ z, regh_ind1 σ r (z : Euc d) = r ^ ((d : ℝ) - σ) * ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-σ) := by
  unfold regh_ind1
  rw [integral_indicator measurableSet_ball, regh_ball_scale hr]

lemma regh_ind2_integral {p r : ℝ} (hr : 0 < r) :
    ∫ z, regh_ind2 p r (z : Euc d) = r ^ ((d : ℝ) - p) * ∫ z in (ball (0 : Euc d) 1)ᶜ, ‖z‖ ^ (-p) := by
  unfold regh_ind2
  rw [integral_indicator measurableSet_ball.compl, regh_tail_scale hr]

/-- Pointwise majorant of the integrand. -/
lemma regh_Tk_pw {s σ θ : ℝ} (hs : 0 < s) (hσs : s ≤ σ) (hσ2 : σ ≤ s + 2) (hθ0 : 0 ≤ θ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {u v : E} {K c1 c3 : ℝ} (hK0 : 0 ≤ K) (hc1 : c1 = max 1 (s / 2))
    (hc3 : c3 = (s * max 2 (max 1 (s / 2 + 1))) * 2 ^ (σ + 1))
    {z h : Euc d} (hh : h ≠ 0) (hz : z ≠ 0) (hzh : z + h ≠ 0)
    (hE : ‖u - v‖ ≤ K * ‖z‖ ^ θ) :
    ‖(regh_k s (z + h) - regh_k s z) • (u - v)‖ ≤
      K * (2 * ‖h‖) ^ θ * c1 * (regh_ind1 σ (3 * ‖h‖) (z + h) + regh_ind1 σ (2 * ‖h‖) z) +
        K * c3 * ‖h‖ * regh_ind2 (σ + 1 - θ) (2 * ‖h‖) z := by
  have hρ : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [norm_smul]
  have hKz : 0 ≤ K * ‖z‖ ^ θ := mul_nonneg hK0 (Real.rpow_nonneg (norm_nonneg z) _)
  have hf₀n := regh_ind1_nonneg (d := d) σ (3 * ‖h‖) (z + h)
  have hf₁n := regh_ind1_nonneg (d := d) σ (2 * ‖h‖) z
  have hf₂n := regh_ind2_nonneg (d := d) (σ + 1 - θ) (2 * ‖h‖) z
  have hc1p : 0 ≤ c1 := by rw [hc1]; exact le_trans zero_le_one (le_max_left _ _)
  have hc3p : 0 ≤ c3 := by
    rw [hc3]
    have : 0 ≤ s * max 2 (max 1 (s / 2 + 1)) :=
      mul_nonneg hs.le (le_trans (by norm_num) (le_max_left _ _))
    positivity
  have hK2 : 0 ≤ K * (2 * ‖h‖) ^ θ * c1 :=
    mul_nonneg (mul_nonneg hK0 (Real.rpow_nonneg (by positivity) _)) hc1p
  have hK3 : 0 ≤ K * c3 * ‖h‖ := by positivity
  rcases lt_or_ge ‖z‖ (2 * ‖h‖) with hnear | hfar
  · have hzhb : ‖z + h‖ < 3 * ‖h‖ :=
      lt_of_le_of_lt (norm_add_le _ _) (by linarith)
    have e0 := regh_ind1_of_lt (σ := σ) hzhb
    have e1 := regh_ind1_of_lt (σ := σ) hnear
    obtain ⟨hk1, hk1'⟩ := regh_k_bound hs hσs hσ2 hz
    obtain ⟨hk2, hk2'⟩ := regh_k_bound hs hσs hσ2 hzh
    have hkd : ‖regh_k s (z + h) - regh_k s z‖ ≤
        c1 * (regh_ind1 σ (3 * ‖h‖) (z + h) + regh_ind1 σ (2 * ‖h‖) z) := by
      rw [Real.norm_eq_abs, abs_le, e0, e1, hc1]
      constructor <;> nlinarith
    have hzθ : ‖z‖ ^ θ ≤ (2 * ‖h‖) ^ θ := Real.rpow_le_rpow (norm_nonneg z) hnear.le hθ0
    have h1 : ‖u - v‖ ≤ K * (2 * ‖h‖) ^ θ :=
      hE.trans (mul_le_mul_of_nonneg_left hzθ hK0)
    have h2 : ‖regh_k s (z + h) - regh_k s z‖ * ‖u - v‖ ≤
        (c1 * (regh_ind1 σ (3 * ‖h‖) (z + h) + regh_ind1 σ (2 * ‖h‖) z)) * (K * (2 * ‖h‖) ^ θ) :=
      mul_le_mul hkd h1 (norm_nonneg _) (mul_nonneg hc1p (add_nonneg hf₀n hf₁n))
    have h3 : 0 ≤ K * c3 * ‖h‖ * regh_ind2 (σ + 1 - θ) (2 * ‖h‖) z := mul_nonneg hK3 hf₂n
    calc _ ≤ _ := h2
      _ = K * (2 * ‖h‖) ^ θ * c1 * (regh_ind1 σ (3 * ‖h‖) (z + h) + regh_ind1 σ (2 * ‖h‖) z) := by ring
      _ ≤ _ := le_add_of_nonneg_right h3
  · have e2 := regh_ind2_of_le (σ := σ + 1 - θ) hfar
    have hkd := regh_k_diff_far hs hσs hσ2 hfar hh
    have e3 : ‖z‖ ^ (-(σ + 1)) * ‖z‖ ^ θ = ‖z‖ ^ (-(σ + 1 - θ)) := by
      rw [← Real.rpow_add hzn]; congr 1; ring
    have h4 : ‖regh_k s (z + h) - regh_k s z‖ ≤ c3 * ‖h‖ * ‖z‖ ^ (-(σ + 1)) := by
      refine hkd.trans (le_of_eq ?_)
      rw [hc3]
    have h2 : ‖regh_k s (z + h) - regh_k s z‖ * ‖u - v‖ ≤
        (c3 * ‖h‖ * ‖z‖ ^ (-(σ + 1))) * (K * ‖z‖ ^ θ) :=
      mul_le_mul h4 hE (norm_nonneg _) (by positivity)
    have h3 : 0 ≤ K * (2 * ‖h‖) ^ θ * c1 *
        (regh_ind1 σ (3 * ‖h‖) (z + h) + regh_ind1 σ (2 * ‖h‖) z) :=
      mul_nonneg hK2 (add_nonneg hf₀n hf₁n)
    calc _ ≤ _ := h2
      _ = K * c3 * ‖h‖ * regh_ind2 (σ + 1 - θ) (2 * ‖h‖) z := by rw [e2, ← e3]; ring
      _ ≤ _ := le_add_of_nonneg_left h3

/-- Hölder gain for the localised potential. -/
theorem regh_Tk_hold {s σ θ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hσs : s ≤ σ) (hσ2 : σ ≤ s + 2) (hσd : σ < d) (hθ0 : 0 ≤ θ) (hθ : θ + ((d : ℝ) - σ) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {F : Euc d → E}, AEStronglyMeasurable F volume → ∀ {B K : ℝ}, (∀ y, ‖F y‖ ≤ B) → 0 ≤ K →
      (∀ x h, ‖F (x + h) - F x‖ ≤ K * ‖h‖ ^ θ) → ∀ x h,
      ‖regh_Tk s F (x + h) - regh_Tk s F x‖ ≤ C * K * ‖h‖ ^ (θ + ((d : ℝ) - σ)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (d : ℝ) - σ := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; linarith
  obtain ⟨c1, hc1⟩ : ∃ c : ℝ, c = max 1 (s / 2) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c : ℝ, c = (s * max 2 (max 1 (s / 2 + 1))) * 2 ^ (σ + 1) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-σ) := ⟨_, rfl⟩
  obtain ⟨J', hJ'⟩ : ∃ J : ℝ, J = ∫ z in (ball (0 : Euc d) 1)ᶜ, ‖z‖ ^ (-(σ + 1 - θ)) := ⟨_, rfl⟩
  have hc1p : 0 ≤ c1 := by rw [hc1]; exact le_trans zero_le_one (le_max_left _ _)
  have hc3p : 0 ≤ c3 := by
    rw [hc3]
    have : 0 ≤ s * max 2 (max 1 (s / 2 + 1)) :=
      mul_nonneg hs.le (le_trans (by norm_num) (le_max_left _ _))
    positivity
  have hJp : 0 ≤ J := by
    rw [hJ]; exact setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg z) _
  have hJ'p : 0 ≤ J' := by
    rw [hJ']
    exact setIntegral_nonneg measurableSet_ball.compl fun z _ => Real.rpow_nonneg (norm_nonneg z) _
  have hp : (d : ℝ) < σ + 1 - θ := by linarith
  have hCp : 0 ≤ 2 ^ θ * c1 * (3 ^ a + 2 ^ a) * J + c3 * 2 ^ (a - 1 + θ) * J' := by positivity
  refine ⟨2 ^ θ * c1 * (3 ^ a + 2 ^ a) * J + c3 * 2 ^ (a - 1 + θ) * J', hCp, ?_⟩
  intro E _ _ _ F hm B K hB hK0 hK x h
  rw [← ha]
  by_cases hh : h = 0
  · subst hh
    simp only [add_zero, sub_self, norm_zero]
    rw [Real.zero_rpow (by linarith)]; simp
  have hρ : 0 < ‖h‖ := norm_pos_iff.2 hh
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ‖h‖ := ⟨_, rfl⟩
  rw [← hρdef] at hρ ⊢
  have hf₀i := regh_ind1_integrable (d := d) hd1 hσd (by positivity : (0 : ℝ) < 3 * ρ)
  have hf₁i := regh_ind1_integrable (d := d) hd1 hσd (by positivity : (0 : ℝ) < 2 * ρ)
  have hf₂i := regh_ind2_integrable (d := d) hp (by positivity : (0 : ℝ) < 2 * ρ)
  have hI₀ : ∫ z : Euc d, regh_ind1 σ (3 * ρ) (z + h) = (3 * ρ) ^ a * J := by
    rw [integral_add_right_eq_self (μ := volume) (regh_ind1 σ (3 * ρ)) h,
      regh_ind1_integral (by positivity), ha, hJ]
  have hI₁ : ∫ z : Euc d, regh_ind1 σ (2 * ρ) z = (2 * ρ) ^ a * J := by
    rw [regh_ind1_integral (by positivity), ha, hJ]
  have hI₂ : ∫ z : Euc d, regh_ind2 (σ + 1 - θ) (2 * ρ) z = (2 * ρ) ^ (a - 1 + θ) * J' := by
    rw [regh_ind2_integral (by positivity), hJ']
    congr 2; rw [ha]; ring
  obtain ⟨m, hmdef⟩ : ∃ m : Euc d → ℝ, m = fun z => K * (2 * ρ) ^ θ * c1 *
      (regh_ind1 σ (3 * ρ) (z + h) + regh_ind1 σ (2 * ρ) z) +
        K * c3 * ρ * regh_ind2 (σ + 1 - θ) (2 * ρ) z := ⟨_, rfl⟩
  have hmi : Integrable m := by
    rw [hmdef]
    exact (((hf₀i.comp_add_right h).add hf₁i).const_mul _).add (hf₂i.const_mul _)
  have hmint : ∫ z, m z = K * (2 * ρ) ^ θ * c1 * ((3 * ρ) ^ a * J + (2 * ρ) ^ a * J) +
      K * c3 * ρ * ((2 * ρ) ^ (a - 1 + θ) * J') := by
    have h0 : Integrable (fun z : Euc d => regh_ind1 σ (3 * ρ) (z + h) + regh_ind1 σ (2 * ρ) z) :=
      (hf₀i.comp_add_right h).add hf₁i
    have h1 : Integrable (fun z : Euc d => K * (2 * ρ) ^ θ * c1 *
        (regh_ind1 σ (3 * ρ) (z + h) + regh_ind1 σ (2 * ρ) z)) := h0.const_mul _
    have h2 : Integrable (fun z : Euc d => K * c3 * ρ * regh_ind2 (σ + 1 - θ) (2 * ρ) z) :=
      hf₂i.const_mul _
    have e : ∫ z, m z = ∫ z, (K * (2 * ρ) ^ θ * c1 *
        (regh_ind1 σ (3 * ρ) (z + h) + regh_ind1 σ (2 * ρ) z) +
        K * c3 * ρ * regh_ind2 (σ + 1 - θ) (2 * ρ) z) := by rw [hmdef]
    rw [e, integral_add h1 h2, integral_const_mul, integral_const_mul,
      integral_add (hf₀i.comp_add_right h) hf₁i, hI₀, hI₁, hI₂]
  -- pointwise bound
  have hbd : ∀ᵐ z : Euc d, ‖(regh_k s (z + h) - regh_k s z) • (F (x - z) - F x)‖ ≤ m z := by
    have hzh : ∀ᵐ z : Euc d, z + h ≠ 0 :=
      (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (regh_ae_ne hd1)
    filter_upwards [regh_ae_ne hd1, hzh] with z hz hzh'
    have hE : ‖F (x - z) - F x‖ ≤ K * ‖z‖ ^ θ := by
      have := hK x (-z)
      rw [norm_neg] at this
      simpa [sub_eq_add_neg] using this
    rw [hmdef]
    have := regh_Tk_pw (d := d) hs hσs hσ2 hθ0 (u := F (x - z)) (v := F x) (K := K) hK0 hc1 hc3
      (z := z) (h := h) hh hz hzh' hE
    rwa [← hρdef] at this
  -- conclude
  rw [regh_Tk_diff_eq hd1 hs hsd hs2 hm hB x h]
  refine (norm_integral_le_of_norm_le hmi hbd).trans ?_
  rw [hmint]
  have r2 : (2 * ρ) ^ θ = 2 ^ θ * ρ ^ θ := Real.mul_rpow (by norm_num) hρ.le
  have r3 : (3 * ρ) ^ a = 3 ^ a * ρ ^ a := Real.mul_rpow (by norm_num) hρ.le
  have r4 : (2 * ρ) ^ a = 2 ^ a * ρ ^ a := Real.mul_rpow (by norm_num) hρ.le
  have r5 : (2 * ρ) ^ (a - 1 + θ) = 2 ^ (a - 1 + θ) * ρ ^ (a - 1 + θ) :=
    Real.mul_rpow (by norm_num) hρ.le
  have r6 : ρ ^ (θ + a) = ρ ^ θ * ρ ^ a := Real.rpow_add hρ _ _
  have r7 : ρ ^ (θ + a) = ρ * ρ ^ (a - 1 + θ) := by
    have := Real.rpow_add hρ 1 (a - 1 + θ)
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  apply le_of_eq
  rw [r2, r3, r4, r5]
  linear_combination (-(2 ^ θ * c1 * (3 ^ a + 2 ^ a) * J * K)) * r6 +
    (-(c3 * 2 ^ (a - 1 + θ) * J' * K)) * r7

lemma regh_gE_lip {s : ℝ} (hs : 0 < s) (z h : Euc d) :
    ‖rege_gE s 1 (z + h) - rege_gE s 1 z‖ ≤ s * ‖h‖ := by
  have hb : ∀ w ∈ (Set.univ : Set (Euc d)), ‖rege_L s (rege_kE s 1 w)‖ ≤ s := by
    intro w _
    rw [rege_L_norm hs.le]
    have := rege_kE_le (d := d) hs one_pos w
    simp only [Real.one_rpow] at this
    nlinarith
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ) (f := rege_gE s 1)
    (f' := fun w => rege_L s (rege_kE s 1 w)) (s := Set.univ) (x := z) (y := z + h)
    (fun w _ => by
      have := rege_gE_hasFDerivAt (s := s) (ε := 1) one_pos 0 w
      simp only [sub_zero] at this
      exact this.hasFDerivWithinAt) hb convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa [add_sub_cancel_left, mul_comm] using this

lemma regh_T1_lip {s : ℝ} (hs : 0 < s) {F : Euc d → E} (hm : AEStronglyMeasurable F volume)
    (hI : Integrable F) (x h : Euc d) :
    ‖regh_T1 s F (x + h) - regh_T1 s F x‖ ≤ s * ‖h‖ * ∫ y, ‖F y‖ := by
  have hint1 := regh_T1_integrable hs hm hI x
  have hint0 := regh_T1_integrable hs hm hI (x + h)
  have hint2 : Integrable (fun z => rege_gE s 1 (z + h) • F (x - z)) := by
    refine (hint0.comp_add_right h).congr (Eventually.of_forall fun z => ?_)
    simp only [add_sub_add_right_eq_sub]
  have e1 : regh_T1 s F (x + h) = ∫ z, rege_gE s 1 (z + h) • F (x - z) := by
    unfold regh_T1
    rw [← integral_add_right_eq_self (μ := volume) (fun z => rege_gE s 1 z • F (x + h - z)) h]
    simp only [add_sub_add_right_eq_sub]
  have e2 : regh_T1 s F (x + h) - regh_T1 s F x =
      ∫ z, (rege_gE s 1 (z + h) - rege_gE s 1 z) • F (x - z) := by
    rw [e1]; unfold regh_T1
    rw [← integral_sub hint2 hint1]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [sub_smul]
  have hFi : Integrable (fun z => ‖F (x - z)‖) := hI.norm.comp_sub_left x
  rw [e2]
  refine (norm_integral_le_of_norm_le (hFi.const_mul (s * ‖h‖)) (ae_of_all _ fun z => ?_)).trans ?_
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (regh_gE_lip hs z h) (norm_nonneg _)
  · rw [integral_const_mul, integral_sub_left_eq_self (fun z : Euc d => ‖F z‖) volume x]

/-- Hölder gain for the full potential `T F`. -/
theorem regh_T_hold {s σ θ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hσs : s ≤ σ) (hσ2 : σ ≤ s + 2) (hσd : σ < d) (hθ0 : 0 ≤ θ) (hθ : θ + ((d : ℝ) - σ) < 1)
    {F : Euc d → E} (hm : AEStronglyMeasurable F volume) (hR : lreg_RDec F) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x h, ‖F (x + h) - F x‖ ≤ K * ‖h‖ ^ θ) :
    (∃ B : ℝ, ∀ x, ‖regh_T s F x‖ ≤ B) ∧
      ∃ K' : ℝ, 0 ≤ K' ∧ ∀ x h, ‖regh_T s F (x + h) - regh_T s F x‖ ≤
        K' * ‖h‖ ^ (θ + ((d : ℝ) - σ)) := by
  obtain ⟨C, hC0, hC⟩ := regh_Tk_hold (d := d) hd1 hs hsd hs2 hσs hσ2 hσd hθ0 hθ
  obtain ⟨C0, hC00, h0⟩ := lreg_bound_of_rdec hR 0
  have hb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using h0 y
  have hB : ∀ y, ‖F y‖ ≤ C0 := fun y => (hb y).trans (by nlinarith [lreg_phi_le_one (d := d) y])
  have hFi : Integrable F := lreg_integrable_of_bound hm hb
  have hTb : ∀ x, ‖regh_T s F x‖ ≤ C0 * lreg_A d s := fun x =>
    (regh_T_integrable hd1 hs hsd hm hC00 hb x).2
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ y, ‖F y‖ := ⟨_, rfl⟩
  obtain ⟨TA, hTAdef⟩ : ∃ T : ℝ, T = C0 * lreg_A d s := ⟨_, rfl⟩
  have hI : 0 ≤ I := by rw [hIdef]; exact integral_nonneg fun _ => norm_nonneg _
  have hTA : 0 ≤ TA := by rw [hTAdef]; exact mul_nonneg hC00 lreg_A_nonneg
  have hTb' : ∀ x, ‖regh_T s F x‖ ≤ TA := fun x => by rw [hTAdef]; exact hTb x
  refine ⟨⟨TA, hTb'⟩, C * K + s * I + 2 * TA, by positivity, fun x h => ?_⟩
  have hTeq := regh_T_eq hd1 hs hsd hs2 hm hR
  have hKtk := hC hm hB hK0 hK x h
  have hT1 := regh_T1_lip hs hm hFi x h
  rw [← hIdef] at hT1
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ‖h‖ ^ (θ + ((d : ℝ) - σ)) := ⟨_, rfl⟩
  have hq : (0 : ℝ) < θ + ((d : ℝ) - σ) := by linarith
  have hq1 : θ + ((d : ℝ) - σ) ≤ 1 := hθ.le
  have hP0 : 0 ≤ P := by rw [hPdef]; exact Real.rpow_nonneg (norm_nonneg h) _
  rw [← hPdef] at hKtk ⊢
  have hCK : 0 ≤ C * K := mul_nonneg hC0 hK0
  have hsplit : regh_T s F (x + h) - regh_T s F x =
      (regh_Tk s F (x + h) - regh_Tk s F x) + (regh_T1 s F (x + h) - regh_T1 s F x) := by
    rw [hTeq]; simp only; abel
  rcases le_or_gt ‖h‖ 1 with hh | hh
  · have hpow : ‖h‖ ≤ P := by
      rw [hPdef]
      rcases eq_or_lt_of_le (norm_nonneg h) with h0' | h0'
      · rw [← h0', Real.zero_rpow hq.ne']
      · calc ‖h‖ = ‖h‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge h0' hh hq1
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h5 : s * ‖h‖ * I ≤ s * P * I := by gcongr
    have h6 : 0 ≤ TA * P := mul_nonneg hTA hP0
    have e : (C * K + s * I + 2 * TA) * P = C * K * P + s * P * I + 2 * (TA * P) := by ring
    rw [e]
    linarith
  · have hpow : 1 ≤ P := by rw [hPdef]; exact Real.one_le_rpow hh.le hq.le
    have h2 : ‖regh_T s F (x + h) - regh_T s F x‖ ≤ 2 * TA := by
      calc _ ≤ ‖regh_T s F (x + h)‖ + ‖regh_T s F x‖ := norm_sub_le _ _
        _ ≤ TA + TA := add_le_add (hTb' _) (hTb' _)
        _ = _ := by ring
    have h3 : TA ≤ TA * P := by nlinarith
    have h4 : 0 ≤ C * K * P := mul_nonneg hCK hP0
    have h5 : 0 ≤ s * P * I := mul_nonneg (mul_nonneg hs.le hP0) hI
    have e : (C * K + s * I + 2 * TA) * P = C * K * P + s * P * I + 2 * (TA * P) := by ring
    rw [e]
    linarith

end Gain

/-! ### Second-order kernel estimates -/

lemma regh_kern_hasFDerivAt {p c : ℝ} {z : Euc d} (hA : 0 < c + ‖z‖ ^ 2) :
    HasFDerivAt (fun w : Euc d => (c + ‖w‖ ^ 2) ^ (-p) • w)
      ((c + ‖z‖ ^ 2) ^ (-p) • ContinuousLinearMap.id ℝ (Euc d) +
        ((-p) * (c + ‖z‖ ^ 2) ^ (-p - 1) * 2) • (innerSL ℝ z).smulRight z) z := by
  have h1 : HasFDerivAt (fun w : Euc d => c + ‖w‖ ^ 2) (2 • (innerSL ℝ z)) z := by
    have := ((hasFDerivAt_id z).norm_sq).const_add c
    refine this.congr_fderiv ?_
    ext w; simp
  have h2 := (Real.hasDerivAt_rpow_const (p := -p) (Or.inl hA.ne')).comp_hasFDerivAt z h1
  have h3 := h2.smul (hasFDerivAt_id z)
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun w => ?_
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, id, nsmul_eq_mul, Nat.cast_ofNat,
    Function.comp_apply, innerSL_apply_apply]
  rw [mul_assoc, mul_assoc, smul_smul]
  congr 2
  ring

/-- Derivative of the kernel `(c + ‖w‖²)^{-p} w`. -/
def regh_Dk (p c : ℝ) (z : Euc d) : Euc d →L[ℝ] Euc d :=
  (c + ‖z‖ ^ 2) ^ (-p) • ContinuousLinearMap.id ℝ (Euc d) +
    ((-p) * (c + ‖z‖ ^ 2) ^ (-p - 1) * 2) • (innerSL ℝ z).smulRight z

lemma regh_kern_hasFDerivAt' {p c : ℝ} {z : Euc d} (hA : 0 < c + ‖z‖ ^ 2) :
    HasFDerivAt (fun w : Euc d => (c + ‖w‖ ^ 2) ^ (-p) • w) (regh_Dk p c z) z :=
  regh_kern_hasFDerivAt hA

lemma regh_Dk_norm_le {p c : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) {z : Euc d} (hA : 0 < c + ‖z‖ ^ 2) :
    ‖regh_Dk p c z‖ ≤ (1 + 2 * p) * (c + ‖z‖ ^ 2) ^ (-p) := by
  unfold regh_Dk
  refine (norm_add_le _ _).trans ?_
  have hA0 : 0 ≤ (c + ‖z‖ ^ 2) ^ (-p) := Real.rpow_nonneg hA.le _
  have h1 : ‖(c + ‖z‖ ^ 2) ^ (-p) • ContinuousLinearMap.id ℝ (Euc d)‖ ≤ (c + ‖z‖ ^ 2) ^ (-p) := by
    rw [norm_smul, Real.norm_of_nonneg hA0]
    calc _ ≤ (c + ‖z‖ ^ 2) ^ (-p) * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hA0
      _ = _ := mul_one _
  have h2 : ‖((-p) * (c + ‖z‖ ^ 2) ^ (-p - 1) * 2) • (innerSL ℝ z).smulRight z‖ ≤
      2 * p * (c + ‖z‖ ^ 2) ^ (-p) := by
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    have e : ‖(-p) * (c + ‖z‖ ^ 2) ^ (-p - 1) * 2‖ = 2 * p * (c + ‖z‖ ^ 2) ^ (-p - 1) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg hp,
        abs_of_nonneg (Real.rpow_nonneg hA.le _), abs_two]; ring
    rw [e]
    have e2 : (c + ‖z‖ ^ 2) ^ (-p) = (c + ‖z‖ ^ 2) ^ (-p - 1) * (c + ‖z‖ ^ 2) := by
      have := Real.rpow_add hA (-p - 1) 1
      rw [Real.rpow_one] at this
      rw [← this]; congr 1; ring
    have h3 : ‖z‖ * ‖z‖ ≤ c + ‖z‖ ^ 2 := by nlinarith
    have h4 : 0 ≤ (c + ‖z‖ ^ 2) ^ (-p - 1) := Real.rpow_nonneg hA.le _
    calc 2 * p * (c + ‖z‖ ^ 2) ^ (-p - 1) * (‖z‖ * ‖z‖)
        ≤ 2 * p * (c + ‖z‖ ^ 2) ^ (-p - 1) * (c + ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * p * (c + ‖z‖ ^ 2) ^ (-p) := by rw [e2]; ring
  linarith

lemma regh_kern_pow_le {p c : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) {z : Euc d} (hz : z ≠ 0) :
    (c + ‖z‖ ^ 2) ^ (-p) ≤ ‖z‖ ^ (-(2 * p)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have : (‖z‖ ^ 2) ^ (-p) = ‖z‖ ^ (-(2 * p)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  rw [← this]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

lemma regh_kap_eq (s : ℝ) :
    (rege_kap s : Euc d → Euc d) = fun w => ((0 : ℝ) + ‖w‖ ^ 2) ^ (-(s / 2 + 1)) • w := by
  funext w
  unfold rege_kap
  by_cases hw : w = 0
  · simp [hw]
  · have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
    congr 1
    rw [zero_add, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring

/-- The gradient `kD = ∇k` of the localised kernel, as a continuous linear form. -/
def regh_kD (s : ℝ) (w : Euc d) : Euc d →L[ℝ] ℝ := rege_L s (rege_kap s w - rege_kE s 1 w)

/-- The Hessian of the localised kernel. -/
def regh_DkD (s : ℝ) (w : Euc d) : Euc d →L[ℝ] Euc d →L[ℝ] ℝ :=
  (rege_L s : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).comp (regh_Dk (s / 2 + 1) 0 w - regh_Dk (s / 2 + 1) 1 w)

lemma regh_kD_hasFDerivAt {s : ℝ} {w : Euc d} (hw : w ≠ 0) :
    HasFDerivAt (regh_kD s) (regh_DkD s w) w := by
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 : HasFDerivAt (rege_kap s : Euc d → Euc d) (regh_Dk (s / 2 + 1) 0 w) w := by
    rw [regh_kap_eq]
    exact regh_kern_hasFDerivAt' (by positivity)
  have h2 : HasFDerivAt (rege_kE s 1 : Euc d → Euc d) (regh_Dk (s / 2 + 1) 1 w) w := by
    have e : (rege_kE s 1 : Euc d → Euc d) =
        fun w => ((1 : ℝ) + ‖w‖ ^ 2) ^ (-(s / 2 + 1)) • w := by
      funext w; simp [rege_kE]
    rw [e]
    exact regh_kern_hasFDerivAt' (c := 1) (by positivity)
  exact (rege_L s : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).hasFDerivAt.comp w (h1.sub h2)

lemma regh_DkD_norm_le {s : ℝ} (hs : 0 < s) {w : Euc d} (hw : w ≠ 0) :
    ‖regh_DkD s w‖ ≤ (2 * s * (s + 3)) * ‖w‖ ^ (-(s + 2)) := by
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hp : 0 ≤ s / 2 + 1 := by positivity
  have h1 := regh_Dk_norm_le (d := d) hp le_rfl (z := w) (c := 0) (by positivity)
  have h2 := regh_Dk_norm_le (d := d) hp zero_le_one (z := w) (c := 1) (by positivity)
  have h3 := regh_kern_pow_le (d := d) hp le_rfl hw
  have h4 := regh_kern_pow_le (d := d) hp zero_le_one hw
  have e : -(2 * (s / 2 + 1)) = -(s + 2) := by ring
  rw [e] at h3 h4
  have e2 : 1 + 2 * (s / 2 + 1) = s + 3 := by ring
  rw [e2] at h1 h2
  unfold regh_DkD
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hL := rege_L_opnorm (d := d) hs.le
  have hsub : ‖regh_Dk (s / 2 + 1) 0 w - regh_Dk (s / 2 + 1) 1 w‖ ≤
      (s + 3) * ‖w‖ ^ (-(s + 2)) * 2 := by
    refine (norm_sub_le _ _).trans ?_
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ s + 3)
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ s + 3)
    linarith
  calc _ ≤ s * ((s + 3) * ‖w‖ ^ (-(s + 2)) * 2) := by
        refine mul_le_mul hL hsub (norm_nonneg _) hs.le
    _ = _ := by ring

lemma regh_seg_norm {z h : Euc d} (hzh : 2 * ‖h‖ ≤ ‖z‖) (hh : h ≠ 0) :
    ∀ w ∈ segment ℝ z (z + h), ‖z‖ / 2 ≤ ‖w‖ ∧ ‖w - z‖ ≤ ‖h‖ := by
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  intro w hw
  rw [segment_eq_image'] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  simp only [add_sub_cancel_left]
  have h2 : ‖t • h‖ ≤ ‖h‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  refine ⟨?_, by simpa using h2⟩
  have h1 : ‖z‖ - ‖t • h‖ ≤ ‖z + t • h‖ := by
    have := norm_sub_norm_le z (-(t • h))
    simpa [sub_neg_eq_add, norm_neg] using this
  linarith

lemma regh_kD_diff_le {s : ℝ} (hs : 0 < s) {z h : Euc d} (hzh : 2 * ‖h‖ ≤ ‖z‖) (hh : h ≠ 0) :
    ∀ w ∈ segment ℝ z (z + h), ‖regh_kD s w - regh_kD s z‖ ≤
      ((2 * s * (s + 3)) * 2 ^ (s + 2) * ‖z‖ ^ (-(s + 2))) * ‖w - z‖ := by
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hzn : 0 < ‖z‖ := by linarith
  intro w hw
  have hsub : segment ℝ z w ⊆ segment ℝ z (z + h) :=
    (convex_segment z (z + h)).segment_subset (left_mem_segment _ _ _) hw
  have hbd : ∀ u ∈ segment ℝ z w, ‖regh_DkD s u‖ ≤ (2 * s * (s + 3)) * 2 ^ (s + 2) * ‖z‖ ^ (-(s + 2)) := by
    intro u hu
    have hu2 := (regh_seg_norm hzh hh u (hsub hu)).1
    have hun : 0 < ‖u‖ := by linarith
    refine (regh_DkD_norm_le hs (norm_pos_iff.1 hun)).trans ?_
    have h1 : ‖u‖ ^ (-(s + 2)) ≤ (‖z‖ / 2) ^ (-(s + 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hu2 (by linarith)
    have h2 : (‖z‖ / 2) ^ (-(s + 2)) = 2 ^ (s + 2) * ‖z‖ ^ (-(s + 2)) := by
      rw [Real.div_rpow hzn.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_eq_mul_inv, inv_inv, mul_comm]
    calc (2 * s * (s + 3)) * ‖u‖ ^ (-(s + 2)) ≤ (2 * s * (s + 3)) * (2 ^ (s + 2) * ‖z‖ ^ (-(s + 2))) := by
          rw [← h2]; gcongr
      _ = _ := by ring
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ) (f := regh_kD s)
    (f' := regh_DkD s) (s := segment ℝ z w) (x := z) (y := w)
    (fun u hu => (regh_kD_hasFDerivAt (s := s)
      (norm_pos_iff.1 (by linarith [(regh_seg_norm hzh hh u (hsub hu)).1] : 0 < ‖u‖))).hasFDerivWithinAt)
    hbd (convex_segment _ _) (left_mem_segment _ _ _) (right_mem_segment _ _ _)

/-- Second-order Taylor estimate for the localised kernel (away from the singularity). -/
lemma regh_k_taylor {s : ℝ} (hs : 0 < s) {z h : Euc d} (hzh : 2 * ‖h‖ ≤ ‖z‖) (hh : h ≠ 0) :
    ‖regh_k s (z + h) - regh_k s z - regh_kD s z h‖ ≤
      ((2 * s * (s + 3)) * 2 ^ (s + 2)) * ‖h‖ ^ 2 * ‖z‖ ^ (-(s + 2)) := by
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hzn : 0 < ‖z‖ := by linarith
  have hdiff := regh_kD_diff_le hs hzh hh
  have hbd : ∀ w ∈ segment ℝ z (z + h),
      ‖regh_kD s w - regh_kD s z‖ ≤ ((2 * s * (s + 3)) * 2 ^ (s + 2) * ‖z‖ ^ (-(s + 2))) * ‖h‖ := by
    intro w hw
    refine (hdiff w hw).trans ?_
    exact mul_le_mul_of_nonneg_left (regh_seg_norm hzh hh w hw).2 (by positivity)
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ)
    (f := fun w => regh_k s w - regh_kD s z w)
    (f' := fun w => regh_kD s w - regh_kD s z) (s := segment ℝ z (z + h)) (x := z) (y := z + h)
    (fun w hw => by
      have hw0 : w ≠ 0 := norm_pos_iff.1 (by linarith [(regh_seg_norm hzh hh w hw).1] : 0 < ‖w‖)
      exact ((regh_k_hasFDerivAt (s := s) hw0).sub ((regh_kD s z).hasFDerivAt)).hasFDerivWithinAt)
    hbd (convex_segment _ _) (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  simp only [add_sub_cancel_left, map_add] at this
  have e : regh_k s (z + h) - (regh_kD s z z + regh_kD s z h) - (regh_k s z - regh_kD s z z) =
      regh_k s (z + h) - regh_k s z - regh_kD s z h := by ring
  rw [e] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-! ### Differentiability of the localised potential -/

section Cross

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma regh_Tk_diff_integrable {s : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    {F : Euc d → E} (hm : AEStronglyMeasurable F volume) {B : ℝ} (hB : ∀ y, ‖F y‖ ≤ B) (x h : Euc d) :
    Integrable (fun z => (regh_k s (z + h) - regh_k s z) • (F (x - z) - F x)) := by
  have hk := regh_k_integrable hd1 hs hsd hs2
  have hint1 := regh_Tk_integrable hd1 hs hsd hs2 hm hB x
  have hint0 := regh_Tk_integrable hd1 hs hsd hs2 hm hB (x + h)
  have hint2 : Integrable (fun z => regh_k s (z + h) • F (x - z)) := by
    have := hint0.comp_add_right h
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [add_sub_add_right_eq_sub]
  have hA : Integrable (fun z => (regh_k s (z + h) - regh_k s z) • F (x - z)) := by
    refine (hint2.sub hint1).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply, sub_smul]
  have hB' : Integrable (fun z => (regh_k s (z + h) - regh_k s z) • F x) :=
    ((hk.comp_add_right h).sub hk).smul_const _
  refine (hA.sub hB').congr (Eventually.of_forall fun z => ?_)
  simp only [Pi.sub_apply, smul_sub]

/-- Candidate derivative of the localised potential. -/
def regh_Pk (s : ℝ) (F : Euc d → E) (x : Euc d) : Euc d →L[ℝ] E :=
  ∫ z, (regh_kD s z).smulRight (F (x - z) - F x)

lemma regh_kD_bound {s σ : ℝ} (hs : 0 < s) (hσs : s ≤ σ) (hσ2 : σ ≤ s + 2) {z : Euc d} (hz : z ≠ 0) :
    ‖regh_kD s z‖ ≤ (s * max 2 (max 1 (s / 2 + 1))) * ‖z‖ ^ (-(σ + 1)) :=
  regh_k_grad_bound hs hσs hσ2 hz

lemma regh_kD_measurable (s : ℝ) : Measurable (regh_kD s : Euc d → Euc d →L[ℝ] ℝ) := by
  unfold regh_kD
  exact (rege_L s : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).continuous.measurable.comp
    ((rege_kap_measurable s).sub (rege_kE_continuous (s := s) one_pos).measurable)

lemma regh_Pk_integrable_aux {s θ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hθ0 : 0 ≤ θ)
    (hθ1 : s + 1 - θ < d) (hs3 : (d : ℝ) < s + 3) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {F : Euc d → E}, AEStronglyMeasurable F volume → ∀ {B K : ℝ}, (∀ y, ‖F y‖ ≤ B) → 0 ≤ K →
      ∀ x, (∀ z, ‖F (x - z) - F x‖ ≤ K * ‖z‖ ^ θ) →
      Integrable (fun z => (regh_kD s z).smulRight (F (x - z) - F x)) ∧
        ‖regh_Pk s F x‖ ≤ C₁ * K + C₂ * B := by
  obtain ⟨c2, hc2⟩ : ∃ c : ℝ, c = s * max 2 (max 1 (s / 2 + 1)) := ⟨_, rfl⟩
  obtain ⟨J₁, hJ₁⟩ : ∃ J : ℝ, J = ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-(s + 1 - θ)) := ⟨_, rfl⟩
  obtain ⟨J₂, hJ₂⟩ : ∃ J : ℝ, J = ∫ z in (ball (0 : Euc d) 1)ᶜ, ‖z‖ ^ (-(s + 3)) := ⟨_, rfl⟩
  have hc2p : 0 ≤ c2 := by
    rw [hc2]; exact mul_nonneg hs.le (le_trans (by norm_num) (le_max_left _ _))
  have hJ₁p : 0 ≤ J₁ := by
    rw [hJ₁]; exact setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg z) _
  have hJ₂p : 0 ≤ J₂ := by
    rw [hJ₂]
    exact setIntegral_nonneg measurableSet_ball.compl fun z _ => Real.rpow_nonneg (norm_nonneg z) _
  refine ⟨c2 * J₁, c2 * (2 * J₂), by positivity, by positivity, ?_⟩
  intro E _ _ _ F hm B K hB hK0 x hE
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hf₁i := regh_ind1_integrable (d := d) (σ := s + 1 - θ) hd1 hθ1 one_pos
  have hf₂i := regh_ind2_integrable (d := d) (p := s + 3) (r := 1) hs3 one_pos
  have hmi : Integrable (fun z : Euc d => c2 * K * regh_ind1 (s + 1 - θ) 1 z +
      c2 * (2 * B) * regh_ind2 (s + 3) 1 z) := (hf₁i.const_mul _).add (hf₂i.const_mul _)
  have hmeas : AEStronglyMeasurable (fun z : Euc d => (regh_kD s z).smulRight (F (x - z) - F x))
      volume := by
    have h1 : AEStronglyMeasurable (regh_kD s : Euc d → Euc d →L[ℝ] ℝ) volume :=
      (regh_kD_measurable s).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun z : Euc d => F (x - z) - F x) volume :=
      ((hm.comp_measurePreserving (volume.measurePreserving_sub_left x))).sub aestronglyMeasurable_const
    exact (ContinuousLinearMap.smulRightL ℝ (Euc d) E).aestronglyMeasurable_comp₂ h1 h2
  have hbd : ∀ᵐ z : Euc d, ‖(regh_kD s z).smulRight (F (x - z) - F x)‖ ≤
      c2 * K * regh_ind1 (s + 1 - θ) 1 z + c2 * (2 * B) * regh_ind2 (s + 3) 1 z := by
    filter_upwards [regh_ae_ne hd1] with z hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have hf₁n := regh_ind1_nonneg (d := d) (s + 1 - θ) 1 z
    have hf₂n := regh_ind2_nonneg (d := d) (s + 3) 1 z
    rcases lt_or_ge ‖z‖ 1 with hnear | hfar
    · have e1 := regh_ind1_of_lt (σ := s + 1 - θ) hnear
      have h1 := regh_kD_bound hs le_rfl (by linarith : s ≤ s + 2) hz
      rw [← hc2] at h1
      have e3 : ‖z‖ ^ (-(s + 1)) * ‖z‖ ^ θ = ‖z‖ ^ (-(s + 1 - θ)) := by
        rw [← Real.rpow_add hzn]; congr 1; ring
      calc ‖regh_kD s z‖ * ‖F (x - z) - F x‖ ≤ (c2 * ‖z‖ ^ (-(s + 1))) * (K * ‖z‖ ^ θ) :=
            mul_le_mul h1 (hE z) (norm_nonneg _) (by positivity)
        _ = c2 * K * ‖z‖ ^ (-(s + 1 - θ)) := by rw [← e3]; ring
        _ = c2 * K * regh_ind1 (s + 1 - θ) 1 z := by rw [e1]
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (mul_nonneg hc2p (by positivity)) hf₂n)
    · have e2 := regh_ind2_of_le (σ := s + 3) hfar
      have h1 := regh_kD_bound hs (by linarith : s ≤ s + 2) le_rfl hz
      rw [← hc2] at h1
      have hE2 : ‖F (x - z) - F x‖ ≤ 2 * B := by
        calc _ ≤ ‖F (x - z)‖ + ‖F x‖ := norm_sub_le _ _
          _ ≤ B + B := add_le_add (hB _) (hB _)
          _ = _ := by ring
      have e4 : s + 2 + 1 = s + 3 := by ring
      rw [e4] at h1
      calc ‖regh_kD s z‖ * ‖F (x - z) - F x‖ ≤ (c2 * ‖z‖ ^ (-(s + 3))) * (2 * B) :=
            mul_le_mul h1 hE2 (norm_nonneg _) (by positivity)
        _ = c2 * (2 * B) * ‖z‖ ^ (-(s + 3)) := by ring
        _ = c2 * (2 * B) * regh_ind2 (s + 3) 1 z := by rw [e2]
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (mul_nonneg hc2p hK0) hf₁n)
  refine ⟨hmi.mono' hmeas hbd, ?_⟩
  unfold regh_Pk
  refine (norm_integral_le_of_norm_le hmi hbd).trans (le_of_eq ?_)
  rw [integral_add (hf₁i.const_mul _) (hf₂i.const_mul _), integral_const_mul, integral_const_mul,
    regh_ind1_integral one_pos, regh_ind2_integral one_pos, Real.one_rpow, Real.one_rpow, one_mul,
    one_mul, ← hJ₁, ← hJ₂]
  ring

lemma regh_Tk_rem_pw {s θ : ℝ} (hs : 0 < s) (hθ0 : 0 ≤ θ)
    {u v : E} {K c1 c2 c4 : ℝ} (hK0 : 0 ≤ K) (hc1 : c1 = max 1 (s / 2))
    (hc2 : c2 = s * max 2 (max 1 (s / 2 + 1))) (hc4 : c4 = (2 * s * (s + 3)) * 2 ^ (s + 2))
    {z h : Euc d} (hh : h ≠ 0) (hz : z ≠ 0) (hzh : z + h ≠ 0) (hE : ‖u - v‖ ≤ K * ‖z‖ ^ θ) :
    ‖(regh_k s (z + h) - regh_k s z - regh_kD s z h) • (u - v)‖ ≤
      K * (2 * ‖h‖) ^ θ * c1 * (regh_ind1 s (3 * ‖h‖) (z + h) + regh_ind1 s (2 * ‖h‖) z) +
        K * c2 * ‖h‖ * regh_ind1 (s + 1 - θ) (2 * ‖h‖) z +
        K * c4 * ‖h‖ ^ 2 * regh_ind2 (s + 2 - θ) (2 * ‖h‖) z := by
  have hρ : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [norm_smul]
  have hf₀n := regh_ind1_nonneg (d := d) s (3 * ‖h‖) (z + h)
  have hf₁n := regh_ind1_nonneg (d := d) s (2 * ‖h‖) z
  have hf₃n := regh_ind1_nonneg (d := d) (s + 1 - θ) (2 * ‖h‖) z
  have hf₂n := regh_ind2_nonneg (d := d) (s + 2 - θ) (2 * ‖h‖) z
  have hc1p : 0 ≤ c1 := by rw [hc1]; exact le_trans zero_le_one (le_max_left _ _)
  have hc2p : 0 ≤ c2 := by
    rw [hc2]; exact mul_nonneg hs.le (le_trans (by norm_num) (le_max_left _ _))
  have hc4p : 0 ≤ c4 := by rw [hc4]; positivity
  have hK2 : 0 ≤ K * (2 * ‖h‖) ^ θ * c1 :=
    mul_nonneg (mul_nonneg hK0 (Real.rpow_nonneg (by positivity) _)) hc1p
  have hK3 : 0 ≤ K * c2 * ‖h‖ := by positivity
  have hK4 : 0 ≤ K * c4 * ‖h‖ ^ 2 := by positivity
  rcases lt_or_ge ‖z‖ (2 * ‖h‖) with hnear | hfar
  · have hzhb : ‖z + h‖ < 3 * ‖h‖ := lt_of_le_of_lt (norm_add_le _ _) (by linarith)
    have e0 := regh_ind1_of_lt (σ := s) hzhb
    have e1 := regh_ind1_of_lt (σ := s) hnear
    have e3 := regh_ind1_of_lt (σ := s + 1 - θ) hnear
    obtain ⟨hk1, hk1'⟩ := regh_k_bound hs le_rfl (by linarith : s ≤ s + 2) hz
    obtain ⟨hk2, hk2'⟩ := regh_k_bound hs le_rfl (by linarith : s ≤ s + 2) hzh
    rw [← hc1, ← e1] at hk1'
    rw [← hc1, ← e0] at hk2'
    have hkD := regh_kD_bound hs le_rfl (by linarith : s ≤ s + 2) hz
    have hkDh : |regh_kD s z h| ≤ c2 * ‖z‖ ^ (-(s + 1)) * ‖h‖ := by
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [hc2]
      exact mul_le_mul_of_nonneg_right hkD (norm_nonneg _)
    have hkDh' := abs_le.1 hkDh
    have hW : |regh_k s (z + h) - regh_k s z - regh_kD s z h| ≤
        c1 * regh_ind1 s (3 * ‖h‖) (z + h) + c1 * regh_ind1 s (2 * ‖h‖) z +
          c2 * ‖z‖ ^ (-(s + 1)) * ‖h‖ := by
      have h0 : 0 ≤ c1 * regh_ind1 s (3 * ‖h‖) (z + h) := mul_nonneg hc1p hf₀n
      have h0' : 0 ≤ c1 * regh_ind1 s (2 * ‖h‖) z := mul_nonneg hc1p hf₁n
      rw [abs_le]
      constructor <;> linarith [hkDh'.1, hkDh'.2]
    have hzθ : ‖z‖ ^ θ ≤ (2 * ‖h‖) ^ θ := Real.rpow_le_rpow (norm_nonneg z) hnear.le hθ0
    have h1 : ‖u - v‖ ≤ K * (2 * ‖h‖) ^ θ := hE.trans (mul_le_mul_of_nonneg_left hzθ hK0)
    have e4 : ‖z‖ ^ (-(s + 1)) * ‖z‖ ^ θ = ‖z‖ ^ (-(s + 1 - θ)) := by
      rw [← Real.rpow_add hzn]; congr 1; ring
    have hWn : 0 ≤ |regh_k s (z + h) - regh_k s z - regh_kD s z h| := abs_nonneg _
    have hA : 0 ≤ c1 * regh_ind1 s (3 * ‖h‖) (z + h) + c1 * regh_ind1 s (2 * ‖h‖) z :=
      add_nonneg (mul_nonneg hc1p hf₀n) (mul_nonneg hc1p hf₁n)
    have hz1 : 0 ≤ ‖z‖ ^ (-(s + 1)) := Real.rpow_nonneg (norm_nonneg z) _
    rw [Real.norm_eq_abs]
    calc |regh_k s (z + h) - regh_k s z - regh_kD s z h| * ‖u - v‖
        ≤ (c1 * regh_ind1 s (3 * ‖h‖) (z + h) + c1 * regh_ind1 s (2 * ‖h‖) z +
            c2 * ‖z‖ ^ (-(s + 1)) * ‖h‖) * (K * ‖z‖ ^ θ) :=
          mul_le_mul hW hE (norm_nonneg _) (by positivity)
      _ = (c1 * regh_ind1 s (3 * ‖h‖) (z + h) + c1 * regh_ind1 s (2 * ‖h‖) z) * (K * ‖z‖ ^ θ) +
            K * c2 * ‖h‖ * (‖z‖ ^ (-(s + 1)) * ‖z‖ ^ θ) := by ring
      _ ≤ (c1 * regh_ind1 s (3 * ‖h‖) (z + h) + c1 * regh_ind1 s (2 * ‖h‖) z) * (K * (2 * ‖h‖) ^ θ) +
            K * c2 * ‖h‖ * regh_ind1 (s + 1 - θ) (2 * ‖h‖) z := by
          rw [e4, e3]
          gcongr
      _ = K * (2 * ‖h‖) ^ θ * c1 * (regh_ind1 s (3 * ‖h‖) (z + h) + regh_ind1 s (2 * ‖h‖) z) +
            K * c2 * ‖h‖ * regh_ind1 (s + 1 - θ) (2 * ‖h‖) z := by ring
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hK4 hf₂n)
  · have e2 := regh_ind2_of_le (σ := s + 2 - θ) hfar
    have hT := regh_k_taylor hs hfar hh
    rw [← hc4] at hT
    have e4 : ‖z‖ ^ (-(s + 2)) * ‖z‖ ^ θ = ‖z‖ ^ (-(s + 2 - θ)) := by
      rw [← Real.rpow_add hzn]; congr 1; ring
    rw [Real.norm_eq_abs]
    have hT' : |regh_k s (z + h) - regh_k s z - regh_kD s z h| ≤ c4 * ‖h‖ ^ 2 * ‖z‖ ^ (-(s + 2)) := by
      rw [← Real.norm_eq_abs]; exact hT
    have hA : 0 ≤ K * (2 * ‖h‖) ^ θ * c1 * (regh_ind1 s (3 * ‖h‖) (z + h) + regh_ind1 s (2 * ‖h‖) z) :=
      mul_nonneg hK2 (add_nonneg hf₀n hf₁n)
    have hB : 0 ≤ K * c2 * ‖h‖ * regh_ind1 (s + 1 - θ) (2 * ‖h‖) z := mul_nonneg hK3 hf₃n
    calc |regh_k s (z + h) - regh_k s z - regh_kD s z h| * ‖u - v‖
        ≤ (c4 * ‖h‖ ^ 2 * ‖z‖ ^ (-(s + 2))) * (K * ‖z‖ ^ θ) :=
          mul_le_mul hT' hE (norm_nonneg _) (by positivity)
      _ = K * c4 * ‖h‖ ^ 2 * (‖z‖ ^ (-(s + 2)) * ‖z‖ ^ θ) := by ring
      _ = K * c4 * ‖h‖ ^ 2 * regh_ind2 (s + 2 - θ) (2 * ‖h‖) z := by rw [e4, e2]
      _ ≤ _ := by linarith

/-- Remainder estimate for the derivative of the localised potential. -/
theorem regh_Tk_remainder {s θ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hθ0 : 0 ≤ θ) (hθa : 1 < θ + ((d : ℝ) - s)) (hθb : θ + ((d : ℝ) - s) < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {F : Euc d → E}, AEStronglyMeasurable F volume → ∀ {B K : ℝ}, (∀ y, ‖F y‖ ≤ B) → 0 ≤ K →
      (∀ x h, ‖F (x + h) - F x‖ ≤ K * ‖h‖ ^ θ) → ∀ x h,
      ‖regh_Tk s F (x + h) - regh_Tk s F x - regh_Pk s F x h‖ ≤
        C * K * ‖h‖ ^ (θ + ((d : ℝ) - s)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (d : ℝ) - s := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c : ℝ, c = max 1 (s / 2) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : ℝ, c = s * max 2 (max 1 (s / 2 + 1)) := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ c : ℝ, c = (2 * s * (s + 3)) * 2 ^ (s + 2) := ⟨_, rfl⟩
  obtain ⟨J₀, hJ₀⟩ : ∃ J : ℝ, J = ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-s) := ⟨_, rfl⟩
  obtain ⟨J₃, hJ₃⟩ : ∃ J : ℝ, J = ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-(s + 1 - θ)) := ⟨_, rfl⟩
  obtain ⟨J₂, hJ₂⟩ : ∃ J : ℝ, J = ∫ z in (ball (0 : Euc d) 1)ᶜ, ‖z‖ ^ (-(s + 2 - θ)) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; linarith
  have hc1p : 0 ≤ c1 := by rw [hc1]; exact le_trans zero_le_one (le_max_left _ _)
  have hc2p : 0 ≤ c2 := by
    rw [hc2]; exact mul_nonneg hs.le (le_trans (by norm_num) (le_max_left _ _))
  have hc4p : 0 ≤ c4 := by rw [hc4]; positivity
  have hJ₀p : 0 ≤ J₀ := by
    rw [hJ₀]; exact setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg z) _
  have hJ₃p : 0 ≤ J₃ := by
    rw [hJ₃]; exact setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg z) _
  have hJ₂p : 0 ≤ J₂ := by
    rw [hJ₂]
    exact setIntegral_nonneg measurableSet_ball.compl fun z _ => Real.rpow_nonneg (norm_nonneg z) _
  have hq3 : s + 1 - θ < d := by linarith
  have hq2 : (d : ℝ) < s + 2 - θ := by linarith
  have hCp : 0 ≤ 2 ^ θ * c1 * (3 ^ a + 2 ^ a) * J₀ + c2 * 2 ^ (a - 1 + θ) * J₃ +
      c4 * 2 ^ (a - 2 + θ) * J₂ := by positivity
  obtain ⟨C₁, C₂, hC₁, hC₂, hPk⟩ := regh_Pk_integrable_aux (d := d) (s := s) (θ := θ) hd1 hs hθ0 hq3
    (by linarith)
  refine ⟨2 ^ θ * c1 * (3 ^ a + 2 ^ a) * J₀ + c2 * 2 ^ (a - 1 + θ) * J₃ + c4 * 2 ^ (a - 2 + θ) * J₂,
    hCp, ?_⟩
  intro E _ _ _ F hm B K hB hK0 hK x h
  rw [← ha]
  by_cases hh : h = 0
  · subst hh
    simp only [add_zero, sub_self, map_zero, norm_zero]
    rw [Real.zero_rpow (by linarith)]; simp
  have hρ : 0 < ‖h‖ := norm_pos_iff.2 hh
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ‖h‖ := ⟨_, rfl⟩
  rw [← hρdef] at hρ ⊢
  have hf₀i := regh_ind1_integrable (d := d) hd1 (by linarith : s < d) (by positivity : (0 : ℝ) < 3 * ρ)
  have hf₁i := regh_ind1_integrable (d := d) hd1 (by linarith : s < d) (by positivity : (0 : ℝ) < 2 * ρ)
  have hf₃i := regh_ind1_integrable (d := d) hd1 hq3 (by positivity : (0 : ℝ) < 2 * ρ)
  have hf₂i := regh_ind2_integrable (d := d) hq2 (by positivity : (0 : ℝ) < 2 * ρ)
  have hI₀ : ∫ z : Euc d, regh_ind1 s (3 * ρ) (z + h) = (3 * ρ) ^ a * J₀ := by
    rw [integral_add_right_eq_self (μ := volume) (regh_ind1 s (3 * ρ)) h,
      regh_ind1_integral (by positivity), ha, hJ₀]
  have hI₁ : ∫ z : Euc d, regh_ind1 s (2 * ρ) z = (2 * ρ) ^ a * J₀ := by
    rw [regh_ind1_integral (by positivity), ha, hJ₀]
  have hI₃ : ∫ z : Euc d, regh_ind1 (s + 1 - θ) (2 * ρ) z = (2 * ρ) ^ (a - 1 + θ) * J₃ := by
    rw [regh_ind1_integral (by positivity), hJ₃]
    congr 2; rw [ha]; ring
  have hI₂ : ∫ z : Euc d, regh_ind2 (s + 2 - θ) (2 * ρ) z = (2 * ρ) ^ (a - 2 + θ) * J₂ := by
    rw [regh_ind2_integral (by positivity), hJ₂]
    congr 2; rw [ha]; ring
  obtain ⟨m, hmdef⟩ : ∃ m : Euc d → ℝ, m = fun z => K * (2 * ρ) ^ θ * c1 *
      (regh_ind1 s (3 * ρ) (z + h) + regh_ind1 s (2 * ρ) z) +
        K * c2 * ρ * regh_ind1 (s + 1 - θ) (2 * ρ) z +
        K * c4 * ρ ^ 2 * regh_ind2 (s + 2 - θ) (2 * ρ) z := ⟨_, rfl⟩
  have h0 : Integrable (fun z : Euc d => regh_ind1 s (3 * ρ) (z + h) + regh_ind1 s (2 * ρ) z) :=
    (hf₀i.comp_add_right h).add hf₁i
  have hmi : Integrable m := by
    rw [hmdef]
    exact ((h0.const_mul _).add (hf₃i.const_mul _)).add (hf₂i.const_mul _)
  have hmint : ∫ z, m z = K * (2 * ρ) ^ θ * c1 * ((3 * ρ) ^ a * J₀ + (2 * ρ) ^ a * J₀) +
      K * c2 * ρ * ((2 * ρ) ^ (a - 1 + θ) * J₃) + K * c4 * ρ ^ 2 * ((2 * ρ) ^ (a - 2 + θ) * J₂) := by
    have h1 : Integrable (fun z : Euc d => K * (2 * ρ) ^ θ * c1 *
        (regh_ind1 s (3 * ρ) (z + h) + regh_ind1 s (2 * ρ) z)) := h0.const_mul _
    have h2 : Integrable (fun z : Euc d => K * c2 * ρ * regh_ind1 (s + 1 - θ) (2 * ρ) z) :=
      hf₃i.const_mul _
    have h3 : Integrable (fun z : Euc d => K * c4 * ρ ^ 2 * regh_ind2 (s + 2 - θ) (2 * ρ) z) :=
      hf₂i.const_mul _
    have e : ∫ z, m z = ∫ z, (K * (2 * ρ) ^ θ * c1 *
        (regh_ind1 s (3 * ρ) (z + h) + regh_ind1 s (2 * ρ) z) +
        K * c2 * ρ * regh_ind1 (s + 1 - θ) (2 * ρ) z +
        K * c4 * ρ ^ 2 * regh_ind2 (s + 2 - θ) (2 * ρ) z) := by rw [hmdef]
    have h12 : Integrable (fun z : Euc d => K * (2 * ρ) ^ θ * c1 *
        (regh_ind1 s (3 * ρ) (z + h) + regh_ind1 s (2 * ρ) z) +
        K * c2 * ρ * regh_ind1 (s + 1 - θ) (2 * ρ) z) := h1.add h2
    rw [e, integral_add h12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_add (hf₀i.comp_add_right h) hf₁i, hI₀, hI₁, hI₂, hI₃]
  have hbd : ∀ᵐ z : Euc d, ‖(regh_k s (z + h) - regh_k s z - regh_kD s z h) • (F (x - z) - F x)‖ ≤
      m z := by
    have hzh : ∀ᵐ z : Euc d, z + h ≠ 0 :=
      (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (regh_ae_ne hd1)
    filter_upwards [regh_ae_ne hd1, hzh] with z hz hzh'
    have hE : ‖F (x - z) - F x‖ ≤ K * ‖z‖ ^ θ := by
      have := hK x (-z)
      rw [norm_neg] at this
      simpa [sub_eq_add_neg] using this
    rw [hmdef]
    have := regh_Tk_rem_pw (d := d) hs hθ0 (u := F (x - z)) (v := F x) (K := K) hK0 hc1 hc2 hc4
      (z := z) (h := h) hh hz hzh' hE
    rwa [← hρdef] at this
  have hE' : ∀ z, ‖F (x - z) - F x‖ ≤ K * ‖z‖ ^ θ := fun z => by
    have := hK x (-z)
    rw [norm_neg] at this
    simpa [sub_eq_add_neg] using this
  obtain ⟨hPi, -⟩ := hPk hm hB hK0 x hE'
  have hPh : regh_Pk s F x h = ∫ z, (regh_kD s z h) • (F (x - z) - F x) := by
    unfold regh_Pk
    rw [ContinuousLinearMap.integral_apply hPi]
    simp only [ContinuousLinearMap.smulRight_apply]
  have hPhi : Integrable (fun z => (regh_kD s z h) • (F (x - z) - F x)) := by
    have := (ContinuousLinearMap.apply ℝ E h).integrable_comp hPi
    simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smulRight_apply] using this
  have hdi := regh_Tk_diff_integrable hd1 hs hsd hs2 hm hB x h
  have hident : regh_Tk s F (x + h) - regh_Tk s F x - regh_Pk s F x h =
      ∫ z, (regh_k s (z + h) - regh_k s z - regh_kD s z h) • (F (x - z) - F x) := by
    rw [regh_Tk_diff_eq hd1 hs hsd hs2 hm hB x h, hPh, ← integral_sub hdi hPhi]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [sub_smul]
  rw [hident]
  refine (norm_integral_le_of_norm_le hmi hbd).trans ?_
  rw [hmint]
  have r2 : (2 * ρ) ^ θ = 2 ^ θ * ρ ^ θ := Real.mul_rpow (by norm_num) hρ.le
  have r3 : (3 * ρ) ^ a = 3 ^ a * ρ ^ a := Real.mul_rpow (by norm_num) hρ.le
  have r4 : (2 * ρ) ^ a = 2 ^ a * ρ ^ a := Real.mul_rpow (by norm_num) hρ.le
  have r5 : (2 * ρ) ^ (a - 1 + θ) = 2 ^ (a - 1 + θ) * ρ ^ (a - 1 + θ) :=
    Real.mul_rpow (by norm_num) hρ.le
  have r5' : (2 * ρ) ^ (a - 2 + θ) = 2 ^ (a - 2 + θ) * ρ ^ (a - 2 + θ) :=
    Real.mul_rpow (by norm_num) hρ.le
  have r6 : ρ ^ (θ + a) = ρ ^ θ * ρ ^ a := Real.rpow_add hρ _ _
  have r7 : ρ ^ (θ + a) = ρ * ρ ^ (a - 1 + θ) := by
    have := Real.rpow_add hρ 1 (a - 1 + θ)
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  have r8 : ρ ^ (θ + a) = ρ ^ 2 * ρ ^ (a - 2 + θ) := by
    have := Real.rpow_add hρ 2 (a - 2 + θ)
    rw [Real.rpow_two] at this
    rw [← this]; congr 1; ring
  apply le_of_eq
  rw [r2, r3, r4, r5, r5']
  linear_combination (-(2 ^ θ * c1 * (3 ^ a + 2 ^ a) * J₀ * K)) * r6 +
    (-(c2 * 2 ^ (a - 1 + θ) * J₃ * K)) * r7 + (-(c4 * 2 ^ (a - 2 + θ) * J₂ * K)) * r8

end Cross

end HRS.MS.Thm

end
