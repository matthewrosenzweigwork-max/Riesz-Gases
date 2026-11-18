import HRS.MS.SuppU2Aux2

/-!
# U2 auxiliary 3: convolution with a homogeneous kernel against a weighted function

`u2Conv κ h x = ∫ κ(z) h(x - z) dz`; differentiation under the integral with the derivatives on `h`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-- The weight `(1 + ‖y‖)^{-L}`. -/
def u2Wt (L : ℝ) (y : Euc d) : ℝ := (1 + ‖y‖) ^ (-L)

lemma u2Wt_pos (L : ℝ) (y : Euc d) : 0 < u2Wt L y := by
  unfold u2Wt; exact Real.rpow_pos_of_pos (by positivity) _

lemma u2Wt_le_one {L : ℝ} (hL : 0 ≤ L) (y : Euc d) : u2Wt L y ≤ 1 := by
  unfold u2Wt
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)

lemma u2Wt_continuous (L : ℝ) : Continuous (u2Wt (d := d) L) := by
  unfold u2Wt
  exact (continuous_const.add continuous_norm).rpow_const (fun x => Or.inl (by show 1 + ‖x‖ ≠ 0; positivity))

lemma u2_peetre {L : ℝ} (hL : 0 ≤ L) {x x0 : Euc d} (hx : ‖x - x0‖ ≤ 1) (z : Euc d) :
    u2Wt L (x - z) ≤ 2 ^ L * u2Wt L (x0 - z) := by
  unfold u2Wt
  have h1 : 1 + ‖x0 - z‖ ≤ 2 * (1 + ‖x - z‖) := by
    have : ‖x0 - z‖ ≤ ‖x0 - x‖ + ‖x - z‖ := by
      calc ‖x0 - z‖ = ‖(x0 - x) + (x - z)‖ := by simp
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖x0 - x‖ ≤ 1 := by rw [norm_sub_rev]; exact hx
    linarith [norm_nonneg (x - z)]
  have hv : 0 < 1 + ‖x0 - z‖ := by positivity
  have hu : 0 < 1 + ‖x - z‖ := by positivity
  have h3 : (1 + ‖x0 - z‖) / 2 ≤ 1 + ‖x - z‖ := by linarith
  have h4 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + ‖x0 - z‖) / 2) h3
    (by linarith : -L ≤ 0)
  refine h4.trans (le_of_eq ?_)
  rw [Real.div_rpow hv.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_neg hv.le]
  field_simp

lemma u2_integrable_wt {L : ℝ} (hL : (d : ℝ) < L) : Integrable (u2Wt (d := d) L) volume := by
  have := integrable_one_add_norm (E := Euc d) (μ := volume) (r := L) (by simpa using hL)
  exact this

/-- Hypotheses on the (scalar) kernel `κ`: measurable, `|κ(z)| ≤ C ‖z‖^{-a}`, `‖z‖^{-a}` locally
integrable. -/
structure U2Ker (κ : Euc d → ℝ) (a : ℝ) : Prop where
  meas : Measurable κ
  a_nonneg : 0 ≤ a
  bound : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ z : Euc d, z ≠ 0 → |κ z| ≤ C0 * ‖z‖ ^ (-a)
  d_pos : 1 ≤ d
  integ : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-a)) (ball (0 : Euc d) 1) volume

lemma u2_integral_nonneg {f : Euc d → ℝ} (hf : ∀ z, 0 ≤ f z) : 0 ≤ ∫ z, f z :=
  integral_nonneg hf

lemma u2_ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ z : Euc d ∂volume, z ≠ 0 := by
  have : Nontrivial (Euc d) := by
    rw [← Module.finrank_pos_iff (R := ℝ)]; simpa using (by omega : 0 < d)
  have := (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))
  filter_upwards [this] with z hz
  simpa using hz

lemma u2_kerInt {κ : Euc d → ℝ} {a : ℝ} (hker : U2Ker κ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Euc d → ℝ, AEStronglyMeasurable w volume → (∀ z, 0 ≤ w z) →
      (∀ z, w z ≤ 1) → Integrable w volume →
      Integrable (fun z => ‖κ z‖ * w z) volume ∧
        ∫ z, ‖κ z‖ * w z ≤ C * (1 + ∫ z, w z) := by
  obtain ⟨C0, hC0, hb⟩ := hker.bound
  set Φ : Euc d → ℝ := (ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-a)) with hΦ
  have hΦi : Integrable Φ volume := (integrable_indicator_iff measurableSet_ball).2 hker.integ
  have hΦ0 : ∀ z, 0 ≤ Φ z := fun z => by
    rw [hΦ]; exact Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) z
  refine ⟨C0 * ((∫ z, Φ z) + 1), mul_nonneg hC0 (by linarith [u2_integral_nonneg hΦ0]), ?_⟩
  intro w hwm hw0 hw1 hwi
  have hpt : ∀ᵐ z : Euc d ∂volume, ‖κ z‖ * w z ≤ C0 * (Φ z + w z) := by
    filter_upwards [u2_ae_ne_zero hker.d_pos] with z hz
    have h1 := hb z hz
    rw [Real.norm_eq_abs]
    by_cases hz1 : ‖z‖ < 1
    · have : Φ z = ‖z‖ ^ (-a) := by
        rw [hΦ]; exact Set.indicator_of_mem (by simpa using hz1) _
      rw [this] at *
      have h2 : |κ z| * w z ≤ C0 * ‖z‖ ^ (-a) * 1 :=
        mul_le_mul h1 (hw1 z) (hw0 z) (by positivity)
      nlinarith [hw0 z, Real.rpow_nonneg (norm_nonneg z) (-a)]
    · push Not at hz1
      have h2 : ‖z‖ ^ (-a) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hz1 (by linarith [hker.a_nonneg])
      have h3 : |κ z| ≤ C0 := h1.trans (by nlinarith)
      have h4 : |κ z| * w z ≤ C0 * w z := mul_le_mul_of_nonneg_right h3 (hw0 z)
      nlinarith [hΦ0 z, hw0 z]
  have hbi : Integrable (fun z => C0 * (Φ z + w z)) volume := (hΦi.add hwi).const_mul C0
  have hmeas : AEStronglyMeasurable (fun z => ‖κ z‖ * w z) volume :=
    hker.meas.norm.aestronglyMeasurable.mul hwm
  have hint : Integrable (fun z => ‖κ z‖ * w z) volume := by
    refine hbi.mono' hmeas ?_
    filter_upwards [hpt] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hw0 z))]
    exact hz
  refine ⟨hint, ?_⟩
  have h1 : ∫ z, ‖κ z‖ * w z ≤ ∫ z, C0 * (Φ z + w z) :=
    integral_mono_ae hint hbi hpt
  rw [integral_const_mul, integral_add hΦi hwi] at h1
  have h2 : 0 ≤ ∫ z, Φ z := u2_integral_nonneg hΦ0
  have h3 : 0 ≤ ∫ z, w z := u2_integral_nonneg hw0
  refine h1.trans ?_
  have : (∫ z, Φ z) + ∫ z, w z ≤ ((∫ z, Φ z) + 1) * (1 + ∫ z, w z) := by nlinarith [mul_nonneg h2 h3]
  nlinarith

/-- The convolution `∫ κ(z) g(x-z) dz`. -/
def u2Conv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : Euc d → ℝ) (g : Euc d → E)
    (x : Euc d) : E := ∫ z, κ z • g (x - z)

section ConvLemmas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma u2_wt_translate_int {κ : Euc d → ℝ} {a L : ℝ} (hker : U2Ker κ a) (hL : (d : ℝ) < L)
    (x : Euc d) : Integrable (fun z => ‖κ z‖ * u2Wt L (x - z)) volume := by
  obtain ⟨C, hC, hK⟩ := u2_kerInt hker
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  exact (hK (fun z => u2Wt L (x - z))
    ((u2Wt_continuous L).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (fun z => (u2Wt_pos L _).le) (fun z => u2Wt_le_one hL0 _)
    ((u2_integrable_wt hL).comp_sub_left x)).1

lemma u2_conv_integrable {κ : Euc d → ℝ} {a L : ℝ} (hker : U2Ker κ a) (hL : (d : ℝ) < L)
    {g : Euc d → E} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (hg0 : ∀ y, ‖g y‖ ≤ A * u2Wt L y)
    (x : Euc d) : Integrable (fun z => κ z • g (x - z)) volume := by
  have hb : Integrable (fun z => A * (‖κ z‖ * u2Wt L (x - z))) volume :=
    (u2_wt_translate_int hker hL x).const_mul A
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact hker.meas.aestronglyMeasurable.smul
      (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [norm_smul]
    have := hg0 (x - z)
    calc ‖κ z‖ * ‖g (x - z)‖ ≤ ‖κ z‖ * (A * u2Wt L (x - z)) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = A * (‖κ z‖ * u2Wt L (x - z)) := by ring

lemma u2_conv_norm_le {κ : Euc d → ℝ} {a L : ℝ} (hker : U2Ker κ a) (hL : (d : ℝ) < L) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (g : Euc d → E) (A : ℝ), 0 ≤ A → (∀ y, ‖g y‖ ≤ A * u2Wt L y) →
      ∀ x, ‖u2Conv κ g x‖ ≤ Cu * A := by
  obtain ⟨C, hC, hK⟩ := u2_kerInt hker
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨C * (1 + ∫ y, u2Wt (d := d) L y), mul_nonneg hC (by
    have := u2_integral_nonneg (f := u2Wt (d := d) L) (fun y => (u2Wt_pos (d := d) L y).le); linarith), ?_⟩
  intro E _ _ g A hA hg0 x
  obtain ⟨hi, hle⟩ := hK (fun z => u2Wt L (x - z))
    ((u2Wt_continuous L).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (fun z => (u2Wt_pos L _).le) (fun z => u2Wt_le_one hL0 _)
    ((u2_integrable_wt hL).comp_sub_left x)
  have hint : ∫ z, u2Wt (d := d) L (x - z) = ∫ y, u2Wt (d := d) L y :=
    integral_sub_left_eq_self (fun y => u2Wt (d := d) L y) volume x
  rw [hint] at hle
  unfold u2Conv
  calc ‖∫ z, κ z • g (x - z)‖ ≤ ∫ z, A * (‖κ z‖ * u2Wt L (x - z)) := by
        refine norm_integral_le_of_norm_le (hi.const_mul A) (Filter.Eventually.of_forall fun z => ?_)
        rw [norm_smul]
        calc ‖κ z‖ * ‖g (x - z)‖ ≤ ‖κ z‖ * (A * u2Wt L (x - z)) :=
              mul_le_mul_of_nonneg_left (hg0 _) (norm_nonneg _)
          _ = A * (‖κ z‖ * u2Wt L (x - z)) := by ring
    _ = A * ∫ z, ‖κ z‖ * u2Wt L (x - z) := by rw [integral_const_mul]
    _ ≤ A * (C * (1 + ∫ y, u2Wt (d := d) L y)) := mul_le_mul_of_nonneg_left hle hA
    _ = C * (1 + ∫ y, u2Wt (d := d) L y) * A := by ring

end ConvLemmas

end HRS.Whole
