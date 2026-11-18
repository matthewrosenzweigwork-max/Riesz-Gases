import HRS.MS.SpecAux67

/-!
# S8L: the log-Sobolev hypothesis and the differential inequality of the Herbst argument (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_LSI μ C` is the log-Sobolev inequality
`Ent_μ(u²) ≤ C ∫|∇u|²` for `C¹` functions with `u ∈ L²(μ)`, `|∇u| ∈ L²(μ)` (with the integrability of `u² log u²`
as part of the conclusion).  `S8pSubsol` collects the hypotheses on a positive subsolution `s` (`L s ≤ a s + b h √s - |∇s|²/(2s)`,
with the integration-by-parts identity for the truncated test functions `G_q(s)`), and `s8p_diff_ineq` is the Gross-Herbst
differential inequality `q Φ'(q) ≤ Φ(q) (log Φ(q) + K)` for the truncated moments `Φ(q) = ∫ s m_ε(s)^{q-1} dμ`.
-/

noncomputable section

open MeasureTheory Set Real

namespace HRS.MS.Spec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The log-Sobolev inequality with constant `C` for the measure `μ`. -/
def s8p_LSI (μ : Measure E) (C : ℝ) : Prop :=
  ∀ u : E → ℝ, ContDiff ℝ 2 u → MemLp u 2 μ → Integrable (fun x => ‖fderiv ℝ u x‖ ^ 2) μ →
    Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) μ ∧
      ∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂μ - (∫ x, u x ^ 2 ∂μ) * Real.log (∫ x, u x ^ 2 ∂μ) ≤
        C * ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂μ

/-- Hypotheses of the Herbst argument: `s ≥ s0 > 0` is a `C²` density with `∫ s = 1`, `h ≥ 0` with `∫ h⁴ ≤ H4`, and the
integrated energy inequality (`en`), consequence of the subsolution property `L s ≤ a s + b h √s - |∇s|²/(2s)`: for all `C¹`
(on `(0,∞)`) nonnegative test functions `G`, bounded with bounded derivative on `[s0, ∞)`,
`∫ G'(s) |∇s|² + ∫ G(s) |∇s|²/(2s) ≤ ∫ (a s + b h √s) G(s)` (both integrals on the left being finite). -/
structure S8pSubsol (μ : Measure E) (s h : E → ℝ) (s0 a b H4 : ℝ) : Prop where
  cont : ContDiff ℝ 2 s
  s0_pos : 0 < s0
  ge : ∀ x, s0 ≤ s x
  int : Integrable s μ
  one : ∫ x, s x ∂μ = 1
  a_nonneg : 0 ≤ a
  b_nonneg : 0 ≤ b
  h_nonneg : ∀ x, 0 ≤ h x
  h_meas : Measurable h
  h4_int : Integrable (fun x => h x ^ 4) μ
  h4_le : ∫ x, h x ^ 4 ∂μ ≤ H4
  en : ∀ G : ℝ → ℝ, ContDiffOn ℝ 1 G (Ioi 0) →
    (∃ B : ℝ, ∀ t, s0 ≤ t → |G t| ≤ B ∧ |deriv G t| ≤ B) → (∀ t, 0 < t → 0 ≤ G t) →
    (∀ t, 0 < t → 0 ≤ deriv G t) →
    Integrable (fun x => deriv G (s x) * ‖fderiv ℝ s x‖ ^ 2) μ ∧
      Integrable (fun x => G (s x) * ‖fderiv ℝ s x‖ ^ 2 / (2 * s x)) μ ∧
      ∫ x, deriv G (s x) * ‖fderiv ℝ s x‖ ^ 2 ∂μ + ∫ x, G (s x) * ‖fderiv ℝ s x‖ ^ 2 / (2 * s x) ∂μ ≤
        ∫ x, (a * s x + b * h x * Real.sqrt (s x)) * G (s x) ∂μ

theorem s8p_Gd_nonneg {q ε t : ℝ} (hq : 1 ≤ q) (hε : 0 ≤ ε) (ht : 0 < t) : 0 ≤ deriv (s8p_G q ε) t := by
  rw [(s8p_G_hasDerivAt q hε ht).deriv]
  have := s8p_G_pos (q := q) hε ht
  unfold s8p_Gd
  positivity

theorem s8p_G_contDiffAt (q : ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    ContDiffAt ℝ 1 (s8p_G q ε) t := by
  have h1 : ContDiffAt ℝ 1 (fun x : ℝ => 1 + ε * x) t := by fun_prop
  have h1' : (1 + ε * t) ≠ 0 := by positivity
  have h2 : ContDiffAt ℝ 1 (fun x : ℝ => x / (1 + ε * x)) t := contDiffAt_id.div h1 h1'
  have hm : (t / (1 + ε * t)) ≠ 0 := by positivity
  exact h2.rpow_const_of_ne hm

theorem s8p_G_contDiffOn (q : ℝ) {ε : ℝ} (hε : 0 ≤ ε) : ContDiffOn ℝ 1 (s8p_G q ε) (Ioi 0) :=
  fun t ht => (s8p_G_contDiffAt q hε ht).contDiffWithinAt

theorem s8p_G_bounds (q : ℝ) {ε s0 : ℝ} (hε : 0 < ε) (hs0 : 0 < s0) :
    ∃ B : ℝ, ∀ t, s0 ≤ t → |s8p_G q ε t| ≤ B ∧ |deriv (s8p_G q ε) t| ≤ B := by
  refine ⟨s8p_Bm ε s0 |q - 1| * (1 + |q - 1| / s0), fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le hs0 ht
  have hBm : 0 ≤ s8p_Bm ε s0 |q - 1| := by
    unfold s8p_Bm
    have := s8p_hm_pos hε.le hs0
    positivity
  have hG : |s8p_G q ε t| ≤ s8p_Bm ε s0 |q - 1| := by
    rw [abs_of_pos (s8p_G_pos hε.le ht0)]
    exact s8p_hm_rpow_le hε hs0 ht le_rfl
  have hGp : (0:ℝ) ≤ |q - 1| / s0 := by positivity
  refine ⟨hG.trans (by nlinarith), ?_⟩
  rw [(s8p_G_hasDerivAt q hε.le ht0).deriv]
  unfold s8p_Gd
  rw [abs_div, abs_mul, abs_of_pos (s8p_G_pos hε.le ht0), abs_of_pos (mul_pos ht0 (by positivity))]
  have h1 : s0 ≤ t * (1 + ε * t) := by nlinarith [mul_nonneg hε.le (sq_nonneg t)]
  have h2 : |q - 1| * s8p_G q ε t / (t * (1 + ε * t)) ≤ |q - 1| * s8p_Bm ε s0 |q - 1| / s0 := by
    rw [div_le_div_iff₀ (by positivity) hs0]
    have hG' : s8p_G q ε t ≤ s8p_Bm ε s0 |q - 1| := by
      have := abs_of_pos (s8p_G_pos hε.le ht0) ▸ hG
      exact this
    calc |q - 1| * s8p_G q ε t * s0 ≤ (|q - 1| * s8p_Bm ε s0 |q - 1|) * s0 := by
          apply mul_le_mul_of_nonneg_right _ hs0.le
          exact mul_le_mul_of_nonneg_left hG' (abs_nonneg _)
      _ ≤ (|q - 1| * s8p_Bm ε s0 |q - 1|) * (t * (1 + ε * t)) := by
          apply mul_le_mul_of_nonneg_left h1; positivity
  calc _ ≤ |q - 1| * s8p_Bm ε s0 |q - 1| / s0 := h2
    _ ≤ _ := by
      rw [mul_div_right_comm]; nlinarith [mul_nonneg hBm hGp]


/-! ### Pointwise facts for the truncated weights -/

theorem s8p_G_sq_le {q ε t : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hε : 0 ≤ ε) (ht : 0 < t) :
    s8p_G q ε t ^ 2 ≤ 1 + s8p_U2 q ε t := by
  have hG := s8p_G_pos (q := q) hε ht
  have hm := s8p_hm_pos hε ht
  unfold s8p_U2
  rcases le_total 1 (s8p_hm ε t) with h1 | h1
  · have h2 : s8p_G q ε t ≤ s8p_hm ε t := by
      unfold s8p_G
      calc s8p_hm ε t ^ (q - 1) ≤ s8p_hm ε t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
        _ = s8p_hm ε t := Real.rpow_one _
    have h3 : s8p_G q ε t ≤ t := h2.trans (s8p_hm_le hε ht)
    nlinarith
  · have h2 : s8p_G q ε t ≤ 1 := by
      unfold s8p_G
      exact Real.rpow_le_one hm.le h1 (by linarith)
    nlinarith [mul_pos ht hG]

theorem s8p_U2_ge {q ε t : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 < t) :
    (t - 1 / 2) / 3 ≤ s8p_U2 q ε t := by
  rcases lt_or_ge t (1 / 2) with h | h
  · have := s8p_U2_pos (q := q) hε ht
    linarith
  · have hm : (1 / 3 : ℝ) ≤ s8p_hm ε t := by
      have h1 : s8p_hm ε (1 / 2) ≤ s8p_hm ε t := s8p_hm_mono hε (by norm_num) h
      have h2 : (1 / 3 : ℝ) ≤ s8p_hm ε (1 / 2) := by
        unfold s8p_hm
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
      linarith
    have hG : (1 / 3 : ℝ) ≤ s8p_G q ε t := by
      unfold s8p_G
      calc (1 / 3 : ℝ) = (1 / 3 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 / 3 : ℝ) ^ (q - 1) :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
        _ ≤ s8p_hm ε t ^ (q - 1) := Real.rpow_le_rpow (by norm_num) hm (by linarith)
    unfold s8p_U2
    nlinarith

theorem s8p_U2_log_ge {q ε t : ℝ} (hq1 : 1 ≤ q) (hε : 0 ≤ ε) (ht : 0 < t) :
    q * (s8p_U2 q ε t * Real.log (s8p_hm ε t)) ≤ s8p_U2 q ε t * Real.log (s8p_U2 q ε t) := by
  have hm := s8p_hm_pos hε ht
  have hG := s8p_G_pos (q := q) hε ht
  have hU := s8p_U2_pos (q := q) hε ht
  have hlog : Real.log (s8p_U2 q ε t) = Real.log t + (q - 1) * Real.log (s8p_hm ε t) := by
    unfold s8p_U2 s8p_G
    rw [Real.log_mul ht.ne' (Real.rpow_pos_of_pos hm _).ne', Real.log_rpow hm]
  have hle : Real.log (s8p_hm ε t) ≤ Real.log t := Real.log_le_log hm (s8p_hm_le hε ht)
  rw [hlog]
  have : q * Real.log (s8p_hm ε t) ≤ Real.log t + (q - 1) * Real.log (s8p_hm ε t) := by linarith
  nlinarith

/-! ### Integrability of the derivative integrand -/

section Dom

variable {μ : Measure E} {s : E → ℝ} {ε s0 : ℝ}

theorem s8p_dPhi_integrable (hε : 0 < ε) (hs0 : 0 < s0) (hs : Measurable s)
    (hint : Integrable s μ) (hge : ∀ x, s0 ≤ s x) (q : ℝ) :
    Integrable (fun x => s8p_U2 q ε (s x) * Real.log (s8p_hm ε (s x))) μ := by
  refine Integrable.mono' (hint.mul_const (s8p_Bm ε s0 |q - 1| * s8p_Lm ε s0)) ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · have : Measurable fun x => s8p_U2 q ε (s x) * Real.log (s8p_hm ε (s x)) := by
      unfold s8p_U2 s8p_G s8p_hm
      fun_prop
    exact this.aestronglyMeasurable
  · simpa [Real.norm_eq_abs] using s8p_U2_log_le (q := q) hε hs0 (hge x) le_rfl

end Dom

end HRS.MS.Spec
