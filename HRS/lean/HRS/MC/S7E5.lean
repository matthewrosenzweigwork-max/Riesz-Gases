import HRS.MC.S7E4

/-!
# Packet `s7_E5_not_tight`

Route.  `sigma_eps -> infinity` (`E3`, via `S7E4.e4_sigma_top`).  For `r > 0` let `tent_r` be the continuous
bump equal to `1` on `[-r, r]` and `0` off `(-2r, 2r)`.  For small `eps`, `R <= r sigma_eps`, so
`P(|Q_eps| <= R) <= E tent_r(Q_eps / sigma_eps)`, which tends to `E tent_r(N) <= 4 r` by `E4`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.E5

open HRS HRS.Sec7

variable {d : ℕ}

/-- the bump function -/
def tent (r x : ℝ) : ℝ := max 0 (min 1 (2 - |x| / r))

theorem tent_cont (r : ℝ) : Continuous (tent r) := by
  unfold tent; fun_prop

theorem tent_nonneg (r x : ℝ) : 0 ≤ tent r x := le_max_left _ _

theorem tent_le_one (r x : ℝ) : tent r x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem tent_eq_one {r x : ℝ} (hr : 0 < r) (hx : |x| ≤ r) : tent r x = 1 := by
  unfold tent
  have : 1 ≤ 2 - |x| / r := by
    have : |x| / r ≤ 1 := (div_le_one hr).2 hx
    linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem tent_eq_zero {r x : ℝ} (hr : 0 < r) (hx : 2 * r ≤ |x|) : tent r x = 0 := by
  unfold tent
  have : 2 - |x| / r ≤ 0 := by
    have : 2 ≤ |x| / r := (le_div_iff₀ hr).2 (by linarith)
    linarith
  rw [min_eq_right (by linarith), max_eq_left this]

theorem gauss_Icc_le {t : ℝ} (ht : 0 ≤ t) :
    gaussianReal 0 1 (Set.Icc (-t) t) ≤ ENNReal.ofReal (2 * t) := by
  rw [gaussianReal_apply 0 one_ne_zero]
  calc ∫⁻ x in Set.Icc (-t) t, gaussianPDF 0 1 x ≤ ∫⁻ x in Set.Icc (-t) t, 1 := by
        refine lintegral_mono fun x => ?_
        unfold gaussianPDF
        rw [ENNReal.ofReal_le_one]
        rw [gaussianPDFReal_def]
        have h1 : Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ (x - 0) ^ 2 := sq_nonneg _
          have h2 : 0 < 2 * ((1 : ℝ≥0) : ℝ) := by norm_num
          exact div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
        have h3 : (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ ≤ 1 := by
          rw [inv_le_one₀ (Real.sqrt_pos.2 (by positivity))]
          rw [Real.one_le_sqrt]
          have := Real.pi_gt_three
          simp only [NNReal.coe_one]; linarith
        calc (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
            ≤ 1 * 1 := mul_le_mul h3 h1 (Real.exp_pos _).le zero_le_one
          _ = 1 := one_mul 1
    _ = ENNReal.ofReal (2 * t) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
        simp only [one_mul]
        congr 1; ring

theorem tent_integral_le {r : ℝ} (hr : 0 < r) : ∫ y, tent r y ∂(gaussianReal 0 1) ≤ 4 * r := by
  have hind : ∀ y, tent r y ≤ (Set.Icc (-(2 * r)) (2 * r)).indicator (1 : ℝ → ℝ) y := by
    intro y
    by_cases hy : y ∈ Set.Icc (-(2 * r)) (2 * r)
    · rw [Set.indicator_of_mem hy]; exact tent_le_one _ _
    · rw [Set.indicator_of_notMem hy]
      have : 2 * r ≤ |y| := by
        by_contra hcon
        push_neg at hcon
        exact hy ⟨by linarith [(abs_lt.1 hcon).1], by linarith [(abs_lt.1 hcon).2]⟩
      rw [tent_eq_zero hr this]
  have hint1 : Integrable (tent r) (gaussianReal 0 1) :=
    Integrable.mono' (integrable_const 1) (tent_cont r).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _ _)]; exact tent_le_one _ _)
  have hint2 : Integrable ((Set.Icc (-(2 * r)) (2 * r)).indicator (1 : ℝ → ℝ)) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  calc ∫ y, tent r y ∂(gaussianReal 0 1) ≤
        ∫ y, (Set.Icc (-(2 * r)) (2 * r)).indicator (1 : ℝ → ℝ) y ∂(gaussianReal 0 1) :=
        integral_mono hint1 hint2 hind
    _ = (gaussianReal 0 1).real (Set.Icc (-(2 * r)) (2 * r)) := integral_indicator_one measurableSet_Icc
    _ ≤ 4 * r := by
        have := gauss_Icc_le (t := 2 * r) (by positivity)
        unfold Measure.real
        have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
        rw [ENNReal.toReal_ofReal (by positivity)] at h2
        linarith

theorem s7_E5_not_tight_proof (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ) (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε))
    (R : ℝ) :
    Tendsto (fun ε : ℝ => P {ω | R < |Q ε ω|}) (𝓝[>] 0) (𝓝 1) := by
  have hσ2 := E4.e4_sigma_top hd hs hsd hβ ρ hρ φ hφ hnc e he P G hG Q hQ
  have hE4 := E4.s7_E4_normalized_clt_proof hd hs hsd hβ ρ hρ φ hφ hnc e he P G hG Q hQ
  have hσ : Tendsto (fun ε : ℝ => Real.sqrt (∫ ω, Q ε ω ^ 2 ∂P)) (𝓝[>] 0) atTop :=
    Real.tendsto_sqrt_atTop.comp hσ2
  set q : ℝ → ℝ≥0∞ := fun ε => P {ω | |Q ε ω| ≤ R} with hqdef
  have hqr : Tendsto (fun ε : ℝ => (q ε).toReal) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Filter.Eventually.of_forall fun ε => lt_of_lt_of_le ha ENNReal.toReal_nonneg
    · set r : ℝ := a / 8 with hr
      have hr0 : 0 < r := by positivity
      have hFb : ∃ M, ∀ x, |tent r x| ≤ M := ⟨1, fun x => by
        rw [abs_of_nonneg (tent_nonneg _ _)]; exact tent_le_one _ _⟩
      have h1 := hE4 (tent r) (tent_cont r) hFb
      have hlt : ∫ y, tent r y ∂(gaussianReal 0 1) < a := by
        have := tent_integral_le hr0
        rw [hr] at this
        linarith
      have h2 := (tendsto_order.1 h1).2 a hlt
      filter_upwards [h2, hσ.eventually_ge_atTop (R / r), hσ.eventually_gt_atTop 0,
        self_mem_nhdsWithin] with ε hε1 hε2 hε3 hε4
      have hε4' : 0 < ε := hε4
      set σ := Real.sqrt (∫ ω, Q ε ω ^ 2 ∂P) with hσdef
      have hmeas : AEStronglyMeasurable (fun ω => tent r (Q ε ω / σ)) P :=
        (tent_cont r).comp_aestronglyMeasurable
          (((hQ ε hε4').1.div_const σ).aestronglyMeasurable)
      have hint : Integrable (fun ω => tent r (Q ε ω / σ)) P :=
        Integrable.mono' (integrable_const 1) hmeas
          (ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _ _)]; exact tent_le_one _ _)
      have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
        (f := fun ω => tent r (Q ε ω / σ)) (ae_of_all _ fun ω => tent_nonneg _ _) hint 1
      have hsub : {ω | |Q ε ω| ≤ R} ⊆ {ω | 1 ≤ tent r (Q ε ω / σ)} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        rw [tent_eq_one hr0]
        rw [abs_div, abs_of_pos hε3, div_le_iff₀ hε3]
        have : R ≤ r * σ := by
          have := (div_le_iff₀ hr0).1 hε2
          linarith
        linarith
      have hle : (q ε).toReal ≤ ∫ ω, tent r (Q ε ω / σ) ∂P := by
        have := measureReal_mono (μ := P) hsub (measure_ne_top _ _)
        simp only [one_mul] at hmk
        exact (le_of_eq rfl).trans (this.trans hmk)
      exact lt_of_le_of_lt hle hε1
  have hq0 : Tendsto q (𝓝[>] 0) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal_iff (fun i => measure_ne_top P _) ENNReal.zero_ne_top).1
      (by simpa using hqr)
    exact this
  have hsub := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hq0 (Or.inl ENNReal.one_ne_top)
  rw [tsub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  have hm : AEMeasurable (fun ω => |Q ε ω|) P := continuous_abs.measurable.comp_aemeasurable (hQ ε hε').1
  have hA : NullMeasurableSet {ω | |Q ε ω| ≤ R} P := hm.nullMeasurable measurableSet_Iic
  have hc : {ω | R < |Q ε ω|} = {ω | |Q ε ω| ≤ R}ᶜ := by
    ext ω; simp
  show 1 - q ε = P {ω | R < |Q ε ω|}
  rw [hc, prob_compl_eq_one_sub₀ hA]

end HRS.MC.Sec7.E5

end
