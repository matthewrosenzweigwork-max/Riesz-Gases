import HRS.MC.E213U13k

/-!
# S21L G11F1 -- fourth moments of the scalar second chaos (R26-T3.G11, sixth step)

Every `Y` in the `L²`-closure `InQ2` of centred quadratic polynomials of an i.i.d. Gaussian sequence satisfies
`Y⁴ ∈ L¹` and `E Y⁴ ≤ 15 (E Y²)²` (`s21l_inQ2_four`): finite quadratic polynomials obey `quadSum_four`
(`E Q⁴ ≤ 60 (∑ c²)²`, `E Q² = 2 ∑ c²`), and the bound passes to `L²`-limits by Fatou (`s21l_fatou_four`).  Prefix `s21l_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.deprecated false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS HRS.MC.E213U13

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem s21l_fatou_four {Qn : ℕ → Ω → ℝ} {Q : Ω → ℝ} (hmeas : ∀ n, AEStronglyMeasurable (Qn n) P)
    (hT : TendstoL2 P Qn Q) {C : ℝ}
    (hC : ∀ n, Integrable (fun ω => Qn n ω ^ 4) P ∧ ∫ ω, Qn n ω ^ 4 ∂P ≤ C) :
    Integrable (fun ω => Q ω ^ 4) P ∧ ∫ ω, Q ω ^ 4 ∂P ≤ C := by
  have hin := tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero (hT.tendsto_eLpNorm hmeas)
  obtain ⟨ns, -, hae⟩ := hin.exists_seq_tendsto_ae
  have hC0 : 0 ≤ C := (integral_nonneg fun ω => by positivity).trans (hC 0).2
  have hc : Continuous fun x : ℝ => ENNReal.ofReal (x ^ 4) :=
    ENNReal.continuous_ofReal.comp (continuous_pow 4)
  have key : ∫⁻ ω, ENNReal.ofReal (Q ω ^ 4) ∂P ≤ ENNReal.ofReal C := by
    calc ∫⁻ ω, ENNReal.ofReal (Q ω ^ 4) ∂P
        = ∫⁻ ω, liminf (fun i => ENNReal.ofReal (Qn (ns i) ω ^ 4)) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          exact (((hc.tendsto _).comp hω).liminf_eq).symm
      _ ≤ liminf (fun i => ∫⁻ ω, ENNReal.ofReal (Qn (ns i) ω ^ 4) ∂P) atTop :=
          lintegral_liminf_le' fun i => ((hmeas _).aemeasurable.pow_const 4).ennreal_ofReal
      _ ≤ ENNReal.ofReal C := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun i => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hC _).1
            (Filter.Eventually.of_forall fun ω => by positivity)]
          exact ENNReal.ofReal_le_ofReal (hC _).2
  have hQm : AEStronglyMeasurable (fun ω => Q ω ^ 4) P := (hT.1.pow 4 : AEStronglyMeasurable (fun ω => Q ω ^ 4) P)
  refine ⟨⟨hQm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => by positivity)]
    exact lt_of_le_of_lt key ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => Q ω ^ 4)
      (Filter.Eventually.of_forall fun ω => by positivity) hQm]
    exact ENNReal.toReal_le_of_le_ofReal hC0 key

theorem s21l_inQ2_four {ξ : ℕ → Ω → ℝ} {hξ : IsStdGaussianSeq P ξ} {Y : Ω → ℝ} (hY : InQ2 hξ Y) :
    Integrable (fun ω => Y ω ^ 4) P ∧ ∫ ω, Y ω ^ 4 ∂P ≤ 15 * (∫ ω, Y ω ^ 2 ∂P) ^ 2 := by
  obtain ⟨hY2, hYc⟩ := hY
  have hK : ∀ m : ℕ, ∃ n : ℕ, ∃ p ∈ K2 hξ n, dist p (hY2.toLp Y) < 1 / ((m : ℝ) + 1) := fun m =>
    (mem_Qc_iff (K2_mono hξ)).1 hYc (1 / ((m : ℝ) + 1)) (by positivity) |>.imp fun n hn => hn
  choose n p hp hd using hK
  have hA : ∀ m, ∃ A : ℕ → ℕ → ℝ, ((p m : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (n m), ∑ j ∈ Finset.range (n m),
        (ξ i ω * ξ j ω - if i = j then 1 else 0) • A i j := fun m => K2_poly hξ (p m) (hp m)
  choose A hAe using hA
  set c : ℕ → ℕ → ℕ → ℝ := fun m i j => (A m i j + A m j i) / 2 with hc
  have hcs : ∀ m i j, c m i j = c m j i := fun m i j => by simp only [hc]; ring
  set Qn : ℕ → Ω → ℝ := fun m => quadSum (c m) ξ (n m) with hQn
  have hQn_eq : ∀ m ω, Qn m ω = ∑ i ∈ Finset.range (n m), ∑ j ∈ Finset.range (n m),
      (ξ i ω * ξ j ω - if i = j then 1 else 0) • A m i j := by
    intro m ω
    set w : ℕ → ℕ → ℝ := fun i j => ξ i ω * ξ j ω - if i = j then 1 else 0 with hw
    have hws : ∀ i j, w i j = w j i := fun i j => by
      simp only [hw]
      rw [mul_comm (ξ i ω)]
      by_cases h : i = j
      · subst h; rfl
      · have h' : j ≠ i := Ne.symm h
        simp [h, h']
    show ∑ i ∈ Finset.range (n m), ∑ j ∈ Finset.range (n m), c m i j * w i j = _
    have e : ∀ i j, c m i j * w i j = (1 / 2) * (w i j • A m i j) + (1 / 2) * (w j i • A m j i) := fun i j => by
      simp only [hc, smul_eq_mul, hws j i]
      ring
    simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e2 : ∑ i ∈ Finset.range (n m), ∑ j ∈ Finset.range (n m), w j i • A m j i =
        ∑ i ∈ Finset.range (n m), ∑ j ∈ Finset.range (n m), w i j • A m i j := Finset.sum_comm
    rw [e2]
    ring
  have hmem : ∀ m, MemLp (Qn m) 2 P := fun m => memLp_quadSum hξ (c m) (n m)
  have hdist : Tendsto (fun m => ∫ ω, (Qn m ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have h1 : ∀ m, ∫ ω, (Qn m ω - Y ω) ^ 2 ∂P = dist (p m) (hY2.toLp Y) ^ 2 := by
      intro m
      rw [dist_eq_norm, Lp2_norm_sq]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (p m) (hY2.toLp Y), hY2.coeFn_toLp, hAe m] with ω h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, hQn_eq]
    have h2 : Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
      simpa using this
    refine squeeze_zero (fun m => integral_nonneg fun ω => sq_nonneg _) (fun m => ?_) h2
    rw [h1]
    exact pow_le_pow_left₀ dist_nonneg (hd m).le 2
  have hT : TendstoL2 P Qn Y := tendstoL2_of_memLp hY2 hmem hdist
  have hmeas : ∀ m, AEStronglyMeasurable (Qn m) P := fun m => (hmem m).aestronglyMeasurable
  obtain ⟨hlim1, hlim2⟩ := L2_limit_moments hY2 hmem hdist
  have h4 : ∀ m, Integrable (fun ω => Qn m ω ^ 4) P ∧ ∫ ω, Qn m ω ^ 4 ∂P ≤ 15 * (∫ ω, Qn m ω ^ 2 ∂P) ^ 2 := by
    intro m
    obtain ⟨hi, hb⟩ := quadSum_four hξ (c m) (hcs m) (n m)
    refine ⟨hi, ?_⟩
    have e2 := quadSum_L2 hξ (c m) (hcs m) (n m)
    rw [vGauss_eq] at e2
    have : ∫ ω, Qn m ω ^ 2 ∂P = 2 * ∑ i ∈ Finset.range (n m), ∑ j ∈ Finset.range (n m), c m i j ^ 2 := e2
    rw [this]
    nlinarith [hb, sq_nonneg (∑ i ∈ Finset.range (n m), ∑ j ∈ Finset.range (n m), c m i j ^ 2)]
  set a : ℝ := ∫ ω, Y ω ^ 2 ∂P with ha
  have hδ : ∀ δ : ℝ, 0 < δ → Integrable (fun ω => Y ω ^ 4) P ∧ ∫ ω, Y ω ^ 4 ∂P ≤ 15 * (a + δ) ^ 2 := by
    intro δ hδ
    obtain ⟨m0, hm0⟩ := (hlim2.eventually (gt_mem_nhds (show a < a + δ by linarith))).exists_forall_of_atTop
    refine s21l_fatou_four (Qn := fun k => Qn (k + m0)) (fun k => hmeas _)
      ⟨hT.1, hT.2.comp (tendsto_add_atTop_nat m0)⟩ (C := 15 * (a + δ) ^ 2) fun k => ⟨(h4 _).1, ?_⟩
    refine (h4 (k + m0)).2.trans ?_
    have h0 : 0 ≤ ∫ ω, Qn (k + m0) ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have := hm0 (k + m0) (by omega)
    have ha0 : 0 ≤ ∫ ω, Qn (k + m0) ω ^ 2 ∂P := h0
    nlinarith
  refine ⟨(hδ 1 one_pos).1, ?_⟩
  have hlim : Tendsto (fun δ : ℝ => 15 * (a + δ) ^ 2) (𝓝[>] 0) (𝓝 (15 * a ^ 2)) := by
    have : Tendsto (fun δ : ℝ => 15 * (a + δ) ^ 2) (𝓝 0) (𝓝 (15 * (a + 0) ^ 2)) :=
      (continuous_const.mul ((continuous_const.add continuous_id).pow 2)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ' => (hδ δ hδ').2)

end HRS.MS.R26T3
