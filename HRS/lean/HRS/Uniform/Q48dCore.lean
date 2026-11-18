import HRS.Uniform.Q48dAux5

/-!
# Q48d, the abstract core of Lemma 3.31

Given an evolution `V` on a separable Hilbert space `E` (strongly continuous cocycle, `‖V(t,u)‖ ≤ C₀ e^{-c(t-u)}`)
satisfying the window maximal estimate `WinMaxU` for the window lengths `1` and `T`, and a Hilbert martingale `D`
(stopped versions with cut covariation densities `Sd`) with `E ‖Sd_r‖_{𝔖₁} ≤ K` for all `r ≥ 0`, the global stochastic
convolution `Z_t = ∫_0^t V(t,u) dD_u` exists with continuous paths and
`‖sup_{a ≤ t ≤ a+T} ‖Z_t‖‖_{L²} ≤ Cfin · K^{1/2}` uniformly in `a ≥ 0`.

The time regularity of the TeX proof is not needed: on the window `Z_t = V(t,a) Z_a + W_t`; the history `Z_a` is
a single random vector, split into blocks of length `≤ 1`, each controlled by the window estimate and the decay.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Uniform.Q48d

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The constant of `core`. -/
def coreConst (C₀ c C₁ CT T : ℝ) : ℝ :=
  C₀ * (C₀ * (1 / (1 - Real.exp (-c / 2))) * Real.sqrt C₁) + Real.sqrt (CT * T)

lemma coreConst_nonneg {C₀ c C₁ CT T : ℝ} (hC0 : 0 ≤ C₀) (hc : 0 < c) : 0 ≤ coreConst C₀ c C₁ CT T := by
  have : Real.exp (-c / 2) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  unfold coreConst
  have : 0 ≤ 1 / (1 - Real.exp (-c / 2)) := div_nonneg zero_le_one (by linarith)
  positivity

theorem core {V : ℝ → ℝ → E →L[ℝ] E} (hV : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution V T)
    {C₀ c : ℝ} (hC0 : 0 ≤ C₀) (hc : 0 < c)
    (hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖V t u‖ ≤ C₀ * Real.exp (-c * (t - u)))
    (hW : ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧ WinMaxU.{u} V T C) {T : ℝ} (hT : 0 < T)
    {C₁ CT : ℝ} (hC1 : 0 ≤ C₁) (hCT0 : 0 ≤ CT) (h1 : WinMaxU.{u} V 1 C₁) (hWT : WinMaxU.{u} V T CT) :
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (D : ℝ → Ω → E) (Sd : ℝ → Ω → (E →L[ℝ] E →L[ℝ] ℝ))
        (_ : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S (fun τ ω => D (min τ S) ω)
          (fun r ω => if r ≤ S then Sd r ω else 0))
        (K : ℝ) (_ : 0 ≤ K)
        (_ : ∀ r : ℝ, 0 ≤ r → ∫⁻ ω, ENNReal.ofReal (traceNormForm (Sd r ω)) ∂P ≤ ENNReal.ofReal K),
        ∃ Z : ℝ → Ω → E,
          (∀ t : ℝ, 0 ≤ t → IsStochConv P V (ContinuousLinearMap.id ℝ E) D 0 t (Z t)) ∧
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Ici 0)) ∧
          ∀ a : ℝ, 0 ≤ a →
            (∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖Z t ω‖ₑ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
              ENNReal.ofReal (coreConst C₀ c C₁ CT T * Real.sqrt K) := by
  set G : ℝ := 1 / (1 - Real.exp (-c / 2)) with hG
  have hG0 : 0 ≤ G := by
    have : Real.exp (-c / 2) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
    rw [hG]; exact div_nonneg zero_le_one (by linarith)
  intro Ω mΩ P _ ℱ D Sd hD K hK0 hK
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := exists_globalZ hW P ℱ D Sd hD
  refine ⟨Z, hZ1, hZ3, fun a ha => ?_⟩
  have hDm : ∀ τ : ℝ, 0 ≤ τ → AEStronglyMeasurable (D τ) P := by
    intro τ hτ
    have := (hD τ hτ).sq_int τ ⟨hτ, le_rfl⟩
    simpa using this.aestronglyMeasurable
  have haT : a ≤ a + T := by linarith
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := window_piece hCT0 hWT P ℱ D Sd hD hK0 hK ha hT.le haT le_rfl
  -- the window identity
  have hid : ∀ᵐ ω ∂P, ∀ t ∈ Icc a (a + T), Z t ω = V t a (Z a ω) + W t ω := by
    have hq : ∀ᵐ ω ∂P, ∀ q ∈ ratIcc a (a + T), Z q ω = V q a (Z a ω) + W q ω := by
      rw [ae_ball_iff (countable_ratIcc a (a + T))]
      intro q hq
      have hqm : q ∈ Icc a (a + T) := ratIcc_subset haT hq
      have hq0 : 0 ≤ q := ha.trans hqm.1
      have hDt : ∀ τ ∈ Icc (0 : ℝ) q, AEStronglyMeasurable (D τ) P := fun τ hτ => hDm τ hτ.1
      have hDa : ∀ τ ∈ Icc (0 : ℝ) a, AEStronglyMeasurable (D τ) P := fun τ hτ => hDm τ hτ.1
      have hDs : ∀ τ ∈ Icc a q, AEStronglyMeasurable (D τ) P := fun τ hτ => hDm τ (ha.trans hτ.1)
      exact sc_concat ha hqm.1 hDt (fun r hr0 hra => (hV q hq0).2.1 r a q hr0 hra hqm.1 le_rfl)
        (hZ2 q hq0) (hZ2 a ha) (hW2 q hqm)
        ((isStochConv_iff (hZ2 q hq0) hDt).1 (hZ1 q hq0))
        ((isStochConv_iff (hZ2 a ha) hDa).1 (hZ1 a ha))
        ((isStochConv_iff (hW2 q hqm) hDs).1 (hW1 q ⟨hqm.1, hqm.2⟩))
    filter_upwards [hq, hW3, hZ3] with ω hq hWc hZc
    have hcz : ContinuousOn (fun t => Z t ω) (Icc a (a + T)) :=
      hZc.mono fun t ht => (ha.trans ht.1 : (0:ℝ) ≤ t)
    have hcv : ContinuousOn (fun t => V t a (Z a ω)) (Icc a (a + T)) := by
      have h := (hV (a + T) (by linarith)).2.2 (Z a ω)
      have hc : ContinuousOn (fun t : ℝ => (t, a)) (Icc a (a + T)) :=
        (continuous_id.prodMk continuous_const).continuousOn
      refine h.comp hc fun t ht => ?_
      exact ⟨ha, ht.1, ht.2⟩
    exact eqOn_Icc_of_ratIcc haT hcz (hcv.add hWc) hq
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂P, (⨆ t ∈ Icc a (a + T), ‖Z t ω‖ₑ) ≤
      ENNReal.ofReal C₀ * ‖Z a ω‖ₑ + ⨆ t ∈ Icc a (a + T), ‖W t ω‖ₑ := by
    filter_upwards [hid] with ω hω
    refine iSup₂_le fun t ht => ?_
    rw [hω t ht]
    refine enorm_add_le _ _ |>.trans (add_le_add ?_ ?_)
    · refine enorm_apply_le (V t a) hC0 ?_ _
      refine (hdec a t ha ht.1).trans ?_
      have : Real.exp (-c * (t - a)) ≤ 1 := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith [ht.1])
      nlinarith
    · exact le_iSup₂ (f := fun t (_ : t ∈ Icc a (a + T)) => ‖W t ω‖ₑ) t ht
  have hfm : AEMeasurable (fun ω => ENNReal.ofReal C₀ * ‖Z a ω‖ₑ) P :=
    ((hZ2 a ha).enorm).const_mul _
  have hgm : AEMeasurable (fun ω => ⨆ t ∈ Icc a (a + T), ‖W t ω‖ₑ) P :=
    aemeasurable_supIcc haT hW2 hW3
  -- the norms of the two terms
  have hA : (∫⁻ ω, (ENNReal.ofReal C₀ * ‖Z a ω‖ₑ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (C₀ * (C₀ * G * Real.sqrt (C₁ * (K * 1)))) := by
    have e : ∫⁻ ω, (ENNReal.ofReal C₀ * ‖Z a ω‖ₑ) ^ 2 ∂P =
        ENNReal.ofReal C₀ ^ 2 * ∫⁻ ω, ‖Z a ω‖ₑ ^ 2 ∂P := by
      simp_rw [mul_pow]
      rw [lintegral_const_mul' _ _ (by simp)]
    rw [e, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← eLpNorm_two_eq (hZ2 a ha)]
    have e2 : (ENNReal.ofReal C₀ ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal C₀ := by
      rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
    rw [e2, ENNReal.ofReal_mul hC0]
    exact mul_le_mul' le_rfl
      (history_bound hV hC0 hc hdec hC1 h1 P ℱ D Sd hD hK0 hK Z hZ1 hZ2 ha)
  have hB : (∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖W t ω‖ₑ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (CT * (K * T))) := by
    calc _ ≤ (ENNReal.ofReal (CT * (K * T))) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hW4 (by norm_num)
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  calc (∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖Z t ω‖ₑ) ^ 2 ∂P) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ω, (ENNReal.ofReal C₀ * ‖Z a ω‖ₑ + ⨆ t ∈ Icc a (a + T), ‖W t ω‖ₑ) ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by norm_num)
        filter_upwards [hpt] with ω hω
        exact pow_le_pow_left' hω 2
    _ ≤ (∫⁻ ω, (ENNReal.ofReal C₀ * ‖Z a ω‖ₑ) ^ 2 ∂P) ^ (1 / 2 : ℝ) +
        (∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖W t ω‖ₑ) ^ 2 ∂P) ^ (1 / 2 : ℝ) :=
        lintegral_sq_add_le hfm hgm
    _ ≤ ENNReal.ofReal (C₀ * (C₀ * G * Real.sqrt (C₁ * (K * 1)))) +
        ENNReal.ofReal (Real.sqrt (CT * (K * T))) := add_le_add hA hB
    _ = ENNReal.ofReal (coreConst C₀ c C₁ CT T * Real.sqrt K) := by
        rw [coreConst, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [mul_one, Real.sqrt_mul hC1, Real.sqrt_mul hCT0, Real.sqrt_mul hK0, Real.sqrt_mul hCT0 T]
        ring

end HRS.Uniform.Q48d
