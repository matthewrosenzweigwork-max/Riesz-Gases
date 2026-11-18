import HRS.MS.R2WinErrAux4
import HRS.MS.FldRemAux2

/-!
# S10.4 packet E3: the forcing remainder, abstract core (part (b) of `r2_window_errors`)

The window remainder `D_b(u)_α` is bounded, for all `u ∈ [0,T]` simultaneously, by three nonnegative pathwise quantities
(the Duhamel decomposition between `b` and `b+u`; no differentiation of a parametric integral is needed):
`∫_0^b |F0_α(r)| dr` (the past, tested against `U(r,b)φ_α`), `∫_b^{b+T} |F1_α(r)| dr` (the instantaneous forcing),
`∬_{b ≤ s ≤ b+T, r ≤ s} |F2_α(s,r)| dr ds` (the time derivative of the orbit).  With the expectation bounds
`κ w_α e^{-c(b-r)}`, `κ w_α`, `κ w_α e^{-c(s-r)}` (`κ = C δ_N`, `Σ w_α < ∞`) the conclusion is `E sup_u ‖D_b(u)‖_{ℓ²} ≤ coef κ W (1/c + T + T/c)`.
`s104_part_b_core` is the shared abstract core; helper names carry the prefix `s104_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2WinErr

open HRS.Whole

lemma s104_lintegral_exp {c : ℝ} (hc : 0 < c) {b : ℝ} (hb : 0 ≤ b) :
    ∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal (Real.exp (-c * (b - r))) ≤ ENNReal.ofReal (1 / c) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Icc (by fun_prop))
    (Eventually.of_forall fun r => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := s104_exp_integral (c := c / 2) (by positivity) hb
  have e : ∀ r : ℝ, Real.exp (-2 * (c / 2) * (b - r)) = Real.exp (-c * (b - r)) := fun r => by
    congr 1; ring
  simp_rw [e] at h
  have e2 : 1 / (2 * (c / 2)) = 1 / c := by field_simp
  rwa [e2] at h

/-- Integral over a set of the exponential kernel `e^{-c(s-r)} 1_{r ≤ s}`. -/
def s104_psi (c : ℝ) (p : ℝ × ℝ) : ℝ := if p.2 ≤ p.1 then Real.exp (-c * (p.1 - p.2)) else 0

lemma s104_psi_lintegral {c : ℝ} (hc : 0 < c) {L s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ r in Set.Icc (0 : ℝ) L, ENNReal.ofReal (s104_psi c (s, r)) ≤ ENNReal.ofReal (1 / c) := by
  set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-c * (s - r))) with hg
  have h1 : ∫⁻ r in Set.Icc (0 : ℝ) L, ENNReal.ofReal (s104_psi c (s, r)) ≤
      ∫⁻ r in Set.Icc (0 : ℝ) L, (Set.Icc (0 : ℝ) s).indicator g r :=
    setLIntegral_mono' measurableSet_Icc fun r hr => by
      unfold s104_psi
      by_cases h : r ≤ s
      · simp only [h, ite_true]
        rw [Set.indicator_of_mem (show r ∈ Set.Icc (0 : ℝ) s from ⟨hr.1, h⟩)]
      · simp [h]
  refine h1.trans ?_
  rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  calc ∫⁻ r in Set.Icc (0 : ℝ) s ∩ Set.Icc (0 : ℝ) L, g r
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) s, g r :=
        lintegral_mono' (Measure.restrict_mono Set.inter_subset_left le_rfl) le_rfl
    _ ≤ _ := s104_lintegral_exp hc hs

lemma s104_swap_bound {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    [SFinite P] (μ : Measure β) [SFinite μ] (g : Ω → β → ℝ)
    (hg : AEMeasurable (fun p : Ω × β => ENNReal.ofReal |g p.1 p.2|) (P.prod μ))
    (K : β → ℝ≥0∞) (hK : ∀ᵐ x ∂μ, ∫⁻ ζ, ENNReal.ofReal |g ζ x| ∂P ≤ K x) :
    ∫⁻ ζ, (∫⁻ x, ENNReal.ofReal |g ζ x| ∂μ) ∂P ≤ ∫⁻ x, K x ∂μ := by
  have := lintegral_lintegral_swap (μ := P) (ν := μ) (f := fun ζ x => ENNReal.ofReal |g ζ x|) hg
  rw [this]
  exact lintegral_mono_ae hK

/-- The abstract core of part (b): see the module docstring. -/
theorem s104_part_b_core {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [Countable ι] {b T c κ coef : ℝ} (hc : 0 < c) (hb : 0 ≤ b) (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hcoef : 0 ≤ coef)
    (w : ι → ℝ) (hw0 : ∀ α, 0 ≤ w α) (hwS : Summable w)
    (a : ι → ℝ → Ω → ℝ) (F0 F1 : ι → ℝ → Ω → ℝ) (F2 : ι → ℝ × ℝ → Ω → ℝ)
    (hH : ∀ᵐ ζ ∂P, ∀ α, ∀ u ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal |a α u ζ| ≤ ENNReal.ofReal coef *
      ((∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal |F0 α r ζ|) +
        (∫⁻ r in Set.Icc b (b + T), ENNReal.ofReal |F1 α r ζ|) +
        (∫⁻ p in (Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)), ENNReal.ofReal |F2 α p ζ|)))
    (M0 : ∀ α, AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |F0 α p.2 p.1|)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) b))))
    (M1 : ∀ α, AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |F1 α p.2 p.1|)
      (P.prod (volume.restrict (Set.Icc b (b + T)))))
    (M2 : ∀ α, AEMeasurable (fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal |F2 α p.2 p.1|)
      (P.prod (volume.restrict ((Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T))))))
    (E0 : ∀ α, ∀ r ∈ Set.Icc (0 : ℝ) b, ∫⁻ ζ, ENNReal.ofReal |F0 α r ζ| ∂P ≤
      ENNReal.ofReal (κ * w α * Real.exp (-c * (b - r))))
    (E1 : ∀ α, ∀ r ∈ Set.Icc b (b + T), ∫⁻ ζ, ENNReal.ofReal |F1 α r ζ| ∂P ≤ ENNReal.ofReal (κ * w α))
    (E2 : ∀ α, ∀ p ∈ (Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)),
      ∫⁻ ζ, ENNReal.ofReal |F2 α p ζ| ∂P ≤ ENNReal.ofReal (κ * w α * s104_psi c p)) :
    ∫⁻ ζ, (⨆ u ∈ Set.Icc (0 : ℝ) T, HRS.Whole.l2NormE (fun α => a α u ζ)) ∂P ≤
      ENNReal.ofReal (coef * κ * (1 / c + T + T * (1 / c)) * ∑' α, w α) := by
  set μ0 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) b) with hμ0
  set μ1 : Measure ℝ := volume.restrict (Set.Icc b (b + T)) with hμ1
  set ν2 : Measure (ℝ × ℝ) := volume.restrict ((Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T))) with hν2
  set A : ι → Ω → ℝ≥0∞ := fun α ζ => ∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal |F0 α r ζ| with hA
  set B : ι → Ω → ℝ≥0∞ := fun α ζ => ∫⁻ r in Set.Icc b (b + T), ENNReal.ofReal |F1 α r ζ| with hB
  set Cc : ι → Ω → ℝ≥0∞ := fun α ζ =>
    ∫⁻ p in (Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)), ENNReal.ofReal |F2 α p ζ| with hC
  -- step 1: pathwise domination by the ℓ¹ sums
  have h1 : ∫⁻ ζ, (⨆ u ∈ Set.Icc (0 : ℝ) T, HRS.Whole.l2NormE (fun α => a α u ζ)) ∂P ≤
      ∫⁻ ζ, ∑' α, ENNReal.ofReal coef * (A α ζ + B α ζ + Cc α ζ) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hH] with ζ hζ
    refine iSup₂_le fun u hu => (HRS.MS.S53.s53_l2NormE_le _).trans ?_
    exact ENNReal.tsum_le_tsum fun α => hζ α u hu
  refine h1.trans ?_
  -- step 2: swap the sum and the expectation
  have hAm : ∀ α, AEMeasurable (A α) P := fun α => (M0 α).lintegral_prod_right'
  have hBm : ∀ α, AEMeasurable (B α) P := fun α => (M1 α).lintegral_prod_right'
  have hCm : ∀ α, AEMeasurable (Cc α) P := fun α => (M2 α).lintegral_prod_right'
  rw [lintegral_tsum (f := fun α ζ => ENNReal.ofReal coef * (A α ζ + B α ζ + Cc α ζ))
    (fun α => (((hAm α).add (hBm α)).add (hCm α)).const_mul _)]
  -- step 3: the three expectations
  have hEA : ∀ α, ∫⁻ ζ, A α ζ ∂P ≤ ENNReal.ofReal (κ * w α) * ENNReal.ofReal (1 / c) := by
    intro α
    have := s104_swap_bound P μ0 (fun ζ r => F0 α r ζ) (M0 α)
      (fun r => ENNReal.ofReal (κ * w α * Real.exp (-c * (b - r))))
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => E0 α r hr))
    refine this.trans ?_
    have e : ∀ r, ENNReal.ofReal (κ * w α * Real.exp (-c * (b - r))) =
        ENNReal.ofReal (κ * w α) * ENNReal.ofReal (Real.exp (-c * (b - r))) := fun r =>
      ENNReal.ofReal_mul (mul_nonneg hκ (hw0 α))
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (s104_lintegral_exp hc hb)
  have hEB : ∀ α, ∫⁻ ζ, B α ζ ∂P ≤ ENNReal.ofReal (κ * w α) * ENNReal.ofReal T := by
    intro α
    have := s104_swap_bound P μ1 (fun ζ r => F1 α r ζ) (M1 α) (fun _ => ENNReal.ofReal (κ * w α))
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => E1 α r hr))
    refine this.trans (le_of_eq ?_)
    rw [lintegral_const, hμ1, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    simp
  have hEC : ∀ α, ∫⁻ ζ, Cc α ζ ∂P ≤ ENNReal.ofReal (κ * w α) * (ENNReal.ofReal T * ENNReal.ofReal (1 / c)) := by
    intro α
    have := s104_swap_bound P ν2 (fun ζ p => F2 α p ζ) (M2 α)
      (fun p => ENNReal.ofReal (κ * w α * s104_psi c p))
      ((ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2
        (Eventually.of_forall fun p hp => E2 α p hp))
    refine this.trans ?_
    have e : ∀ p, ENNReal.ofReal (κ * w α * s104_psi c p) =
        ENNReal.ofReal (κ * w α) * ENNReal.ofReal (s104_psi c p) := fun p =>
      ENNReal.ofReal_mul (mul_nonneg hκ (hw0 α))
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul' le_rfl ?_
    have hpsim : Measurable (s104_psi c) := by
      unfold s104_psi
      exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) (by fun_prop) measurable_const
    have hprod : ν2 = μ1.prod (volume.restrict (Set.Icc (0 : ℝ) (b + T))) := by
      rw [hν2, hμ1, Measure.prod_restrict, Measure.volume_eq_prod]
    rw [hprod, lintegral_prod _ (hpsim.ennreal_ofReal.aemeasurable)]
    refine le_trans (lintegral_mono_ae (g := fun _ => ENNReal.ofReal (1 / c)) ?_) (le_of_eq ?_)
    · rw [hμ1]
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact s104_psi_lintegral hc (hb.trans hs.1)
    · rw [lintegral_const, hμ1, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc]
      simp [mul_comm]
  -- step 4: sum over `α`
  have hsum : ∀ α, ENNReal.ofReal coef * (∫⁻ ζ, A α ζ ∂P + ∫⁻ ζ, B α ζ ∂P + ∫⁻ ζ, Cc α ζ ∂P) ≤
      ENNReal.ofReal (coef * κ * (1 / c + T + T * (1 / c)) * w α) := by
    intro α
    calc ENNReal.ofReal coef * (∫⁻ ζ, A α ζ ∂P + ∫⁻ ζ, B α ζ ∂P + ∫⁻ ζ, Cc α ζ ∂P)
        ≤ ENNReal.ofReal coef * (ENNReal.ofReal (κ * w α) * ENNReal.ofReal (1 / c) +
            ENNReal.ofReal (κ * w α) * ENNReal.ofReal T +
            ENNReal.ofReal (κ * w α) * (ENNReal.ofReal T * ENNReal.ofReal (1 / c))) := by
          gcongr
          · exact hEA α
          · exact hEB α
          · exact hEC α
      _ = ENNReal.ofReal (coef * κ * (1 / c + T + T * (1 / c)) * w α) := by
          have hk0 : 0 ≤ κ * w α := mul_nonneg hκ (hw0 α)
          rw [← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul hT,
            ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hcoef]
          congr 1; ring
  calc ∑' α, ∫⁻ ζ, ENNReal.ofReal coef * (A α ζ + B α ζ + Cc α ζ) ∂P
      ≤ ∑' α, ENNReal.ofReal (coef * κ * (1 / c + T + T * (1 / c)) * w α) := by
        refine ENNReal.tsum_le_tsum fun α => ?_
        have e1 := lintegral_add_left' ((hAm α).add (hBm α)) (Cc α)
        have e2 := lintegral_add_left' (hAm α) (B α)
        simp only [Pi.add_apply] at e1 e2
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, e1, e2]
        exact hsum α
    _ = ENNReal.ofReal (coef * κ * (1 / c + T + T * (1 / c)) * ∑' α, w α) := by
        have hK : 0 ≤ coef * κ * (1 / c + T + T * (1 / c)) := by positivity
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun α => mul_nonneg hK (hw0 α))
          (hwS.mul_left _), tsum_mul_left]

end HRS.MS.R2WinErr
