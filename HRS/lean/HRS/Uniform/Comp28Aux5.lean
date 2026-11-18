import HRS.Uniform.Comp28Aux4

/-!
# COMP-28, part 5: assembly of Proposition 3.28 (smooth assertion), positive horizon

`smooth_pos_w`: for `a + T > 0` the bound `K e^{-ca} E‖X₀ - X₀'‖ + E‖R‖ + ½K² E∫ w_a² ‖Σ - Cb‖` on the smooth distance of the
window laws.  (The degenerate case `a = T = 0` is `smooth_zero_w`.)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.LindebergAux

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

lemma windowPath_congr_a {a T : ℝ} {Y Y' : ℝ → Ω → E} {ω : Ω}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, Y (a + t) ω = Y' (a + t) ω) : windowPath a T Y ω = windowPath a T Y' ω := by
  have e : (fun t : Set.Icc (0 : ℝ) T => Y (a + (t : ℝ)) ω) =
      fun t : Set.Icc (0 : ℝ) T => Y' (a + (t : ℝ)) ω := funext fun t => h (t : ℝ) t.2
  by_cases hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y (a + (t : ℝ)) ω
  · have hc' : Continuous fun t : Set.Icc (0 : ℝ) T => Y' (a + (t : ℝ)) ω := e ▸ hc
    have e1 : windowPath a T Y ω = (⟨fun t => Y (a + (t : ℝ)) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, E)) := by
      unfold windowPath; exact dif_pos hc
    have e2 : windowPath a T Y' ω = (⟨fun t => Y' (a + (t : ℝ)) ω, hc'⟩ : C(Set.Icc (0 : ℝ) T, E)) := by
      unfold windowPath; exact dif_pos hc'
    rw [e1, e2]
    exact ContinuousMap.ext fun t => congrFun e t
  · have hc' : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => Y' (a + (t : ℝ)) ω := e ▸ hc
    have e1 : windowPath a T Y ω = 0 := by unfold windowPath; exact dif_neg hc
    have e2 : windowPath a T Y' ω = 0 := by unfold windowPath; exact dif_neg hc'
    rw [e1, e2]

lemma aemeasurable_windowPath_a (P : Measure Ω) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hT' : 0 < a + T)
    (Y : ℝ → Ω → E) (hY : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (Y t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) :
    AEMeasurable (windowPath a T Y) P := by
  have h0 := aemeasurable_windowPath P hT' Y hY hc
  have h1 : AEMeasurable (fun ω => resWin a T ha hT (windowPath 0 (a + T) Y ω)) P :=
    (resWin a T ha hT).continuous.measurable.comp_aemeasurable h0
  refine h1.congr ?_
  filter_upwards [hc] with ω hω
  exact (windowPath_eq_resWin ha hT Y hω).symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable (P : Measure Ω) [IsProbabilityMeasure P]

lemma lintegral_wdisc_eq {ℱ : Filtration ℝ mΩ} {T : ℝ} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} (hCb : IsDetCovDensity T Cb) {c a : ℝ} (hc : 0 ≤ c) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal
        (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (Sg r ω - Cb r))) ∂P =
      ENNReal.ofReal (covDiscW P T (fun σ => wt c a σ ^ 2) Sg Cb) := by
  have hwm : Measurable fun σ : ℝ => wt c a σ ^ 2 := ((wt_continuous c a).pow 2).measurable
  have hB : ∀ σ, wt c a σ ^ 2 ≤ 1 := fun σ => pow_le_one₀ (wt_pos _ _ _).le (wt_le_one hc a σ)
  have hint := wdisc_integrable P hM hCb hwm (fun σ => sq_nonneg _) hB
  have hpath := wdisc_pathint P hM hCb hwm (fun σ => sq_nonneg _) hB
  unfold covDiscW
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ =>
      mul_nonneg (sq_nonneg _) (traceNormForm_nonneg _))]
  refine lintegral_congr_ae ?_
  filter_upwards [hpath] with ω hω
  rw [ofReal_integral_eq_lintegral_ofReal hω
    (ae_of_all _ fun σ => mul_nonneg (sq_nonneg _) (traceNormForm_nonneg _))]
  rfl

end Helpers

end HRS.Uniform.Comp28
