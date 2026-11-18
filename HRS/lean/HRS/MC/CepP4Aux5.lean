import HRS.MC.CepP4Aux4

/-!
# Packet P4, Aux5: equality of the integrals of a good test function against `selectedLaw` and `f t`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP4

open HRS HRS.MC.CepP3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

theorem isProb_selectedLaw [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → Config d N}
    (hX : ∀ t : ℝ, Measurable (X (Real.toNNReal t))) (t : ℝ) :
    IsProbabilityMeasure (selectedLaw P X t) := by
  unfold selectedLaw law
  exact (Measure.isProbabilityMeasure_map_iff (hX t).aemeasurable).2 inferInstance

theorem lintegral_indicator_Ioo {T : ℝ} {S : Set ℝ} (hS : MeasurableSet S) (hsub : S ⊆ Ioo 0 T)
    (v : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioo 0 T, S.indicator v t = ∫⁻ t in S, v t := by
  rw [lintegral_indicator hS, Measure.restrict_restrict hS, inter_eq_left.2 hsub]

theorem slice_good [IsProbabilityMeasure P] {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {D : DynData d} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X)
    (hm : Measurable (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2))
    (hXm : ∀ t : ℝ, Measurable (X (Real.toNNReal t)))
    {f : ℝ → Config d N → ℝ}
    (hgc : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => f p.1 (mkC p.2)) (Ioo 0 T ×ˢ liftedFree d N))
    (hfs : Measurable (ghat f T))
    (hf0 : ∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x)
    (hstar : ∀ {G : ℝ × Config d N → ℝ≥0∞}, Measurable G →
      ∫⁻ t in Ioo 0 T, ∫⁻ x in (collisionSet d N)ᶜ, G (t, x) ∂(selectedLaw P X t)
      = ∫⁻ t in Ioo 0 T, ∫⁻ x in (collisionSet d N)ᶜ, ENNReal.ofReal (fhat f T (t, x)) * G (t, x))
    {ψ : Config d N → ℝ} {δ : ℝ} (hψ : Good ψ δ) {t0 : ℝ} (ht0 : t0 ∈ Ioo 0 T) :
    ∫⁻ x, ENNReal.ofReal (ψ x) ∂(selectedLaw P X t0)
      = ∫⁻ x in (collisionSet d N)ᶜ, ENNReal.ofReal (fhat f T (t0, x)) * ENNReal.ofReal (ψ x) := by
  classical
  have hCm : MeasurableSet (collisionSet d N)ᶜ := (isClosed_collisionSet d N).measurableSet.compl
  have hψm : Measurable ψ := hψ.1.measurable
  haveI := isProb_selectedLaw (P := P) hXm
  set ψb : BoundedContinuousFunction (Fin N → Torus d) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨ψ, hψ.1⟩ with hψb
  have hψb_apply : ∀ x, ψb x = ψ x := fun x => rfl
  -- the two sides as functions of time
  set A : ℝ → ℝ := fun t => ∫ x, ψ x ∂(selectedLaw P X t) with hA
  set B : ℝ → ℝ := Bfun f T ψ with hB
  have hAnn : ∀ t, 0 ≤ A t := fun t => integral_nonneg (fun x => hψ.2.1 x)
  have hBnn : ∀ t, 0 ≤ B t := fun t => integral_nonneg (fun Y => mul_nonneg (hψ.2.1 _) (ghat_nonneg hf0 _))
  -- lintegral of ψ against the law is ofReal of A
  have hlA : ∀ t, ∫⁻ x, ENNReal.ofReal (ψ x) ∂(selectedLaw P X t) = ENNReal.ofReal (A t) := by
    intro t
    exact (ofReal_integral_eq_lintegral_ofReal (ψb.integrable (selectedLaw P X t))
      (Eventually.of_forall fun x => hψ.2.1 x)).symm
  have hlA' : ∀ t, ∫⁻ x in (collisionSet d N)ᶜ, ENNReal.ofReal (ψ x) ∂(selectedLaw P X t)
      = ENNReal.ofReal (A t) := by
    intro t
    rw [← hlA t]
    refine setLIntegral_eq_of_support_subset (fun x hx => ?_)
    have : ψ x ≠ 0 := by intro h0; apply hx; simp [h0]
    exact hψ.notMem this
  -- identity on sets of times
  have hset : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Ioo 0 T →
      ∫⁻ t in S, ENNReal.ofReal (A t) = ∫⁻ t in S, ENNReal.ofReal (B t) := by
    intro S hS hsub
    have hG : Measurable (fun q : ℝ × Config d N => S.indicator (fun _ => (1 : ℝ≥0∞)) q.1 *
        ENNReal.ofReal (ψ q.2)) :=
      ((measurable_const.indicator hS).comp measurable_fst).mul
        (ENNReal.measurable_ofReal.comp (hψm.comp measurable_snd))
    have h := hstar hG
    have hL : ∫⁻ t in Ioo 0 T, ∫⁻ x in (collisionSet d N)ᶜ,
        S.indicator (fun _ => (1 : ℝ≥0∞)) t * ENNReal.ofReal (ψ x) ∂(selectedLaw P X t)
        = ∫⁻ t in S, ENNReal.ofReal (A t) := by
      rw [← lintegral_indicator_Ioo hS hsub]
      refine lintegral_congr fun t => ?_
      rw [lintegral_const_mul _ (show Measurable (fun x => ENNReal.ofReal (ψ x)) from
        ENNReal.measurable_ofReal.comp hψm), hlA' t]
      by_cases ht : t ∈ S <;> simp [Set.indicator, ht]
    have hR : ∫⁻ t in Ioo 0 T, ∫⁻ x in (collisionSet d N)ᶜ, ENNReal.ofReal (fhat f T (t, x)) *
        (S.indicator (fun _ => (1 : ℝ≥0∞)) t * ENNReal.ofReal (ψ x))
        = ∫⁻ t in S, ENNReal.ofReal (B t) := by
      rw [← lintegral_indicator_Ioo hS hsub]
      refine lintegral_congr fun t => ?_
      by_cases ht : t ∈ S
      · have htI : t ∈ Ioo 0 T := hsub ht
        have : ∀ x, ENNReal.ofReal (fhat f T (t, x)) *
            (S.indicator (fun _ => (1 : ℝ≥0∞)) t * ENNReal.ofReal (ψ x)) =
            ENNReal.ofReal (fhat f T (t, x)) * ENNReal.ofReal (ψ x) := by
          intro x; simp [Set.indicator, ht]
        simp only [this]
        rw [lintegral_eq_ofReal_Bfun hgc hfs hf0 hψ htI]
        simp [Set.indicator, ht, hB]
      · simp [Set.indicator, ht]
    rw [← hL, ← hR]
    exact h
  -- continuity
  set a := t0 / 2 with ha
  set b := (t0 + T) / 2 with hb
  have hab : Ioo a b ⊆ Ioo 0 T := fun t ht => ⟨by linarith [ht.1, ht0.1], by linarith [ht.2, ht0.2]⟩
  have ht0ab : t0 ∈ Ioo a b := ⟨by linarith [ht0.1], by linarith [ht0.2]⟩
  have hAc : ContinuousOn A (Ioo a b) := by
    have h1 := selectedLaw_narrow_continuous hX ψb
    refine h1.mono (fun t ht => ?_)
    exact ⟨by linarith [ht.1, ht0.1], by linarith [ht.2, ht0.2]⟩
  have hBc : ContinuousOn B (Ioo a b) := fun t ht =>
    (continuousAt_Bfun hgc hfs hψ (hab ht)).continuousWithinAt
  -- almost everywhere equality on the interval
  have hae : (fun t => ENNReal.ofReal (A t)) =ᵐ[volume.restrict (Ioo a b)] (fun t => ENNReal.ofReal (B t)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (μ := volume.restrict (Ioo a b))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hAc.aemeasurable measurableSet_Ioo))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hBc.aemeasurable measurableSet_Ioo)) ?_
    intro s hs _
    rw [Measure.restrict_restrict hs]
    exact hset (s ∩ Ioo a b) (hs.inter measurableSet_Ioo) (inter_subset_right.trans hab)
  have hae2 : A =ᵐ[volume.restrict (Ioo a b)] B := by
    filter_upwards [hae] with t ht
    exact (ENNReal.ofReal_eq_ofReal_iff (hAnn t) (hBnn t)).1 ht
  have hEq := Measure.eqOn_open_of_ae_eq hae2 isOpen_Ioo hAc hBc ht0ab
  rw [hlA t0, lintegral_eq_ofReal_Bfun hgc hfs hf0 hψ ht0]
  have : A t0 = B t0 := hEq
  rw [this]

end HRS.MC.CepP4
