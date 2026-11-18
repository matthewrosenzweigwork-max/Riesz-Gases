import HRS.MS.SuppU1Aux4

/-!
# U1 aux 5: diagonal null sets, the envelope of a mollified kernel (product Haar measure).
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace HRS.Whole.U1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

instance u1_prod_negInvariant : (μ.prod μ).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular (μ.prod μ)

lemma u1_diag_null (hd : 1 ≤ Module.finrank ℝ E) (w : E) :
    (μ.prod μ) {t : E × E | t.1 - t.2 = w} = 0 := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hmeas : MeasurableSet {t : E × E | t.1 - t.2 = w} :=
    measurableSet_eq_fun (measurable_fst.sub measurable_snd) measurable_const
  rw [Measure.prod_apply hmeas]
  have : ∀ x : E, μ (Prod.mk x ⁻¹' {t : E × E | t.1 - t.2 = w}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {t : E × E | t.1 - t.2 = w} = {x - w} := by
      ext y
      simp only [mem_preimage, mem_setOf_eq, mem_singleton_iff]
      constructor
      · intro h; rw [← h, sub_sub_cancel]
      · rintro rfl; rw [sub_sub_cancel]
    rw [this]; exact measure_singleton _
  rw [lintegral_congr this]; simp

lemma u1_ae_ne (hd : 1 ≤ Module.finrank ℝ E) (w : E) : ∀ᵐ x ∂μ, x ≠ w := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have : μ {w} = 0 := measure_singleton w
  simpa [ae_iff] using this

lemma u1_mollify_envelope {s : ℝ} (hs : 0 ≤ s) (hsd : s < (Module.finrank ℝ E : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ψ f : E × E → ℝ) (ε Cψ B : ℝ), 0 < ε → 0 ≤ Cψ → 0 ≤ B →
      (∀ t, 0 ≤ ψ t) → (∀ t, ψ t ≠ 0 → ‖t.1‖ ≤ ε ∧ ‖t.2‖ ≤ ε) → (∀ t, ψ t ≤ Cψ) →
      (∀ᵐ q ∂(μ.prod μ), |f q| ≤ B * u1Vs s ‖q.1 - q.2‖) → ∀ p : E × E, p.1 ≠ p.2 →
      |∫ t, ψ t * f (p - t) ∂(μ.prod μ)|
        ≤ Cψ * (K * ε ^ Module.finrank ℝ E) ^ 2 * B * u1Vs s ‖p.1 - p.2‖ := by
  have hd0 : (0:ℝ) < Module.finrank ℝ E := lt_of_le_of_lt hs hsd
  have hd : 1 ≤ Module.finrank ℝ E := by exact_mod_cast hd0
  obtain ⟨K, hK0, hK⟩ := u1_avg_estimate μ hs hsd
  refine ⟨K, hK0, fun ψ f ε Cψ B hε hC hB hψ0 hψS hψC hf p hp => ?_⟩
  set w : E := p.1 - p.2 with hwdef
  have hw : w ≠ 0 := sub_ne_zero.mpr hp
  set S : Set (E × E) := closedBall (0:E) ε ×ˢ closedBall (0:E) ε with hSdef
  have hS : MeasurableSet S := measurableSet_closedBall.prod measurableSet_closedBall
  set g : E × E → ℝ := fun t => u1Vs s ‖w - (t.1 - t.2)‖ with hgdef
  have hae : ∀ᵐ t ∂(μ.prod μ), ‖ψ t * f (p - t)‖ ≤ Cψ * B * S.indicator g t := by
    have h1 : ∀ᵐ t ∂(μ.prod μ), |f (p - t)| ≤ B * u1Vs s ‖(p - t).1 - (p - t).2‖ :=
      (Measure.measurePreserving_sub_left (μ.prod μ) p).quasiMeasurePreserving.ae hf
    filter_upwards [h1] with t ht
    by_cases htS : t ∈ S
    · rw [indicator_of_mem htS, norm_mul, Real.norm_of_nonneg (hψ0 t)]
      have : (p - t).1 - (p - t).2 = w - (t.1 - t.2) := by
        simp only [Prod.fst_sub, Prod.snd_sub, hwdef]; abel
      rw [this] at ht
      rw [Real.norm_eq_abs]
      calc ψ t * |f (p - t)| ≤ Cψ * (B * u1Vs s ‖w - (t.1 - t.2)‖) :=
            mul_le_mul (hψC t) ht (abs_nonneg _) hC
        _ = Cψ * B * g t := by simp only [hgdef]; ring
    · have : ψ t = 0 := by
        by_contra h
        have := hψS t h
        exact htS (by simpa [hSdef] using this)
      rw [this, indicator_of_notMem htS]; simp
  set c : ℝ := K * ε ^ Module.finrank ℝ E with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hVw : 1 ≤ u1Vs s ‖w‖ := u1Vs_ge_one (norm_nonneg w)
  have hinner : ∀ t1 : E, t1 ≠ w → ∫⁻ t2 in closedBall (0:E) ε, ENNReal.ofReal (g (t1, t2)) ∂μ
      ≤ ENNReal.ofReal (c * u1Vs s ‖w - t1‖) := by
    intro t1 ht1
    have hw1 : w - t1 ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    have := hK (fun t2 => (w - t1) + t2) (w - t1) ε hε hw1 (measurePreserving_add_left μ (w - t1))
      (Homeomorph.addLeft (w - t1)).measurableEmbedding (fun t ht => by
        have := abs_norm_sub_norm_le ((w - t1) + t) (w - t1)
        rw [add_sub_cancel_left] at this; exact this.trans ht)
    refine le_trans (le_of_eq ?_) this
    refine lintegral_congr fun t2 => ?_
    have : w - (t1 - t2) = w - t1 + t2 := by abel
    simp only [hgdef, this]
  have hnull : ∀ᵐ t1 ∂μ, t1 ≠ w := u1_ae_ne μ hd w
  have houter : ∫⁻ t1 in closedBall (0:E) ε, ENNReal.ofReal (c * u1Vs s ‖w - t1‖) ∂μ
      ≤ ENNReal.ofReal c * ENNReal.ofReal (c * u1Vs s ‖w‖) := by
    have h2 := hK (fun t => w - t) w ε hε hw (Measure.measurePreserving_sub_left μ w)
      (Homeomorph.subLeft w).measurableEmbedding (fun t ht => by
        have := abs_norm_sub_norm_le (w - t) w
        rw [sub_sub_cancel_left, norm_neg] at this; exact this.trans ht)
    calc ∫⁻ t1 in closedBall (0:E) ε, ENNReal.ofReal (c * u1Vs s ‖w - t1‖) ∂μ
        = ∫⁻ t1 in closedBall (0:E) ε, (ENNReal.ofReal c * ENNReal.ofReal (u1Vs s ‖w - t1‖)) ∂μ := by
          refine lintegral_congr fun t1 => ?_; rw [ENNReal.ofReal_mul hc0]
      _ = ENNReal.ofReal c * ∫⁻ t1 in closedBall (0:E) ε, ENNReal.ofReal (u1Vs s ‖w - t1‖) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (c * u1Vs s ‖w‖) := by
          gcongr
  have hgm : Measurable (fun t : E × E => ENNReal.ofReal (g t)) :=
    ENNReal.measurable_ofReal.comp ((u1Vs_measurable (E := E) s).comp
      (measurable_const.sub (measurable_fst.sub measurable_snd)))
  have hmain : ∫⁻ t in S, ENNReal.ofReal (g t) ∂(μ.prod μ)
      ≤ ENNReal.ofReal c * ENNReal.ofReal (c * u1Vs s ‖w‖) := by
    rw [hSdef, ← Measure.prod_restrict, lintegral_prod _ hgm.aemeasurable]
    calc ∫⁻ t1 in closedBall (0:E) ε, ∫⁻ t2 in closedBall (0:E) ε, ENNReal.ofReal (g (t1, t2)) ∂μ ∂μ
        ≤ ∫⁻ t1 in closedBall (0:E) ε, ENNReal.ofReal (c * u1Vs s ‖w - t1‖) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae hnull] with t1 ht1 using hinner t1 ht1
      _ ≤ _ := houter
  have hlin : ∫⁻ t, ENNReal.ofReal (Cψ * B * S.indicator g t) ∂(μ.prod μ)
      ≤ ENNReal.ofReal (Cψ * B) * (ENNReal.ofReal c * ENNReal.ofReal (c * u1Vs s ‖w‖)) := by
    have : ∀ t, ENNReal.ofReal (Cψ * B * S.indicator g t)
        = S.indicator (fun t => ENNReal.ofReal (Cψ * B) * ENNReal.ofReal (g t)) t := by
      intro t
      by_cases ht : t ∈ S
      · simp [indicator_of_mem ht, ENNReal.ofReal_mul (mul_nonneg hC hB)]
      · simp [indicator_of_notMem ht]
    simp_rw [this]
    rw [lintegral_indicator hS, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
  have hfin : ENNReal.ofReal (Cψ * B) * (ENNReal.ofReal c * ENNReal.ofReal (c * u1Vs s ‖w‖)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hV0 : 0 ≤ u1Vs s ‖w‖ := by linarith
  calc |∫ t, ψ t * f (p - t) ∂(μ.prod μ)| = ‖∫ t, ψ t * f (p - t) ∂(μ.prod μ)‖ := (Real.norm_eq_abs _).symm
    _ ≤ (∫⁻ t, ENNReal.ofReal ‖ψ t * f (p - t)‖ ∂(μ.prod μ)).toReal := norm_integral_le_lintegral_norm _
    _ ≤ (∫⁻ t, ENNReal.ofReal (Cψ * B * S.indicator g t) ∂(μ.prod μ)).toReal := by
        refine ENNReal.toReal_mono (ne_top_of_le_ne_top hfin hlin) ?_
        exact lintegral_mono_ae (hae.mono fun t ht => ENNReal.ofReal_le_ofReal ht)
    _ ≤ (ENNReal.ofReal (Cψ * B) * (ENNReal.ofReal c * ENNReal.ofReal (c * u1Vs s ‖w‖))).toReal :=
        ENNReal.toReal_mono hfin hlin
    _ = Cψ * c ^ 2 * B * u1Vs s ‖w‖ := by
        rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (mul_nonneg hC hB),
          ENNReal.toReal_ofReal (by positivity)]
        ring

end HRS.Whole.U1
