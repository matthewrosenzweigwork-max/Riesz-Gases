import HRS.PDE.MovEAux2

/-!
# MOVE Aux3: from a frequently-bounded sequence to the dual inequality (`movT_lp_lsc`)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS

theorem move_lsc_of_seq {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] {ν Q : Measure α} {νn Qn : ℕ → Measure α} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure Q] [∀ n, IsProbabilityMeasure (νn n)] [∀ n, IsProbabilityMeasure (Qn n)]
    (hν : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(νn n)) atTop (𝓝 (∫ x, φ x ∂ν)))
    (hQ : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(Qn n)) atTop (𝓝 (∫ x, φ x ∂Q)))
    (hacn : ∀ᶠ n in atTop, νn n ≪ Qn n) {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hfreq : ∃ᶠ n in atTop, eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n) ≤ A) :
    ν ≪ Q ∧ eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal p) Q ≤ A := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < q := by
    have h3 : 0 < 1 / q := by
      have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
      linarith
    exact one_div_pos.1 h3
  have hHC : p.HolderConjugate q :=
    Real.holderConjugate_iff.2 ⟨hp, by simpa [one_div] using hpq⟩
  refine move_dual_core hp hpq hA fun φ hφc hφ0 => ?_
  have hfq : ∃ᶠ n in atTop, νn n ≪ Qn n ∧
      eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n) ≤ A := hacn.and_frequently hfreq
  obtain ⟨F, hFdef⟩ : ∃ F : Filter ℕ, F = atTop ⊓ 𝓟 {n | νn n ≪ Qn n ∧
      eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n) ≤ A} := ⟨_, rfl⟩
  haveI : NeBot F := by rw [hFdef]; exact Filter.frequently_iff_neBot.1 hfq
  have hφq : Continuous fun x => φ x ^ q := hφc.rpow_const fun x => Or.inr hq.le
  have hint : ∀ μ : Measure α, IsProbabilityMeasure μ → ∀ f : α → ℝ, Continuous f → (∀ x, 0 ≤ f x) →
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ENNReal.ofReal (∫ x, f x ∂μ) := by
    intro μ hμ f hf hf0
    rw [ofReal_integral_eq_lintegral_ofReal
      (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Eventually.of_forall hf0)]
  have hint2 : ∀ μ : Measure α, IsProbabilityMeasure μ →
      ∫⁻ x, ENNReal.ofReal (φ x) ^ q ∂μ = ENNReal.ofReal (∫ x, φ x ^ q ∂μ) := by
    intro μ hμ
    rw [← hint μ hμ _ hφq fun x => Real.rpow_nonneg (hφ0 x) _]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (hφ0 x) hq.le]
  rw [hint ν inferInstance φ hφc hφ0, hint2 Q inferInstance]
  have h1 := ENNReal.tendsto_ofReal (hν φ hφc)
  have h2 : Tendsto (fun n => A * (ENNReal.ofReal (∫ x, φ x ^ q ∂(Qn n))) ^ (1 / q)) atTop
      (𝓝 (A * (ENNReal.ofReal (∫ x, φ x ^ q ∂Q)) ^ (1 / q))) :=
    ENNReal.Tendsto.const_mul (((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto _).comp
      (ENNReal.tendsto_ofReal (hQ _ hφq))) (Or.inr hA)
  have hFle : F ≤ atTop := by rw [hFdef]; exact inf_le_left
  refine le_of_tendsto_of_tendsto (h1.mono_left hFle) (h2.mono_left hFle) ?_
  have hmem : {n | νn n ≪ Qn n ∧ eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n) ≤ A} ∈ F := by
    rw [hFdef]; exact mem_inf_of_right (mem_principal_self _)
  filter_upwards [hmem] with n hn
  obtain ⟨hac, hnorm⟩ := hn
  have hm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) (Qn n) :=
    (ENNReal.measurable_ofReal.comp hφc.measurable).aemeasurable
  have hl : ∫⁻ x, ENNReal.ofReal (φ x) ∂(νn n) =
      ∫⁻ x, (νn n).rnDeriv (Qn n) x * ENNReal.ofReal (φ x) ∂(Qn n) :=
    (lintegral_rnDeriv_mul hac hm).symm
  rw [← hint (νn n) inferInstance φ hφc hφ0, ← hint2 (Qn n) inferInstance, hl]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (Qn n) hHC
    (Measure.measurable_rnDeriv (νn n) (Qn n)).aemeasurable hm
  refine hH.trans ?_
  gcongr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
    (Measure.measurable_rnDeriv (νn n) (Qn n)).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le] at hnorm
  simpa using hnorm

theorem move_lp_lsc {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {ν Q : Measure α} {νn Qn : ℕ → Measure α} [IsProbabilityMeasure ν] [IsProbabilityMeasure Q]
    [∀ n, IsProbabilityMeasure (νn n)] [∀ n, IsProbabilityMeasure (Qn n)]
    (hν : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(νn n)) atTop (𝓝 (∫ x, φ x ∂ν)))
    (hQ : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(Qn n)) atTop (𝓝 (∫ x, φ x ∂Q)))
    (hacn : ∀ᶠ n in atTop, νn n ≪ Qn n) {p : ℝ} (hp : 1 < p)
    (hlim : liminf (fun n => eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n)) atTop < ⊤) :
    ν ≪ Q ∧ eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal p) Q ≤
      liminf (fun n => eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n)) atTop := by
  set ℓ := liminf (fun n => eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n)) atTop with hℓ
  have hp0 : 0 < p := by linarith
  obtain ⟨q, hpq⟩ : ∃ q : ℝ, 1 / p + 1 / q = 1 := by
    refine ⟨p / (p - 1), ?_⟩
    have : p - 1 ≠ 0 := by linarith
    field_simp
    ring
  have key : ∀ A : ℝ≥0∞, ℓ < A → A ≠ ⊤ →
      ν ≪ Q ∧ eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal p) Q ≤ A := by
    intro A hA hAt
    refine move_lsc_of_seq hν hQ hacn hp hpq hAt ?_
    exact (Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hA).mono fun n hn => hn.le
  refine ⟨(key (ℓ + 1) (ENNReal.lt_add_right hlim.ne one_ne_zero)
    (ENNReal.add_ne_top.2 ⟨hlim.ne, ENNReal.one_ne_top⟩)).1, ?_⟩
  refine le_of_forall_gt_imp_ge_of_dense fun A hA => ?_
  by_cases hAt : A = ⊤
  · rw [hAt]; exact le_top
  exact (key A hA hAt).2

end HRS

end
