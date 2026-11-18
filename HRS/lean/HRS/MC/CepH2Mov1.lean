import HRS.MC.CepH2Freeze2
import HRS.MC.CepH2Ent4
import HRS.MC.CepH2Fish3

/-!
# CEPH2, G2 (a): lower semicontinuity of the cylinder entropy for a moving, frozen potential
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

section
variable {U : Ch N → ℝ} {Un : ℕ → Ch N → ℝ} {θ : ℝ} {c C : ℝ}

/-- Weighted lintegrals over the cell converge along the frozen potentials. -/
theorem h2_weight_lintegral_tendsto (hUc : Continuous U) (hUnc : ∀ n, Continuous (Un n)) (hθ : 0 < θ)
    (hc : 0 < c) (hlow : ∀ n z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Un n z)
    (hUnU : ∀ (n : ℕ) (z : Ch N), ‖h2_perp z‖ < (n : ℝ) → Un n z = U z)
    {f : Ch N → ℝ≥0∞} (hf : Measurable f) {M : ℝ≥0∞} (hM : M ≠ ⊤) (hfM : ∀ x, f x ≤ M) :
    Tendsto (fun n => ∫⁻ x in cep_cell N, cep_cylWeight θ (Un n) x * f x) atTop
      (𝓝 (∫⁻ x in cep_cell N, cep_cylWeight θ U x * f x)) := by
  set V : Ch N → ℝ := fun z => c * Metric.infDist z (cep_Alcove N) ^ 2 - C with hV
  have hVconf : ∃ c' C' : ℝ, 0 < c' ∧ ∀ z, c' * Metric.infDist z (cep_Alcove N) ^ 2 - C' ≤ V z :=
    ⟨c, C, hc, fun z => le_rfl⟩
  have hZV := h2_partition_lt_top hVconf hθ
  refine tendsto_lintegral_of_dominated_convergence (fun x => cep_cylWeight θ V x * M)
    (fun n => (h2_cylWeight_measurable (hUnc n) θ).mul hf) (fun n => ae_of_all _ fun x => ?_) ?_ ?_
  · refine mul_le_mul' ?_ (hfM x)
    unfold cep_cylWeight
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := hlow n x
    have h2 : -(Un n x) ≤ -(V x) := by simp only [hV]; linarith
    exact div_le_div_of_nonneg_right h2 hθ.le
  · rw [lintegral_mul_const' _ _ hM]
    exact ENNReal.mul_ne_top (by simpa [cep_cylPartition] using hZV.ne) hM
  · refine ae_of_all _ fun x => ?_
    obtain ⟨n0, hn0⟩ := exists_nat_gt ‖h2_perp x‖
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n0] with n hn
    have : ‖h2_perp x‖ < (n : ℝ) := lt_of_lt_of_le hn0 (by exact_mod_cast hn)
    simp only [cep_cylWeight, hUnU n x this]

theorem h2_integral_eq_lintegral {m : Measure (Ch N)} [IsProbabilityMeasure m] {ψ : Ch N → ℝ}
    (hψ : Measurable ψ) {C0 : ℝ} (hC : ∀ z, |ψ z| ≤ C0) :
    ∫ z, ψ z ∂m = (∫⁻ z, ENNReal.ofReal (ψ z + C0) ∂m).toReal - C0 := by
  have hint : Integrable ψ m :=
    Integrable.of_bound hψ.aestronglyMeasurable C0 (ae_of_all _ fun z => by simpa using hC z)
  have h1 : ∫ z, (ψ z + C0) ∂m = (∫⁻ z, ENNReal.ofReal (ψ z + C0) ∂m).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => by show (0:ℝ) ≤ ψ z + C0; linarith [(abs_le.1 (hC z)).1])
      (hint.add (integrable_const C0)).aestronglyMeasurable
  rw [← h1, integral_add hint (integrable_const C0)]
  simp

/-- The Gibbs references converge narrowly along the frozen potentials. -/
theorem h2_ref_tendsto (hUc : Continuous U) (hUnc : ∀ n, Continuous (Un n)) (hθ : 0 < θ)
    (hc : 0 < c) (hlow : ∀ n z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Un n z)
    (hUnU : ∀ (n : ℕ) (z : Ch N), ‖h2_perp z‖ < (n : ℝ) → Un n z = U z)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {ψ : Ch N → ℝ} (hψ : Measurable ψ) {C0 : ℝ} (hC : ∀ z, |ψ z| ≤ C0) :
    Tendsto (fun n => ∫ z, ψ z ∂(cep_cylRef θ (Un n))) atTop (𝓝 (∫ z, ψ z ∂(cep_cylRef θ U))) := by
  have hconfn : ∀ n, ∃ c' C' : ℝ, 0 < c' ∧ ∀ z, c' * Metric.infDist z (cep_Alcove N) ^ 2 - C' ≤ Un n z :=
    fun n => ⟨c, C, hc, hlow n⟩
  haveI := h2_cylRef_prob hUc hconf hθ
  haveI : ∀ n, IsProbabilityMeasure (cep_cylRef θ (Un n)) := fun n => h2_cylRef_prob (hUnc n) (hconfn n) hθ
  have hC0 : 0 ≤ C0 := (abs_nonneg _).trans (hC 0)
  set f : Ch N → ℝ≥0∞ := fun z => ENNReal.ofReal (ψ z + C0) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (hψ.add measurable_const)
  have hfM : ∀ x, f x ≤ ENNReal.ofReal (2 * C0) := fun x => by
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [(abs_le.1 (hC x)).2]
  have hZ := h2_weight_lintegral_tendsto (θ := θ) hUc hUnc hθ hc hlow hUnU (f := fun _ => 1) measurable_const
    (M := 1) ENNReal.one_ne_top (fun _ => le_rfl)
  have hZ' : Tendsto (fun n => cep_cylPartition θ (Un n)) atTop (𝓝 (cep_cylPartition θ U)) := by
    simpa [cep_cylPartition] using hZ
  have hW := h2_weight_lintegral_tendsto (θ := θ) hUc hUnc hθ hc hlow hUnU hfm ENNReal.ofReal_ne_top hfM
  have hZne : cep_cylPartition θ U ≠ ⊤ := (h2_partition_lt_top hconf hθ).ne
  have hZ0 : cep_cylPartition θ U ≠ 0 := (h2_partition_pos hUc θ).ne'
  have hinv : Tendsto (fun n => (cep_cylPartition θ (Un n))⁻¹) atTop (𝓝 (cep_cylPartition θ U)⁻¹) :=
    tendsto_inv_iff.2 hZ'
  have hL : Tendsto (fun n => ∫⁻ z, f z ∂(cep_cylRef θ (Un n))) atTop (𝓝 (∫⁻ z, f z ∂(cep_cylRef θ U))) := by
    have e : ∀ V : Ch N → ℝ, Continuous V → ∫⁻ z, f z ∂(cep_cylRef θ V) =
        (cep_cylPartition θ V)⁻¹ * ∫⁻ z in cep_cell N, cep_cylWeight θ V z * f z := fun V hV =>
      h2_lintegral_cylRef hV θ hfm
    simp_rw [e _ (hUnc _), e _ hUc]
    exact ENNReal.Tendsto.mul hinv (Or.inl (ENNReal.inv_ne_zero.2 hZne)) hW
      (Or.inr (ENNReal.inv_ne_top.2 hZ0))
  have hfin : ∫⁻ z, f z ∂(cep_cylRef θ U) ≠ ⊤ := by
    have h1 : ∫⁻ z, f z ∂(cep_cylRef θ U) ≤ ENNReal.ofReal (2 * C0) := by
      calc ∫⁻ z, f z ∂(cep_cylRef θ U) ≤ ∫⁻ z, ENNReal.ofReal (2 * C0) ∂(cep_cylRef θ U) :=
            lintegral_mono hfM
        _ = ENNReal.ofReal (2 * C0) := by simp
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have := (ENNReal.tendsto_toReal hfin).comp hL |>.sub_const C0
  rw [h2_integral_eq_lintegral hψ hC]
  simp_rw [h2_integral_eq_lintegral hψ hC]
  exact this

/-- Lower semicontinuity of `klDiv` with a moving reference. -/
theorem h2_klDiv_liminf_moving {μ ν : Measure (Ch N)} {μn νn : ℕ → Measure (Ch N)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [∀ n, IsProbabilityMeasure (μn n)]
    [∀ n, IsProbabilityMeasure (νn n)]
    (hμ : μ (cep_cell N)ᶜ = 0) (hν : ν (cep_cell N)ᶜ = 0)
    (hconv : ∀ ψ : Ch N → ℝ, Continuous ψ → (∀ z, ψ (z + cep_diag N) = ψ z) → (∃ C, ∀ z, |ψ z| ≤ C) →
      Tendsto (fun n => ∫ z, ψ z ∂(μn n)) atTop (𝓝 (∫ z, ψ z ∂μ)))
    (hconv' : ∀ ψ : Ch N → ℝ, Continuous ψ → (∃ C, ∀ z, |ψ z| ≤ C) →
      Tendsto (fun n => ∫ z, ψ z ∂(νn n)) atTop (𝓝 (∫ z, ψ z ∂ν))) :
    klDiv μ ν ≤ liminf (fun n => klDiv (μn n) (νn n)) atTop := by
  haveI : IsProbabilityMeasure (μ.map h2_pi) := (Measure.isProbabilityMeasure_map_iff h2_continuous_pi.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (ν.map h2_pi) := (Measure.isProbabilityMeasure_map_iff h2_continuous_pi.aemeasurable).2 inferInstance
  haveI : ∀ n, IsProbabilityMeasure ((μn n).map h2_pi) := fun n =>
    (Measure.isProbabilityMeasure_map_iff h2_continuous_pi.aemeasurable).2 inferInstance
  haveI : ∀ n, IsProbabilityMeasure ((νn n).map h2_pi) := fun n =>
    (Measure.isProbabilityMeasure_map_iff h2_continuous_pi.aemeasurable).2 inferInstance
  have hb : ∀ φ : H2Alpha N → ℝ, Continuous φ → ∃ C, ∀ z, |(φ ∘ h2_pi) z| ≤ C := by
    intro φ hφ
    obtain ⟨C, hC⟩ := (isCompact_univ (X := H2Alpha N)).exists_bound_of_continuousOn hφ.continuousOn
    exact ⟨C, fun z => by simpa using hC (h2_pi z) (mem_univ _)⟩
  have hP : ∀ φ : H2Alpha N → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂((μn n).map h2_pi)) atTop (𝓝 (∫ x, φ x ∂(μ.map h2_pi))) := by
    intro φ hφ
    have hc : Continuous (φ ∘ h2_pi) := hφ.comp h2_continuous_pi
    have := hconv (φ ∘ h2_pi) hc (fun z => by simp only [Function.comp, h2_pi_periodic]) (hb φ hφ)
    have e : ∀ m : Measure (Ch N), ∫ x, φ x ∂(m.map h2_pi) = ∫ z, (φ ∘ h2_pi) z ∂m := fun m =>
      integral_map h2_continuous_pi.aemeasurable hφ.aestronglyMeasurable
    simp only [e]
    exact this
  have hQ : ∀ φ : H2Alpha N → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂((νn n).map h2_pi)) atTop (𝓝 (∫ x, φ x ∂(ν.map h2_pi))) := by
    intro φ hφ
    have hc : Continuous (φ ∘ h2_pi) := hφ.comp h2_continuous_pi
    have := hconv' (φ ∘ h2_pi) hc (hb φ hφ)
    have e : ∀ m : Measure (Ch N), ∫ x, φ x ∂(m.map h2_pi) = ∫ z, (φ ∘ h2_pi) z ∂m := fun m =>
      integral_map h2_continuous_pi.aemeasurable hφ.aestronglyMeasurable
    simp only [e]
    exact this
  have h1 := b15b_klDiv_liminf_le hP hQ
  rw [h2_klDiv_map_pi hμ hν]
  refine h1.trans (liminf_le_liminf (Eventually.of_forall fun n => ?_))
  exact klDiv_map_le (μn n) (νn n) h2_continuous_pi.measurable

theorem h2_liminf_sub_moving (k : ℕ → ℝ≥0∞) (L : ℕ → ℝ) (L0 : ℝ) (hL : Tendsto L atTop (𝓝 L0)) :
    (((liminf k atTop : ℝ≥0∞) : EReal)) - (L0 : EReal) ≤ liminf (fun n => (k n : EReal) - (L n : EReal)) atTop := by
  rw [h2_liminf_sub_const k L0]
  have hsum : ∀ n, (k n : EReal) - (L0 : EReal) + ((L0 - L n : ℝ) : EReal) = (k n : EReal) - (L n : EReal) := by
    intro n
    by_cases hk : k n = ⊤
    · rw [hk, EReal.coe_ennreal_top, EReal.top_sub_coe, EReal.top_add_coe, EReal.top_sub_coe]
    · rw [← EReal.coe_ennreal_toReal hk, ← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_sub]
      congr 1
      ring
  have he : Tendsto (fun n => ((L0 - L n : ℝ) : EReal)) atTop (𝓝 ((0 : ℝ) : EReal)) := by
    have : Tendsto (fun n => L0 - L n) atTop (𝓝 0) := by simpa using hL.const_sub L0
    exact (continuous_coe_real_ereal.tendsto _).comp this
  have hle := EReal.le_liminf_add (f := atTop) (u := fun n => (k n : EReal) - (L0 : EReal))
    (v := fun n => ((L0 - L n : ℝ) : EReal))
  rw [he.liminf_eq] at hle
  simp only [EReal.coe_zero, add_zero] at hle
  refine hle.trans (le_of_eq ?_)
  congr 1
  funext n
  exact hsum n

end

end HRS.MC.CepH2
