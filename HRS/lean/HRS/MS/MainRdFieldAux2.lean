import HRS.Prob.HilbertMartingale
import HRS.Main.A34Aux20

/-!
# S.A.6, packet P6a: the abstract Hilbert-space `d_{C²}` assembly

Everything here is independent of the whole-space model: `H` is a separable Hilbert space, `M` an `H`-valued continuous
martingale with covariation `Sg` (`IsHilbertMartingaleWithCovariation`), `sb` a deterministic covariance density and `γ`
the centered Gaussian with covariance `∫ sb`.

* `sa6_shift`: for an `ℱ_0`-measurable `H`-valued `X` and `Φ ∈ C_b²(H)` unit ball,
  `|E Φ(X + M_t) - E f_Φ(X)| ≤ ½ E ∫ ‖Σ - Σ̄‖_{𝔖₁}`, `f_Φ(x) = ∫ Φ(x+z) dγ(z)` (conditional Hilbert CLT
  `hilbert_martingale_clt_cond` applied to the translates `Φ(x_k + ·)` on the fibres of a finite-range `ℱ_0`-measurable
  approximation, as `a9_shift_H` of the torus).
* `sa6_dC2_assembly`: `d_{C²}(Law(I_emp + M_t + R), μ_I ∗ γ) ≤ E‖R‖ + ½ D + d_{C²}(Law I_emp, μ_I)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

section Shift

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma sa6_fiber_sum (S : Finset H) (ξ : Ω → H) (hS : ∀ ω, ξ ω ∈ S)
    (hm : ∀ x, MeasurableSet (ξ ⁻¹' {x})) {f : Ω → ℝ} (hf : Integrable f P) :
    ∫ ω, f ω ∂P = ∑ x ∈ S, ∫ ω in ξ ⁻¹' {x}, f ω ∂P := by
  classical
  have h1 : ∀ ω, f ω = ∑ x ∈ S, (ξ ⁻¹' {x}).indicator f ω := by
    intro ω
    rw [Finset.sum_eq_single (ξ ω)]
    · simp [Set.indicator]
    · intro b _ hb
      have : ω ∉ ξ ⁻¹' {b} := fun h => hb (h.symm)
      simp [Set.indicator, this]
    · intro h; exact absurd (hS ω) h
  calc ∫ ω, f ω ∂P = ∫ ω, ∑ x ∈ S, (ξ ⁻¹' {x}).indicator f ω ∂P := integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ∑ x ∈ S, ∫ ω, (ξ ⁻¹' {x}).indicator f ω ∂P :=
        integral_finset_sum _ fun x _ => hf.indicator (hm x)
    _ = _ := Finset.sum_congr rfl fun x _ => integral_indicator (hm x)

variable {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
  {sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} {γ : Measure H}

lemma sa6_cb_bdd {Φ : H → ℝ} (hΦ : Φ ∈ CbUnitBall H 2) (x : H) : |Φ x| ≤ 1 :=
  abs_apply_le_of_mem hΦ x

lemma sa6_cb_lip {Φ : H → ℝ} (hΦ : Φ ∈ CbUnitBall H 2) (x y : H) : |Φ x - Φ y| ≤ ‖x - y‖ := by
  have h1 : Φ ∈ CbUnitBall H 1 := cbUnitBall_anti (by norm_num) hΦ
  have := norm_sub_le_of_mem_one h1 x y
  simpa [Real.norm_eq_abs] using this

lemma sa6_f_props [IsProbabilityMeasure γ] {Φ : H → ℝ} (hΦ : Φ ∈ CbUnitBall H 2) :
    Continuous (fun x => ∫ z, Φ (x + z) ∂γ) ∧ ∀ x, |∫ z, Φ (x + z) ∂γ| ≤ 1 ∧
      ∀ x y, |(∫ z, Φ (x + z) ∂γ) - ∫ z, Φ (y + z) ∂γ| ≤ ‖x - y‖ := by
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hfi : ∀ w : H, Integrable (fun z => Φ (w + z)) γ := fun w =>
    Integrable.of_bound (C := 1) (hΦc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa using sa6_cb_bdd hΦ (w + z))
  have hlip : ∀ x y, |(∫ z, Φ (x + z) ∂γ) - ∫ z, Φ (y + z) ∂γ| ≤ ‖x - y‖ := fun x y => by
    rw [← integral_sub (hfi x) (hfi y), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ‖x - y‖) (Filter.Eventually.of_forall fun z => ?_)).trans
      (by simp)
    have := sa6_cb_lip hΦ (x + z) (y + z)
    simpa [add_sub_add_right_eq_sub, Real.norm_eq_abs] using this
  refine ⟨?_, fun x => ⟨?_, hlip⟩⟩
  · have : LipschitzWith 1 (fun x => ∫ z, Φ (x + z) ∂γ) := LipschitzWith.of_dist_le_mul fun x y => by
      simpa [dist_eq_norm, Real.dist_eq] using hlip x y
    exact this.continuous
  · have := norm_integral_le_of_norm_le_const (μ := γ) (C := 1) (f := fun z => Φ (x + z))
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using sa6_cb_bdd hΦ (x + z))
    simpa [Real.norm_eq_abs] using this

theorem sa6_shift_simple (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg) (ht : 0 ≤ t)
    (hsb : IsDetCovDensity t sb) (hγ : IsGaussianWithIntegratedCov t sb γ)
    (S : Finset H) (ξ : Ω → H) (hS : ∀ ω, ξ ω ∈ S) (hξ : ∀ x, MeasurableSet[ℱ 0] (ξ ⁻¹' {x}))
    {Φ : H → ℝ} (hΦ : Φ ∈ CbUnitBall H 2) :
    |(∫ ω, Φ (ξ ω + M t ω) ∂P) - ∫ ω, (∫ z, Φ (ξ ω + z) ∂γ) ∂P| ≤
      (1 / 2) * covDiscrepancy P t Sg sb := by
  classical
  haveI : IsProbabilityMeasure γ := hγ.1
  have hm0 : ℱ 0 ≤ mΩ := ℱ.le 0
  have hξm : ∀ x, MeasurableSet (ξ ⁻¹' {x}) := fun x => hm0 _ (hξ x)
  have hξmeas : Measurable ξ := by
    intro s _
    have : ξ ⁻¹' s = ⋃ x ∈ (S.filter (· ∈ s)), ξ ⁻¹' {x} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop,
        Finset.mem_filter]
      exact ⟨fun h => ⟨ξ ω, ⟨hS ω, h⟩, rfl⟩, fun ⟨x, ⟨_, hx⟩, e⟩ => e ▸ hx⟩
    rw [this]
    exact Finset.measurableSet_biUnion _ fun x _ => hξm x
  have hMt : AEMeasurable (M t) P := (hM.sq_int t ⟨ht, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hΦc : Continuous Φ := hΦ.1.continuous
  obtain ⟨hfc, hfb⟩ := sa6_f_props (γ := γ) hΦ
  have hint1 : Integrable (fun ω => Φ (ξ ω + M t ω)) P :=
    Integrable.of_bound (C := 1)
      (hΦc.measurable.comp_aemeasurable (hξmeas.aemeasurable.add hMt)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using sa6_cb_bdd hΦ _)
  have hint2 : Integrable (fun ω => ∫ z, Φ (ξ ω + z) ∂γ) P :=
    Integrable.of_bound (C := 1) (hfc.measurable.comp hξmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using (hfb (ξ ω)).1)
  have hgint := discrepancy_integrable P hM hsb
  set g : Ω → ℝ := fun ω => ∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω - sb σ) with hg
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _
  rw [sa6_fiber_sum P S ξ hS hξm hint1, sa6_fiber_sum P S ξ hS hξm hint2]
  unfold covDiscrepancy
  have hgsum : ∫ ω, g ω ∂P = ∑ x ∈ S, ∫ ω in ξ ⁻¹' {x}, g ω ∂P :=
    sa6_fiber_sum P S ξ hS hξm hgint
  show |_ - _| ≤ 1 / 2 * ∫ ω, g ω ∂P
  rw [hgsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  have hB : MeasurableSet[ℱ 0] (ξ ⁻¹' {x}) := hξ x
  have hBm := hm0 _ hB
  set h : H → ℝ := fun z => Φ (x + z) with hh
  have hhmem : h ∈ CbUnitBall H 2 := by
    have := cbUnitBall_translate hΦ x
    simpa [hh, add_comm] using this
  have e1 : ∫ ω in ξ ⁻¹' {x}, Φ (ξ ω + M t ω) ∂P = ∫ ω in ξ ⁻¹' {x}, h (M t ω) ∂P :=
    setIntegral_congr_fun hBm fun ω hω => by
      rw [show ξ ω = x from hω]
  have e2 : ∫ ω in ξ ⁻¹' {x}, (∫ z, Φ (ξ ω + z) ∂γ) ∂P = P.real (ξ ⁻¹' {x}) * ∫ z, h z ∂γ := by
    rw [setIntegral_congr_fun hBm (g := fun _ => ∫ z, h z ∂γ) fun ω hω => by
      rw [show ξ ω = x from hω],
      setIntegral_const, smul_eq_mul]
  rw [e1, e2]
  -- the conditional estimate on the fibre
  let 𝒢 : InitialSigma ℱ := ⟨ℱ 0, le_rfl⟩
  have hcl := hilbert_martingale_clt_cond P ℱ t ht 𝒢 M Sg hM sb hsb γ hγ h hhmem
  have hhc : Continuous h := hhmem.1.continuous
  have hXint : Integrable (fun ω => h (M t ω)) P :=
    Integrable.of_bound (C := 1) (hhc.measurable.comp_aemeasurable hMt).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using sa6_cb_bdd hhmem _)
  have c1 : ∫ ω in ξ ⁻¹' {x}, (P[fun ω => h (M t ω) | ℱ 0]) ω ∂P =
      ∫ ω in ξ ⁻¹' {x}, h (M t ω) ∂P := setIntegral_condExp hm0 hXint hB
  have c2 : ∫ ω in ξ ⁻¹' {x}, (P[g | ℱ 0]) ω ∂P = ∫ ω in ξ ⁻¹' {x}, g ω ∂P :=
    setIntegral_condExp hm0 hgint hB
  have hci1 : Integrable (P[fun ω => h (M t ω) | ℱ 0]) P := integrable_condExp
  have hci2 : Integrable (P[g | ℱ 0]) P := integrable_condExp
  have key : |(∫ ω in ξ ⁻¹' {x}, (P[fun ω => h (M t ω) | ℱ 0]) ω ∂P) -
      P.real (ξ ⁻¹' {x}) * ∫ z, h z ∂γ| ≤ 1 / 2 * ∫ ω in ξ ⁻¹' {x}, (P[g | ℱ 0]) ω ∂P := by
    have e3 : (∫ ω in ξ ⁻¹' {x}, (P[fun ω => h (M t ω) | ℱ 0]) ω ∂P) -
        P.real (ξ ⁻¹' {x}) * ∫ z, h z ∂γ =
        ∫ ω in ξ ⁻¹' {x}, ((P[fun ω => h (M t ω) | ℱ 0]) ω - ∫ z, h z ∂γ) ∂P := by
      rw [integral_sub hci1.integrableOn (integrable_const _).integrableOn, setIntegral_const,
        smul_eq_mul]
    rw [e3, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_ae ((hci1.sub (integrable_const _)).norm.integrableOn)
      (hci2.integrableOn.const_mul _) (ae_restrict_of_ae ?_)
    filter_upwards [hcl] with ω hω
    simpa [Real.norm_eq_abs] using hω
  rw [c1, c2] at key
  exact key

/-- finite-range `ℱ_0`-measurable approximation. -/
lemma sa6_exists_finrange_approx {m : MeasurableSpace Ω} {X : Ω → H} (hX : Measurable[m] X) :
    ∃ (ξ : ℕ → Ω → H) (S : ℕ → Finset H), (∀ n ω, ξ n ω ∈ S n) ∧
      (∀ n x, MeasurableSet[m] (ξ n ⁻¹' {x})) ∧
      ∀ ω, Tendsto (fun n => ξ n ω) atTop (𝓝 (X ω)) := by
  classical
  have hXs : StronglyMeasurable[m] X := hX.stronglyMeasurable
  exact ⟨fun n => hXs.approx n, fun n => (hXs.approx n).range,
    fun n ω => SimpleFunc.mem_range_self _ ω, fun n x => (hXs.approx n).measurableSet_fiber x,
    fun ω => hXs.tendsto_approx ω⟩

theorem sa6_shift (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg) (ht : 0 ≤ t)
    (hsb : IsDetCovDensity t sb) (hγ : IsGaussianWithIntegratedCov t sb γ)
    (X : Ω → H) (hX : Measurable[ℱ 0] X) {Φ : H → ℝ} (hΦ : Φ ∈ CbUnitBall H 2) :
    |(∫ ω, Φ (X ω + M t ω) ∂P) - ∫ ω, (∫ z, Φ (X ω + z) ∂γ) ∂P| ≤
      (1 / 2) * covDiscrepancy P t Sg sb := by
  classical
  haveI : IsProbabilityMeasure γ := hγ.1
  obtain ⟨hfc, hfb⟩ := sa6_f_props (γ := γ) hΦ
  obtain ⟨ξ, S, hS, hξ, hξt⟩ := sa6_exists_finrange_approx (m := ℱ 0) hX
  have hm0 : ℱ 0 ≤ mΩ := ℱ.le 0
  have hXm : Measurable X := hX.mono hm0 le_rfl
  have hMt : AEMeasurable (M t) P := (hM.sq_int t ⟨ht, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hξmeas : ∀ n, Measurable (ξ n) := fun n => by
    intro s _
    have : ξ n ⁻¹' s = ⋃ x ∈ ((S n).filter (· ∈ s)), ξ n ⁻¹' {x} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop,
        Finset.mem_filter]
      exact ⟨fun h => ⟨ξ n ω, ⟨hS n ω, h⟩, rfl⟩, fun ⟨x, ⟨_, hx⟩, e⟩ => e ▸ hx⟩
    rw [this]
    exact Finset.measurableSet_biUnion _ fun x _ => hm0 _ (hξ n x)
  have hbd1 : Tendsto (fun n => ∫ ω, Φ (ξ n ω + M t ω) ∂P) atTop
      (𝓝 (∫ ω, Φ (X ω + M t ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_)
      (integrable_const 1) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (hΦc.measurable.comp_aemeasurable ((hξmeas n).aemeasurable.add hMt)).aestronglyMeasurable
    · simpa using sa6_cb_bdd hΦ _
    · exact (hΦc.tendsto _).comp ((hξt ω).add_const (M t ω))
  have hbd2 : Tendsto (fun n => ∫ ω, (∫ z, Φ (ξ n ω + z) ∂γ) ∂P) atTop
      (𝓝 (∫ ω, (∫ z, Φ (X ω + z) ∂γ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_)
      (integrable_const 1) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (hfc.measurable.comp (hξmeas n)).aestronglyMeasurable
    · simpa using (hfb (ξ n ω)).1
    · exact (hfc.tendsto _).comp (hξt ω)
  have hlim := (hbd1.sub hbd2).abs
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  exact sa6_shift_simple P hM ht hsb hγ (S n) (ξ n) (hS n) (hξ n) hΦ

end Shift

section Assembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- `∫ Φ d(ν ∗ γ) = ∫ c_Φ dν`. -/
lemma sa6_conv_integral (ν γ : Measure H) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    {Φ : H → ℝ} (hΦ : Φ ∈ CbUnitBall H 2) :
    ∫ y, Φ y ∂(ν ∗ γ) = ∫ x, (∫ z, Φ (x + z) ∂γ) ∂ν := by
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hadd : Measurable (fun p : H × H => p.1 + p.2) := measurable_fst.add measurable_snd
  have hint : Integrable (fun p : H × H => Φ (p.1 + p.2)) (ν.prod γ) :=
    Integrable.of_bound (C := 1) (hΦc.comp continuous_add).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by simpa using sa6_cb_bdd hΦ _)
  show ∫ y, Φ y ∂((ν.prod γ).map (fun p : H × H => p.1 + p.2)) = _
  rw [integral_map hadd.aemeasurable hΦc.aestronglyMeasurable]
  exact integral_prod _ hint

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
  {sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} {γ : Measure H}

theorem sa6_dC2_assembly (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg) (ht : 0 ≤ t)
    (hsb : IsDetCovDensity t sb) (hγ : IsGaussianWithIntegratedCov t sb γ)
    (Iemp R : Ω → H) (hI : Measurable[ℱ 0] Iemp) (hR : AEMeasurable R P)
    (μI : Measure H) [IsProbabilityMeasure μI] (ρR : ℝ) (hρR0 : 0 ≤ ρR)
    (hρR : ∫⁻ ω, ‖R ω‖ₑ ∂P ≤ ENNReal.ofReal ρR) :
    smoothDist 2 (law P (fun ω => Iemp ω + M t ω + R ω)) (μI ∗ γ) ≤
      ρR + (1 / 2) * covDiscrepancy P t Sg sb + smoothDist 2 (law P Iemp) μI := by
  haveI : IsProbabilityMeasure γ := hγ.1
  have hm0 : ℱ 0 ≤ mΩ := ℱ.le 0
  have hIm : Measurable Iemp := hI.mono hm0 le_rfl
  have hMt : AEMeasurable (M t) P := (hM.sq_int t ⟨ht, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hD0 : 0 ≤ covDiscrepancy P t Sg sb :=
    integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _
  have hY : AEMeasurable (fun ω => Iemp ω + M t ω + R ω) P := (hIm.aemeasurable.add hMt).add hR
  haveI : IsProbabilityMeasure (law P Iemp) := (Measure.isProbabilityMeasure_map_iff hIm.aemeasurable).2 inferInstance
  have : Nonempty (CbUnitBall H 2) := ⟨⟨0, zero_mem_cbUnitBall 2⟩⟩
  refine Real.iSup_le (fun Φ => ?_) (add_nonneg (add_nonneg hρR0 (by positivity))
    (smoothDist_nonneg 2 (law P Iemp) μI))
  have hΦ : Φ.1 ∈ CbUnitBall H 2 := Φ.2
  have hΦc : Continuous Φ.1 := hΦ.1.continuous
  obtain ⟨hfc, hfb⟩ := sa6_f_props (γ := γ) hΦ
  -- 1. the remainder
  have s1 : |(∫ ω, Φ.1 (Iemp ω + M t ω + R ω) ∂P) - ∫ ω, Φ.1 (Iemp ω + M t ω) ∂P| ≤ ρR := by
    have hi : ∀ Y : Ω → H, AEMeasurable Y P → Integrable (fun ω => Φ.1 (Y ω)) P := fun Y hY =>
      Integrable.of_bound (C := 1) (hΦc.measurable.comp_aemeasurable hY).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by simpa using sa6_cb_bdd hΦ _)
    rw [← integral_sub (hi _ hY) (hi (fun ω => Iemp ω + M t ω) (hIm.aemeasurable.add hMt))]
    have h1 : ‖∫ ω, (Φ.1 (Iemp ω + M t ω + R ω) - Φ.1 (Iemp ω + M t ω)) ∂P‖ₑ ≤
        ENNReal.ofReal ρR := by
      refine (enorm_integral_le_lintegral_enorm _).trans (le_trans ?_ hρR)
      refine lintegral_mono fun ω => ?_
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal ?_
      have := sa6_cb_lip hΦ (Iemp ω + M t ω + R ω) (Iemp ω + M t ω)
      simpa [Real.norm_eq_abs] using this
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_ofReal_iff hρR0] at h1
    simpa [Real.norm_eq_abs] using h1
  -- 2. the shift
  have s2 := sa6_shift P hM ht hsb hγ Iemp hI hΦ
  -- 3. convolution with `γ`
  have s3 : |(∫ ω, (∫ z, Φ.1 (Iemp ω + z) ∂γ) ∂P) - ∫ x, (∫ z, Φ.1 (x + z) ∂γ) ∂μI| ≤
      smoothDist 2 (law P Iemp) μI := by
    have e1 : ∫ ω, (∫ z, Φ.1 (Iemp ω + z) ∂γ) ∂P = ∫ y, Φ.1 y ∂((law P Iemp) ∗ γ) := by
      rw [sa6_conv_integral (law P Iemp) γ hΦ, integral_map hIm.aemeasurable hfc.aestronglyMeasurable]
    rw [e1, ← sa6_conv_integral μI γ hΦ]
    refine (abs_integral_sub_le_smoothDist hΦ _ _).trans ?_
    exact HRS.A34.a34_conv_left _ _ γ
  have e0 : ∫ y, Φ.1 y ∂(law P (fun ω => Iemp ω + M t ω + R ω)) =
      ∫ ω, Φ.1 (Iemp ω + M t ω + R ω) ∂P := integral_map hY hΦc.aestronglyMeasurable
  have e1' : ∫ y, Φ.1 y ∂(μI ∗ γ) = ∫ x, (∫ z, Φ.1 (x + z) ∂γ) ∂μI := sa6_conv_integral μI γ hΦ
  rw [e0, e1']
  have t1 := abs_sub_le (∫ ω, Φ.1 (Iemp ω + M t ω + R ω) ∂P) (∫ ω, Φ.1 (Iemp ω + M t ω) ∂P)
    (∫ x, (∫ z, Φ.1 (x + z) ∂γ) ∂μI)
  have t2 := abs_sub_le (∫ ω, Φ.1 (Iemp ω + M t ω) ∂P) (∫ ω, (∫ z, Φ.1 (Iemp ω + z) ∂γ) ∂P)
    (∫ x, (∫ z, Φ.1 (x + z) ∂γ) ∂μI)
  linarith

end Assembly

end HRS.MS.MainRdField
