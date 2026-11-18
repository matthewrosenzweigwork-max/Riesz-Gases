import HRS.MP.SelfSimP5LimA
import HRS.Appendix.B15BAux1

/-!
# MPP5D (10b): lower semicontinuity of the entropy with moving references on `ℝ^N`

Namespace `HRS.MP.SelfSimP5Impl`, helpers `ss5l_`.  Part of the proof of `HRS.MP.SelfSimP5.ss5_limit`.

Route.  `ss5l_klDiv_liminf`: joint lower semicontinuity of `klDiv` on `ℝ^N` under narrow convergence of both
arguments, through the embedding `t ↦ t/(1+|t|)` into the compact cube (`b15b_klDiv_liminf_le`).  The references
`Z_n⁻¹ e^{-U_{ε_n}/θ} dz` converge narrowly to `m⁻¹ e^{-U/θ} 1_C dz` (`ss5l_ref_tendsto`: uniform Gaussian majorant from
`ss5t_U_ge`, pointwise convergence everywhere: eventual equality on the open chamber `C`, and `U_{ε_n} → ∞` off `C`
because `φ_ε(g) ≥ -log ε` for `g ≤ 0`).  `ss5l_entropy_lsc_ch` is the chamber statement; `ss5l_entropy_transport` compares
`gibbsEntropyW (selfSimWeight 1 0 θ N 0) ν` with the chamber entropy of `ν.map (ss5_toCh σ)` through the free-energy
comparison `ss5i_klDiv_cmp` and the invariance of `klDiv` under the measurable equivalence `ss5l_equiv`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open HRS HRS.MP.SelfSimP5 HRS.MP.SelfSim HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MP.SelfSimP5Impl

/-! ### Lower semicontinuity of `klDiv` on `ℝ^N` through the cube embedding -/

/-- The coordinate squashing `t ↦ t/(1+|t|)` into `(-1,1)`. -/
def ss5l_h (t : ℝ) : ℝ := t / (1 + |t|)

theorem ss5l_h_mem (t : ℝ) : ss5l_h t ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold ss5l_h
  have h : 0 < 1 + |t| := by positivity
  rw [Set.mem_Icc, ← abs_le, abs_div, abs_of_pos h, div_le_one h]
  linarith

theorem ss5l_h_inj : Function.Injective ss5l_h := by
  have key : ∀ t, |ss5l_h t| = |t| / (1 + |t|) := fun t => by
    unfold ss5l_h
    rw [abs_div, abs_of_pos (by positivity : 0 < 1 + |t|)]
  have inv : ∀ t, ss5l_h t / (1 - |ss5l_h t|) = t := fun t => by
    rw [key]
    have h : (0 : ℝ) < 1 + |t| := by positivity
    have : 1 - |t| / (1 + |t|) = 1 / (1 + |t|) := by field_simp; ring
    rw [this]
    unfold ss5l_h
    field_simp
  intro t u htu
  rw [← inv t, ← inv u, htu]

theorem ss5l_h_cont : Continuous ss5l_h :=
  continuous_id.div (continuous_const.add continuous_abs) (fun t => by positivity)

/-- The compact cube `[-1,1]^N`. -/
abbrev Ss5lCube (N : ℕ) := Fin N → Set.Icc (-1 : ℝ) 1

/-- The embedding of `ℝ^N` into the cube. -/
def ss5lF (N : ℕ) (x : Ch5 N) : Ss5lCube N := fun k => ⟨ss5l_h (x k), ss5l_h_mem _⟩

theorem ss5lF_cont (N : ℕ) : Continuous (ss5lF N) := by
  refine continuous_pi fun k => Continuous.subtype_mk ?_ _
  exact ss5l_h_cont.comp (EuclideanSpace.proj k : Ch5 N →L[ℝ] ℝ).continuous

theorem ss5lF_embedding (N : ℕ) : MeasurableEmbedding (ss5lF N) := by
  refine (ss5lF_cont N).measurableEmbedding ?_
  intro x y hxy
  ext j
  refine ss5l_h_inj ?_
  have := congrArg (fun z : Ss5lCube N => (z j : ℝ)) hxy
  simpa [ss5lF] using this

theorem ss5l_klDiv_le_map (N : ℕ) (μ ρ : Measure (Ch5 N)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ] :
    klDiv μ ρ ≤ klDiv (μ.map (ss5lF N)) (ρ.map (ss5lF N)) := by
  obtain ⟨g, hg, hgF⟩ := (ss5lF_embedding N).exists_measurable_extend
    (measurable_id : Measurable (id : Ch5 N → Ch5 N)) (fun _ => ⟨0⟩)
  have h := klDiv_map_le (μ.map (ss5lF N)) (ρ.map (ss5lF N)) hg
  rw [Measure.map_map hg (ss5lF_embedding N).measurable, Measure.map_map hg
    (ss5lF_embedding N).measurable, hgF, Measure.map_id, Measure.map_id] at h
  exact h

/-- Lower semicontinuity of `klDiv` along sequences with narrow convergence of both arguments on `ℝ^N`
(through the cube embedding; test functions bounded and continuous). -/
theorem ss5l_klDiv_liminf {N : ℕ} {μ ρ : Measure (Ch5 N)} {μn ρn : ℕ → Measure (Ch5 N)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] [∀ n, IsProbabilityMeasure (μn n)]
    [∀ n, IsProbabilityMeasure (ρn n)]
    (hμ : ∀ ψ : Ch5 N → ℝ, Continuous ψ → (∃ C, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x ∂(μn n)) atTop (𝓝 (∫ x, ψ x ∂μ)))
    (hρ : ∀ ψ : Ch5 N → ℝ, Continuous ψ → (∃ C, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x ∂(ρn n)) atTop (𝓝 (∫ x, ψ x ∂ρ))) :
    klDiv μ ρ ≤ liminf (fun n => klDiv (μn n) (ρn n)) atTop := by
  have hFm : Measurable (ss5lF N) := (ss5lF_embedding N).measurable
  have hw : ∀ (ν : Measure (Ch5 N)) (φ : Ss5lCube N → ℝ), Continuous φ →
      ∫ y, φ y ∂(ν.map (ss5lF N)) = ∫ x, φ (ss5lF N x) ∂ν := fun ν φ hφ =>
    integral_map hFm.aemeasurable hφ.aestronglyMeasurable
  have hbd : ∀ φ : Ss5lCube N → ℝ, Continuous φ → ∃ C, ∀ x, |φ (ss5lF N x)| ≤ C := by
    intro φ hφ
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
    exact ⟨C, fun x => by simpa using hC (ss5lF N x) trivial⟩
  have key := b15b_klDiv_liminf_le (P := μ.map (ss5lF N)) (Q := ρ.map (ss5lF N))
    (Pn := fun n => (μn n).map (ss5lF N)) (Qn := fun n => (ρn n).map (ss5lF N))
    (fun φ hφ => by
      simp_rw [hw _ φ hφ]
      exact hμ _ (hφ.comp (ss5lF_cont N)) (hbd φ hφ))
    (fun φ hφ => by
      simp_rw [hw _ φ hφ]
      exact hρ _ (hφ.comp (ss5lF_cont N)) (hbd φ hφ))
  refine (ss5l_klDiv_le_map N μ ρ).trans (key.trans ?_)
  exact liminf_le_liminf (Eventually.of_forall fun n => klDiv_map_le _ _ hFm)
    (by isBoundedDefault) (by isBoundedDefault)


/-! ### The moving references -/

/-- The limit potential `Φ + ¼|z|²` (on the open chamber). -/
def ss5l_Ulim (N : ℕ) (z : Ch5 N) : ℝ := ss5_Phi N z + (1 / 4 : ℝ) * ‖z‖ ^ 2

/-- The density of the level-`n` unnormalised Gibbs weight. -/
def ss5l_fn (N : ℕ) (θ : ℝ) (n : ℕ) (z : Ch5 N) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-ss5_U N (ss5_eps n) z / θ))

/-- The density of the limit unnormalised Gibbs weight, carried by the open chamber. -/
def ss5l_finf (N : ℕ) (θ : ℝ) (z : Ch5 N) : ℝ≥0∞ :=
  (ss5_chamber N).indicator (fun z => ENNReal.ofReal (Real.exp (-ss5l_Ulim N z / θ))) z

theorem ss5l_Phi_meas (N : ℕ) : Measurable (ss5_Phi N) := by
  unfold ss5_Phi
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_) _
  by_cases hkl : k < l
  · simp only [hkl, if_true]
    have hm : ∀ i : Fin N, Measurable fun z : Ch5 N => z i := fun i =>
      (EuclideanSpace.proj i : Ch5 N →L[ℝ] ℝ).continuous.measurable
    exact (Real.measurable_log.comp ((hm l).sub (hm k))).neg
  · simp [hkl]

theorem ss5l_Ulim_meas (N : ℕ) : Measurable (ss5l_Ulim N) :=
  (ss5l_Phi_meas N).add (measurable_norm.pow_const 2 |>.const_mul _)

theorem ss5l_finf_meas (N : ℕ) (θ : ℝ) : Measurable (ss5l_finf N θ) := by
  unfold ss5l_finf
  exact (Real.measurable_exp.comp ((ss5l_Ulim_meas N).neg.div_const θ)).ennreal_ofReal.indicator
    (ss5i_chamber_measurable N)

theorem ss5l_fn_meas (N : ℕ) (θ : ℝ) (n : ℕ) : Measurable (ss5l_fn N θ n) :=
  ss5i_wU_meas N (θ := θ) (ss5_eps_pos n)

theorem ss5l_eventually_eps_le {N : ℕ} {z : Ch5 N} (hz : z ∈ ss5_chamber N) :
    ∀ᶠ n : ℕ in atTop, ∀ k l : Fin N, k < l → ss5_eps n ≤ z l - z k := by
  refine Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => ?_
  by_cases hkl : k < l
  · have hgap : 0 < z l - z k := sub_pos.2 (hz k l hkl)
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hgap)] with n hn _ using hn.le
  · exact Filter.Eventually.of_forall fun _ h => absurd h hkl

theorem ss5l_phi_ge_neg_log {ε g : ℝ} (hε : 0 < ε) (hg : g ≤ 0) : -Real.log ε ≤ ss5_phiTr ε g := by
  unfold ss5_phiTr
  rw [if_neg (by linarith)]
  have h1 : 0 ≤ -(g - ε) / ε := div_nonneg (by linarith) hε.le
  have h2 : 0 ≤ (g - ε) ^ 2 / (2 * ε ^ 2) := by positivity
  have e : -(g - ε) / ε = -((g - ε) / ε) := by ring
  linarith

theorem ss5l_PhiTr_lower {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : Ch5 N)
    {k0 l0 : Fin N} (hk : k0 < l0) (hg : z l0 - z k0 ≤ 0) :
    (1 / (N : ℝ)) * (-Real.log ε - ∑ k : Fin N, ∑ l : Fin N, |z l - z k|) ≤ ss5_PhiTr N ε z := by
  unfold ss5_PhiTr
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set t : Fin N → Fin N → ℝ := fun k l => if k < l then ss5_phiTr ε (z l - z k) else 0 with ht
  set s : Fin N → Fin N → ℝ := fun k l => |z l - z k| with hs
  have hts : ∀ k l, 0 ≤ t k l + s k l := by
    intro k l
    by_cases hkl : k < l
    · simp only [ht, hs, hkl, ite_true]
      have := ss5t_phi_ge hε hε1 (z l - z k)
      linarith
    · simp only [ht, hs, hkl, ite_false]
      positivity
  have hbad : -Real.log ε ≤ t k0 l0 + s k0 l0 := by
    simp only [ht, hs, hk, ite_true]
    have := ss5l_phi_ge_neg_log hε hg
    have := abs_nonneg (z l0 - z k0)
    linarith
  have hsum : t k0 l0 + s k0 l0 ≤ ∑ k : Fin N, ∑ l : Fin N, (t k l + s k l) := by
    calc t k0 l0 + s k0 l0 ≤ ∑ l : Fin N, (t k0 l + s k0 l) :=
          Finset.single_le_sum (f := fun l => t k0 l + s k0 l) (fun l _ => hts k0 l) (Finset.mem_univ l0)
      _ ≤ _ := Finset.single_le_sum (f := fun k => ∑ l : Fin N, (t k l + s k l))
          (fun k _ => Finset.sum_nonneg fun l _ => hts k l) (Finset.mem_univ k0)
  have e : ∑ k : Fin N, ∑ l : Fin N, (t k l + s k l) =
      (∑ k : Fin N, ∑ l : Fin N, t k l) + ∑ k : Fin N, ∑ l : Fin N, s k l := by
    simp only [Finset.sum_add_distrib]
  have : -Real.log ε - ∑ k : Fin N, ∑ l : Fin N, s k l ≤ ∑ k : Fin N, ∑ l : Fin N, t k l := by
    linarith
  exact this

theorem ss5l_fn_tendsto {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : 0 < θ) (z : Ch5 N) :
    Tendsto (fun n => ss5l_fn N θ n z) atTop (𝓝 (ss5l_finf N θ z)) := by
  by_cases hz : z ∈ ss5_chamber N
  · have : ss5l_finf N θ z = ENNReal.ofReal (Real.exp (-ss5l_Ulim N z / θ)) := by
      unfold ss5l_finf; rw [Set.indicator_of_mem hz]
    rw [this]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ss5l_eventually_eps_le hz] with n hn
    unfold ss5l_fn ss5_U ss5l_Ulim
    rw [ss5l_PhiTr_eq hn]
  · have h0 : ss5l_finf N θ z = 0 := by
      unfold ss5l_finf; rw [Set.indicator_of_notMem hz]
    rw [h0]
    have : ∃ k l : Fin N, k < l ∧ z l - z k ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hz fun k l hkl => sub_pos.1 (hcon k l hkl)
    obtain ⟨k0, l0, hk, hg⟩ := this
    set B : ℝ := ∑ k : Fin N, ∑ l : Fin N, |z l - z k| with hB
    have hlow : ∀ n : ℕ, (1 / (N : ℝ)) * (Real.log ((n : ℝ) + 1) - B) ≤ ss5_U N (ss5_eps n) z := by
      intro n
      have h1 := ss5l_PhiTr_lower hN (ss5_eps_pos n) (ss5_eps_le_one n) z hk hg
      have hlog : -Real.log (ss5_eps n) = Real.log ((n : ℝ) + 1) := by
        unfold ss5_eps
        rw [one_div, Real.log_inv, neg_neg]
      rw [hlog] at h1
      unfold ss5_U
      have : 0 ≤ (1 / 4 : ℝ) * ‖z‖ ^ 2 := by positivity
      have e : Real.log ((n : ℝ) + 1) - B = Real.log ((n : ℝ) + 1) - B := rfl
      linarith
    have hNpos : (0 : ℝ) < 1 / (N : ℝ) := by
      have : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    have hlogT : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hUT : Tendsto (fun n : ℕ => ss5_U N (ss5_eps n) z) atTop atTop := by
      refine tendsto_atTop_mono hlow ?_
      exact (tendsto_atTop_add_const_right _ (-B) hlogT).const_mul_atTop hNpos |>.congr
        (fun n => by ring)
    have hUθ : Tendsto (fun n : ℕ => ss5_U N (ss5_eps n) z / θ) atTop atTop :=
      hUT.atTop_div_const hθ
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp hUθ
    have h3 := ENNReal.tendsto_ofReal h2
    simp only [ENNReal.ofReal_zero] at h3
    refine h3.congr fun n => ?_
    unfold ss5l_fn
    simp [Function.comp, neg_div]


/-- The uniform Gaussian majorant of the level densities. -/
def ss5l_dom (N : ℕ) (θ : ℝ) (z : Ch5 N) : ℝ :=
  Real.exp ((8 * (N : ℝ) ^ 2) / θ) * Real.exp (-(1 / (8 * θ)) * ‖z‖ ^ 2)

theorem ss5l_dom_nonneg (N : ℕ) (θ : ℝ) (z : Ch5 N) : 0 ≤ ss5l_dom N θ z := by
  unfold ss5l_dom; positivity

theorem ss5l_dom_int (N : ℕ) {θ : ℝ} (hθ : 0 < θ) : Integrable (ss5l_dom N θ) :=
  (ss5i_gauss_ch N (c := 1 / (8 * θ)) (by positivity)).const_mul _

theorem ss5l_fn_le (N : ℕ) {θ : ℝ} (hθ : 0 < θ) (n : ℕ) (z : Ch5 N) :
    ss5l_fn N θ n z ≤ ENNReal.ofReal (ss5l_dom N θ z) := by
  unfold ss5l_fn ss5l_dom
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := ss5t_U_ge (N := N) (ss5_eps_pos n) (ss5_eps_le_one n) z
  have h2 : -ss5_U N (ss5_eps n) z / θ ≤
      -((1 / 8 : ℝ) * ‖z‖ ^ 2 - 8 * (N : ℝ) ^ 2) / θ := by
    apply div_le_div_of_nonneg_right _ hθ.le
    linarith
  refine h2.trans (le_of_eq ?_)
  field_simp
  ring

theorem ss5l_finf_le_fn (N : ℕ) {θ : ℝ} (hθ : 0 < θ) (n : ℕ) (z : Ch5 N) :
    ss5l_finf N θ z ≤ ss5l_fn N θ n z := by
  unfold ss5l_finf
  by_cases hz : z ∈ ss5_chamber N
  · rw [Set.indicator_of_mem hz]
    unfold ss5l_fn
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 := ss5i_PhiTr_le (N := N) (ss5_eps_pos n) hz
    unfold ss5_U ss5l_Ulim
    apply div_le_div_of_nonneg_right _ hθ.le
    linarith
  · rw [Set.indicator_of_notMem hz]
    exact bot_le

theorem ss5l_finf_ne_top (N : ℕ) (θ : ℝ) (z : Ch5 N) : ss5l_finf N θ z ≠ ⊤ := by
  unfold ss5l_finf
  by_cases hz : z ∈ ss5_chamber N
  · rw [Set.indicator_of_mem hz]; exact ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem hz]; exact ENNReal.zero_ne_top

theorem ss5l_m_tendsto {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun n => ss5_partition θ (ss5_U N (ss5_eps n))) atTop
      (𝓝 (∫⁻ z : Ch5 N, ss5l_finf N θ z)) := by
  have hint : ∫⁻ z : Ch5 N, ENNReal.ofReal (ss5l_dom N θ z) ≠ ⊤ :=
    (ss5l_dom_int N hθ).lintegral_lt_top.ne
  exact tendsto_lintegral_of_dominated_convergence (fun z => ENNReal.ofReal (ss5l_dom N θ z))
    (fun n => ss5l_fn_meas N θ n) (fun n => Eventually.of_forall fun z => ss5l_fn_le N hθ n z) hint
    (Eventually.of_forall fun z => ss5l_fn_tendsto hN hθ z)

theorem ss5l_m_pos_fin {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : 0 < θ) :
    (∫⁻ z : Ch5 N, ss5l_finf N θ z) ≠ 0 ∧ (∫⁻ z : Ch5 N, ss5l_finf N θ z) ≠ ⊤ := by
  constructor
  · refine ((lintegral_pos_iff_support (ss5l_finf_meas N θ)).2 ?_).ne'
    have hsupp : Function.support (ss5l_finf N θ) = ss5_chamber N := by
      ext z
      unfold ss5l_finf
      by_cases hz : z ∈ ss5_chamber N
      · simp [Set.indicator_of_mem hz, hz, Real.exp_pos]
      · simp [Set.indicator_of_notMem hz, hz]
    rw [hsupp]
    refine (ss5l_chamber_open N).measure_pos _ ?_
    refine ⟨WithLp.toLp 2 fun k : Fin N => ((k : ℕ) : ℝ), fun k l hkl => ?_⟩
    simpa using hkl
  · have h0 := (ss5i_partition (N := N) (ε := ss5_eps 0) (θ := θ) (ss5_eps_pos 0) hθ).2
    refine ne_top_of_le_ne_top h0 ?_
    exact lintegral_mono fun z => ss5l_finf_le_fn N hθ 0 z

/-- The normalised limit reference measure. -/
def ss5l_ref (N : ℕ) (θ : ℝ) : Measure (Ch5 N) :=
  (∫⁻ z : Ch5 N, ss5l_finf N θ z)⁻¹ • (volume : Measure (Ch5 N)).withDensity (ss5l_finf N θ)

theorem ss5l_prob_smul {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0∞} {μ : Measure α}
    (hf : Measurable f) (h0 : ∫⁻ x, f x ∂μ ≠ 0) (ht : ∫⁻ x, f x ∂μ ≠ ⊤) :
    IsProbabilityMeasure ((∫⁻ x, f x ∂μ)⁻¹ • μ.withDensity f) := by
  refine ⟨?_⟩
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 ht

theorem ss5l_ref_prob {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : 0 < θ) : IsProbabilityMeasure (ss5l_ref N θ) :=
  ss5l_prob_smul (ss5l_finf_meas N θ) (ss5l_m_pos_fin hN hθ).1 (ss5l_m_pos_fin hN hθ).2

theorem ss5l_refn_prob {N : ℕ} {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    IsProbabilityMeasure (ss5_ref θ (ss5_U N (ss5_eps n))) :=
  ss5l_prob_smul (f := fun z : Ch5 N => ss5l_fn N θ n z) (ss5l_fn_meas N θ n)
    (ss5i_partition (N := N) (ss5_eps_pos n) hθ).1 (ss5i_partition (N := N) (ss5_eps_pos n) hθ).2

theorem ss5l_ref_integral {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0∞} {μ : Measure α}
    (hf : Measurable f) (hft : ∀ x, f x ≠ ⊤) (g : α → ℝ) :
    ∫ x, g x ∂((∫⁻ x, f x ∂μ)⁻¹ • μ.withDensity f) =
      (((∫⁻ x, f x ∂μ)⁻¹).toReal) * ∫ x, (f x).toReal * g x ∂μ := by
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hf
    (Eventually.of_forall fun x => (hft x).lt_top)]
  simp only [smul_eq_mul]

theorem ss5l_ref_tendsto {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : 0 < θ) {g : Ch5 N → ℝ}
    (hg : Continuous g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Tendsto (fun n => ∫ x, g x ∂(ss5_ref θ (ss5_U N (ss5_eps n)))) atTop
      (𝓝 (∫ x, g x ∂(ss5l_ref N θ))) := by
  have hpf := ss5l_m_pos_fin hN hθ
  have hZ := ss5l_m_tendsto hN hθ
  have h1 : Tendsto (fun n => ((ss5_partition θ (ss5_U N (ss5_eps n)))⁻¹).toReal) atTop
      (𝓝 (((∫⁻ z : Ch5 N, ss5l_finf N θ z)⁻¹).toReal)) :=
    (ENNReal.tendsto_toReal (ENNReal.inv_ne_top.2 hpf.1)).comp (_root_.tendsto_inv_iff.2 hZ)
  have h2 : Tendsto (fun n => ∫ x, (ss5l_fn N θ n x).toReal * g x) atTop
      (𝓝 (∫ x, (ss5l_finf N θ x).toReal * g x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ss5l_dom N θ x * C)
      (fun n => ((ss5l_fn_meas N θ n).ennreal_toReal.mul hg.measurable).aestronglyMeasurable)
      ((ss5l_dom_int N hθ).mul_const C) (fun n => Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      have h3 : (ss5l_fn N θ n x).toReal ≤ ss5l_dom N θ x := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (ss5l_fn_le N hθ n x)
        rwa [ENNReal.toReal_ofReal (ss5l_dom_nonneg N θ x)] at this
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul h3 (hC x) (abs_nonneg _) (ss5l_dom_nonneg N θ x)
    · refine Eventually.of_forall fun x => ?_
      exact ((ENNReal.tendsto_toReal (ss5l_finf_ne_top N θ x)).comp
        (ss5l_fn_tendsto hN hθ x)).mul_const _
  have hrw : ∀ n, ∫ x, g x ∂(ss5_ref θ (ss5_U N (ss5_eps n))) =
      (((ss5_partition θ (ss5_U N (ss5_eps n)))⁻¹).toReal) * ∫ x, (ss5l_fn N θ n x).toReal * g x := by
    intro n
    exact ss5l_ref_integral (f := fun z : Ch5 N => ss5l_fn N θ n z) (ss5l_fn_meas N θ n)
      (fun x => (ss5l_fn_le N hθ n x).trans_lt ENNReal.ofReal_lt_top |>.ne) g
  simp_rw [hrw]
  rw [show ss5l_ref N θ = (∫⁻ z : Ch5 N, ss5l_finf N θ z)⁻¹ •
    (volume : Measure (Ch5 N)).withDensity (ss5l_finf N θ) from rfl,
    ss5l_ref_integral (ss5l_finf_meas N θ) (ss5l_finf_ne_top N θ) g]
  exact h1.mul h2


/-- The `ENNReal` liminf passes through the coercion to `EReal`. -/
theorem ss5l_coe_liminf (a : ℕ → ℝ≥0∞) :
    ((liminf a atTop : ℝ≥0∞) : EReal) = liminf (fun n => (a n : EReal)) atTop := by
  have hm : Monotone (fun x : ℝ≥0∞ => (x : EReal)) := fun x y h =>
    EReal.coe_ennreal_le_coe_ennreal_iff.2 h
  exact hm.map_liminf_of_continuousAt (F := atTop) a continuous_coe_ennreal_ereal.continuousAt

/-- **Entropy lower semicontinuity in chamber coordinates** (narrow convergence of the laws). -/
theorem ss5l_entropy_lsc_ch {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : 0 < θ) {μ : Measure (Ch5 N)}
    {μn : ℕ → Measure (Ch5 N)} [IsProbabilityMeasure μ] [∀ n, IsProbabilityMeasure (μn n)]
    (hconv : ∀ ψ : Ch5 N → ℝ, Continuous ψ → (∃ C, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x ∂(μn n)) atTop (𝓝 (∫ x, ψ x ∂μ))) :
    ((klDiv μ (ss5l_ref N θ) : ℝ≥0∞) : EReal) -
        ((Real.log (∫⁻ z : Ch5 N, ss5l_finf N θ z).toReal : ℝ) : EReal) ≤
      liminf (fun n => ss5_ent θ (ss5_U N (ss5_eps n)) (μn n)) atTop := by
  haveI := ss5l_ref_prob hN hθ
  haveI : ∀ n, IsProbabilityMeasure (ss5_ref θ (ss5_U N (ss5_eps n))) := ss5l_refn_prob hθ
  have hkl := ss5l_klDiv_liminf (μ := μ) (μn := μn) (ρ := ss5l_ref N θ)
    (ρn := fun n => ss5_ref θ (ss5_U N (ss5_eps n))) hconv
    (fun ψ hψ ⟨C, hC⟩ => ss5l_ref_tendsto hN hθ hψ hC)
  have hkl' : ((klDiv μ (ss5l_ref N θ) : ℝ≥0∞) : EReal) ≤
      liminf (fun n => ((klDiv (μn n) (ss5_ref θ (ss5_U N (ss5_eps n))) : ℝ≥0∞) : EReal)) atTop := by
    rw [← ss5l_coe_liminf]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 hkl
  have hpf := ss5l_m_pos_fin hN hθ
  have hZ := ss5l_m_tendsto hN hθ
  have hlog : Tendsto (fun n => Real.log (ss5_partition θ (ss5_U N (ss5_eps n))).toReal) atTop
      (𝓝 (Real.log (∫⁻ z : Ch5 N, ss5l_finf N θ z).toReal)) := by
    have h1 := (ENNReal.tendsto_toReal hpf.2).comp hZ
    refine (Real.continuousAt_log ?_).tendsto.comp h1
    exact (ENNReal.toReal_pos hpf.1 hpf.2).ne'
  have hneg : Tendsto
      (fun n => -((Real.log (ss5_partition θ (ss5_U N (ss5_eps n))).toReal : ℝ) : EReal)) atTop
      (𝓝 (-((Real.log (∫⁻ z : Ch5 N, ss5l_finf N θ z).toReal : ℝ) : EReal))) :=
    (continuous_neg.tendsto _).comp ((continuous_coe_real_ereal.tendsto _).comp hlog)
  unfold ss5_ent relEntropy
  simp_rw [sub_eq_add_neg]
  calc _ ≤ liminf (fun n => ((klDiv (μn n) (ss5_ref θ (ss5_U N (ss5_eps n))) : ℝ≥0∞) : EReal)) atTop +
        -((Real.log (∫⁻ z : Ch5 N, ss5l_finf N θ z).toReal : ℝ) : EReal) :=
        add_le_add_left hkl' _
    _ = _ + liminf (fun n => -((Real.log (ss5_partition θ (ss5_U N (ss5_eps n))).toReal : ℝ) : EReal))
        atTop := by rw [hneg.liminf_eq]
    _ ≤ _ := EReal.le_liminf_add


/-! ### Transport of the entropy to configuration space -/

theorem ss5l_weight_nonneg (N : ℕ) (θ : ℝ) (ξ : EucConfig 1 N) : 0 ≤ selfSimWeight 1 0 θ N 0 ξ := by
  unfold selfSimWeight
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem ss5l_ZG_ne_top {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : 0 < θ) :
    gibbsPartitionW (selfSimWeight 1 0 θ N 0) ≠ ⊤ := by
  unfold gibbsPartitionW
  set K : ℝ := Real.exp (θ⁻¹ * ((N : ℝ) / 2)) with hK
  have hc : 0 < θ⁻¹ / 8 := by positivity
  have hG := ((ss5h_gauss_integrable N hc).const_mul K).lintegral_lt_top
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hG)
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := ss5h_weight_le hN hθ ξ
  refine h1.trans (le_of_eq ?_)
  rw [hK, ← Real.exp_add]
  congr 1
  ring

theorem ss5l_klDiv_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν e.measurable) ?_
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rw [Measure.map_map e.symm.measurable e.measurable, Measure.map_map e.symm.measurable e.measurable] at h
  have e1 : ((e.symm : β → α) ∘ (e : α → β)) = id := by funext x; simp
  rw [e1, Measure.map_id, Measure.map_id] at h
  exact h

theorem ss5l_winf_le {N : ℕ} (σ : Equiv.Perm (Fin N)) (θ : ℝ) :
    (volume : Measure (Ch5 N)).withDensity (ss5l_finf N θ) ≤
      ((volume : Measure (EucConfig 1 N)).withDensity
        fun ξ => ENNReal.ofReal (selfSimWeight 1 0 θ N 0 ξ)).map (ss5_toCh σ) := by
  have hT : Measurable (ss5_toCh σ : EucConfig 1 N → Ch5 N) := (ss5i_toCh_mp σ).measurable
  have hC := ss5i_chamber_measurable N
  refine Measure.le_iff.2 fun A hA => ?_
  have hAC : MeasurableSet (A ∩ ss5_chamber N) := hA.inter hC
  have hpre : MeasurableSet ((ss5_toCh σ) ⁻¹' (A ∩ ss5_chamber N)) := hT hAC
  have hpreA : MeasurableSet ((ss5_toCh σ) ⁻¹' A) := hT hA
  rw [Measure.map_apply hT hA, withDensity_apply _ hpreA, withDensity_apply _ hA]
  have hind : ∫⁻ z in A, ss5l_finf N θ z =
      ∫⁻ z in A ∩ ss5_chamber N, ENNReal.ofReal (Real.exp (-ss5l_Ulim N z / θ)) := by
    unfold ss5l_finf
    rw [lintegral_indicator hC, Measure.restrict_restrict hC, Set.inter_comm]
  have hmp := (ss5i_toCh_mp σ).setLIntegral_comp_preimage hAC
    (f := fun z : Ch5 N => ENNReal.ofReal (Real.exp (-ss5l_Ulim N z / θ)))
    ((Real.measurable_exp.comp ((ss5l_Ulim_meas N).neg.div_const θ)).ennreal_ofReal)
  rw [hind, ← hmp]
  calc ∫⁻ x in (ss5_toCh σ) ⁻¹' (A ∩ ss5_chamber N), ENNReal.ofReal (Real.exp (-ss5l_Ulim N (ss5_toCh σ x) / θ))
      = ∫⁻ x in (ss5_toCh σ) ⁻¹' (A ∩ ss5_chamber N), ENNReal.ofReal (selfSimWeight 1 0 θ N 0 x) := by
        refine setLIntegral_congr_fun hpre fun x hx => ?_
        have hxc : x ∈ ss5_cone σ := hx.2
        rw [ss5i_weight_cone σ hxc]
        unfold ss5l_Ulim
        rfl
    _ ≤ ∫⁻ x in (ss5_toCh σ) ⁻¹' A, ENNReal.ofReal (selfSimWeight 1 0 θ N 0 x) :=
        lintegral_mono_set (Set.preimage_mono Set.inter_subset_left)


theorem ss5l_entropy_transport {N : ℕ} (hN : 0 < N) (σ : Equiv.Perm (Fin N)) {θ : ℝ} (hθ : 0 < θ)
    (ν : Measure (EucConfig 1 N)) [IsProbabilityMeasure ν] :
    gibbsEntropyW (selfSimWeight 1 0 θ N 0) ν ≤
      ((klDiv (ν.map (ss5_toCh σ)) (ss5l_ref N θ) : ℝ≥0∞) : EReal) -
        ((Real.log (∫⁻ z : Ch5 N, ss5l_finf N θ z).toReal : ℝ) : EReal) := by
  have hT : Measurable (ss5_toCh σ : EucConfig 1 N → Ch5 N) := (ss5i_toCh_mp σ).measurable
  have hC := ss5i_chamber_measurable N
  set G := selfSimWeight 1 0 θ N 0 with hG
  set μ : Measure (Ch5 N) := ν.map (ss5_toCh σ) with hμ
  haveI : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 inferInstance
  set wG : Measure (EucConfig 1 N) := volume.withDensity fun ξ => ENNReal.ofReal (G ξ) with hwG
  set winf : Measure (Ch5 N) := volume.withDensity (ss5l_finf N θ) with hwinf
  set m : ℝ≥0∞ := ∫⁻ z : Ch5 N, ss5l_finf N θ z with hm
  have hpf := ss5l_m_pos_fin hN hθ
  have hZw : winf Set.univ = m := by
    rw [hwinf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hZG : gibbsPartitionW G = wG Set.univ := by
    rw [hwG, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; rfl
  have hrefG : gibbsRefW G = (wG Set.univ)⁻¹ • wG := by
    unfold gibbsRefW; rw [hZG]
  have hrefinf : ss5l_ref N θ = (winf Set.univ)⁻¹ • winf := by
    unfold ss5l_ref; rw [hZw]
  by_cases hK : klDiv μ (ss5l_ref N θ) = ⊤
  · rw [hK]
    simp [EReal.top_sub_coe]
  haveI : IsFiniteMeasure winf := ⟨by rw [hZw]; exact lt_top_iff_ne_top.2 hpf.2⟩
  have hZGt : wG Set.univ ≠ ⊤ := by rw [← hZG]; exact ss5l_ZG_ne_top hN hθ
  haveI : IsFiniteMeasure wG := ⟨lt_top_iff_ne_top.2 hZGt⟩
  rw [hrefinf] at hK
  obtain ⟨hn1, hn2⟩ := ss5i_norm (μ := μ) (w := winf) (by rw [hZw]; exact hpf.1)
  have hKw : klDiv μ winf ≠ ⊤ := hn1.1 hK
  have hμac : μ ≪ winf := (klDiv_ne_top_iff.1 hKw).1
  -- `μ` is carried by the chamber
  have hwinfC : winf (ss5_chamber N)ᶜ = 0 := by
    rw [hwinf, withDensity_apply _ hC.compl]
    rw [setLIntegral_congr_fun hC.compl (g := fun _ => 0) (fun z hz => by
      unfold ss5l_finf; rw [Set.indicator_of_notMem hz])]
    simp
  have hμs : μ (ss5_chamber N)ᶜ = 0 := hμac hwinfC
  set w' : Measure (Ch5 N) := wG.map (ss5_toCh σ) with hw'
  have hle : winf ≤ w' := ss5l_winf_le σ θ
  have hmass : w' Set.univ = wG Set.univ := by
    rw [hw', Measure.map_apply hT MeasurableSet.univ]; rfl
  have hZG0 : wG Set.univ ≠ 0 := by
    intro h0
    have : winf Set.univ ≤ w' Set.univ := hle Set.univ
    rw [hmass, h0, hZw] at this
    exact hpf.1 (le_antisymm this bot_le)
  haveI : IsFiniteMeasure w' := by rw [hw']; infer_instance
  have hcmp := ss5i_klDiv_cmp (μ := μ) (ν₁ := winf) (ν₂ := w') hC hμs hμac
    (Measure.restrict_le_self.trans hle)
  have hkeq : klDiv μ w' = klDiv ν wG := ss5l_klDiv_equiv (ss5l_equiv σ) ν wG
  rw [hmass] at hcmp
  have hKG : klDiv ν wG ≠ ⊤ := by
    rw [← hkeq]
    have : klDiv μ w' + winf Set.univ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hKw, measure_ne_top _ _⟩) hcmp
    exact fun h => this (by rw [h]; simp)
  obtain ⟨hm1, hm2⟩ := ss5i_norm (μ := ν) (w := wG) hZG0
  have hKG' := hm1.2 hKG
  have e1 := hm2 hKG
  have e2 := hn2 hKw
  unfold gibbsEntropyW relEntropy
  change ((klDiv ν (gibbsRefW G) : ℝ≥0∞) : EReal) - ((Real.log (gibbsPartitionW G).toReal : ℝ) : EReal) ≤
    ((klDiv μ (ss5l_ref N θ) : ℝ≥0∞) : EReal) - ((Real.log m.toReal : ℝ) : EReal)
  rw [hrefG, hrefinf, hZG, ← hZw]
  rw [← EReal.coe_ennreal_toReal hKG', ← EReal.coe_ennreal_toReal hK, ← EReal.coe_sub,
    ← EReal.coe_sub, EReal.coe_le_coe_iff, e1, e2]
  have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hKw, measure_ne_top _ _⟩) hcmp
  rw [← hkeq] at *
  rw [ENNReal.toReal_add (by rw [hkeq]; exact hKG) (measure_ne_top _ _),
    ENNReal.toReal_add hKw (measure_ne_top _ _)] at h3
  rw [hkeq] at h3
  linarith


/-- **Entropy lower semicontinuity with moving references**, from the configuration-space law `ν` to the chamber
laws `μn` converging narrowly to `ν.map (ss5_toCh σ)`. -/
theorem ss5l_entropy_lsc {N : ℕ} (hN : 0 < N) (σ : Equiv.Perm (Fin N)) {θ : ℝ} (hθ : 0 < θ)
    (ν : Measure (EucConfig 1 N)) [IsProbabilityMeasure ν] (μn : ℕ → Measure (Ch5 N))
    [∀ n, IsProbabilityMeasure (μn n)]
    (hconv : ∀ ψ : Ch5 N → ℝ, Continuous ψ → (∃ C, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x ∂(μn n)) atTop (𝓝 (∫ x, ψ x ∂(ν.map (ss5_toCh σ))))) :
    gibbsEntropyW (selfSimWeight 1 0 θ N 0) ν ≤
      liminf (fun n => ss5_ent θ (ss5_U N (ss5_eps n)) (μn n)) atTop := by
  have hT : Measurable (ss5_toCh σ : EucConfig 1 N → Ch5 N) := (ss5i_toCh_mp σ).measurable
  haveI : IsProbabilityMeasure (ν.map (ss5_toCh σ)) :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 inferInstance
  exact (ss5l_entropy_transport hN σ hθ ν).trans (ss5l_entropy_lsc_ch hN hθ hconv)

end HRS.MP.SelfSimP5Impl
