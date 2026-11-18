import HRS.MP.SelfSimP4Gibbs
import HRS.Appendix.B15BAux1

/-!
# MP-SSP4LSCM: `p4_lsc_M` (lower semicontinuity of entropy and Fisher information with moving reference)

Namespace `HRS.MP.SelfSimP4Impl`, helpers `p4m_`.  Theorem `p4_lsc_M_proof`, tied to `HRS.MP.SelfSimP4.p4_lsc_M`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4Impl

/-! ### Setwise convergence gives convergence of bounded measurable integrals -/

theorem p4m_setwise_integral {E : Type*} [MeasurableSpace E] {μ : Measure E} {μn : ℕ → Measure E}
    [IsProbabilityMeasure μ] [∀ n, IsProbabilityMeasure (μn n)]
    (htv : ∀ A : Set E, MeasurableSet A → Tendsto (fun n => μn n A) atTop (𝓝 (μ A)))
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Tendsto (fun n => ∫ x, f x ∂(μn n)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  set g : E → ℝ := fun x => f x + C with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => by have := (abs_le.1 (hC x)).1; simp only [hg]; linarith
  have hgm : Measurable g := hf.add_const C
  have hg2 : ∀ x, g x ≤ 2 * C := fun x => by have := (abs_le.1 (hC x)).2; simp only [hg]; linarith
  -- layer cake for every probability measure
  have hlayer : ∀ ν : Measure E, ∫⁻ x, ENNReal.ofReal (g x) ∂ν =
      ∫⁻ t in Set.Ioi (0 : ℝ), ν {a | t < g a} := fun ν =>
    lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hg0) hgm.aemeasurable
  have hbound : Tendsto (fun n => ∫⁻ t in Set.Ioi (0 : ℝ), μn n {a | t < g a}) atTop
      (𝓝 (∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < g a})) := by
    refine tendsto_lintegral_of_dominated_convergence
      (fun t => Set.indicator (Set.Ioc 0 (2 * C)) (fun _ => (1 : ℝ≥0∞)) t) ?_ ?_ ?_ ?_
    · intro n
      exact (Antitone.measurable (fun s t hst => measure_mono fun a ha => lt_of_le_of_lt hst ha))
    · intro n
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      show μn n {a | t < g a} ≤ Set.indicator (Set.Ioc 0 (2 * C)) (fun _ => (1 : ℝ≥0∞)) t
      by_cases h : t ≤ 2 * C
      · rw [Set.indicator_of_mem (show t ∈ Set.Ioc 0 (2 * C) from ⟨ht, h⟩)]
        exact prob_le_one
      · have : {a | t < g a} = ∅ := by
          ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
          exact (hg2 a).trans (not_le.1 h).le
        rw [this]; simp
    · rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul]
      exact ((measure_mono Set.inter_subset_left).trans_lt measure_Ioc_lt_top).ne
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      exact htv _ (measurableSet_lt measurable_const hgm)
  have hlint : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (g x) ∂(μn n)) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (g x) ∂μ)) := by
    simp_rw [hlayer]; exact hbound
  have hfin : ∀ ν : Measure E, IsProbabilityMeasure ν → ∫⁻ x, ENNReal.ofReal (g x) ∂ν ≠ ⊤ := by
    intro ν hν
    haveI := hν
    refine ne_top_of_le_ne_top (b := ∫⁻ _x, ENNReal.ofReal (2 * C) ∂ν)
      (by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top) ?_
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hg2 x)
  have hreal : Tendsto (fun n => ∫ x, g x ∂(μn n)) atTop (𝓝 (∫ x, g x ∂μ)) := by
    have := (ENNReal.tendsto_toReal (hfin μ inferInstance)).comp hlint
    have e : ∀ ν : Measure E, ∫ x, g x ∂ν = (∫⁻ x, ENNReal.ofReal (g x) ∂ν).toReal := fun ν =>
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm.aestronglyMeasurable
    simp_rw [e]
    exact this
  have hsub : ∀ ν : Measure E, IsProbabilityMeasure ν → ∫ x, f x ∂ν = ∫ x, g x ∂ν - C := by
    intro ν hν
    have hi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable C
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
    simp only [hg]
    rw [integral_add hi (integrable_const C)]
    simp
  simp_rw [hsub _ inferInstance]
  exact hreal.sub_const C

/-! ### The cube embedding and lower semicontinuity of `klDiv` -/

/-- The coordinate squashing `t ↦ t/(1+|t|)` into `(-1,1)`. -/
def p4m_h (t : ℝ) : ℝ := t / (1 + |t|)

theorem p4m_h_mem (t : ℝ) : p4m_h t ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold p4m_h
  have h : 0 < 1 + |t| := by positivity
  rw [Set.mem_Icc, ← abs_le, abs_div, abs_of_pos h, div_le_one h]
  linarith

theorem p4m_h_inj : Function.Injective p4m_h := by
  have key : ∀ t, |p4m_h t| = |t| / (1 + |t|) := fun t => by
    unfold p4m_h
    rw [abs_div, abs_of_pos (by positivity : 0 < 1 + |t|)]
  have inv : ∀ t, p4m_h t / (1 - |p4m_h t|) = t := fun t => by
    rw [key]
    have h : (0 : ℝ) < 1 + |t| := by positivity
    have : 1 - |t| / (1 + |t|) = 1 / (1 + |t|) := by field_simp; ring
    rw [this]
    unfold p4m_h
    field_simp
  intro t u htu
  rw [← inv t, ← inv u, htu]

theorem p4m_h_cont : Continuous p4m_h :=
  continuous_id.div (continuous_const.add continuous_abs) (fun t => by positivity)

/-- The compact cube `[-1,1]^{N×d}`. -/
abbrev P4mCube (d N : ℕ) := Fin N × Fin d → Set.Icc (-1 : ℝ) 1

/-- The embedding of `(ℝ^d)^N` into the cube. -/
def p4mF (d N : ℕ) (x : EucConfig d N) : P4mCube d N := fun k => ⟨p4m_h (x k.1 k.2), p4m_h_mem _⟩

theorem p4mF_cont (d N : ℕ) : Continuous (p4mF d N) := by
  refine continuous_pi fun k => Continuous.subtype_mk ?_ _
  exact p4m_h_cont.comp ((PiLp.continuous_apply 2 _ k.2).comp (continuous_apply k.1))

theorem p4mF_embedding (d N : ℕ) : MeasurableEmbedding (p4mF d N) := by
  refine (p4mF_cont d N).measurableEmbedding ?_
  intro x y hxy
  funext i
  refine PiLp.ext fun j => p4m_h_inj ?_
  have := congrArg (fun z : P4mCube d N => (z (i, j) : ℝ)) hxy
  simpa [p4mF] using this

theorem p4m_klDiv_le_map (d N : ℕ) (μ ρ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ] :
    klDiv μ ρ ≤ klDiv (μ.map (p4mF d N)) (ρ.map (p4mF d N)) := by
  obtain ⟨g, hg, hgF⟩ := (p4mF_embedding d N).exists_measurable_extend
    (measurable_id : Measurable (id : EucConfig d N → EucConfig d N)) (fun _ => ⟨0⟩)
  have h := klDiv_map_le (μ.map (p4mF d N)) (ρ.map (p4mF d N)) hg
  rw [Measure.map_map hg (p4mF_embedding d N).measurable, Measure.map_map hg
    (p4mF_embedding d N).measurable, hgF, Measure.map_id, Measure.map_id] at h
  exact h

/-- Lower semicontinuity of `klDiv` along sequences with narrow-in-the-bounded-measurable-sense convergence of
both arguments (no compactness: through the cube embedding). -/
theorem p4lm_klDiv_liminf {d N : ℕ} {μ ρ : Measure (EucConfig d N)} {μn ρn : ℕ → Measure (EucConfig d N)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] [∀ n, IsProbabilityMeasure (μn n)]
    [∀ n, IsProbabilityMeasure (ρn n)]
    (hμ : ∀ ψ : EucConfig d N → ℝ, Measurable ψ → (∃ C, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x ∂(μn n)) atTop (𝓝 (∫ x, ψ x ∂μ)))
    (hρ : ∀ ψ : EucConfig d N → ℝ, Measurable ψ → (∃ C, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x ∂(ρn n)) atTop (𝓝 (∫ x, ψ x ∂ρ))) :
    klDiv μ ρ ≤ liminf (fun n => klDiv (μn n) (ρn n)) atTop := by
  have hFm : Measurable (p4mF d N) := (p4mF_embedding d N).measurable
  have hw : ∀ (ν : Measure (EucConfig d N)) (φ : P4mCube d N → ℝ), Continuous φ →
      ∫ y, φ y ∂(ν.map (p4mF d N)) = ∫ x, φ (p4mF d N x) ∂ν := fun ν φ hφ =>
    integral_map hFm.aemeasurable hφ.aestronglyMeasurable
  have hbd : ∀ φ : P4mCube d N → ℝ, Continuous φ → ∃ C, ∀ x, |φ (p4mF d N x)| ≤ C := by
    intro φ hφ
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
    exact ⟨C, fun x => by simpa using hC (p4mF d N x) trivial⟩
  have key := b15b_klDiv_liminf_le (P := μ.map (p4mF d N)) (Q := ρ.map (p4mF d N))
    (Pn := fun n => (μn n).map (p4mF d N)) (Qn := fun n => (ρn n).map (p4mF d N))
    (fun φ hφ => by
      simp_rw [hw _ φ hφ]
      exact hμ _ (hφ.measurable.comp hFm) (hbd φ hφ))
    (fun φ hφ => by
      simp_rw [hw _ φ hφ]
      exact hρ _ (hφ.measurable.comp hFm) (hbd φ hφ))
  refine (p4m_klDiv_le_map d N μ ρ).trans (key.trans ?_)
  exact liminf_le_liminf (Eventually.of_forall fun n => klDiv_map_le _ _ hFm)
    (by isBoundedDefault) (by isBoundedDefault)

/-! ### Convergence of the moving references -/

variable {d N : ℕ}

theorem p4m_pot_eq {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (τ : ℝ) (x : EucConfig d N)
    (hx : ∀ i j, i ≠ j → r₀ ≤ ‖x i - x j‖) :
    p4Pot k s N τ x = selfSimPotential d s N τ x := by
  unfold p4Pot selfSimPotential
  have hsum : ∑ i, ∑ j ∈ Finset.univ.erase i, k (x i - x j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (x i - x j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
    exact hk.eq_far _ (hx i j hij)
  rw [hsum]

theorem p4m_ev_far (x : EucConfig d N) (hx : x ∉ eucCollisionSet d N) :
    ∀ᶠ M : ℕ in atTop, ∀ i j, i ≠ j → 1 / ((M : ℝ) + 1) ≤ ‖x i - x j‖ := by
  rw [Filter.eventually_all]; intro i; rw [Filter.eventually_all]; intro j
  by_cases hij : i = j
  · exact Eventually.of_forall fun M h => absurd hij h
  have hne : 0 < ‖x i - x j‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hx ⟨i, j, hij, h⟩)
  filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hne)]
    with M hM _ using hM.le

theorem p4m_weight_eventually {s : ℝ} {invβ τ : ℝ} {gM : ℕ → Euc d → ℝ}
    (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M)) (x : EucConfig d N)
    (hx : x ∉ eucCollisionSet d N) :
    ∀ᶠ M : ℕ in atTop,
      p4GibbsOf invβ (p4Pot (gM M) s N τ) x = selfSimWeight d s invβ N τ x := by
  filter_upwards [p4m_ev_far x hx] with M hM
  classical
  simp only [selfSimWeight, p4GibbsOf, if_neg hx]
  rw [p4m_pot_eq (hgM M) τ x hM]

/-- The uniform Gaussian majorant. -/
theorem p4m_major {s : ℝ} {invβ : ℝ} (hβ : 0 < invβ) (τ : ℝ) {gM : ℕ → Euc d → ℝ}
    (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M)) (M : ℕ) (x : EucConfig d N) :
    p4GibbsOf invβ (p4Pot (gM M) s N τ) x ≤
      Real.exp (invβ⁻¹ * (2 * (aSelfSim s τ * N) ^ 2)) * Real.exp (-(invβ⁻¹ / 8 * ‖x‖ ^ 2)) :=
  p4g_gibbsOf_le (hgM M) hβ τ x

theorem p4m_major_int {s : ℝ} {invβ : ℝ} (hβ : 0 < invβ) (τ : ℝ) :
    Integrable (fun x : EucConfig d N =>
      Real.exp (invβ⁻¹ * (2 * (aSelfSim s τ * N) ^ 2)) * Real.exp (-(invβ⁻¹ / 8 * ‖x‖ ^ 2))) volume :=
  (p4g_integrable_gauss_pi (c := invβ⁻¹ / 8) (by positivity)).const_mul _

theorem p4m_ae_noncollision (hd : 1 ≤ d) :
    ∀ᵐ x ∂(volume : Measure (EucConfig d N)), x ∉ eucCollisionSet d N := by
  rw [ae_iff]
  simpa using p4g_collision_null hd N

theorem p4m_pot_meas {s : ℝ} {r₀ : ℝ} {k : Euc d → ℝ}
    (hk : IsP4Kernel d s r₀ k) (invβ τ : ℝ) :
    Measurable (p4GibbsOf invβ (p4Pot k s N τ)) :=
  p4g_gibbsOf_meas _ (p4g_p4Pot_meas hk.smooth.continuous.measurable s N τ)

/-- Convergence of the partition functions. -/
theorem p4m_Z_tendsto (hd : 1 ≤ d) {s : ℝ} {invβ : ℝ} (hβ : 0 < invβ) (τ : ℝ) {gM : ℕ → Euc d → ℝ}
    (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M)) :
    Tendsto (fun M => gibbsPartitionW (p4GibbsOf invβ (p4Pot (gM M) s N τ))) atTop
      (𝓝 (gibbsPartitionW (selfSimWeight d s invβ N τ))) := by
  unfold gibbsPartitionW
  refine tendsto_lintegral_of_dominated_convergence
    (fun x => ENNReal.ofReal (Real.exp (invβ⁻¹ * (2 * (aSelfSim s τ * N) ^ 2)) *
      Real.exp (-(invβ⁻¹ / 8 * ‖x‖ ^ 2)))) (fun M => (p4m_pot_meas (hgM M) invβ τ).ennreal_ofReal)
    (fun M => Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (p4m_major hβ τ hgM M x))
    (p4m_major_int hβ τ).lintegral_lt_top.ne ?_
  filter_upwards [p4m_ae_noncollision (N := N) hd] with x hx
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [p4m_weight_eventually (invβ := invβ) (τ := τ) hgM x hx] with M hM
  rw [hM]

theorem p4m_ref_integral {G : EucConfig d N → ℝ} (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x)
    (ψ : EucConfig d N → ℝ) :
    ∫ x, ψ x ∂(gibbsRefW G) = ((gibbsPartitionW G)⁻¹).toReal * ∫ x, G x * ψ x := by
  unfold gibbsRefW
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hG.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hG0 x)]

theorem p4m_ref_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {invβ : ℝ} (hβ : 0 < invβ) (τ : ℝ)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M))
    {ψ : EucConfig d N → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C) :
    Tendsto (fun M => ∫ x, ψ x ∂(gibbsRefW (p4GibbsOf invβ (p4Pot (gM M) s N τ)))) atTop
      (𝓝 (∫ x, ψ x ∂(gibbsRefW (selfSimWeight d s invβ N τ)))) := by
  have hG := p4_gibbs_proof hd s hs0 N invβ hβ τ (hgM 0)
  have hZ0 : gibbsPartitionW (selfSimWeight d s invβ N τ) ≠ 0 := hG.1.1.ne'
  have hZt : gibbsPartitionW (selfSimWeight d s invβ N τ) ≠ ⊤ := hG.1.2.ne
  have hZ := p4m_Z_tendsto (N := N) hd hβ τ hgM
  have h1 : Tendsto (fun M => ((gibbsPartitionW (p4GibbsOf invβ (p4Pot (gM M) s N τ)))⁻¹).toReal)
      atTop (𝓝 ((gibbsPartitionW (selfSimWeight d s invβ N τ))⁻¹).toReal) :=
    (ENNReal.tendsto_toReal (ENNReal.inv_ne_top.2 hZ0)).comp (_root_.tendsto_inv_iff.2 hZ)
  have h2 : Tendsto (fun M => ∫ x, p4GibbsOf invβ (p4Pot (gM M) s N τ) x * ψ x) atTop
      (𝓝 (∫ x, selfSimWeight d s invβ N τ x * ψ x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => Real.exp (invβ⁻¹ * (2 * (aSelfSim s τ * N) ^ 2)) * Real.exp (-(invβ⁻¹ / 8 * ‖x‖ ^ 2)) * C)
      (fun M => ((p4m_pot_meas (hgM M) invβ τ).mul hψ).aestronglyMeasurable)
      ((p4m_major_int hβ τ).mul_const C) (fun M => Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      have hp : |p4GibbsOf invβ (p4Pot (gM M) s N τ) x| = p4GibbsOf invβ (p4Pot (gM M) s N τ) x :=
        abs_of_pos (by unfold p4GibbsOf; exact Real.exp_pos _)
      exact mul_le_mul (by rw [hp]; exact p4m_major hβ τ hgM M x) (hC x) (abs_nonneg _) (by positivity)
    · filter_upwards [p4m_ae_noncollision (N := N) hd] with x hx
      have : Tendsto (fun M => p4GibbsOf invβ (p4Pot (gM M) s N τ) x) atTop
          (𝓝 (selfSimWeight d s invβ N τ x)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [p4m_weight_eventually (invβ := invβ) (τ := τ) hgM x hx] with M hM
        rw [hM]
      exact this.mul_const _
  have hrw : ∀ M, ∫ x, ψ x ∂(gibbsRefW (p4GibbsOf invβ (p4Pot (gM M) s N τ))) =
      ((gibbsPartitionW (p4GibbsOf invβ (p4Pot (gM M) s N τ)))⁻¹).toReal *
        ∫ x, p4GibbsOf invβ (p4Pot (gM M) s N τ) x * ψ x := fun M =>
    p4m_ref_integral (p4m_pot_meas (hgM M) invβ τ) (fun x => (Real.exp_pos _).le) ψ
  simp_rw [hrw]
  rw [p4m_ref_integral (p4g_ssWeight_meas d s invβ N τ) (p4g_ssWeight_nonneg d s invβ N τ) ψ]
  exact h1.mul h2

/-- The `ENNReal` liminf passes through the coercion to `EReal`. -/
theorem p4m_coe_liminf (a : ℕ → ℝ≥0∞) :
    ((liminf a atTop : ℝ≥0∞) : EReal) = liminf (fun n => (a n : EReal)) atTop := by
  have hm : Monotone (fun x : ℝ≥0∞ => (x : EReal)) := fun x y h =>
    EReal.coe_ennreal_le_coe_ennreal_iff.2 h
  exact hm.map_liminf_of_continuousAt (F := atTop) a continuous_coe_ennreal_ereal.continuousAt

/-- **Entropy** part of `p4_lsc_M`. -/
theorem p4lm_entropy_lsc (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {invβ : ℝ} (hβ : 0 < invβ) (τ : ℝ)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M))
    {μ : Measure (EucConfig d N)} {μM : ℕ → Measure (EucConfig d N)}
    [IsProbabilityMeasure μ] [∀ M, IsProbabilityMeasure (μM M)]
    (htv : ∀ A : Set (EucConfig d N), MeasurableSet A →
      Tendsto (fun M => μM M A) atTop (𝓝 (μ A))) :
    gibbsEntropyW (selfSimWeight d s invβ N τ) μ ≤
      liminf (fun M => gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N τ)) (μM M)) atTop := by
  have hG := fun M => p4_gibbs_proof hd s hs0 N invβ hβ τ (hgM M)
  have hZs : 0 < gibbsPartitionW (selfSimWeight d s invβ N τ) ∧
      gibbsPartitionW (selfSimWeight d s invβ N τ) < ⊤ := (hG 0).1
  haveI : IsProbabilityMeasure (gibbsRefW (selfSimWeight d s invβ N τ)) :=
    p4g_ref_prob _ (p4g_ssWeight_meas d s invβ N τ) hZs.1.ne' hZs.2.ne
  haveI : ∀ M, IsProbabilityMeasure (gibbsRefW (p4GibbsOf invβ (p4Pot (gM M) s N τ))) := fun M =>
    p4g_ref_prob _ (p4m_pot_meas (hgM M) invβ τ) (hG M).2.1.1.ne' (hG M).2.1.2.ne
  have hkl := p4lm_klDiv_liminf (μ := μ) (μn := μM) (ρ := gibbsRefW (selfSimWeight d s invβ N τ))
    (ρn := fun M => gibbsRefW (p4GibbsOf invβ (p4Pot (gM M) s N τ)))
    (fun ψ hψ ⟨C, hC⟩ => p4m_setwise_integral htv hψ hC)
    (fun ψ hψ ⟨C, hC⟩ => p4m_ref_tendsto hd hs0 hβ τ hgM hψ hC)
  have hkl' : ((klDiv μ (gibbsRefW (selfSimWeight d s invβ N τ)) : ℝ≥0∞) : EReal) ≤
      liminf (fun M => ((klDiv (μM M) (gibbsRefW (p4GibbsOf invβ (p4Pot (gM M) s N τ))) : ℝ≥0∞) : EReal))
        atTop := by
    rw [← p4m_coe_liminf]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 hkl
  -- the logarithms of the partition functions converge
  have hZ := p4m_Z_tendsto (N := N) hd hβ τ hgM
  have hlog : Tendsto (fun M => Real.log (gibbsPartitionW (p4GibbsOf invβ (p4Pot (gM M) s N τ))).toReal)
      atTop (𝓝 (Real.log (gibbsPartitionW (selfSimWeight d s invβ N τ)).toReal)) := by
    have h1 := (ENNReal.tendsto_toReal hZs.2.ne).comp hZ
    refine (Real.continuousAt_log ?_).tendsto.comp h1
    exact (ENNReal.toReal_pos hZs.1.ne' hZs.2.ne).ne'
  have hneg : Tendsto (fun M => -((Real.log (gibbsPartitionW (p4GibbsOf invβ (p4Pot (gM M) s N τ))).toReal : ℝ) : EReal))
      atTop (𝓝 (-((Real.log (gibbsPartitionW (selfSimWeight d s invβ N τ)).toReal : ℝ) : EReal))) :=
    (continuous_neg.tendsto _).comp ((continuous_coe_real_ereal.tendsto _).comp hlog)
  unfold gibbsEntropyW relEntropy
  simp_rw [sub_eq_add_neg]
  calc _ ≤ liminf (fun M => ((klDiv (μM M) (gibbsRefW (p4GibbsOf invβ (p4Pot (gM M) s N τ))) : ℝ≥0∞) : EReal))
        atTop + -((Real.log (gibbsPartitionW (selfSimWeight d s invβ N τ)).toReal : ℝ) : EReal) :=
        add_le_add_left hkl' _
    _ = _ + liminf (fun M => -((Real.log (gibbsPartitionW (p4GibbsOf invβ (p4Pot (gM M) s N τ))).toReal : ℝ) : EReal)) atTop := by
        rw [hneg.liminf_eq]
    _ ≤ _ := EReal.le_liminf_add

/-! ### The Fisher information -/

/-- The integrand of the variational formula for `fisherInfoW`. -/
def p4m_fi (G : EucConfig d N → ℝ) (ζ : EucConfig d N → EucConfig d N) (X : EucConfig d N) : ℝ :=
  -2 * configDivW ζ X - 2 * fderiv ℝ (fun Z : EucConfig d N => Real.log (G Z)) X (ζ X) -
    ∑ i, ‖ζ X i‖ ^ 2

theorem p4m_fisher_eq (G : EucConfig d N → ℝ) (P : Measure (EucConfig d N)) :
    fisherInfoW G P = ⨆ (ζ : EucConfig d N → EucConfig d N) (_ : IsFisherTestFieldW ζ),
      ENNReal.ofReal (∫ X, p4m_fi G ζ X ∂P) := rfl

theorem p4m_dlog {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (θ τ : ℝ)
    (x v : EucConfig d N) :
    fderiv ℝ (fun Z : EucConfig d N => Real.log (p4GibbsOf θ (p4Pot k s N τ) Z)) x v =
      θ⁻¹ * ∑ i, inner ℝ (p4Drift k s N τ x i) (v i) := by
  have hev : ∀ y, k (-y) = k y := hk.even
  have h1 := (p4k_hasFDeriv_pot (hk.smooth.differentiable (by norm_num)) hev s N τ x).const_mul (-(θ⁻¹))
  have hf : (fun Z : EucConfig d N => Real.log (p4GibbsOf θ (p4Pot k s N τ) Z)) =
      fun Z => -(θ⁻¹) * p4Pot k s N τ Z := by
    funext Z; simp [p4GibbsOf]
  rw [hf, h1.fderiv]
  simp [p4k_p4InnerL_apply]

theorem p4m_dlog_cont {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (θ τ : ℝ)
    {ζ : EucConfig d N → EucConfig d N} (hζ : Continuous ζ) :
    Continuous fun x => fderiv ℝ (fun Z : EucConfig d N => Real.log (p4GibbsOf θ (p4Pot k s N τ) Z)) x (ζ x) := by
  have hd := p4k_cont_drift hk N
  have hdr : Continuous (p4Drift k s N τ) := by
    have h2 : Continuous fun x : EucConfig d N => Function.uncurry (p4Drift k s N) (τ, x) :=
      hd.comp (Continuous.prodMk continuous_const continuous_id)
    exact h2
  simp_rw [p4m_dlog hk θ τ]
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
  exact ((continuous_apply i).comp hdr).inner ((continuous_apply i).comp hζ)

theorem p4m_div_cont {ζ : EucConfig d N → EucConfig d N} (hζ : ContDiff ℝ ∞ ζ) :
    Continuous (configDivW ζ) := by
  unfold configDivW
  refine continuous_finsetSum _ fun k _ => ?_
  have hc : ContDiff ℝ ∞ (fun Z : EucConfig d N => ζ Z k.1 k.2) :=
    (EuclideanSpace.proj k.2 : Euc d →L[ℝ] ℝ).contDiff.comp
      ((contDiff_apply ℝ (Euc d) k.1).comp hζ)
  exact (hc.continuous_fderiv (by simp)).clm_apply continuous_const

theorem p4m_div_zero {ζ : EucConfig d N → EucConfig d N} {K : Set (EucConfig d N)}
    (hKc : IsClosed K) (hKz : ∀ x, x ∉ K → ζ x = 0) {x : EucConfig d N} (hx : x ∉ K) :
    configDivW ζ x = 0 := by
  unfold configDivW
  refine Finset.sum_eq_zero fun k _ => ?_
  have hev : (fun Z : EucConfig d N => ζ Z k.1 k.2) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hKc.isOpen_compl.mem_nhds hx] with y hy
    simp [hKz y hy]
  rw [hev.fderiv_eq]
  simp

/-- Separation: a compact set avoiding the collision set has a uniformly positive pair distance. -/
theorem p4m_sep {K : Set (EucConfig d N)} (hK : IsCompact K) (hKd : Disjoint K (eucCollisionSet d N)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ i j, i ≠ j → δ ≤ ‖x i - x j‖ := by
  have hp : ∀ p : Fin N × Fin N, ∃ c : ℝ, 0 < c ∧ (p.1 ≠ p.2 → ∀ x ∈ K, c ≤ ‖x p.1 - x p.2‖) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => absurd hp h⟩
    · obtain ⟨c, hc0, hc⟩ := hK.exists_forall_le' (f := fun x : EucConfig d N => ‖x p.1 - x p.2‖)
        (a := 0) (by fun_prop) (fun x hx => by
          refine norm_pos_iff.2 (sub_ne_zero.2 fun h => ?_)
          exact Set.disjoint_left.1 hKd hx ⟨p.1, p.2, hp, h⟩)
      exact ⟨c, hc0, fun _ x hx => hc x hx⟩
  choose c hc0 hc using hp
  have hsum0 : 0 ≤ ∑ p, 1 / c p := Finset.sum_nonneg fun p _ => (one_div_pos.2 (hc0 p)).le
  refine ⟨1 / (1 + ∑ p, 1 / c p), by positivity, fun x hx i j hij => ?_⟩
  have h1 : 1 / c (i, j) ≤ 1 + ∑ p, 1 / c p := by
    have := Finset.single_le_sum (f := fun p => 1 / c p) (fun p _ => (one_div_pos.2 (hc0 p)).le)
      (Finset.mem_univ (i, j))
    linarith
  calc 1 / (1 + ∑ p, 1 / c p) ≤ 1 / (1 / c (i, j)) :=
        one_div_le_one_div_of_le (one_div_pos.2 (hc0 _)) h1
    _ = c (i, j) := by rw [one_div_one_div]
    _ ≤ ‖x i - x j‖ := hc (i, j) hij x hx

theorem p4m_exists_M0 {K : Set (EucConfig d N)} (hK : IsCompact K)
    (hKd : Disjoint K (eucCollisionSet d N)) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → ∀ x ∈ K, ∀ᶠ y in 𝓝 x,
      ∀ i j, i ≠ j → 1 / ((M : ℝ) + 1) ≤ ‖y i - y j‖ := by
  obtain ⟨δ, hδ, hsep⟩ := p4m_sep hK hKd
  obtain ⟨M0, hM0⟩ := exists_nat_one_div_lt (show 0 < δ / 2 by positivity)
  refine ⟨M0, fun M hM x hx => ?_⟩
  have hMM : 1 / ((M : ℝ) + 1) ≤ δ / 2 := by
    refine le_trans ?_ hM0.le
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hM 1)
  filter_upwards [Metric.ball_mem_nhds x (show 0 < δ / 4 by positivity)] with y hy i j hij
  have hxy : dist y x < δ / 4 := hy
  have h1 : dist (y i) (x i) ≤ dist y x := dist_le_pi_dist y x i
  have h2 : dist (y j) (x j) ≤ dist y x := dist_le_pi_dist y x j
  have h3 := hsep x hx i j hij
  have h4 : dist (x i) (x j) ≤ dist (x i) (y i) + dist (y i) (y j) + dist (y j) (x j) :=
    dist_triangle4 _ _ _ _
  rw [dist_eq_norm] at h4
  rw [dist_comm (x i) (y i)] at h4
  have h5 : dist (y i) (y j) = ‖y i - y j‖ := dist_eq_norm _ _
  linarith

theorem p4m_weight_eq_of_far {s : ℝ} {invβ τ : ℝ} {gM : ℕ → Euc d → ℝ}
    (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M)) (M : ℕ) (y : EucConfig d N)
    (hy : ∀ i j, i ≠ j → 1 / ((M : ℝ) + 1) ≤ ‖y i - y j‖) :
    p4GibbsOf invβ (p4Pot (gM M) s N τ) y = selfSimWeight d s invβ N τ y := by
  classical
  have hnc : y ∉ eucCollisionSet d N := by
    rintro ⟨i, j, hij, h⟩
    have := hy i j hij
    rw [h, sub_self, norm_zero] at this
    have : (0 : ℝ) < 1 / ((M : ℝ) + 1) := by positivity
    linarith
  simp only [selfSimWeight, p4GibbsOf, if_neg hnc]
  rw [p4m_pot_eq (hgM M) τ y hy]

theorem p4m_fi_eq {s : ℝ} {invβ τ : ℝ} {gM : ℕ → Euc d → ℝ}
    (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M)) {M : ℕ}
    {ζ : EucConfig d N → EucConfig d N} {K : Set (EucConfig d N)} (hKz : ∀ x, x ∉ K → ζ x = 0)
    (hM : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, ∀ i j, i ≠ j → 1 / ((M : ℝ) + 1) ≤ ‖y i - y j‖) (x : EucConfig d N) :
    p4m_fi (p4GibbsOf invβ (p4Pot (gM M) s N τ)) ζ x = p4m_fi (selfSimWeight d s invβ N τ) ζ x := by
  unfold p4m_fi
  by_cases hx : x ∈ K
  · have hev : (fun Z : EucConfig d N => Real.log (p4GibbsOf invβ (p4Pot (gM M) s N τ) Z)) =ᶠ[𝓝 x]
        fun Z => Real.log (selfSimWeight d s invβ N τ Z) := by
      filter_upwards [hM x hx] with y hy
      rw [p4m_weight_eq_of_far hgM M y hy]
    rw [hev.fderiv_eq]
  · rw [hKz x hx]
    simp

/-- **Fisher** part of `p4_lsc_M`. -/
theorem p4lm_fisher_lsc {s : ℝ} {invβ : ℝ} (τ : ℝ)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M))
    {μ : Measure (EucConfig d N)} {μM : ℕ → Measure (EucConfig d N)}
    [IsProbabilityMeasure μ] [∀ M, IsProbabilityMeasure (μM M)]
    (htv : ∀ A : Set (EucConfig d N), MeasurableSet A →
      Tendsto (fun M => μM M A) atTop (𝓝 (μ A))) :
    fisherInfoW (selfSimWeight d s invβ N τ) μ ≤
      liminf (fun M => fisherInfoW (p4GibbsOf invβ (p4Pot (gM M) s N τ)) (μM M)) atTop := by
  rw [p4m_fisher_eq]
  refine iSup₂_le fun ζ hζ => ?_
  obtain ⟨K, hK, hKd, hKz⟩ := hζ.support
  obtain ⟨M0, hM0⟩ := p4m_exists_M0 hK hKd
  have heq : ∀ M, M0 ≤ M → ∀ x, p4m_fi (p4GibbsOf invβ (p4Pot (gM M) s N τ)) ζ x =
      p4m_fi (selfSimWeight d s invβ N τ) ζ x := fun M hM =>
    p4m_fi_eq hgM hKz (hM0 M hM)
  have hζc : Continuous ζ := hζ.smooth.continuous
  -- the common integrand is continuous with compact support
  have hcont : Continuous (p4m_fi (selfSimWeight d s invβ N τ) ζ) := by
    have : p4m_fi (selfSimWeight d s invβ N τ) ζ =
        p4m_fi (p4GibbsOf invβ (p4Pot (gM M0) s N τ)) ζ := funext fun x => (heq M0 le_rfl x).symm
    rw [this]
    unfold p4m_fi
    refine Continuous.sub (Continuous.sub ?_ ?_) ?_
    · exact continuous_const.mul (p4m_div_cont hζ.smooth)
    · exact continuous_const.mul (p4m_dlog_cont (hgM M0) invβ τ hζc)
    · exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hζc).norm.pow 2
  have hzero : ∀ x, x ∉ K → p4m_fi (selfSimWeight d s invβ N τ) ζ x = 0 := by
    intro x hx
    unfold p4m_fi
    rw [hKz x hx, p4m_div_zero hK.isClosed hKz hx]
    simp
  have hcs : HasCompactSupport (p4m_fi (selfSimWeight d s invβ N τ) ζ) :=
    HasCompactSupport.intro hK hzero
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  have hlim := p4m_setwise_integral htv hcont.measurable (C := C) (fun x => by
    simpa [Real.norm_eq_abs] using hC x)
  have hlim' := ENNReal.tendsto_ofReal hlim
  rw [← hlim'.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [Filter.eventually_ge_atTop M0] with M hM
  rw [p4m_fisher_eq]
  refine le_iSup₂_of_le ζ hζ ?_
  have : (fun x => p4m_fi (p4GibbsOf invβ (p4Pot (gM M) s N τ)) ζ x) =
      fun x => p4m_fi (selfSimWeight d s invβ N τ) ζ x := funext (heq M hM)
  rw [this]

/-- **(9)** `M → ∞` at a fixed time: lower semicontinuity of the entropy and of the Fisher information with the
moving references. -/
theorem p4_lsc_M_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ) (invβ : ℝ) (hβ : 0 < invβ) (τ : ℝ)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M))
    {μ : Measure (EucConfig d N)} {μM : ℕ → Measure (EucConfig d N)}
    [IsProbabilityMeasure μ] [∀ M, IsProbabilityMeasure (μM M)]
    (htv : ∀ A : Set (EucConfig d N), MeasurableSet A → Tendsto (fun M => μM M A) atTop (𝓝 (μ A))) :
    gibbsEntropyW (selfSimWeight d s invβ N τ) μ ≤
        liminf (fun M => gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N τ)) (μM M)) atTop ∧
      fisherInfoW (selfSimWeight d s invβ N τ) μ ≤
        liminf (fun M => fisherInfoW (p4GibbsOf invβ (p4Pot (gM M) s N τ)) (μM M)) atTop :=
  ⟨p4lm_entropy_lsc hd hs0 hβ τ hgM htv, p4lm_fisher_lsc τ hgM htv⟩

example := (@p4_lsc_M_proof : type_of% @HRS.MP.SelfSimP4.p4_lsc_M)

end HRS.MP.SelfSimP4Impl
