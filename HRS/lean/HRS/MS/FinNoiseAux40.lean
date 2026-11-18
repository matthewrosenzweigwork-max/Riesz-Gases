import HRS.MS.FinNoiseAux39

/-!
# S8.6 `finite_noise`: the pointwise symmetric-root bound through the chart reconstruction (S86b)

`s86_pointwise`: for the global forms `Sf = κ ∑_a ∫ Γ_a⊗Γ_a dν` (empirical `ν`, mass `≤ 1`) and `Df = κ ∑_a ∫ Γ_a⊗Γ_a dμ`
(reference probability `μ`), any symmetric nonnegative roots `S₀, Sb₀` satisfy
`∑_k ‖(S₀ - Sb₀) e_k‖² ≤ 2 ∑_{(j,a)} ‖R_{ja}‖² · (4κ/lo_j) · 𝒬(𝒞_j(ν) - 𝒞_j(μ))`
(`ℝ≥0∞`; `𝒬` the relative quadratic form of the chart covariances), whenever the localised features are reconstructed by the
operators `R_{ja}` on charts with partition of unity `χ_j` and `μ`-chart densities `≥ lo_j`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS HRS.Uniform HRS.Uniform.ChartAux

variable {d : ℕ}

theorem s86_tsum_prod_fin {J : Type*} (g : J × Fin d → ℝ) (hg : Summable g) :
    ∑' p : J × Fin d, g p = ∑ a : Fin d, ∑' j : J, g (j, a) := by
  have hswap : Summable fun q : Fin d × J => g q.swap :=
    (Equiv.prodComm (Fin d) J).summable_iff.2 hg
  calc ∑' p : J × Fin d, g p = ∑' q : Fin d × J, g q.swap :=
        ((Equiv.prodComm (Fin d) J).tsum_eq g).symm
    _ = ∑' a : Fin d, ∑' j : J, g (j, a) := hswap.tsum_prod' (fun a => hswap.prod_factor a)
    _ = ∑ a : Fin d, ∑' j : J, g (j, a) := tsum_fintype _

set_option maxHeartbeats 1600000 in
theorem s86_pointwise (r : ℕ) (hr : d < r) {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] {ιK : Type*} [Countable ιK] (e : HilbertBasis ιK ℝ K)
    {J : Type*} [Countable J] (U : J → Set (Euc d)) (hU : ∀ j, MeasurableSet (U j))
    (ψ : J → Euc d → Torus d) (hψ : ∀ j, Measurable (ψ j)) (χ : J → Euc d → ℝ)
    (hχm : ∀ j, Measurable (χ j)) (hχ1 : ∀ x, HasSum (fun j => χ j x ^ 2) 1)
    (κ : ℝ) (hκ : 0 < κ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (ν : Measure (Euc d))
    [IsFiniteMeasure ν] (hν : ν Set.univ ≤ 1)
    (Γ : Fin d → Euc d → K) (hΓm : ∀ a, Measurable (Γ a)) (B : ℝ) (hΓb : ∀ a x, ‖Γ a x‖ ≤ B)
    (R : J → Fin d → FeatureSpace d →L[ℝ] K)
    (hR : ∀ j a x, χ j x • Γ a x = (U j).indicator
      (fun x => R j a (chartFeature (d := d) r (ψ j x))) x)
    (hRs : Summable fun p : J × Fin d => ‖R p.1 p.2‖ ^ 2)
    (lo : J → ℝ) (hlo0 : ∀ j, 0 < lo j)
    (hlo : ∀ j, ENNReal.ofReal (lo j) • (volume : Measure (Torus d)) ≤ (μ.restrict (U j)).map (ψ j))
    (S0 Sb0 : K →L[ℝ] K) (Sf Df : K →L[ℝ] K →L[ℝ] ℝ)
    (hSf : ∀ x y, Sf x y = κ * ∑ a, ∫ z, ⟪Γ a z, x⟫ * ⟪Γ a z, y⟫ ∂ν)
    (hDf : ∀ x y, Df x y = κ * ∑ a, ∫ z, ⟪Γ a z, x⟫ * ⟪Γ a z, y⟫ ∂μ)
    (hS0 : IsSqrtOfForm S0 Sf) (hSb0 : IsSqrtOfForm Sb0 Df) :
    ∑' k, ENNReal.ofReal (‖(S0 - Sb0) (e k)‖ ^ 2) ≤
      2 * ∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) *
        (ENNReal.ofReal (4 * κ / lo p.1) * relQuad (hb d) (chartWeight r)
          (outerCov (chartFeature (d := d) r) ((ν.restrict (U p.1)).map (ψ p.1)) -
            outerCov (chartFeature (d := d) r) ((μ.restrict (U p.1)).map (ψ p.1)))) := by
  classical
  letI : MeasurableSpace (FeatureSpace d) := borel _
  haveI : BorelSpace (FeatureSpace d) := ⟨rfl⟩
  haveI := secondCountable_featureSpace d
  have hbc := continuous_chartFeature (d := d) r hr
  have hM : ∀ u, ‖chartFeature (d := d) r u‖ ^ 2 ≤ 2 * ∑' k : Lattice d, chartWeight r k :=
    fun u => norm_sq_chartFeature_le r hr u
  set W : ℝ := 2 * ∑' k : Lattice d, chartWeight r k with hWdef
  have hW0 : 0 ≤ W := by
    have : 0 ≤ ∑' k : Lattice d, chartWeight r k := tsum_nonneg fun k => (chartWeight_pos r k).le
    simp only [hWdef]; linarith
  set νc : J → Measure (Torus d) := fun j => (ν.restrict (U j)).map (ψ j) with hνc
  set μc : J → Measure (Torus d) := fun j => (μ.restrict (U j)).map (ψ j) with hμc
  have hmass : ∀ (m : Measure (Euc d)) (hm : m Set.univ ≤ 1) (j : J),
      ((m.restrict (U j)).map (ψ j)) Set.univ ≤ 1 := by
    intro m hm j
    rw [Measure.map_apply (hψ j) MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
    exact (measure_mono (Set.subset_univ _)).trans hm
  have hmassR : ∀ (m : Measure (Euc d)) (hm : m Set.univ ≤ 1) (j : J),
      (((m.restrict (U j)).map (ψ j)) Set.univ).toReal ≤ 1 := by
    intro m hm j
    have := hmass m hm j
    calc (((m.restrict (U j)).map (ψ j)) Set.univ).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top this
      _ = 1 := by simp
  have hμ1 : μ Set.univ ≤ 1 := by simp
  haveI : ∀ j, IsFiniteMeasure (νc j) := fun j => inferInstance
  haveI : ∀ j, IsFiniteMeasure (μc j) := fun j => inferInstance
  set C : J → FeatureSpace d →L[ℝ] FeatureSpace d →L[ℝ] ℝ :=
    fun j => κ • outerCov (chartFeature (d := d) r) (νc j) with hC
  set D : J → FeatureSpace d →L[ℝ] FeatureSpace d →L[ℝ] ℝ :=
    fun j => κ • outerCov (chartFeature (d := d) r) (μc j) with hD
  have hCt : ∀ j, IsTraceClassCov (C j) := fun j =>
    isTraceClassCov_smul (isTraceClassCov_outerCov hbc hM (νc j)) hκ.le
  have hDt : ∀ j, IsTraceClassCov (D j) := fun j =>
    isTraceClassCov_smul (isTraceClassCov_outerCov hbc hM (μc j)) hκ.le
  set Sj : J → FeatureSpace d →L[ℝ] FeatureSpace d := fun j => formSqrt (C j) with hSj
  set Sbj : J → FeatureSpace d →L[ℝ] FeatureSpace d := fun j => formSqrt (D j) with hSbj
  have hSjs : ∀ j, IsSqrtOfForm (Sj j) (C j) := fun j => RelCov.formSqrt_spec (hCt j)
  have hSbjs : ∀ j, IsSqrtOfForm (Sbj j) (D j) := fun j => RelCov.formSqrt_spec (hDt j)
  -- bounds
  have hCΛ : ∀ j x, C j x x ≤ (κ * W) * ‖x‖ ^ 2 := by
    intro j x
    have h := s86_outerCov_abs_le r hr (νc j) x x
    have h2 : outerCov (chartFeature (d := d) r) (νc j) x x ≤ W * ‖x‖ ^ 2 := by
      calc _ ≤ |outerCov (chartFeature (d := d) r) (νc j) x x| := le_abs_self _
        _ ≤ W * ((νc j) Set.univ).toReal * (‖x‖ * ‖x‖) := h
        _ ≤ W * 1 * (‖x‖ * ‖x‖) := by
            gcongr
            exact hmassR ν hν j
        _ = W * ‖x‖ ^ 2 := by ring
    simp only [hC, ContinuousLinearMap.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h2 hκ.le]
  have hDΛ : ∀ j x, D j x x ≤ (κ * W) * ‖x‖ ^ 2 := by
    intro j x
    have h := s86_outerCov_abs_le r hr (μc j) x x
    have h2 : outerCov (chartFeature (d := d) r) (μc j) x x ≤ W * ‖x‖ ^ 2 := by
      calc _ ≤ |outerCov (chartFeature (d := d) r) (μc j) x x| := le_abs_self _
        _ ≤ W * ((μc j) Set.univ).toReal * (‖x‖ * ‖x‖) := h
        _ ≤ W * 1 * (‖x‖ * ‖x‖) := by
            gcongr
            exact hmassR μ hμ1 j
        _ = W * ‖x‖ ^ 2 := by ring
    simp only [hD, ContinuousLinearMap.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h2 hκ.le]
  have hHS : ∀ (j : J) (m : Measure (Euc d)) (hm : m Set.univ ≤ 1) (T : FeatureSpace d →L[ℝ] FeatureSpace d)
      (Cf : FeatureSpace d →L[ℝ] FeatureSpace d →L[ℝ] ℝ),
      IsSqrtOfForm T Cf → Cf = κ • outerCov (chartFeature (d := d) r) ((m.restrict (U j)).map (ψ j)) →
      Summable (fun i => ‖T (hb d i)‖ ^ 2) ∧ ∑' i, ‖T (hb d i)‖ ^ 2 ≤ κ * W := by
    intro j m hm T Cf hT hCf
    haveI : IsFiniteMeasure ((m.restrict (U j)).map (ψ j)) :=
      ⟨by have := hmass m hm j; exact lt_of_le_of_lt this ENNReal.one_lt_top⟩
    obtain ⟨hs, hle⟩ := s86_trace_outerCov r hr ((m.restrict (U j)).map (ψ j))
    have e1 : ∀ i, ‖T (hb d i)‖ ^ 2 = κ * outerCov (chartFeature (d := d) r)
        ((m.restrict (U j)).map (ψ j)) (hb d i) (hb d i) := by
      intro i
      rw [s86_sqrt_sq_diag hT, hCf]
      simp
    simp_rw [e1]
    refine ⟨hs.mul_left κ, ?_⟩
    rw [tsum_mul_left]
    have := hmassR m hm j
    calc κ * ∑' i, outerCov (chartFeature (d := d) r) ((m.restrict (U j)).map (ψ j)) (hb d i) (hb d i)
        ≤ κ * (W * (((m.restrict (U j)).map (ψ j)) Set.univ).toReal) :=
          mul_le_mul_of_nonneg_left hle hκ.le
      _ ≤ κ * (W * 1) := by gcongr
      _ = κ * W := by ring
  -- the global form identities
  have hnormS : ∀ j x, ‖Sj j x‖ ^ 2 ≤ (κ * W) * ‖x‖ ^ 2 := fun j x => by
    rw [s86_sqrt_sq_diag (hSjs j)]; exact hCΛ j x
  have hnormSb : ∀ j x, ‖Sbj j x‖ ^ 2 ≤ (κ * W) * ‖x‖ ^ 2 := fun j x => by
    rw [s86_sqrt_sq_diag (hSbjs j)]; exact hDΛ j x
  have hCabs : ∀ (j : J) (m : Measure (Euc d)) (hm : m Set.univ ≤ 1) (z w : FeatureSpace d),
      |outerCov (chartFeature (d := d) r) ((m.restrict (U j)).map (ψ j)) z w| ≤ W * (‖z‖ * ‖w‖) := by
    intro j m hm z w
    haveI : IsFiniteMeasure ((m.restrict (U j)).map (ψ j)) :=
      ⟨by have := hmass m hm j; exact lt_of_le_of_lt this ENNReal.one_lt_top⟩
    have h := s86_outerCov_abs_le r hr ((m.restrict (U j)).map (ψ j)) z w
    refine h.trans ?_
    have := hmassR m hm j
    calc W * (((m.restrict (U j)).map (ψ j)) Set.univ).toReal * (‖z‖ * ‖w‖)
        ≤ W * 1 * (‖z‖ * ‖w‖) := by gcongr
      _ = W * (‖z‖ * ‖w‖) := by ring
  have hglobal : ∀ (m : Measure (Euc d)) [IsFiniteMeasure m] (hm : m Set.univ ≤ 1)
      (Cf : K →L[ℝ] K →L[ℝ] ℝ),
      (∀ x y, Cf x y = κ * ∑ a, ∫ z, ⟪Γ a z, x⟫ * ⟪Γ a z, y⟫ ∂m) →
      ∀ x y, Cf x y = ∑' p : J × Fin d, (κ • outerCov (chartFeature (d := d) r)
        ((m.restrict (U p.1)).map (ψ p.1))) (ContinuousLinearMap.adjoint (R p.1 p.2) x)
          (ContinuousLinearMap.adjoint (R p.1 p.2) y) := by
    intro m _ hm Cf hCf x y
    rw [hCf]
    have hform : ∀ a, ∫ z, ⟪Γ a z, x⟫ * ⟪Γ a z, y⟫ ∂m = ∑' j, outerCov (chartFeature (d := d) r)
        ((m.restrict (U j)).map (ψ j)) (ContinuousLinearMap.adjoint (R j a) x)
        (ContinuousLinearMap.adjoint (R j a) y) := fun a =>
      s86_form_chart r hr m U hU ψ hψ χ hχm hχ1 (Γ a) (hΓm a) B (hΓb a) (fun j => R j a)
        (fun j x => hR j a x) x y
    simp_rw [hform]
    have hsumm : Summable fun p : J × Fin d => outerCov (chartFeature (d := d) r)
        ((m.restrict (U p.1)).map (ψ p.1)) (ContinuousLinearMap.adjoint (R p.1 p.2) x)
        (ContinuousLinearMap.adjoint (R p.1 p.2) y) := by
      refine Summable.of_norm_bounded ((hRs.mul_left (W * (‖x‖ * ‖y‖)))) fun p => ?_
      rw [Real.norm_eq_abs]
      refine (hCabs p.1 m hm _ _).trans ?_
      have h1 : ‖ContinuousLinearMap.adjoint (R p.1 p.2) x‖ ≤ ‖R p.1 p.2‖ * ‖x‖ := by
        have := (ContinuousLinearMap.adjoint (R p.1 p.2)).le_opNorm x
        rwa [ContinuousLinearMap.adjoint.norm_map] at this
      have h2 : ‖ContinuousLinearMap.adjoint (R p.1 p.2) y‖ ≤ ‖R p.1 p.2‖ * ‖y‖ := by
        have := (ContinuousLinearMap.adjoint (R p.1 p.2)).le_opNorm y
        rwa [ContinuousLinearMap.adjoint.norm_map] at this
      calc W * (‖ContinuousLinearMap.adjoint (R p.1 p.2) x‖ * ‖ContinuousLinearMap.adjoint (R p.1 p.2) y‖)
          ≤ W * ((‖R p.1 p.2‖ * ‖x‖) * (‖R p.1 p.2‖ * ‖y‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) hW0
        _ = W * (‖x‖ * ‖y‖) * ‖R p.1 p.2‖ ^ 2 := by ring
    have hsumm' : Summable fun p : J × Fin d => (κ • outerCov (chartFeature (d := d) r)
        ((m.restrict (U p.1)).map (ψ p.1))) (ContinuousLinearMap.adjoint (R p.1 p.2) x)
          (ContinuousLinearMap.adjoint (R p.1 p.2) y) := by
      simpa [ContinuousLinearMap.smul_apply] using hsumm.mul_left κ
    rw [s86_tsum_prod_fin _ hsumm', Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp [ContinuousLinearMap.smul_apply]
  -- apply the deterministic root comparison
  have hSM := hglobal ν hν Sf hSf
  have hSbM := hglobal μ hμ1 Df hDf
  have hSM' : ∀ x y, inner ℝ (S0 x) (S0 y) = ∑' p : J × Fin d, C p.1
      (ContinuousLinearMap.adjoint (R p.1 p.2) x) (ContinuousLinearMap.adjoint (R p.1 p.2) y) :=
    fun x y => (hS0.sq x y).trans (hSM x y)
  have hSbM' : ∀ x y, inner ℝ (Sb0 x) (Sb0 y) = ∑' p : J × Fin d, D p.1
      (ContinuousLinearMap.adjoint (R p.1 p.2) x) (ContinuousLinearMap.adjoint (R p.1 p.2) y) :=
    fun x y => (hSb0.sq x y).trans (hSbM x y)
  obtain ⟨hsum, hcc, hbd⟩ := s86_det_root e (hb d) (fun p : J × Fin d => R p.1 p.2)
    (fun p => C p.1) (fun p => D p.1) (fun p => Sj p.1) (fun p => Sbj p.1)
    (fun p => hSjs p.1) (fun p => hSbjs p.1) (κ * W) (κ * W) (by positivity) (by positivity)
    (fun p x => hCΛ p.1 x) (fun p x => hDΛ p.1 x) hRs
    (fun p => hHS p.1 ν hν (Sj p.1) (C p.1) (hSjs p.1) rfl)
    (fun p => hHS p.1 μ hμ1 (Sbj p.1) (D p.1) (hSbjs p.1) rfl)
    S0 Sb0 hS0.symm hS0.nonneg hSb0.symm hSb0.nonneg hSM' hSbM'
  -- back to ℝ≥0∞
  set h : J × Fin d → ℝ := fun p => ∑' i, ‖(Sj p.1 - Sbj p.1) (hb d i)‖ ^ 2 with hh
  have hh0 : ∀ p, 0 ≤ h p := fun p => tsum_nonneg fun i => sq_nonneg _
  have hofh : ∀ p, ENNReal.ofReal (h p) ≤ ∑' i, ENNReal.ofReal (‖(Sj p.1 - Sbj p.1) (hb d i)‖ ^ 2) := by
    intro p
    by_cases hs : Summable fun i => ‖(Sj p.1 - Sbj p.1) (hb d i)‖ ^ 2
    · exact le_of_eq (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs)
    · simp only [hh]
      rw [tsum_eq_zero_of_not_summable hs]
      simp
  have hpt : ∀ p : J × Fin d, ∑' i, ENNReal.ofReal (‖(Sj p.1 - Sbj p.1) (hb d i)‖ ^ 2) ≤
      ENNReal.ofReal (4 * κ / lo p.1) * relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r) (νc p.1) - outerCov (chartFeature (d := d) r) (μc p.1)) :=
    fun p => s86_chart_pt r hr (lo p.1) (hlo0 p.1) (μc p.1) (νc p.1) (hlo p.1) κ hκ (Sj p.1) (Sbj p.1)
      (hSjs p.1) (hSbjs p.1)
  calc ∑' k, ENNReal.ofReal (‖(S0 - Sb0) (e k)‖ ^ 2)
      = ENNReal.ofReal (∑' k, ‖(S0 - Sb0) (e k)‖ ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsum).symm
    _ ≤ ENNReal.ofReal (2 * ∑' p : J × Fin d, ‖R p.1 p.2‖ ^ 2 * h p) := ENNReal.ofReal_le_ofReal hbd
    _ = 2 * ∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) * ENNReal.ofReal (h p) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_tsum_of_nonneg
          (fun p => mul_nonneg (sq_nonneg _) (hh0 p)) hcc]
        simp only [ENNReal.ofReal_ofNat]
        congr 1
        refine tsum_congr fun p => ?_
        exact ENNReal.ofReal_mul (sq_nonneg _)
    _ ≤ 2 * ∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) *
        (ENNReal.ofReal (4 * κ / lo p.1) * relQuad (hb d) (chartWeight r)
          (outerCov (chartFeature (d := d) r) (νc p.1) - outerCov (chartFeature (d := d) r) (μc p.1))) := by
        gcongr with p
        exact (hofh p).trans (hpt p)

end HRS.MS.FinNoise
