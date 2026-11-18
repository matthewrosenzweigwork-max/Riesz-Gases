import HRS.MS.R26T8AV13a

/-!
# S8.2 observed-time layer, packet T8A.V13: maximal inequality for the centered process along a stationary path, closure form

For `F` in the generator closure (`GeneratorClosure a beta F LF`) and `C²` off collisions, the bound of V12 persists:
`E sup_{t ≤ T} |F(X_{u+t}) - ∫F|² ≤ 100 (Var F + (T/β) E|∇F|²)`.
Proof: take the cutoff sequence `Fn` of the closure; centered `Fn - ∫Fn → F - ∫F` in `L²(canonicalP)`; a subsequence
converges a.e., hence (stationarity of `X`) simultaneously at countably many times along the path a.s.; the supremum over
`[0,T]` equals the supremum over a countable dense set (path continuous, no collisions, `F` continuous off collisions);
Fatou's lemma and V12 for `Fn`, together with convergence of the energies, give the bound.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_reversible_corrector_maximal (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N) (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (hrev : r26t8a_ReversibleWindows P X)
    (F LF : EucConfig d N → ℝ) (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ)
    (hdom : GeneratorClosure a beta F LF) (u T : ℝ) (hu : 0 ≤ u) (hT : 0 < T) :
    let Y := fun t w => centerUnder (canonicalP d N a beta) F (X (u + t).toNNReal w)
    AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) P ∧
      r26t8a_scalarSupSq P T Y ≤ 100 * (evariance F (canonicalP d N a beta) +
        ENNReal.ofReal (T / beta) * ∫⁻ x, ∑ i,
          ‖HRS.MS.Phase2S82.configGrad F x i‖ₑ ^ 2 ∂canonicalP d N a beta) := by
  intro Y
  classical
  haveI hP0 : IsProbabilityMeasure (canonicalP d N a beta) :=
    HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  obtain ⟨hF2, -, hgr, Fn, hFn, hT1, -, hT3⟩ := hdom
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t => (hX.solution (t : ℝ)).adapted t
  have hlaw : ∀ q ∈ Set.Icc (0 : ℝ) T,
      P.map (X (u + q).toNNReal) = canonicalP d N a beta := fun q hq => by
    have := hX.invariant P (u + T) X0 W X hX.brownian hX.indep hX.init (hX.solution (u + T))
      (u + q).toNNReal (by rw [Real.coe_toNNReal _ (by linarith [hq.1])]; linarith [hq.2])
    exact this
  have hFnc : ∀ n, Continuous (Fn n) := fun n => (hFn n).1.continuous
  have hFnint : ∀ n, Integrable (Fn n) (canonicalP d N a beta) := fun n =>
    (hFnc n).integrable_of_hasCompactSupport (hFn n).2.1
  have hFint : Integrable F (canonicalP d N a beta) := hF2.integrable one_le_two
  have hFam : AEStronglyMeasurable F (canonicalP d N a beta) := hF2.aestronglyMeasurable
  set c : ℝ := ∫ y, F y ∂canonicalP d N a beta with hc
  have hdelta : Tendsto (fun n => eLpNorm (fun x => Fn n x - F x) 2 (canonicalP d N a beta))
      atTop (𝓝 0) :=
    r26t8a_v13a_L2_tendsto (fun n => (hFnc n).aestronglyMeasurable.sub hFam) hT1.2
  have heta : Tendsto (fun n => eLpNorm (fun x => (Fn n x - ∫ y, Fn n y ∂canonicalP d N a beta) -
      (F x - c)) 2 (canonicalP d N a beta)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using ENNReal.Tendsto.const_mul hdelta (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ⊤)))
      (fun _ => zero_le) (fun n => r26t8a_v13a_center_bound _ (hFnint n) hFint)
  have hinm : TendstoInMeasure (canonicalP d N a beta)
      (fun n x => Fn n x - ∫ y, Fn n y ∂canonicalP d N a beta) atTop (fun x => F x - c) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) heta
  obtain ⟨ns, hns, hae⟩ := hinm.exists_seq_tendsto_ae
  obtain ⟨D, hDc, hDs, hDd⟩ := TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ) T)
  have hGm : AEMeasurable (fun x => F x - c) (canonicalP d N a beta) :=
    (hFam.sub aestronglyMeasurable_const).aemeasurable
  have hYae : ∀ q ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Y q) P := fun q hq => by
    have : AEMeasurable (fun x => F x - c) (P.map (X (u + q).toNNReal)) := by
      rw [hlaw q hq]; exact hGm
    exact this.comp_aemeasurable (hXm _).aemeasurable
  have hcont : ∀ᵐ w ∂P, ContinuousOn (fun t : ℝ => Y t w) (Set.Icc 0 T) := by
    filter_upwards [(hX.solution (u + T)).cont, (hX.solution (u + T)).no_collision] with w hw hnc
    have hpath : Continuous fun t : ℝ => X (u + t).toNNReal w :=
      (continuous_pi hw).comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))
    have hmaps : MapsTo (fun t : ℝ => X (u + t).toNNReal w) (Set.Icc 0 T)
        (eucCollisionSet d N)ᶜ := fun t ht => by
      show X (u + t).toNNReal w ∉ eucCollisionSet d N
      refine hnc _ ?_
      rw [Real.coe_toNNReal _ (by linarith [ht.1])]; linarith [ht.2]
    exact ((hF.continuousOn).comp hpath.continuousOn hmaps).sub continuousOn_const
  have hYsup : ∀ᵐ w ∂P, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) = ⨆ q ∈ D, ‖Y q w‖ₑ := by
    filter_upwards [hcont] with w hw
    rw [← r26t8a_v13a_sup_dense hw hDs hDd]
    exact (iSup_subtype' (p := fun t => t ∈ Set.Icc (0 : ℝ) T) (f := fun t _ => ‖Y t w‖ₑ)).symm
  have hAm : AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) P :=
    (AEMeasurable.biSup D hDc fun q hq => (hYae q (hDs hq)).enorm).congr
      (hYsup.mono fun w h => h.symm)
  refine ⟨hAm, ?_⟩
  -- pointwise a.e. convergence along the subsequence at the countably many times of `D`
  have hconv : ∀ᵐ w ∂P, ∀ q ∈ D, Tendsto (fun k => Fn (ns k) (X (u + q).toNNReal w) -
      ∫ y, Fn (ns k) y ∂canonicalP d N a beta) atTop (𝓝 (F (X (u + q).toNNReal w) - c)) := by
    rw [ae_ball_iff hDc]
    intro q hq
    exact ae_of_ae_map (hXm _).aemeasurable
      (p := fun x => Tendsto (fun k => Fn (ns k) x - ∫ y, Fn (ns k) y ∂canonicalP d N a beta)
        atTop (𝓝 (F x - c)))
      (by rw [hlaw q (hDs hq)]; exact hae)
  -- V12 for each cutoff function
  set S : ℕ → Omega → ℝ≥0∞ := fun n w => ⨆ t : Set.Icc (0 : ℝ) T,
    ‖centerUnder (canonicalP d N a beta) (Fn n) (X (u + t).toNNReal w)‖ₑ with hS
  have hV12 : ∀ n, AEMeasurable (S n) P ∧ ∫⁻ w, (S n w) ^ 2 ∂P ≤
      100 * (evariance (Fn n) (canonicalP d N a beta) + ENNReal.ofReal (T / beta) *
        ∫⁻ x, ∑ i, ‖HRS.MS.Phase2S82.configGrad (Fn n) x i‖ₑ ^ 2 ∂canonicalP d N a beta) := fun n => by
    have := r26t8a_compact_corrector_maximal d N hd hN a beta ha hbeta P X0 W X hX hrev (Fn n)
      (hFn n).1 (hFn n).2.1 (hFn n).2.2 u T hu hT
    exact this
  -- the upper bounds
  set ν : ℝ≥0∞ := eLpNorm (fun x => F x - c) 2 (canonicalP d N a beta) with hν
  set τ : ℝ≥0∞ := ENNReal.ofReal (T / beta) with hτ
  set η : ℕ → ℝ≥0∞ := fun n => eLpNorm (fun x => (Fn n x -
    ∫ y, Fn n y ∂canonicalP d N a beta) - (F x - c)) 2 (canonicalP d N a beta) with hη
  set γ : Fin N → ℝ≥0∞ := fun i => eLpNorm (fun x => HRS.MS.Phase2S82.configGrad F x i) 2
    (canonicalP d N a beta) with hγ
  set ε : Fin N → ℕ → ℝ≥0∞ := fun i n => eLpNorm (fun x => HRS.MS.Phase2S82.configGrad (Fn n) x i -
    HRS.MS.Phase2S82.configGrad F x i) 2 (canonicalP d N a beta) with hε
  have hgm : ∀ n i, Measurable fun x => HRS.MS.Phase2S82.configGrad (Fn n) x i := fun n i =>
    (r26t8a_v10a_cont (Fn n) ((hFn n).1.of_le (by simp)) i).measurable
  have hVar : evariance F (canonicalP d N a beta) = ν ^ 2 :=
    lintegral_enorm_sq_eq_eLpNorm_sq (hFam.sub aestronglyMeasurable_const)
  have hE : ∫⁻ x, ∑ i, ‖HRS.MS.Phase2S82.configGrad F x i‖ₑ ^ 2 ∂canonicalP d N a beta =
      ∑ i, γ i ^ 2 := by
    rw [lintegral_finset_sum' Finset.univ
      (fun i _ => ((hgr i).aestronglyMeasurable.enorm).pow_const 2)]
    exact Finset.sum_congr rfl fun i _ => lintegral_enorm_sq_eq_eLpNorm_sq (hgr i).aestronglyMeasurable
  have hVn : ∀ n, evariance (Fn n) (canonicalP d N a beta) ≤ (ν + η n) ^ 2 := by
    intro n
    have hm : AEStronglyMeasurable (fun x => Fn n x - ∫ y, Fn n y ∂canonicalP d N a beta)
        (canonicalP d N a beta) := (hFnc n).aestronglyMeasurable.sub aestronglyMeasurable_const
    have h1 : evariance (Fn n) (canonicalP d N a beta) =
        eLpNorm (fun x => Fn n x - ∫ y, Fn n y ∂canonicalP d N a beta) 2
          (canonicalP d N a beta) ^ 2 := lintegral_enorm_sq_eq_eLpNorm_sq hm
    rw [h1]
    gcongr
    have e : (fun x => Fn n x - ∫ y, Fn n y ∂canonicalP d N a beta) =
        (fun x => F x - c) + (fun x => (Fn n x - ∫ y, Fn n y ∂canonicalP d N a beta) - (F x - c)) := by
      funext x; simp
    rw [e]
    exact eLpNorm_add_le one_le_two
  have hEn : ∀ n, ∫⁻ x, ∑ i, ‖HRS.MS.Phase2S82.configGrad (Fn n) x i‖ₑ ^ 2
      ∂canonicalP d N a beta ≤ ∑ i, (γ i + ε i n) ^ 2 := by
    intro n
    rw [lintegral_finset_sum' Finset.univ (fun i _ => ((hgm n i).enorm.pow_const 2).aemeasurable)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [lintegral_enorm_sq_eq_eLpNorm_sq (hgm n i).aestronglyMeasurable]
    gcongr
    have e : (fun x => HRS.MS.Phase2S82.configGrad (Fn n) x i) =
        (fun x => HRS.MS.Phase2S82.configGrad F x i) +
          (fun x => HRS.MS.Phase2S82.configGrad (Fn n) x i - HRS.MS.Phase2S82.configGrad F x i) := by
      funext x; simp
    rw [e]
    exact eLpNorm_add_le one_le_two
  set U : ℕ → ℝ≥0∞ := fun n => 100 * ((ν + η n) ^ 2 + τ * ∑ i, (γ i + ε i n) ^ 2) with hU
  have hUle : ∀ n, ∫⁻ w, (S n w) ^ 2 ∂P ≤ U n := fun n =>
    (hV12 n).2.trans (mul_le_mul' le_rfl (add_le_add (hVn n) (mul_le_mul' le_rfl (hEn n))))
  have hUt : Tendsto U atTop (𝓝 (100 * (ν ^ 2 + τ * ∑ i, γ i ^ 2))) := by
    have h1 : Tendsto (fun n => (ν + η n) ^ 2) atTop (𝓝 (ν ^ 2)) := by
      have := ((ENNReal.continuous_pow 2).tendsto (ν + 0)).comp (tendsto_const_nhds.add heta)
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun n => ∑ i, (γ i + ε i n) ^ 2) atTop (𝓝 (∑ i, γ i ^ 2)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have := ((ENNReal.continuous_pow 2).tendsto (γ i + 0)).comp
        (tendsto_const_nhds.add (hT3 i))
      simpa [Function.comp_def] using this
    exact ENNReal.Tendsto.const_mul
      (h1.add (ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top))) (Or.inr (by simp))
  -- Fatou
  have hpt : ∀ᵐ w ∂P, (⨆ q ∈ D, ‖Y q w‖ₑ) ^ 2 ≤ liminf (fun k => (S (ns k) w) ^ 2) atTop := by
    filter_upwards [hconv] with w hw
    rw [iSup_subtype' (p := fun q => q ∈ D) (f := fun q _ => ‖Y q w‖ₑ),
      ENNReal.iSup_pow_of_ne_zero (by norm_num)]
    refine iSup_le fun q => ?_
    have h1 : Tendsto (fun k => ‖Fn (ns k) (X (u + (q : ℝ)).toNNReal w) -
        ∫ y, Fn (ns k) y ∂canonicalP d N a beta‖ₑ ^ 2) atTop
        (𝓝 (‖F (X (u + (q : ℝ)).toNNReal w) - c‖ₑ ^ 2)) :=
      ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp (hw q q.2))
    calc ‖Y q w‖ₑ ^ 2 = liminf (fun k => ‖Fn (ns k) (X (u + (q : ℝ)).toNNReal w) -
          ∫ y, Fn (ns k) y ∂canonicalP d N a beta‖ₑ ^ 2) atTop := h1.liminf_eq.symm
      _ ≤ liminf (fun k => (S (ns k) w) ^ 2) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
          have := le_iSup (fun t : Set.Icc (0 : ℝ) T =>
            ‖centerUnder (canonicalP d N a beta) (Fn (ns k)) (X (u + t).toNNReal w)‖ₑ)
            ⟨q, hDs q.2⟩
          exact pow_le_pow_left' this 2
  unfold r26t8a_scalarSupSq
  calc ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) ^ 2 ∂P
      = ∫⁻ w, (⨆ q ∈ D, ‖Y q w‖ₑ) ^ 2 ∂P :=
        lintegral_congr_ae (hYsup.mono fun w h => congrArg (fun x => x ^ 2) h)
    _ ≤ ∫⁻ w, liminf (fun k => (S (ns k) w) ^ 2) atTop ∂P := lintegral_mono_ae hpt
    _ ≤ liminf (fun k => ∫⁻ w, (S (ns k) w) ^ 2 ∂P) atTop :=
        lintegral_liminf_le' (fun k => (hV12 (ns k)).1.pow_const 2)
    _ ≤ liminf (fun k => U (ns k)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k => hUle (ns k))
    _ = 100 * (ν ^ 2 + τ * ∑ i, γ i ^ 2) := (hUt.comp hns.tendsto_atTop).liminf_eq
    _ = _ := by rw [hVar, hE]

end HRS.MS.R26T8A
