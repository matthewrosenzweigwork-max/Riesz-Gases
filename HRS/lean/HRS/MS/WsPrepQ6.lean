import HRS.MS.WsPrepQ5
import HRS.MS.WsPrepAux13

/-!
# S21S packet M6: WMASTER, the window master comparison for a moving mean-field trajectory

`s21m_master`: for every window start `b ≥ 0` and every probability measure `γ0` on the window path space `C([0,T]; B_m)` there is a Gaussian measure `Γ_b`
(finite-dimensional laws centered Gaussian with covariance `noiseCovW C β⁻¹ (b+t) (b+t')`, positive semidefinite) such that the law of the particle window
`Ξ_b = flucPathW m T b (√N) X ρ` satisfies

* `d_2(law Ξ_b, γ0 * Γ_b) ≤ Cs · W + F + d_2(law K_b, γ0)`,
* `W_1(law Ξ_b, γ0 * Γ_b) ≤ Cw · W^{1/2} + F + W_1(law K_b, γ0)`,

where `K_b = s21mPath0` is the transported initial particle field path, `F` bounds `E sup_u ‖(σ/2)∫_0^{b+u} r2CommForcingMov‖` and `W` bounds
`E ∫_0^{b+T} ‖C_r - C̄_r‖₁ dr` (both taken as hypotheses).  This is the window version of `s21_master` (WsStatAux29), proved from the coupling
`gff_adapted_coupling_trace`, the abstract comparison `S105WinCompareHyp`, the Duhamel identity `s21m_R_coord` of the moving reference and the
convolution contraction `t25_smoothDist_conv_le`, `s21_wasserstein_conv_le`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S21m

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.MH.DualityRd HRS.MS.R2GenInit
  HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

theorem s21m_rho_clamp_meas {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ b + T) : Measurable fun p : ℝ × Euc d => ρ (mrrClamp t p.1) p.2 := by
  have e : (fun p : ℝ × Euc d => ρ (mrrClamp t p.1) p.2) =
      fun p => ρ (mrrClamp (b + T) (mrrClamp t p.1)) p.2 := by
    funext p
    have hm := mrrClamp_mem ht0 p.1
    rw [mrrClamp_of_mem (T := b + T) (r := mrrClamp t p.1) ⟨hm.1, hm.2.trans ht⟩]
  rw [e]
  exact hS.hρm.comp (((continuous_mrrClamp t).measurable.comp measurable_fst).prodMk measurable_snd)

set_option maxHeartbeats 6400000 in
theorem s21m_master (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (hβ : 0 < β)
    {T b : ℝ} (hb : 0 ≤ b) (hT : 0 < T) {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) {N : ℕ} (hN : 2 ≤ N)
    {Cs Cw : ℝ} (hCmp : S105WinCompareHyp (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T Cs Cw)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) (b + T) X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (F Wt : ℝ≥0∞)
    (hFb : ∫⁻ ζ, ⨆ u ∈ Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α
          (b + u) r ζ) ∂P ≤ F)
    (hBt : ∃ Bt : ℝ → Ω → (KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ]
        KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ] ℝ),
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ ζ u v, Bt r ζ u v =
        featureForm ((wholeSpaceIndex d : ℕ) : ℝ) T β⁻¹
          (fun (i : Fin d) (x : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ)
            ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp i) b r x) (HRS.Whole.empirical (X r.toNNReal ζ)) u v -
        featureForm ((wholeSpaceIndex d : ℕ) : ℝ) T β⁻¹
          (fun (i : Fin d) (x : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ)
            ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp i) b r x) (HRS.Whole.withDensityReal (ρ r)) u v) ∧
      ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm (Bt r ζ))) ∂P ≤ Wt)
    (γ0 : Measure (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T)) [IsProbabilityMeasure γ0] {εs : ℝ} {εw : ℝ≥0∞}
    (hsm0 : smoothDist 2 (law P (s21mPath0 ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) hT.le (ρ 0) X)) γ0 ≤ εs)
    (hw0 : wassersteinE 1 (law P (s21mPath0 ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) hT.le (ρ 0) X)) γ0 ≤ εw) :
    ∃ Γ : Measure (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T), IsProbabilityMeasure Γ ∧
      (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
        (Matrix.of fun i j => noiseCovW ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹ (b + ts i) (b + ts j)
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i))
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))).PosSemidef ∧
        Γ.map (fun w : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => (WithLp.toLp 2 fun a => OscDual.coord
            (OscPath.at' w ⟨ts a, hts a⟩) (αs a) : EuclideanSpace ℝ (Fin p))) =
          multivariateGaussian 0 (Matrix.of fun i j => noiseCovW ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
            (b + ts i) (b + ts j) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i))
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j)))) ∧
      ENNReal.ofReal (smoothDist 2 (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ))
          ((γ0.prod Γ).map (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T ×
            OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2))) ≤
        ENNReal.ofReal Cs * Wt + F + ENNReal.ofReal εs ∧
      wassersteinE 1 (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ))
          ((γ0.prod Γ).map (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T ×
            OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2)) ≤
        ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F + εw := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ T := hT.le
  have hτ : 0 ≤ b + T := by linarith
  have hq : 0 ≤ β⁻¹ := inv_nonneg.2 hβ.le
  have hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (b + T) := ⟨le_rfl, hτ⟩
  haveI hνp : IsProbabilityMeasure (HRS.Whole.withDensityReal (ρ 0)) :=
    HRS.MS.Thm.cb_withDensityReal_isProb (hS.hprob h0)
  have hXm : ∀ t, Measurable (X t) := hX.adapted
  -- the particle martingale and the Gaussian coupling
  obtain ⟨M₁, hM₁ito, hM₁⟩ := s105_particle_martingale hτ hS.hF N hN1 β⁻¹ hq P ℱ W' X hF.brownian
    hF.progressive
  set Db := s21mDb _ hS.hF hS.hpAll β⁻¹ hq with hDbdef
  have hDb : IsDetCovDensity (b + T) Db := s21mDb_isDet hτ _ hS.hF hS.hpAll hS.hρm β⁻¹ hq
  set Sg₁ : ℝ → Ω → (KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ] KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ] ℝ) :=
    fun r z => hsCovForm (s105Phi (fun a' r x => r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x) (b + T) β⁻¹ X r z) with hSg₁
  obtain ⟨Ω₂, mΩ₂, P₂, π₂, ℱ₂, Gb, Sd, hc⟩ :=
    gff_adapted_coupling_trace P ℱ (b + T) hτ ⟨ℱ 0, le_rfl⟩ M₁ Sg₁ hM₁ Db hDb
  haveI : IsProbabilityMeasure (P₂ : Measure Ω₂) := inferInstance
  have hπ : MeasurePreserving π₂ (P₂ : Measure Ω₂) P := hc.preserving
  set X₂ : ℝ≥0 → Ω₂ → EucConfig d N := fun t ζ => X t (π₂ ζ) with hX₂def
  have hXm₂ : ∀ t, Measurable (X₂ t) := fun t => (hXm t).comp hπ.measurable
  have hπ' : ∀ i : ℝ, Measurable[ℱ₂ i, ℱ i] π₂ := fun i => Measurable.of_comap_le (hc.filtration i)
  set Mm : ℝ → Ω₂ → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T := fun τ ζ => M₁ τ (π₂ ζ) with hMmdef
  set Sg₂ : ℝ → Ω₂ → (KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ] KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ] ℝ) :=
    fun r ζ => Sg₁ r (π₂ ζ) with hSg₂def
  have hMm₂ : IsHilbertMartingaleWithCovariation (P₂ : Measure Ω₂) ℱ₂ (b + T) Mm Sg₂ :=
    hc.martingale (b + T) hτ le_rfl
  have hMm₁m : ∀ t, Measurable (M₁ t) := fun t => HRS.Uniform.Q07c.measurable_of_isHM hM₁ t
  have hMmm : ∀ t, Measurable (Mm t) := fun t => (hMm₁m t).comp hπ.measurable
  have hGb : IsHilbertMartingaleWithCovariation (P₂ : Measure Ω₂) ℱ₂ (b + T) Gb (fun r _ => Db r) := by
    have h1 := hc.gaussian (b + T) hτ le_rfl
    have e : (fun (r : ℝ) (_ : Ω₂) => if ENNReal.ofReal r ≤ ENNReal.ofReal (b + T) then Db r else 0) =
        fun r _ => Db r := by
      funext r _
      by_cases hr : r ≤ b + T
      · rw [if_pos (ENNReal.ofReal_le_ofReal hr)]
      · rw [if_neg ((ENNReal.ofReal_le_ofReal_iff hτ).not.2 hr)]
        exact (s21mDb_zero _ hS.hF hS.hpAll β⁻¹ hq (fun h => hr h.2)).symm
    rw [e] at h1
    exact h1
  have hGm : ∀ t, Measurable (Gb t) := fun t =>
    gfb4_measurable_of_weak fun x => (((hGb.martingale x).stronglyAdapted t).mono (ℱ₂.le t)).measurable
  have hdiff := gf_coupling_difference hc hτ
  have hcost := gf_coupling_cost_le hc hτ
  -- the initial state, the remainder and the particle window
  have hπ0 : Measurable[ℱ₂ 0, ℱ 0] π₂ := hπ' 0
  obtain ⟨Bf, hBf0, hBf⟩ := hS.hF.bound
  have hK0f : Measurable fun x : EucConfig d N => s105k0 (fun (a' : Fin d) (z : Euc d) => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b 0 z)
      (Real.sqrt N) (HRS.Whole.empirical x) (HRS.Whole.withDensityReal (ρ 0)) :=
    s105_k0_meas _ (Real.sqrt N) Bf hBf0 (fun a' => (hS.hF.cont_x a' 0 h0).measurable)
      (fun a' z => hBf a' 0 h0 z) (by omega) _ (s56_integrable_norm_withDensity (hS.hprob h0) hS.hρ2)
  have hk0₁ : Measurable[ℱ 0] (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) (ρ 0) X) := hK0f.comp (hF.adapted 0)
  have hk0₂ : Measurable[ℱ₂ 0] (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) (ρ 0) X₂) := hk0₁.comp hπ0
  have hk0m : Measurable (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) (ρ 0) X₂) := hk0₂.mono (ℱ₂.le 0) le_rfl
  set R₂ : ℝ → Ω₂ → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ) := fun t ζ =>
    if t ∈ Set.Icc (0 : ℝ) T then s21mR ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂ Mm t ζ else 0 with hR₂def
  have hRm : ∀ t, Measurable (R₂ t) := fun t => by
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · have e : R₂ t = s21mR ((quadraticGradientDyn d s a β).coeff ρ)
          ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂ Mm t := funext fun ζ => if_pos ht
      rw [e]
      haveI := HRS.MS.Thm.cb_withDensityReal_isProb
        (hS.hprob (r := b + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      unfold s21mR s21mXi
      refine (((s56_xi_cont_config hd1 hm (Real.sqrt N) (by omega)
        (HRS.Whole.withDensityReal (ρ (b + t)))).measurable.comp (hXm₂ _)).sub
        ((s56_evalA_cont hT0 t).measurable.comp hk0m)).sub ?_
      unfold reconstructPath
      exact (((s56_evalA_cont hT0 t).measurable.comp (hMmm (b + T))).sub
        (HRS.MS.U9.u9_continuous_B.measurable.comp (hMmm (b + T)))).add
        (HRS.MS.U9.u9_continuous_B.measurable.comp (hMmm (b + t)))
    · have e : R₂ t = fun _ => (0 : OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) := funext fun ζ => if_neg ht
      rw [e]
      exact measurable_const
  have hRc₁ : ∀ᵐ z ∂P, ContinuousOn (fun u => s21mR ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X M₁ u z) (Set.Icc (0 : ℝ) T) := by
    filter_upwards [hX.cont] with z hz
    exact s21m_R_cont hd1 hT0 hb hS hN1 (Real.sqrt N) hm X z hz M₁ (hM₁ito.cont z).continuousOn
  have hRc : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ContinuousOn (fun t => R₂ t ζ) (Set.Icc 0 T) := by
    filter_upwards [hπ.quasiMeasurePreserving.ae hRc₁] with ζ hζ
    refine hζ.congr fun t ht => ?_
    simp only [hR₂def, if_pos ht]
    rfl
  -- the comparison path
  have hrecm : ∀ t, Measurable fun ζ => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
      (fun τ ζ => Gb (b + τ) ζ) ζ t := fun t => by
    unfold reconstructPath
    exact (((s56_evalA_cont hT0 t).measurable.comp (hGm (b + T))).sub
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm (b + T)))).add
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm (b + t)))
  have hrecc : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), Continuous fun t : Set.Icc (0 : ℝ) T =>
      reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => Gb (b + τ) ζ) ζ t := by
    filter_upwards [hGb.cont] with ζ hζ
    exact HRS.MS.U9.u9_continuous_recon hT0 _ ζ (hζ.comp (by fun_prop)
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩))
  have hYhm : AEMeasurable (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
      (fun t => (s105K0 ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b
        (Real.sqrt N) (ρ 0) X₂ ζ).evalA t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
          (fun τ ζ => Gb (b + τ) ζ) ζ t)) (P₂ : Measure Ω₂) := by
    have := gfb4_aemeasurable_windowPath (P₂ : Measure Ω₂) hT0
      (fun t ζ => (s105K0 ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b
        (Real.sqrt N) (ρ 0) X₂ ζ).evalA t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
          (fun τ ζ => Gb (b + τ) ζ) ζ t)
      (fun t _ => ((s56_evalA_cont hT0 t).measurable.comp hk0m).add (hrecm t))
      (by
        filter_upwards [hrecc] with ζ hζ
        exact (HRS.MS.U9.u9_continuousOn_evalA hT0 _).add (continuousOn_iff_continuous_restrict.2 hζ))
    rwa [← s56_wpo_eq_windowPath] at this
  have hΞP : AEMeasurable (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ) P :=
    HRS.Whole.s21p_fluc_window_aemeas hd1 (by omega) hm hb hT0 P X ρ (Real.sqrt N) hXm hX.cont
      (fun t ht => hS.hprob ht) hS.hcont
  have hΞm : AEMeasurable (fun ζ => flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ (π₂ ζ))
      (P₂ : Measure Ω₂) := hΞP.comp_quasiMeasurePreserving hπ.quasiMeasurePreserving
  have hlawΞ : law (P₂ : Measure Ω₂) (fun ζ => flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ
      (π₂ ζ)) = law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ) :=
    HRS.GF.law_comp_mp hπ hΞP
  have hΞeq : ∀ ζ, flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ (π₂ ζ) =
      windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) (ρ 0) X₂ ζ).evalA t +
        reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => Mm (b + τ) ζ) ζ t + R₂ t ζ) := by
    intro ζ
    rw [s21m_fluc_eq]
    refine s56_wpo_congr fun t ht => ?_
    have e : R₂ t ζ = s21mR ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂ Mm t ζ := if_pos ht
    rw [e]
    unfold s21mR
    abel
  have hcmp := hCmp b hb Ω₂ (P₂ : Measure Ω₂) ℱ₂ (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
    ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) (ρ 0) X₂) hk0₂ Mm Sg₂ hMm₂ hMmm Gb Db hDb hGb hGm Sd
    (fun r ζ => traceNormForm (Sg₂ r ζ - Db r)) hdiff hcost hMm₂.cont hMm₂.zero hGb.cont hGb.zero R₂ hRc hRm
    (fun ζ => flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ (π₂ ζ))
    (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => (s105K0
      ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b
        (Real.sqrt N) (ρ 0) X₂ ζ).evalA t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
          (fun τ ζ => Gb (b + τ) ζ) ζ t)) hΞm hYhm hYhm (Filter.Eventually.of_forall hΞeq)
  obtain ⟨hsm, hw1⟩ := hcmp
  rw [hlawΞ] at hsm hw1
  -- the covariance error
  have hT₂ : ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm (Sg₂ r ζ - Db r)))
      ∂(P₂ : Measure Ω₂) ≤ Wt := by
    obtain ⟨Bt, hBtid, hBtint⟩ := hBt
    set Fh : Ω → ℝ≥0∞ := fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm
      (hsCovForm (fun k : Fin N × Fin d => Real.sqrt (2 * β⁻¹ / N) • (fun (a' : Fin d) (r : ℝ) (x : Euc d) =>
        r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T
          (gradComp a') b r x) k.2 (mrrClamp (b + T) r) (X (Real.toNNReal (mrrClamp (b + T) r)) ζ k.1)) - Db r))
      with hFhdef
    have hFhm : Measurable Fh :=
      s105_trace_meas hτ hS.hF β⁻¹ Db (fun u v => hDb.meas u v) ℱ X hF.progressive
    have hFh_eq : ∀ ζ, Fh ζ = ∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm (Bt r ζ)) := by
      intro ζ
      refine setLIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
      congr 2
      refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.sub_apply]
      have hh := s105_hsCov_eq (fun (a' : Fin d) (r : ℝ) (x : Euc d) => r2WindowFeature
        ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
        (b + T) β⁻¹ hq hN1 r (X (Real.toNNReal (mrrClamp (b + T) r)) ζ) u v
      beta_reduce at hh
      rw [hh, (s21mDb_spec _ hS.hF hS.hpAll β⁻¹ hq hr).1, hBtid r hr ζ u v, mrrClamp_of_mem hr]
    have hint : ∀ ζ, ∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm (Sg₂ r ζ - Db r)) =
        Fh (π₂ ζ) := by
      intro ζ
      refine setLIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
      simp only [hSg₂def, hSg₁]
      unfold s105Phi
      simp only [mrrClamp_of_mem hr, hX₂def]
    simp_rw [hint]
    rw [HRS.GF.lintegral_comp_mp hπ hFhm.aemeasurable]
    simp_rw [hFh_eq]
    exact hBtint
  -- the remainder
  have hRint : ∫⁻ ζ, ‖windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => R₂ t ζ)‖ₑ
      ∂(P₂ : Measure Ω₂) ≤ F := by
    haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT0⟩⟩
    set s' : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hs'def
    have hs' : DenseRange s' := TopologicalSpace.denseRange_denseSeq _
    set Hp : Ω → ℝ≥0∞ := fun ζ => ⨆ n : ℕ, l2NormE (fun α : MultiIndex d =>
      -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), r2CommForcingMov
        ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α
        (b + (s' n)) r ζ) with hHpdef
    have hHpm : Measurable Hp := by
      refine Measurable.iSup fun n => ?_
      unfold l2NormE
      refine Measurable.pow_const (Measurable.ennreal_tsum fun α => ?_) _
      have ht0 : 0 ≤ b + s' n := by linarith [(s' n).2.1]
      have htT : b + s' n ≤ b + T := by linarith [(s' n).2.2]
      have hcl := hS.hcl α (b + s' n) ht0
      have hf := s21m_force_meas s ((quadraticGradientDyn d s a β).coeff ρ) (t := b + s' n) ht0 hcl
        (fun r hr => hS.hprob ⟨hr.1, hr.2.trans htT⟩) (s21m_rho_clamp_meas hS ht0 htT) ℱ X hF.progressive
      exact ((measurable_const.mul hf).pow_const 2).ennreal_ofReal
    have hΦ₁ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' (s105Phi (fun a' r x => r2WindowFeature
        ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
        (b + T) β⁻¹ X) := fun τ => s105_phi_isHS hτ hS.hF N β⁻¹ P ℱ X hF.progressive τ
    have hRb₁ := s21m_R_bound_dense hd hs0 hsd hβ hb hT hS hN1 hm P X₀ W X hX ℱ W' hF M₁ hΦ₁ hM₁ito s' hs'
    have hpt : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ‖windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => R₂ t ζ)‖ₑ ≤
        Hp (π₂ ζ) := by
      filter_upwards [hπ.quasiMeasurePreserving.ae hRb₁] with ζ hζ
      have := gfb4_windowPath_enorm_le T R₂ ζ (Hp (π₂ ζ)) (fun t ht => by
        simp only [hR₂def, if_pos ht]
        exact hζ t ht)
      rwa [← s56_wpo_eq_windowPath (m := ((wholeSpaceIndex d : ℕ) : ℝ)) (T := T)
        (fun t ζ => R₂ t ζ) |> fun e => congrFun e ζ] at this
    calc ∫⁻ ζ, ‖windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => R₂ t ζ)‖ₑ ∂(P₂ : Measure Ω₂)
        ≤ ∫⁻ ζ, Hp (π₂ ζ) ∂(P₂ : Measure Ω₂) := lintegral_mono_ae hpt
      _ = ∫⁻ ζ, Hp ζ ∂P := HRS.GF.lintegral_comp_mp hπ hHpm.aemeasurable
      _ ≤ ∫⁻ ζ, ⨆ u ∈ Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u), r2CommForcingMov
            ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α
            (b + u) r ζ) ∂P := by
        refine lintegral_mono fun ζ => iSup_le fun n => ?_
        exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) => l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u), r2CommForcingMov
            ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α
            (b + u) r ζ)) (s' n : ℝ) (s' n).2
      _ ≤ F := hFb
  -- the independent decomposition
  set k0₂ : Ω₂ → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T := fun ζ => s105K0
    ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) (ρ 0) X₂ ζ with hk0₂def
  set U : Ω₂ → OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T := fun ζ => s56EvalPath hT0 (k0₂ ζ) with hUdef
  have hUm : Measurable U := (s56EvalPath hT0).continuous.measurable.comp hk0m
  set V : Ω₂ → OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T := fun ζ => windowPathOf
    ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
      (fun τ ζ => Gb (b + τ) ζ) ζ t) with hVdef
  have hGbc := hGb.cont
  have hVm : AEMeasurable V (P₂ : Measure Ω₂) := by
    have := gfb4_aemeasurable_windowPath (P₂ : Measure Ω₂) hT0 (fun t ζ => reconstructPath
      ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => Gb (b + τ) ζ) ζ t) (fun t _ => hrecm t)
      (by
        filter_upwards [hrecc] with ζ hζ
        exact continuousOn_iff_continuous_restrict.2 hζ)
    rwa [← s56_wpo_eq_windowPath] at this
  haveI hΓp : IsProbabilityMeasure (law (P₂ : Measure Ω₂) V) :=
    (Measure.isProbabilityMeasure_map_iff hVm).2 inferInstance
  have hind := gf_coupling_indep hc hτ (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
    ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) (ρ 0) X) hk0₁
  have hindep : IndepFun k0₂ V (P₂ : Measure Ω₂) :=
    s21m_recon_indep hS hb hT β⁻¹ hq (P₂ : Measure Ω₂) hGb hGm k0₂ hind
  have hindU : IndepFun U V (P₂ : Measure Ω₂) :=
    hindep.comp (s56EvalPath hT0).continuous.measurable measurable_id
  have hYh : (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => (k0₂ ζ).evalA t +
      reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => Gb (b + τ) ζ) ζ t)) =ᵐ[(P₂ : Measure Ω₂)]
      fun ζ => U ζ + V ζ := by
    filter_upwards [hrecc] with ζ hc
    exact HRS.MS.S21.s21_wpo_evalA_add hT0 (k0₂ ζ) (fun t => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
      (fun τ ζ => Gb (b + τ) ζ) ζ t) (continuousOn_iff_continuous_domRestrict.2 hc)
  have hlawYh : law (P₂ : Measure Ω₂) (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
      (fun t => (k0₂ ζ).evalA t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
        (fun τ ζ => Gb (b + τ) ζ) ζ t)) =
      ((law (P₂ : Measure Ω₂) U).prod (law (P₂ : Measure Ω₂) V)).map
        (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2) := by
    unfold law
    rw [Measure.map_congr hYh]
    exact HRS.MS.S21.s21_law_add_of_indep (P₂ : Measure Ω₂) U V hUm.aemeasurable hVm hindU
  have hU0m : Measurable (s21mPath0 ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b
      (Real.sqrt N) hT0 (ρ 0) X) :=
    (s56EvalPath hT0).continuous.measurable.comp
      (s105_K0_meas _ _ T b (Real.sqrt N) (hS.hprob h0) hS.hρ2 hN1 (τ₀ := b + T) (by linarith) hb hS.hF X (hXm 0))
  have hlawU : law (P₂ : Measure Ω₂) U = law P (s21mPath0 ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) hT0 (ρ 0) X) :=
    HRS.GF.law_comp_mp hπ hU0m.aemeasurable
  haveI hlP : IsProbabilityMeasure (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ)) :=
    (Measure.isProbabilityMeasure_map_iff hΞP).2 inferInstance
  haveI hlU : IsProbabilityMeasure (law P (s21mPath0 ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) hT0 (ρ 0) X)) :=
    (Measure.isProbabilityMeasure_map_iff hU0m.aemeasurable).2 inferInstance
  have hadd : Measurable (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T ×
      OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2) :=
    measurable_fst.add measurable_snd
  haveI hQp : IsProbabilityMeasure ((γ0.prod (law (P₂ : Measure Ω₂) V)).map
      (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2)) :=
    (Measure.isProbabilityMeasure_map_iff hadd.aemeasurable).2 inferInstance
  haveI hYlp : IsProbabilityMeasure (((law (P₂ : Measure Ω₂) U).prod (law (P₂ : Measure Ω₂) V)).map
      (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2)) := by
    haveI : IsProbabilityMeasure (law (P₂ : Measure Ω₂) U) :=
      (Measure.isProbabilityMeasure_map_iff hUm.aemeasurable).2 inferInstance
    exact (Measure.isProbabilityMeasure_map_iff hadd.aemeasurable).2 inferInstance
  -- the two bounds against the law of `k₀path + 𝒯G`
  have hsm' : ENNReal.ofReal (smoothDist 2 (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ))
      (((law (P₂ : Measure Ω₂) U).prod (law (P₂ : Measure Ω₂) V)).map
        (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T =>
          z.1 + z.2))) ≤ ENNReal.ofReal Cs * Wt + F := by
    rw [← hlawYh]
    simp only [sub_self, enorm_zero, lintegral_zero, add_zero] at hsm
    exact hsm.trans (add_le_add (mul_le_mul' le_rfl hT₂) hRint)
  have hw' : wassersteinE 1 (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ))
      (((law (P₂ : Measure Ω₂) U).prod (law (P₂ : Measure Ω₂) V)).map
        (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T =>
          z.1 + z.2)) ≤ ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F := by
    rw [← hlawYh]
    simp only [sub_self, enorm_zero, lintegral_zero, add_zero] at hw1
    refine hw1.trans (add_le_add ?_ hRint)
    exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hT₂ (by norm_num))
  rw [hlawU] at hsm' hw'
  refine ⟨law (P₂ : Measure Ω₂) V, hΓp, fun p ts hts αs => ?_, ?_, ?_⟩
  · refine ⟨s21m_noiseCov_psd hS hb hT β⁻¹ hq ts hts αs, ?_⟩
    have hvec : Measurable (fun w : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => (WithLp.toLp 2 fun a => OscDual.coord
        (OscPath.at' w ⟨ts a, hts a⟩) (αs a) : EuclideanSpace ℝ (Fin p))) := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
      have h1 : Continuous fun w : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => OscPath.at' w ⟨ts a, hts a⟩ := by
        have : Continuous fun w : C(Set.Icc (0 : ℝ) T, OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) => w ⟨ts a, hts a⟩ :=
          continuous_eval_const _
        exact this
      exact ((s56_continuous_coord ((wholeSpaceIndex d : ℕ) : ℝ) (αs a)).comp h1).measurable
    unfold law
    rw [AEMeasurable.map_map_of_aemeasurable hvec.aemeasurable hVm]
    exact s21m_recon_fdd hS hb hT β⁻¹ hq (P₂ : Measure Ω₂) hGb ts hts αs
  · have htri := smoothDist_triangle 2 (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ))
      (((law P (s21mPath0 ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b
        (Real.sqrt N) hT0 (ρ 0) X)).prod (law (P₂ : Measure Ω₂) V)).map
        (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2))
      ((γ0.prod (law (P₂ : Measure Ω₂) V)).map
        (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2))
    have hconv := HRS.T25.t25_smoothDist_conv_le (law P (s21mPath0 ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) hT0 (ρ 0) X)) γ0 (law (P₂ : Measure Ω₂) V)
    have hεs0 : 0 ≤ εs := (smoothDist_nonneg _ _ _).trans (hconv.trans hsm0)
    calc ENNReal.ofReal (smoothDist 2 (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ))
          ((γ0.prod (law (P₂ : Measure Ω₂) V)).map
            (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T =>
              z.1 + z.2)))
        ≤ ENNReal.ofReal (smoothDist 2 (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ))
            (((law P (s21mPath0 ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b
              (Real.sqrt N) hT0 (ρ 0) X)).prod (law (P₂ : Measure Ω₂) V)).map
              (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T =>
                z.1 + z.2)) + εs) :=
          ENNReal.ofReal_le_ofReal (htri.trans (add_le_add le_rfl (hconv.trans hsm0)))
      _ = ENNReal.ofReal (smoothDist 2 (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ))
            (((law P (s21mPath0 ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b
              (Real.sqrt N) hT0 (ρ 0) X)).prod (law (P₂ : Measure Ω₂) V)).map
              (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T =>
                z.1 + z.2))) + ENNReal.ofReal εs :=
          ENNReal.ofReal_add (smoothDist_nonneg _ _ _) hεs0
      _ ≤ _ := add_le_add hsm' le_rfl
  · have htri := wassersteinE_triangle 1 le_rfl
      (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ))
      (((law P (s21mPath0 ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b
        (Real.sqrt N) hT0 (ρ 0) X)).prod (law (P₂ : Measure Ω₂) V)).map
        (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2))
      ((γ0.prod (law (P₂ : Measure Ω₂) V)).map
        (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2))
    have hconv := HRS.MS.S21.s21_wasserstein_conv_le 1 le_rfl (law P (s21mPath0
      ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) hT0 (ρ 0) X)) γ0
      (law (P₂ : Measure Ω₂) V)
    exact htri.trans (add_le_add hw' (hconv.trans hw0))

end HRS.MS.S21m
