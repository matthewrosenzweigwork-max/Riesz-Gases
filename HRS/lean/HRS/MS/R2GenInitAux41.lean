import HRS.MS.R2GenInitAux42

/-!
# S10.5 window comparison, packet F2: the master comparison on the coupling space (stationary quadratic dynamics)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.GF HRS.Uniform HRS.MH.DualityRd

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem s105_master {T Cs Cw : ℝ} (hCmp : S105WinCompareHyp (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T Cs Cw)
    (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hT : 0 < T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {b : ℝ} (hb : 0 ≤ b) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hreal : IsR2Realization d s a β P X₀ W X) (η₀ : Ω → (Euc d → ℝ) → ℝ)
    (Y : ℝ → Ω → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ))
    (hY : ∀ T' : ℝ, IsLinearFluctuationSolutionW P ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) β⁻¹ T' η₀ Y)
    (hcontc : ∀ᵐ ζ ∂P, Continuous fun u : Set.Icc (0 : ℝ) T => r2InitCouplingFun
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ)
      (HRS.Whole.withDensityReal ρ) b X₀ η₀ ζ u)
    (F Wt : ℝ≥0∞)
    (hFb : ∫⁻ ζ, ⨆ u ∈ Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) s ((wholeSpaceIndex d : ℕ) : ℝ) (fun _ => ρ) X α
          (b + u) r ζ) ∂P ≤ F)
    (hBt : ∃ Bt : ℝ → Ω → (KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ] KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ] ℝ),
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ ζ u v, Bt r ζ u v =
        featureForm ((wholeSpaceIndex d : ℕ) : ℝ) T β⁻¹
          (fun (i : Fin d) (x : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
            ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp i) b r x) (HRS.Whole.empirical (X r.toNNReal ζ)) u v -
        featureForm ((wholeSpaceIndex d : ℕ) : ℝ) T β⁻¹
          (fun (i : Fin d) (x : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
            ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp i) b r x) (HRS.Whole.withDensityReal ρ) u v) ∧
      ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm (Bt r ζ))) ∂P ≤ Wt) :
    (ENNReal.ofReal (smoothDist 2 (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X (fun _ : ℝ => ρ)))
          (law P (processWindow ((wholeSpaceIndex d : ℕ) : ℝ) T b Y))) ≤
        ENNReal.ofReal Cs * Wt + F + ∫⁻ ζ, ENNReal.ofReal ‖r2InitCouplingPath
          ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T
          (HRS.Whole.withDensityReal ρ) b X₀ η₀ ζ‖ ∂P) ∧
    (wassersteinE 1 (law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X (fun _ : ℝ => ρ)))
          (law P (processWindow ((wholeSpaceIndex d : ℕ) : ℝ) T b Y)) ≤
        ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F + ∫⁻ ζ, ENNReal.ofReal ‖r2InitCouplingPath
          ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T
          (HRS.Whole.withDensityReal ρ) b X₀ η₀ ζ‖ ∂P) := by
  have hd1 : 1 ≤ d := by omega
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ T := hT.le
  have hτ : 0 ≤ b + T := by linarith
  have hτ' : 0 < b + T := by linarith
  have hq : 0 ≤ β⁻¹ := inv_nonneg.2 hβ.le
  have hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hS : S105Stat d s a β T b ρ := s105_stat_of_thermal hd hs0 hsd ha hβ hT hρ hb
  haveI hνp : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.Thm.cb_withDensityReal_isProb hS.hprob
  obtain ⟨ℱ, W', hfilt⟩ := hreal.filtered
  have hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) (b + T) X₀ W X := hreal.solution (b + T)
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT0⟩⟩
  set s' : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hs'def
  have hs' : DenseRange s' := TopologicalSpace.denseRange_denseSeq _
  have hη' : ∀ i : ℕ × MultiIndex d, AEMeasurable (fun ζ => s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ i) P := fun i =>
    s105_hη _ _ _ b T P η₀ Y (hY (b + T)) (s' i.1).2 hb i.2
  have hΨc : AEMeasurable (s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀) P := aemeasurable_pi_iff.2 hη'
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, c', Ψt, hΨtm, hΨae, hX₁, hF₁, hc'0, hlaw₁⟩ :=
    s105_stage1 P X₀ W X hX ℱ W' hfilt (s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀) hΨc
  set X₁ : ℝ≥0 → Ω₁ → EucConfig d N := fun t z => X t (π₁ z) with hX₁def
  have hXm₁ : ∀ t, Measurable (X₁ t) := fun t => (hX.adapted t).comp hπ₁.measurable
  obtain ⟨M₁, hM₁ito, hM₁⟩ := s105_particle_martingale hτ hS.hF N hN1 β⁻¹ hq P₁ ℱ₁
    (fun t z k => W' t (π₁ z) k) X₁ hF₁.brownian hF₁.progressive
  set Db := s105Db _ hS.hF (HRS.Whole.withDensityReal ρ) β⁻¹ hq with hDbdef
  have hDb : IsDetCovDensity (b + T) Db := s105Db_isDet hτ _ hS.hF hS.hprob β⁻¹ hq
  set Sg₁ : ℝ → Ω₁ → (KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ] KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ] ℝ) :=
    fun r z => hsCovForm (s105Phi (fun a' r x => r2WindowFeature ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x) (b + T) β⁻¹ X₁ r z) with hSg₁
  obtain ⟨Ω₂, mΩ₂, P₂, π₂, ℱ₂, Gb, Sd, hc⟩ :=
    gff_adapted_coupling_trace P₁ ℱ₁ (b + T) hτ ⟨ℱ₁ 0, le_rfl⟩ M₁ Sg₁ hM₁ Db hDb
  haveI : IsProbabilityMeasure (P₂ : Measure Ω₂) := inferInstance
  have hπ : MeasurePreserving π₂ (P₂ : Measure Ω₂) P₁ := hc.preserving
  set π : Ω₂ → Ω := fun ζ => π₁ (π₂ ζ) with hπdef
  have hπtot : MeasurePreserving π (P₂ : Measure Ω₂) P := hπ₁.comp hπ
  set X₂ : ℝ≥0 → Ω₂ → EucConfig d N := fun t ζ => X t (π ζ) with hX₂def
  have hπ' : ∀ i : ℝ, Measurable[ℱ₂ i, ℱ₁ i] π₂ := fun i => Measurable.of_comap_le (hc.filtration i)
  have hprog₂ : IsProgressive ℱ₂ (ofNNRealTime X₂) := fun i =>
    (hF₁.progressive i).comp (measurable_fst.prodMk ((hπ' i).comp measurable_snd))
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
        exact (s105Db_zero _ hS.hF _ β⁻¹ hq (fun h => hr h.2)).symm
    rw [e] at h1
    exact h1
  have hGm : ∀ t, Measurable (Gb t) := fun t =>
    gfb4_measurable_of_weak fun x => (((hGb.martingale x).stronglyAdapted t).mono (ℱ₂.le t)).measurable
  have hdiff := gf_coupling_difference hc hτ
  have hcost := gf_coupling_cost_le hc hτ
  -- the initial state, the remainder and the particle window
  have hπ0 : Measurable[ℱ₂ 0, ℱ₁ 0] π₂ := hπ' 0
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (b + T) := ⟨le_rfl, hτ⟩
  obtain ⟨Bf, hBf0, hBf⟩ := hS.hF.bound
  have hK0f : Measurable fun x : EucConfig d N => s105k0 (fun (a' : Fin d) (z : Euc d) => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b 0 z)
      (Real.sqrt N) (HRS.Whole.empirical x) (HRS.Whole.withDensityReal ρ) :=
    s105_k0_meas _ (Real.sqrt N) Bf hBf0 (fun a' => (hS.hF.cont_x a' 0 h0).measurable)
      (fun a' z => hBf a' 0 h0 z) (by omega) _ (s56_integrable_norm_withDensity hS.hprob hS.hρ2)
  have hk0₁ : Measurable[ℱ₁ 0] (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₁) := hK0f.comp (hF₁.adapted 0)
  have hk0₂ : Measurable[ℱ₂ 0] (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂) := hk0₁.comp hπ0
  have hk0m : Measurable (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂) := hk0₂.mono (ℱ₂.le 0) le_rfl
  have hXm₂ : ∀ t, Measurable (X₂ t) := fun t => (hX.adapted t).comp hπtot.measurable
  set R₂ : ℝ → Ω₂ → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ) := fun t ζ =>
    if t ∈ Set.Icc (0 : ℝ) T then s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂ Mm t ζ else 0 with hR₂def
  have hRm : ∀ t, Measurable (R₂ t) := fun t => by
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · have e : R₂ t = s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
          ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂ Mm t := funext fun ζ => if_pos ht
      rw [e]
      unfold s105R s105Xi
      refine (((s56_xi_cont_config hd1 hm (Real.sqrt N) (by omega) (HRS.Whole.withDensityReal ρ)).measurable.comp
        (hXm₂ _)).sub ((s56_evalA_cont hT0 t).measurable.comp hk0m)).sub ?_
      unfold reconstructPath
      exact (((s56_evalA_cont hT0 t).measurable.comp (hMmm (b + T))).sub
        (HRS.MS.U9.u9_continuous_B.measurable.comp (hMmm (b + T)))).add
        (HRS.MS.U9.u9_continuous_B.measurable.comp (hMmm (b + t)))
    · have e : R₂ t = fun _ => (0 : OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) := funext fun ζ => if_neg ht
      rw [e]
      exact measurable_const
  have hW₁ : IsWholeStrongSolution P₁ (quadraticGradientDyn d s a β) (b + T) (fun z => X₀ (π₁ z))
      (fun t z => W t (π₁ z)) X₁ := hX₁
  have hRc₁ : ∀ᵐ z ∂P₁, ContinuousOn (fun u => s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₁ M₁ u z) (Set.Icc (0 : ℝ) T) := by
    filter_upwards [hX₁.cont] with z hz
    exact s105_R_cont hd1 hT0 hb hS hN1 (Real.sqrt N) hm X₁ z hz M₁ (hM₁ito.cont z).continuousOn
  have hRc : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ContinuousOn (fun t => R₂ t ζ) (Set.Icc 0 T) := by
    filter_upwards [hπ.quasiMeasurePreserving.ae hRc₁] with ζ hζ
    refine hζ.congr fun t ht => ?_
    simp only [hR₂def, if_pos ht]
    rfl
  -- the Gaussian martingale: continuous modification, independence from the initial array
  obtain ⟨G', hG', hG'c, hG'z, hGG'⟩ := gfb4_modify (P₂ : Measure Ω₂) ℱ₂ hτ Gb Db
    (fun σ hσ => s105Db_zero _ hS.hF _ β⁻¹ hq hσ) hGb
  have hG'm : ∀ t, Measurable (G' t) := fun t => HRS.Uniform.Q07c.measurable_of_isHM hG' t
  have hX0m : Measurable fun z : Ω₁ => X 0 (π₁ z) := (hX.adapted 0).comp hπ₁.measurable
  have hc'm : Measurable c' := hc'0.mono (ℱ₁.le 0) le_rfl
  set c'' : Ω₂ → (ℕ × MultiIndex d → ℝ) := fun ζ => c' (π₂ ζ) with hc''def
  have hc''m : Measurable c'' := hc'm.comp hπ.measurable
  have hc''law : (P₂ : Measure Ω₂).map c'' = P.map (s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀) := by
    have e1 : (P₂ : Measure Ω₂).map c'' = P₁.map c' := by
      rw [show c'' = c' ∘ π₂ from rfl, ← Measure.map_map hc'm hπ.measurable, hπ.map_eq]
    have e2 : P₁.map c' = P.map Ψt := by
      have := congrArg (fun μ => μ.map Prod.snd) hlaw₁
      rwa [Measure.map_map measurable_snd (hX0m.prodMk hc'm),
        Measure.map_map measurable_snd ((hX.adapted 0).prodMk hΨtm)] at this
    rw [e1, e2]
    exact Measure.map_congr hΨae.symm
  have hind0 := gf_coupling_indep hc hτ c' hc'0
  have hW : ∀ (p : ℕ) (f : Fin p → ℕ × MultiIndex d),
      IndepFun (fun ζ => (WithLp.toLp 2 fun i => s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G' ζ (f i) :
        EuclideanSpace ℝ (Fin p))) (fun ζ => (WithLp.toLp 2 fun i => c'' ζ (f i) : EuclideanSpace ℝ (Fin p)))
        (P₂ : Measure Ω₂) := by
    intro p f
    have h1 := s105_indepFun_vec ((wholeSpaceIndex d : ℕ) : ℝ) T b hb (P₂ : Measure Ω₂) s' Gb c'' hind0 f
    refine IndepFun.congr h1 ?_ Filter.EventuallyEq.rfl
    have : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ∀ i : Fin p, G' (b + s' (f i).1) ζ = Gb (b + s' (f i).1) ζ :=
      ae_all_iff.2 fun i => hGG' _ ⟨by linarith [(s' (f i).1).2.1], by linarith [(s' (f i).1).2.2]⟩
    filter_upwards [this] with ζ hζ
    ext i
    simp only [s105FArr, hζ i]
  have hemb := s56_measurableEmbedding_pathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' hs'
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  have hgleft : ∀ c ∈ Set.range (s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s'),
      s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' (g c) = c := by
    rintro _ ⟨w, rfl⟩
    have := congrFun hg w
    simp only [Function.comp, id] at this
    rw [this]
  have hYcl := s105_Yc_law hS hb hT β⁻¹ hq P (P₂ : Measure Ω₂) η₀ Y (hY (b + T)).meas (hY (b + T)) s' hs' hη'
    (ℱ₂ := gfb4_aug (P₂ : Measure Ω₂) ℱ₂) hG' hG'c hG'z hG'm g hgm hgleft c'' hc''m hc''law hW
  -- laws and measurability of the two paths
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
  have hlawYc : law (P₂ : Measure Ω₂) (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
      (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
        (fun τ ζ => Gb (b + τ) ζ) ζ t)) =
      law P (processWindow ((wholeSpaceIndex d : ℕ) : ℝ) T b Y) := by
    rw [← hYcl]
    exact Measure.map_congr (s105_window_recon_ae hb hT0 (P₂ : Measure Ω₂) Gb G' s' hs' hGb.cont hG'c
      (fun τ hτ => (hGG' τ hτ).symm) (fun ζ => g (c'' ζ)))
  have hYhm : AEMeasurable (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
      (fun t => (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
        (Real.sqrt N) ρ X₂ ζ).evalA t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
          (fun τ ζ => Gb (b + τ) ζ) ζ t)) (P₂ : Measure Ω₂) := by
    have := gfb4_aemeasurable_windowPath (P₂ : Measure Ω₂) hT0
      (fun t ζ => (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
        (Real.sqrt N) ρ X₂ ζ).evalA t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
          (fun τ ζ => Gb (b + τ) ζ) ζ t)
      (fun t _ => ((s56_evalA_cont hT0 t).measurable.comp hk0m).add (hrecm t))
      (by
        filter_upwards [hrecc] with ζ hζ
        exact (HRS.MS.U9.u9_continuousOn_evalA hT0 _).add (continuousOn_iff_continuous_restrict.2 hζ))
    rwa [← s56_wpo_eq_windowPath] at this
  have hYcm : AEMeasurable (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
      (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
        (fun τ ζ => Gb (b + τ) ζ) ζ t)) (P₂ : Measure Ω₂) := by
    have := gfb4_aemeasurable_windowPath (P₂ : Measure Ω₂) hT0
      (fun t ζ => s56Ext hT0 (g (c'' ζ)) t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
          (fun τ ζ => Gb (b + τ) ζ) ζ t)
      (fun t _ => (s56Ext_meas hT0 _ (hgm.comp hc''m) t).add (hrecm t))
      (by
        filter_upwards [hrecc] with ζ hζ
        exact (s56Ext_cont hT0 (g (c'' ζ))).continuousOn.add (continuousOn_iff_continuous_restrict.2 hζ))
    rwa [← s56_wpo_eq_windowPath] at this
  have hΞP : AEMeasurable (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X (fun _ : ℝ => ρ)) P := by
    have e : flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X (fun _ : ℝ => ρ) =
        HRS.Uniform.windowPath b T (s105Xi ((wholeSpaceIndex d : ℕ) : ℝ) (Real.sqrt N) ρ X) := by
      funext ζ
      unfold flucPathW windowPathOf HRS.Uniform.windowPath s105Xi
      rfl
    rw [e]
    refine HRS.Uniform.Comp28.aemeasurable_windowPath_a P hb hT0 hτ' _ (fun t _ => ?_) ?_
    · unfold s105Xi
      exact (s56_xi_cont_config hd1 hm (Real.sqrt N) (by omega) (HRS.Whole.withDensityReal ρ)).measurable.comp
        (hX.adapted _)
    · filter_upwards [hX.cont] with ζ hζ
      exact s56_xi_cont_time hd1 hm (Real.sqrt N) (by omega) (T := b + T) (fun _ => ρ) (fun t _ => hS.hprob)
        (fun ψ _ _ => continuousOn_const) (fun t => X (Real.toNNReal t) ζ)
        (fun i => (hζ i).comp continuous_real_toNNReal)
  have hΞm : AEMeasurable (fun ζ => flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X
      (fun _ : ℝ => ρ) (π ζ)) (P₂ : Measure Ω₂) :=
    hΞP.comp_quasiMeasurePreserving hπtot.quasiMeasurePreserving
  have hlawΞ : law (P₂ : Measure Ω₂) (fun ζ => flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X
      (fun _ : ℝ => ρ) (π ζ)) = law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X (fun _ : ℝ => ρ)) :=
    HRS.GF.law_comp_mp hπtot hΞP
  have hΞeq : ∀ ζ, flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X (fun _ : ℝ => ρ) (π ζ) =
      windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => (s105K0 ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂ ζ).evalA t +
        reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => Mm (b + τ) ζ) ζ t + R₂ t ζ) := by
    intro ζ
    rw [s105_fluc_eq]
    refine s56_wpo_congr fun t ht => ?_
    have e : R₂ t ζ = s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂ Mm t ζ := if_pos ht
    rw [e]
    unfold s105R
    abel
  have hcmp := hCmp b hb Ω₂ (P₂ : Measure Ω₂) ℱ₂ (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
    ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂) hk0₂ Mm Sg₂ hMm₂ hMmm Gb Db hDb hGb hGm Sd
    (fun r ζ => traceNormForm (Sg₂ r ζ - Db r)) hdiff hcost hMm₂.cont hMm₂.zero hGb.cont hGb.zero R₂ hRc hRm
    (fun ζ => flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X (fun _ : ℝ => ρ) (π ζ))
    (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
      (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
        (fun τ ζ => Gb (b + τ) ζ) ζ t)) hΞm hYcm hYhm (Filter.Eventually.of_forall hΞeq)
  obtain ⟨hsm, hw1⟩ := hcmp
  rw [hlawΞ, hlawYc] at hsm hw1
  -- the covariance error
  have hT₂ : ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm (Sg₂ r ζ - Db r)))
      ∂(P₂ : Measure Ω₂) ≤ Wt := by
    obtain ⟨Bt, hBtid, hBtint⟩ := hBt
    set Fh : Ω → ℝ≥0∞ := fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm
      (hsCovForm (fun k : Fin N × Fin d => Real.sqrt (2 * β⁻¹ / N) • (fun (a' : Fin d) (r : ℝ) (x : Euc d) =>
        r2WindowFeature ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T
          (gradComp a') b r x) k.2 (mrrClamp (b + T) r) (X (Real.toNNReal (mrrClamp (b + T) r)) ζ k.1)) - Db r))
      with hFhdef
    have hFhm : Measurable Fh := s105_trace_meas hτ hS.hF β⁻¹ Db (fun u v => hDb.meas u v) ℱ X hfilt.progressive
    have hFh_eq : ∀ ζ, Fh ζ = ∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm (Bt r ζ)) := by
      intro ζ
      refine setLIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
      congr 2
      refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.sub_apply]
      have hh := s105_hsCov_eq (fun (a' : Fin d) (r : ℝ) (x : Euc d) => r2WindowFeature
        ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
        (b + T) β⁻¹ hq hN1 r (X (Real.toNNReal (mrrClamp (b + T) r)) ζ) u v
      beta_reduce at hh
      rw [hh, (s105Db_spec _ hS.hF _ β⁻¹ hq hr).1, hBtid r hr ζ u v, mrrClamp_of_mem hr]
    have hint : ∀ ζ, ∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm (Sg₂ r ζ - Db r)) =
        Fh (π ζ) := by
      intro ζ
      refine setLIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
      simp only [hSg₂def, hSg₁]
      unfold s105Phi
      simp only [mrrClamp_of_mem hr, hX₁def, hπdef]
    simp_rw [hint]
    rw [HRS.GF.lintegral_comp_mp hπtot hFhm.aemeasurable]
    simp_rw [hFh_eq]
    exact hBtint
  -- the remainder
  have hRint : ∫⁻ ζ, ‖windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => R₂ t ζ)‖ₑ ∂(P₂ : Measure Ω₂) ≤ F := by
    set Hp : Ω → ℝ≥0∞ := fun ζ => ⨆ n : ℕ, l2NormE (fun α : MultiIndex d =>
      -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), r2CommForcingMov
        ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) s ((wholeSpaceIndex d : ℕ) : ℝ) (fun _ => ρ) X α
        (b + (s' n)) r ζ) with hHpdef
    have hHpm : Measurable Hp := by
      refine Measurable.iSup fun n => ?_
      unfold l2NormE
      refine Measurable.pow_const (Measurable.ennreal_tsum fun α => ?_) _
      have hcl := hS.hcl α (b + s' n) (by linarith [(s' n).2.1])
      have hf := s105_force_meas s ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (t := b + s' n)
        (by linarith [(s' n).2.1]) hcl hS.hprob ℱ X hfilt.progressive
      exact ((measurable_const.mul hf).pow_const 2).ennreal_ofReal
    have hΦ₁ : ∀ T' : ℝ, IsHSIntegrand P₁ ℱ₁ T' (s105Phi (fun a' r x => r2WindowFeature
        ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
        (b + T) β⁻¹ X₁) := fun τ => s105_phi_isHS hτ hS.hF N β⁻¹ P₁ ℱ₁ X₁ hF₁.progressive τ
    have hRb₁ := s105_R_bound_dense hd hs0 hsd ha hβ hb hT hρ hS hN1 hm P₁ (fun z => X₀ (π₁ z))
      (fun t z => W t (π₁ z)) X₁ hX₁ ℱ₁ (fun t z k => W' t (π₁ z) k) hF₁ M₁ hΦ₁ hM₁ito s' hs'
    have hpt : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ‖windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => R₂ t ζ)‖ₑ ≤
        Hp (π ζ) := by
      filter_upwards [hπ.quasiMeasurePreserving.ae hRb₁] with ζ hζ
      have := gfb4_windowPath_enorm_le T R₂ ζ (Hp (π ζ)) (fun t ht => by
        simp only [hR₂def, if_pos ht]
        exact hζ t ht)
      rwa [← s56_wpo_eq_windowPath (m := ((wholeSpaceIndex d : ℕ) : ℝ)) (T := T)
        (fun t ζ => R₂ t ζ) |> fun e => congrFun e ζ] at this
    calc ∫⁻ ζ, ‖windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => R₂ t ζ)‖ₑ ∂(P₂ : Measure Ω₂)
        ≤ ∫⁻ ζ, Hp (π ζ) ∂(P₂ : Measure Ω₂) := lintegral_mono_ae hpt
      _ = ∫⁻ ζ, Hp ζ ∂P := HRS.GF.lintegral_comp_mp hπtot hHpm.aemeasurable
      _ ≤ ∫⁻ ζ, ⨆ u ∈ Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u), r2CommForcingMov
            ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) s ((wholeSpaceIndex d : ℕ) : ℝ) (fun _ => ρ) X α
            (b + u) r ζ) ∂P := by
        refine lintegral_mono fun ζ => iSup_le fun n => ?_
        exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) => l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u), r2CommForcingMov
            ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) s ((wholeSpaceIndex d : ℕ) : ℝ) (fun _ => ρ) X α
            (b + u) r ζ)) (s' n : ℝ) (s' n).2
      _ ≤ F := hFb
  -- the initial coupling cost
  have hεint : ∫⁻ ζ, ‖windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
        (fun t => (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
          (Real.sqrt N) ρ X₂ ζ).evalA t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
            (fun τ ζ => Gb (b + τ) ζ) ζ t) -
      windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
        (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
          (fun τ ζ => Gb (b + τ) ζ) ζ t)‖ₑ ∂(P₂ : Measure Ω₂) =
      ∫⁻ ζ, ENNReal.ofReal ‖r2InitCouplingPath ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T (HRS.Whole.withDensityReal ρ) b X₀ η₀ ζ‖ ∂P := by
    have hHm := s105Hfun_meas ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
      (Real.sqrt N) hS.hprob hS.hρ2 hT0 hN1 (τ₀ := b + T) (by linarith) hb hS.hF g hgm
    have hpt : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ‖windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
        (fun t => (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
          (Real.sqrt N) ρ X₂ ζ).evalA t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
            (fun τ ζ => Gb (b + τ) ζ) ζ t) -
      windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
        (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
          (fun τ ζ => Gb (b + τ) ζ) ζ t)‖ₑ =
        s105Hfun ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
          (Real.sqrt N) (HRS.Whole.withDensityReal ρ) hT0 g (X 0 (π₁ (π₂ ζ))) (c' (π₂ ζ)) := by
      filter_upwards [hrecc] with ζ hζ
      have hc1 : ContinuousOn (fun t => (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
          ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂ ζ).evalA t +
          reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => Gb (b + τ) ζ) ζ t) (Set.Icc 0 T) :=
        (HRS.MS.U9.u9_continuousOn_evalA hT0 _).add (continuousOn_iff_continuous_restrict.2 hζ)
      have hc2 : ContinuousOn (fun t => s56Ext hT0 (g (c'' ζ)) t +
          reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => Gb (b + τ) ζ) ζ t) (Set.Icc 0 T) :=
        (s56Ext_cont hT0 (g (c'' ζ))).continuousOn.add (continuousOn_iff_continuous_restrict.2 hζ)
      have : windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
        (fun t => (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
          (Real.sqrt N) ρ X₂ ζ).evalA t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
            (fun τ ζ => Gb (b + τ) ζ) ζ t) -
        windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
        (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
          (fun τ ζ => Gb (b + τ) ζ) ζ t) =
          s56EvalPath hT0 (s105K0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
            ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X₂ ζ) - g (c'' ζ) := by
        refine ContinuousMap.ext fun t => ?_
        show (show C(Set.Icc (0 : ℝ) T, OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) from windowPathOf _ _ 0 _) t -
          (show C(Set.Icc (0 : ℝ) T, OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) from windowPathOf _ _ 0 _) t =
          (show C(Set.Icc (0 : ℝ) T, OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) from s56EvalPath hT0 _) t -
            (show C(Set.Icc (0 : ℝ) T, OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) from g (c'' ζ)) t
        rw [s56_wpo_apply hc1 t, s56_wpo_apply hc2 t, s56EvalPath_apply, s56Ext_of_mem hT0 _ t.2]
        abel
      rw [this]
      rfl
    rw [lintegral_congr_ae hpt]
    have h1 : ∫⁻ ζ, s105Hfun ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
        (Real.sqrt N) (HRS.Whole.withDensityReal ρ) hT0 g (X 0 (π₁ (π₂ ζ))) (c' (π₂ ζ)) ∂(P₂ : Measure Ω₂) =
        ∫⁻ z, s105Hfun ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
          (Real.sqrt N) (HRS.Whole.withDensityReal ρ) hT0 g (X 0 (π₁ z)) (c' z) ∂P₁ :=
      HRS.GF.lintegral_comp_mp hπ (f := fun z => s105Hfun ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) (HRS.Whole.withDensityReal ρ) hT0 g (X 0 (π₁ z)) (c' z))
        ((hHm.comp (hX0m.prodMk hc'm)).aemeasurable)
    have h2 : ∫⁻ z, s105Hfun ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
          (Real.sqrt N) (HRS.Whole.withDensityReal ρ) hT0 g (X 0 (π₁ z)) (c' z) ∂P₁ =
        ∫⁻ ζ, s105Hfun ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b
          (Real.sqrt N) (HRS.Whole.withDensityReal ρ) hT0 g (X 0 ζ) (Ψt ζ) ∂P := by
      rw [← lintegral_map hHm (hX0m.prodMk hc'm), hlaw₁, lintegral_map hHm ((hX.adapted 0).prodMk hΨtm)]
    rw [h1, h2]
    obtain ⟨-, hrangeΨ⟩ := s105_D_range hS hb hT β⁻¹ hq P (P₂ : Measure Ω₂) η₀ Y (hY (b + T)).meas (hY (b + T))
      s' hs' hη' (ℱ₂ := gfb4_aug (P₂ : Measure Ω₂) ℱ₂) hG' hG'c hG'z hG'm
    refine lintegral_congr_ae ?_
    filter_upwards [hX.init, hΨae, hrangeΨ, hcontc] with ζ h1 h2 h3 h4
    rw [h1, ← h2]
    obtain ⟨w, hw⟩ := h3
    have hmemℓ : ∀ n : ℕ, Memℓp (fun α => s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ (n, α)) 2 := by
      intro n
      rw [← hw]
      show Memℓp (fun α => OscDual.coord (OscPath.at' w (s' n)) α) 2
      exact (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).2
        (by simpa using OscDual.coord_sq_summable' (OscPath.at' w (s' n)))
    have hpath := s105_eps_path hS hb hT hN1 s' hs' g (X₀ ζ) (η₀ ζ)
      (s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ)
      (fun i => rfl) hmemℓ (by rw [← hw]; exact hgleft _ ⟨w, rfl⟩) hm h4
    unfold s105Hfun
    rw [hpath, ← ofReal_norm]
    rfl
  refine ⟨?_, ?_⟩
  · calc _ ≤ _ := hsm
      _ ≤ ENNReal.ofReal Cs * Wt + F + _ := by
        rw [hεint] at *
        gcongr
  · refine hw1.trans ?_
    rw [hεint]
    gcongr

end HRS.MS.R2GenInit
