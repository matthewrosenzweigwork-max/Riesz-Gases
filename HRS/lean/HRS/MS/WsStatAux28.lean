import HRS.MS.WsStatAux27

/-!
# S21 packet I-6: the stationary master comparison, part 1 (coupling space and the abstract comparison)

`s21_master_core` produces, from the particle data, the coupling space `(Ω₂, P₂)` with the Gaussian martingale `Gb` and states the two
abstract bounds with the path law of `k0path + window (recon Gb)`.  The identification of that law with a convolution and the
probability measure `Γ` are done in `s21_master` (`WsStatAux29`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.GF HRS.Uniform HRS.Whole.AppendixA
open HRS (Euc)

variable {d : ℕ}

theorem s21_master_core (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 2 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    {Cs Cw1 Cw2 : ℝ} (hCmp : S56CompareHyp (d := d) b.m b.T Cs Cw1 Cw2)
    {Ctr' : ℝ} (hCtr0 : 0 ≤ Ctr') (hTr : S56TraceHyp b Ctr') (M₂ : ℝ) (hM₂0 : 0 ≤ M₂)
    (hM1 : b.M = -1) {ρ : Euc d → ℝ} (hρ' : ∀ t, S.ρ N t = ρ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (hstat : ∀ t ∈ Set.Icc (0 : ℝ) b.T, P.map (X (Real.toNNReal t)) = P.map (X 0))
    (hν1 : Integrable (fun x : Euc d => ‖x‖) (HRS.Whole.meanEmpirical (P.map (X 0))))
    (hfub : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IntegrableOn (fun r => ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P)
          (Set.Icc 0 t) ∧
        ∫ ζ, (∫ r in Set.Icc (0 : ℝ) t,
            commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ) ∂P =
          ∫ r in Set.Icc (0 : ℝ) t, ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P ∧
        Integrable (fun ζ => ∫ r in Set.Icc (0 : ℝ) t,
          commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ) P)
    (hint : ∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IntegrableOn (fun r => commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ)
        (Set.Icc 0 t))
    (hmom : ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      ∫⁻ ζ, ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal t) ζ))
        (fun x => ‖x‖ ^ 2)) ∂P ≤ ENNReal.ofReal M₂ ∧
      ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) (fun x => ‖x‖ ^ 2)) ≤
        ENNReal.ofReal M₂)
    (hE1 : S.energyMomentE N 1 P X ≠ ⊤) {ER : ℝ≥0∞}
    (hrem : (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
        s21Gfun b S ρ P X t α ζ)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤ ER) :
    ∃ (Ω₂ : Type) (mΩ₂ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂) (_ : IsProbabilityMeasure P₂)
      (π₂ : Ω₂ → Ω) (_ : MeasurePreserving π₂ P₂ P) (ℱ₂ : Filtration ℝ mΩ₂)
      (Gb : ℝ → Ω₂ → KSpace d b.m b.T),
      IsHilbertMartingaleWithCovariation P₂ ℱ₂ b.T Gb (fun r _ => s56Db b S N hOM (s56_hS b S N) (S.q N) (s56_q_nonneg b S N (by omega)) r) ∧
      (∀ t, Measurable (Gb t)) ∧
      Indep (MeasurableSpace.comap (fun ζ => s21K0c S X (HRS.Whole.meanEmpirical (P.map (X 0))) (π₂ ζ))
          inferInstance)
        (⨆ τ ∈ Set.Icc (0 : ℝ) b.T, MeasurableSpace.comap (Gb τ) inferInstance) P₂ ∧
      (ENNReal.ofReal (smoothDist 2
          (law P (s21XiPath S X (HRS.Whole.meanEmpirical (P.map (X 0)))))
          (law P₂ (fun ζ => windowPathOf b.m b.T 0 (fun t =>
            (s21K0c S X (HRS.Whole.meanEmpirical (P.map (X 0))) (π₂ ζ)).evalA t +
              reconstructPath b.m b.T Gb ζ t)))) ≤
        ENNReal.ofReal Cs * ENNReal.ofReal (Ctr' * S.q N *
          generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N) + ER) ∧
      (wassersteinE 1 (law P (s21XiPath S X (HRS.Whole.meanEmpirical (P.map (X 0)))))
          (law P₂ (fun ζ => windowPathOf b.m b.T 0 (fun t =>
            (s21K0c S X (HRS.Whole.meanEmpirical (P.map (X 0))) (π₂ ζ)).evalA t +
              reconstructPath b.m b.T Gb ζ t))) ≤
        ENNReal.ofReal Cw1 * (ENNReal.ofReal (Ctr' * S.q N *
          generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)) ^ (1 / 2 : ℝ) + ER) := by
  classical
  have hT0 : 0 ≤ b.T := hbv.hT.le
  have hN1 : 1 ≤ N := by omega
  have hq : 0 ≤ S.q N := s56_q_nonneg b S N hN1
  have hS := s56_hS b S N
  have hXm : ∀ t, Measurable (X t) := hX.adapted
  haveI hP0 : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).2 inferInstance
  set νb : Measure (Euc d) := HRS.Whole.meanEmpirical (P.map (X 0)) with hνb
  haveI hνbp : IsProbabilityMeasure νb := HRS.Whole.meanEmpirical_isProbabilityMeasure _ hN1
  -- the particle martingale
  obtain ⟨M₁, hM₁ito, hM₁⟩ := s56_particle_martingale b hbv S N hN1 hC (S.q N) hq P ℱ W' X hF.brownian
    hF.progressive
  set Db := s56Db b S N hOM hS (S.q N) hq with hDbdef
  have hDb : IsDetCovDensity b.T Db := s56Db_isDet b hbv S N hC hOM hS (S.q N) hq
  set Sg₁ : ℝ → Ω → (KSpace d b.m b.T →L[ℝ] KSpace d b.m b.T →L[ℝ] ℝ) :=
    fun r z => hsCovForm (s56Phi (S.coeff N) b.m b.T (S.q N) X r z) with hSg₁
  -- the remainder on `P`
  have hcoord : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂P,
      OscDual.coord (s21Rt S X νb M₁ t ζ) α = s21Gfun b S ρ P X t α ζ :=
    fun t ht α => s21_centered_coord b hbv S hN hC hM1 hρ' P hX ℱ W' hF M₁ hM₁ito hstat hν1 hfub hint ht α
  have hRbd := s21_Rt_bound b hbv S hN1 P X νb M₁ hX.cont hM₁ito.cont (s21Gfun b S ρ P X) hcoord
  set R₁ : ℝ → Ω → OscDual d b.m := fun t ζ =>
    if t ∈ Set.Icc (0 : ℝ) b.T then s21Rt S X νb M₁ t ζ else 0 with hR₁def
  have hMm₁m : ∀ t, Measurable (M₁ t) := fun t => HRS.Uniform.Q07c.measurable_of_isHM hM₁ t
  have hR₁m : ∀ t, Measurable (R₁ t) := fun t => by
    by_cases ht : t ∈ Set.Icc (0 : ℝ) b.T
    · have e : R₁ t = s21Rt S X νb M₁ t := funext fun ζ => if_pos ht
      rw [e]
      exact s21_Rt_meas b hbv S hN1 hC X hXm νb hν1 M₁ hMm₁m t
    · have e : R₁ t = fun _ => (0 : OscDual d b.m) := funext fun ζ => if_neg ht
      rw [e]
      exact measurable_const
  have hR₁c : ∀ᵐ ζ ∂P, ContinuousOn (fun t => R₁ t ζ) (Set.Icc 0 b.T) := by
    filter_upwards [hX.cont] with ζ hζ
    refine (s21_Rt_cont b hbv S hN1 X νb M₁ ζ hζ (hM₁ito.cont ζ).continuousOn).congr fun t ht => ?_
    simp only [hR₁def, if_pos ht]
  set Rpath : Ω → OscPath d b.m b.T := fun ζ => windowPathOf b.m b.T 0 (fun t => R₁ t ζ) with hRpath
  have hRpm : AEMeasurable Rpath P := by
    have := gfb4_aemeasurable_windowPath P hT0 R₁ (fun t _ => hR₁m t) hR₁c
    rwa [← s56_wpo_eq_windowPath] at this
  have hRpbd : ∀ᵐ ζ ∂P, ‖Rpath ζ‖ₑ ≤ ⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
      s21Gfun b S ρ P X t α ζ) := by
    filter_upwards [hRbd] with ζ hζ
    have := gfb4_windowPath_enorm_le b.T (fun t ζ => R₁ t ζ) ζ _ (fun t ht => by
      simp only [hR₁def, if_pos ht]
      exact hζ t ht)
    have e : windowPath 0 b.T (fun t ζ => R₁ t ζ) ζ = Rpath ζ :=
      (congrFun (s56_wpo_eq_windowPath (m := b.m) (T := b.T) (fun t ζ => R₁ t ζ)) ζ).symm
    rw [← e]
    exact this
  have hRL1 : ∫⁻ ζ, ‖Rpath ζ‖ₑ ∂P ≤ ER := by
    have h1 := s56_lintegral_le_sqrt' P (g := fun ζ => ‖Rpath ζ‖ₑ) hRpm.enorm
    rw [measure_univ, ENNReal.one_rpow, one_mul] at h1
    refine h1.trans (le_trans ?_ hrem)
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    refine lintegral_mono_ae ?_
    filter_upwards [hRpbd] with ζ hζ
    exact ENNReal.rpow_le_rpow hζ (by norm_num)
  -- the Gaussian coupling
  obtain ⟨Ω₂, mΩ₂, P₂, π₂, ℱ₂, Gb, Sd, hc⟩ :=
    gff_adapted_coupling_trace P ℱ b.T hT0 ⟨ℱ 0, le_rfl⟩ M₁ Sg₁ hM₁ Db hDb
  haveI : IsProbabilityMeasure (P₂ : Measure Ω₂) := inferInstance
  have hπ : MeasurePreserving π₂ (P₂ : Measure Ω₂) P := hc.preserving
  set X₂ : ℝ≥0 → Ω₂ → EucConfig d N := fun t ζ => X t (π₂ ζ) with hX₂def
  have hX₂ : IsWholeStrongSolution (P₂ : Measure Ω₂) (S.dyn N) b.T (fun ζ => X₀ (π₂ ζ))
      (fun t ζ => W t (π₂ ζ)) X₂ := s56_strong_comp hπ hX
  have hXm₂ : ∀ t, Measurable (X₂ t) := fun t => (hX.adapted t).comp hπ.measurable
  have hπ' : ∀ i : ℝ, Measurable[ℱ₂ i, ℱ i] π₂ := fun i => Measurable.of_comap_le (hc.filtration i)
  have hprog₂ : IsProgressive ℱ₂ (ofNNRealTime X₂) := fun i =>
    (hF.progressive i).comp (measurable_fst.prodMk ((hπ' i).comp measurable_snd))
  have hinj₂ : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      Function.Injective (X₂ (Real.toNNReal t) ζ) := by
    filter_upwards [hX₂.no_collision] with ζ hζ t ht
    have := hζ (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
    intro i j hij
    by_contra hne
    exact this ⟨i, j, hne, hij⟩
  have hEeq : ∀ p : ℝ, S.energyMomentE N p (P₂ : Measure Ω₂) X₂ = S.energyMomentE N p P X := fun p =>
    s56_energyMoment_comp b hbv S (by omega) hπ X (fun t => hX.adapted t) p
  -- second moments on the coupling space
  have hsm_meas : Measurable fun x : EucConfig d N => secondMomentOf (HRS.Whole.empirical x) := by
    have e : (fun x : EucConfig d N => secondMomentOf (HRS.Whole.empirical x)) =
        fun x => (N : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := by
      funext x
      unfold secondMomentOf
      exact HRS.Whole.pair_empirical (by omega) x _
    rw [e]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).norm).pow_const 2)
  have hmom₂ : ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      ∫⁻ ζ, ENNReal.ofReal (secondMomentOf (HRS.Whole.empirical (X₂ (Real.toNNReal t) ζ)))
        ∂(P₂ : Measure Ω₂) ≤ ENNReal.ofReal M₂ ∧
      ENNReal.ofReal (secondMomentOf (HRS.Whole.withDensityReal (S.ρ N t))) ≤ ENNReal.ofReal M₂ := by
    intro t ht
    obtain ⟨h1, h2⟩ := hmom t ht
    refine ⟨?_, h2⟩
    have hm : Measurable fun ζ => ENNReal.ofReal (secondMomentOf
        (HRS.Whole.empirical (X (Real.toNNReal t) ζ))) :=
      ENNReal.measurable_ofReal.comp (hsm_meas.comp (hX.adapted _))
    have := HRS.GF.lintegral_comp_mp hπ hm.aemeasurable
    exact this.trans_le h1
  -- the trace bound
  have htrace : ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) b.T, ENNReal.ofReal (traceNormForm
        (hsCovForm (s56Phi (S.coeff N) b.m b.T (S.q N) X₂ r ζ) - Db r))) ∂(P₂ : Measure Ω₂) ≤
      ENNReal.ofReal (Ctr' * S.q N * generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N) := by
    have h := hTr S N hN (S.q N) hq M₂ hM₂0 (P₂ : Measure Ω₂) X₂ hinj₂
      (s56_energy_aemeas b hbv S N _ ℱ₂ X₂ hprog₂) (s56_mm_aemeas (by omega) _ ℱ₂ X₂ hprog₂ hT0)
      hmom₂ (by rw [hEeq 1]; exact hE1)
      (fun r ζ => hsCovForm (s56Phi (S.coeff N) b.m b.T (S.q N) X₂ r ζ)) Db
      (fun r hr ζ u v => by
        have h0 := s56_hsCov_eq b.m b.T (S.q N) hq (S.coeff N) hN1 r (X₂ (Real.toNNReal r) ζ) u v
        unfold s56Phi
        rw [mrrClamp_of_mem hr] at h0 ⊢
        exact h0)
      (fun r hr u v => (s56Db_spec b S N hOM hS (S.q N) hq hr).1 u v)
    rwa [hEeq 1] at h
  -- martingales on the coupling space
  set Mm : ℝ → Ω₂ → KSpace d b.m b.T := fun τ ζ => M₁ τ (π₂ ζ) with hMmdef
  set Sg₂ : ℝ → Ω₂ → (KSpace d b.m b.T →L[ℝ] KSpace d b.m b.T →L[ℝ] ℝ) :=
    fun r ζ => Sg₁ r (π₂ ζ) with hSg₂def
  have hMm₂ : IsHilbertMartingaleWithCovariation (P₂ : Measure Ω₂) ℱ₂ b.T Mm Sg₂ :=
    hc.martingale b.T hT0 le_rfl
  have hMmm : ∀ t, Measurable (Mm t) := fun t => (hMm₁m t).comp hπ.measurable
  have hGb : IsHilbertMartingaleWithCovariation (P₂ : Measure Ω₂) ℱ₂ b.T Gb (fun r _ => Db r) := by
    have h1 := hc.gaussian b.T hT0 le_rfl
    have e : (fun (r : ℝ) (_ : Ω₂) => if ENNReal.ofReal r ≤ ENNReal.ofReal b.T then Db r else 0) =
        fun r _ => Db r := by
      funext r _
      by_cases hr : r ≤ b.T
      · rw [if_pos (ENNReal.ofReal_le_ofReal hr)]
      · rw [if_neg ((ENNReal.ofReal_le_ofReal_iff hT0).not.2 hr)]
        exact (s56Db_zero b S N hOM hS (S.q N) hq (fun h => hr h.2)).symm
    rw [e] at h1
    exact h1
  have hGm : ∀ t, Measurable (Gb t) := fun t =>
    gfb4_measurable_of_weak fun x => (((hGb.martingale x).stronglyAdapted t).mono (ℱ₂.le t)).measurable
  have hdiff := gf_coupling_difference hc hT0
  have hcost := gf_coupling_cost_le hc hT0
  -- the initial state
  have hk0cfg : Measurable fun x : EucConfig d N =>
      s56k0 (S.coeff N) b.m b.T (S.σ N) (HRS.Whole.empirical x) νb :=
    s21_K0c_meas b hbv S hN1 hC (Ω := EucConfig d N) (fun _ x => x) measurable_id νb hν1
  have hk0₁ : Measurable[ℱ 0] (s21K0c S X νb) := hk0cfg.comp (hF.adapted 0)
  have hπ0 : Measurable[ℱ₂ 0, ℱ 0] π₂ := hπ' 0
  have hk0₂ : Measurable[ℱ₂ 0] (s21K0c S X₂ νb) := hk0₁.comp hπ0
  have hk0m : Measurable (s21K0c S X₂ νb) := hk0cfg.comp (hXm₂ 0)
  -- the remainder on the coupling space
  set R₂ : ℝ → Ω₂ → OscDual d b.m := fun t ζ => R₁ t (π₂ ζ) with hR₂def
  have hRm : ∀ t, Measurable (R₂ t) := fun t => (hR₁m t).comp hπ.measurable
  have hRc : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ContinuousOn (fun t => R₂ t ζ) (Set.Icc 0 b.T) :=
    hπ.quasiMeasurePreserving.ae hR₁c
  -- the particle path
  have hΞeq : ∀ ζ, s21XiPath S X νb (π₂ ζ) =
      windowPathOf b.m b.T 0 (fun t => (s21K0c S X₂ νb ζ).evalA t +
        reconstructPath b.m b.T Mm ζ t + R₂ t ζ) := by
    intro ζ
    unfold s21XiPath
    refine s56_wpo_congr fun t ht => ?_
    have e : R₂ t ζ = s21Rt S X νb M₁ t (π₂ ζ) := if_pos ht
    rw [e]
    unfold s21Rt
    show s21Xi S X νb t (π₂ ζ) = (s21K0c S X νb (π₂ ζ)).evalA t + reconstructPath b.m b.T M₁ (π₂ ζ) t +
      (s21Xi S X νb t (π₂ ζ) - (s21K0c S X νb (π₂ ζ)).evalA t - reconstructPath b.m b.T M₁ (π₂ ζ) t)
    abel
  have hΞm : AEMeasurable (s21XiPath S X νb) P := by
    have h := gfb4_aemeasurable_windowPath P hT0 (s21Xi S X νb)
      (fun t _ => s21_Xi_meas b hbv S (by omega) X hXm νb t)
      (by
        filter_upwards [hX.cont] with ζ hζ
        exact (s21_Xi_cont b hbv S (by omega) X νb ζ hζ).continuousOn)
    rw [← s56_wpo_eq_windowPath] at h
    exact h
  have hΞm₂ : AEMeasurable (fun ζ => s21XiPath S X νb (π₂ ζ)) (P₂ : Measure Ω₂) :=
    hΞm.comp_quasiMeasurePreserving hπ.quasiMeasurePreserving
  have hlawΞ : law (P₂ : Measure Ω₂) (fun ζ => s21XiPath S X νb (π₂ ζ)) = law P (s21XiPath S X νb) :=
    HRS.GF.law_comp_mp hπ hΞm
  -- the comparison path
  have hrecm : ∀ t, Measurable fun ζ => reconstructPath b.m b.T Gb ζ t := fun t => by
    unfold reconstructPath
    exact (((s56_evalA_cont hT0 t).measurable.comp (hGm b.T)).sub
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm b.T))).add
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm t))
  have hrecc : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), Continuous fun t : Set.Icc (0 : ℝ) b.T =>
      reconstructPath b.m b.T Gb ζ t := by
    filter_upwards [hGb.cont] with ζ hζ
    exact HRS.MS.U9.u9_continuous_recon hT0 Gb ζ hζ
  have hYhm : AEMeasurable (fun ζ => windowPathOf b.m b.T 0 (fun t =>
      (s21K0c S X₂ νb ζ).evalA t + reconstructPath b.m b.T Gb ζ t)) (P₂ : Measure Ω₂) := by
    have := gfb4_aemeasurable_windowPath (P₂ : Measure Ω₂) hT0
      (fun t ζ => (s21K0c S X₂ νb ζ).evalA t + reconstructPath b.m b.T Gb ζ t)
      (fun t _ => ((s56_evalA_cont hT0 t).measurable.comp hk0m).add (hrecm t))
      (by
        filter_upwards [hrecc] with ζ hζ
        exact (HRS.MS.U9.u9_continuousOn_evalA hT0 _).add (continuousOn_iff_continuous_domRestrict.2 hζ))
    rwa [← s56_wpo_eq_windowPath] at this
  have hcmp := hCmp Ω₂ (P₂ : Measure Ω₂) ℱ₂ (s21K0c S X₂ νb) hk0₂ Mm Sg₂ hMm₂ hMmm Gb Db hDb hGb hGm Sd
    (fun r ζ => traceNormForm (Sg₂ r ζ - Db r)) hdiff hcost hMm₂.cont hMm₂.zero hGb.cont hGb.zero R₂ hRc hRm
    (fun ζ => s21XiPath S X νb (π₂ ζ))
    (fun ζ => windowPathOf b.m b.T 0 (fun t => (s21K0c S X₂ νb ζ).evalA t +
      reconstructPath b.m b.T Gb ζ t))
    hΞm₂ hYhm hYhm (Filter.Eventually.of_forall hΞeq)
  obtain ⟨hsm, hw1, -⟩ := hcmp
  rw [hlawΞ] at hsm hw1
  have hRint : ∫⁻ ζ, ‖windowPathOf b.m b.T 0 (fun t => R₂ t ζ)‖ₑ ∂(P₂ : Measure Ω₂) ≤ ER := by
    have := HRS.GF.lintegral_comp_mp hπ (f := fun ζ => ‖Rpath ζ‖ₑ) hRpm.enorm
    exact this.trans_le hRL1
  have hzero : ∀ ζ, ‖windowPathOf b.m b.T 0 (fun t => (s21K0c S X₂ νb ζ).evalA t +
      reconstructPath b.m b.T Gb ζ t) - windowPathOf b.m b.T 0 (fun t => (s21K0c S X₂ νb ζ).evalA t +
      reconstructPath b.m b.T Gb ζ t)‖ₑ = 0 := fun ζ => by simp
  have hT₂ : ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) b.T, ENNReal.ofReal (traceNormForm (Sg₂ r ζ - Db r)))
      ∂(P₂ : Measure Ω₂) ≤ ENNReal.ofReal (Ctr' * S.q N *
        generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N) := htrace
  refine ⟨Ω₂, mΩ₂, P₂, inferInstance, π₂, hπ, ℱ₂, Gb, hGb, hGm,
    gf_coupling_indep hc hT0 (s21K0c S X νb) hk0₁, ?_, ?_⟩
  · simp only [hzero, lintegral_zero, add_zero] at hsm
    exact hsm.trans (add_le_add (mul_le_mul' le_rfl hT₂) hRint)
  · have e1 : ∀ ζ, ENNReal.ofReal (‖windowPathOf b.m b.T 0 (fun t => (s21K0c S X₂ νb ζ).evalA t +
        reconstructPath b.m b.T Gb ζ t) - windowPathOf b.m b.T 0 (fun t => (s21K0c S X₂ νb ζ).evalA t +
        reconstructPath b.m b.T Gb ζ t)‖ ^ (1 : ℝ)) = 0 := fun ζ => by simp
    simp only [e1, lintegral_zero] at hw1
    simp only [Real.rpow_one, ENNReal.rpow_one, div_one, add_zero] at hw1
    refine hw1.trans (add_le_add ?_ hRint)
    exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hT₂ (by norm_num))

end HRS.MS.S21
