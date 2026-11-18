import HRS.MS.WsStatAux28
import HRS.Main.T25Aux8

/-!
# S21 packet I-7: the stationary master comparison (convolution form)

`s21_master`: with `gamma0` any probability measure on the path space `C([0,T];B_m)`, there is a probability measure `Gamma` (the path law
of the Gaussian martingale `T G`; its finite-dimensional laws are the Gaussian ones with covariance `noiseCovW`) such that

* `d_2(law Xi, gamma0 * Gamma) <= Cs (Ctr' q w_N) + ER + eps_s`,
* `W_1(law Xi, gamma0 * Gamma) <= Cw1 (Ctr' q w_N)^{1/2} + ER + eps_w`,

where `Xi = s21XiPath` is the centred field path, `ER` bounds the `L^2` norm of `sup_t' ||(-(sigma/2) int (c - E c))||_{l^2}`
(`field_remainder_centered`), and `eps_s`, `eps_w` bound the distances of the centred initial path from `gamma0`.
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

theorem s21_recon_fdd (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (hq : 0 ≤ S.q N) {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    {ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›} {G : ℝ → Ω₂ → KSpace d b.m b.T}
    (hG : IsHilbertMartingaleWithCovariation P₂ ℱ₂ b.T G (fun r _ => s56Db b S N hOM hS (S.q N) hq r))
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) b.T) (αs : Fin p → MultiIndex d) :
    P₂.map (fun ζ => (WithLp.toLp 2 fun a => OscDual.coord (OscPath.at'
        (windowPathOf b.m b.T 0 (fun t => reconstructPath b.m b.T G ζ t)) ⟨ts a, hts a⟩) (αs a) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a c => noiseCovW (S.coeff N) (S.q N) (ts a) (ts c)
        (oscTestFun b.m (αs a)) (oscTestFun b.m (αs c))) := by
  classical
  have hT0 : 0 ≤ b.T := hbv.hT.le
  obtain ⟨G', hG', hG'c, hG'z, hGG'⟩ := gfb4_modify P₂ ℱ₂ hT0 G
    (s56Db b S N hOM hS (S.q N) hq) (fun σ hσ => s56Db_zero b S N hOM hS (S.q N) hq hσ) hG
  have hG'm : ∀ t, Measurable (G' t) := fun t => HRS.Uniform.Q07c.measurable_of_isHM hG' t
  have h := s56_Gb_fdd b hbv S N hC hOM hS (S.q N) hq hG' hG'c hG'z hG'm ts hts αs
  rw [← h]
  refine Measure.map_congr ?_
  have h1 : ∀ a : Fin p, ∀ᵐ ζ ∂P₂, OscDual.coord (reconstructPath b.m b.T G ζ (ts a)) (αs a) =
      inner ℝ (G (ts a) ζ) (HRS.MS.S52.s52y1 b.m b.T (ts a) (αs a)) := fun a =>
    s56_recon_coord_eq b hbv S N hC hOM hS (S.q N) hq hG (hts a) (αs a)
  have h2 : ∀ a : Fin p, ∀ᵐ ζ ∂P₂, G (ts a) ζ = G' (ts a) ζ := fun a => (hGG' _ (hts a)).symm
  filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 h2, hG.cont] with ζ e1 e2 hc
  have hrc : ContinuousOn (fun t => reconstructPath b.m b.T G ζ t) (Set.Icc 0 b.T) :=
    continuousOn_iff_continuous_domRestrict.2 (HRS.MS.U9.u9_continuous_recon hT0 G ζ hc)
  ext a
  simp only
  have := s56_wpo_apply (m := b.m) (T := b.T) (f := fun t => reconstructPath b.m b.T G ζ t) hrc ⟨ts a, hts a⟩
  unfold OscPath.at'
  rw [this]
  show OscDual.coord (reconstructPath b.m b.T G ζ (ts a)) (αs a) = _
  rw [e1 a, e2 a]

theorem s21_master (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 2 ≤ N)
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
        s21Gfun b S ρ P X t α ζ)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤ ER)
    (γ0 : Measure (OscPath d b.m b.T)) [IsProbabilityMeasure γ0] {εs : ℝ} {εw : ℝ≥0∞}
    (hsm0 : smoothDist 2 (law P (s21Path0 hbv.hT.le S X (HRS.Whole.meanEmpirical (P.map (X 0))))) γ0 ≤ εs)
    (hw0 : wassersteinE 1 (law P (s21Path0 hbv.hT.le S X (HRS.Whole.meanEmpirical (P.map (X 0))))) γ0 ≤ εw) :
    ∃ Γ : Measure (OscPath d b.m b.T), IsProbabilityMeasure Γ ∧
      (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) b.T) (αs : Fin p → MultiIndex d),
        Γ.map (fun w : OscPath d b.m b.T => (WithLp.toLp 2 fun a => OscDual.coord
            (OscPath.at' w ⟨ts a, hts a⟩) (αs a) : EuclideanSpace ℝ (Fin p))) =
          multivariateGaussian 0 (Matrix.of fun a c => noiseCovW (S.coeff N) (S.q N) (ts a) (ts c)
            (oscTestFun b.m (αs a)) (oscTestFun b.m (αs c)))) ∧
      ENNReal.ofReal (smoothDist 2 (law P (s21XiPath S X (HRS.Whole.meanEmpirical (P.map (X 0)))))
          ((γ0.prod Γ).map (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2))) ≤
        ENNReal.ofReal Cs * ENNReal.ofReal (Ctr' * S.q N *
          generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N) + ER + ENNReal.ofReal εs ∧
      wassersteinE 1 (law P (s21XiPath S X (HRS.Whole.meanEmpirical (P.map (X 0)))))
          ((γ0.prod Γ).map (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2)) ≤
        ENNReal.ofReal Cw1 * (ENNReal.ofReal (Ctr' * S.q N *
          generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)) ^ (1 / 2 : ℝ) + ER + εw := by
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
  obtain ⟨Ω₂, mΩ₂, P₂, hP₂, π₂, hπ, ℱ₂, Gb, hGb, hGm, hind, hsm, hw⟩ :=
    s21_master_core b hbv S hN hC hOM hCmp hCtr0 hTr M₂ hM₂0 hM1 hρ' P hX ℱ W' hF hstat hν1 hfub hint hmom hE1 hrem
  -- the independent decomposition
  have hk0cfg : Measurable fun x : EucConfig d N =>
      s56k0 (S.coeff N) b.m b.T (S.σ N) (HRS.Whole.empirical x) νb :=
    s21_K0c_meas b hbv S hN1 hC (Ω := EucConfig d N) (fun _ x => x) measurable_id νb hν1
  set k0₂ : Ω₂ → KSpace d b.m b.T := fun ζ => s21K0c S X νb (π₂ ζ) with hk0₂def
  have hk0m : Measurable k0₂ := hk0cfg.comp ((hXm 0).comp hπ.measurable)
  set U : Ω₂ → OscPath d b.m b.T := fun ζ => s56EvalPath hT0 (k0₂ ζ) with hUdef
  have hUm : Measurable U := (s56EvalPath hT0).continuous.measurable.comp hk0m
  set V : Ω₂ → OscPath d b.m b.T := fun ζ => windowPathOf b.m b.T 0 (fun t =>
    reconstructPath b.m b.T Gb ζ t) with hVdef
  have hrecm : ∀ t, Measurable fun ζ => reconstructPath b.m b.T Gb ζ t := fun t => by
    unfold reconstructPath
    exact (((s56_evalA_cont hT0 t).measurable.comp (hGm b.T)).sub
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm b.T))).add
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm t))
  have hGbc := hGb.cont
  have hVm : AEMeasurable V P₂ := by
    have := gfb4_aemeasurable_windowPath P₂ hT0 (fun t ζ => reconstructPath b.m b.T Gb ζ t)
      (fun t _ => hrecm t)
      (by
        filter_upwards [hGbc] with ζ hζ
        exact continuousOn_iff_continuous_domRestrict.2 (HRS.MS.U9.u9_continuous_recon hT0 Gb ζ hζ))
    rwa [← s56_wpo_eq_windowPath] at this
  haveI hΓp : IsProbabilityMeasure (law P₂ V) :=
    (Measure.isProbabilityMeasure_map_iff hVm).2 inferInstance
  have hindep : IndepFun k0₂ V P₂ :=
    s21_recon_indep b hbv S N hC hOM hS hq P₂ hGb hGm k0₂ hind
  have hindU : IndepFun U V P₂ := hindep.comp (s56EvalPath hT0).continuous.measurable measurable_id
  have hYh : (fun ζ => windowPathOf b.m b.T 0 (fun t => (k0₂ ζ).evalA t +
      reconstructPath b.m b.T Gb ζ t)) =ᵐ[P₂] fun ζ => U ζ + V ζ := by
    filter_upwards [hGbc] with ζ hc
    exact s21_wpo_evalA_add hT0 (k0₂ ζ) (fun t => reconstructPath b.m b.T Gb ζ t)
      (continuousOn_iff_continuous_domRestrict.2 (HRS.MS.U9.u9_continuous_recon hT0 Gb ζ hc))
  have hlawYh : law P₂ (fun ζ => windowPathOf b.m b.T 0 (fun t => (k0₂ ζ).evalA t +
      reconstructPath b.m b.T Gb ζ t)) =
      ((law P₂ U).prod (law P₂ V)).map (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2) := by
    unfold law
    rw [Measure.map_congr hYh]
    exact s21_law_add_of_indep P₂ U V hUm.aemeasurable hVm hindU
  have hU0m : Measurable (s21Path0 hT0 S X νb) :=
    (s56EvalPath hT0).continuous.measurable.comp (s21_K0c_meas b hbv S hN1 hC X (hXm 0) νb hν1)
  have hlawU : law P₂ U = law P (s21Path0 hT0 S X νb) := HRS.GF.law_comp_mp hπ hU0m.aemeasurable
  have hΞm : AEMeasurable (s21XiPath S X νb) P := by
    have h := gfb4_aemeasurable_windowPath P hT0 (s21Xi S X νb)
      (fun t _ => s21_Xi_meas b hbv S (by omega) X hXm νb t)
      (by
        filter_upwards [hX.cont] with ζ hζ
        exact (s21_Xi_cont b hbv S (by omega) X νb ζ hζ).continuousOn)
    rw [← s56_wpo_eq_windowPath] at h
    exact h
  haveI hlP : IsProbabilityMeasure (law P (s21XiPath S X νb)) :=
    (Measure.isProbabilityMeasure_map_iff hΞm).2 inferInstance
  haveI hlU : IsProbabilityMeasure (law P (s21Path0 hT0 S X νb)) :=
    (Measure.isProbabilityMeasure_map_iff hU0m.aemeasurable).2 inferInstance
  have hadd : Measurable (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2) :=
    measurable_fst.add measurable_snd
  haveI hQp : IsProbabilityMeasure ((γ0.prod (law P₂ V)).map
      (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2)) :=
    (Measure.isProbabilityMeasure_map_iff hadd.aemeasurable).2 inferInstance
  haveI hYlp : IsProbabilityMeasure (((law P₂ U).prod (law P₂ V)).map
      (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2)) := by
    haveI : IsProbabilityMeasure (law P₂ U) :=
      (Measure.isProbabilityMeasure_map_iff hUm.aemeasurable).2 inferInstance
    exact (Measure.isProbabilityMeasure_map_iff hadd.aemeasurable).2 inferInstance
  have hsm' : ENNReal.ofReal (smoothDist 2 (law P (s21XiPath S X νb))
      (((law P₂ U).prod (law P₂ V)).map (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2))) ≤
      ENNReal.ofReal Cs * ENNReal.ofReal (Ctr' * S.q N *
        generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N) + ER := by
    rw [← hlawYh]; exact hsm
  have hw' : wassersteinE 1 (law P (s21XiPath S X νb))
      (((law P₂ U).prod (law P₂ V)).map (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2)) ≤
      ENNReal.ofReal Cw1 * (ENNReal.ofReal (Ctr' * S.q N *
        generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)) ^ (1 / 2 : ℝ) + ER := by
    rw [← hlawYh]; exact hw
  rw [hlawU] at hsm' hw'
  refine ⟨law P₂ V, hΓp, fun p ts hts αs => ?_, ?_, ?_⟩
  · have hvec : Measurable (fun w : OscPath d b.m b.T => (WithLp.toLp 2 fun a => OscDual.coord
        (OscPath.at' w ⟨ts a, hts a⟩) (αs a) : EuclideanSpace ℝ (Fin p))) := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
      have h1 : Continuous fun w : OscPath d b.m b.T => OscPath.at' w ⟨ts a, hts a⟩ := by
        have : Continuous fun w : C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) => w ⟨ts a, hts a⟩ :=
          continuous_eval_const _
        exact this
      exact ((s56_continuous_coord b.m (αs a)).comp h1).measurable
    unfold law
    rw [AEMeasurable.map_map_of_aemeasurable hvec.aemeasurable hVm]
    exact s21_recon_fdd b hbv S N hC hOM hS hq P₂ hGb ts hts αs
  · have htri := smoothDist_triangle 2 (law P (s21XiPath S X νb))
      (((law P (s21Path0 hT0 S X νb)).prod (law P₂ V)).map
        (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2))
      ((γ0.prod (law P₂ V)).map (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2))
    have hconv := HRS.T25.t25_smoothDist_conv_le (law P (s21Path0 hT0 S X νb)) γ0 (law P₂ V)
    have hεs0 : 0 ≤ εs := (smoothDist_nonneg _ _ _).trans (hconv.trans hsm0)
    calc ENNReal.ofReal (smoothDist 2 (law P (s21XiPath S X νb))
          ((γ0.prod (law P₂ V)).map (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2)))
        ≤ ENNReal.ofReal (smoothDist 2 (law P (s21XiPath S X νb))
            (((law P (s21Path0 hT0 S X νb)).prod (law P₂ V)).map
              (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2)) + εs) :=
          ENNReal.ofReal_le_ofReal (htri.trans (add_le_add le_rfl (hconv.trans hsm0)))
      _ = ENNReal.ofReal (smoothDist 2 (law P (s21XiPath S X νb))
            (((law P (s21Path0 hT0 S X νb)).prod (law P₂ V)).map
              (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2))) + ENNReal.ofReal εs :=
          ENNReal.ofReal_add (smoothDist_nonneg _ _ _) hεs0
      _ ≤ _ := add_le_add hsm' le_rfl
  · have htri := wassersteinE_triangle 1 le_rfl (law P (s21XiPath S X νb))
      (((law P (s21Path0 hT0 S X νb)).prod (law P₂ V)).map
        (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2))
      ((γ0.prod (law P₂ V)).map (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2))
    have hconv := s21_wasserstein_conv_le 1 le_rfl (law P (s21Path0 hT0 S X νb)) γ0 (law P₂ V)
    exact htri.trans (add_le_add hw' (hconv.trans hw0))

end HRS.MS.S21
