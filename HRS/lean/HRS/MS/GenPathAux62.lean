import HRS.MS.GenPathAux61
import HRS.Main.GFFinal1

/-!
# S5.6 packet P10b: the master comparison on the coupling space (stages 1 and 2)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem HRS.GF HRS.Uniform HRS.Whole.AppendixA

variable {d : ℕ}

theorem s56_master (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 2 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    {Cs Cw1 Cw2 : ℝ} (hCmp : S56CompareHyp (d := d) b.m b.T Cs Cw1 Cw2)
    {Ctr' C1 C2 : ℝ} (hCtr0 : 0 ≤ Ctr') (hTr : S56TraceHyp b Ctr') (hR1 : S56RemHyp b C1 1)
    (hR2 : S56RemHyp b C2 2) (M₂ : ℝ) (hM₂0 : 0 ≤ M₂)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (η₀ : Ω → (Euc d → ℝ) → ℝ)
    (hmom : ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      ∫⁻ ζ, ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal t) ζ))
        (fun x => ‖x‖ ^ 2)) ∂P ≤ ENNReal.ofReal M₂ ∧
      ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) (fun x => ‖x‖ ^ 2)) ≤
        ENNReal.ofReal M₂)
    (hE1 : S.energyMomentE N 1 P X ≠ ⊤)
    (Y : ℝ → Ω → OscDual d b.m) (hYm : ∀ t, Measurable (Y t))
    (hY : IsLinearFluctuationSolutionW P (S.coeff N) b.m (S.q N) b.T (fun ζ f => S.A N * η₀ ζ f) Y)
    (hη : ∀ (t : Set.Icc (0 : ℝ) b.T) (α : MultiIndex d),
      AEMeasurable (fun ζ => S.A N * η₀ ζ (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) P) :
      (ENNReal.ofReal (smoothDist 2 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y))) ≤
        ENNReal.ofReal Cs * ENNReal.ofReal (Ctr' * S.q N *
          generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N) +
          ENNReal.ofReal (C1 * S.σ N) * S.energyMomentE N 1 P X +
          ENNReal.ofReal (S.A N) * S.initialErrorE N 1 P X₀ η₀) ∧
      (wassersteinE 1 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y)) ≤
        ENNReal.ofReal Cw1 * (ENNReal.ofReal (Ctr' * S.q N *
          generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (C1 * S.σ N) * S.energyMomentE N 1 P X +
          ENNReal.ofReal (S.A N) * S.initialErrorE N 1 P X₀ η₀) ∧
      (wassersteinE 2 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y)) ≤
        ENNReal.ofReal Cw2 * (ENNReal.ofReal (Ctr' * S.q N *
          generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (C2 * S.σ N) * S.energyMomentE N 2 P X +
          ENNReal.ofReal (S.A N) * S.initialErrorE N 2 P X₀ η₀) := by
  have hT0 : 0 ≤ b.T := hbv.hT.le
  have hq : 0 ≤ S.q N := s56_q_nonneg b S N (by omega)
  have hS := s56_hS b S N
  have hN1 : 1 ≤ N := by omega
  haveI : Nonempty (Set.Icc (0 : ℝ) b.T) := ⟨⟨0, le_rfl, hT0⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) b.T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) b.T) with hsdef
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hη' : ∀ i : ℕ × MultiIndex d, AEMeasurable (fun ζ => s56Psic S N s η₀ ζ i) P :=
    fun i => hη (s i.1) i.2
  have hΨc : AEMeasurable (s56Psic S N s η₀) P := aemeasurable_pi_iff.2 hη'
  -- the first enlargement
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, c', Ψt, hΨtm, hΨae, hX₁, hF₁, hc'0, hlaw₁⟩ :=
    s56_stage1 b S P X₀ W X hX ℱ W' hF (s56Psic S N s η₀) hΨc
  -- particle data on the first enlargement
  set X₁ : ℝ≥0 → Ω₁ → EucConfig d N := fun t z => X t (π₁ z) with hX₁def
  have hXm₁ : ∀ t, Measurable (X₁ t) := fun t => (hX.adapted t).comp hπ₁.measurable
  obtain ⟨M₁, hM₁ito, hM₁⟩ := s56_particle_martingale b hbv S N hN1 hC (S.q N) hq P₁ ℱ₁
    (fun t z k => W' t (π₁ z) k) X₁ hF₁.brownian hF₁.progressive
  set Db := s56Db b S N hOM hS (S.q N) hq with hDbdef
  have hDb : IsDetCovDensity b.T Db := s56Db_isDet b hbv S N hC hOM hS (S.q N) hq
  set Sg₁ : ℝ → Ω₁ → (KSpace d b.m b.T →L[ℝ] KSpace d b.m b.T →L[ℝ] ℝ) :=
    fun r z => hsCovForm (s56Phi (S.coeff N) b.m b.T (S.q N) X₁ r z) with hSg₁
  -- the Gaussian coupling
  obtain ⟨Ω₂, mΩ₂, P₂, π₂, ℱ₂, Gb, Sd, hc⟩ :=
    gff_adapted_coupling_trace P₁ ℱ₁ b.T hT0 ⟨ℱ₁ 0, le_rfl⟩ M₁ Sg₁ hM₁ Db hDb
  haveI : IsProbabilityMeasure (P₂ : Measure Ω₂) := inferInstance
  have hπ : MeasurePreserving π₂ (P₂ : Measure Ω₂) P₁ := hc.preserving
  set π : Ω₂ → Ω := fun ζ => π₁ (π₂ ζ) with hπdef
  have hπtot : MeasurePreserving π (P₂ : Measure Ω₂) P := hπ₁.comp hπ
  set X₂ : ℝ≥0 → Ω₂ → EucConfig d N := fun t ζ => X t (π ζ) with hX₂def
  have hX₂ : IsWholeStrongSolution (P₂ : Measure Ω₂) (S.dyn N) b.T (fun ζ => X₀ (π ζ))
      (fun t ζ => W t (π ζ)) X₂ := s56_strong_comp hπtot hX
  have hXm₂ : ∀ t, Measurable (X₂ t) := fun t => (hX.adapted t).comp hπtot.measurable
  have hπ' : ∀ i : ℝ, Measurable[ℱ₂ i, ℱ₁ i] π₂ := fun i => Measurable.of_comap_le (hc.filtration i)
  have hprog₂ : IsProgressive ℱ₂ (ofNNRealTime X₂) := fun i =>
    (hF₁.progressive i).comp (measurable_fst.prodMk ((hπ' i).comp measurable_snd))
  have hinj₂ : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      Function.Injective (X₂ (Real.toNNReal t) ζ) := by
    filter_upwards [hX₂.no_collision] with ζ hζ t ht
    have := hζ (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
    intro i j hij
    by_contra hne
    exact this ⟨i, j, hne, hij⟩
  have hEeq : ∀ p : ℝ, S.energyMomentE N p (P₂ : Measure Ω₂) X₂ = S.energyMomentE N p P X := fun p =>
    s56_energyMoment_comp b hbv S (by omega) hπtot X (fun t => hX.adapted t) p
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
    have := HRS.GF.lintegral_comp_mp hπtot hm.aemeasurable
    exact this.trans_le h1
  -- the trace bound
  have hSg₂ : ∀ r ζ, hsCovForm (s56Phi (S.coeff N) b.m b.T (S.q N) X₂ r ζ) = Sg₁ r (π₂ ζ) := fun r ζ => rfl
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
  have hMm₁m : ∀ t, Measurable (M₁ t) := fun t => HRS.Uniform.Q07c.measurable_of_isHM hM₁ t
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
  -- the initial state and the remainder
  have hπ0 : Measurable[ℱ₂ 0, ℱ₁ 0] π₂ := hπ' 0
  have hk0₁ : Measurable[ℱ₁ 0] (s56K0 S X₁) :=
    (s56_k0_meas' b hbv S hN1 hC (S.σ N)).comp (hF₁.adapted 0)
  have hk0₂ : Measurable[ℱ₂ 0] (s56K0 S X₂) := hk0₁.comp hπ0
  set R₂ : ℝ → Ω₂ → OscDual d b.m := fun t ζ =>
    if t ∈ Set.Icc (0 : ℝ) b.T then s56R S X₂ Mm t ζ else 0 with hR₂def
  have hRm : ∀ t, Measurable (R₂ t) := fun t => by
    by_cases ht : t ∈ Set.Icc (0 : ℝ) b.T
    · have e : R₂ t = s56R S X₂ Mm t := funext fun ζ => if_pos ht
      rw [e]
      exact s56_R_meas b hbv S hN1 hC X₂ hXm₂ Mm hMmm ht
    · have e : R₂ t = fun _ => (0 : OscDual d b.m) := funext fun ζ => if_neg ht
      rw [e]
      exact measurable_const
  have hW₁ : IsWholeStrongSolution P₁ (S.dyn N) b.T (fun z => X₀ (π₁ z)) (fun t z => W t (π₁ z)) X₁ := hX₁
  have hRc₁ := s56_R_cont b hbv S hN1 P₁ (fun z => X₀ (π₁ z)) (fun t z => W t (π₁ z)) X₁ hX₁ ℱ₁
    (fun t z k => W' t (π₁ z) k) M₁ hM₁ito.cont
  have hRb₁ := s56_R_bound b hbv S hN1 hC P₁ (fun z => X₀ (π₁ z)) (fun t z => W t (π₁ z)) X₁ hX₁ ℱ₁
    (fun t z k => W' t (π₁ z) k) hF₁ M₁ hM₁ito
  have hRc : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ContinuousOn (fun t => R₂ t ζ) (Set.Icc 0 b.T) := by
    filter_upwards [hπ.quasiMeasurePreserving.ae hRc₁] with ζ hζ
    refine hζ.congr fun t ht => ?_
    simp only [hR₂def, if_pos ht]
    rfl
  -- the sup bound of the remainder
  have hRbd : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ‖windowPathOf b.m b.T 0 (fun t => R₂ t ζ)‖ₑ ≤
      ⨆ t' : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
        S.σ N * ∫ r in Set.Icc (0 : ℝ) t', HRS.Whole.AppendixA.flucInteractionRd (S.dyn N)
          (propagatorW (S.coeff N) r t' (oscTestFun b.m α)) (X₂ (Real.toNNReal r) ζ) (S.ρ N r)) := by
    filter_upwards [hπ.quasiMeasurePreserving.ae hRb₁] with ζ hζ
    have := gfb4_windowPath_enorm_le b.T (fun t ζ => R₂ t ζ) ζ _ (fun t ht => by
      simp only [hR₂def, if_pos ht]
      exact hζ t ht)
    have e : windowPath 0 b.T (fun t ζ => R₂ t ζ) ζ = windowPathOf b.m b.T 0 (fun t => R₂ t ζ) :=
      (congrFun (s56_wpo_eq_windowPath (m := b.m) (T := b.T) (fun t ζ => R₂ t ζ)) ζ).symm
    rw [← e]
    exact this
  -- the particle path
  have hΞeq : ∀ ζ, flucPathW b.m b.T 0 (S.σ N) X (S.ρ N) (π ζ) =
      windowPathOf b.m b.T 0 (fun t => (s56K0 S X₂ ζ).evalA t + reconstructPath b.m b.T Mm ζ t + R₂ t ζ) := by
    intro ζ
    unfold flucPathW
    refine s56_wpo_congr fun t ht => ?_
    have e : R₂ t ζ = s56R S X₂ Mm t ζ := if_pos ht
    rw [e]
    unfold s56R s56Xi
    abel
  have hΞm : AEMeasurable (fun ζ => flucPathW b.m b.T 0 (S.σ N) X (S.ρ N) (π ζ)) (P₂ : Measure Ω₂) :=
    (s56_fluc_aemeas b hbv S hN1 P X₀ W X hX).comp_quasiMeasurePreserving hπtot.quasiMeasurePreserving
  have hlawΞ : law (P₂ : Measure Ω₂) (fun ζ => flucPathW b.m b.T 0 (S.σ N) X (S.ρ N) (π ζ)) =
      law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)) :=
    HRS.GF.law_comp_mp hπtot (s56_fluc_aemeas b hbv S hN1 P X₀ W X hX)
  -- the everywhere continuous modification of the Gaussian martingale
  obtain ⟨G', hG', hG'c, hG'z, hGG'⟩ := gfb4_modify (P₂ : Measure Ω₂) ℱ₂ hT0 Gb Db
    (fun σ hσ => s56Db_zero b S N hOM hS (S.q N) hq hσ) hGb
  have hG'm : ∀ t, Measurable (G' t) := fun t => HRS.Uniform.Q07c.measurable_of_isHM hG' t
  -- the law of the initial array and its independence of the Gaussian martingale
  have hX0m : Measurable fun z : Ω₁ => X 0 (π₁ z) := (hX.adapted 0).comp hπ₁.measurable
  have hc'm : Measurable c' := hc'0.mono (ℱ₁.le 0) le_rfl
  set c'' : Ω₂ → (ℕ × MultiIndex d → ℝ) := fun ζ => c' (π₂ ζ) with hc''def
  have hc''m : Measurable c'' := hc'm.comp hπ.measurable
  have hc''law : (P₂ : Measure Ω₂).map c'' = P.map (s56Psic S N s η₀) := by
    have e1 : (P₂ : Measure Ω₂).map c'' = P₁.map c' := by
      rw [show c'' = c' ∘ π₂ from rfl, ← Measure.map_map hc'm hπ.measurable, hπ.map_eq]
    have e2 : P₁.map c' = P.map Ψt := by
      have := congrArg (fun μ => μ.map Prod.snd) hlaw₁
      rwa [Measure.map_map measurable_snd (hX0m.prodMk hc'm),
        Measure.map_map measurable_snd ((hX.adapted 0).prodMk hΨtm)] at this
    rw [e1, e2]
    exact Measure.map_congr hΨae.symm
  have hind0 := gf_coupling_indep hc hT0 c' hc'0
  have hW : ∀ (p : ℕ) (f : Fin p → ℕ × MultiIndex d),
      IndepFun (fun ζ => (WithLp.toLp 2 fun a => s56FArr b s G' ζ (f a) : EuclideanSpace ℝ (Fin p)))
        (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) : EuclideanSpace ℝ (Fin p))) (P₂ : Measure Ω₂) := by
    intro p f
    have h1 := s56_indepFun_vec b (P₂ : Measure Ω₂) s Gb c'' hind0 f
    refine IndepFun.congr h1 ?_ Filter.EventuallyEq.rfl
    have : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ∀ a : Fin p, G' (s (f a).1) ζ = Gb (s (f a).1) ζ :=
      ae_all_iff.2 fun a => hGG' _ (s (f a).1).2
    filter_upwards [this] with ζ hζ
    ext a
    simp only [s56FArr, hζ a]
  -- the path `g (c'')` and the law of the path of `Y`
  have hemb := s56_measurableEmbedding_pathCoords (d := d) b.m b.T s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  have hgleft : ∀ c ∈ Set.range (s56PathCoords (d := d) b.m b.T s), s56PathCoords (d := d) b.m b.T s (g c) = c := by
    rintro _ ⟨w, rfl⟩
    have := congrFun hg w
    simp only [Function.comp, id] at this
    rw [this]
  have hYcl := s56_Yc_law b hbv S N hC hOM hS hq (P := P) (P₂ := (P₂ : Measure Ω₂)) η₀ Y hYm hY s hs hη'
    (ℱ₂ := gfb4_aug (P₂ : Measure Ω₂) ℱ₂) hG' hG'c hG'z hG'm g hgm hgleft c'' hc''m hc''law hW
  have hlawYc : law (P₂ : Measure Ω₂) (fun ζ => windowPathOf b.m b.T 0
      (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath b.m b.T Gb ζ t)) =
      law P (processWindow b.m b.T 0 Y) := by
    rw [show processWindow b.m b.T 0 Y = fun ζ => windowPathOf b.m b.T 0 (fun t => Y t ζ) from rfl, ← hYcl]
    exact Measure.map_congr (s56_window_recon_ae b hT0 (P₂ : Measure Ω₂) Gb G' s hs hGb.cont hG'c
      (fun τ hτ => (hGG' τ hτ).symm) (fun ζ => g (c'' ζ)))
  -- measurability of the two paths
  have hrecm : ∀ t, Measurable fun ζ => reconstructPath b.m b.T Gb ζ t := fun t => by
    unfold reconstructPath
    exact (((s56_evalA_cont hT0 t).measurable.comp (hGm b.T)).sub
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm b.T))).add
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm t))
  have hk0m : Measurable (s56K0 S X₂) := s56_K0_meas b hbv S hN1 hC X₂ (hXm₂ 0)
  have hrecc : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), Continuous fun t : Set.Icc (0 : ℝ) b.T =>
      reconstructPath b.m b.T Gb ζ t := by
    filter_upwards [hGb.cont] with ζ hζ
    exact HRS.MS.U9.u9_continuous_recon hT0 Gb ζ hζ
  have hYhm : AEMeasurable (fun ζ => windowPathOf b.m b.T 0 (fun t =>
      (s56K0 S X₂ ζ).evalA t + reconstructPath b.m b.T Gb ζ t)) (P₂ : Measure Ω₂) := by
    have := gfb4_aemeasurable_windowPath (P₂ : Measure Ω₂) hT0
      (fun t ζ => (s56K0 S X₂ ζ).evalA t + reconstructPath b.m b.T Gb ζ t)
      (fun t _ => ((s56_evalA_cont hT0 t).measurable.comp hk0m).add (hrecm t))
      (by
        filter_upwards [hrecc] with ζ hζ
        exact (HRS.MS.U9.u9_continuousOn_evalA hT0 _).add (continuousOn_iff_continuous_restrict.2 hζ))
    rwa [← s56_wpo_eq_windowPath] at this
  have hYcm : AEMeasurable (fun ζ => windowPathOf b.m b.T 0 (fun t =>
      s56Ext hT0 (g (c'' ζ)) t + reconstructPath b.m b.T Gb ζ t)) (P₂ : Measure Ω₂) := by
    have := gfb4_aemeasurable_windowPath (P₂ : Measure Ω₂) hT0
      (fun t ζ => s56Ext hT0 (g (c'' ζ)) t + reconstructPath b.m b.T Gb ζ t)
      (fun t _ => (s56Ext_meas hT0 _ (hgm.comp hc''m) t).add (hrecm t))
      (by
        filter_upwards [hrecc] with ζ hζ
        exact (s56Ext_cont hT0 (g (c'' ζ))).continuousOn.add (continuousOn_iff_continuous_restrict.2 hζ))
    rwa [← s56_wpo_eq_windowPath] at this
  -- the `L^p` distance of the initial paths
  have hrangeΨ : ∀ᵐ ζ ∂P, s56Psic S N s η₀ ζ ∈ Set.range (s56PathCoords (d := d) b.m b.T s) :=
    (s56_D_range b hbv S N hC hOM hS hq P (P₂ : Measure Ω₂) η₀ Y hYm hY s hs hη'
      (ℱ₂ := gfb4_aug (P₂ : Measure Ω₂) ℱ₂) hG' hG'c hG'z hG'm).2
  have hεint : ∀ p : ℝ, 0 < p →
      ∫⁻ ζ, ‖windowPathOf b.m b.T 0 (fun t => (s56K0 S X₂ ζ).evalA t + reconstructPath b.m b.T Gb ζ t) -
        windowPathOf b.m b.T 0 (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath b.m b.T Gb ζ t)‖ₑ ^ p
          ∂(P₂ : Measure Ω₂) ≤
        ENNReal.ofReal (S.A N) ^ p * ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE fun α : MultiIndex d =>
          S.κ N * (HRS.Whole.pair (HRS.Whole.empirical (X₀ ζ))
              (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
            HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0))
              (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) -
            η₀ ζ (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) ^ p ∂P := by
    intro p hp
    have hHm := s56Hfun_meas b hbv S hN1 hC g hgm p
    have hpair₁ : Measurable fun z : Ω₁ => (X 0 (π₁ z), c' z) := hX0m.prodMk hc'm
    have hdiff_eq : ∀ᵐ ζ ∂(P₂ : Measure Ω₂), ‖windowPathOf b.m b.T 0 (fun t =>
        (s56K0 S X₂ ζ).evalA t + reconstructPath b.m b.T Gb ζ t) -
        windowPathOf b.m b.T 0 (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath b.m b.T Gb ζ t)‖ₑ ^ p =
        s56Hfun b hbv S g p (X 0 (π₁ (π₂ ζ))) (c' (π₂ ζ)) := by
      filter_upwards [hrecc] with ζ hζ
      have hc1 : ContinuousOn (fun t => (s56K0 S X₂ ζ).evalA t + reconstructPath b.m b.T Gb ζ t)
          (Set.Icc 0 b.T) :=
        (HRS.MS.U9.u9_continuousOn_evalA hT0 _).add (continuousOn_iff_continuous_restrict.2 hζ)
      have hc2 : ContinuousOn (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath b.m b.T Gb ζ t)
          (Set.Icc 0 b.T) :=
        (s56Ext_cont hT0 (g (c'' ζ))).continuousOn.add (continuousOn_iff_continuous_restrict.2 hζ)
      have : windowPathOf b.m b.T 0 (fun t => (s56K0 S X₂ ζ).evalA t + reconstructPath b.m b.T Gb ζ t) -
          windowPathOf b.m b.T 0 (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath b.m b.T Gb ζ t) =
          s56EvalPath hT0 (s56K0 S X₂ ζ) - g (c'' ζ) := by
        refine ContinuousMap.ext fun t => ?_
        show (show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from windowPathOf b.m b.T 0 _) t -
          (show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from windowPathOf b.m b.T 0 _) t =
          (show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from s56EvalPath hT0 (s56K0 S X₂ ζ)) t -
            (show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from g (c'' ζ)) t
        rw [s56_wpo_apply hc1 t, s56_wpo_apply hc2 t, s56EvalPath_apply, s56Ext_of_mem hT0 _ t.2]
        abel
      rw [this]
      rfl
    calc ∫⁻ ζ, ‖windowPathOf b.m b.T 0 (fun t => (s56K0 S X₂ ζ).evalA t + reconstructPath b.m b.T Gb ζ t) -
        windowPathOf b.m b.T 0 (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath b.m b.T Gb ζ t)‖ₑ ^ p
          ∂(P₂ : Measure Ω₂)
        = ∫⁻ ζ, s56Hfun b hbv S g p (X 0 (π₁ (π₂ ζ))) (c' (π₂ ζ)) ∂(P₂ : Measure Ω₂) :=
          lintegral_congr_ae hdiff_eq
      _ = ∫⁻ z, s56Hfun b hbv S g p (X 0 (π₁ z)) (c' z) ∂P₁ :=
          HRS.GF.lintegral_comp_mp hπ (f := fun z => s56Hfun b hbv S g p (X 0 (π₁ z)) (c' z))
            (hHm.comp hpair₁).aemeasurable
      _ = ∫⁻ ζ, s56Hfun b hbv S g p (X 0 ζ) (Ψt ζ) ∂P := by
          rw [← lintegral_map hHm hpair₁, hlaw₁, lintegral_map hHm ((hX.adapted 0).prodMk hΨtm)]
      _ ≤ _ := s56_eps_integral b hbv S hN1 hC s hs g hgleft P X₀ (X 0) hX.init η₀ Ψt hΨae hrangeΨ p hp
  -- the abstract comparison
  have hcmp := hCmp Ω₂ (P₂ : Measure Ω₂) ℱ₂ (s56K0 S X₂) hk0₂ Mm Sg₂ hMm₂ hMmm Gb Db hDb hGb hGm Sd
    (fun r ζ => traceNormForm (Sg₂ r ζ - Db r)) hdiff hcost hMm₂.cont hMm₂.zero hGb.cont hGb.zero R₂ hRc hRm
    (fun ζ => flucPathW b.m b.T 0 (S.σ N) X (S.ρ N) (π ζ))
    (fun ζ => windowPathOf b.m b.T 0 (fun t => s56Ext hT0 (g (c'' ζ)) t + reconstructPath b.m b.T Gb ζ t))
    hΞm hYcm hYhm (Filter.Eventually.of_forall hΞeq)
  obtain ⟨hsm, hw1, hw2⟩ := hcmp
  rw [hlawΞ, hlawYc] at hsm hw1 hw2
  -- the three pieces
  set T₂ : ℝ≥0∞ := ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) b.T, ENNReal.ofReal (traceNormForm (Sg₂ r ζ - Db r)))
    ∂(P₂ : Measure Ω₂) with hT₂
  have hT₂le : T₂ ≤ ENNReal.ofReal (Ctr' * S.q N *
      generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N) := htrace
  have hRp : ∀ (C p : ℝ) (hR : S56RemHyp b C p) (hp : 0 < p),
      (∫⁻ ζ, ‖windowPathOf b.m b.T 0 (fun t => R₂ t ζ)‖ₑ ^ p ∂(P₂ : Measure Ω₂)) ^ (1 / p) ≤
        ENNReal.ofReal (C * S.σ N) * S.energyMomentE N p P X := by
    intro C p hR hp
    have h := hR S N hN (P₂ : Measure Ω₂) ℱ₂ X₂ hprog₂ hinj₂
    rw [hEeq p] at h
    refine le_trans (ENNReal.rpow_le_rpow ?_ (by positivity)) h
    refine lintegral_mono_ae ?_
    filter_upwards [hRbd] with ζ hζ
    exact ENNReal.rpow_le_rpow hζ hp.le
  have hεp : ∀ p : ℝ, 0 < p →
      (∫⁻ ζ, ENNReal.ofReal (‖windowPathOf b.m b.T 0 (fun t => (s56K0 S X₂ ζ).evalA t +
        reconstructPath b.m b.T Gb ζ t) - windowPathOf b.m b.T 0 (fun t => s56Ext hT0 (g (c'' ζ)) t +
          reconstructPath b.m b.T Gb ζ t)‖ ^ p) ∂(P₂ : Measure Ω₂)) ^ (1 / p) ≤
        ENNReal.ofReal (S.A N) * S.initialErrorE N p P X₀ η₀ := by
    intro p hp
    have h := hεint p hp
    have e : ∀ ζ, ENNReal.ofReal (‖windowPathOf b.m b.T 0 (fun t => (s56K0 S X₂ ζ).evalA t +
        reconstructPath b.m b.T Gb ζ t) - windowPathOf b.m b.T 0 (fun t => s56Ext hT0 (g (c'' ζ)) t +
          reconstructPath b.m b.T Gb ζ t)‖ ^ p) = ‖windowPathOf b.m b.T 0 (fun t => (s56K0 S X₂ ζ).evalA t +
        reconstructPath b.m b.T Gb ζ t) - windowPathOf b.m b.T 0 (fun t => s56Ext hT0 (g (c'' ζ)) t +
          reconstructPath b.m b.T Gb ζ t)‖ₑ ^ p := fun ζ => by
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ofReal_norm]
    simp_rw [e]
    calc (∫⁻ ζ, ‖windowPathOf b.m b.T 0 (fun t => (s56K0 S X₂ ζ).evalA t +
          reconstructPath b.m b.T Gb ζ t) - windowPathOf b.m b.T 0 (fun t => s56Ext hT0 (g (c'' ζ)) t +
          reconstructPath b.m b.T Gb ζ t)‖ₑ ^ p ∂(P₂ : Measure Ω₂)) ^ (1 / p)
        ≤ (ENNReal.ofReal (S.A N) ^ p * ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE fun α : MultiIndex d =>
          S.κ N * (HRS.Whole.pair (HRS.Whole.empirical (X₀ ζ))
              (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
            HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0))
              (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) -
            η₀ ζ (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) ^ p ∂P) ^ (1 / p) :=
          ENNReal.rpow_le_rpow h (by positivity)
      _ = ENNReal.ofReal (S.A N) * S.initialErrorE N p P X₀ η₀ := by
          unfold WholeSetup.initialErrorE
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hp.ne', ENNReal.rpow_one]
  have hcost : ∀ (p : ℝ), (T₂) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (Ctr' * S.q N *
      generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)) ^ (1 / 2 : ℝ) := fun _ =>
    ENNReal.rpow_le_rpow hT₂le (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have hR1' := hRp C1 1 hR1 one_pos
    have hε1 := hεp 1 one_pos
    simp only [Real.rpow_one, ofReal_norm, div_one, ENNReal.rpow_one] at hR1' hε1
    exact hsm.trans (add_le_add (add_le_add (mul_le_mul' le_rfl hT₂le) hR1') hε1)
  · have hR1' := hRp C1 1 hR1 one_pos
    have hε1 := hεp 1 one_pos
    exact hw1.trans (add_le_add (add_le_add (mul_le_mul' le_rfl (hcost 1)) hR1') hε1)
  · have hR2' := hRp C2 2 hR2 two_pos
    have hε2 := hεp 2 two_pos
    exact hw2.trans (add_le_add (add_le_add (mul_le_mul' le_rfl (hcost 2)) hR2') hε2)

end HRS.MS.GenPath
