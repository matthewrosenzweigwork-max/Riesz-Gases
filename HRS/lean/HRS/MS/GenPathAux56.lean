import HRS.MS.GenPathAux55

/-!
# S5.6 packet P8i: the law of `Y` as a sum of the independent initial array and the Gaussian array
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MS.S52 HRS.Uniform.Q54c

variable {d : ℕ}

theorem s56_ae_mem_of_map_eq {Ω Ω' β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace β]
    (P : Measure Ω) (P' : Measure Ω') (f : Ω → β) (f' : Ω' → β) (hf : AEMeasurable f P)
    (hf' : AEMeasurable f' P') (h : P.map f = P'.map f') {A : Set β} (hA : MeasurableSet A)
    (h' : ∀ᵐ z ∂P', f' z ∈ A) : ∀ᵐ ζ ∂P, f ζ ∈ A := by
  have h1 : ∀ᵐ y ∂(P'.map f'), y ∈ A := (ae_map_iff hf' hA).2 h'
  rw [← h] at h1
  exact (ae_map_iff hf hA).1 h1

/-- The law of the Gaussian part of `Y`, as an array, is the law of the coordinate array of `𝒯G`. -/
theorem s56_D_law (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (hq : 0 ≤ S.q N) {Ω Ω₂ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    (P : Measure Ω) [IsProbabilityMeasure P] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d b.m) (hYm : ∀ t, Measurable (Y t))
    (hY : IsLinearFluctuationSolutionW P (S.coeff N) b.m (S.q N) b.T (fun ζ f => S.A N * η₀ ζ f) Y)
    (s : ℕ → Set.Icc (0 : ℝ) b.T)
    (hη : ∀ i : ℕ × MultiIndex d, AEMeasurable (fun ζ => s56Psic S N s η₀ ζ i) P)
    {ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›} {G : ℝ → Ω₂ → KSpace d b.m b.T}
    (hG : IsHilbertMartingaleWithCovariation P₂ ℱ₂ b.T G (fun r _ => s56Db b S N hOM hS (S.q N) hq r))
    (hGc : ∀ ζ, Continuous fun t => G t ζ) (hGz : ∀ ζ, G 0 ζ = 0) (hGm : ∀ t, Measurable (G t)) :
    P.map (fun ζ i => s56Psi0 s Y ζ i - s56Psic S N s η₀ ζ i) = P₂.map (s56FArr b s G) := by
  have hFm : Measurable (s56FArr b s G) :=
    measurable_pi_iff.2 fun i => (hGm _).inner measurable_const
  have hD : AEMeasurable (fun ζ i => s56Psi0 s Y ζ i - s56Psic S N s η₀ ζ i) P :=
    aemeasurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp (s56_Psi0_meas s Y hYm)).aemeasurable.sub (hη i)
  refine s56_seq_law_eq P P₂ _ _ hD hFm.aemeasurable fun p f hf => ?_
  obtain ⟨-, hlaw⟩ := s56_VD_law b S N P η₀ Y hY s f
  rw [show (fun ζ => (WithLp.toLp 2 fun a => (fun ζ i => s56Psi0 s Y ζ i - s56Psic S N s η₀ ζ i) ζ (f a) :
      EuclideanSpace ℝ (Fin p))) = (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) -
        s56Psic S N s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) from rfl, hlaw]
  exact (s56_Gb_fdd b hbv S N hC hOM hS (S.q N) hq hG hGc hGz hGm (fun a => (s (f a).1 : ℝ))
    (fun a => (s (f a).1).2) (fun a => (f a).2)).symm

theorem s56_D_range (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (hq : 0 ≤ S.q N) {Ω Ω₂ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    (P : Measure Ω) [IsProbabilityMeasure P] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d b.m) (hYm : ∀ t, Measurable (Y t))
    (hY : IsLinearFluctuationSolutionW P (S.coeff N) b.m (S.q N) b.T (fun ζ f => S.A N * η₀ ζ f) Y)
    (s : ℕ → Set.Icc (0 : ℝ) b.T) (hs : DenseRange s)
    (hη : ∀ i : ℕ × MultiIndex d, AEMeasurable (fun ζ => s56Psic S N s η₀ ζ i) P)
    {ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›} {G : ℝ → Ω₂ → KSpace d b.m b.T}
    (hG : IsHilbertMartingaleWithCovariation P₂ ℱ₂ b.T G (fun r _ => s56Db b S N hOM hS (S.q N) hq r))
    (hGc : ∀ ζ, Continuous fun t => G t ζ) (hGz : ∀ ζ, G 0 ζ = 0) (hGm : ∀ t, Measurable (G t)) :
    (∀ᵐ ζ ∂P, (fun i => s56Psi0 s Y ζ i - s56Psic S N s η₀ ζ i) ∈
        Set.range (s56PathCoords (d := d) b.m b.T s)) ∧
    (∀ᵐ ζ ∂P, s56Psic S N s η₀ ζ ∈ Set.range (s56PathCoords (d := d) b.m b.T s)) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  have hemb := s56_measurableEmbedding_pathCoords (d := d) b.m b.T s hs
  have hFm : Measurable (s56FArr b s G) :=
    measurable_pi_iff.2 fun i => (hGm _).inner measurable_const
  have hD : AEMeasurable (fun ζ i => s56Psi0 s Y ζ i - s56Psic S N s η₀ ζ i) P :=
    aemeasurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp (s56_Psi0_meas s Y hYm)).aemeasurable.sub (hη i)
  have hlaw := s56_D_law b hbv S N hC hOM hS hq P P₂ η₀ Y hYm hY s hη hG hGc hGz hGm
  have hF : ∀ᵐ ζ ∂P₂, s56FArr b s G ζ ∈ Set.range (s56PathCoords (d := d) b.m b.T s) := by
    filter_upwards [s56_FArr_range b hbv S N hC hOM hS (S.q N) hq hG s] with ζ hζ
    refine ⟨windowPathOf b.m b.T 0 (fun t => reconstructPath b.m b.T G ζ t), ?_⟩
    rw [hζ]
    exact s56_pathCoords_windowPathOf (d := d) (m := b.m) (T := b.T) s (fun t ζ => reconstructPath b.m b.T G ζ t)
      (HRS.MS.U9.u9_continuous_recon hT G ζ (hGc ζ).continuousOn |> fun h => continuousOn_iff_continuous_restrict.2 h)
  have hD' := s56_ae_mem_of_map_eq P P₂ _ _ hD hFm.aemeasurable hlaw hemb.measurableSet_range hF
  refine ⟨hD', ?_⟩
  filter_upwards [hD', hY.cont] with ζ h1 h2
  obtain ⟨w', hw'⟩ := h1
  refine ⟨windowPathOf b.m b.T 0 (fun t => Y t ζ) - w', ?_⟩
  rw [s56_pathCoords_sub, s56_pathCoords_windowPathOf s Y h2, hw']
  funext i
  simp only [Pi.sub_apply, s56Psi0]
  ring

end HRS.MS.GenPath
