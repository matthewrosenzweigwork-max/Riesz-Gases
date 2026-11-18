import HRS.MS.GenPathAux56

/-!
# S5.6 packet P8j: the coordinate array of `Y` has the law of `c'' + F`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MS.S52 HRS.Uniform.Q54c

variable {d : ℕ}

theorem s56_Y_array_law (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
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
    (hGc : ∀ ζ, Continuous fun t => G t ζ) (hGz : ∀ ζ, G 0 ζ = 0) (hGm : ∀ t, Measurable (G t))
    (c'' : Ω₂ → (ℕ × MultiIndex d → ℝ)) (hc''m : Measurable c'')
    (hc''law : P₂.map c'' = P.map (s56Psic S N s η₀))
    (hW : ∀ (p : ℕ) (f : Fin p → ℕ × MultiIndex d),
      IndepFun (fun ζ => (WithLp.toLp 2 fun a => s56FArr b s G ζ (f a) : EuclideanSpace ℝ (Fin p)))
        (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) : EuclideanSpace ℝ (Fin p))) P₂) :
    P.map (s56Psi0 s Y) = P₂.map (fun ζ i => c'' ζ i + s56FArr b s G ζ i) := by
  have hFm : Measurable (s56FArr b s G) :=
    measurable_pi_iff.2 fun i => (hGm _).inner measurable_const
  have hΨc : AEMeasurable (s56Psic S N s η₀) P := aemeasurable_pi_iff.2 hη
  have hlawD := s56_D_law b hbv S N hC hOM hS hq P P₂ η₀ Y hYm hY s hη hG hGc hGz hGm
  refine s56_seq_law_eq P P₂ _ _ (s56_Psi0_meas s Y hYm).aemeasurable (hc''m.add hFm).aemeasurable
    fun p f hf => ?_
  obtain ⟨hDm, hVcm, hindV⟩ := s56_Vc_props b S N P η₀ Y hYm hY s hη f
  set vec : (ℕ × MultiIndex d → ℝ) → EuclideanSpace ℝ (Fin p) := fun x => WithLp.toLp 2 fun a => x (f a) with hvec
  have hvm : Measurable vec :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => measurable_pi_apply (f a))
  have hD' : AEMeasurable (fun ζ i => s56Psi0 s Y ζ i - s56Psic S N s η₀ ζ i) P :=
    aemeasurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp (s56_Psi0_meas s Y hYm)).aemeasurable.sub (hη i)
  -- decomposition
  have e1 : (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) : EuclideanSpace ℝ (Fin p))) =
      fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) - s56Psic S N s η₀ ζ (f a) :
        EuclideanSpace ℝ (Fin p)) + (WithLp.toLp 2 fun a => s56Psic S N s η₀ ζ (f a) :
        EuclideanSpace ℝ (Fin p)) := by
    funext ζ; ext a; simp
  have e2 : (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) + s56FArr b s G ζ (f a) : EuclideanSpace ℝ (Fin p))) =
      fun ζ => (WithLp.toLp 2 fun a => s56FArr b s G ζ (f a) : EuclideanSpace ℝ (Fin p)) +
        (WithLp.toLp 2 fun a => c'' ζ (f a) : EuclideanSpace ℝ (Fin p)) := by
    funext ζ; ext a; simp [add_comm]
  show P.map (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) : EuclideanSpace ℝ (Fin p))) =
    P₂.map (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) + s56FArr b s G ζ (f a) : EuclideanSpace ℝ (Fin p)))
  rw [e1, e2]
  have hWF : Measurable (fun ζ => (WithLp.toLp 2 fun a => s56FArr b s G ζ (f a) : EuclideanSpace ℝ (Fin p))) :=
    hvm.comp hFm
  have hWc : Measurable (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) : EuclideanSpace ℝ (Fin p))) :=
    hvm.comp hc''m
  have hlawc : P.map (fun ζ => (WithLp.toLp 2 fun a => s56Psic S N s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) =
      P₂.map (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) : EuclideanSpace ℝ (Fin p))) := by
    have := congrArg (fun μ => μ.map vec) hc''law
    rw [Measure.map_map hvm hc''m, AEMeasurable.map_map_of_aemeasurable hvm.aemeasurable hΨc] at this
    exact this.symm
  have hlawF : P.map (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) - s56Psic S N s η₀ ζ (f a) :
        EuclideanSpace ℝ (Fin p))) =
      P₂.map (fun ζ => (WithLp.toLp 2 fun a => s56FArr b s G ζ (f a) : EuclideanSpace ℝ (Fin p))) := by
    have := congrArg (fun μ => μ.map vec) hlawD
    rw [AEMeasurable.map_map_of_aemeasurable hvm.aemeasurable hD', Measure.map_map hvm hFm] at this
    exact this
  exact s56_sum_law P P₂ _ _ _ _ hVcm hDm hWc.aemeasurable hWF.aemeasurable hindV (hW p f) hlawc hlawF

end HRS.MS.GenPath
