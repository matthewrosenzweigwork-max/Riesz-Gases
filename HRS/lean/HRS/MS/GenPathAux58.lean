import HRS.MS.GenPathAux57

/-!
# S5.6 packet P8k: the law of the path of `Y` is the law of `c̃ + 𝒯G`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MS.S52 HRS.Uniform.Q54c

variable {d : ℕ}

theorem s56_Yc_law (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
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
    (hGc : ∀ ζ, Continuous fun t => G t ζ) (hGz : ∀ ζ, G 0 ζ = 0) (hGm : ∀ t, Measurable (G t))
    (g : (ℕ × MultiIndex d → ℝ) → OscPath d b.m b.T) (hgm : Measurable g)
    (hgleft : ∀ c ∈ Set.range (s56PathCoords (d := d) b.m b.T s), s56PathCoords (d := d) b.m b.T s (g c) = c)
    (c'' : Ω₂ → (ℕ × MultiIndex d → ℝ)) (hc''m : Measurable c'')
    (hc''law : P₂.map c'' = P.map (s56Psic S N s η₀))
    (hW : ∀ (p : ℕ) (f : Fin p → ℕ × MultiIndex d),
      IndepFun (fun ζ => (WithLp.toLp 2 fun a => s56FArr b s G ζ (f a) : EuclideanSpace ℝ (Fin p)))
        (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) : EuclideanSpace ℝ (Fin p))) P₂) :
    law P₂ (fun ζ => windowPathOf b.m b.T 0
        (fun t => s56Ext hbv.hT.le (g (c'' ζ)) t + reconstructPath b.m b.T G ζ t)) =
      law P (fun ζ => windowPathOf b.m b.T 0 (fun t => Y t ζ)) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  have hemb := s56_measurableEmbedding_pathCoords (d := d) b.m b.T s hs
  have hΨc : AEMeasurable (s56Psic S N s η₀) P := aemeasurable_pi_iff.2 hη
  obtain ⟨-, hrange⟩ := s56_D_range b hbv S N hC hOM hS hq P P₂ η₀ Y hYm hY s hs hη hG hGc hGz hGm
  have hrange₂ : ∀ᵐ ζ ∂P₂, c'' ζ ∈ Set.range (s56PathCoords (d := d) b.m b.T s) :=
    s56_ae_mem_of_map_eq P₂ P c'' _ hc''m.aemeasurable hΨc hc''law hemb.measurableSet_range hrange
  have hcoords : ∀ᵐ ζ ∂P₂, s56PathCoords (d := d) b.m b.T s (g (c'' ζ)) = c'' ζ := by
    filter_upwards [hrange₂] with ζ hζ
    exact hgleft _ hζ
  have hFm : Measurable (s56FArr b s G) :=
    measurable_pi_iff.2 fun i => (hGm _).inner measurable_const
  -- the process `Y'`
  set Y' : ℝ → Ω₂ → OscDual d b.m := fun t ζ => s56Ext hT (g (c'' ζ)) t + reconstructPath b.m b.T G ζ t with hY'
  have hrecm : ∀ t, Measurable fun ζ => reconstructPath b.m b.T G ζ t := fun t => by
    unfold reconstructPath
    exact (((s56_evalA_cont hT t).measurable.comp (hGm b.T)).sub
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm b.T))).add
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm t))
  have hY'm : ∀ t, Measurable (Y' t) := fun t =>
    (s56Ext_meas hT _ (hgm.comp hc''m) t).add (hrecm t)
  have hY'c : ∀ᵐ ζ ∂P₂, ContinuousOn (fun t => Y' t ζ) (Set.Icc 0 b.T) := by
    refine Filter.Eventually.of_forall fun ζ => ?_
    exact ((s56Ext_cont hT (g (c'' ζ))).continuousOn).add
      (continuousOn_iff_continuous_restrict.2 (HRS.MS.U9.u9_continuous_recon hT G ζ (hGc ζ).continuousOn))
  have harr := s56_Y_array_law b hbv S N hC hOM hS hq P P₂ η₀ Y hYm hY s hη hG hGc hGz hGm c'' hc''m hc''law hW
  have harr' : P.map (s56Psi0 s Y) =
      P₂.map (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Y' (s i.1) ζ) i.2) := by
    rw [harr]
    refine Measure.map_congr ?_
    filter_upwards [hcoords, s56_FArr_range b hbv S N hC hOM hS (S.q N) hq hG s] with ζ h1 h2
    funext i
    simp only [hY']
    rw [OscDual.coord_add, s56Ext_of_mem hT _ (s i.1).2]
    have := congrFun h1 i
    simp only [s56PathCoords, OscPath.at'] at this
    rw [this, congrFun h2 i]
  have key := s56_path_law_eq hT P P₂ Y Y' hYm hY'm hY.cont hY'c s hs harr'
  exact key.symm

end HRS.MS.GenPath
