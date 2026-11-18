import HRS.MS.WsStatAux23

/-!
# S21 packet I-2: the Gaussian-martingale path and its independence of the initial state

* `s21_wpo_evalA_add`: `window(A k + f) = s56EvalPath k + window f` for `f` continuous on `[0,T]`.
* `s21_window_recon_ae`: the window of the reconstructed path of an a.s. continuous process agrees a.s. with that of an everywhere
  continuous modification.
* `s21_recon_indep`: if `xi` is independent of `sigma(G_tau, tau <= T)` then `xi` is independent of the path `window (recon G)`.
  (The coordinate array of the path at a dense sequence of times is `sigma(G_tau)`-measurable and determines the path:
  `s56_measurableEmbedding_pathCoords`.)
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.Uniform.Q54c
open HRS (Euc)

variable {d : ℕ}

theorem s21_wpo_evalA_add {m T : ℝ} (hT : 0 ≤ T) (k : KSpace d m T) (f : ℝ → OscDual d m)
    (hf : ContinuousOn f (Set.Icc 0 T)) :
    windowPathOf m T 0 (fun t => k.evalA t + f t) = s56EvalPath hT k + windowPathOf m T 0 f := by
  have hc : ContinuousOn (fun t => k.evalA t + f t) (Set.Icc 0 T) :=
    (HRS.MS.U9.u9_continuousOn_evalA hT k).add hf
  refine ContinuousMap.ext fun t => ?_
  have h1 := s56_wpo_apply (m := m) (T := T) hc t
  have h2 := s56_wpo_apply (m := m) (T := T) hf t
  show (show C(Set.Icc (0 : ℝ) T, OscDual d m) from windowPathOf m T 0 _) t =
    (show C(Set.Icc (0 : ℝ) T, OscDual d m) from s56EvalPath hT k) t +
      (show C(Set.Icc (0 : ℝ) T, OscDual d m) from windowPathOf m T 0 f) t
  rw [h1, h2, s56EvalPath_apply]

theorem s21_window_recon_ae (b : WholeBounds d) (hT : 0 ≤ b.T) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G G' : ℝ → Ω → KSpace d b.m b.T) (s : ℕ → Set.Icc (0 : ℝ) b.T) (hs : DenseRange s)
    (hGc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => G t ζ) (Set.Icc 0 b.T))
    (hG'c : ∀ ζ, Continuous fun t => G' t ζ)
    (hae : ∀ τ ∈ Set.Icc (0 : ℝ) b.T, G τ =ᵐ[P] G' τ) :
    (fun ζ => windowPathOf b.m b.T 0 (fun t => reconstructPath b.m b.T G ζ t)) =ᵐ[P]
    (fun ζ => windowPathOf b.m b.T 0 (fun t => reconstructPath b.m b.T G' ζ t)) := by
  have hT' : b.T ∈ Set.Icc (0 : ℝ) b.T := ⟨hT, le_rfl⟩
  have h1 : ∀ᵐ ζ ∂P, ∀ n : ℕ, G (s n) ζ = G' (s n) ζ := ae_all_iff.2 fun n => hae _ (s n).2
  filter_upwards [h1, hae _ hT', hGc] with ζ hn hT'' hc
  refine s56_wpo_congr fun t ht => ?_
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) b.T => reconstructPath b.m b.T G ζ t :=
    HRS.MS.U9.u9_continuous_recon hT G ζ hc
  have hcont' : Continuous fun t : Set.Icc (0 : ℝ) b.T => reconstructPath b.m b.T G' ζ t :=
    HRS.MS.U9.u9_continuous_recon hT G' ζ (hG'c ζ).continuousOn
  have heq : (fun t : Set.Icc (0 : ℝ) b.T => reconstructPath b.m b.T G ζ t) =
      fun t : Set.Icc (0 : ℝ) b.T => reconstructPath b.m b.T G' ζ t := by
    refine hs.equalizer hcont hcont' (funext fun n => ?_)
    show reconstructPath b.m b.T G ζ (s n) = reconstructPath b.m b.T G' ζ (s n)
    unfold reconstructPath
    rw [hT'', hn n]
  exact congrFun heq ⟨t, ht⟩

theorem s21_recon_indep (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (hq : 0 ≤ S.q N) {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    {ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›} {G : ℝ → Ω₂ → KSpace d b.m b.T}
    (hG : IsHilbertMartingaleWithCovariation P₂ ℱ₂ b.T G (fun r _ => s56Db b S N hOM hS (S.q N) hq r))
    (hGm : ∀ t, Measurable (G t)) {E' : Type} [mE : MeasurableSpace E'] (ξ : Ω₂ → E')
    (hind : Indep (MeasurableSpace.comap ξ mE)
      (⨆ τ ∈ Set.Icc (0 : ℝ) b.T, MeasurableSpace.comap (G τ) inferInstance) P₂) :
    IndepFun ξ (fun ζ => windowPathOf b.m b.T 0 (fun t => reconstructPath b.m b.T G ζ t)) P₂ := by
  have hT : 0 ≤ b.T := hbv.hT.le
  haveI : Nonempty (Set.Icc (0 : ℝ) b.T) := ⟨⟨0, le_rfl, hT⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) b.T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) b.T) with hsdef
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hemb := s56_measurableEmbedding_pathCoords (d := d) b.m b.T s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  set m : MeasurableSpace Ω₂ := ⨆ τ ∈ Set.Icc (0 : ℝ) b.T, MeasurableSpace.comap (G τ) inferInstance with hm
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) b.T, MeasurableSpace.comap (G t) inferInstance ≤ m := fun t ht =>
    le_iSup₂ (f := fun τ (_ : τ ∈ Set.Icc (0 : ℝ) b.T) => MeasurableSpace.comap (G τ) inferInstance) t ht
  have hG' : ∀ t ∈ Set.Icc (0 : ℝ) b.T, @Measurable Ω₂ (KSpace d b.m b.T) m _ (G t) := fun t ht =>
    Measurable.of_comap_le (hle t ht)
  have hArr : @Measurable Ω₂ (ℕ × MultiIndex d → ℝ) m _ (s56FArr b s G) := by
    refine @measurable_pi_iff Ω₂ (ℕ × MultiIndex d) (fun _ => ℝ) m _ _ |>.2 fun i => ?_
    exact @Measurable.comp Ω₂ (KSpace d b.m b.T) ℝ m _ _
      (fun x : KSpace d b.m b.T => inner ℝ x (HRS.MS.S52.s52y1 b.m b.T (s i.1) i.2)) (G (s i.1))
      (continuous_id.inner continuous_const).measurable (hG' _ (s i.1).2)
  have hgA : @Measurable Ω₂ (OscPath d b.m b.T) m _ (fun ζ => g (s56FArr b s G ζ)) :=
    @Measurable.comp Ω₂ (ℕ × MultiIndex d → ℝ) (OscPath d b.m b.T) m _ _ g (s56FArr b s G) hgm hArr
  have hae : (fun ζ => windowPathOf b.m b.T 0 (fun t => reconstructPath b.m b.T G ζ t)) =ᵐ[P₂]
      fun ζ => g (s56FArr b s G ζ) := by
    filter_upwards [s56_FArr_range b hbv S N hC hOM hS (S.q N) hq hG s, hG.cont] with ζ h1 hc
    have hrc : ContinuousOn (fun t => reconstructPath b.m b.T G ζ t) (Set.Icc 0 b.T) :=
      continuousOn_iff_continuous_domRestrict.2 (HRS.MS.U9.u9_continuous_recon hT G ζ hc)
    have h2 := s56_pathCoords_windowPathOf (d := d) (m := b.m) (T := b.T) s
      (fun t ζ => reconstructPath b.m b.T G ζ t) hrc
    rw [h1, ← h2]
    exact (congrFun hg _).symm
  refine IndepFun.congr ?_ Filter.EventuallyEq.rfl hae.symm
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right hind hgA.comap_le

end HRS.MS.S21
