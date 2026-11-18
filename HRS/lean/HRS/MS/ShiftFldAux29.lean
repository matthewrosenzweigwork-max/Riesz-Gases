import HRS.MS.ShiftFldAux28

/-!
# S79P: stationarity of the Gaussian window (`GaussianWindowStationary`)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd HRS.MS.GenPath
open HRS (Euc)

variable {d : ℕ}

local notation "mm" => ((wholeSpaceIndex d : ℕ) : ℝ)

theorem s79g_fdd {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {C : WholeCoeff d} {m q H : ℝ} {C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ} {Z : ℝ → Ω' → OscDual d m}
    (hZ : IsLinearGaussianEvolutionW P' C m q H C₀ Z) {p : ℕ} (ts : Fin p → ℝ)
    (hts : ∀ a, ts a ∈ Icc (0 : ℝ) H) (αs : Fin p → MultiIndex d) :
    P'.map (fun ζ => (WithLp.toLp 2 fun a => OscDual.coord (Z (ts a) ζ) (αs a) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a c =>
        C₀ (propagatorW C 0 (ts a) (oscTestFun m (αs a))) (propagatorW C 0 (ts c) (oscTestFun m (αs c))) +
          noiseCovW C q (ts a) (ts c) (oscTestFun m (αs a)) (oscTestFun m (αs c))) := by
  have h := hZ.gaussian p ts (fun a => oscTestFun m (αs a)) hts (fun a => s56_isOscTest m (αs a))
  simp only [OscDual.eval_oscTestFun] at h
  exact h

theorem s79g_gauss_stationary (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) : HRS.Whole.S79.GaussianWindowStationary d s a β := by
  intro T hT ρβ hρβ Ω' _ P' _ Z hZ a₀ ha₀
  have hρeq : ρβ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs.le hsd ha hβ hρβ
  subst hρeq
  have hZT := hZ T
  have hZH := hZ (a₀ + T)
  let Z' : ℝ → Ω' → OscDual d mm := fun t ζ => Z (a₀ + t) ζ
  have hZ'm : ∀ t, Measurable (Z' t) := fun t => hZH.meas (a₀ + t)
  have hZ'c : ∀ᵐ ζ ∂P', ContinuousOn (fun t => Z' t ζ) (Icc 0 T) := by
    filter_upwards [hZH.cont] with ζ hζ
    exact hζ.comp (continuousOn_const.add continuousOn_id)
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hae' : AEMeasurable (processWindow mm T 0 Z') P' := by
    have h := HRS.GF.gfb4_aemeasurable_windowPath P' hT.le Z' (fun t _ => hZ'm t) hZ'c
    rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
    exact h
  have hae0 : AEMeasurable (processWindow mm T 0 Z) P' := by
    have h := HRS.GF.gfb4_aemeasurable_windowPath P' hT.le Z (fun t _ => hZT.meas t) hZT.cont
    rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
    exact h
  have hshift : processWindow mm T a₀ Z = processWindow mm T 0 Z' := funext fun ζ =>
    HRS.Whole.S79.s79p_processWindow_shift T a₀ Z ζ
  rw [hshift]
  refine ⟨hae', ?_⟩
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  set sq : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hsq
  have hdense : DenseRange sq := TopologicalSpace.denseRange_denseSeq _
  have hlaw : P'.map (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Z (sq i.1) ζ) i.2) =
      P'.map (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Z' (sq i.1) ζ) i.2) := by
    have hmΨ : Measurable (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Z (sq i.1) ζ) i.2) :=
      measurable_pi_iff.2 fun i => (s56_continuous_coord mm i.2).measurable.comp (hZT.meas _)
    have hmΨ' : Measurable (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Z' (sq i.1) ζ) i.2) :=
      measurable_pi_iff.2 fun i => (s56_continuous_coord mm i.2).measurable.comp (hZ'm _)
    refine s56_seq_law_eq P' P' _ _ hmΨ.aemeasurable hmΨ'.aemeasurable fun p f _ => ?_
    have hts : ∀ a, ((sq (f a).1 : Set.Icc (0 : ℝ) T) : ℝ) ∈ Icc (0 : ℝ) T := fun a => (sq (f a).1).2
    have hts' : ∀ a, a₀ + ((sq (f a).1 : Set.Icc (0 : ℝ) T) : ℝ) ∈ Icc (0 : ℝ) (a₀ + T) := fun a =>
      ⟨by linarith [(sq (f a).1).2.1], by linarith [(sq (f a).1).2.2]⟩
    have e1 := s79g_fdd P' hZT (fun a => ((sq (f a).1 : Set.Icc (0 : ℝ) T) : ℝ)) hts (fun a => (f a).2)
    have e2 := s79g_fdd P' hZH (fun a => a₀ + ((sq (f a).1 : Set.Icc (0 : ℝ) T) : ℝ)) hts'
      (fun a => (f a).2)
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    ext a c
    simp only [Matrix.of_apply]
    exact (s79g_Kcov_shift hd hs hsd ha hβ hρβ mm (f a).2 (f c).2 (sq (f a).1).2.1 (sq (f c).1).2.1 ha₀).symm
  have key := s56_path_law_eq hT.le P' P' Z Z' hZT.meas hZ'm hZT.cont hZ'c sq hdense hlaw
  exact key.symm

end HRS.MS.S79G
