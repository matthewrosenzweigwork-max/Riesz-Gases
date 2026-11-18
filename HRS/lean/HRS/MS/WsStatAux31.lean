import HRS.MS.WsStatAux30

/-!
# S21 packet L-2: law of a Gaussian process with covariance `Cc + Cn` as a convolution

`s21_Zlaw`: let `Z` be a continuous `B_m`-valued process whose finite-dimensional Hermite-coordinate laws are
`multivariateGaussian 0 (Sigma_c + Sigma_n)`, and `gamma0`, `Gamma` probability measures on the path space whose finite-dimensional
coordinate laws are `multivariateGaussian 0 Sigma_c`, `multivariateGaussian 0 Sigma_n` with positive semidefinite matrices.  Then
`law (window Z) = gamma0 * Gamma` (convolution).  Proof: the laws of paths are determined by the coordinate arrays at a dense set of times
(`s56_path_law_eq`, `s56_seq_law_eq`), and the coordinates of `(w, v) |-> w + v` under the product measure are an independent sum of
Gaussians (`s21_gauss_conv`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc)

variable {d : ℕ}

theorem s21_Zlaw (m T : ℝ) (hT : 0 ≤ T) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (Zh : ℝ → Ω' → OscDual d m) (hZm : ∀ t, Measurable (Zh t))
    (hZc : ∀ᵐ ζ ∂P', ContinuousOn (fun t => Zh t ζ) (Set.Icc 0 T))
    (Cc Cn : ℝ → ℝ → MultiIndex d → MultiIndex d → ℝ)
    (γ0 Γ : Measure (OscPath d m T)) [IsProbabilityMeasure γ0] [IsProbabilityMeasure Γ]
    (hZ : ∀ (p : ℕ) (ts : Fin p → ℝ) (_ : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
      P'.map (fun ζ => (WithLp.toLp 2 fun a => OscDual.coord (Zh (ts a) ζ) (αs a) :
          EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => Cc (ts a) (ts c) (αs a) (αs c) +
          Cn (ts a) (ts c) (αs a) (αs c)))
    (hγ : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
      (Matrix.of fun a c => Cc (ts a) (ts c) (αs a) (αs c)).PosSemidef ∧
      γ0.map (fun w : OscPath d m T => (WithLp.toLp 2 fun a => OscDual.coord (OscPath.at' w ⟨ts a, hts a⟩)
          (αs a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => Cc (ts a) (ts c) (αs a) (αs c)))
    (hΓ : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
      (Matrix.of fun a c => Cn (ts a) (ts c) (αs a) (αs c)).PosSemidef ∧
      Γ.map (fun w : OscPath d m T => (WithLp.toLp 2 fun a => OscDual.coord (OscPath.at' w ⟨ts a, hts a⟩)
          (αs a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => Cn (ts a) (ts c) (αs a) (αs c))) :
    law P' (processWindow m T 0 Zh) = (γ0.prod Γ).map (fun z : OscPath d m T × OscPath d m T => z.1 + z.2) := by
  classical
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hsdef
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  set Y' : ℝ → (OscPath d m T × OscPath d m T) → OscDual d m :=
    fun t z => s56Ext hT z.1 t + s56Ext hT z.2 t with hY'
  have hY'm : ∀ t, Measurable (Y' t) := fun t =>
    (s56Ext_meas hT _ measurable_fst t).add (s56Ext_meas hT _ measurable_snd t)
  have hY'c : ∀ᵐ z ∂(γ0.prod Γ), ContinuousOn (fun t => Y' t z) (Set.Icc 0 T) :=
    Filter.Eventually.of_forall fun z => ((s56Ext_cont hT z.1).add (s56Ext_cont hT z.2)).continuousOn
  have hwin : ∀ z : OscPath d m T × OscPath d m T, windowPathOf m T 0 (fun t => Y' t z) = z.1 + z.2 := by
    intro z
    refine ContinuousMap.ext fun t => ?_
    have hc : ContinuousOn (fun t => Y' t z) (Set.Icc 0 T) :=
      ((s56Ext_cont hT z.1).add (s56Ext_cont hT z.2)).continuousOn
    have := s56_wpo_apply (m := m) (T := T) hc t
    show (show C(Set.Icc (0 : ℝ) T, OscDual d m) from windowPathOf m T 0 _) t = _
    rw [this]
    simp only [hY']
    rw [s56Ext_of_mem hT z.1 t.2, s56Ext_of_mem hT z.2 t.2]
    rfl
  have hΨm : Measurable (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Zh (s i.1) ζ) i.2) :=
    measurable_pi_iff.2 fun i => (s56_continuous_coord m i.2).measurable.comp (hZm _)
  have hΨ'm : Measurable (fun z (i : ℕ × MultiIndex d) =>
      OscDual.coord (Y' (s i.1) z) i.2) :=
    measurable_pi_iff.2 fun i => (s56_continuous_coord m i.2).measurable.comp (hY'm _)
  have hlaw : P'.map (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Zh (s i.1) ζ) i.2) =
      (γ0.prod Γ).map (fun z (i : ℕ × MultiIndex d) => OscDual.coord (Y' (s i.1) z) i.2) := by
    refine s56_seq_law_eq P' (γ0.prod Γ) _ _ hΨm.aemeasurable hΨ'm.aemeasurable fun p f _ => ?_
    have hL := hZ p (fun a => ((s (f a).1 : Set.Icc (0 : ℝ) T) : ℝ)) (fun a => (s (f a).1).2)
      (fun a => (f a).2)
    have h1 := hγ p (fun a => ((s (f a).1 : Set.Icc (0 : ℝ) T) : ℝ)) (fun a => (s (f a).1).2)
      (fun a => (f a).2)
    have h2 := hΓ p (fun a => ((s (f a).1 : Set.Icc (0 : ℝ) T) : ℝ)) (fun a => (s (f a).1).2)
      (fun a => (f a).2)
    set v1 : OscPath d m T → EuclideanSpace ℝ (Fin p) := fun w => (WithLp.toLp 2 fun a =>
      OscDual.coord (OscPath.at' w ⟨((s (f a).1 : Set.Icc (0 : ℝ) T) : ℝ), (s (f a).1).2⟩) (f a).2 :
        EuclideanSpace ℝ (Fin p)) with hv1
    have hv1m : Measurable v1 := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
      have h1 : Continuous fun w : OscPath d m T => OscPath.at' w ⟨((s (f a).1 : Set.Icc (0 : ℝ) T) : ℝ),
          (s (f a).1).2⟩ := by
        have : Continuous fun w : C(Set.Icc (0 : ℝ) T, OscDual d m) =>
            w ⟨((s (f a).1 : Set.Icc (0 : ℝ) T) : ℝ), (s (f a).1).2⟩ := continuous_eval_const _
        exact this
      exact ((s56_continuous_coord m (f a).2).comp h1).measurable
    have hfun : (fun z : OscPath d m T × OscPath d m T => (WithLp.toLp 2 fun a =>
        OscDual.coord (Y' (s (f a).1) z) (f a).2 : EuclideanSpace ℝ (Fin p))) =
        fun z => v1 z.1 + v1 z.2 := by
      funext z
      ext a
      simp only [hY', hv1, OscDual.coord_add, PiLp.add_apply, WithLp.ofLp_toLp]
      rw [s56Ext_of_mem hT z.1 (s (f a).1).2, s56Ext_of_mem hT z.2 (s (f a).1).2]
      rfl
    rw [hfun]
    have hmp : (γ0.prod Γ).map (fun z : OscPath d m T × OscPath d m T => v1 z.1 + v1 z.2) =
        ((γ0.map v1).prod (Γ.map v1)).map (fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) =>
          z.1 + z.2) := by
      have hadd : Measurable (fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) => z.1 + z.2) :=
        measurable_fst.add measurable_snd
      rw [Measure.map_prod_map γ0 Γ hv1m hv1m, Measure.map_map hadd (hv1m.prodMap hv1m)]
      rfl
    rw [hmp, h1.2, h2.2, s21_gauss_conv h1.1 h2.1]
    rw [hL]
    congr 1
  have key := s56_path_law_eq hT P' (γ0.prod Γ) Zh Y' hZm hY'm hZc hY'c s hs hlaw
  show law P' (fun ζ => windowPathOf m T 0 (fun t => Zh t ζ)) = _
  rw [key]
  unfold law
  congr 1
  funext z
  exact hwin z

end HRS.MS.S21
