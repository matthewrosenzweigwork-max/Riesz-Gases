import HRS.MS.R2InterpAux114

/-!
# S10.2 (worker S10R), part 115 (packet M3h): measurability of `ζ ↦ ∫ cylA`, `∫ cylJ`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

/-- The observed predicted path is a jointly measurable function of `(u,ζ)`. -/
theorem s102_obsY_jmeas (hS : S102Std C m T r c) (hT : 0 < T) (L : ℕ) {N : ℕ} (hN : 0 < N) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N)
    (hXm : ∀ t, Measurable (X t)) (hXjm : ∀ t ∈ Icc (0 : ℝ) T, Measurable fun q : ℝ × Ω => X (min q.1 t).toNNReal q.2) :
    ∃ Ob : ℝ × Ω → EuclideanSpace ℝ (Fin (s102_q d L)), Measurable Ob ∧
      ∀ u : ℝ, 0 ≤ u → ∀ ζ, (EuclideanSpace.equiv (Fin (s102_q d L)) ℝ).symm
        (fun i => s102_zf P X ζ (min u (s102_tk hT L i)) (s102_orb C m hT L i (min u (s102_tk hT L i)))) = Ob (u, ζ) := by
  choose F hFm hFeq using fun i : Fin (s102_q d L) =>
    s102_zf_orb_jmeas hN P X hXm (s102_tauk hT L i).2.1 (s102_orb_classical hS hT L i)
      (hXjm _ (s102_tauk hT L i).2)
  refine ⟨fun q => (EuclideanSpace.equiv (Fin (s102_q d L)) ℝ).symm (fun i => F i q), ?_, fun u hu ζ => ?_⟩
  · exact (EuclideanSpace.equiv (Fin (s102_q d L)) ℝ).symm.continuous.measurable.comp (measurable_pi_iff.2 hFm)
  · congr 1
    funext i
    exact hFeq i u hu ζ

theorem s102_heatFderiv_meas (hT : 0 < T) (L : ℕ) (hG : S102GramInt C m hT L) (γ : ℝ → Measure (OscPath d m T))
    (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ} (hG2 : MemCb 2 G) (i : Fin (s102_q d L)) :
    Measurable fun p : ℝ × EuclideanSpace ℝ (Fin (s102_q d L)) =>
      if p.1 ∈ Icc (0 : ℝ) T then
        fderiv ℝ (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G p.1) p.2 (EuclideanSpace.single i 1)
      else 0 := by
  classical
  have hcont := s102_heatDeriv_cont hT L hG γ hγ hG2 (j := 1) (by norm_num)
  have h2 := (HRS.MC.Sec7.S7PIL.S7PIL_ev (fun _ : Fin 1 => (EuclideanSpace.single i (1 : ℝ) :
    EuclideanSpace ℝ (Fin (s102_q d L))))).continuous.comp_continuousOn hcont
  have h3 : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (s102_q d L)) =>
      fderiv ℝ (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G p.1) p.2 (EuclideanSpace.single i 1))
      (Icc 0 T ×ˢ univ) := by
    refine h2.congr fun p hp => ?_
    simp [HRS.MC.Sec7.S7PIL.S7PIL_ev_apply, iteratedFDeriv_one_apply]
  have hset : MeasurableSet (Icc (0 : ℝ) T ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (s102_q d L))))) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have := ContinuousOn.measurable_piecewise (g := fun _ => (0 : ℝ)) h3 continuousOn_const hset
  have e : (fun p : ℝ × EuclideanSpace ℝ (Fin (s102_q d L)) =>
      if p.1 ∈ Icc (0 : ℝ) T then
        fderiv ℝ (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G p.1) p.2 (EuclideanSpace.single i 1)
      else 0) = Set.piecewise (Icc (0 : ℝ) T ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (s102_q d L)))))
        (fun p : ℝ × EuclideanSpace ℝ (Fin (s102_q d L)) =>
          fderiv ℝ (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G p.1) p.2 (EuclideanSpace.single i 1))
        (fun _ => (0 : ℝ)) := by
    funext p
    simp only [Set.piecewise, mem_prod, mem_univ, and_true]
  rw [e]
  exact this

theorem s102_heatD2_meas (hT : 0 < T) (L : ℕ) (hG : S102GramInt C m hT L) (γ : ℝ → Measure (OscPath d m T))
    (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ} (hG2 : MemCb 2 G) (i j : Fin (s102_q d L)) :
    Measurable fun p : ℝ × EuclideanSpace ℝ (Fin (s102_q d L)) =>
      if p.1 ∈ Icc (0 : ℝ) T then
        iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G p.1) p.2
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
      else 0 := by
  classical
  have hcont := s102_heatDeriv_cont hT L hG γ hγ hG2 (j := 2) le_rfl
  have h3 := (HRS.MC.Sec7.S7PIL.S7PIL_ev (![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j 1] :
    Fin 2 → EuclideanSpace ℝ (Fin (s102_q d L)))).continuous.comp_continuousOn hcont
  have h3' : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (s102_q d L)) =>
      iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G p.1) p.2
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) (Icc 0 T ×ˢ univ) := h3
  have hset : MeasurableSet (Icc (0 : ℝ) T ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (s102_q d L))))) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have := ContinuousOn.measurable_piecewise (g := fun _ => (0 : ℝ)) h3' continuousOn_const hset
  have e : (fun p : ℝ × EuclideanSpace ℝ (Fin (s102_q d L)) =>
      if p.1 ∈ Icc (0 : ℝ) T then
        iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G p.1) p.2
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
      else 0) = Set.piecewise (Icc (0 : ℝ) T ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (s102_q d L)))))
        (fun p : ℝ × EuclideanSpace ℝ (Fin (s102_q d L)) =>
          iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G p.1) p.2
            ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) (fun _ => (0 : ℝ)) := by
    funext p
    simp only [Set.piecewise, mem_prod, mem_univ, and_true]
  rw [e]
  exact this

end HRS.MS.R2Interp

end
