import HRS.MS.S81sRecent
import HRS.MS.S81sDuhamel
import HRS.MS.S81sRecentPhys
import HRS.MS.GenPathAux31

/-!
# S8.1 (worker S81S): auxiliary facts for the product-space glue

Namespace `HRS.Whole.S81S`, prefix `s81s_`.

* `s81s_W0`, `s81s_canonical_W0`: a canonical realization with its filtered form `(ℱ, W')` is again a canonical realization for the everywhere
  defined (continuous, adapted) driver `W₀ = W'` read as a vector, whose coordinates are exactly `W'` (so that the frozen producers, which need the
  Brownian property of `W` itself, apply).
* `s81s_proc_comp`, `s81s_L2_comp`, `s81s_indepFun_comp`, `s81s_comap_proc`: transport of processes, `L²` sizes and independence along a
  measure-preserving map.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.Whole.S81P

namespace HRS.Whole.S81S

section Driver

variable {d N : ℕ} {Ω : Type}

/-- The vector-valued driver whose coordinates are `W'`. -/
def s81s_W0 (d N : ℕ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) : ℝ≥0 → Ω → (Fin N → Euc d) :=
  fun t z i => WithLp.toLp 2 (fun j => W' t z (i, j))

theorem s81s_canonical_W0 {s a β : ℝ} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hR : IsCanonicalRealization d s a β N P X₀ W X)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
    (hF : IsWholeFilteredSolution P ℱ W' W X) :
    IsCanonicalRealization d s a β N P X₀ (s81s_W0 d N W') X ∧
      IsWholeFilteredSolution P ℱ W' (s81s_W0 d N W') X := by
  have hW0 : ∀ᵐ ζ ∂P, ∀ t, s81s_W0 d N W' t ζ = W t ζ := by
    filter_upwards [hF.coords] with ζ hζ t
    funext i
    ext j
    simp [s81s_W0, hζ t i j]
  have hF' : IsWholeFilteredSolution P ℱ W' (s81s_W0 d N W') X :=
    { brownian := hF.brownian
      coords := Filter.Eventually.of_forall fun ζ t i j => rfl
      adapted := hF.adapted
      progressive := hF.progressive }
  refine ⟨?_, hF'⟩
  refine
    { brownian := ?_
      indep := ?_
      init := hR.init
      solution := fun T' => ?_
      filtered := ⟨ℱ, W', hF'⟩
      invariant := hR.invariant }
  · refine ⟨fun i j => ?_, ?_⟩
    · have h := hR.brownian.1 i j
      refine ⟨h.toIsPreBrownianReal.congr (fun t => ?_), Filter.Eventually.of_forall fun ω => ?_⟩
      · filter_upwards [hW0] with ζ hζ
        simp [hζ t]
      · exact (continuous_apply (i, j)).comp (hF.brownian.cont ω)
    · have h := hR.brownian.2
      refine (iIndepFun_congr (fun ij => ?_)).1 h
      filter_upwards [hW0] with ζ hζ
      funext t
      simp [hζ t]
  · refine IndepFun.congr hR.indep Filter.EventuallyEq.rfl ?_
    filter_upwards [hW0] with ζ hζ
    funext t
    exact (hζ t).symm
  · have hsol := hR.solution T'
    refine { hsol with eqn := ?_ }
    filter_upwards [hsol.eqn, hW0] with ζ h1 h2
    intro t ht
    obtain ⟨hint, heq⟩ := h1 t ht
    refine ⟨hint, fun i => ?_⟩
    rw [heq i, h2 t, h2 0]

end Driver

section Transport

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ} {m T : ℝ}

theorem s81s_proc_comp {P : Measure Ω} {Q : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π Q P)
    {Y : ℝ → Ω → OscDual d m} (hY : S81PProc P T Y) : S81PProc Q T (fun t ζ => Y t (π ζ)) :=
  ⟨fun t => (hY.1 t).comp hπ.measurable, hπ.quasiMeasurePreserving.ae hY.2⟩

theorem s81s_L2_comp {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {Q : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π Q P) (hT : 0 ≤ T)
    {Y : ℝ → Ω → OscDual d m} (hY : S81PProc P T Y) :
    s81p_L2 Q (processWindow m T 0 (fun t ζ => Y t (π ζ))) = s81p_L2 P (processWindow m T 0 Y) := by
  unfold s81p_L2
  congr 1
  have hae : AEMeasurable (fun ζ => ENNReal.ofReal (‖processWindow m T 0 Y ζ‖ ^ (2 : ℝ))) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (((hY.aemeasurable hT).norm).pow_const (2 : ℝ))
  have hae' : AEMeasurable (fun ζ => ENNReal.ofReal (‖processWindow m T 0 Y ζ‖ ^ (2 : ℝ)))
      (Measure.map π Q) := by rw [hπ.map_eq]; exact hae
  have := lintegral_map' hae' (hπ.aemeasurable)
  rw [hπ.map_eq] at this
  exact this.symm

/-- Independence of two (measurable) random elements is preserved by pulling back along a measure-preserving map. -/
theorem s81s_indepFun_comp {E E' : Type*} [MeasurableSpace E] [MeasurableSpace E'] {P : Measure Ω}
    {Q : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π Q P) {f : Ω → E} {g : Ω → E'}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun f g P) :
    IndepFun (fun ζ => f (π ζ)) (fun ζ => g (π ζ)) Q := by
  have := s81s_indep_comp (MeasurableSpace.comap f inferInstance) (MeasurableSpace.comap g inferInstance)
    hπ hf.comap_le hg.comap_le h
  rw [IndepFun_iff_Indep]
  rwa [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp] at this

/-- The σ-algebra of a process (as a map into the product space) is the supremum of the σ-algebras of its time sections. -/
theorem s81s_comap_proc {E : Type*} [MeasurableSpace E] (Y : ℝ → Ω → E) :
    MeasurableSpace.comap (fun ζ (t : ℝ) => Y t ζ) inferInstance =
      ⨆ t : ℝ, MeasurableSpace.comap (Y t) inferInstance := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp]
  rfl

end Transport

section ZetaProc

variable {d N : ℕ}

/-- The centered particle process `t ↦ ζ_N(u+t)` is a measurable, a.s. continuous `B_m`-valued process (stationary realizations). -/
theorem s81s_zeta_proc (hd : 2 ≤ d) {a β : ℝ} (m : ℝ) (hm : (d : ℝ) < m) (hN : 1 ≤ N) (T u : ℝ) (hu : 0 ≤ u)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hR : IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X) :
    S81PProc P T (fun t ζ => zetaB m (P.map (X (Real.toNNReal (u + t)))) (X (Real.toNNReal (u + t)) ζ)) := by
  have hNpos : 0 < N := by omega
  have hXm : ∀ t, Measurable (X t) := fun t => (hR.solution t).adapted t
  have hlaw : ∀ t : ℝ≥0, P.map (X t) =
      HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β :=
    fun t => HRS.Whole.S79.s79_law_X_eq hR t
  haveI hP0 : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).2 inferInstance
  set νb : Measure (Euc d) := HRS.Whole.meanEmpirical (P.map (X 0)) with hνb
  haveI : IsProbabilityMeasure νb := HRS.Whole.meanEmpirical_isProbabilityMeasure _ hN
  have hz : ∀ t : ℝ, ∀ x : EucConfig d N, zetaB m (P.map (X (Real.toNNReal (u + t)))) x =
      Real.sqrt N • OscDual.ofMeasureDiff m (HRS.Whole.empirical x) νb := by
    intro t x
    unfold zetaB
    rw [hlaw (Real.toNNReal (u + t)), ← hlaw 0]
  have hd1 : 1 ≤ d := by omega
  have hcont := HRS.MS.GenPath.s56_xi_cont_config hd1 hm (Real.sqrt N) hNpos νb
  refine ⟨fun t => ?_, ?_⟩
  · show Measurable fun ζ => zetaB m (P.map (X (Real.toNNReal (u + t)))) (X (Real.toNNReal (u + t)) ζ)
    have : (fun ζ => zetaB m (P.map (X (Real.toNNReal (u + t)))) (X (Real.toNNReal (u + t)) ζ)) =
        fun ζ => Real.sqrt N • OscDual.ofMeasureDiff m (HRS.Whole.empirical (X (Real.toNNReal (u + t)) ζ)) νb := by
      funext ζ; exact hz t _
    rw [this]
    exact hcont.measurable.comp (hXm _)
  · filter_upwards [(hR.solution 0).cont] with ζ hζ
    have hx : Continuous fun t : ℝ≥0 => X t ζ := continuous_pi hζ
    have h1 := HRS.Whole.S79.s79_continuous_window (m := m) hNpos hm νb u T (fun t => X t ζ) hx
    have h2 : Continuous fun t : Set.Icc (0 : ℝ) T =>
        Real.sqrt N • OscDual.ofMeasureDiff m (HRS.Whole.empirical (X (Real.toNNReal (u + t)) ζ)) νb :=
      (continuous_const_smul (Real.sqrt N)).comp h1
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    have : (Set.Icc (0 : ℝ) T).domRestrict (fun t => zetaB m (P.map (X (Real.toNNReal (u + t)))) (X (Real.toNNReal (u + t)) ζ)) =
        fun t : Set.Icc (0 : ℝ) T =>
          Real.sqrt N • OscDual.ofMeasureDiff m (HRS.Whole.empirical (X (Real.toNNReal (u + t)) ζ)) νb := by
      funext t; exact hz t _
    rw [this]; exact h2

end ZetaProc


end HRS.Whole.S81S
