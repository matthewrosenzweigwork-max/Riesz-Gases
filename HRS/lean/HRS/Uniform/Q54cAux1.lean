import HRS.Dynamics.Setup

/-!
# Q54c, part 1: the law of a continuous `E_m`-valued process is determined by its coordinate marginals

`toPath_law_eq`: two processes `Y`, `Y'` (on possibly different probability spaces) with a.s. continuous
paths on `[0,T]`, measurable time sections, and the same joint laws of finitely many coordinates
`⟨k⟩^{-m} Ŷ^t(k)` at finitely many times in `[0,T]` have the same law as random elements of the path space
`𝒳_{m,T} = C([0,T]; E_m)`.  (A Lusin–Souslin left inverse of the coordinate map on the Polish space of paths.)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Uniform.Q54c

variable {d : ℕ}

/-- The coordinate map `w ↦ (⟨k⟩^{-m} ŵ(s_n)(k))_{n,k}` of a path at a dense sequence of times. -/
def pathCoords (m T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) :
    PathSpace d m T → (ℕ × NonzeroLattice d → ℝ) :=
  fun w i => NegSobolev.coord (PathSpace.at' w (s i.1)) i.2

theorem continuous_coord (m : ℝ) (k : NonzeroLattice d) :
    Continuous fun F : NegSobolev d m => NegSobolev.coord F k := by
  unfold NegSobolev.coord
  have hl : LipschitzWith 1 fun F : lp (fun _ : NonzeroLattice d => ℝ) 2 => F k := by
    refine LipschitzWith.of_dist_le_mul fun F G => ?_
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (F - G) k
    simpa using this
  exact hl.continuous

theorem measurable_pathCoords (m T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) :
    Measurable (pathCoords (d := d) m T s) := by
  refine measurable_pi_iff.2 fun i => ?_
  have h1 : Continuous fun w : PathSpace d m T => PathSpace.at' w (s i.1) := by
    have : Continuous fun w : C(Set.Icc (0 : ℝ) T, NegSobolev d m) => w (s i.1) :=
      continuous_eval_const (s i.1)
    exact this
  have h2 : Continuous fun F : NegSobolev d m => NegSobolev.coord F i.2 := continuous_coord m i.2
  exact (h2.comp h1).measurable


/-- A finite measure on a countable product of reals is determined by its finite-dimensional marginals. -/
theorem measure_ext_of_restrict {ι : Type*} {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (h : ∀ J : Finset ι, μ.map J.restrict = ν.map J.restrict) : μ = ν := by
  have hr : ∀ J : Finset ι, Measurable (J.restrict : (ι → ℝ) → (J → ℝ)) := fun J =>
    measurable_pi_iff.2 fun i => measurable_pi_apply (i : ι)
  have huniv : μ Set.univ = ν Set.univ := by
    have := congrArg (fun m : Measure ((∅ : Finset ι) → ℝ) => m Set.univ) (h ∅)
    simp only [Measure.map_apply (hr ∅) MeasurableSet.univ, Set.preimage_univ] at this
    exact this
  refine ext_of_generate_finite (measurableCylinders fun _ : ι => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ huniv
  intro t ht
  obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
  have h1 := congrArg (fun m : Measure (J → ℝ) => m S) (h J)
  simp only [Measure.map_apply (hr J) hS] at h1
  exact h1


/-- Injectivity of `pathCoords` for a dense sequence of times. -/
theorem pathCoords_injective (m T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s) :
    Function.Injective (pathCoords (d := d) m T s) := by
  intro w w' h
  have hpt : ∀ n, PathSpace.at' w (s n) = PathSpace.at' w' (s n) := by
    intro n
    have hk : ∀ k, NegSobolev.coord (PathSpace.at' w (s n)) k =
        NegSobolev.coord (PathSpace.at' w' (s n)) k := fun k => congrFun h (n, k)
    refine Subtype.ext (funext fun k => ?_)
    exact hk k
  have hc : Continuous fun t => PathSpace.at' w t :=
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w).continuous
  have hc' : Continuous fun t => PathSpace.at' w' t :=
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w').continuous
  have hfun : (fun t => PathSpace.at' w t) = fun t => PathSpace.at' w' t :=
    hs.equalizer hc hc' (funext hpt)
  exact ContinuousMap.ext fun t => congrFun hfun t

theorem measurableEmbedding_pathCoords (m T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s) :
    MeasurableEmbedding (pathCoords (d := d) m T s) := by
  have : PolishSpace (PathSpace d m T) :=
    inferInstanceAs (PolishSpace C(Set.Icc (0 : ℝ) T, NegSobolev d m))
  exact (measurable_pathCoords m T s).measurableEmbedding (pathCoords_injective m T s hs)


open Classical in
/-- On a path with continuous time sections, `pathCoords ∘ toPath` reads off the coordinates of `Y`. -/
theorem pathCoords_toPath {m T : ℝ} (s : ℕ → Set.Icc (0 : ℝ) T) {Ω : Type*} (Y : ℝ → Ω → NegSobolev d m)
    {ω : Ω} (h : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    pathCoords (d := d) m T s (toPath m T Y ω) = fun i => NegSobolev.coord (Y (s i.1) ω) i.2 := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω := h.comp_continuous continuous_subtype_val
    fun t => t.2
  funext i
  have e : toPath m T Y ω = (⟨fun t : Set.Icc (0 : ℝ) T => Y t ω, hc⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold toPath
    exact dif_pos hc
  rw [pathCoords, e]
  rfl

/-- **Uniqueness in law for continuous processes in `E_m`**: the law of `toPath` is determined by the joint
laws of finitely many coordinates at finitely many times of `[0,T]`. -/
theorem toPath_law_eq {m T : ℝ} (hT : 0 ≤ T) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Y : ℝ → Ω → NegSobolev d m) (Y' : ℝ → Ω' → NegSobolev d m)
    (hm : ∀ t, Measurable (Y t)) (hm' : ∀ t, Measurable (Y' t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (hc' : ∀ᵐ ω ∂P', ContinuousOn (fun t => Y' t ω) (Set.Icc 0 T))
    (hfdd : ∀ (p : ℕ) (ts : Fin p → ℝ) (ks : Fin p → NonzeroLattice d), (∀ a, ts a ∈ Set.Icc 0 T) →
      P.map (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) =
        P'.map (fun ω a => NegSobolev.coord (Y' (ts a) ω) (ks a))) :
    law P (toPath m T Y) = law P' (toPath m T Y') := by
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hsdef
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hemb := measurableEmbedding_pathCoords (d := d) m T s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id
    (fun _ => ⟨0⟩)
  -- the coordinate vectors
  set Ψ₀ : Ω → (ℕ × NonzeroLattice d → ℝ) := fun ω i => NegSobolev.coord (Y (s i.1) ω) i.2 with hΨ₀
  set Ψ₀' : Ω' → (ℕ × NonzeroLattice d → ℝ) := fun ω i => NegSobolev.coord (Y' (s i.1) ω) i.2
    with hΨ₀'
  have hcoordm : ∀ (k : NonzeroLattice d), Measurable fun F : NegSobolev d m => NegSobolev.coord F k :=
    fun k => (continuous_coord m k).measurable
  have hΨm : Measurable Ψ₀ := measurable_pi_iff.2 fun i => (hcoordm i.2).comp (hm _)
  have hΨm' : Measurable Ψ₀' := measurable_pi_iff.2 fun i => (hcoordm i.2).comp (hm' _)
  have hae : toPath m T Y =ᵐ[P] fun ω => g (Ψ₀ ω) := by
    filter_upwards [hc] with ω h
    have := pathCoords_toPath (d := d) s Y h
    have h2 := congrFun hg (toPath m T Y ω)
    simp only [Function.comp, id] at h2
    rw [← h2, this]
  have hae' : toPath m T Y' =ᵐ[P'] fun ω => g (Ψ₀' ω) := by
    filter_upwards [hc'] with ω h
    have := pathCoords_toPath (d := d) s Y' h
    have h2 := congrFun hg (toPath m T Y' ω)
    simp only [Function.comp, id] at h2
    rw [← h2, this]
  have hlaw : P.map Ψ₀ = P'.map Ψ₀' := by
    haveI : IsFiniteMeasure (P.map Ψ₀) := inferInstance
    refine measure_ext_of_restrict fun J => ?_
    have hr : ∀ J : Finset (ℕ × NonzeroLattice d), Measurable
        (J.restrict : (ℕ × NonzeroLattice d → ℝ) → (J → ℝ)) := fun J =>
      measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℕ × NonzeroLattice d)
    rw [Measure.map_map (hr J) hΨm, Measure.map_map (hr J) hΨm']
    let e : J ≃ Fin J.card := J.equivFin
    set ts : Fin J.card → ℝ := fun a => (s (e.symm a).1.1 : ℝ) with hts
    set ks : Fin J.card → NonzeroLattice d := fun a => (e.symm a).1.2 with hks
    have hmem : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T := fun a => (s (e.symm a).1.1).2
    have hf := hfdd J.card ts ks hmem
    have hre : Measurable (fun (v : Fin J.card → ℝ) (j : J) => v (e j)) :=
      measurable_pi_iff.2 fun j => measurable_pi_apply (e j)
    have e1 : (J.restrict ∘ Ψ₀) = (fun (v : Fin J.card → ℝ) (j : J) => v (e j)) ∘
        (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) := by
      funext ω j
      simp [hΨ₀, hts, hks, Function.comp, Finset.restrict]
    have e2 : (J.restrict ∘ Ψ₀') = (fun (v : Fin J.card → ℝ) (j : J) => v (e j)) ∘
        (fun ω a => NegSobolev.coord (Y' (ts a) ω) (ks a)) := by
      funext ω j
      simp [hΨ₀', hts, hks, Function.comp, Finset.restrict]
    have hmv : Measurable (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) :=
      measurable_pi_iff.2 fun a => (hcoordm _).comp (hm _)
    have hmv' : Measurable (fun ω a => NegSobolev.coord (Y' (ts a) ω) (ks a)) :=
      measurable_pi_iff.2 fun a => (hcoordm _).comp (hm' _)
    rw [e1, e2, ← Measure.map_map hre hmv, ← Measure.map_map hre hmv', hf]
  unfold law
  rw [Measure.map_congr hae, Measure.map_congr hae']
  have h1 : (fun ω => g (Ψ₀ ω)) = g ∘ Ψ₀ := rfl
  have h2 : (fun ω => g (Ψ₀' ω)) = g ∘ Ψ₀' := rfl
  rw [h1, h2, ← Measure.map_map hgm hΨm, ← Measure.map_map hgm hΨm', hlaw]

end HRS.Uniform.Q54c
