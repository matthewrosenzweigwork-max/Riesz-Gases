import HRS.MP.SelfSimP1CepaUniq

/-!
# MPP1CEPA (b): measurability of the solution map of the Cépa-Lépingle equation on the line

Part of packet P1 (`HRS/MP/SelfSimSpec.lean`).  Route: Lusin-Souslin (`ContinuousOn.measurableEmbedding`) in place of Souslin
separation.

* `ssp1c_exists_borel_of_graph`: a Borel subset `Γ ⊂ A × B` of a product of Polish spaces whose sections have at most
  one point is the graph of a (globally defined) Borel map `F : A → B` on its projection.
* `ssp1c_ae_eq_map`: a random element `(a, b)` lying in `Γ` almost surely satisfies `b = F ∘ a` a.s.
* `ssp1c_Gamma` is the solution relation `{((x₀, w), x)}` on the path spaces `C([0,T]; ℝ^N)` (`ssp1c_Sol` for the extensions
  of `w`, `x` by constants; collision-free `x₀`); `ssp1c_Gamma_measurableSet` shows it is Borel, `ssp1c_Gamma_unique`
  (from `ssp1c_unique`) that it is a graph.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS.Whole HRS.Whole.AppendixA
open scoped BigOperators

namespace HRS.MP.SelfSimP1

/-! ### Abstract: a Borel graph over its projection -/

section Abstract

variable {A B : Type*} [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B] [Nonempty B]

/-- A Borel relation that is a graph (at most one `b` over each `a`) is the graph of a Borel map `A → B`
(Lusin-Souslin: the projection of `Γ` is injective, hence a measurable embedding). -/
theorem ssp1c_exists_borel_of_graph {Γ : Set (A × B)} (hΓ : MeasurableSet Γ)
    (huniq : ∀ a b b', (a, b) ∈ Γ → (a, b') ∈ Γ → b = b') :
    ∃ F : A → B, Measurable F ∧ ∀ a b, (a, b) ∈ Γ → F a = b := by
  have hinj : InjOn (Prod.fst : A × B → A) Γ := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    simp only at h
    subst h
    rw [huniq a b b' hab hab']
  have hemb := ContinuousOn.measurableEmbedding hΓ continuous_fst.continuousOn hinj
  obtain ⟨F, hFm, hF⟩ := hemb.exists_measurable_extend
    (g := fun p : Γ => p.1.2) (measurable_snd.comp measurable_subtype_coe) (fun _ => ⟨Classical.arbitrary B⟩)
  refine ⟨F, hFm, fun a b hab => ?_⟩
  have := congrFun hF ⟨(a, b), hab⟩
  simpa using this

/-- A random element in a Borel graph is almost surely a Borel function of its first coordinate. -/
theorem ssp1c_ae_eq_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Γ : Set (A × B)}
    (hΓ : MeasurableSet Γ) (huniq : ∀ a b b', (a, b) ∈ Γ → (a, b') ∈ Γ → b = b')
    (a : Ω → A) (b : Ω → B) (hab : ∀ᵐ ω ∂P, (a ω, b ω) ∈ Γ) :
    ∃ F : A → B, Measurable F ∧ ∀ᵐ ω ∂P, b ω = F (a ω) := by
  obtain ⟨F, hF, hFΓ⟩ := ssp1c_exists_borel_of_graph hΓ huniq
  exact ⟨F, hF, by filter_upwards [hab] with ω hω using (hFΓ _ _ hω).symm⟩

end Abstract


/-! ### Path spaces and the drift as a Borel map -/

section Analysis

variable {N : ℕ}

theorem ssp1c_gradient_measurable (f : Euc 1 → ℝ) : Measurable (gradient f) := by
  have h : gradient f = fun x => (InnerProductSpace.toDual ℝ (Euc 1)).symm (fderiv ℝ f x) := rfl
  rw [h]
  exact (InnerProductSpace.toDual ℝ (Euc 1)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem ssp1c_drift_measurable (invβ : ℝ) (i : Fin N) :
    Measurable (fun X : EucConfig 1 N => particleDriftW (ssp1c_D invβ) X i) := by
  have h0 : ∀ y : Euc 1, gradient (fun _ : Euc 1 => (0 : ℝ)) y = 0 := fun y => by simp [gradient]
  have hs : Measurable (fun X : EucConfig 1 N => ∑ j ∈ Finset.univ.erase i,
      Torus.matVec (-1 : Matrix (Fin 1) (Fin 1) ℝ) (rieszKernelGrad 1 0 (X i - X j))) := by
    refine Finset.measurable_sum _ fun j _ => ?_
    have h1 : Measurable (fun X : EucConfig 1 N => X i - X j) :=
      (measurable_pi_apply i).sub (measurable_pi_apply j)
    have h2 : Measurable (rieszKernelGrad 1 0) := ssp1c_gradient_measurable _
    have h3 : Continuous (Torus.matVec (-1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
      LinearMap.continuous_of_finiteDimensional _
    exact h3.measurable.comp (h2.comp h1)
  have : (fun X : EucConfig 1 N => particleDriftW (ssp1c_D invβ) X i) =
      fun X => (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
        Torus.matVec (-1 : Matrix (Fin 1) (Fin 1) ℝ) (rieszKernelGrad 1 0 (X i - X j)) := by
    funext X
    simp only [particleDriftW, ssp1c_D, h0, sub_zero]
  rw [this]
  exact hs.const_smul (1 / (N : ℝ))

/-- The coordinates of a drift-driven equation: for a path `p` and a dense set `D` of times, the integrated equation
on all of `[0,T]` is equivalent to integrability on `[0,T]` and the equation at the times of `D`. -/
theorem ssp1c_eqn_iff_dense (invβ T : ℝ) (hT : 0 ≤ T) {D : Set ℝ} (hD : D ⊆ Icc (0 : ℝ) T)
    (hDd : Icc (0 : ℝ) T ⊆ closure D) {p w : ℝ → EucConfig 1 N} (hp : Continuous p) (hw : Continuous w) :
    (∀ t ∈ Icc (0 : ℝ) T,
      (∀ i, IntegrableOn (fun r : ℝ => particleDriftW (ssp1c_D invβ) (p r) i) (Icc 0 t)) ∧
      ∀ i, p t i = p 0 i + (∫ r in Icc (0 : ℝ) t, particleDriftW (ssp1c_D invβ) (p r) i) +
        Real.sqrt (2 * invβ) • (w t i - w 0 i)) ↔
    ((∀ i, IntegrableOn (fun r : ℝ => particleDriftW (ssp1c_D invβ) (p r) i) (Icc 0 T)) ∧
      ∀ t ∈ D, ∀ i, p t i = p 0 i + (∫ r in Icc (0 : ℝ) t, particleDriftW (ssp1c_D invβ) (p r) i) +
        Real.sqrt (2 * invβ) • (w t i - w 0 i)) := by
  have hT0 : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  constructor
  · intro h
    exact ⟨fun i => (h T hT0).1 i, fun t ht i => (h t (hD ht)).2 i⟩
  · rintro ⟨hint, heq⟩ t ht
    refine ⟨fun i => (hint i).mono_set (Icc_subset_Icc_right ht.2), fun i => ?_⟩
    have hcont : ContinuousOn (fun t : ℝ => ∫ r in Icc (0 : ℝ) t,
        particleDriftW (ssp1c_D invβ) (p r) i) (Icc 0 T) := by
      have h1 := intervalIntegral.continuousOn_primitive_interval
        (μ := volume) (a := 0) (b := T) (f := fun r : ℝ => particleDriftW (ssp1c_D invβ) (p r) i)
        (by rw [uIcc_of_le hT]; exact hint i)
      rw [uIcc_of_le hT] at h1
      refine h1.congr fun s hs => ?_
      dsimp only
      rw [intervalIntegral.integral_of_le hs.1, integral_Icc_eq_integral_Ioc]
    have hL : ContinuousOn (fun t : ℝ => p t i) (Icc 0 T) :=
      ((continuous_apply i).comp hp).continuousOn
    have hR : ContinuousOn (fun t : ℝ => p 0 i + (∫ r in Icc (0 : ℝ) t,
        particleDriftW (ssp1c_D invβ) (p r) i) + Real.sqrt (2 * invβ) • (w t i - w 0 i)) (Icc 0 T) := by
      refine (continuousOn_const.add hcont).add ?_
      exact Continuous.continuousOn (by fun_prop)
    have hEq : EqOn (fun t : ℝ => p t i) (fun t : ℝ => p 0 i + (∫ r in Icc (0 : ℝ) t,
        particleDriftW (ssp1c_D invβ) (p r) i) + Real.sqrt (2 * invβ) • (w t i - w 0 i)) (Icc 0 T) :=
      Set.EqOn.of_subset_closure (fun s hs => heq s hs i) hL hR hD hDd
    exact hEq ht

end Analysis


/-! ### The path space `C([0,T]; ℝ^N)` and the solution relation -/

section PathSpace

variable (T : ℝ) (N : ℕ)

/-- Continuous paths on `[0,T]` with values in `ℝ^N`. -/
abbrev ssp1c_PS : Type := C(Icc (0 : ℝ) T, EucConfig 1 N)

/-- The Borel σ-algebra of the path space (a local instance in this file; downstream files re-declare it). -/
@[instance_reducible] def ssp1c_pathMeas : MeasurableSpace (ssp1c_PS T N) := borel _

attribute [local instance] ssp1c_pathMeas

local instance ssp1c_pathBorel : BorelSpace (ssp1c_PS T N) := ⟨rfl⟩

variable {T N}

/-- Extension of a path on `[0,T]` by constants to all of `ℝ`. -/
def ssp1c_ext (hT : 0 ≤ T) (x : ssp1c_PS T N) (r : ℝ) : EucConfig 1 N :=
  x (Set.projIcc 0 T hT r)

theorem ssp1c_ext_of_mem (hT : 0 ≤ T) (x : ssp1c_PS T N) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    ssp1c_ext hT x r = x ⟨r, hr⟩ := by
  simp [ssp1c_ext, Set.projIcc_of_mem _ hr]

theorem ssp1c_continuous_ext (hT : 0 ≤ T) (x : ssp1c_PS T N) : Continuous (ssp1c_ext hT x) :=
  x.continuous.comp (continuous_projIcc (h := hT))

theorem ssp1c_continuous_ext_joint (hT : 0 ≤ T) :
    Continuous (fun p : ssp1c_PS T N × ℝ => ssp1c_ext hT p.1 p.2) :=
  continuous_eval.comp (continuous_fst.prodMk ((continuous_projIcc (h := hT)).comp continuous_snd))

theorem ssp1c_continuous_ext_param (hT : 0 ≤ T) (r : ℝ) :
    Continuous (fun x : ssp1c_PS T N => ssp1c_ext hT x r) :=
  continuous_eval_const _

/-- The solution relation `Γ = {((x₀, w), x)}`: `x₀` is collision-free and the extension of `x` is an ordered
null-occupation solution on `[0,T]` driven by the extension of `w`. -/
def ssp1c_Gamma (invβ : ℝ) (hT : 0 ≤ T) : Set ((EucConfig 1 N × ssp1c_PS T N) × ssp1c_PS T N) :=
  {q | q.1.1 ∉ eucCollisionSet 1 N ∧ ssp1c_Sol invβ T q.1.1 (ssp1c_ext hT q.1.2) (ssp1c_ext hT q.2)}

/-- `Γ` is a graph: the solution is unique given `(x₀, w)`. -/
theorem ssp1c_Gamma_unique (invβ : ℝ) (hT : 0 ≤ T) :
    ∀ a b b', (a, b) ∈ ssp1c_Gamma (N := N) invβ hT → (a, b') ∈ ssp1c_Gamma (N := N) invβ hT → b = b' := by
  rintro ⟨x₀, w⟩ x y ⟨hx₀, hx⟩ ⟨_, hy⟩
  have := ssp1c_unique invβ T hT hx₀ hx hy
  refine ContinuousMap.ext fun t => ?_
  have h := this t.1 t.2
  rw [ssp1c_ext_of_mem hT x t.2, ssp1c_ext_of_mem hT y t.2] at h
  exact h

end PathSpace


/-! ### The relation `Γ` is Borel -/

section Meas

variable {T : ℝ} {N : ℕ}

attribute [local instance] ssp1c_pathMeas ssp1c_pathBorel

theorem ssp1c_isClosed_collision : IsClosed (eucCollisionSet 1 N) := by
  have : eucCollisionSet 1 N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j), {X : EucConfig 1 N | X i = X j} := by
    ext X; simp [eucCollisionSet]
  rw [this]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)

theorem ssp1c_measurableSet_init (hT : 0 ≤ T) :
    MeasurableSet {q : (EucConfig 1 N × ssp1c_PS T N) × ssp1c_PS T N | ssp1c_ext hT q.2 0 = q.1.1} :=
  (isClosed_eq ((ssp1c_continuous_ext_param hT 0).comp continuous_snd)
    (continuous_fst.comp continuous_fst)).measurableSet

theorem ssp1c_measurable_bfun (invβ : ℝ) (hT : 0 ≤ T) (i : Fin N) :
    Measurable (fun p : ssp1c_PS T N × ℝ => particleDriftW (ssp1c_D invβ) (ssp1c_ext hT p.1 p.2) i) :=
  (ssp1c_drift_measurable invβ i).comp (ssp1c_continuous_ext_joint hT).measurable

theorem ssp1c_measurable_bfun_section (invβ : ℝ) (hT : 0 ≤ T) (i : Fin N) (x : ssp1c_PS T N) :
    Measurable (fun r : ℝ => particleDriftW (ssp1c_D invβ) (ssp1c_ext hT x r) i) := by
  exact (ssp1c_drift_measurable invβ i).comp (ssp1c_continuous_ext hT x).measurable


theorem ssp1c_measurableSet_int (invβ : ℝ) (hT : 0 ≤ T) :
    MeasurableSet {x : ssp1c_PS T N | ∀ i, IntegrableOn
      (fun r : ℝ => particleDriftW (ssp1c_D invβ) (ssp1c_ext hT x r) i) (Icc 0 T)} := by
  have h : {x : ssp1c_PS T N | ∀ i, IntegrableOn
      (fun r : ℝ => particleDriftW (ssp1c_D invβ) (ssp1c_ext hT x r) i) (Icc 0 T)} =
      ⋂ i : Fin N, {x : ssp1c_PS T N | ∫⁻ r in Icc (0 : ℝ) T,
        ‖particleDriftW (ssp1c_D invβ) (ssp1c_ext hT x r) i‖ₑ < ⊤} := by
    ext x
    simp only [mem_setOf_eq, mem_iInter]
    refine forall_congr' fun i => ?_
    have hm := ssp1c_measurable_bfun_section invβ hT i x
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hm.aestronglyMeasurable, h⟩
  rw [h]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable (fun p : ssp1c_PS T N × ℝ =>
      ‖particleDriftW (ssp1c_D invβ) (ssp1c_ext hT p.1 p.2) i‖ₑ) :=
    (ssp1c_measurable_bfun invβ hT i).enorm
  exact measurableSet_lt (hm.lintegral_prod_right' (ν := volume.restrict (Icc (0 : ℝ) T))) measurable_const


theorem ssp1c_measurableSet_eqAt (invβ : ℝ) (hT : 0 ≤ T) (t : ℝ) (i : Fin N) :
    MeasurableSet {q : (EucConfig 1 N × ssp1c_PS T N) × ssp1c_PS T N |
      ssp1c_ext hT q.2 t i = ssp1c_ext hT q.2 0 i +
        (∫ r in Icc (0 : ℝ) t, particleDriftW (ssp1c_D invβ) (ssp1c_ext hT q.2 r) i) +
        Real.sqrt (2 * invβ) • (ssp1c_ext hT q.1.2 t i - ssp1c_ext hT q.1.2 0 i)} := by
  have hf : Measurable (fun q : (EucConfig 1 N × ssp1c_PS T N) × ssp1c_PS T N => ssp1c_ext hT q.2 t i) :=
    ((continuous_apply i).comp ((ssp1c_continuous_ext_param hT t).comp continuous_snd)).measurable
  have hI : Measurable (fun q : (EucConfig 1 N × ssp1c_PS T N) × ssp1c_PS T N =>
      ∫ r in Icc (0 : ℝ) t, particleDriftW (ssp1c_D invβ) (ssp1c_ext hT q.2 r) i) := by
    have hjoint : Measurable (fun p : ((EucConfig 1 N × ssp1c_PS T N) × ssp1c_PS T N) × ℝ =>
        particleDriftW (ssp1c_D invβ) (ssp1c_ext hT p.1.2 p.2) i) :=
      (ssp1c_drift_measurable invβ i).comp ((ssp1c_continuous_ext_joint hT).comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).measurable
    exact (hjoint.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Icc (0 : ℝ) t))).measurable
  have h0 : Measurable (fun q : (EucConfig 1 N × ssp1c_PS T N) × ssp1c_PS T N => ssp1c_ext hT q.2 0 i) :=
    ((continuous_apply i).comp ((ssp1c_continuous_ext_param hT 0).comp continuous_snd)).measurable
  have hd : Measurable (fun q : (EucConfig 1 N × ssp1c_PS T N) × ssp1c_PS T N =>
      ssp1c_ext hT q.1.2 t i - ssp1c_ext hT q.1.2 0 i) := by
    refine Measurable.sub ?_ ?_
    · exact ((continuous_apply i).comp ((ssp1c_continuous_ext_param hT t).comp
        (continuous_snd.comp continuous_fst))).measurable
    · exact ((continuous_apply i).comp ((ssp1c_continuous_ext_param hT 0).comp
        (continuous_snd.comp continuous_fst))).measurable
  have hw := hd.const_smul (Real.sqrt (2 * invβ))
  exact measurableSet_eq_fun hf ((h0.add hI).add hw)


theorem ssp1c_measurableSet_occ (hT : 0 ≤ T) :
    MeasurableSet {q : (EucConfig 1 N × ssp1c_PS T N) × ssp1c_PS T N |
      volume {r : ℝ | r ∈ Icc (0 : ℝ) T ∧ ssp1c_ext hT q.2 r ∈ eucCollisionSet 1 N} = 0} := by
  set Z : Set (ssp1c_PS T N × ℝ) :=
    {p | p.2 ∈ Icc (0 : ℝ) T ∧ ssp1c_ext hT p.1 p.2 ∈ eucCollisionSet 1 N} with hZdef
  have hZ : MeasurableSet Z :=
    ((isClosed_Icc.preimage continuous_snd).inter
      (ssp1c_isClosed_collision.preimage (ssp1c_continuous_ext_joint hT))).measurableSet
  have hm : Measurable (fun x : ssp1c_PS T N => volume (Prod.mk x ⁻¹' Z)) :=
    measurable_measure_prodMk_left hZ
  exact (hm.comp measurable_snd) (measurableSet_singleton 0)

theorem ssp1c_continuous_coord (j : Fin 1) : Continuous (fun v : Euc 1 => v j) :=
  (EuclideanSpace.proj j : Euc 1 →L[ℝ] ℝ).continuous

theorem ssp1c_measurableSet_ord (hT : 0 ≤ T) :
    MeasurableSet {x : ssp1c_PS T N | ∃ π : Equiv.Perm (Fin N), ssp1c_OrdBy T (ssp1c_ext hT x) π} := by
  have h : {x : ssp1c_PS T N | ∃ π : Equiv.Perm (Fin N), ssp1c_OrdBy T (ssp1c_ext hT x) π} =
      ⋃ π : Equiv.Perm (Fin N), ⋂ t : Icc (0 : ℝ) T, ⋂ j : Fin 1, ⋂ k : Fin N, ⋂ k' : Fin N,
        ⋂ (_ : k ≤ k'), {x : ssp1c_PS T N | x t (π k) j ≤ x t (π k') j} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, mem_iInter, ssp1c_OrdBy]
    refine exists_congr fun π => ?_
    constructor
    · intro hπ t j k k' hk
      have := hπ t.1 t.2 j k k' hk
      rw [ssp1c_ext_of_mem hT x t.2] at this
      exact this
    · intro hπ t ht j k k' hk
      have := hπ ⟨t, ht⟩ j k k' hk
      rw [ssp1c_ext_of_mem hT x ht]
      exact this
  rw [h]
  refine MeasurableSet.iUnion fun π => ?_
  refine IsClosed.measurableSet ?_
  refine isClosed_iInter fun t => isClosed_iInter fun j => isClosed_iInter fun k =>
    isClosed_iInter fun k' => isClosed_iInter fun _ => isClosed_le ?_ ?_
  · exact (ssp1c_continuous_coord j).comp ((continuous_apply (π k)).comp (continuous_eval_const t))
  · exact (ssp1c_continuous_coord j).comp ((continuous_apply (π k')).comp (continuous_eval_const t))


/-- **The solution relation is Borel.** -/
theorem ssp1c_Gamma_measurableSet (invβ : ℝ) (hT : 0 ≤ T) :
    MeasurableSet (ssp1c_Gamma (N := N) invβ hT) := by
  haveI : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  set tn : ℕ → ℝ := fun n => ((TopologicalSpace.denseSeq (Icc (0 : ℝ) T) n : Icc (0 : ℝ) T) : ℝ) with htn
  have hD : range tn ⊆ Icc (0 : ℝ) T := by
    rintro _ ⟨n, rfl⟩; exact (TopologicalSpace.denseSeq (Icc (0 : ℝ) T) n).2
  have hDd : Icc (0 : ℝ) T ⊆ closure (range tn) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : Icc (0 : ℝ) T) ∈ closure (range (TopologicalSpace.denseSeq (Icc (0 : ℝ) T))) :=
      (TopologicalSpace.denseRange_denseSeq (Icc (0 : ℝ) T)) _
    have h2 := Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image
      (s := range (TopologicalSpace.denseSeq (Icc (0 : ℝ) T)))
    rw [h2] at h1
    have h3 : (Subtype.val '' range (TopologicalSpace.denseSeq (Icc (0 : ℝ) T))) = range tn := by
      rw [← range_comp]; rfl
    rw [mem_preimage, h3] at h1
    exact h1
  have key : ssp1c_Gamma (N := N) invβ hT =
      {q | q.1.1 ∉ eucCollisionSet 1 N} ∩ ({q | ssp1c_ext hT q.2 0 = q.1.1} ∩
      ((Prod.snd ⁻¹' {x : ssp1c_PS T N | ∀ i, IntegrableOn
          (fun r : ℝ => particleDriftW (ssp1c_D invβ) (ssp1c_ext hT x r) i) (Icc 0 T)}) ∩
      ((⋂ n : ℕ, ⋂ i : Fin N, {q : (EucConfig 1 N × ssp1c_PS T N) × ssp1c_PS T N |
        ssp1c_ext hT q.2 (tn n) i = ssp1c_ext hT q.2 0 i +
        (∫ r in Icc (0 : ℝ) (tn n), particleDriftW (ssp1c_D invβ) (ssp1c_ext hT q.2 r) i) +
        Real.sqrt (2 * invβ) • (ssp1c_ext hT q.1.2 (tn n) i - ssp1c_ext hT q.1.2 0 i)}) ∩
      ({q | volume {r : ℝ | r ∈ Icc (0 : ℝ) T ∧ ssp1c_ext hT q.2 r ∈ eucCollisionSet 1 N} = 0} ∩
      (Prod.snd ⁻¹' {x : ssp1c_PS T N | ∃ π : Equiv.Perm (Fin N), ssp1c_OrdBy T (ssp1c_ext hT x) π}))))) := by
    ext q
    simp only [ssp1c_Gamma, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_iInter]
    constructor
    · rintro ⟨hx₀, hsol⟩
      have hiff := (ssp1c_eqn_iff_dense invβ T hT hD hDd (ssp1c_continuous_ext hT q.2)
        (ssp1c_continuous_ext hT q.1.2)).1 hsol.eqn
      exact ⟨hx₀, hsol.init, hiff.1, fun n i => hiff.2 (tn n) ⟨n, rfl⟩ i, hsol.occ, hsol.ord⟩
    · rintro ⟨hx₀, hinit, hint, heq, hocc, hord⟩
      refine ⟨hx₀, ⟨hinit, ?_, hocc, hord⟩⟩
      refine (ssp1c_eqn_iff_dense invβ T hT hD hDd (ssp1c_continuous_ext hT q.2)
        (ssp1c_continuous_ext hT q.1.2)).2 ⟨hint, ?_⟩
      rintro t ⟨n, rfl⟩ i
      exact heq n i
  rw [key]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter (ssp1c_measurableSet_init hT)
    (MeasurableSet.inter (measurable_snd (ssp1c_measurableSet_int invβ hT))
    (MeasurableSet.inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun i =>
      ssp1c_measurableSet_eqAt invβ hT (tn n) i)
    (MeasurableSet.inter (ssp1c_measurableSet_occ hT) (measurable_snd (ssp1c_measurableSet_ord hT))))))
  exact (ssp1c_isClosed_collision.measurableSet.compl).preimage (measurable_fst.comp measurable_fst)


/-- The product `ℝ^N × C([0,T];ℝ^N)` is Polish (instance search for the product times out, so we assemble it). -/
local instance ssp1c_polish_prod : PolishSpace (EucConfig 1 N × ssp1c_PS T N) :=
  @instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace _ _ inferInstance inferInstance

/-- **The solution map is Borel.**  There is a Borel map `F : ℝ^N × C([0,T];ℝ^N) → C([0,T];ℝ^N)` with
`F (x₀, w) = x` for every ordered null-occupation solution `x` started at the collision-free `x₀` and driven by `w`. -/
theorem ssp1c_solution_map (invβ : ℝ) (hT : 0 ≤ T) :
    ∃ F : EucConfig 1 N × ssp1c_PS T N → ssp1c_PS T N, Measurable F ∧
      ∀ x₀ w x, x₀ ∉ eucCollisionSet 1 N → ssp1c_Sol invβ T x₀ (ssp1c_ext hT w) (ssp1c_ext hT x) →
        F (x₀, w) = x := by
  obtain ⟨F, hF, hFΓ⟩ := ssp1c_exists_borel_of_graph (ssp1c_Gamma_measurableSet (N := N) invβ hT)
    (ssp1c_Gamma_unique invβ hT)
  exact ⟨F, hF, fun x₀ w x hx₀ hsol => hFΓ (x₀, w) x ⟨hx₀, hsol⟩⟩

/-- A map into the path space is measurable as soon as every evaluation is. -/
theorem ssp1c_measurable_of_eval {Ω : Type*} [MeasurableSpace Ω] (hT : 0 ≤ T)
    {f : Ω → ssp1c_PS T N} (hf : ∀ t : Icc (0 : ℝ) T, Measurable fun ω => f ω t) : Measurable f := by
  haveI : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  let d : ℕ → Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Icc (0 : ℝ) T)
  let Φ : ssp1c_PS T N → (ℕ → EucConfig 1 N) := fun g n => g (d n)
  have hΦc : Continuous Φ := continuous_pi fun n => continuous_eval_const (d n)
  have hΦi : Function.Injective Φ := by
    intro g h hgh
    refine ContinuousMap.ext fun t => ?_
    have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq _
    have := hd.equalizer g.continuous h.continuous (funext fun n => congrFun hgh n)
    exact congrFun this t
  have hemb : MeasurableEmbedding Φ := hΦc.measurableEmbedding hΦi
  rw [← hemb.measurable_comp_iff]
  exact measurable_pi_iff.2 fun n => hf (d n)

/-- **Adaptedness form of the solution map.**  If `(x₀, w, x)` is a random triple in the path space which is almost surely
a collision-free-started ordered null-occupation solution, then `x` equals almost surely a Borel function of `(x₀, w)`;
in particular each coordinate `x_t` (`t ∈ [0,T]`) is a Borel function of `(x₀, w)`. -/
theorem ssp1c_ae_eq_solution_map (invβ : ℝ) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x₀ : Ω → EucConfig 1 N) (w x : Ω → ssp1c_PS T N)
    (hsol : ∀ᵐ ω ∂P, x₀ ω ∉ eucCollisionSet 1 N ∧
      ssp1c_Sol invβ T (x₀ ω) (ssp1c_ext hT (w ω)) (ssp1c_ext hT (x ω))) :
    ∃ F : EucConfig 1 N × ssp1c_PS T N → ssp1c_PS T N, Measurable F ∧
      ∀ᵐ ω ∂P, x ω = F (x₀ ω, w ω) := by
  obtain ⟨F, hF, hFx⟩ := ssp1c_solution_map (N := N) invβ hT
  refine ⟨F, hF, ?_⟩
  filter_upwards [hsol] with ω hω using (hFx _ _ _ hω.1 hω.2).symm

end Meas

end HRS.MP.SelfSimP1
