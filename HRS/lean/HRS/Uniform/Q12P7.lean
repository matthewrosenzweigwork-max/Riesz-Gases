import HRS.Uniform.Q12P6

/-!
# Q12, Peyre part 7: cluster points of probability measures on a compact space
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q12

instance q12_borel_prod {d : ℕ} : BorelSpace (Torus d × Torus d) := Prod.borelSpace

section Cluster

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [BorelSpace X]
  [CompactSpace X]

/-- A cluster point (along `atTop`) of a sequence of probability measures on a compact space,
which is a cluster point of every integral against a continuous function. -/
lemma q12_exists_cluster (ξ : ℕ → ProbabilityMeasure X) :
    ∃ π : ProbabilityMeasure X, ∀ φ : X → ℝ, Continuous φ →
      ClusterPt (∫ x, φ x ∂(π : Measure X)) (map (fun n => ∫ x, φ x ∂(ξ n : Measure X)) atTop) := by
  obtain ⟨π, hπ⟩ := exists_clusterPt_of_compactSpace (map ξ atTop)
  refine ⟨π, fun φ hφ => ?_⟩
  let f : BoundedContinuousFunction X ℝ := BoundedContinuousFunction.mkOfCompact ⟨φ, hφ⟩
  have hc := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
  set g : ProbabilityMeasure X → ℝ := fun μ => ∫ x, f x ∂(μ : Measure X) with hg
  have htend : Tendsto g (map ξ atTop) (map (fun n => g (ξ n)) atTop) := by
    unfold Tendsto
    rw [Filter.map_map]
    exact le_rfl
  have := hπ.map hc.continuousAt htend
  simpa [f, hg] using this

end Cluster


lemma q12_clusterPt_eq {u : ℕ → ℝ} {a c : ℝ} (hu : Tendsto u atTop (𝓝 c))
    (h : ClusterPt a (map u atTop)) : a = c := by
  have h2 : ClusterPt a (𝓝 c) := h.mono hu
  exact eq_of_nhds_neBot h2

lemma q12_clusterPt_le {u : ℕ → ℝ} {a b : ℝ} (hu : ∀ᶠ n in atTop, u n ≤ b)
    (h : ClusterPt a (map u atTop)) : a ≤ b := by
  have hmem : {y : ℝ | y ≤ b} ∈ map u atTop := hu
  have := h.mem_closure_of_mem _ hmem
  rwa [show {y : ℝ | y ≤ b} = Iic b from rfl, closure_Iic] at this

variable {d : ℕ}

/-- Existence of a limiting coupling. -/
theorem q12_weak_limit (μ0 μ1 : Measure (Torus d)) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μ1] (π : ℕ → Measure (Torus d × Torus d))
    (hπp : ∀ n, IsProbabilityMeasure (π n)) (hfst : ∀ n, (π n).map Prod.fst = μ0)
    (hsnd : ∀ φ : Torus d → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂((π n).map Prod.snd)) atTop (𝓝 (∫ x, φ x ∂μ1)))
    (A : ℝ) (hcost : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∫ z, Torus.tdist z.1 z.2 ^ 2 ∂(π n) ≤ A + ε) :
    ∃ π' : Measure (Torus d × Torus d), IsProbabilityMeasure π' ∧ π'.map Prod.fst = μ0 ∧
      π'.map Prod.snd = μ1 ∧ ∫ z, Torus.tdist z.1 z.2 ^ 2 ∂π' ≤ A := by
  let ξ : ℕ → ProbabilityMeasure (Torus d × Torus d) := fun n => ⟨π n, hπp n⟩
  obtain ⟨π', hcl⟩ := q12_exists_cluster ξ
  refine ⟨(π' : Measure (Torus d × Torus d)), inferInstance, ?_, ?_, ?_⟩
  · refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    have hfc : Continuous fun z : Torus d × Torus d => f z.1 := f.continuous.comp continuous_fst
    have h1 := hcl _ hfc
    have h2 : ∀ n, ∫ z, f z.1 ∂(ξ n : Measure (Torus d × Torus d)) = ∫ x, f x ∂μ0 := fun n => by
      show ∫ z, f z.1 ∂(π n) = _
      rw [← hfst n, integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    simp_rw [h2] at h1
    have h3 := q12_clusterPt_eq (u := fun _ => ∫ x, f x ∂μ0) tendsto_const_nhds h1
    rw [integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    exact h3
  · refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    have hfc : Continuous fun z : Torus d × Torus d => f z.2 := f.continuous.comp continuous_snd
    have h1 := hcl _ hfc
    have h2 : ∀ n, ∫ z, f z.2 ∂(ξ n : Measure (Torus d × Torus d)) =
        ∫ x, f x ∂((π n).map Prod.snd) := fun n => by
      show ∫ z, f z.2 ∂(π n) = _
      rw [integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    simp_rw [h2] at h1
    have h3 := q12_clusterPt_eq (hsnd f f.continuous) h1
    rw [integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    exact h3
  · have hc : Continuous fun z : Torus d × Torus d => Torus.tdist z.1 z.2 ^ 2 :=
      Uniform.Q14.q14_continuous_tdist.pow 2
    have h1 := hcl _ hc
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact q12_clusterPt_le (hcost ε hε) h1

end HRS.Uniform.Q12
