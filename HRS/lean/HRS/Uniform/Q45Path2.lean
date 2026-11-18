import HRS.Uniform.Q45Path1

/-!
# Q45: finite-rank orthogonal projections in a separable Hilbert space, uniform on paths
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]

/-- A finite orthonormal family, whose orthogonal projections approximate the identity uniformly on every
compact set of vectors (in particular on the range of a path). -/
theorem exists_spatial_approx (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] :
    ∃ (d : ℕ → ℕ) (b : ∀ n, Fin (d n) → E), (∀ n, Orthonormal ℝ (b n)) ∧
      ∀ (T : ℝ) (y : PathSp T E) (ε : ℝ), 0 < ε → ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t : Set.Icc (0 : ℝ) T,
        ‖pcm y t - ∑ a, inner ℝ (b n a) (pcm y t) • b n a‖ ≤ ε := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq E
  set U : ℕ → Submodule ℝ E := fun n => Submodule.span ℝ (e '' (Set.Iio n)) with hU
  have hUfin : ∀ n, FiniteDimensional ℝ (U n) := fun n => by
    haveI : Finite (e '' (Set.Iio n)) := (Set.finite_Iio n).image e |>.to_subtype
    exact FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio n).image e)
  have hUmono : Monotone U := fun m n hmn =>
    Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hmn))
  let B : ∀ n, OrthonormalBasis (Fin (Module.finrank ℝ (U n))) ℝ (U n) := fun n =>
    haveI := hUfin n
    stdOrthonormalBasis ℝ (U n)
  have hproj : ∀ n (v : E), ∑ a, inner ℝ ((B n a : U n) : E) v • ((B n a : U n) : E) =
      (U n).starProjection v := by
    intro n v
    haveI := hUfin n
    have := congrArg (fun (F : E →L[ℝ] E) => F v)
      (OrthonormalBasis.starProjection_eq_sum_rankOne (B n)).symm
    simpa using this
  refine ⟨fun n => Module.finrank ℝ (U n), fun n a => ((B n a : U n) : E), fun n => ?_, ?_⟩
  · exact (B n).orthonormal.comp_linearIsometry (U n).subtypeₗᵢ
  · intro T y ε hε
    simp only [hproj]
    -- distance to `U n`
    set F : ℕ → Set.Icc (0 : ℝ) T → ℝ := fun n t => ‖pcm y t - (U n).starProjection (pcm y t)‖ with hF
    have hFeq : ∀ n t, F n t = Metric.infDist (pcm y t) (U n) := by
      intro n t
      haveI := hUfin n
      simp only [hF]
      rw [Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
      simp [dist_eq_norm]
    have hFcont : ∀ n, Continuous (F n) := fun n => by
      haveI := hUfin n
      exact ((pcm y).continuous.sub ((U n).starProjection.continuous.comp (pcm y).continuous)).norm
    have hFanti : Antitone F := fun m n hmn t => by
      simp only [hFeq]
      exact Metric.infDist_le_infDist_of_subset (SetLike.coe_subset_coe.2 (hUmono hmn))
        ⟨0, (U m).zero_mem⟩
    have hFlim : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 0) := by
      intro t
      rw [Metric.tendsto_atTop]
      intro η hη
      obtain ⟨i, hi⟩ := Metric.denseRange_iff.1 he (pcm y t) η hη
      refine ⟨i + 1, fun n hn => ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by simp only [hF]; exact norm_nonneg _), hFeq]
      calc Metric.infDist (pcm y t) (U n) ≤ dist (pcm y t) (e i) :=
            Metric.infDist_le_dist_of_mem (Submodule.subset_span ⟨i, by simp; omega, rfl⟩)
        _ < η := hi
    have hunif := Antitone.tendstoUniformly_of_forall_tendsto (F := F) (f := fun _ => (0 : ℝ))
      hFcont hFanti continuous_const hFlim
    rw [Metric.tendstoUniformly_iff] at hunif
    obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1 (hunif ε hε)
    refine ⟨n0, fun n hn t => ?_⟩
    have := hn0 n hn t
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (by simp only [hF]; exact norm_nonneg _)] at this
    exact this.le

end HRS.Uniform.Q45
