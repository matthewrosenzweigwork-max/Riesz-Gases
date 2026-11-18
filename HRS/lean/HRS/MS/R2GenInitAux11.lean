import HRS.MS.R2GenInitStat
import HRS.MS.GenPathTie

/-!
# S10.5 window comparison, packet A0: the identity evolution is dissipative with constant `0`

The abstract comparison theorems of Section 3 (`smooth_path_comparison`, `maximal_estimate`) have constants depending on the
horizon through `detConst T K = K^2 + exp(|K| T/2) + 1`.  For the window comparison of S10.5 the horizon is `b + T` and the constants
must be independent of `b`.  The identity evolution satisfies the "one dissipative level" alternative of `EvolData.MaxHyp` with `K = 0`
(`A = 0`), for which `detConst T 0 = 2`.  Here: a sequence of finite-rank orthogonal projections converging strongly to the identity in
a separable Hilbert space (needed for the Galerkin clause), and `s105_idEvol_maxHyp_zero`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Uniform HRS.MS.GenPath

theorem s105_proj_seq (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] :
    ∃ P : ℕ → H →L[ℝ] H, (∀ n, (P n).comp (P n) = P n) ∧ (∀ n x y, inner ℝ (P n x) y = inner ℝ x (P n y)) ∧
      (∀ n, FiniteDimensional ℝ (LinearMap.range (P n : H →ₗ[ℝ] H))) ∧
      ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x) := by
  have : Nonempty H := ⟨0⟩
  set s : ℕ → H := TopologicalSpace.denseSeq H with hs
  have hdense : DenseRange s := TopologicalSpace.denseRange_denseSeq H
  set U : ℕ → Submodule ℝ H := fun n => Submodule.span ℝ (s '' Set.Iio n) with hU
  have hfin : ∀ n, FiniteDimensional ℝ (U n) := fun n =>
    FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio n).image s)
  have : ∀ n, (U n).HasOrthogonalProjection := fun n => inferInstance
  refine ⟨fun n => (U n).starProjection, fun n => ?_, fun n x y => ?_, fun n => ?_, fun x => ?_⟩
  · exact (U n).isIdempotentElem_starProjection
  · exact (U n).inner_starProjection_left_eq_right x y
  · have : LinearMap.range ((U n).starProjection : H →ₗ[ℝ] H) = U n := by
      have := (U n).range_starProjection
      exact this
    rw [this]
    exact hfin n
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := hdense.exists_dist_lt x (half_pos hε)
    refine ⟨k + 1, fun n hn => ?_⟩
    have hmem : s k ∈ U n := Submodule.subset_span ⟨k, by simp only [Set.mem_Iio]; omega, rfl⟩
    have hmin := (U n).starProjection_minimal x
    have hle : ‖x - (U n).starProjection x‖ ≤ ‖x - s k‖ := by
      rw [hmin]
      exact ciInf_le (f := fun w : U n => ‖x - (w : H)‖) ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
        (⟨s k, hmem⟩ : U n)
    rw [dist_comm, dist_eq_norm]
    have hk' : ‖x - s k‖ < ε / 2 := by rwa [dist_eq_norm] at hk
    linarith

theorem s105_idEvol_dissipative (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [SecondCountableTopology K] (T : ℝ) : (s56_idEvol K).Dissipative T 0 := by
  obtain ⟨P, hPi, hPs, hPf, hPt⟩ := s105_proj_seq K
  refine ⟨fun x => rfl, fun y => ⟨y, rfl⟩, ?_, ?_, P, fun n _ _ => P n, hPi, hPs, hPf, ?_, hPt, ?_, ?_, ?_, ?_⟩
  · intro r _ z
    rw [s56_idEvol_A]
    simp
  · intro r _ t _ x
    refine ⟨Submodule.mem_top, ?_⟩
    rw [s56_idEvol_A]
    exact hasDerivWithinAt_const _ _ _
  · intro n x
    exact Submodule.mem_top
  · intro n r x _
    rfl
  · intro n t r x
    exact ⟨x, rfl⟩
  · intro n r t x y h _ _ _
    rw [s56_idEvol_A]
    simpa using hasDerivWithinAt_const t (Set.Icc r T) (inner ℝ y (P n x))
  · intro r _ t _ x
    exact hPt x

theorem s105_idEvol_maxHyp_zero (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [SecondCountableTopology K] (T : ℝ) : (s56_idEvol K).MaxHyp T 0 :=
  ⟨s56_idEvol_isEvolution T, Or.inr (s105_idEvol_dissipative K T)⟩

end HRS.MS.R2GenInit
