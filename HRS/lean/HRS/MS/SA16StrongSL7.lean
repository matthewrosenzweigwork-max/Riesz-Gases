import HRS.MS.SA16StrongDefs

/-!
# S.A.16 SL7: `strong_limit_of_dense_cauchy`

A common operator bound and dense-set uniform Cauchy data give, in a Banach space, a uniform strong
limit by bounded linear operators, continuous in time for each fixed vector.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

theorem strong_limit_of_dense_cauchy
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T M : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (S : Set X) (hS : Dense S) (U : ℕ → ℝ → X →L[ℝ] X)
    (hcont : ∀ n x, ContinuousOn (fun t => U n t x) (Icc (0 : ℝ) T))
    (hbound : ∀ n, ∀ t ∈ Icc (0 : ℝ) T, ‖U n t‖ ≤ M)
    (hCauchy : ∀ x ∈ S, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ k ≥ n₀, ∀ t ∈ Icc (0 : ℝ) T, ‖U n t x-U k t x‖ < ε) :
    ∃ V : ℝ → X →L[ℝ] X,
      (∀ t ∈ Icc (0 : ℝ) T, ‖V t‖ ≤ M) ∧
      (∀ x, ContinuousOn (fun t => V t x) (Icc (0 : ℝ) T)) ∧
      ∀ x, StrongUniformLimit T (fun n t => U n t x) (fun t => V t x) := by
  classical
  -- Step 1: uniform Cauchy property for every vector
  have hAll : ∀ x : X, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ k ≥ n₀, ∀ t ∈ Icc (0 : ℝ) T, ‖U n t x - U k t x‖ < ε := by
    intro x ε hε
    have hδ : 0 < ε / (4 * (M + 1)) := by positivity
    obtain ⟨s, hs, hxs⟩ := hS.exists_dist_lt x hδ
    obtain ⟨n₀, hn₀⟩ := hCauchy s hs (ε / 2) (by positivity)
    refine ⟨n₀, fun n hn k hk t ht => ?_⟩
    have h1 : ‖U n t (x - s)‖ ≤ M * (ε / (4 * (M + 1))) := by
      calc ‖U n t (x - s)‖ ≤ ‖U n t‖ * ‖x - s‖ := (U n t).le_opNorm _
        _ ≤ M * (ε / (4 * (M + 1))) := by
            refine mul_le_mul (hbound n t ht) ?_ (norm_nonneg _) hM
            rw [dist_eq_norm] at hxs
            exact hxs.le
    have h2 : ‖U k t (x - s)‖ ≤ M * (ε / (4 * (M + 1))) := by
      calc ‖U k t (x - s)‖ ≤ ‖U k t‖ * ‖x - s‖ := (U k t).le_opNorm _
        _ ≤ M * (ε / (4 * (M + 1))) := by
            refine mul_le_mul (hbound k t ht) ?_ (norm_nonneg _) hM
            rw [dist_eq_norm] at hxs
            exact hxs.le
    have h3 := hn₀ n hn k hk t ht
    have hMε : M * (ε / (4 * (M + 1))) ≤ ε / 4 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc ‖U n t x - U k t x‖
        = ‖U n t (x - s) + (U n t s - U k t s) - U k t (x - s)‖ := by
          congr 1; simp only [map_sub]; abel
      _ ≤ ‖U n t (x - s)‖ + ‖U n t s - U k t s‖ + ‖U k t (x - s)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ < ε := by linarith
  -- Step 2: pointwise limits
  have hlim : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : X, ∃ y, Tendsto (fun n => U n t x) atTop (𝓝 y) := by
    intro t ht x
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨n₀, hn₀⟩ := hAll x ε hε
    exact ⟨n₀, fun n hn => by rw [dist_eq_norm]; exact hn₀ n hn n₀ le_rfl t ht⟩
  choose! Vl hVl using hlim
  have hadd : ∀ t ∈ Icc (0 : ℝ) T, ∀ x y : X, Vl t (x + y) = Vl t x + Vl t y := by
    intro t ht x y
    refine tendsto_nhds_unique (hVl t ht (x + y)) ?_
    have := (hVl t ht x).add (hVl t ht y)
    simpa [map_add] using this
  have hsmul : ∀ t ∈ Icc (0 : ℝ) T, ∀ (c : ℝ) (x : X), Vl t (c • x) = c • Vl t x := by
    intro t ht c x
    refine tendsto_nhds_unique (hVl t ht (c • x)) ?_
    have := (hVl t ht x).const_smul c
    simpa [map_smul] using this
  have hbd : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : X, ‖Vl t x‖ ≤ M * ‖x‖ := by
    intro t ht x
    refine le_of_tendsto (hVl t ht x).norm (Eventually.of_forall fun n => ?_)
    exact ((U n t).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hbound n t ht) (norm_nonneg _))
  let Vt : ∀ t ∈ Icc (0 : ℝ) T, X →L[ℝ] X := fun t ht =>
    LinearMap.mkContinuous
      { toFun := Vl t, map_add' := hadd t ht, map_smul' := hsmul t ht } M (hbd t ht)
  let V : ℝ → X →L[ℝ] X := fun t => if h : t ∈ Icc (0 : ℝ) T then Vt t h else 0
  have hV : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, V t x = Vl t x := by
    intro t ht x
    show (if h : t ∈ Icc (0 : ℝ) T then Vt t h else 0) x = Vl t x
    rw [dif_pos ht]
    rfl
  -- uniform convergence
  have hunif : ∀ x : X, StrongUniformLimit T (fun n t => U n t x) (fun t => V t x) := by
    intro x ε hε
    obtain ⟨n₀, hn₀⟩ := hAll x (ε / 2) (by positivity)
    refine ⟨n₀, fun n hn t ht => ?_⟩
    show ‖U n t x - V t x‖ < ε
    rw [hV t ht x]
    have : ‖U n t x - Vl t x‖ ≤ ε / 2 := by
      refine le_of_tendsto (tendsto_const_nhds.sub (hVl t ht x)).norm
        (Filter.eventually_atTop.2 ⟨n₀, fun k hk => (hn₀ n hn k hk t ht).le⟩)
    linarith
  refine ⟨V, fun t ht => ?_, fun x => ?_, hunif⟩
  · have : V t = Vt t ht := dif_pos ht
    rw [this]
    exact LinearMap.mkContinuous_norm_le _ hM _
  · have hu : TendstoUniformlyOn (fun n t => U n t x) (fun t => V t x) atTop (Icc (0 : ℝ) T) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨n₀, hn₀⟩ := hunif x ε hε
      refine Filter.eventually_atTop.2 ⟨n₀, fun n hn t ht => ?_⟩
      rw [dist_comm, dist_eq_norm]
      exact hn₀ n hn t ht
    exact hu.continuousOn (Eventually.of_forall fun n => hcont n x).frequently

end HRS.Whole.AppendixA.Phase2SA16
