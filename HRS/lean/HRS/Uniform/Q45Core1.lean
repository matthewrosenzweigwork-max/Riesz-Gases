import HRS.Uniform.Q45Win2

/-!
# Q45: the grid limit `n → ∞` of the test-function expectations
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

lemma projB_sub {d : ℕ} (b : Fin d → E) (v w : E) : projB b (v - w) = projB b v - projB b w := by
  unfold projB
  simp [inner_sub_right, sub_smul, Finset.sum_sub_distrib]

lemma continuous_projB {d : ℕ} (b : Fin d → E) : Continuous (projB b) := by
  unfold projB
  fun_prop

lemma pcm_vpath_add_window {T K : ℝ} (S : EvolData H E) (hS : S.MaxHyp T K) (x : H) (Z : ℝ → Ω → E)
    {ω : Ω} (hω : ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) (t : Set.Icc (0 : ℝ) T) :
    pcm (vpath S hS.1 x + windowPath 0 T Z ω) t = S.VE (t : ℝ) 0 (S.j x) + Z (t : ℝ) ω := by
  rw [pcm_add, pcm_vpath, pcm_windowPath Z hω]

/-- The finite-dimensional approximants converge in expectation. -/
theorem core_limit {T K : ℝ} (hT : 0 < T) (S : EvolData H E) (hS : S.MaxHyp T K)
    {d : ℕ → ℕ} {b : ∀ n, Fin (d n) → E} (hb : ∀ n, Orthonormal ℝ (b n))
    (hspat : ∀ (y : PathSp T E) (ε : ℝ), 0 < ε → ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t : Set.Icc (0 : ℝ) T,
      ‖pcm y t - ∑ a, inner ℝ (b n a) (pcm y t) • b n a‖ ≤ ε)
    {ℱ : Filtration ℝ mΩ} (X₀ : Ω → H) (hX : Measurable[ℱ 0] X₀) (Z : ℝ → Ω → E)
    (hZm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Z t))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    {Φ : PathSp T E → ℝ} (hΦ : Φ ∈ CbUnitBall (PathSp T E) 2) :
    Tendsto (fun n : ℕ => ∫ ω, Φ (hatPath T (n + 1) (fun i =>
        projB (b n) (S.VE (unifPart T (n + 1) i) 0 (S.j (X₀ ω)) + Z (unifPart T (n + 1) i) ω))) ∂P)
      atTop (𝓝 (∫ ω, Φ (vpath S hS.1 (X₀ ω) + windowPath 0 T Z ω) ∂P)) := by
  obtain ⟨hΦc, hΦb, -, -⟩ := cbUnit_bounds hΦ
  have hX' : Measurable X₀ := hX.mono (ℱ.le 0) le_rfl
  have hmeasB : ∀ n : ℕ, Measurable fun ω => hatPath T (n + 1) (fun i =>
      projB (b n) (S.VE (unifPart T (n + 1) i) 0 (S.j (X₀ ω)) + Z (unifPart T (n + 1) i) ω)) := by
    intro n
    have : Measurable fun ω => (fun i : Fin (n + 1 + 1) =>
        projB (b n) (S.VE (unifPart T (n + 1) i) 0 (S.j (X₀ ω)) + Z (unifPart T (n + 1) i) ω)) :=
      measurable_pi_iff.2 fun i =>
        (continuous_projB (b n)).measurable.comp
          ((((S.VE _ 0).continuous.comp S.j.continuous).measurable.comp hX').add
            (hZm _ ⟨unifPart_nonneg hT.le _ _, gridT_le hT (Nat.le_add_left 1 n) i⟩))
    exact (continuous_hatPath hT (Nat.le_add_left 1 n)).measurable.comp this
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n =>
    (hΦc.continuous.measurable.comp (hmeasB n)).aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hΦb _) ?_
  filter_upwards [hZc] with ω hω
  set Y : PathSp T E := vpath S hS.1 (X₀ ω) + windowPath 0 T Z ω with hY
  have hsamp : ∀ (n : ℕ) (i : Fin (n + 1 + 1)), samplePath hT.le (n + 1) Y i =
      S.VE (unifPart T (n + 1) i) 0 (S.j (X₀ ω)) + Z (unifPart T (n + 1) i) ω := by
    intro n i
    unfold samplePath
    have hi : (i : ℝ) * T / ((n + 1 : ℕ) : ℝ) ∈ Set.Icc 0 T :=
      ⟨by positivity, gridT_le hT (Nat.le_add_left 1 n) i⟩
    have := pcm_vpath_add_window S hS (X₀ ω) Z hω ⟨_, hi⟩
    rw [Set.projIcc_of_mem hT.le hi]
    simpa [unifPart] using this
  have hconv : Tendsto (fun n : ℕ => hatPath T (n + 1) (fun i =>
      projB (b n) (S.VE (unifPart T (n + 1) i) 0 (S.j (X₀ ω)) + Z (unifPart T (n + 1) i) ω))) atTop
      (𝓝 Y) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n0, hn0⟩ := lambda_approx hT hb hspat Y (show 0 < ε / 2 by positivity)
    refine ⟨n0, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have := hn0 n hn
    have e : (fun i : Fin (n + 1 + 1) => projB (b n) (samplePath hT.le (n + 1) Y i)) =
        fun i : Fin (n + 1 + 1) => projB (b n) (S.VE (unifPart T (n + 1) i) 0 (S.j (X₀ ω)) +
          Z (unifPart T (n + 1) i) ω) := by
      funext i; rw [hsamp]
    rw [e] at this
    linarith
  exact (hΦc.continuous.tendsto Y).comp hconv

end HRS.Uniform.Q45
