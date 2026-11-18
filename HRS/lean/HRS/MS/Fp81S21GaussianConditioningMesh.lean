import HRS.MS.Fp81S21GaussianConditioningLimits

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MS.R2Interp
open scoped BigOperators

namespace HRS.Fp81.S21

def fp81s21_meshN (n : ℕ) : ℕ := n + 1

def fp81s21_meshPoint (H : ℝ) (n i : ℕ) : ℝ :=
  (i : ℝ) * (H / (fp81s21_meshN n : ℝ))

def fp81s21_meshWidth (H : ℝ) (n : ℕ) : ℝ := H / (fp81s21_meshN n : ℝ)

/-- Uniform partitions meet the hypotheses of the conditioned RS limit. -/
theorem fp81s21_uniform_mesh (H : ℝ) (hH : 0 ≤ H) :
    (∀ n, fp81s21_meshPoint H n 0 = 0) ∧
    (∀ n, fp81s21_meshPoint H n (fp81s21_meshN n) = H) ∧
    (∀ n i, i < fp81s21_meshN n →
      fp81s21_meshPoint H n i ≤ fp81s21_meshPoint H n (i + 1)) ∧
    (∀ n i, i < fp81s21_meshN n →
      fp81s21_meshPoint H n (i + 1) - fp81s21_meshPoint H n i ≤
        fp81s21_meshWidth H n) ∧
    Tendsto (fp81s21_meshWidth H) atTop (𝓝 0) := by
  have hp (n : ℕ) : (0 : ℝ) < (fp81s21_meshN n : ℝ) := by
    simp only [fp81s21_meshN, Nat.cast_add, Nat.cast_one]
    positivity
  have hw (n : ℕ) : 0 ≤ fp81s21_meshWidth H n :=
    div_nonneg hH (le_of_lt (hp n))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp [fp81s21_meshPoint]
  · intro n
    simp [fp81s21_meshPoint, mul_div_cancel₀ _ (ne_of_gt (hp n))]
  · intro n i hi
    apply mul_le_mul_of_nonneg_right _ (hw n)
    exact_mod_cast Nat.le_succ i
  · intro n i hi
    dsimp [fp81s21_meshPoint, fp81s21_meshWidth]
    push_cast
    ring_nf
    exact le_rfl
  · have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul H
    change Tendsto (fun n : ℕ => H / ((↑(n + 1) : ℝ))) atTop (𝓝 0)
    simpa [Nat.cast_add, div_eq_mul_inv] using ht

/-- A certified RS value is the limit along the uniform right-endpoint sums. -/
theorem fp81s21_uniform_rs_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ) (hH : 0 ≤ H) (A : ℝ → E →L[ℝ] ℝ) (F : ℝ → E) (I : ℝ)
    (hI : fp81s21_IsRSOn 0 H (fun τ u v => A τ (F v - F u)) I) :
    Tendsto (fun n => ∑ i ∈ Finset.range (fp81s21_meshN n),
      A (fp81s21_meshPoint H n (i + 1))
        (F (fp81s21_meshPoint H n (i + 1)) - F (fp81s21_meshPoint H n i)))
      atTop (𝓝 I) := by
  by_cases hz : H = 0
  · subst H
    have hzero : I = 0 := fp81s21_isRSOn_zero_forces hI
    subst I
    simpa [fp81s21_meshPoint] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hpos : 0 < H := lt_of_le_of_ne hH (Ne.symm hz)
    have hR : IsR2RS H (fun τ u v => A τ (F v - F u)) I := by
      simpa [fp81s21_IsRSOn] using hI
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨δ, hδ, hRS⟩ := fp81s21_rR_nat_of_IsR2RS hR ε hε
    have hm := (fp81s21_uniform_mesh H hH).2.2.2.2
    have he : ∀ᶠ n in atTop, fp81s21_meshWidth H n < δ :=
      hm.eventually (eventually_lt_nhds hδ)
    obtain ⟨N, hN⟩ := eventually_atTop.mp he
    refine ⟨N, ?_⟩
    intro n hn
    have hw : 0 < fp81s21_meshWidth H n := by
      apply div_pos hpos
      simp only [fp81s21_meshN, Nat.cast_add, Nat.cast_one]
      positivity
    have ha : fp81s21_RAdm 0 H (fp81s21_meshN n) (fp81s21_meshPoint H n)
        (fun i => fp81s21_meshPoint H n (i + 1)) := by
      refine ⟨(fp81s21_uniform_mesh H hH).1 n,
        (fp81s21_uniform_mesh H hH).2.1 n, ?_, ?_⟩
      · intro i j hij hj
        dsimp [fp81s21_meshPoint]
        apply mul_lt_mul_of_pos_right _ hw
        exact_mod_cast hij
      · intro i hi
        exact ⟨(fp81s21_uniform_mesh H hH).2.2.1 n i hi, le_rfl⟩
    have hmesh : fp81s21_RMesh δ (fp81s21_meshN n) (fp81s21_meshPoint H n) := by
      intro i hi
      exact lt_of_le_of_lt ((fp81s21_uniform_mesh H hH).2.2.2.1 n i hi) (hN n hn)
    simpa only [Real.dist_eq] using hRS (fp81s21_meshN n) (fp81s21_meshPoint H n)
      (fun i => fp81s21_meshPoint H n (i + 1)) ha hmesh

/-- The same limit holds almost everywhere for the supplied RS window. -/
theorem fp81s21_uniform_window_rs_limit
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) (H : ℝ) (hH : 0 ≤ H)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (W : fp81s21_RSBVWindow P H A F) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ Finset.range (fp81s21_meshN n),
      A ω (fp81s21_meshPoint H n (i + 1))
        (F ω (fp81s21_meshPoint H n (i + 1)) - F ω (fp81s21_meshPoint H n i)))
      atTop (𝓝 (W.value 0 H ω)) := by
  filter_upwards [W.value_isRS 0 H le_rfl hH le_rfl] with ω hω
  exact fp81s21_uniform_rs_limit H hH (A ω) (F ω) _ hω

#print axioms fp81s21_uniform_mesh
#print axioms fp81s21_uniform_rs_limit
#print axioms fp81s21_uniform_window_rs_limit
end HRS.Fp81.S21
end
