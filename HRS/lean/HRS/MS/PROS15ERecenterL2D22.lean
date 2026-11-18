import HRS.MS.PROS15ERecenterScalarD22

/-!
# S15e: deterministic recentering preserves mean-square limits

The result is stated for an arbitrary probability space. It is used
under the actual normalized exponential tilt, not under an independent
or artificially chosen reference probability law.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15e_recenter_L2_convergence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : ℕ → Ω → ℝ) (G : Ω → ℝ)
    (hF : ∀ n, MemLp (F n) 2 P) (hG : MemLp G 2 P)
    (a : ℕ → ℝ) (c : ℝ)
    (hlim : Tendsto (fun n => ∫ ω, (F n ω - G ω) ^ 2 ∂P) atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 c)) :
    Tendsto (fun n => ∫ ω, ((F n ω - a n) - (G ω - c)) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hpoint : ∀ n ω,
      ((F n ω - a n) - (G ω - c)) ^ 2 ≤
      2 * (F n ω - G ω) ^ 2 + 2 * (a n - c) ^ 2 := by
    intro n ω
    nlinarith [sq_nonneg ((F n ω - G ω) + (a n - c))]
  have hleft : ∀ n, Integrable (fun ω =>
      ((F n ω - a n) - (G ω - c)) ^ 2) P := by
    intro n
    exact (((hF n).sub (memLp_const _)).sub
      (hG.sub (memLp_const _))).integrable_sq
  have hright : ∀ n, Integrable (fun ω =>
      2 * (F n ω - G ω) ^ 2 + 2 * (a n - c) ^ 2) P := by
    intro n
    exact ((((hF n).sub hG).integrable_sq).const_mul 2).add
      (integrable_const _)
  have hbound : ∀ n,
      (∫ ω, ((F n ω - a n) - (G ω - c)) ^ 2 ∂P) ≤
      2 * (∫ ω, (F n ω - G ω) ^ 2 ∂P) +
      2 * (a n - c) ^ 2 := by
    intro n
    calc
      _ ≤ ∫ ω, (2 * (F n ω - G ω) ^ 2 + 2 * (a n - c) ^ 2) ∂P :=
        integral_mono (hleft n) (hright n) (hpoint n)
      _ = (∫ ω, 2 * (F n ω - G ω) ^ 2 ∂P) +
          (∫ _ : Ω, 2 * (a n - c) ^ 2 ∂P) :=
        integral_add ((((hF n).sub hG).integrable_sq).const_mul 2)
          (integrable_const _)
      _ = _ := by rw [integral_const_mul]; simp
  have hcs : Tendsto (fun n => 2 * (a n - c) ^ 2) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    have hsub := ha.sub hconst
    have hsq := hsub.pow 2
    have hh := hsq.const_mul 2
    simpa using hh
  have htop : Tendsto (fun n =>
      2 * (∫ ω, (F n ω - G ω) ^ 2 ∂P) + 2 * (a n - c) ^ 2)
      atTop (𝓝 0) := by
    convert (hlim.const_mul 2).add hcs using 1 <;> ring
  exact squeeze_zero
    (fun n => integral_nonneg (fun ω => sq_nonneg _))
    hbound htop

#print axioms s15e_recenter_L2_convergence
end HRS.MS.R26T3
