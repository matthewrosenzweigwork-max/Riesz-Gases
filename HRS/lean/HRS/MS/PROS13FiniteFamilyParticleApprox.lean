import HRS.MS.PROS13FamilyMoment
import HRS.MS.S21T4ProdZ

/-!
# S13: joint particle-kernel approximation, uniformly in particle number

This result is valid for every probability measure, including atomic ones.
The limiting finite-rank families need not have a common rank or basis.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_particle_family_approx_uniform
    {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ)
    (hj : ℕ → Fin m → Euc d → Euc d → ℝ)
    (hm : ∀ k, MemLp (fun z : Euc d × Euc d => h k z.1 z.2) 2 (μ.prod μ))
    (hmj : ∀ j k, MemLp (fun z : Euc d × Euc d => hj j k z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ k x y, h k x y = h k y x)
    (hsj : ∀ j k x y, hj j k x y = hj j k y x)
    (hT : ∀ k, Tendsto (fun j =>
      eLpNorm (fun z : Euc d × Euc d =>
        h k z.1 z.2 - hj j k z.1 z.2) 2 (μ.prod μ)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ N : ℕ, 2 ≤ N →
      (∑ k : Fin m, ∫ X : EucConfig d N,
        ((N : ℝ) * (pairEnergy (h k) X μ - pairEnergy (hj j k) X μ) +
          (1 / 2 : ℝ) * ∫ x, ∫ y, (h k x y - hj j k x y) ∂μ ∂μ) ^ 2
        ∂(Measure.pi fun _ : Fin N => μ)) < ε := by
  classical
  let D : Fin m → ℕ → Euc d × Euc d → ℝ :=
    fun k j z => h k z.1 z.2 - hj j k z.1 z.2
  have hDm : ∀ k j, MemLp (D k j) 2 (μ.prod μ) :=
    fun k j => (hm k).sub (hmj j k)
  have htk : ∀ k, Tendsto
      (fun j => ∫ z : Euc d × Euc d, (D k j z) ^ 2 ∂(μ.prod μ))
      atTop (𝓝 0) := by
    intro k
    exact s21t4_integral_sq_tendsto_zero (D k) (hDm k) (hT k)
  have hsum : Tendsto
      (fun j => ∑ k : Fin m, ∫ z : Euc d × Euc d,
        (D k j z) ^ 2 ∂(μ.prod μ)) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin m))
      (fun k _ => htk k)
    simpa only [Finset.sum_const_zero] using h
  intro ε hε
  have hε18 : (0 : ℝ) < ε / 18 := by positivity
  have hevent : ∀ᶠ j in atTop,
      (∑ k : Fin m, ∫ z : Euc d × Euc d,
        (D k j z) ^ 2 ∂(μ.prod μ)) < ε / 18 :=
    hsum.eventually (Iio_mem_nhds hε18)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨J, fun j hjJ N hN => ?_⟩
  have hbound := pro_s13_generic_particle_family_difference_L2_bound
    hN h (hj j) hm (hmj j) hs (hsj j)
  have hsmall : (∑ k : Fin m, ∫ z : Euc d × Euc d,
        (h k z.1 z.2 - hj j k z.1 z.2) ^ 2 ∂(μ.prod μ)) < ε / 18 := by
    simpa only [D] using hJ j hjJ
  exact lt_of_le_of_lt hbound (by nlinarith : 
    18 * (∑ k : Fin m, ∫ z : Euc d × Euc d,
        (h k z.1 z.2 - hj j k z.1 z.2) ^ 2 ∂(μ.prod μ)) < ε)

end HRS.MS.R26T3
