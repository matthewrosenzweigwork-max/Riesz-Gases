import HRS.MS.S21T4ProdCB
import HRS.MS.S21T4ProdBY
import HRS.MS.S21L_S13V

/-!
# S13: simultaneous L² bounds for finite families of general product kernels

These estimates are uniform in particle number and accommodate atomic
reference measures. The Gaussian quadratic comparisons use the SAME isonormal
field on both sides. They are the quantitative inputs for a common-space
convergence-together argument, not a closure of the generic S13 contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_particle_family_L2_bound
    {m N : ℕ} (hN : 2 ≤ N) (h : Fin m → Euc d → Euc d → ℝ)
    (hm : ∀ k, MemLp (fun z : Euc d × Euc d => h k z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ k x y, h k x y = h k y x) :
    (∑ k : Fin m, ∫ X : EucConfig d N,
       ((N : ℝ) * pairEnergy (h k) X μ +
         (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ) ^ 2
       ∂(Measure.pi fun _ : Fin N => μ)) ≤
      18 * ∑ k : Fin m, ∫ z : Euc d × Euc d,
        (h k z.1 z.2) ^ 2 ∂(μ.prod μ) := by
  have hb : ∀ k : Fin m,
      (∫ X : EucConfig d N,
         ((N : ℝ) * pairEnergy (h k) X μ +
           (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ) ^ 2
         ∂(Measure.pi fun _ : Fin N => μ)) ≤
      18 * ∫ z : Euc d × Euc d, (h k z.1 z.2) ^ 2 ∂(μ.prod μ) :=
    fun k => s21l_s13_variance μ hN (h k) (hm k) (hs k)
  simpa only [Finset.mul_sum] using
    (Finset.sum_le_sum (s := Finset.univ) (fun k _ => hb k))

theorem pro_s13_generic_particle_family_difference_L2_bound
    {m N : ℕ} (hN : 2 ≤ N)
    (h h' : Fin m → Euc d → Euc d → ℝ)
    (hm : ∀ k, MemLp (fun z : Euc d × Euc d => h k z.1 z.2) 2 (μ.prod μ))
    (hm' : ∀ k, MemLp (fun z : Euc d × Euc d => h' k z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ k x y, h k x y = h k y x)
    (hs' : ∀ k x y, h' k x y = h' k y x) :
    (∑ k : Fin m, ∫ X : EucConfig d N,
       ((N : ℝ) * (pairEnergy (h k) X μ - pairEnergy (h' k) X μ) +
          (1 / 2 : ℝ) * ∫ x, ∫ y, (h k x y - h' k x y) ∂μ ∂μ) ^ 2
       ∂(Measure.pi fun _ : Fin N => μ)) ≤
      18 * ∑ k : Fin m, ∫ z : Euc d × Euc d,
        (h k z.1 z.2 - h' k z.1 z.2) ^ 2 ∂(μ.prod μ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have htwo : (2 : ℝ) / N ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast hN
  have hb : ∀ k : Fin m,
      (∫ X : EucConfig d N,
       ((N : ℝ) * (pairEnergy (h k) X μ - pairEnergy (h' k) X μ) +
          (1 / 2 : ℝ) * ∫ x, ∫ y, (h k x y - h' k x y) ∂μ ∂μ) ^ 2
       ∂(Measure.pi fun _ : Fin N => μ)) ≤
      18 * ∫ z : Euc d × Euc d,
        (h k z.1 z.2 - h' k z.1 z.2) ^ 2 ∂(μ.prod μ) := by
    intro k
    let H : Euc d → Euc d → ℝ := fun x y => h k x y - h' k x y
    have hmem : MemLp (fun z : Euc d × Euc d => H z.1 z.2) 2 (μ.prod μ) :=
      (hm k).sub (hm' k)
    have hsym : ∀ x y, H x y = H y x := by
      intro x y
      simp only [H, hs k x y, hs' k x y]
    have hvar := s21l_s13_variance_diff μ hN (h k) (h' k)
      (hm k) (hm' k) (hs k) (hs' k)
    have hcen := (s21l_s13_variance_sharp μ hN H hmem hsym).2
    have hnonneg : 0 ≤ ∫ z : Euc d × Euc d,
        (H z.1 z.2) ^ 2 ∂(μ.prod μ) :=
      integral_nonneg (fun z => sq_nonneg _)
    have htail : 2 * (∫ z : Euc d × Euc d, (H z.1 z.2) ^ 2 ∂(μ.prod μ)) / N ≤
        ∫ z : Euc d × Euc d, (H z.1 z.2) ^ 2 ∂(μ.prod μ) := by
      calc
        _ = (2 / (N : ℝ)) *
          (∫ z : Euc d × Euc d, (H z.1 z.2) ^ 2 ∂(μ.prod μ)) := by ring
        _ ≤ 1 * (∫ z : Euc d × Euc d, (H z.1 z.2) ^ 2 ∂(μ.prod μ)) :=
          mul_le_mul_of_nonneg_right htwo hnonneg
        _ = _ := one_mul _
    change
      (∫ X : EucConfig d N,
       ((N : ℝ) * (pairEnergy (h k) X μ - pairEnergy (h' k) X μ) +
          (1 / 2 : ℝ) * ∫ x, ∫ y, H x y ∂μ ∂μ) ^ 2
       ∂(Measure.pi fun _ : Fin N => μ)) ≤
      18 * ∫ z : Euc d × Euc d, (H z.1 z.2) ^ 2 ∂(μ.prod μ)
    linarith
  simpa only [Finset.mul_sum] using
    (Finset.sum_le_sum (s := Finset.univ) (fun k _ => hb k))

theorem pro_s13_generic_gaussian_family_difference_L2_bound
    (I : ProductGaussian μ) {m : ℕ}
    (r s : Fin m → ℕ)
    (c : (k : Fin m) → Fin (r k) → Fin (r k) → ℝ)
    (u : (k : Fin m) → Fin (r k) → Euc d → ℝ)
    (c' : (k : Fin m) → Fin (s k) → Fin (s k) → ℝ)
    (v : (k : Fin m) → Fin (s k) → Euc d → ℝ)
    (hu : ∀ k, IsR2FiniteRankData (c k) (u k))
    (hv : ∀ k, IsR2FiniteRankData (c' k) (v k)) :
    (∑ k : Fin m, ∫ ω : I.Ω,
      (((1 / 2 : ℝ) *
          ∑ i : Fin (r k), ∑ j : Fin (r k), c k i j *
            (I.η (u k i) ω * I.η (u k j) ω -
              ∫ ζ, I.η (u k i) ζ * I.η (u k j) ζ ∂I.P)) -
        (1 / 2 : ℝ) *
          ∑ i : Fin (s k), ∑ j : Fin (s k), c' k i j *
            (I.η (v k i) ω * I.η (v k j) ω -
              ∫ ζ, I.η (v k i) ζ * I.η (v k j) ζ ∂I.P)) ^ 2 ∂I.P) ≤
      18 * ∑ k : Fin m, ∫ z : Euc d × Euc d,
        (r2FiniteRankKernel (c k) (u k) z.1 z.2 -
          r2FiniteRankKernel (c' k) (v k) z.1 z.2) ^ 2 ∂(μ.prod μ) := by
  have hb : ∀ k : Fin m,
      (∫ ω : I.Ω,
        (((1 / 2 : ℝ) *
          ∑ i : Fin (r k), ∑ j : Fin (r k), c k i j *
            (I.η (u k i) ω * I.η (u k j) ω -
              ∫ ζ, I.η (u k i) ζ * I.η (u k j) ζ ∂I.P)) -
        (1 / 2 : ℝ) *
          ∑ i : Fin (s k), ∑ j : Fin (s k), c' k i j *
            (I.η (v k i) ω * I.η (v k j) ω -
              ∫ ζ, I.η (v k i) ζ * I.η (v k j) ζ ∂I.P)) ^ 2 ∂I.P) ≤
      18 * ∫ z : Euc d × Euc d,
        (r2FiniteRankKernel (c k) (u k) z.1 z.2 -
          r2FiniteRankKernel (c' k) (v k) z.1 z.2) ^ 2 ∂(μ.prod μ) :=
    fun k => s21t4_generic_product_finite_rank_quadratic_distinct_factors_bound
      I (c k) (u k) (c' k) (v k) (hu k) (hv k)
  simpa only [Finset.mul_sum] using
    (Finset.sum_le_sum (s := Finset.univ) (fun k _ => hb k))

end HRS.MS.R26T3
