import HRS.MS.S21T4ProdBX
import HRS.MS.S21L_S13V

/-!
# S13: integrability of the actual centered particle statistic

The uniform second-moment estimate in S21L_S13V is not used as a
substitute for integrability. This proves integrability directly from
the Hoeffding decomposition and product-measure L² bounds, including
when the reference measure has atoms.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_generic_particle_centered_memLp {N : ℕ} (hN : 2 ≤ N)
    (h : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) :
    MemLp (fun X : EucConfig d N =>
      (N : ℝ) * pairEnergy h X μ +
        (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ) 2
      (Measure.pi fun _ : Fin N => μ) := by
  let ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ
  let m : Euc d → ℝ := fun x => ∫ y, h x y ∂μ
  let c : ℝ := ∫ x, ∫ y, h x y ∂μ ∂μ
  let V : EucConfig d N → ℝ := fun X =>
    (1 / 2 : ℝ) * ((N : ℝ)⁻¹ *
      ∑ i, ∑ j ∈ Finset.univ.erase i, r2CenterKernel μ h (X i) (X j))
  let R : EucConfig d N → ℝ := fun X =>
    -((1 / (N : ℝ)) * ∑ i, (m (X i) - c))
  have hcL : MemLp (fun z : Euc d × Euc d =>
      r2CenterKernel μ h z.1 z.2) 2 (μ.prod μ) :=
    s21h2_c_memLp μ hm
  have hmL : MemLp m 2 μ := s21h2_m_memLp μ hm
  have hterm : ∀ i j : Fin N, j ∈ Finset.univ.erase i →
      MemLp (fun X : EucConfig d N =>
        r2CenterKernel μ h (X i) (X j)) 2 ν := by
    intro i j hj
    exact s21g2_s11_memLp μ (r2CenterKernel μ h) hcL
      (Finset.ne_of_mem_erase hj).symm
  have hVL : MemLp V 2 ν := by
    have hsum := (memLp_finsetSum (Finset.univ : Finset (Fin N))
      (f := fun i X => ∑ j ∈ Finset.univ.erase i,
        r2CenterKernel μ h (X i) (X j)) (p := 2) (μ := ν)
      fun i _ => memLp_finsetSum _ fun j hj => hterm i j hj)
    exact (hsum.const_mul (N : ℝ)⁻¹).const_mul (1 / 2)
  have hrow : ∀ i : Fin N,
      MemLp (fun X : EucConfig d N => m (X i) - c) 2 ν := by
    intro i
    have hh := (hmL.sub (memLp_const c)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin N => μ) i)
    simpa [Function.comp_def] using hh
  have hRL : MemLp R 2 ν := by
    have hsum := (memLp_finsetSum (Finset.univ : Finset (Fin N))
      (f := fun i X => m (X i) - c) (p := 2) (μ := ν)
      fun i _ => hrow i)
    exact (hsum.const_mul (1 / (N : ℝ))).neg
  have hex : ∀ X : EucConfig d N,
      (N : ℝ) * pairEnergy h X μ +
        (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ = V X + R X := by
    intro X
    rw [s21l_s13_alg μ hN h hs X]
    simp only [V, R, m, c]
    ring
  convert hVL.add hRL using 1
  funext X
  exact hex X

end HRS.MS.R26T3
