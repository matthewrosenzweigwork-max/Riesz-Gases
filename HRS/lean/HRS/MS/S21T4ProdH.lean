import HRS.MS.S21T4ProdF
import HRS.MS.S21L_S13V

/-! Uniform L² genuine integrability of the singular product particle statistic. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]

/-- The centered N-scaled product pair energy is genuinely an L² variable, not a
Bochner-integral junk value. This is the integrability input for Chebyshev and
the uniform kernel-approximation step in R26-T3.S13. -/
theorem s21t4_s13_particle_memLp {N : ℕ} (hN : 2 ≤ N)
    (h : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) :
    MemLp (fun X : EucConfig d N =>
      (N : ℝ) * pairEnergy h X μ +
        (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ) 2 (Measure.pi fun _ : Fin N => μ) := by
  let ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ
  let m : Euc d → ℝ := fun x => ∫ y, h x y ∂μ
  let c : ℝ := ∫ x, ∫ y, h x y ∂μ ∂μ
  have hcL : MemLp (fun z : Euc d × Euc d => r2CenterKernel μ h z.1 z.2) 2
      (μ.prod μ) := s21h2_c_memLp μ hm
  have hmL : MemLp m 2 μ := s21h2_m_memLp μ hm
  have hterm : ∀ (i j : Fin N), j ∈ Finset.univ.erase i →
      MemLp (fun X : EucConfig d N => r2CenterKernel μ h (X i) (X j)) 2 ν := by
    intro i j hj
    exact s21g2_s11_memLp μ (r2CenterKernel μ h) hcL
      (Finset.ne_of_mem_erase hj).symm
  have hV : MemLp (fun X : EucConfig d N =>
      (1 / 2) * ((N : ℝ)⁻¹ *
        ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, r2CenterKernel μ h (X i) (X j))) 2 ν := by
    have hsum : MemLp (fun X : EucConfig d N =>
        ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
          r2CenterKernel μ h (X i) (X j)) 2 ν :=
      memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j hj => hterm i j hj
    exact (hsum.const_mul (N : ℝ)⁻¹).const_mul (1 / 2)
  have hrow : ∀ i : Fin N, MemLp
      (fun X : EucConfig d N => m (X i) - c) 2 ν := by
    intro i
    have hi := (hmL.sub (memLp_const c)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin N => μ) i)
    simpa [Function.comp_def] using hi
  have hR : MemLp (fun X : EucConfig d N =>
      -((1 / (N : ℝ)) * ∑ i : Fin N, (m (X i) - c))) 2 ν := by
    have hsum : MemLp (fun X : EucConfig d N =>
        ∑ i : Fin N, (m (X i) - c)) 2 ν :=
      memLp_finsetSum _ fun i _ => hrow i
    exact (hsum.const_mul (1 / (N : ℝ))).neg
  have hVR := hV.add hR
  have hident : ∀ X : EucConfig d N,
      ((N : ℝ) * pairEnergy h X μ + (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ) =
      (1 / 2) * ((N : ℝ)⁻¹ *
        ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, r2CenterKernel μ h (X i) (X j)) -
        (1 / (N : ℝ)) * ∑ i : Fin N, (m (X i) - c) := by
    intro X
    exact s21l_s13_alg μ hN h hs X
  have heq : (fun X : EucConfig d N =>
      (N : ℝ) * pairEnergy h X μ + (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ) =ᵐ[ν]
      (fun X : EucConfig d N =>
        (1 / 2) * ((N : ℝ)⁻¹ *
          ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, r2CenterKernel μ h (X i) (X j)) -
          (1 / (N : ℝ)) * ∑ i : Fin N, (m (X i) - c)) :=
    Filter.Eventually.of_forall hident
  exact (memLp_congr_ae heq).2 hVR

end HRS.MS.R26T3
