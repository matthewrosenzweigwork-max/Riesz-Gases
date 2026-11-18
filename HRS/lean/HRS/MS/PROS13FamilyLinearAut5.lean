import HRS.MS.PROS13CrossLimitScale

/-!
# Generic S13: exact simultaneous Gaussian quadratic linear combinations

The Gaussian quadratic limits are the actual second-chaos random variables
constructed from finite-rank pair kernels on one fixed ProductGaussian space.
Their finite linear combinations are again actual quadratic limits. The
statement has no nonatomicity hypothesis and includes the empty family.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_actual_product_quadratic_zero
    (I : ProductGaussian μ) :
    HasActualProductQuadraticLimit I
      (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) := by
  have hh : MemLp
      (fun _ : Euc d × Euc d => (0 : ℝ)) 2 (μ.prod μ) := by
    exact memLp_const 0
  obtain ⟨Q, hQ⟩ := pro_s13_actual_product_quadratic_exists
    I (fun _ _ => 0) hh (by intro x y; rfl)
  simpa using
    (pro_s13_actual_product_quadratic_scale I
      (fun _ _ => 0) Q hQ (0 : ℝ))

theorem pro_s13_actual_product_quadratic_finsum
    (I : ProductGaussian μ) {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, MemLp (fun z : Euc d × Euc d => h k z.1 z.2)
      2 (μ.prod μ))
    (Q : Fin m → I.Ω → ℝ)
    (hQ : ∀ k, HasActualProductQuadraticLimit I (h k) (Q k))
    (α : Fin m → ℝ) :
    HasActualProductQuadraticLimit I
      (fun x y => ∑ k : Fin m, α k * h k x y)
      (fun ω => ∑ k : Fin m, α k * Q k ω) := by
  classical
  have hfin : ∀ s : Finset (Fin m),
      MemLp (fun z : Euc d × Euc d =>
        ∑ k ∈ s, α k * h k z.1 z.2) 2 (μ.prod μ) ∧
      HasActualProductQuadraticLimit I
        (fun x y => ∑ k ∈ s, α k * h k x y)
        (fun ω => ∑ k ∈ s, α k * Q k ω) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        constructor
        · simpa using
            (memLp_const (0 : ℝ) :
              MemLp (fun _ : Euc d × Euc d => (0 : ℝ))
                2 (μ.prod μ))
        · simpa using pro_s13_actual_product_quadratic_zero I
    | @insert k s hks ih =>
        have hm : MemLp
            (fun z : Euc d × Euc d => α k * h k z.1 z.2)
            2 (μ.prod μ) := (hh k).const_mul (α k)
        have hquad := pro_s13_actual_product_quadratic_add
          I (fun x y => α k * h k x y)
            (fun x y => ∑ i ∈ s, α i * h i x y)
            hm ih.1
            (fun ω => α k * Q k ω)
            (fun ω => ∑ i ∈ s, α i * Q i ω)
            (pro_s13_actual_product_quadratic_scale
              I (h k) (Q k) (hQ k) (α k))
            ih.2
        have hmadd : MemLp
            (fun z : Euc d × Euc d =>
              α k * h k z.1 z.2 + ∑ i ∈ s, α i * h i z.1 z.2)
            2 (μ.prod μ) := by
          convert (hm.add ih.1) using 1
        simpa only [Finset.sum_insert hks] using
          (And.intro hmadd hquad)
  simpa using (hfin Finset.univ).2

#print axioms pro_s13_actual_product_quadratic_zero
#print axioms pro_s13_actual_product_quadratic_finsum
end HRS.MS.R26T3
