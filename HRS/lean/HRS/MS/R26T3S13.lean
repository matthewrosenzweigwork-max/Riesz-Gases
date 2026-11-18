import HRS.MS.PROS13WickIdentificationAut5
import HRS.MS.PROS13FamilyJointAut5

/-!
# R26-T3.S13: exact arbitrary-probability product-singular contract

The limit is the actual common-space Gaussian quadratic L² limit, rather
than an arbitrary second-chaos law. The final topological map separates
the centered Euclidean family and restores the deterministic pair-energy
shift. No nonatomicity hypothesis is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem r26t3_product_singular
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (I : ProductGaussian μ) (n m : ℕ)
    (f : Fin n → Euc d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ i, MemLp
      (fun z : Euc d × Euc d => h i z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ i x y, h i x y = h i y x) :
    ∃ Q : Fin m → I.Ω → ℝ,
      (∀ i, MemLp (Q i) 2 I.P) ∧
      (∀ (a : ℕ → Euc d → ℝ), IsR2ZeroMeanONB μ a → ∀ (i : Fin m),
        HRS.Whole.IsR2WickChaos I.P μ a (fun j => I.η (a j))
          (r2CenterKernel μ (h i)) (fun (ζ : I.Ω) => (2 : ℝ) * (Q i ζ))) ∧
      TendstoInDistribution
        (fun N (X : EucConfig d N) =>
          ((fun i : Fin n => Real.sqrt N *
              (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i))),
           (fun j : Fin m => (N : ℝ) * pairEnergy (h j) X μ))) atTop
        (fun ω =>
          ((fun i : Fin n => I.η (f i) ω),
           (fun j : Fin m => Q j ω -
             (1 / 2 : ℝ) * ∫ x, ∫ y, h j x y ∂μ ∂μ)))
        (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  classical
  obtain ⟨Q, hQ, hActual, hdist⟩ :=
    pro_s13_generic_finite_family_centered_joint_with_actual
      I f hf h hh hs
  let b : Fin m → ℝ :=
    fun j => (1 / 2 : ℝ) * ∫ x, ∫ y, h j x y ∂μ ∂μ
  let splitShift : EuclideanSpace ℝ (Fin (n + m)) →
      (Fin n → ℝ) × (Fin m → ℝ) :=
    fun v => ((fun i => v (Fin.castAdd m i)),
      (fun j => v (Fin.natAdd n j) - b j))
  have hcontinuous : Continuous splitShift := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi (fun i => PiLp.continuous_apply 2 (fun _ : Fin (n + m) => ℝ) (Fin.castAdd m i))
    · exact continuous_pi (fun j =>
        (PiLp.continuous_apply 2 (fun _ : Fin (n + m) => ℝ) (Fin.natAdd n j)).sub continuous_const)
  refine ⟨Q, (fun i => (hQ i).1), ?_, ?_⟩
  · intro a ha i
    exact pro_s13_actual_product_quadratic_all_ONB_wick
      I (h i) (hh i) (hs i) (Q i) (hActual i) a ha
  · have hcomp := hdist.continuous_comp hcontinuous
    convert hcomp using 1
    · funext N X
      apply Prod.ext
      · funext i
        simp [splitShift, r2EmpDistr]
      · funext j
        simp [splitShift, b]
    · funext ω
      apply Prod.ext
      · funext i
        simp [splitShift]
      · funext j
        simp [splitShift, b]

#print axioms r26t3_product_singular
end HRS.MS.R26T3
