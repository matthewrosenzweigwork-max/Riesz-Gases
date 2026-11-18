import HRS.MS.PROS13FamilyJointAut5

/-!
# S13: arbitrary finite-family uncentered pair-energy normalization

This translates the jointly convergent centered Gaussian quadratic vector
by precisely one-half the corresponding double integrals. The source
coordinates are the original unmodified particle pair energies.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_finite_family_joint_unshifted
    (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, MemLp
      (fun z : Euc d × Euc d => h k z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ k x y, h k x y = h k y x) :
    ∃ Q : Fin m → I.Ω → ℝ,
      (∀ k, MemLp (Q k) 2 I.P ∧
        InSecondChaos I.P I.ξ 3 (Q k)) ∧
      TendstoInDistribution
        (fun N (X : EucConfig d N) =>
          (WithLp.toLp 2 (Fin.append
            (fun i : Fin n => r2EmpDistr μ X (f i))
            (fun k : Fin m => (N : ℝ) * pairEnergy (h k) X μ)) :
              EuclideanSpace ℝ (Fin (n + m)))) atTop
        (fun ω : I.Ω =>
          (WithLp.toLp 2 (Fin.append
            (fun i : Fin n => I.η (f i) ω)
            (fun k : Fin m => Q k ω -
              (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ)) :
              EuclideanSpace ℝ (Fin (n + m))))
        (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  classical
  obtain ⟨Q, hQ, hclt⟩ :=
    pro_s13_generic_finite_family_centered_joint I f hf h hh hs
  let b : Fin m → ℝ := fun k =>
    (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ
  let B : EuclideanSpace ℝ (Fin (n + m)) :=
    WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ)) b)
  let T : EuclideanSpace ℝ (Fin (n + m)) →
      EuclideanSpace ℝ (Fin (n + m)) := fun z => z - B
  have hT : Continuous T := continuous_id.sub continuous_const
  have h := hclt.continuous_comp hT
  refine ⟨Q, hQ, ?_⟩
  convert h using 1
  · funext N X
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [T, B, b]
    · simp [T, B, b]
  · funext ω
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [T, B, b]
    · simp [T, B, b]

#print axioms pro_s13_generic_finite_family_joint_unshifted
end HRS.MS.R26T3
