import HRS.MS.PROS13GenericTransferE
import HRS.MS.PROS13QuadraticChaos

/-!
# Unconditional scalar singular product-kernel joint CLT

For every Borel probability law and every symmetric product-L² kernel,
without a nonatomicity condition, the original centered particle pair energy
converges jointly with arbitrary finitely many empirical linear observables
to the *actual* second Gaussian Wiener chaos on the same ProductGaussian
probability space. The finite-family kernel vector and all-ONB Wick identity
of the full S13 contract are further obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_scalar_joint_second_chaos
    (I : ProductGaussian μ) {n : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) :
    ∃ Q : I.Ω → ℝ,
      MemLp Q 2 I.P ∧ InSecondChaos I.P I.ξ 3 Q ∧
      TendstoInDistribution
        (fun N (X : EucConfig d N) =>
          ((fun i : Fin n => Real.sqrt N *
            (HRS.Whole.pair (HRS.Whole.empirical X) (f i) -
              HRS.Whole.pair μ (f i))),
           (N : ℝ) * pairEnergy h X μ +
             (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ)) atTop
        (fun ω : I.Ω => ((fun i : Fin n => I.η (f i) ω), Q ω))
        (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  classical
  letI := I.mΩ
  letI := I.prob
  obtain ⟨r, c, u, Q, hd, hK, hQ, hlim⟩ :=
    pro_s13_generic_actual_quadratic_L2_witness I h hh hs
  have hQsecond := pro_s13_quadratic_limit_in_second_chaos
    I r c u hd Q hQ hlim
  have hbase := s21t4_finite_rank_centered_joint_clt I f hf
    (c 0) (u 0) (hd 0)
  have hY : ∀ N, AEMeasurable
      (fun X : EucConfig d N =>
        ((fun i : Fin n => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) (f i) -
            HRS.Whole.pair μ (f i))),
         (N : ℝ) * pairEnergy h X μ +
           (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ))
      (Measure.pi fun _ : Fin N => μ) := by
    intro N
    let ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ
    have hfY : AEMeasurable
        (fun X : EucConfig d N => fun i : Fin n => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) (f i) -
            HRS.Whole.pair μ (f i))) ν :=
      (hbase.forall_aemeasurable N).fst
    have hp : MemLp (fun X : EucConfig d N =>
        (N : ℝ) * pairEnergy h X μ +
          (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ) 2 ν :=
      ((pro_s13_generic_pairEnergy_memLp h hh).const_mul (N : ℝ)).add
        (memLp_const ((1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ))
    exact hfY.prodMk hp.aestronglyMeasurable.aemeasurable
  exact ⟨Q, hQ, hQsecond,
    pro_s13_generic_scalar_joint_of_aemeasurable
      I f hf h hh hs r c u hd hK Q hQ hlim hY⟩

end HRS.MS.R26T3
