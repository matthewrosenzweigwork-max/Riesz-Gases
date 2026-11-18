import HRS.MS.PROS13GenericTransferF

/-!
# Unconditional generic singular kernel joint limit in the frozen normalization

The deterministic half-double-integral offset is retained exactly.
Only one pair kernel is treated; extension to the arbitrary finite family
and the all-ONB Wick representation remain unproved.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_scalar_joint_unshifted
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
           (N : ℝ) * pairEnergy h X μ)) atTop
        (fun ω : I.Ω =>
          ((fun i : Fin n => I.η (f i) ω),
           Q ω - (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ))
        (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  obtain ⟨Q, hQ, hQsecond, hweak⟩ :=
    pro_s13_generic_scalar_joint_second_chaos I f hf h hh hs
  let b : ℝ := (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ
  let T : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) :=
    fun z => (z.1, z.2 - b)
  have hT : Continuous T :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have hweak' := hweak.continuous_comp hT
  have hY : (fun N (X : EucConfig d N) =>
          ((fun i : Fin n => Real.sqrt N *
            (HRS.Whole.pair (HRS.Whole.empirical X) (f i) -
              HRS.Whole.pair μ (f i))),
           (N : ℝ) * pairEnergy h X μ)) =
      (fun N (X : EucConfig d N) => T
        ((fun i : Fin n => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) (f i) -
            HRS.Whole.pair μ (f i))),
          (N : ℝ) * pairEnergy h X μ +
            (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ)) := by
    funext N X
    apply Prod.ext
    · rfl
    · dsimp [T, b]
      ring
  change TendstoInDistribution
    (fun N (X : EucConfig d N) => T
      ((fun i : Fin n => Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical X) (f i) -
          HRS.Whole.pair μ (f i))),
        (N : ℝ) * pairEnergy h X μ +
          (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ)) atTop
    (fun ω : I.Ω => T ((fun i : Fin n => I.η (f i) ω), Q ω))
    (fun N => Measure.pi fun _ : Fin N => μ) I.P at hweak'
  refine ⟨Q, hQ, hQsecond, ?_⟩
  convert hweak' using 1

end HRS.MS.R26T3
