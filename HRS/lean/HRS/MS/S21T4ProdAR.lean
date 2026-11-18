import HRS.MS.S21T4ProdAQ
import HRS.MS.R2ChaosAux42

/-! S13: unconditional (within its physical hypotheses) centered singular product joint CLT. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

/-- The centered singular-kernel product CLT, without an assumed approximation
sequence or an assumed complete Gaussian test basis. Both are produced by
the already verified S9.1 and S9.4 theorems. -/
theorem s21t4_physical_singular_centered_joint_clt
    (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L : ℝ) (ρ : Euc d → ℝ) (hρ : IsRound2Density d s M L ρ)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)]
    (I : ProductGaussian (HRS.Whole.withDensityReal ρ))
    {n : ℕ} (f : Fin n → Euc d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (HRS.Whole.withDensityReal ρ))
    (B : ℝ) (h : Euc d → Euc d → ℝ) (hh : IsBoundedPairKernel s B h) :
    ∃ Q : I.Ω → ℝ, MemLp Q 2 I.P ∧
      TendstoInDistribution
        (fun N (X : EucConfig d N) =>
          ((fun i => Real.sqrt N *
            (HRS.Whole.pair (HRS.Whole.empirical X) (f i) -
              HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (f i))),
           (N : ℝ) * pairEnergy h X (HRS.Whole.withDensityReal ρ) +
             (1 / 2) * ∫ x, ∫ y, h x y
               ∂(HRS.Whole.withDensityReal ρ)
               ∂(HRS.Whole.withDensityReal ρ))) atTop
        (fun ω : I.Ω => ((fun i => I.η (f i) ω), (1 / 2 : ℝ) * Q ω))
        (fun N => Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) I.P := by
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
    HRS.Whole.U1.u1_isProb hρ.prob
  letI := I.mΩ
  letI := I.prob
  obtain ⟨C, happrox⟩ := HRS.Whole.U1.round2_approximation_proof hd s hs0 hs
  obtain ⟨hj, hA⟩ := happrox M L ρ hρ B h hh
  obtain ⟨a, ha⟩ := s94_exists_onb hd hρ
  obtain ⟨Q, hW, hdist⟩ := s21t4_round2_singular_centered_joint_clt
    hd hs0 hs hρ I f hf hh hA a ha
  exact ⟨Q, hW.1, hdist⟩

end HRS.MS.R26T3
