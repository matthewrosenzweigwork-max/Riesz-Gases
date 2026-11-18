import HRS.MS.S21T4ProdAK

/-! S13: true particle L² error for a finite-rank S9.1 approximant. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem s21t4_round2_particle_sq_bound
    {s M L B C : ℝ} {ρ : Euc d → ℝ}
    (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {hj : ℕ → Euc d → Euc d → ℝ}
    (hA : IsRound2Approx s C B (HRS.Whole.withDensityReal ρ) h hj)
    (j N : ℕ) (hN : 2 ≤ N) :
    (∫ X : EucConfig d N,
      ((N : ℝ) *
        (pairEnergy (hj j) X (HRS.Whole.withDensityReal ρ) -
          pairEnergy h X (HRS.Whole.withDensityReal ρ)) +
        (1 / 2) * ∫ x, ∫ y, (hj j x y - h x y)
          ∂(HRS.Whole.withDensityReal ρ)
          ∂(HRS.Whole.withDensityReal ρ)) ^ 2
          ∂(Measure.pi fun _ : Fin N => (HRS.Whole.withDensityReal ρ))) ≤
       18 * ∫ z : Euc d × Euc d,
         (hj j z.1 z.2 - h z.1 z.2) ^ 2
           ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  let μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ
  letI : IsProbabilityMeasure μ := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨m, c, u, hdata, heq⟩ := hA.finiteRank j
  have hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ) :=
    s94_env_memLp hd hs0 hs hρ hh
  have hjm : MemLp (fun z : Euc d × Euc d => hj j z.1 z.2) 2 (μ.prod μ) := by
    rw [heq]
    exact s21t4_finite_rank_memLp c u hdata
  have hjs : ∀ x y, hj j x y = hj j y x := by
    intro x y
    rw [heq]
    exact s21t4_finite_rank_symmetric c u hdata x y
  have hΔm := hjm.sub hm
  have hΔs : ∀ x y, (hj j x y - h x y) = hj j y x - h y x := by
    intros; rw [hjs, hh.symm]
  have hkey := s21l_s13_variance μ hN
    (fun x y => hj j x y - h x y) hΔm hΔs
  have he : ∫ X : EucConfig d N,
    ((N : ℝ) * (pairEnergy (hj j) X μ - pairEnergy h X μ) +
      (1 / 2) * ∫ x, ∫ y, (hj j x y - h x y) ∂μ ∂μ) ^ 2
      ∂(Measure.pi fun _ : Fin N => μ) =
    ∫ X : EucConfig d N,
    ((N : ℝ) * pairEnergy (fun x y => hj j x y - h x y) X μ +
      (1 / 2) * ∫ x, ∫ y, (hj j x y - h x y) ∂μ ∂μ) ^ 2
      ∂(Measure.pi fun _ : Fin N => μ) := by
    apply integral_congr_ae
    filter_upwards [s21t4_pairEnergy_sub_ae μ (hj j) h hjm hm] with X hX
    rw [hX]
  rw [he]
  exact hkey

end HRS.MS.R26T3
