import HRS.MS.S21T4ProdAM

/-! S13: exact pair-valued second-moment bound for the particle approximation. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem s21t4_round2_particle_pair_L2_bound {s M L B C : ℝ}
    {ρ : Euc d → ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {hj : ℕ → Euc d → Euc d → ℝ}
    (hA : IsRound2Approx s C B (HRS.Whole.withDensityReal ρ) h hj)
    {n : ℕ} (j N : ℕ) (hN : 2 ≤ N) :
    (∫⁻ X : EucConfig d N,
      ‖(((0 : Fin n → ℝ),
        (N : ℝ) * (pairEnergy (hj j) X (HRS.Whole.withDensityReal ρ) -
          pairEnergy h X (HRS.Whole.withDensityReal ρ)) +
          (1 / 2) * ∫ x, ∫ y, (hj j x y - h x y)
            ∂(HRS.Whole.withDensityReal ρ)
            ∂(HRS.Whole.withDensityReal ρ)))‖ₑ ^ 2
          ∂(Measure.pi fun _ : Fin N => (HRS.Whole.withDensityReal ρ))) ≤
      ENNReal.ofReal (18 * ∫ z : Euc d × Euc d,
        (hj j z.1 z.2 - h z.1 z.2) ^ 2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))) := by
  let μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ
  letI : IsProbabilityMeasure μ := HRS.Whole.U1.u1_isProb hρ.prob
  let ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ
  let Δ : Euc d → Euc d → ℝ := fun x y => hj j x y - h x y
  let v : EucConfig d N → ℝ := fun X =>
    (N : ℝ) * (pairEnergy (hj j) X μ - pairEnergy h X μ) +
      (1 / 2) * ∫ x, ∫ y, Δ x y ∂μ ∂μ
  have hH : S94KOK μ h := s21t4_singular_kernel_KOK hd hs0 hs hρ hh
  obtain ⟨m,c,u,hdata,heq⟩ := hA.finiteRank j
  have hHj : S94KOK μ (hj j) := by
    rw [heq]
    exact s21t4_finite_rank_KOK c u hdata
  have hm : MemLp (fun z : Euc d × Euc d => Δ z.1 z.2) 2 (μ.prod μ) :=
    hHj.memLp.sub hH.memLp
  have hsΔ : ∀ x y, Δ x y = Δ y x := by
    intros x y
    simp only [Δ, hHj.symm x y, hh.symm x y]
  have hv0 : MemLp (fun X : EucConfig d N =>
      (N : ℝ) * pairEnergy Δ X μ +
        (1 / 2) * ∫ x, ∫ y, Δ x y ∂μ ∂μ) 2 ν :=
    s21t4_s13_particle_memLp μ hN Δ hm hsΔ
  have he : (fun X : EucConfig d N =>
      (N : ℝ) * pairEnergy Δ X μ +
        (1 / 2) * ∫ x, ∫ y, Δ x y ∂μ ∂μ) =ᵐ[ν] v := by
    filter_upwards [s21t4_pairEnergy_sub_ae μ (hj j) h hHj.memLp hH.memLp] with X hX
    simp only [Δ, v, hX]
  have hv : MemLp v 2 ν := (memLp_congr_ae he).1 hv0
  have hsq := s21t4_round2_particle_sq_bound hd hs0 hs hρ hh hA j N hN
  change (∫ X, (v X) ^ 2 ∂ν) ≤ 18 * ∫ z,
    Δ z.1 z.2 ^ 2 ∂(μ.prod μ) at hsq
  change (∫⁻ X, ‖(((0 : Fin n → ℝ), v X))‖ₑ ^ 2 ∂ν) ≤ _
  rw [s21t4_pair_second_lintegral v hv]
  exact ENNReal.ofReal_le_ofReal hsq

end HRS.MS.R26T3
