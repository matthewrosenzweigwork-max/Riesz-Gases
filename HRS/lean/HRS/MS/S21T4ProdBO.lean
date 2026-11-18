import HRS.MS.S21T4ProdBN
import HRS.MS.S21T4ProdAQ
import HRS.MS.S21T4ProdAV

/-!
# R26-T3.S13: scalar projections of simultaneous singular-kernel statistics

For a finite family of physical singular kernels, any scalar linear
combination of their exactly centered pair energies converges jointly
with the linear empirical fluctuations. The Gaussian limit is the prescribed
linear combination of Wick-chaos witnesses on the original ProductGaussian
space, not a newly selected Gaussian probability space.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ}

theorem s21t4_singular_family_scalar_clt
    (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L : ℝ) (ρ : Euc d → ℝ) (hρ : IsRound2Density d s M L ρ)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)]
    (I : ProductGaussian (HRS.Whole.withDensityReal ρ))
    {n m : ℕ}
    (f : Fin n → Euc d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (HRS.Whole.withDensityReal ρ))
    (B : Fin m → ℝ) (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, IsBoundedPairKernel s (B k) (h k))
    (Q : Fin m → I.Ω → ℝ)
    (hQ : ∀ a, IsR2ZeroMeanONB (HRS.Whole.withDensityReal ρ) a →
      ∀ k, IsR2WickChaos I.P (HRS.Whole.withDensityReal ρ)
        a (fun j => I.η (a j)) (r2CenterKernel
          (HRS.Whole.withDensityReal ρ) (h k)) (fun ω => 2 * Q k ω))
    (α : Fin m → ℝ) :
    TendstoInDistribution
      (fun N (X : EucConfig d N) =>
        ((fun i : Fin n => r2EmpDistr
          (HRS.Whole.withDensityReal ρ) X (f i)),
         (N : ℝ) * pairEnergy (fun x y => ∑ k, α k * h k x y) X
           (HRS.Whole.withDensityReal ρ) +
         (1 / 2 : ℝ) * ∫ x, ∫ y, (∑ k, α k * h k x y)
           ∂(HRS.Whole.withDensityReal ρ)
           ∂(HRS.Whole.withDensityReal ρ))) atTop
      (fun ω : I.Ω =>
        ((fun i : Fin n => I.η (f i) ω),
          ∑ k : Fin m, α k * Q k ω))
      (fun N => Measure.pi fun _ : Fin N =>
        HRS.Whole.withDensityReal ρ) I.P := by
  let μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ
  letI : IsProbabilityMeasure μ := HRS.Whole.U1.u1_isProb hρ.prob
  letI := I.mΩ
  letI := I.prob
  let hstar : Euc d → Euc d → ℝ :=
    fun x y => ∑ k : Fin m, α k * h k x y
  let Bstar : ℝ := ∑ k : Fin m, |α k| * |B k|
  have hhstar : IsBoundedPairKernel s Bstar hstar :=
    s21t4_weighted_kernel_bound s B α h hh
  obtain ⟨C, happ⟩ := HRS.Whole.U1.round2_approximation_proof hd s hs0 hs
  obtain ⟨hj, hA⟩ := happ M L ρ hρ Bstar hstar hhstar
  obtain ⟨a, ha⟩ := s94_exists_onb hd hρ
  obtain ⟨R, hR, hdist⟩ :=
    s21t4_round2_singular_centered_joint_clt
      hd hs0 hs hρ I f hf hhstar hA a ha
  have hz : S94GSeq I.P (fun i ω => I.η (a i) ω) 1 :=
    s21l_gseq (s21t4_product_eta_bundle I) ha.1 ha.2.1
  have hRW : IsR2WickChaos I.P μ a (fun i => I.η (a i))
      (r2CenterKernel μ hstar) R := hR.isWick hz
  have hk : ∀ k : Fin m, S94KOK μ (h k) :=
    fun k => s21t4_singular_kernel_KOK hd hs0 hs hρ (hh k)
  have hRsum := s21t4_product_centered_wick_family_linear
    I a ha h hk α (fun k ω => 2 * Q k ω) (hQ a ha) R hRW
  have hlim : (fun ω : I.Ω =>
      ((fun i : Fin n => I.η (f i) ω), (1 / 2 : ℝ) * R ω)) =ᵐ[I.P]
      (fun ω : I.Ω =>
        ((fun i : Fin n => I.η (f i) ω),
          ∑ k : Fin m, α k * Q k ω)) := by
    filter_upwards [hRsum] with ω hω
    apply Prod.ext
    · rfl
    · simp only [Prod.snd]
      rw [hω, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
  refine TendstoInDistribution.congr
    (fun N => ae_of_all _ fun X => ?_) hlim hdist
  rfl

end HRS.MS.R26T3
