import HRS.MS.S21T4ProdBO
import HRS.MS.S21T4ProdBB
import HRS.MS.S21T4ProdF

/-!
# R26-T3.S13: simultaneous singular-kernel joint central limit theorem

The full finite family of physical pair energies converges on the one
canonical ProductGaussian probability space together with any finite family
of L² empirical fluctuations. Each quadratic coordinate is exactly the
half-Wick limit minus half the double mean of its uncentered kernel.

Cramér-Wold is applied to genuine particle statistics: a scalar projection
is the pair energy of the corresponding weighted sum kernel, and its Gaussian
limit is identified using the L²-linearity of common-space Wick chaos.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ}

theorem s21t4_physical_singular_joint_family_one_space
    (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L : ℝ) (ρ : Euc d → ℝ) (hρ : IsRound2Density d s M L ρ)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)]
    (I : ProductGaussian (HRS.Whole.withDensityReal ρ))
    {n m : ℕ}
    (f : Fin n → Euc d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (HRS.Whole.withDensityReal ρ))
    (B : Fin m → ℝ) (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, IsBoundedPairKernel s (B k) (h k)) :
    ∃ Q : Fin m → I.Ω → ℝ,
      (∀ k, MemLp (Q k) 2 I.P) ∧
      TendstoInDistribution
        (fun N (X : EucConfig d N) =>
          (WithLp.toLp 2 (Fin.append
            (fun i : Fin n => r2EmpDistr
              (HRS.Whole.withDensityReal ρ) X (f i))
            (fun k : Fin m => (N : ℝ) * pairEnergy (h k) X
              (HRS.Whole.withDensityReal ρ))) :
            EuclideanSpace ℝ (Fin (n + m)))) atTop
        (fun ω : I.Ω =>
          (WithLp.toLp 2 (Fin.append
            (fun i : Fin n => I.η (f i) ω)
            (fun k : Fin m => Q k ω -
              (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y
                ∂(HRS.Whole.withDensityReal ρ)
                ∂(HRS.Whole.withDensityReal ρ))) :
            EuclideanSpace ℝ (Fin (n + m))))
        (fun N => Measure.pi fun _ : Fin N =>
          HRS.Whole.withDensityReal ρ) I.P := by
  let μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ
  letI : IsProbabilityMeasure μ := HRS.Whole.U1.u1_isProb hρ.prob
  letI := I.mΩ
  letI := I.prob
  have hk : ∀ k : Fin m, S94KOK μ (h k) :=
    fun k => s21t4_singular_kernel_KOK hd hs0 hs hρ (hh k)
  obtain ⟨Q, hQL2, hQwick⟩ :=
    s21t4_product_wick_finite_L2 I m h
      (fun k => (hk k).memLp) (fun k => (hk k).symm)
  let b : Fin m → ℝ :=
    fun k => (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ
  let X : (N : ℕ) → EucConfig d N →
      EuclideanSpace ℝ (Fin (n + m)) :=
    fun N v => WithLp.toLp 2 (Fin.append
      (fun i : Fin n => r2EmpDistr μ v (f i))
      (fun k : Fin m => (N : ℝ) * pairEnergy (h k) v μ))
  let Z : I.Ω → EuclideanSpace ℝ (Fin (n + m)) :=
    fun ω => WithLp.toLp 2 (Fin.append
      (fun i : Fin n => I.η (f i) ω)
      (fun k : Fin m => Q k ω - b k))
  refine ⟨Q, hQL2, ?_⟩
  change TendstoInDistribution X atTop Z
      (fun N => Measure.pi fun _ : Fin N => μ) I.P
  have hQb : ∀ k, MemLp (fun ω => Q k ω - b k) 2 I.P :=
    fun k => (hQL2 k).sub (memLp_const _)
  refine s21t4_varying_cramer_wold
    (fun N => s21t4_singular_family_source_ae I f hf h hk N)
    (s21t4_singular_family_limit_ae I f hf
      (fun k ω => Q k ω - b k) hQb) ?_
  intro t
  let α : Fin m → ℝ := fun k => t (Fin.natAdd n k)
  let hstar : Euc d → Euc d → ℝ :=
    fun x y => ∑ k : Fin m, α k * h k x y
  let bstar : ℝ := (1 / 2 : ℝ) * ∫ x, ∫ y, hstar x y ∂μ ∂μ
  have hmean : bstar = ∑ k : Fin m, α k * b k := by
    dsimp [bstar, b, hstar]
    rw [s21t4_kernel_family_double_integral h hk α,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hkm
    ring
  have hpair : ∀ N (v : EucConfig d N),
      (∑ k : Fin m, α k * ((N : ℝ) * pairEnergy (h k) v μ)) =
      (N : ℝ) * pairEnergy hstar v μ := by
    intro N v
    have he := s21t4_pairEnergy_family_linear h hk α v
    rw [he]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hkm
    ring
  let G : ((Fin n → ℝ) × ℝ) → ℝ :=
    fun v => (∑ i : Fin n, t (Fin.castAdd m i) * v.1 i) + v.2 - bstar
  have hG : Continuous G := by
    exact ((continuous_finset_sum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp continuous_fst)).add
      continuous_snd).sub continuous_const
  have hb := s21t4_singular_family_scalar_clt
    hd s hs0 hs M L ρ hρ I f hf B h hh Q hQwick α
  have hproj := hb.continuous_comp hG
  have hsource : ∀ N (v : EucConfig d N),
      inner ℝ (X N v) t =
      G ((fun i : Fin n => r2EmpDistr μ v (f i)),
          (N : ℝ) * pairEnergy hstar v μ + bstar) := by
    intro N v
    calc
      _ = (∑ i : Fin n, t (Fin.castAdd m i) * r2EmpDistr μ v (f i)) +
        ∑ k : Fin m, α k * ((N : ℝ) * pairEnergy (h k) v μ) :=
          s21t4_finappend_inner _ _ t
      _ = G ((fun i : Fin n => r2EmpDistr μ v (f i)),
          (N : ℝ) * pairEnergy hstar v μ + bstar) := by
            rw [hpair N v]
            dsimp [G]
            ring
  have hlimit : ∀ ω : I.Ω,
      inner ℝ (Z ω) t =
        G ((fun i : Fin n => I.η (f i) ω),
          ∑ k : Fin m, α k * Q k ω) := by
    intro ω
    have hsum : (∑ k : Fin m, α k * (Q k ω - b k)) =
        (∑ k : Fin m, α k * Q k ω) - bstar := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← hmean]
    calc
      _ = (∑ i : Fin n, t (Fin.castAdd m i) * I.η (f i) ω) +
          ∑ k : Fin m, α k * (Q k ω - b k) :=
            s21t4_finappend_inner _ _ t
      _ = G ((fun i : Fin n => I.η (f i) ω),
          ∑ k : Fin m, α k * Q k ω) := by
            rw [hsum]
            dsimp [G]
            ring
  convert hproj using 1
  · funext N v
    exact hsource N v
  · funext ω
    exact hlimit ω

end HRS.MS.R26T3
