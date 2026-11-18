import HRS.MS.PROS13GenericTransferC
import HRS.MS.S21T4ProdAI
import HRS.MS.R2ChaosAux2

/-!
# Scalar generic product-kernel joint CLT by L² approximation

All pair-kernel assumptions are those of the original S13 contract, apart
from the explicitly stated measurability of the limiting particle statistic.
The latter is a separate obligation for the fully general S13 theorem and
must be removed before claiming unconditional closure.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_scalar_joint_of_aemeasurable
    (I : ProductGaussian μ) {n : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x)
    (r : ℕ → ℕ)
    (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
    (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
    (hd : ∀ j, IsR2FiniteRankData (c j) (u j))
    (hK : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0))
    (Q : I.Ω → ℝ) (hQ : MemLp Q 2 I.P)
    (hlim : Tendsto (fun j : ℕ => ∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         Q ω) ^ 2 ∂I.P) atTop (𝓝 0))
    (hY : ∀ N, AEMeasurable
      (fun X : EucConfig d N =>
        ((fun i : Fin n => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i))),
         (N : ℝ) * pairEnergy h X μ +
           (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ))
      (Measure.pi fun _ : Fin N => μ)) :
    TendstoInDistribution
      (fun N (X : EucConfig d N) =>
        ((fun i : Fin n => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i))),
         (N : ℝ) * pairEnergy h X μ +
           (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ)) atTop
      (fun ω : I.Ω => ((fun i : Fin n => I.η (f i) ω), Q ω))
      (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  letI := I.mΩ
  letI := I.prob
  let hj : ℕ → Euc d → Euc d → ℝ := fun j =>
    r2FiniteRankKernel (c j) (u j)
  let Qj : ℕ → I.Ω → ℝ := fun j ω =>
    (1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
      (I.η (u j a) ω * I.η (u j b) ω -
        ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)
  let F : (N : ℕ) → EucConfig d N → Fin n → ℝ := fun N X i =>
    Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i))
  let Y : (N : ℕ) → EucConfig d N → (Fin n → ℝ) × ℝ := fun N X =>
    (F N X, (N : ℝ) * pairEnergy h X μ +
      (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ)
  let Yj : ℕ → (N : ℕ) → EucConfig d N → (Fin n → ℝ) × ℝ := fun j N X =>
    (F N X, (N : ℝ) * pairEnergy (hj j) X μ +
      (1 / 2 : ℝ) * ∫ x, ∫ y, hj j x y ∂μ ∂μ)
  let Z : I.Ω → (Fin n → ℝ) × ℝ := fun ω =>
    ((fun i : Fin n => I.η (f i) ω), Q ω)
  let Zj : ℕ → I.Ω → (Fin n → ℝ) × ℝ := fun j ω =>
    ((fun i : Fin n => I.η (f i) ω), Qj j ω)
  have hmem : ∀ j, MemLp (fun z : Euc d × Euc d => hj j z.1 z.2)
      2 (μ.prod μ) := fun j => s21t4_finite_rank_memLp (c j) (u j) (hd j)
  have hsym : ∀ j x y, hj j x y = hj j y x := fun j x y =>
    s21t4_finite_rank_symmetric (c j) (u j) (hd j) x y
  have hQj : ∀ j, MemLp (Qj j) 2 I.P := by
    intro j
    have hu : ∀ i, MemLp (u j i) 2 μ :=
      fun i => ((hd j).smooth i).continuous.memLp_of_hasCompactSupport
        ((hd j).compactSupport i)
    exact s21t4_generic_product_finite_rank_quadratic_L2 I (u j) hu (c j)
  have h1 : ∀ j, TendstoInDistribution (Yj j) atTop (Zj j)
      (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
    intro j
    simpa only [Yj, Zj, F, hj, Qj] using
      (s21t4_finite_rank_centered_joint_clt I f hf (c j) (u j) (hd j))
  have hYj : ∀ j N, AEMeasurable (Yj j N) (Measure.pi fun _ : Fin N => μ) :=
    fun j N => (h1 j).forall_aemeasurable N
  have hZj : ∀ j, AEMeasurable (Zj j) I.P :=
    fun j => (h1 j).aemeasurable_limit
  have hZ : AEMeasurable Z I.P := by
    have hfZ : AEMeasurable
        (fun ω : I.Ω => fun i : Fin n => I.η (f i) ω) I.P :=
      ((h1 0).aemeasurable_limit).fst
    exact hfZ.prodMk hQ.aestronglyMeasurable.aemeasurable
  let η : ℕ → ℝ := fun j => 72 * ∫ z : Euc d × Euc d,
      (hj j z.1 z.2 - h z.1 z.2) ^ 2 ∂(μ.prod μ)
  have hη0 : ∀ j, 0 ≤ η j := fun j =>
    mul_nonneg (by norm_num) (integral_nonneg fun z => sq_nonneg _)
  have hη : Tendsto η atTop (𝓝 0) := by
    have hc := s21t4_integral_sq_tendsto_zero
      (fun j (z : Euc d × Euc d) => hj j z.1 z.2 - h z.1 z.2)
      (fun j => (hmem j).sub hh) (by simpa only [hj] using hK)
    simpa only [η, mul_zero] using hc.const_mul 72
  have hZdiff : ∀ j ω, Zj j ω - Z ω =
      ((0 : Fin n → ℝ), Qj j ω - Q ω) := by
    intro j ω
    apply Prod.ext
    · funext i
      simp [Zj, Z]
    · simp [Zj, Z]
  have h2 : ∀ j,
      (∫⁻ ω, ‖Zj j ω - Z ω‖ₑ ^ 2 ∂I.P) ≤ ENNReal.ofReal (η j) := by
    intro j
    simp_rw [hZdiff j]
    have hq2 := pro_s13_generic_gaussian_quadratic_error_bound
      I h hh r c u hd Q hQ hK hlim j
    have hp : MemLp (fun ω => Qj j ω - Q ω) 2 I.P := (hQj j).sub hQ
    rw [s21t4_pair_second_lintegral (n := n) (fun ω => Qj j ω - Q ω) hp]
    exact ENNReal.ofReal_le_ofReal (by simpa only [η, hj, Qj] using hq2)
  have hYdiff : ∀ j N X, Yj j N X - Y N X =
      ((0 : Fin n → ℝ),
       (N : ℝ) * (pairEnergy (hj j) X μ - pairEnergy h X μ) +
        (1 / 2 : ℝ) * ∫ x, ∫ y, (hj j x y - h x y) ∂μ ∂μ) := by
    intro j N X
    have hmean := pro_s13_generic_double_mean_sub (hj j) h (hmem j) hh
    apply Prod.ext
    · funext i
      simp [Yj, Y]
    · dsimp only [Yj, Y, Prod.snd_sub]
      rw [hmean]
      ring
  have h3 : ∀ j, ∀ᶠ N in atTop,
      (∫⁻ X, ‖Yj j N X - Y N X‖ₑ ^ 2
        ∂(Measure.pi fun _ : Fin N => μ)) ≤ ENNReal.ofReal (η j) := by
    intro j
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp_rw [hYdiff j N]
    have hp := pro_s13_generic_particle_pair_L2_bound (n := n)
      hN (hj j) h (hmem j) hh (hsym j) hs
    have hl : 18 * (∫ z : Euc d × Euc d,
        (hj j z.1 z.2 - h z.1 z.2) ^ 2 ∂(μ.prod μ)) ≤ η j := by
      have hz : 0 ≤ (∫ z : Euc d × Euc d,
          (hj j z.1 z.2 - h z.1 z.2) ^ 2 ∂(μ.prod μ)) :=
        integral_nonneg fun z => sq_nonneg _
      dsimp only [η]
      linarith
    exact hp.trans (ENNReal.ofReal_le_ofReal hl)
  exact s94_tid_of_approx Y Z Yj Zj (by simpa only [Y] using hY)
    hZ hYj hZj h1 η hη0 hη h2 h3

end HRS.MS.R26T3
