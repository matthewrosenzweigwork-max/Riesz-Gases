import HRS.MS.S21T4ProdAP
import HRS.MS.R2ChaosAux2

/-! S13: the centered scalar singular-kernel product CLT via convergence together. -/
set_option autoImplicit false
set_option maxHeartbeats 12800000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem s21t4_round2_singular_centered_joint_clt {s M L B C : ℝ}
    {ρ : Euc d → ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s)
    (hs : s < (d : ℝ) / 2) (hρ : IsRound2Density d s M L ρ)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)]
    (I : ProductGaussian (HRS.Whole.withDensityReal ρ))
    {n : ℕ} (f : Fin n → Euc d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (HRS.Whole.withDensityReal ρ))
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {hj : ℕ → Euc d → Euc d → ℝ}
    (hA : IsRound2Approx s C B (HRS.Whole.withDensityReal ρ) h hj)
    (a : ℕ → Euc d → ℝ) (ha : IsR2ZeroMeanONB (HRS.Whole.withDensityReal ρ) a) :
    ∃ Q : I.Ω → ℝ,
      s94WickL2 I.P (HRS.Whole.withDensityReal ρ) a
        (fun i ω => I.η (a i) ω)
        (r2CenterKernel (HRS.Whole.withDensityReal ρ) h) Q ∧
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
  let μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ
  letI : IsProbabilityMeasure μ := HRS.Whole.U1.u1_isProb hρ.prob
  letI := I.mΩ
  letI := I.prob
  obtain ⟨m,c,u,Q,hdata,hW,hlim⟩ :=
    s21t4_round2_explicit_wick_approx hd hs0 hs hρ hh hA I a ha
  let Qj : ℕ → I.Ω → ℝ := fun j ω =>
    ∑ α : Fin (m j), ∑ β : Fin (m j), c j α β *
      (I.η (u j α) ω * I.η (u j β) ω -
        ∫ ζ, I.η (u j α) ζ * I.η (u j β) ζ ∂I.P)
  have hwj : ∀ j, s94WickL2 I.P μ a (fun i ω => I.η (a i) ω)
      (r2CenterKernel μ (hj j)) (Qj j) := by
    intro j
    rw [(hdata j).2]
    exact s21t4_finite_rank_explicit_wick I a ha (c j) (u j) (hdata j).1
  let F : (N : ℕ) → EucConfig d N → Fin n → ℝ := fun N X i =>
    Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (f i) -
      HRS.Whole.pair μ (f i))
  let Y : (N : ℕ) → EucConfig d N → (Fin n → ℝ) × ℝ := fun N X =>
    (F N X, (N : ℝ) * pairEnergy h X μ + (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ)
  let Yj : ℕ → (N : ℕ) → EucConfig d N → (Fin n → ℝ) × ℝ := fun j N X =>
    (F N X, (N : ℝ) * pairEnergy (hj j) X μ +
      (1 / 2) * ∫ x, ∫ y, hj j x y ∂μ ∂μ)
  let Z : I.Ω → (Fin n → ℝ) × ℝ :=
    fun ω => ((fun i => I.η (f i) ω), (1 / 2 : ℝ) * Q ω)
  let Zj : ℕ → I.Ω → (Fin n → ℝ) × ℝ :=
    fun j ω => ((fun i => I.η (f i) ω), (1 / 2 : ℝ) * Qj j ω)
  have h1 : ∀ j, TendstoInDistribution (Yj j) atTop (Zj j)
      (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
    intro j
    have hb := s21t4_finite_rank_centered_joint_clt I f hf
      (c j) (u j) (hdata j).1
    simpa only [Yj, Zj, Qj, F, (hdata j).2] using hb
  have hYj : ∀ j N, AEMeasurable (Yj j N) (Measure.pi fun _ : Fin N => μ) :=
    fun j N => (h1 j).forall_aemeasurable N
  have hZj : ∀ j, AEMeasurable (Zj j) I.P :=
    fun j => (h1 j).aemeasurable_limit
  have hY : ∀ N, AEMeasurable (Y N) (Measure.pi fun _ : Fin N => μ) := by
    intro N
    have hfN : AEMeasurable (F N) (Measure.pi fun _ : Fin N => μ) :=
      ((h1 0).forall_aemeasurable N).fst
    have hpm : Measurable (fun X : EucConfig d N => pairEnergy h X μ) :=
      HRS.MS.Wr.wr9_measurable_pairEnergy hh.measurable
    exact hfN.prodMk ((measurable_const.mul hpm).add measurable_const).aemeasurable
  have hZ : AEMeasurable Z I.P := by
    have hfZ : AEMeasurable (fun ω : I.Ω => fun i : Fin n => I.η (f i) ω) I.P :=
      ((h1 0).aemeasurable_limit).fst
    exact hfZ.prodMk (hW.1.const_mul (1 / 2 : ℝ)).aemeasurable
  let η : ℕ → ℝ := fun j =>
    18 * ∫ z : Euc d × Euc d, (hj j z.1 z.2 - h z.1 z.2) ^ 2 ∂(μ.prod μ)
  have hη0 : ∀ j, 0 ≤ η j := fun j =>
    mul_nonneg (by norm_num) (integral_nonneg (fun z => sq_nonneg _))
  have hη : Tendsto η atTop (𝓝 0) := by
    have h := s21t4_round2_approx_integral_sq_zero s C B (by linarith)
      h (s94_env_memLp hd hs0 hs hρ hh) hj hA
    simpa [η, μ] using h.const_mul 18
  have hZdiff : ∀ j ω, Zj j ω - Z ω =
      ((0 : Fin n → ℝ), (1 / 2 : ℝ) * (Qj j ω - Q ω)) := by
    intro j ω
    apply Prod.ext
    · funext i
      simp [Zj, Z]
    · simp [Zj, Z]
      ring
  have h2 : ∀ j, (∫⁻ ω, ‖Zj j ω - Z ω‖ₑ ^ 2 ∂I.P) ≤
      ENNReal.ofReal (η j) := by
    intro j
    simp_rw [hZdiff j]
    exact s21t4_round2_gaussian_pair_L2_bound hd hs0 hs hρ hh hA I a ha
      Q Qj hW hwj j
  have hYdiff : ∀ j N X, Yj j N X - Y N X =
      ((0 : Fin n → ℝ),
       (N : ℝ) * (pairEnergy (hj j) X μ - pairEnergy h X μ) +
          (1 / 2) * ∫ x, ∫ y, (hj j x y - h x y) ∂μ ∂μ) := by
    intro j N X
    apply Prod.ext
    · funext i
      simp [Yj,Y]
    · dsimp [Yj, Y]
      rw [s21t4_round2_mean_sub hd hs0 hs hρ hh hA j]
      ring
  have h3 : ∀ j, ∀ᶠ N in atTop,
      (∫⁻ X, ‖Yj j N X - Y N X‖ₑ ^ 2
        ∂(Measure.pi fun _ : Fin N => μ)) ≤ ENNReal.ofReal (η j) := by
    intro j
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp_rw [hYdiff j N]
    exact s21t4_round2_particle_pair_L2_bound hd hs0 hs hρ hh hA j N hN
  refine ⟨Q, hW, ?_⟩
  exact s94_tid_of_approx Y Z Yj Zj hY hZ hYj hZj h1 η hη0 hη h2 h3

end HRS.MS.R26T3
