import HRS.MS.PROS13FamilyLinearAut5
import HRS.MS.PROS13CommonFactorGaussian
import HRS.MS.PROS13FiniteFamilyCentered
import HRS.MS.PROS13GenericFamilyAE
import HRS.MS.PROS13VectorSubtract
import HRS.MS.PROS13FamilyMoment
import HRS.MS.PROS13GenericTransferD

/-!
# S13: joint CLT for finitely many arbitrary symmetric product-L² kernels

We use shared smooth finite-rank approximation of all pair kernels, the
finite-rank common-space Gaussian CLT, and an L² convergence-together
argument. No nonatomicity or everywhere row-integrability is imposed.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_finite_family_centered_joint_with_actual
    (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, MemLp
      (fun z : Euc d × Euc d => h k z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ k x y, h k x y = h k y x) :
    ∃ Q : Fin m → I.Ω → ℝ,
      (∀ k, MemLp (Q k) 2 I.P ∧
        InSecondChaos I.P I.ξ 3 (Q k)) ∧
      (∀ k, HasActualProductQuadraticLimit I (h k) (Q k)) ∧
      TendstoInDistribution
        (fun N (X : EucConfig d N) =>
          (WithLp.toLp 2 (Fin.append
            (fun i : Fin n => r2EmpDistr μ X (f i))
            (fun k : Fin m => (N : ℝ) * pairEnergy (h k) X μ +
              (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ)) :
              EuclideanSpace ℝ (Fin (n + m)))) atTop
        (fun ω : I.Ω =>
          (WithLp.toLp 2 (Fin.append
            (fun i : Fin n => I.η (f i) ω)
            (fun k : Fin m => Q k ω)) :
              EuclideanSpace ℝ (Fin (n + m))))
        (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  classical
  letI := I.mΩ
  letI := I.prob
  obtain ⟨r, u, c, Q, htest, hd, hQ, hK, hlim, hsum⟩ :=
    pro_s13_generic_common_factor_gaussian_family I h hh hs
  let hj : ℕ → Fin m → Euc d → Euc d → ℝ :=
    fun j k => r2FiniteRankKernel (c j k) (u j)
  let Qj : ℕ → Fin m → I.Ω → ℝ :=
    fun j k ω => (1 / 2 : ℝ) *
      ∑ a : Fin (r j), ∑ b : Fin (r j), c j k a b *
        (I.η (u j a) ω * I.η (u j b) ω -
          ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)
  let Y : (N : ℕ) → EucConfig d N →
    EuclideanSpace ℝ (Fin (n + m)) :=
    fun N X => WithLp.toLp 2 (Fin.append
      (fun i : Fin n => r2EmpDistr μ X (f i))
      (fun k : Fin m => (N : ℝ) * pairEnergy (h k) X μ +
        (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ))
  let Yj : ℕ → (N : ℕ) → EucConfig d N →
    EuclideanSpace ℝ (Fin (n + m)) :=
    fun j N X => WithLp.toLp 2 (Fin.append
      (fun i : Fin n => r2EmpDistr μ X (f i))
      (fun k : Fin m => (N : ℝ) * pairEnergy (hj j k) X μ +
        (1 / 2 : ℝ) * ∫ x, ∫ y, hj j k x y ∂μ ∂μ))
  let Z : I.Ω → EuclideanSpace ℝ (Fin (n + m)) :=
    fun ω => WithLp.toLp 2 (Fin.append
      (fun i : Fin n => I.η (f i) ω) (fun k : Fin m => Q k ω))
  let Zj : ℕ → I.Ω → EuclideanSpace ℝ (Fin (n + m)) :=
    fun j ω => WithLp.toLp 2 (Fin.append
      (fun i : Fin n => I.η (f i) ω)
      (fun k : Fin m => Qj j k ω))
  have hmemj : ∀ j k, MemLp
      (fun z : Euc d × Euc d => hj j k z.1 z.2) 2 (μ.prod μ) :=
    fun j k => s21t4_finite_rank_memLp (c j k) (u j) (hd j k)
  have hsymj : ∀ j k x y, hj j k x y = hj j k y x :=
    fun j k x y => s21t4_finite_rank_symmetric
      (c j k) (u j) (hd j k) x y
  have hQjm : ∀ j k, MemLp (Qj j k) 2 I.P := by
    intro j k
    have hu : ∀ a, MemLp (u j a) 2 μ :=
      fun a => ((hd j k).smooth a).continuous.memLp_of_hasCompactSupport
        ((hd j k).compactSupport a)
    exact s21t4_generic_product_finite_rank_quadratic_L2
      I (u j) hu (c j k)
  have h1 : ∀ j, TendstoInDistribution (Yj j) atTop (Zj j)
      (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
    intro j
    simpa only [Yj, Zj, hj, Qj] using
      (pro_s13_finite_family_centered_joint
        I f hf (c j) (u j) (htest j)
        (fun k a b => (hd j k).symm a b))
  have hY : ∀ N, AEMeasurable (Y N)
      (Measure.pi fun _ : Fin N => μ) := by
    intro N
    simpa only [Y] using
      (pro_s13_generic_family_centered_source_ae I f hf h hh N)
  have hYj : ∀ j N, AEMeasurable (Yj j N)
      (Measure.pi fun _ : Fin N => μ) :=
    fun j N => (h1 j).forall_aemeasurable N
  have hZj : ∀ j, AEMeasurable (Zj j) I.P :=
    fun j => (h1 j).aemeasurable_limit
  have hZ : AEMeasurable Z I.P := by
    have hfull : AEMeasurable
        (fun ω : I.Ω => Fin.append
          (fun i : Fin n => I.η (f i) ω)
          (fun k : Fin m => Q k ω)) I.P := by
      refine aemeasurable_pi_iff.mpr fun i => ?_
      refine Fin.addCases (fun j => ?_) (fun k => ?_) i
      · simpa only [Fin.append_left] using
          (I.meas (f j) (hf j)).aemeasurable
      · simpa only [Fin.append_right] using
          (hQ k).1.aestronglyMeasurable.aemeasurable
    exact (PiLp.continuous_toLp 2
      (fun _ : Fin (n + m) => ℝ)).aemeasurable.comp_aemeasurable hfull
  let a : ℕ → ℝ := fun j => ∑ k : Fin m,
    ∫ z : Euc d × Euc d, (hj j k z.1 z.2 - h k z.1 z.2) ^ 2 ∂(μ.prod μ)
  let b : ℕ → ℝ := fun j => ∑ k : Fin m,
    ∫ ω : I.Ω, (Qj j k ω - Q k ω) ^ 2 ∂I.P
  let η : ℕ → ℝ := fun j => 18 * a j + b j
  have ha0 : ∀ j, 0 ≤ a j := fun j => Finset.sum_nonneg
    (fun k _ => integral_nonneg (fun z => sq_nonneg _))
  have hb0 : ∀ j, 0 ≤ b j := fun j => Finset.sum_nonneg
    (fun k _ => integral_nonneg (fun ω => sq_nonneg _))
  have hη0 : ∀ j, 0 ≤ η j := by
    intro j
    exact add_nonneg (mul_nonneg (by norm_num) (ha0 j)) (hb0 j)
  have haT : Tendsto a atTop (𝓝 0) := by
    have hsingle : ∀ k, Tendsto
        (fun j => ∫ z : Euc d × Euc d,
          (hj j k z.1 z.2 - h k z.1 z.2) ^ 2 ∂(μ.prod μ))
        atTop (𝓝 0) := by
      intro k
      have hTk : Tendsto
          (fun j => eLpNorm
            (fun z : Euc d × Euc d =>
              hj j k z.1 z.2 - h k z.1 z.2) 2 (μ.prod μ))
          atTop (𝓝 0) := by
        simpa only [hj] using hK k
      have hmk : ∀ j, MemLp
          (fun z : Euc d × Euc d =>
            hj j k z.1 z.2 - h k z.1 z.2) 2 (μ.prod μ) :=
        fun j => (hmemj j k).sub (hh k)
      exact s21t4_integral_sq_tendsto_zero
        (ν := μ.prod μ)
        (fun j (z : Euc d × Euc d) =>
          hj j k z.1 z.2 - h k z.1 z.2) hmk hTk
    simpa only [a, Finset.sum_const_zero] using
      (tendsto_finset_sum (Finset.univ : Finset (Fin m))
        (fun k _ => hsingle k))
  have hbT : Tendsto b atTop (𝓝 0) := by
    simpa only [b, Qj, Finset.sum_const_zero] using hsum
  have hηT : Tendsto η atTop (𝓝 0) := by
    have ht := (haT.const_mul 18).add hbT
    simpa only [η, mul_zero, zero_add] using ht
  have hZdiff : ∀ j ω, Zj j ω - Z ω =
      (WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ))
        (fun k : Fin m => Qj j k ω - Q k ω)) :
        EuclideanSpace ℝ (Fin (n + m))) := by
    intro j ω
    exact pro_s13_euclidean_append_sub
      (fun i : Fin n => I.η (f i) ω)
      (fun k => Qj j k ω) (fun k => Q k ω)
  have h2 : ∀ j, (∫⁻ ω, ‖Zj j ω - Z ω‖ₑ ^ 2 ∂I.P) ≤
      ENNReal.ofReal (η j) := by
    intro j
    simp_rw [hZdiff j]
    rw [pro_s13_euclidean_append_zero_lintegral I.P
      (fun k ω => Qj j k ω - Q k ω)
      (fun k => (hQjm j k).sub (hQ k).1)]
    exact ENNReal.ofReal_le_ofReal (by
      dsimp only [η]
      nlinarith [ha0 j])
  have hYdiff : ∀ j N (X : EucConfig d N),
      Yj j N X - Y N X =
        (WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ))
          (fun k : Fin m => (N : ℝ) *
            (pairEnergy (hj j k) X μ - pairEnergy (h k) X μ) +
            (1 / 2 : ℝ) * ∫ x, ∫ y,
              (hj j k x y - h k x y) ∂μ ∂μ)) :
          EuclideanSpace ℝ (Fin (n + m))) := by
    intro j N X
    have hmean : ∀ k,
        (∫ x, ∫ y, (hj j k x y - h k x y) ∂μ ∂μ) =
          (∫ x, ∫ y, hj j k x y ∂μ ∂μ) -
          (∫ x, ∫ y, h k x y ∂μ ∂μ) := by
      intro k
      exact pro_s13_generic_double_mean_sub
        (hj j k) (h k) (hmemj j k) (hh k)
    change (WithLp.toLp 2 (Fin.append
      (fun i : Fin n => r2EmpDistr μ X (f i))
      (fun k : Fin m => (N : ℝ) * pairEnergy (hj j k) X μ +
        (1 / 2 : ℝ) * ∫ x, ∫ y, hj j k x y ∂μ ∂μ)) :
        EuclideanSpace ℝ (Fin (n + m))) -
      (WithLp.toLp 2 (Fin.append
      (fun i : Fin n => r2EmpDistr μ X (f i))
      (fun k : Fin m => (N : ℝ) * pairEnergy (h k) X μ +
        (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ)) :
        EuclideanSpace ℝ (Fin (n + m))) = _
    rw [pro_s13_euclidean_append_sub]
    congr 1
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
      rw [hmean k]
      ring
  have h3 : ∀ j, ∀ᶠ N in atTop,
      (∫⁻ X, ‖Yj j N X - Y N X‖ₑ ^ 2
        ∂(Measure.pi fun _ : Fin N => μ)) ≤ ENNReal.ofReal (η j) := by
    intro j
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp_rw [hYdiff j N]
    let ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ
    have hcomponent : ∀ k, MemLp
        (fun X : EucConfig d N => (N : ℝ) *
          (pairEnergy (hj j k) X μ - pairEnergy (h k) X μ) +
          (1 / 2 : ℝ) * ∫ x, ∫ y,
            (hj j k x y - h k x y) ∂μ ∂μ) 2 ν := by
      intro k
      exact (((pro_s13_generic_pairEnergy_memLp
        (hj j k) (hmemj j k)).sub
        (pro_s13_generic_pairEnergy_memLp (h k) (hh k))).const_mul
          (N : ℝ)).add (memLp_const _)
    rw [pro_s13_euclidean_append_zero_lintegral ν
      (fun k X => (N : ℝ) *
        (pairEnergy (hj j k) X μ - pairEnergy (h k) X μ) +
          (1 / 2 : ℝ) * ∫ x, ∫ y,
            (hj j k x y - h k x y) ∂μ ∂μ) hcomponent]
    have hp := pro_s13_generic_particle_family_difference_L2_bound
      hN (hj j) h (hmemj j) hh (hsymj j) hs
    have hle : 18 * a j ≤ η j := by
      dsimp only [η]
      linarith [hb0 j]
    exact (ENNReal.ofReal_le_ofReal
      (by simpa only [a, hj] using hp)).trans
      (ENNReal.ofReal_le_ofReal hle)
  have hActual : ∀ k, HasActualProductQuadraticLimit I (h k) (Q k) := by
    intro k
    exact ⟨(hQ k).1, r, (fun j => c j k), u,
      (fun j => hd j k), hK k, hlim k⟩
  refine ⟨Q, hQ, hActual, ?_⟩
  change TendstoInDistribution Y atTop Z
    (fun N => Measure.pi fun _ : Fin N => μ) I.P
  exact s94_tid_of_approx Y Z Yj Zj hY hZ hYj hZj
    h1 η hη0 hηT h2 h3

theorem pro_s13_generic_finite_family_centered_joint
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
            (fun k : Fin m => (N : ℝ) * pairEnergy (h k) X μ +
              (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ)) :
              EuclideanSpace ℝ (Fin (n + m)))) atTop
        (fun ω : I.Ω =>
          (WithLp.toLp 2 (Fin.append
            (fun i : Fin n => I.η (f i) ω)
            (fun k : Fin m => Q k ω)) :
              EuclideanSpace ℝ (Fin (n + m))))
        (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  obtain ⟨Q, hQ, _, hdist⟩ :=
    pro_s13_generic_finite_family_centered_joint_with_actual I f hf h hh hs
  exact ⟨Q, hQ, hdist⟩

#print axioms pro_s13_generic_finite_family_centered_joint_with_actual
#print axioms pro_s13_generic_finite_family_centered_joint
end HRS.MS.R26T3
