import HRS.MS.SA12Z2NearN3B

/-!
# S.A.12 N3, part C (SA12Z2): the first Riesz derivative as a kernel integral, and the
symmetrized pairing at fixed smoothing

* `∂_i (g * v) = g * ∂_i v` for `v ∈ C¹_c` (Mathlib convolution derivative);
* for `ε > 0`, the smoothed pairing `∫ u(x) ∫ g_ε(x-y) ∂_i v(y)` equals the one with the derivative
  moved to the kernel (`D_ε = ∂_e g_ε`), by one integration by parts in `y`;
* the symmetrized quadratic form `∫∫ u(x) u(y) D_ε(x-y) (a(y)-a(x))` is bounded by
  `(σ/2) cb (∫ k_ρ) ∫ u²`, uniformly in `ε > 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- `∂_i (g * v) = g * ∂_i v` for `v ∈ C¹_c` and the Riesz kernel `g` (locally integrable for `s < d`). -/
theorem sa12z2_firstRiesz_eq {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (x : Euc d) :
    firstRiesz d s i v x =
      ∫ y, rieszKernel d s (x - y) * fderiv ℝ v y (EuclideanSpace.single i (1 : ℝ)) := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  have hconv := hvc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hv x
  have hfun : (fun x' => ∫ y, rieszKernel d s (x' - y) * v y) =
      rieszKernel d s ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] v := by
    funext x'
    have h := integral_sub_left_eq_self (μ := volume) (fun t => rieszKernel d s t * v (x' - t)) x'
    simp only [sub_sub_cancel] at h
    simpa [convolution_def] using h
  have hint : Integrable (fun t => (ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d)
      (rieszKernel d s t) (fderiv ℝ v (x - t))) := by
    have := (hvc.fderiv ℝ).convolutionExists_right ((ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d))
      hK (hv.continuous_fderiv (by norm_num)) x
    exact this
  unfold firstRiesz
  rw [hfun, hconv.fderiv, convolution_def]
  show (∫ t, (ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d) (rieszKernel d s t)
      (fderiv ℝ v (x - t)) ∂volume) (EuclideanSpace.single i (1 : ℝ)) = _
  rw [ContinuousLinearMap.integral_apply hint]
  have key : ∀ t, (ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d) (rieszKernel d s t)
      (fderiv ℝ v (x - t)) (EuclideanSpace.single i (1 : ℝ)) =
        rieszKernel d s t * fderiv ℝ v (x - t) (EuclideanSpace.single i (1 : ℝ)) :=
    fun t => rfl
  simp only [key]
  have h := integral_sub_left_eq_self (μ := volume)
    (fun t => rieszKernel d s t * fderiv ℝ v (x - t) (EuclideanSpace.single i (1 : ℝ))) x
  simp only [sub_sub_cancel] at h
  exact h.symm

/-- The product of `u(x)` and the difference of `a` vanishes off `{p.1 - p.2 = 0}`, which is null. -/
theorem sa12z2_diag_ae (hd : 1 ≤ d) :
    ∀ᵐ p ∂(volume.prod volume : Measure (Euc d × Euc d)), p.1 - p.2 ≠ 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hS : MeasurableSet {p : Euc d × Euc d | p.1 - p.2 = 0} :=
    (measurableSet_singleton (0 : Euc d)).preimage (measurable_fst.sub measurable_snd)
  have h0 : (volume.prod volume) {p : Euc d × Euc d | p.1 - p.2 = 0} = 0 := by
    rw [Measure.prod_apply hS]
    have hx : ∀ x : Euc d, volume {a : Euc d | x - a = 0} = 0 := by
      intro x
      have hset : {a : Euc d | x - a = 0} = {x} := by
        ext y
        simp [sub_eq_zero, eq_comm]
      rw [hset, measure_singleton]
    simp [hx]
  refine ae_iff.2 ?_
  convert h0 using 2
  ext p
  simp

/-- A `C¹` function vanishing outside a closed ball has zero derivative outside it. -/
theorem sa12z2_deriv_zero_outside {v : Euc d → ℝ} {c : Euc d} {ρ : ℝ}
    (hsupp : Function.support v ⊆ Metric.closedBall c ρ) (e : Euc d) {y : Euc d}
    (hy : y ∉ Metric.closedBall c ρ) : fderiv ℝ v y e = 0 := by
  by_contra h
  have hne : fderiv ℝ v y ≠ 0 := fun h0 => h (by simp [h0])
  have hmem : y ∈ tsupport v := support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 hne)
  have hts : tsupport v ⊆ Metric.closedBall c ρ :=
    closure_minimal hsupp Metric.isClosed_closedBall
  exact hy (hts hmem)

/-- A continuous function on the product vanishing off `B × B` is integrable. -/
theorem sa12z2_integrable_prod_of_zero {F : Euc d × Euc d → ℝ} {c : Euc d} {ρ : ℝ}
    (hF : Continuous F)
    (h0 : ∀ p : Euc d × Euc d, p.1 ∉ Metric.closedBall c ρ ∨ p.2 ∉ Metric.closedBall c ρ → F p = 0) :
    Integrable F (volume.prod volume) := by
  refine hF.integrable_of_hasCompactSupport (HasCompactSupport.intro
    ((isCompact_closedBall c ρ).prod (isCompact_closedBall c ρ)) (fun p hp => h0 p ?_))
  rw [← not_and_or]
  exact fun h => hp (Set.mem_prod.2 h)

/-- The derivative in the direction `e` of the smoothed kernel is continuous for `ε > 0`. -/
theorem sa12z2_dEps_cont (s : ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    Continuous (fun z : Euc d => movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) z) := by
  have hgC : ContDiff ℝ ∞ (movtr_gEps d s ε) := n3_gEps_contDiff s hε
  have : (fun z : Euc d => movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) z) =
      fun z => fderiv ℝ (movtr_gEps d s ε) z (EuclideanSpace.single i (1 : ℝ)) :=
    funext fun z => (n3_gEps_fderiv s hε _ z).symm
  rw [this]
  exact (hgC.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- One integration by parts in `y` for the smoothed kernel: the derivative moves to the kernel. -/
theorem sa12z2_gEps_ibp (s : ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (x : Euc d) :
    ∫ y, movtr_gEps d s ε (x - y) * fderiv ℝ v y (EuclideanSpace.single i (1 : ℝ)) =
      ∫ y, movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (x - y) * v y := by
  have hgC : ContDiff ℝ ∞ (movtr_gEps d s ε) := n3_gEps_contDiff s hε
  have hk : ∀ t ∈ tsupport v, ContDiffAt ℝ 1 (fun y => movtr_gEps d s ε (x - y)) t := fun t _ =>
    ((hgC.comp (contDiff_const.sub contDiff_id)).contDiffAt).of_le (by exact_mod_cast le_top)
  have hdk : ∀ t, fderiv ℝ (fun y => movtr_gEps d s ε (x - y)) t
      (EuclideanSpace.single i (1 : ℝ)) = -movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (x - t) := by
    intro t
    have hg : HasFDerivAt (movtr_gEps d s ε) (fderiv ℝ (movtr_gEps d s ε) (x - t)) (x - t) :=
      ((hgC.differentiable (by simp)) (x - t)).hasFDerivAt
    have h2 := hg.comp t ((hasFDerivAt_const x t).sub (hasFDerivAt_id t))
    show fderiv ℝ (movtr_gEps d s ε ∘ fun y => x - y) t (EuclideanSpace.single i (1 : ℝ)) = _
    rw [h2.fderiv]
    simp [n3_gEps_fderiv s hε]
  have hibp := HRS.MS.UniqN0.n0_ibp hv hvc hk (EuclideanSpace.single i (1 : ℝ))
  simp only [hdk] at hibp
  rw [hibp]
  simp only [neg_mul, integral_neg, neg_neg]

/-- For `ε > 0`, the smoothed pairing equals the pairing with the derivative moved to the kernel. -/
theorem sa12z2_prod_eq {u v : Euc d → ℝ} {c : Euc d} {ρ : ℝ} (hu : Continuous u)
    (hsu : Function.support u ⊆ Metric.closedBall c ρ) (s : ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin d)
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (hsv : Function.support v ⊆ Metric.closedBall c ρ) :
    ∫ p : Euc d × Euc d, u p.1 * movtr_gEps d s ε (p.1 - p.2) *
        fderiv ℝ v p.2 (EuclideanSpace.single i (1 : ℝ)) ∂(volume.prod volume) =
      ∫ p : Euc d × Euc d, u p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) *
        v p.2 ∂(volume.prod volume) := by
  have hu0 : ∀ y, y ∉ Metric.closedBall c ρ → u y = 0 := fun y hy =>
    by_contra fun h => hy (hsu (Function.mem_support.2 h))
  have hv0 : ∀ y, y ∉ Metric.closedBall c ρ → v y = 0 := fun y hy =>
    by_contra fun h => hy (hsv (Function.mem_support.2 h))
  have hgC : ContDiff ℝ ∞ (movtr_gEps d s ε) := n3_gEps_contDiff s hε
  have hgc : Continuous (movtr_gEps d s ε) := hgC.continuous
  have hwc : Continuous (fun y => fderiv ℝ v y (EuclideanSpace.single i (1 : ℝ))) :=
    (hv.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hvc' : Continuous v := hv.continuous
  have hDc := sa12z2_dEps_cont (d := d) s hε i
  have hΦ : Integrable (fun p : Euc d × Euc d => u p.1 * movtr_gEps d s ε (p.1 - p.2) *
      fderiv ℝ v p.2 (EuclideanSpace.single i (1 : ℝ))) (volume.prod volume) := by
    refine sa12z2_integrable_prod_of_zero (c := c) (ρ := ρ) ?_ ?_
    · exact ((hu.comp continuous_fst).mul (hgc.comp (continuous_fst.sub continuous_snd))).mul
        (hwc.comp continuous_snd)
    · intro p hp
      rcases hp with h | h
      · simp [hu0 _ h]
      · simp [sa12z2_deriv_zero_outside hsv (EuclideanSpace.single i (1 : ℝ)) h]
  have hΨ : Integrable (fun p : Euc d × Euc d => u p.1 *
      movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * v p.2) (volume.prod volume) := by
    refine sa12z2_integrable_prod_of_zero (c := c) (ρ := ρ) ?_ ?_
    · exact ((hu.comp continuous_fst).mul (hDc.comp (continuous_fst.sub continuous_snd))).mul
        (hvc'.comp continuous_snd)
    · intro p hp
      rcases hp with h | h
      · simp [hu0 _ h]
      · simp [hv0 _ h]
  rw [integral_prod _ hΦ, integral_prod _ hΨ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, sa12z2_gEps_ibp s hε i hv hvc x]

/-- The symmetrized pairing at fixed `ε > 0`: the quadratic-form estimate with the factor
`σ cb ∫ k_ρ`, halved by the symmetrization. -/
theorem sa12z2_psi_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d)
    {a u : Euc d → ℝ} {c : Euc d} {ρ : ℝ} (ha : MemCb 1 a) (hu : Continuous u)
    (hucs : HasCompactSupport u) (hsu : Function.support u ⊆ Metric.closedBall c ρ)
    {ε : ℝ} (hε : 0 < ε) :
    |∫ p : Euc d × Euc d, u p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) *
        (a p.2 * u p.2) ∂(volume.prod volume)| ≤
      movtr_sigma s / 2 * cbNorm 1 a * (∫ z, sa12z2_k d s ρ z) * ∫ x, u x ^ 2 := by
  have hsig : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  have hcb : 0 ≤ cbNorm 1 a := HRS.MH.AdjointRd.Phase2SA12Companions.sa12z_cb_nonneg ha
  have hac : Continuous a := ha.1.continuous
  have hu0 : ∀ y, y ∉ Metric.closedBall c ρ → u y = 0 := fun y hy =>
    by_contra fun h => hy (hsu (Function.mem_support.2 h))
  have hDc := sa12z2_dEps_cont (d := d) s hε i
  have hQ := sa12z2_quad_bound hd hs0 hsd hu hucs ρ
  have hΨ : Integrable (fun p : Euc d × Euc d => u p.1 *
      movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * (a p.2 * u p.2))
      (volume.prod volume) := by
    refine sa12z2_integrable_prod_of_zero (c := c) (ρ := ρ) ?_ ?_
    · exact ((hu.comp continuous_fst).mul (hDc.comp (continuous_fst.sub continuous_snd))).mul
        ((hac.comp continuous_snd).mul (hu.comp continuous_snd))
    · intro p hp
      rcases hp with h | h
      · simp [hu0 _ h]
      · simp [hu0 _ h]
  have hG : Integrable (fun p : Euc d × Euc d => u p.2 *
      movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * (a p.1 * u p.1))
      (volume.prod volume) := by
    refine sa12z2_integrable_prod_of_zero (c := c) (ρ := ρ) ?_ ?_
    · exact ((hu.comp continuous_snd).mul (hDc.comp (continuous_fst.sub continuous_snd))).mul
        ((hac.comp continuous_fst).mul (hu.comp continuous_fst))
    · intro p hp
      rcases hp with h | h
      · simp [hu0 _ h]
      · simp [hu0 _ h]
  -- symmetry: the swapped integrand is the negative of `G`
  have hpt_sw : ∀ p : Euc d × Euc d,
      u p.swap.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.swap.1 - p.swap.2) *
        (a p.swap.2 * u p.swap.2) =
      -(u p.2 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) *
        (a p.1 * u p.1)) := by
    intro p
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [← neg_sub p.1 p.2, movtr_dEps_odd]
    ring
  have hswap : ∫ p : Euc d × Euc d, u p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ))
        (p.1 - p.2) * (a p.2 * u p.2) ∂(volume.prod volume) =
      -∫ p : Euc d × Euc d, u p.2 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) *
        (a p.1 * u p.1) ∂(volume.prod volume) := by
    rw [← integral_neg]
    calc _ = ∫ p : Euc d × Euc d, u p.swap.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ))
          (p.swap.1 - p.swap.2) * (a p.swap.2 * u p.swap.2) ∂(volume.prod volume) :=
          (integral_prod_swap (fun p : Euc d × Euc d => u p.1 *
            movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) *
            (a p.2 * u p.2)) (μ := volume) (ν := volume)).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hpt_sw)
  -- the difference `Ψ - G` is `D (u u) (a(y) - a(x))`
  have hdiff : ∫ p : Euc d × Euc d, (u p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ))
        (p.1 - p.2) * (a p.2 * u p.2) - u p.2 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ))
        (p.1 - p.2) * (a p.1 * u p.1)) ∂(volume.prod volume) =
      ∫ p : Euc d × Euc d, movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) *
        (u p.1 * u p.2) * (a p.2 - a p.1) ∂(volume.prod volume) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => by beta_reduce; ring)
  have hsub := integral_sub hΨ hG
  have hΨeq : ∫ p : Euc d × Euc d, u p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ))
        (p.1 - p.2) * (a p.2 * u p.2) ∂(volume.prod volume) =
      (∫ p : Euc d × Euc d, movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) *
        (u p.1 * u p.2) * (a p.2 - a p.1) ∂(volume.prod volume)) / 2 := by
    linarith [hswap, hsub, hdiff]
  -- pointwise bound of the integrand of `∫ (Ψ - G)`
  have hbd : ∀ p : Euc d × Euc d,
      ‖movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * (u p.1 * u p.2) *
        (a p.2 - a p.1)‖ ≤
      movtr_sigma s * cbNorm 1 a * (|u p.1| * |u p.2| * sa12z2_k d s ρ (p.1 - p.2)) := by
    intro p
    have hnn : 0 ≤ movtr_sigma s * cbNorm 1 a *
        (|u p.1| * |u p.2| * sa12z2_k d s ρ (p.1 - p.2)) :=
      mul_nonneg (mul_nonneg hsig hcb)
        (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (sa12z2_k_nonneg (d := d) s ρ _))
    by_cases hz : p.1 - p.2 = 0
    · have h12 : a p.2 - a p.1 = 0 := by
        have hp : p.1 = p.2 := sub_eq_zero.1 hz
        rw [hp, sub_self]
      rw [h12, mul_zero, norm_zero]
      exact hnn
    by_cases hb : u p.1 = 0 ∨ u p.2 = 0
    · have h0 : ‖movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * (u p.1 * u p.2) *
          (a p.2 - a p.1)‖ = 0 := by
        rcases hb with h | h <;> simp [h]
      rw [h0]
      exact hnn
    push_neg at hb
    have h1B : p.1 ∈ Metric.closedBall c ρ := by
      by_contra h
      exact hb.1 (hu0 _ h)
    have h2B : p.2 ∈ Metric.closedBall c ρ := by
      by_contra h
      exact hb.2 (hu0 _ h)
    have hnorm : ‖p.1 - p.2‖ ≤ 2 * ρ := by
      have h1 := Metric.mem_closedBall.1 h1B
      have h2 := Metric.mem_closedBall.1 h2B
      rw [← dist_eq_norm]
      have htri := dist_triangle p.1 c p.2
      rw [dist_comm c p.2] at htri
      linarith
    have hmem : p.1 - p.2 ∈ Metric.closedBall (0 : Euc d) (2 * ρ) := by
      rw [mem_closedBall_zero_iff]
      exact hnorm
    have hkz : sa12z2_k d s ρ (p.1 - p.2) = ‖p.1 - p.2‖ ^ (-s) := by
      unfold sa12z2_k
      rw [Set.indicator_of_mem hmem]
    have hez : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ ≤ 1 := by simp
    have hD := movtr_dEps_abs_le_z hs0 hε.le (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) hez hz
    have hlip := HRS.MH.AdjointRd.Phase2SA12Companions.sa12z_lip_of_cb (r := 1) le_rfl ha p.2 p.1
    rw [norm_sub_rev p.2 p.1] at hlip
    have hne : ‖p.1 - p.2‖ ≠ 0 := norm_ne_zero_iff.2 hz
    have hpow : ‖p.1 - p.2‖ ^ (-s) = ‖p.1 - p.2‖ ^ (-s - 1) * ‖p.1 - p.2‖ := by
      rw [← Real.rpow_add_one hne]
      congr 1
      ring
    rw [hkz]
    simp only [norm_mul, Real.norm_eq_abs]
    calc |movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2)| *
          (|u p.1| * |u p.2|) * |a p.2 - a p.1|
        ≤ (movtr_sigma s * ‖p.1 - p.2‖ ^ (-s - 1)) * (|u p.1| * |u p.2|) *
            (cbNorm 1 a * ‖p.1 - p.2‖) := by gcongr
      _ = movtr_sigma s * cbNorm 1 a * (|u p.1| * |u p.2| *
            (‖p.1 - p.2‖ ^ (-s - 1) * ‖p.1 - p.2‖)) := by ring
      _ = movtr_sigma s * cbNorm 1 a * (|u p.1| * |u p.2| * ‖p.1 - p.2‖ ^ (-s)) := by rw [hpow]
  have hnormH : ‖∫ p : Euc d × Euc d, movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) *
        (u p.1 * u p.2) * (a p.2 - a p.1) ∂(volume.prod volume)‖ ≤
      movtr_sigma s * cbNorm 1 a * ((∫ z, sa12z2_k d s ρ z) * ∫ x, u x ^ 2) := by
    refine (norm_integral_le_of_norm_le ((hQ.1.const_mul (movtr_sigma s * cbNorm 1 a)))
      (Filter.Eventually.of_forall hbd)).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hQ.2 (mul_nonneg hsig hcb)
  rw [hΨeq, abs_div, abs_two, ← Real.norm_eq_abs]
  linarith [hnormH]

end HRS.MH.AdjointRd.Phase2SA12Near
