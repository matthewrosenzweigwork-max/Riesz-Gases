import HRS.MS.SA12NearN3A

/-!
# S.A.12 N3, part B (SA12Z2): the truncated singular weight and the quadratic-form estimate

Schur-type bound for the truncated Riesz weight `|z|^{-s} 1_{|z| ≤ 2ρ}`:
`∫ k_ρ ≤ C_k ρ^d` for `ρ ≥ 1`, and `∬ |u x| |u y| k_ρ(x-y) ≤ (∫ k_ρ) ∫ u²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- The truncated singular weight `|z|^{-s} 1_{|z| ≤ 2ρ}`. -/
def sa12z2_k (d : ℕ) (s ρ : ℝ) (z : Euc d) : ℝ :=
  (Metric.closedBall (0 : Euc d) (2 * ρ)).indicator (fun z => ‖z‖ ^ (-s)) z

theorem sa12z2_rpow_locInt (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    LocallyIntegrable (fun z : Euc d => ‖z‖ ^ (-s)) volume := by
  by_cases hs : s = 0
  · subst hs
    simpa using (continuous_const (y := (1 : ℝ))).locallyIntegrable
  · have := rieszKernel_locallyIntegrable (d := d) (s := s) hs0 hsd
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    unfold rieszKernel
    simp [hs]

theorem sa12z2_k_nonneg (s ρ : ℝ) (z : Euc d) : 0 ≤ sa12z2_k d s ρ z := by
  unfold sa12z2_k
  exact Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) z

theorem sa12z2_k_even (s ρ : ℝ) (z : Euc d) : sa12z2_k d s ρ (-z) = sa12z2_k d s ρ z := by
  unfold sa12z2_k
  simp [Set.indicator, norm_neg]

theorem sa12z2_k_measurable (s ρ : ℝ) : Measurable (sa12z2_k d s ρ) := by
  unfold sa12z2_k
  exact (measurable_norm.pow_const (-s)).indicator Metric.isClosed_closedBall.measurableSet

theorem sa12z2_k_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (ρ : ℝ) :
    Integrable (sa12z2_k d s ρ) := by
  unfold sa12z2_k
  exact ((sa12z2_rpow_locInt hd hs0 hsd).integrableOn_isCompact
    (isCompact_closedBall (0 : Euc d) (2 * ρ))).integrable_indicator
    Metric.isClosed_closedBall.measurableSet

/-- `∫ k_ρ ≤ C ρ^d` for `ρ ≥ 1`. -/
theorem sa12z2_k_integral_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∫ z, sa12z2_k d s ρ z ≤ Ck * ρ ^ d := by
  set K1 : ℝ := ∫ z in Metric.closedBall (0 : Euc d) 1, ‖z‖ ^ (-s) with hK1
  set V1 : ℝ := (volume (Metric.ball (0 : Euc d) 1)).toReal with hV1
  have hK10 : 0 ≤ K1 := setIntegral_nonneg Metric.isClosed_closedBall.measurableSet
    (fun z _ => Real.rpow_nonneg (norm_nonneg z) _)
  have hV10 : 0 ≤ V1 := ENNReal.toReal_nonneg
  refine ⟨K1 + 2 ^ d * V1, by positivity, fun ρ hρ => ?_⟩
  have hρ0 : 0 ≤ 2 * ρ := by linarith
  have hloc := sa12z2_rpow_locInt hd hs0 hsd
  have hint2 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.closedBall 0 (2 * ρ)) :=
    hloc.integrableOn_isCompact (isCompact_closedBall _ _)
  have hone : IntegrableOn (fun _ : Euc d => (1 : ℝ)) (Metric.closedBall 0 (2 * ρ)) :=
    integrableOn_const (measure_closedBall_lt_top.ne)
  set ind : Euc d → ℝ := (Metric.closedBall (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) with hind
  have hint1 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.closedBall 0 1) :=
    hloc.integrableOn_isCompact (isCompact_closedBall _ _)
  have hindint : Integrable ind := hint1.integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hind0 : ∀ z, 0 ≤ ind z := fun z =>
    Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) z
  unfold sa12z2_k
  rw [integral_indicator Metric.isClosed_closedBall.measurableSet]
  have h1 : ∫ z in Metric.closedBall (0 : Euc d) (2 * ρ), ‖z‖ ^ (-s) ≤
      ∫ z in Metric.closedBall (0 : Euc d) (2 * ρ), (ind z + 1) := by
    refine setIntegral_mono_on hint2 (hindint.integrableOn.add hone)
      Metric.isClosed_closedBall.measurableSet (fun z _ => ?_)
    by_cases hz : z ∈ Metric.closedBall (0 : Euc d) 1
    · rw [hind, Set.indicator_of_mem hz]; linarith
    · rw [hind, Set.indicator_of_notMem hz]
      have hz1 : 1 < ‖z‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz
      have := Real.rpow_le_one_of_one_le_of_nonpos hz1.le (by linarith : -s ≤ 0)
      linarith
  refine h1.trans ?_
  rw [integral_add hindint.integrableOn hone]
  have hA : ∫ z in Metric.closedBall (0 : Euc d) (2 * ρ), ind z ≤ K1 := by
    calc ∫ z in Metric.closedBall (0 : Euc d) (2 * ρ), ind z ≤ ∫ z, ind z :=
          setIntegral_le_integral hindint (Filter.Eventually.of_forall hind0)
      _ = K1 := by rw [hind, integral_indicator Metric.isClosed_closedBall.measurableSet]
  have hB : ∫ z in Metric.closedBall (0 : Euc d) (2 * ρ), (1 : ℝ) = (2 * ρ) ^ d * V1 := by
    have hfr : Module.finrank ℝ (Euc d) = d := by simp
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real,
      Measure.addHaar_closedBall _ _ hρ0, hfr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hρ0 _), hV1]
  rw [hB]
  have hρd : (1 : ℝ) ≤ ρ ^ d := one_le_pow₀ hρ
  have e1 : (2 * ρ) ^ d * V1 = 2 ^ d * V1 * ρ ^ d := by rw [mul_pow]; ring
  rw [e1]
  nlinarith [mul_nonneg hK10 (sub_nonneg.2 hρd)]

theorem sa12z2_quad_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {u : Euc d → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) (ρ : ℝ) :
    Integrable (fun p : Euc d × Euc d => |u p.1| * |u p.2| * sa12z2_k d s ρ (p.1 - p.2))
      (volume.prod volume) ∧
    ∫ p : Euc d × Euc d, |u p.1| * |u p.2| * sa12z2_k d s ρ (p.1 - p.2) ∂(volume.prod volume) ≤
      (∫ z, sa12z2_k d s ρ z) * ∫ x, u x ^ 2 := by
  have hk := sa12z2_k_integrable hd hs0 hsd ρ
  have hkm := sa12z2_k_measurable (d := d) s ρ
  have hu2c : HasCompactSupport (fun x => u x ^ 2) :=
    huc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hu2 : Integrable (fun x => u x ^ 2) := (hu.pow 2).integrable_of_hasCompactSupport hu2c
  have hF1 : Integrable (fun p : Euc d × Euc d => u p.2 ^ 2 * sa12z2_k d s ρ (p.1 - p.2))
      (volume.prod volume) := by
    have := hu2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hk
    simpa using this
  have hF2 : Integrable (fun p : Euc d × Euc d => u p.1 ^ 2 * sa12z2_k d s ρ (p.1 - p.2))
      (volume.prod volume) := by
    refine (hF1.swap).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
    rw [← neg_sub p.1 p.2, sa12z2_k_even]
  have hmeas : AEStronglyMeasurable
      (fun p : Euc d × Euc d => |u p.1| * |u p.2| * sa12z2_k d s ρ (p.1 - p.2)) (volume.prod volume) := by
    refine ((hu.comp continuous_fst).abs.mul (hu.comp continuous_snd).abs).aestronglyMeasurable.mul ?_
    exact (hkm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  have hdom : ∀ p : Euc d × Euc d, |u p.1| * |u p.2| * sa12z2_k d s ρ (p.1 - p.2) ≤
      (1 / 2) * (u p.2 ^ 2 * sa12z2_k d s ρ (p.1 - p.2) + u p.1 ^ 2 * sa12z2_k d s ρ (p.1 - p.2)) := by
    intro p
    have hk0 := sa12z2_k_nonneg (d := d) s ρ (p.1 - p.2)
    have hAM : |u p.1| * |u p.2| ≤ (1 / 2) * (u p.2 ^ 2 + u p.1 ^ 2) := by
      have := two_mul_le_add_sq |u p.1| |u p.2|
      rw [sq_abs, sq_abs] at this
      linarith
    calc |u p.1| * |u p.2| * sa12z2_k d s ρ (p.1 - p.2)
        ≤ ((1 / 2) * (u p.2 ^ 2 + u p.1 ^ 2)) * sa12z2_k d s ρ (p.1 - p.2) :=
          mul_le_mul_of_nonneg_right hAM hk0
      _ = _ := by ring
  have hint : Integrable (fun p : Euc d × Euc d => |u p.1| * |u p.2| * sa12z2_k d s ρ (p.1 - p.2))
      (volume.prod volume) := by
    refine Integrable.mono' ((hF1.add hF2).const_mul (1 / 2)) hmeas (Filter.Eventually.of_forall fun p => ?_)
    have hk0 := sa12z2_k_nonneg (d := d) s ρ (p.1 - p.2)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hk0)]
    have := hdom p
    simp only [Pi.add_apply]
    linarith
  refine ⟨hint, ?_⟩
  have hI1 : ∫ p : Euc d × Euc d, u p.2 ^ 2 * sa12z2_k d s ρ (p.1 - p.2) ∂(volume.prod volume) =
      (∫ z, sa12z2_k d s ρ z) * ∫ x, u x ^ 2 := by
    rw [integral_prod_symm _ hF1]
    have : ∀ y : Euc d, ∫ x, u y ^ 2 * sa12z2_k d s ρ (x - y) = u y ^ 2 * ∫ z, sa12z2_k d s ρ z := by
      intro y
      rw [integral_const_mul, integral_sub_right_eq_self (sa12z2_k d s ρ) y]
    simp_rw [this]
    rw [integral_mul_const, mul_comm]
  have hI2 : ∫ p : Euc d × Euc d, u p.1 ^ 2 * sa12z2_k d s ρ (p.1 - p.2) ∂(volume.prod volume) =
      (∫ z, sa12z2_k d s ρ z) * ∫ x, u x ^ 2 := by
    rw [← hI1, ← integral_prod_swap (fun p : Euc d × Euc d => u p.2 ^ 2 * sa12z2_k d s ρ (p.1 - p.2))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [← neg_sub p.1 p.2, sa12z2_k_even]
  calc _ ≤ ∫ p : Euc d × Euc d, (1 / 2) * (u p.2 ^ 2 * sa12z2_k d s ρ (p.1 - p.2) +
        u p.1 ^ 2 * sa12z2_k d s ρ (p.1 - p.2)) ∂(volume.prod volume) :=
        integral_mono hint ((hF1.add hF2).const_mul (1 / 2)) hdom
    _ = (1 / 2) * ((∫ p : Euc d × Euc d, u p.2 ^ 2 * sa12z2_k d s ρ (p.1 - p.2) ∂(volume.prod volume)) +
        ∫ p : Euc d × Euc d, u p.1 ^ 2 * sa12z2_k d s ρ (p.1 - p.2) ∂(volume.prod volume)) := by
        rw [integral_const_mul, integral_add hF1 hF2]
    _ = (∫ z, sa12z2_k d s ρ z) * ∫ x, u x ^ 2 := by
        rw [hI1, hI2]; ring

end HRS.MH.AdjointRd.Phase2SA12Near
