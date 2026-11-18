import HRS.MS.SA16CutDefs
import HRS.MS.CzElemAux4

/-!
# S.A.16 K7, part (a): representation of the jump commutator and the case `0 < θ < 1` (worker SA16U3)

`jumpCut(μW) - μ jumpCut(W) = ∫_{δ<|z|} (μ(x)-μ(x-z)) W(x-z) |z|^{-(d+θ)} dz` (`sa16u3_k7_repr`).  For `θ < 1` the
kernel is dominated by `elema_kk d (θ+1) 1 ‖Dμ‖ ‖μ‖` (Lipschitz near zero, boundedness far away), which is in `L^1`
uniformly in `δ`; Young's inequality closes the estimate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA

section K7a
variable {d : ℕ}

/-- the commutator is the integral of `(μ x - μ (x-z)) W (x-z) / |z|^(d+θ)` over `|z| > δ` -/
lemma sa16u3_k7_repr (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) {μ : Euc d → ℝ}
    (hμ : MemCb 2 μ) (W : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    jumpCut d θ δ (fun y => μ y * W y) x - μ x * jumpCut d θ δ W x =
      ∫ z in {z : Euc d | δ < ‖z‖}, (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ) := by
  obtain ⟨B0, L0, M0, hpvμ⟩ := PvC2.of_memCb hμ
  obtain ⟨BW, LW, MW, hpvW⟩ := PvC2.of_schwartz W
  have hpvμW := hpvμ.mul hpvW
  have iA := pvapi_integrableOn_h1 hd hθ hpvμW x hδ
  have iB := pvapi_integrableOn_h1 hd hθ hpvW x hδ
  unfold jumpCut
  rw [← integral_const_mul, ← integral_sub iA (iB.const_mul (μ x))]
  refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm) fun z _ => ?_
  ring

lemma sa16u3_k7_aesm {θ δ : ℝ} {μ : Euc d → ℝ} (hμ : Continuous μ) (W : SchwartzMap (Euc d) ℝ) :
    AEStronglyMeasurable (fun x : Euc d => ∫ z in {z : Euc d | δ < ‖z‖},
      (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ)) volume := by
  have hS : MeasurableSet {z : Euc d | δ < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hmeas : Measurable (fun q : Euc d × Euc d => Set.indicator {q : Euc d × Euc d | δ < ‖q.2‖}
      (fun q => (μ q.1 - μ (q.1 - q.2)) * W (q.1 - q.2) / ‖q.2‖ ^ ((d : ℝ) + θ)) q) := by
    refine Measurable.indicator ?_ (measurableSet_lt measurable_const (measurable_norm.comp measurable_snd))
    exact ((((hμ.comp continuous_fst).sub (hμ.comp (continuous_fst.sub continuous_snd))).mul
      (W.continuous.comp (continuous_fst.sub continuous_snd))).measurable).div
      ((measurable_norm.comp measurable_snd).pow_const _)
  have heq : (fun x : Euc d => ∫ z in {z : Euc d | δ < ‖z‖},
      (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ)) =
      fun x : Euc d => ∫ z, (fun q : Euc d × Euc d => Set.indicator {q : Euc d × Euc d | δ < ‖q.2‖}
        (fun q => (μ q.1 - μ (q.1 - q.2)) * W (q.1 - q.2) / ‖q.2‖ ^ ((d : ℝ) + θ)) q) (x, z) := by
    funext x
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Set.indicator, Set.mem_setOf_eq]
  rw [heq]
  exact (hmeas.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable

/-- pointwise bound of the commutator kernel for `0 < θ < 1` -/
lemma sa16u3_kk_le {θ B0 B1 D : ℝ} (hθ : 0 < θ) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (z : Euc d)
    (h1 : |D| ≤ B1 * ‖z‖) (h2 : |D| ≤ 2 * B0) :
    |D| / ‖z‖ ^ ((d : ℝ) + θ) ≤ elema_kk d (θ + 1) 1 B1 B0 z := by
  by_cases hz : z = 0
  · subst hz
    have : ‖(0 : Euc d)‖ = 0 := norm_zero
    have h3 : (0 : ℝ) ≤ elema_kk d (θ + 1) 1 B1 B0 0 :=
      elema_kk_nonneg _ 1 _ _ zero_le_one hB1 hB0 0
    calc |D| / ‖(0 : Euc d)‖ ^ ((d : ℝ) + θ) ≤ 0 := by
          rw [this]
          have : (0 : ℝ) ^ ((d : ℝ) + θ) = 0 := Real.zero_rpow (by
            have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
            linarith)
          rw [this, div_zero]
      _ ≤ _ := h3
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hD : 0 < ‖z‖ ^ ((d : ℝ) + θ) := Real.rpow_pos_of_pos hn _
    rw [div_le_iff₀ hD]
    unfold elema_kk
    split_ifs with h
    · calc |D| ≤ B1 * ‖z‖ := h1
        _ = 1 * B1 * ‖z‖ ^ (2 - ((d : ℝ) + (θ + 1))) * ‖z‖ ^ ((d : ℝ) + θ) := by
            rw [mul_assoc (1 * B1), ← Real.rpow_add hn]
            have : (2 - ((d : ℝ) + (θ + 1)) + ((d : ℝ) + θ)) = 1 := by ring
            rw [this, Real.rpow_one]
            ring
    · calc |D| ≤ 2 * B0 := h2
        _ = 1 * (2 * B0) * ‖z‖ ^ (1 - ((d : ℝ) + (θ + 1))) * ‖z‖ ^ ((d : ℝ) + θ) := by
            rw [mul_assoc (1 * (2 * B0)), ← Real.rpow_add hn]
            have : (1 - ((d : ℝ) + (θ + 1)) + ((d : ℝ) + θ)) = 0 := by ring
            rw [this, Real.rpow_zero]
            ring

end K7a

/-- K7 for `0 < θ < 1` -/
theorem sa16u3_k7_lt_one (d : ℕ) (hd : 1 ≤ d) (θ p : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ μ : Euc d → ℝ, MemCb 2 μ →
      ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (fun x => jumpCut d θ δ (fun y => μ y * W y) x - μ x * jumpCut d θ δ W x)
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * cbNorm 2 μ) * eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨C0, hC0, hkk⟩ := elema_kk_lintegral hd (θ := θ + 1) (by linarith) (by linarith)
    (B := 1) zero_le_one
  refine ⟨C0 + 1, by linarith, fun δ hδ μ hμ W => ?_⟩
  have hμ2 : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hcb, -, h0, h1, h2⟩ := elema_cb2_data hμ
  have hlip : ∀ a b, |μ a - μ b| ≤ B1 * ‖a - b‖ :=
    pvapi_lip_of_fderiv (hμ2.differentiable (by norm_num)) h1
  have hfun : (fun x => jumpCut d θ δ (fun y => μ y * W y) x - μ x * jumpCut d θ δ W x) =
      fun x : Euc d => ∫ z in {z : Euc d | δ < ‖z‖},
        (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ) :=
    funext fun x => sa16u3_k7_repr hd hθ0 hδ.1 hμ W x
  rw [hfun]
  have hFm := sa16u3_k7_aesm (θ := θ) (δ := δ) hμ2.continuous W
  have hbound := hkk B1 B0 hB1 hB0
  refine (elema_young (elema_kk_measurable (θ + 1) 1 B1 B0) W.continuous.measurable
    hFm (by linarith) (fun x => ?_)).trans (mul_le_mul_left ?_ _)
  · refine (enorm_integral_le_lintegral_enorm _).trans
      ((setLIntegral_le_lintegral _ _).trans (lintegral_mono fun z => ?_))
    have hk0 := elema_kk_nonneg (d := d) (θ + 1) 1 B1 B0 zero_le_one hB1 hB0 z
    have e1 : |μ x - μ (x - z)| ≤ B1 * ‖z‖ := by
      have := hlip x (x - z)
      simpa using this
    have e2 : |μ x - μ (x - z)| ≤ 2 * B0 := by
      have a1 := h0 x
      have a2 := h0 (x - z)
      calc |μ x - μ (x - z)| ≤ |μ x| + |μ (x - z)| := abs_sub _ _
        _ ≤ 2 * B0 := by linarith
    have hk := sa16u3_kk_le (d := d) hθ0 hB0 hB1 z e1 e2
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hk0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hn : 0 ≤ ‖z‖ ^ ((d : ℝ) + θ) := Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hn]
    calc |μ x - μ (x - z)| * |W (x - z)| / ‖z‖ ^ ((d : ℝ) + θ)
        = (|μ x - μ (x - z)| / ‖z‖ ^ ((d : ℝ) + θ)) * |W (x - z)| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  · refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hcb]
    nlinarith [mul_nonneg hC0 hB0, mul_nonneg hC0 hB1, mul_nonneg hC0 hB2]

end HRS.Whole.AppendixA.Phase2SA16Cutoff
