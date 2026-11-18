import HRS.MS.SA16CutDefs
import HRS.MS.CzElemAux4

/-!
# S.A.16 K6: `jump_commutator_expansion`

At finite cutoff, the commutator of the positive-jump operator with `μ`, minus the raw odd cutoff against
`∇μ`, is the integral over `{δ < |z|}` of the Taylor remainder kernel `elema_G`; the same majorant
`elema_kk` (in `L¹` for `1 < θ < 2`) and Young's inequality give the `L^p` bound uniformly in `δ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA

lemma sa16k_repr {d : ℕ} (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) {μ : Euc d → ℝ}
    (hμ : MemCb 2 μ) (W : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    jumpCut d θ δ (fun y => μ y * W y) x - μ x * jumpCut d θ δ W x -
        ∑ i : Fin d, gradient μ x i * rawOdd d θ δ i W x =
      ∫ z in {z : Euc d | δ < ‖z‖}, elema_G d θ μ W x z := by
  have hθ0 : 0 < θ := by linarith
  have hμ2 : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, -, -, h0, h1, h2⟩ := elema_cb2_data hμ
  have hpvμ : PvC2 μ B0 B1 B2 :=
    PvC2.of_contDiff hμ2 (fun y => by simpa [Real.norm_eq_abs] using h0 y)
      (fun y => by simpa using h1 y) h2
  obtain ⟨BW, LW, MW, hpvW⟩ := PvC2.of_schwartz W
  have hpvμW := hpvμ.mul hpvW
  set S : Set (Euc d) := {z : Euc d | δ < ‖z‖} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have iA := pvapi_integrableOn_h1 hd hθ0 hpvμW x hδ
  have iB := pvapi_integrableOn_h1 hd hθ0 hpvW x hδ
  have iC : ∀ i : Fin d, IntegrableOn (fun z : Euc d => z i / ‖z‖ ^ ((d : ℝ) + θ) * W (x - z)) S := by
    intro i
    have hrpow : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-((d : ℝ) + θ - 1))) S :=
      pvapi_integrableOn_rpow_outside hd (s := (d : ℝ) + θ - 1) (by linarith) hδ
    have hmeas : Measurable (fun z : Euc d => z i / ‖z‖ ^ ((d : ℝ) + θ) * W (x - z)) :=
      (((EuclideanSpace.proj i).continuous.measurable).div
        (measurable_norm.pow_const _)).mul
        (W.continuous.measurable.comp (measurable_const.sub measurable_id))
    refine Integrable.mono' (hrpow.const_mul BW) hmeas.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun z hz => ?_)
    have hz' : δ < ‖z‖ := hz
    have hn : 0 < ‖z‖ := hδ.trans hz'
    have hW : |W (x - z)| ≤ BW := hpvW.bdd _
    have hzi : |z i| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z i
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (Real.rpow_pos_of_pos hn _)]
    have e : ‖z‖ ^ (-((d : ℝ) + θ - 1)) = ‖z‖ / ‖z‖ ^ ((d : ℝ) + θ) := by
      rw [show -((d : ℝ) + θ - 1) = (1 : ℝ) - ((d : ℝ) + θ) by ring, Real.rpow_sub hn,
        Real.rpow_one]
    rw [e]
    have hpos : 0 < ‖z‖ ^ ((d : ℝ) + θ) := Real.rpow_pos_of_pos hn _
    calc |z i| / ‖z‖ ^ ((d : ℝ) + θ) * |W (x - z)| ≤ ‖z‖ / ‖z‖ ^ ((d : ℝ) + θ) * BW := by
          refine mul_le_mul (div_le_div_of_nonneg_right hzi hpos.le) hW (abs_nonneg _)
            (by positivity)
      _ = BW * (‖z‖ / ‖z‖ ^ ((d : ℝ) + θ)) := by ring
  -- pointwise identity
  have hpt : ∀ z : Euc d, elema_G d θ μ W x z =
      ((μ x * W x - μ (x - z) * W (x - z)) / ‖z‖ ^ ((d : ℝ) + θ)) -
        μ x * ((W x - W (x - z)) / ‖z‖ ^ ((d : ℝ) + θ)) -
        ∑ i : Fin d, gradient μ x i * (z i / ‖z‖ ^ ((d : ℝ) + θ) * W (x - z)) := by
    intro z
    have hs : ∑ i : Fin d, gradient μ x i * (z i / ‖z‖ ^ ((d : ℝ) + θ) * W (x - z)) =
        (∑ i : Fin d, gradient μ x i * z i) * (W (x - z) / ‖z‖ ^ ((d : ℝ) + θ)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hs, elema_grad_sum]
    unfold elema_G elema_R
    ring
  have hint : ∫ z in S, elema_G d θ μ W x z =
      (∫ z in S, ((μ x * W x - μ (x - z) * W (x - z)) / ‖z‖ ^ ((d : ℝ) + θ))) -
        μ x * (∫ z in S, (W x - W (x - z)) / ‖z‖ ^ ((d : ℝ) + θ)) -
        ∑ i : Fin d, gradient μ x i *
          ∫ z in S, z i / ‖z‖ ^ ((d : ℝ) + θ) * W (x - z) := by
    simp_rw [hpt]
    have iAB : IntegrableOn (fun z : Euc d => ((μ x * W x - μ (x - z) * W (x - z)) /
        ‖z‖ ^ ((d : ℝ) + θ)) - μ x * ((W x - W (x - z)) / ‖z‖ ^ ((d : ℝ) + θ))) S :=
      iA.sub (iB.const_mul (μ x))
    have iCs : IntegrableOn (fun z : Euc d => ∑ i : Fin d, gradient μ x i *
        (z i / ‖z‖ ^ ((d : ℝ) + θ) * W (x - z))) S :=
      integrable_finset_sum _ fun i _ => (iC i).const_mul (gradient μ x i)
    rw [integral_sub iAB iCs, integral_sub iA (iB.const_mul (μ x)), integral_const_mul,
      integral_finset_sum _ (fun i _ => (iC i).const_mul (gradient μ x i))]
    simp_rw [integral_const_mul]
    rfl
  rw [hint]
  unfold jumpCut rawOdd
  rfl


theorem jump_commutator_expansion (d : ℕ) (hd : 1 ≤ d) (θ p : ℝ)
    (hθ1 : 1 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,
      ∀ μ : Euc d → ℝ, MemCb 2 μ → ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (fun x => jumpCut d θ δ (fun y => μ y*W y) x-
          μ x*jumpCut d θ δ W x-
          ∑ i : Fin d, gradient μ x i*rawOdd d θ δ i W x)
        (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C*cbNorm 2 μ)*eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨C0, hC0, hkk⟩ := elema_kk_lintegral hd hθ1 hθ2 (B := 1) zero_le_one
  refine ⟨C0 + 1, by linarith, fun δ hδ μ hμ W => ?_⟩
  have hμ2 : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hcb, -, h0, h1, h2⟩ := elema_cb2_data hμ
  have hfun : (fun x => jumpCut d θ δ (fun y => μ y*W y) x-
          μ x*jumpCut d θ δ W x-
          ∑ i : Fin d, gradient μ x i*rawOdd d θ δ i W x) =
      fun x : Euc d => ∫ z in {z : Euc d | δ < ‖z‖}, elema_G d θ μ W x z :=
    funext fun x => sa16k_repr hd hθ1 hδ.1 hμ W x
  rw [hfun]
  have hS : MeasurableSet {z : Euc d | δ < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hFm : AEStronglyMeasurable (fun x : Euc d => ∫ z in {z : Euc d | δ < ‖z‖},
      elema_G d θ μ W x z) volume := by
    have hmeas : Measurable (fun q : Euc d × Euc d =>
        Set.indicator {q : Euc d × Euc d | δ < ‖q.2‖} (fun q => elema_G d θ μ W q.1 q.2) q) :=
      (elema_G_measurable_prod (θ := θ) hμ2.continuous (hμ2.continuous_fderiv (by norm_num))
        W.continuous).indicator (measurableSet_lt measurable_const (measurable_norm.comp measurable_snd))
    have heq : (fun x : Euc d => ∫ z in {z : Euc d | δ < ‖z‖}, elema_G d θ μ W x z) =
        fun x : Euc d => ∫ z, (fun q : Euc d × Euc d => Set.indicator
          {q : Euc d × Euc d | δ < ‖q.2‖} (fun q => elema_G d θ μ W q.1 q.2) q) (x, z) := by
      funext x
      rw [← integral_indicator hS]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [Set.indicator, Set.mem_setOf_eq]
    rw [heq]
    exact (hmeas.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
  have hbound := hkk (B2 / 2) (B0 + B1 / 2) (by linarith) (by linarith)
  refine (elema_young (elema_kk_measurable θ 1 (B2 / 2) (B0 + B1 / 2)) W.continuous.measurable
    hFm (by linarith) (fun x => ?_)).trans (mul_le_mul_left ?_ _)
  · refine (enorm_integral_le_lintegral_enorm _).trans
      ((setLIntegral_le_lintegral _ _).trans (lintegral_mono fun z => ?_))
    exact elema_G_le hμ2 hB0 hB1 hB2 h0 h1 h2 x z
  · refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hcb]
    have hcb0 : 0 ≤ B0 + B1 + B2 := by linarith
    nlinarith [mul_nonneg hC0 hB0, mul_nonneg hC0 hB1, mul_nonneg hC0 hB2]

end HRS.Whole.AppendixA.Phase2SA16Cutoff
