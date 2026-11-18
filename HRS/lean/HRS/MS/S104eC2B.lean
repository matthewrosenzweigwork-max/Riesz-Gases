import HRS.MS.S104eC2A
import HRS.MS.UlTail

/-!
# S104E route C, packet C2, part B: sup bound, vanishing at infinity, identification and differentiation of `ultK` on Hölder data

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.  For `g` continuous, `η`-Hölder near (`HolNear η H g`), `‖g y‖ ≤ A0 (1+‖y‖)^{-L}`, `L > d`:

* `s104c2_K_bound`: `‖ultK κ g x‖ ≤ CN H + CF A0`;
* `s104c2_K_van`: `ultK κ g x → 0` at infinity;
* `s104c2_conv_comp`: `convGradConvW (rieszKernelGrad d s) g x i = ultK (u2_kap d s i) g x` and the integrand is integrable (no Bochner junk);
* `s104c2_K_iter`: `D^m (ultK κ k) = ultK κ (D^m k)` and `ultK κ k ∈ C^j` for `k ∈ U2Dec j L A` with all `D^m k` Hölder near.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

lemma s104c2_near_bound (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η : ℝ} (hK : UlKer κ s) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) :
    ∃ CN : ℝ, 0 ≤ CN ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Euc d → F) (H : ℝ),
      0 ≤ H → HolNear η H g → ∀ x, ‖ultNear κ g x‖ ≤ CN * H := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  have hΦ := s104c2_Psi_int hd hK.hs0 hη1 hηd
  have hΦ0 : 0 ≤ ∫ z, s104c2_Psi d s η z := integral_nonneg fun z => s104c2_Psi_nonneg s η z
  refine ⟨C0 * ∫ z, s104c2_Psi d s η z, mul_nonneg hC0 hΦ0, ?_⟩
  intro F _ _ g H hH hh x
  unfold ultNear
  calc ‖∫ z, ultKN κ z • (g (x - z) - g x)‖
      ≤ ∫ z, C0 * H * s104c2_Psi d s η z := by
        refine norm_integral_le_of_norm_le (hΦ.const_mul (C0 * H)) ?_
        filter_upwards [u2_ae_ne_zero hd] with z hz
        refine s104c2_near_dom hC0 hb hH hz (fun h1 => ?_)
        have := hh (x - z) x (by simpa using h1)
        simpa using this
    _ = (C0 * ∫ z, s104c2_Psi d s η z) * H := by rw [integral_const_mul]; ring

lemma s104c2_K_bound (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η : ℝ} (hK : UlKer κ s) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) {L : ℝ} (hL : (d : ℝ) < L) :
    ∃ CN CF : ℝ, 0 ≤ CN ∧ 0 ≤ CF ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : Euc d → F) (H A0 : ℝ), 0 ≤ H → 0 ≤ A0 → HolNear η H g → (∀ y, ‖g y‖ ≤ A0 * u2Wt L y) →
      ∀ x, ‖ultK κ g x‖ ≤ CN * H + CF * A0 := by
  obtain ⟨CN, hCN0, hCN⟩ := s104c2_near_bound hd hK hη1 hηd
  obtain ⟨Cu, hCu0, hCu⟩ := u2_conv_norm_le (ult_far_U2Ker hd hK) hL
  refine ⟨CN, Cu, hCN0, hCu0, ?_⟩
  intro F _ _ g H A0 hH hA0 hh hw x
  unfold ultK
  exact (norm_add_le _ _).trans (add_le_add (hCN F g H hH hh x) (hCu F g A0 hA0 hw x))

lemma s104c2_far_pt {κ : Euc d → ℝ} {s C0 : ℝ} (hC0 : 0 ≤ C0)
    (hb : ∀ z : Euc d, z ≠ 0 → ‖κ z‖ ≤ C0 * ‖z‖ ^ (-(s + 1))) {z : Euc d} (hz : z ≠ 0) :
    ‖ultKF κ z‖ ≤ C0 * ‖z‖ ^ (-(s + 1)) := by
  by_cases h : ‖z‖ ≤ 1 / 4
  · simp only [ultKF, h, ite_true, norm_zero]
    exact mul_nonneg hC0 (Real.rpow_nonneg (norm_nonneg _) _)
  · simp only [ultKF, h, ite_false]
    exact hb z hz

lemma s104c2_far_van (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L : ℝ} (hL : (d : ℝ) < L)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {g : Euc d → F} (hg : Continuous g) {A0 : ℝ}
    (hA0 : 0 ≤ A0) (hb : ∀ y, ‖g y‖ ≤ A0 * u2Wt L y) :
    Tendsto (u2Conv (ultKF κ) g) (cocompact (Euc d)) (𝓝 0) := by
  obtain ⟨C0, hC0, hb0⟩ := ult_ker_bound hK
  have hgi : Integrable g volume := by
    refine ((u2_integrable_wt hL).const_mul A0).mono' hg.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  have hfun : u2Conv (ultKF κ) g = fun x => ∫ y, ultKF κ (x - y) • g y := by
    funext x
    unfold u2Conv
    rw [← integral_sub_left_eq_self (fun y => ultKF κ (x - y) • g y) volume x]
    simp
  rw [hfun]
  have : (cocompact (Euc d)).IsCountablyGenerated := by
    have : cocompact (Euc d) = comap norm atTop := by
      exact (Metric.cobounded_eq_cocompact (α := Euc d)).symm.trans (comap_norm_atTop (E := Euc d)).symm
    rw [this]
    infer_instance
  have hFb : ∀ z : Euc d, ‖ultKF κ z‖ ≤ C0 * (1 / 4 : ℝ) ^ (-(s + 1)) := fun z =>
    ult_far_bound hC0 hb0 hK.hs0 z
  have hmain := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := cocompact (Euc d))
    (F := fun x y => ultKF κ (x - y) • g y) (f := fun _ => (0 : F))
    (bound := fun y => (C0 * (1 / 4 : ℝ) ^ (-(s + 1))) * ‖g y‖) ?_ ?_ (hgi.norm.const_mul _) ?_
  · simpa using hmain
  · refine Filter.Eventually.of_forall fun x => ?_
    exact ((ultKF_meas hK.meas).comp (measurable_const.sub measurable_id)).aestronglyMeasurable.smul
      hg.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun y => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hFb _) (norm_nonneg _)
  · refine Filter.Eventually.of_forall fun y => ?_
    have h1 : Tendsto (fun x : Euc d => ultKF κ (x - y)) (cocompact (Euc d)) (𝓝 0) := by
      have hx : Tendsto (fun x : Euc d => ‖x - y‖) (cocompact (Euc d)) atTop :=
        tendsto_norm_cocompact_atTop.comp ((Homeomorph.subRight y).isClosedEmbedding.tendsto_cocompact)
      have hr : Tendsto (fun x : Euc d => C0 * ‖x - y‖ ^ (-(s + 1))) (cocompact (Euc d)) (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop (y := s + 1) (by linarith [hK.hs0])).comp hx
        simpa using this.const_mul C0
      refine squeeze_zero_norm' (Filter.Eventually.of_forall fun x => ?_) hr
      by_cases hz : x - y = 0
      · rw [hz]
        have : ultKF κ (0 : Euc d) = 0 := by simp [ultKF]
        rw [this, norm_zero]
        have h2 : (0 : ℝ) ^ (-(s + 1)) = 0 := Real.zero_rpow (by linarith [hK.hs0])
        rw [norm_zero, h2, mul_zero]
      · have := s104c2_far_pt hC0 hb0 hz
        simpa using this
    simpa using h1.smul_const (g y)

end HRS.MS.S104e.C

end
