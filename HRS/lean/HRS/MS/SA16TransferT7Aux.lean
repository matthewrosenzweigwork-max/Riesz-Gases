import HRS.MS.SA16CutK2
import HRS.MS.SA16StrongSL10

/-!
# S.A.16 T7 support: the compatible odd operators

* `sa16y_spliceOdd_diff_bound`: for Schwartz `v`, `‖spliceOdd δ - spliceOdd η‖_{W^m} ≲ (δ^(2-θ)+η^(2-θ)) ‖v‖_{W^{m+1}}`
  (K2 for the Coulomb cores and SL2 for the raw annular operators).
* `sa16y_spliceOdd_tendsto`: `spliceOdd δ i w_n x → spliceOdd δ i w x` for uniformly bounded, uniformly integrable
  `w_n → w`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv Phase2SA16

section T7Aux
variable {d : ℕ}

lemma sa16y_rawOdd_eq_oddCut (θ a : ℝ) (i : Fin d) (u : Euc d → ℝ) (x : Euc d) :
    rawOdd d θ a i u x = oddCut d θ a i u x := by
  unfold rawOdd oddCut
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (z i / ‖z‖ ^ ((d : ℝ) + θ)) * u (x - z) = ((‖z‖⁻¹ • z) i / ‖z‖ ^ ((d : ℝ) + θ - 1)) * u (x - z)
  rw [sa16s_kernel_eq]
  rfl

lemma sa16y_wNormE_sub_le (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (f g : Euc d → ℝ) :
    wNormE m p (fun x => f x - g x) ≤ wNormE m p f + wNormE m p g := by
  have h1 := sa16y_wNormE_add_le (d := d) m p f (fun x => (-1 : ℝ) * g x)
  have h2 := sa16y_wNormE_smul_le (d := d) m p (-1) g
  simp only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul] at h2
  have : (fun x => f x - g x) = fun x => f x + (-1 : ℝ) * g x := by funext x; ring
  rw [this]
  exact h1.trans (add_le_add le_rfl h2)

/-- the splice operator on a continuous bounded integrable function: core plus raw part -/
lemma sa16y_splice_repr {θ δ : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) (hθ : 0 < θ) (i : Fin d)
    {w : Euc d → ℝ} (hwc : Continuous w) {B : ℝ} (hB : ∀ y, |w y| ≤ B) (hwi : Integrable w) (x : Euc d) :
    spliceOdd d θ δ i w x = (∫ z, sa16k2_k d θ δ i z * w (x - z)) + oddCut d θ δ i w x := by
  have hint2 : Integrable (fun z => sa16k2_k d θ δ i z * w (x - z)) := by
    refine Integrable.mono' ((sa16k2_k_int (θ := θ) hd hδ i).norm.mul_const B)
      ((sa16k2_k_meas θ δ i).aestronglyMeasurable.mul
        (hwc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).le.trans (hB _)) (norm_nonneg _)
  have hint1 : Integrable (fun z => sa16s_kr d θ δ i z * w (x - z)) := by
    refine Integrable.mono' ((hwi.comp_sub_left x).norm.const_mul (δ ^ (1 - ((d : ℝ) + θ))))
      ((sa16s_kr_meas θ δ i).aestronglyMeasurable.mul
        (hwc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (sa16s_kr_abs_le hd hδ hθ i z) (norm_nonneg _)
  have hspl : spliceOdd d θ δ i w x = ∫ z, (sa16k2_k d θ δ i z * w (x - z) +
      sa16s_kr d θ δ i z * w (x - z)) := by
    unfold spliceOdd
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16k2_k]
    ring
  rw [hspl, integral_add hint2 hint1, sa16y_oddCut_eq']

/-- dominated convergence against an integrable kernel and uniformly bounded functions -/
lemma sa16y_dct_int {κ : Euc d → ℝ} (hκ : Integrable κ) {Bw : ℝ} {w : ℕ → Euc d → ℝ}
    (hwc : ∀ n, Continuous (w n)) {w' : Euc d → ℝ} (hwb : ∀ n y, |w n y| ≤ Bw)
    (hwl : ∀ y, Tendsto (fun n => w n y) atTop (𝓝 (w' y))) (x : Euc d) :
    Tendsto (fun n => ∫ z, κ z * w n (x - z)) atTop (𝓝 (∫ z, κ z * w' (x - z))) := by
  refine tendsto_integral_of_dominated_convergence (fun z => ‖κ z‖ * Bw) (fun n => ?_)
    (hκ.norm.mul_const Bw) (fun n => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · exact hκ.aestronglyMeasurable.mul
      ((hwc n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).le.trans (hwb n _)) (norm_nonneg _)
  · exact (hwl (x - z)).const_mul (κ z)

lemma sa16y_spliceOdd_tendsto (hd : 1 ≤ d) {θ δ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) (i : Fin d)
    {w : ℕ → Euc d → ℝ} (hwc : ∀ n, Continuous (w n)) {w' : Euc d → ℝ} (hwc' : Continuous w')
    {Bw : ℝ} (hwb : ∀ n y, |w n y| ≤ Bw) (hwi : ∀ n, Integrable (w n))
    {H : Euc d → ℝ} (hH : Integrable H) (hwH : ∀ n y, |w n y| ≤ H y)
    (hwl : ∀ y, Tendsto (fun n => w n y) atTop (𝓝 (w' y))) (x : Euc d) :
    Tendsto (fun n => spliceOdd d θ δ i (w n) x) atTop (𝓝 (spliceOdd d θ δ i w' x)) := by
  have hwb' : ∀ y, |w' y| ≤ Bw := fun y => le_of_tendsto' (hwl y).abs (fun n => hwb n y)
  have hwi' : Integrable w' := by
    refine Integrable.mono' hH hwc'.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact le_of_tendsto' (hwl y).abs (fun n => hwH n y)
  simp_rw [sa16y_splice_repr hd hδ hθ i (hwc _) (hwb _) (hwi _) x]
  rw [sa16y_splice_repr hd hδ hθ i hwc' hwb' hwi' x]
  refine Tendsto.add (sa16y_dct_int (sa16k2_k_int (θ := θ) hd hδ i) hwc hwb hwl x) ?_
  simp_rw [sa16y_oddCut_eq']
  exact sa16y_dct_conv (sa16s_kr_meas θ δ i) (Kb := δ ^ (1 - ((d : ℝ) + θ)))
    (fun z => sa16s_kr_abs_le hd hδ hθ i z) hH hwc hwH hwl x

theorem sa16y_spliceOdd_diff_bound (d : ℕ) (hd : 1 ≤ d) (m : ℕ) (θ p : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    [Fact (2 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ δ η : ℝ, δ ∈ Ioc (0 : ℝ) 1 → η ∈ Ioc (0 : ℝ) 1 → ∀ (i : Fin d) (v : 𝓢(Euc d, ℝ)),
      wNormE m p (fun x => spliceOdd d θ δ i v x - spliceOdd d θ η i v x) ≤
        ENNReal.ofReal (C * (δ ^ (2 - θ) + η ^ (2 - θ))) * wNormE (m + 1) p (⇑v) := by
  obtain ⟨CK, hCK, hK⟩ := splice_correction_bound d m hd θ p hθ0 hθ2
  obtain ⟨C2, hC2, h2⟩ := oddCut_difference_bound d hd m θ p hθ0 hθ2
  refine ⟨CK + C2, by positivity, fun δ η hδ hη i v => ?_⟩
  have hfun : (fun x => spliceOdd d θ δ i v x - spliceOdd d θ η i v x) =
      fun x => ((spliceOdd d θ δ i v x - rawOdd d θ δ i v x) +
        (oddCut d θ δ i v x - oddCut d θ η i v x)) -
        (spliceOdd d θ η i v x - rawOdd d θ η i v x) := by
    funext x
    rw [sa16y_rawOdd_eq_oddCut, sa16y_rawOdd_eq_oddCut]
    ring
  rw [hfun]
  set W : ℝ≥0∞ := wNormE (m + 1) p (⇑v) with hW
  refine (sa16y_wNormE_sub_le m p _ _).trans ?_
  refine (add_le_add (sa16y_wNormE_add_le m p _ _) le_rfl).trans ?_
  have e1 := hK δ hδ i v
  have e2 := h2 δ η hδ hη i v
  have e3 := hK η hη i v
  have hδ0 : 0 ≤ δ ^ (2 - θ) := Real.rpow_nonneg hδ.1.le _
  have hη0 : 0 ≤ η ^ (2 - θ) := Real.rpow_nonneg hη.1.le _
  calc _ ≤ (ENNReal.ofReal (CK * δ ^ (2 - θ)) * W + ENNReal.ofReal (C2 * (δ ^ (2 - θ) + η ^ (2 - θ))) * W) +
        ENNReal.ofReal (CK * η ^ (2 - θ)) * W := add_le_add (add_le_add e1 e2) e3
    _ = ENNReal.ofReal (CK * δ ^ (2 - θ) + C2 * (δ ^ (2 - θ) + η ^ (2 - θ)) + CK * η ^ (2 - θ)) * W := by
        rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((CK + C2) * (δ ^ (2 - θ) + η ^ (2 - θ))) * W := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        nlinarith [mul_nonneg hCK.le hδ0, mul_nonneg hCK.le hη0, mul_nonneg hC2.le hδ0, mul_nonneg hC2.le hη0]

lemma sa16y_splice_int {θ δ : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) (hθ : 0 < θ) (i : Fin d)
    {w : Euc d → ℝ} (hwc : Continuous w) {B : ℝ} (hB : ∀ y, |w y| ≤ B) (hwi : Integrable w)
    (x : Euc d) : Integrable (fun z => spliceKernel d θ δ i z * w (x - z)) := by
  have hint2 : Integrable (fun z => sa16k2_k d θ δ i z * w (x - z)) := by
    refine Integrable.mono' ((sa16k2_k_int (θ := θ) hd hδ i).norm.mul_const B)
      ((sa16k2_k_meas θ δ i).aestronglyMeasurable.mul
        (hwc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).le.trans (hB _)) (norm_nonneg _)
  have hint1 : Integrable (fun z => sa16s_kr d θ δ i z * w (x - z)) := by
    refine Integrable.mono' ((hwi.comp_sub_left x).norm.const_mul (δ ^ (1 - ((d : ℝ) + θ))))
      ((sa16s_kr_meas θ δ i).aestronglyMeasurable.mul
        (hwc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (sa16s_kr_abs_le hd hδ hθ i z) (norm_nonneg _)
  refine (hint2.add hint1).congr (Eventually.of_forall fun z => ?_)
  show (sa16k2_k d θ δ i z * w (x - z) + sa16s_kr d θ δ i z * w (x - z)) = _
  simp only [sa16k2_k]
  ring

lemma sa16y_spliceOdd_sub {θ δ : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) (hθ : 0 < θ) (i : Fin d)
    (v w : 𝓢(Euc d, ℝ)) (x : Euc d) :
    spliceOdd d θ δ i (fun y => v y - w y) x = spliceOdd d θ δ i (⇑v) x - spliceOdd d θ δ i (⇑w) x := by
  obtain ⟨B1, hB1⟩ := sa16j_schwartz_bdd v
  obtain ⟨B2, hB2⟩ := sa16j_schwartz_bdd w
  unfold spliceOdd
  rw [← integral_sub (sa16y_splice_int hd hδ hθ i v.continuous hB1 v.integrable x)
    (sa16y_splice_int hd hδ hθ i w.continuous hB2 w.integrable x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  ring

end T7Aux

end HRS.Whole.AppendixA.Phase2SA16Cutoff
