import HRS.MS.SuppU2Aux13

/-!
# UL-T (S5.1 convolution tails), part 1: the cancellation operator `ultK` and its derivatives

Infrastructure packet UL-T (supplement `W:r2:convolution-tail`, S L3300-3320); not a manuscript row.
Notation: `κ` is a scalar component of the force `∇g` (`u2_kap d s i`), `a = s + 1`, `0 ≤ s < d`.

The cancellation convolution of `HRS.Whole.convGradConvW` is, componentwise (change of variable
`y = x - z`),
`ultK κ h x = ∫ κ(z) (h(x - z) - 1_{|z| ≤ 1/4} h(x)) dz = ultNear κ h x + u2Conv (ultKF κ) h x`
with the near part `∫ 1_{|z| ≤ 1/4} κ(z) (h(x - z) - h(x)) dz` (integrable because
`|κ(z)||z| ≲ |z|^{-s}`, `s < d`) and the bounded far kernel `ultKF κ = 1_{|z| > 1/4} κ`.

Main results of this file (all for `h` with the weighted decay predicate `U2Dec` of `SuppU2Aux4`):
* `ult_K_integrable`: both parts are integrable (no Bochner junk);
* `ult_K_iter`: `D^m (ultK κ h) = ultK κ (D^m h)` for `m ≤ k` and `ultK κ h` is `C^k`
  (`U2Dec (k+1)` is used for the two extra derivatives needed to differentiate the near part);
* `ult_K_clm`: `ultK` commutes with continuous linear maps.

Helper lemmas carry the prefix `ult_`; namespace `HRS.MS.Ul`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.Ul

open HRS HRS.Whole

variable {d : ℕ}

/-- Kernel hypotheses: a measurable function, smooth off the origin, `‖D^j κ(z)‖ ≤ C_j |z|^{-(s+1)-j}`. -/
structure UlKer (κ : Euc d → ℝ) (s : ℝ) : Prop where
  meas : Measurable κ
  hs0 : 0 ≤ s
  hsd : s < (d : ℝ)
  hsm : ∀ z : Euc d, z ≠ 0 → ContDiffAt ℝ ∞ κ z
  hD : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : Euc d, z ≠ 0 → ‖iteratedFDeriv ℝ j κ z‖ ≤ C * ‖z‖ ^ (-(s + 1) - j)

/-- The components of `∇g` satisfy the kernel hypotheses for every `0 ≤ s < d`. -/
lemma ult_ker_kap {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (i : Fin d) :
    UlKer (u2_kap d s i) s :=
  ⟨u2_kap_measurable s i, hs0, hsd, fun z hz => u2_kap_contDiffAt s i hz,
    fun j => u2_iter_bound (u2_kap d s i) (s + 1) (fun z hz => u2_kap_contDiffAt s i hz)
      (fun t ht z hz => u2_kap_hom s i ht hz) j⟩

lemma ult_ker_bound {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Euc d, z ≠ 0 → ‖κ z‖ ≤ C * ‖z‖ ^ (-(s + 1)) := by
  obtain ⟨C, hC, hb⟩ := hK.hD 0
  refine ⟨C, hC, fun z hz => ?_⟩
  have := hb z hz
  simpa using this

/-- Near and far parts of the kernel (cutoff at `|z| = 1/4`, the convention of `convGradConvW`). -/
def ultKN (κ : Euc d → ℝ) (z : Euc d) : ℝ := if ‖z‖ ≤ 1 / 4 then κ z else 0

def ultKF (κ : Euc d → ℝ) (z : Euc d) : ℝ := if ‖z‖ ≤ 1 / 4 then 0 else κ z

lemma ultKN_meas {κ : Euc d → ℝ} (hκ : Measurable κ) : Measurable (ultKN κ) :=
  Measurable.ite (measurableSet_le measurable_norm measurable_const) hκ measurable_const

lemma ultKF_meas {κ : Euc d → ℝ} (hκ : Measurable κ) : Measurable (ultKF κ) :=
  Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_const hκ

lemma ult_ball_int (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (ball (0 : Euc d) 1) volume := by
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    simp only [neg_zero, Real.rpow_zero]
    exact integrableOn_const (measure_ball_lt_top).ne
  · exact u2_integrableOn_ball_rpow hd h0 hsd

/-- The pointwise bound of the near kernel times `|z|`. -/
lemma ult_near_pt {κ : Euc d → ℝ} {s C0 : ℝ} (hC0 : 0 ≤ C0)
    (hb : ∀ z : Euc d, z ≠ 0 → ‖κ z‖ ≤ C0 * ‖z‖ ^ (-(s + 1))) (z : Euc d) (hz : z ≠ 0) :
    ‖ultKN κ z‖ * ‖z‖ ≤ (ball (0 : Euc d) 1).indicator (fun z => C0 * ‖z‖ ^ (-s)) z := by
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases h : ‖z‖ ≤ 1 / 4
  · have hmem : z ∈ ball (0 : Euc d) 1 := by
      rw [mem_ball_zero_iff]; linarith
    rw [Set.indicator_of_mem hmem]
    simp only [ultKN, if_pos h]
    calc ‖κ z‖ * ‖z‖ ≤ C0 * ‖z‖ ^ (-(s + 1)) * ‖z‖ := mul_le_mul_of_nonneg_right (hb z hz) hzp.le
      _ = C0 * ‖z‖ ^ (-s) := by
          rw [mul_assoc, ← Real.rpow_add_one hzp.ne']
          congr 2; ring
  · simp only [ultKN, if_neg h, norm_zero, zero_mul]
    exact Set.indicator_nonneg (fun z _ => mul_nonneg hC0 (Real.rpow_nonneg (norm_nonneg z) _)) z

/-- The far kernel is bounded. -/
lemma ult_far_bound {κ : Euc d → ℝ} {s C0 : ℝ} (hC0 : 0 ≤ C0)
    (hb : ∀ z : Euc d, z ≠ 0 → ‖κ z‖ ≤ C0 * ‖z‖ ^ (-(s + 1))) (hs0 : 0 ≤ s) (z : Euc d) :
    ‖ultKF κ z‖ ≤ C0 * (1 / 4 : ℝ) ^ (-(s + 1)) := by
  by_cases h : ‖z‖ ≤ 1 / 4
  · simp only [ultKF, if_pos h, norm_zero]
    positivity
  · push Not at h
    simp only [ultKF, if_neg (not_le.mpr h)]
    have hz : z ≠ 0 := norm_pos_iff.mp (by linarith)
    refine (hb z hz).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) h.le (by linarith)

lemma ult_far_U2Ker (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) : U2Ker (ultKF κ) 0 := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  refine ⟨ultKF_meas hK.meas, le_rfl, ⟨C0 * (1 / 4 : ℝ) ^ (-(s + 1)), by positivity, fun z _ => ?_⟩,
    hd, ?_⟩
  · simpa using ult_far_bound hC0 hb hK.hs0 z
  · simp only [neg_zero, Real.rpow_zero]
    exact integrableOn_const (measure_ball_lt_top).ne

section Near

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The near part of the cancellation convolution. -/
def ultNear (κ : Euc d → ℝ) (g : Euc d → F) (x : Euc d) : F :=
  ∫ z, ultKN κ z • (g (x - z) - g x)

lemma ult_lip_of_fderiv {g : Euc d → F} (hg : Differentiable ℝ g) {B : ℝ}
    (hB : ∀ y, ‖fderiv ℝ g y‖ ≤ B) (a b : Euc d) : ‖g a - g b‖ ≤ B * ‖a - b‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := g) (s := Set.univ) (x := b) (y := a)
    (fun y _ => hg y) (fun y _ => hB y) convex_univ (Set.mem_univ _) (Set.mem_univ _)

lemma ult_near_dom {κ : Euc d → ℝ} {s C0 : ℝ} (hC0 : 0 ≤ C0)
    (hb : ∀ z : Euc d, z ≠ 0 → ‖κ z‖ ≤ C0 * ‖z‖ ^ (-(s + 1))) {B : ℝ} (hB : 0 ≤ B)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {w : G}
    {z : Euc d} (hz : z ≠ 0) (hw : ‖w‖ ≤ B * ‖z‖) :
    ‖ultKN κ z • w‖ ≤ C0 * B * (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) z := by
  have h1 := ult_near_pt hC0 hb z hz
  have h3 : (ball (0 : Euc d) 1).indicator (fun z => C0 * ‖z‖ ^ (-s)) z =
      C0 * (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) z := by
    by_cases hz1 : z ∈ ball (0 : Euc d) 1
    · simp [Set.indicator_of_mem hz1]
    · simp [Set.indicator_of_notMem hz1]
  rw [norm_smul]
  calc ‖ultKN κ z‖ * ‖w‖ ≤ ‖ultKN κ z‖ * (B * ‖z‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = B * (‖ultKN κ z‖ * ‖z‖) := by ring
    _ ≤ B * (C0 * (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) z) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h1 hB
    _ = C0 * B * (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) z := by ring

lemma ult_Phi_int (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) :
    Integrable ((ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-s))) volume :=
  (integrable_indicator_iff measurableSet_ball).2 (ult_ball_int hd hK.hs0 hK.hsd)

lemma ult_near_meas {κ : Euc d → ℝ} (hκ : Measurable κ) {g : Euc d → F} (hg : Continuous g)
    (x : Euc d) : AEStronglyMeasurable (fun z => ultKN κ z • (g (x - z) - g x)) volume :=
  (ultKN_meas hκ).aestronglyMeasurable.smul
    ((hg.comp (continuous_const.sub continuous_id)).sub continuous_const).aestronglyMeasurable

lemma ult_near_integrable (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {g : Euc d → F}
    (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B) (hLip : ∀ a b, ‖g a - g b‖ ≤ B * ‖a - b‖)
    (x : Euc d) : Integrable (fun z => ultKN κ z • (g (x - z) - g x)) volume := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  refine ((ult_Phi_int hd hK).const_mul (C0 * B)).mono' (ult_near_meas hK.meas hg x) ?_
  filter_upwards [u2_ae_ne_zero hd] with z hz
  refine ult_near_dom hC0 hb hB hz ?_
  have := hLip (x - z) x
  simpa using this

lemma ult_near_continuous (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {g : Euc d → F}
    (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B) (hLip : ∀ a b, ‖g a - g b‖ ≤ B * ‖a - b‖) :
    Continuous (ultNear κ g) := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  refine continuous_iff_continuousAt.2 fun x0 => ?_
  refine MeasureTheory.continuousAt_of_dominated (μ := volume)
    (F := fun x z => ultKN κ z • (g (x - z) - g x))
    (bound := fun z => C0 * B * (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) z)
    (Filter.Eventually.of_forall fun x => ult_near_meas hK.meas hg x) ?_
    ((ult_Phi_int hd hK).const_mul (C0 * B)) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    filter_upwards [u2_ae_ne_zero hd] with z hz
    refine ult_near_dom hC0 hb hB hz ?_
    have := hLip (x - z) x
    simpa using this
  · refine Filter.Eventually.of_forall fun z => ?_
    refine (continuous_const.smul ?_).continuousAt
    exact (hg.comp (continuous_id.sub continuous_const)).sub hg

lemma ult_near_hasFDerivAt [CompleteSpace F] (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s)
    {g : Euc d → F} (hg : Differentiable ℝ g) {B1 B2 : ℝ} (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ B1)
    (h2 : ∀ a b, ‖fderiv ℝ g a - fderiv ℝ g b‖ ≤ B2 * ‖a - b‖) (x0 : Euc d) :
    HasFDerivAt (ultNear κ g) (ultNear κ (fun y => fderiv ℝ g y) x0) x0 := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  have hgc : Continuous g := hg.continuous
  have hLip := ult_lip_of_fderiv hg h1
  have hfc : Continuous (fderiv ℝ g) :=
    (LipschitzWith.of_dist_le_mul (K := ⟨B2, hB2⟩) fun a b => by
      rw [dist_eq_norm, dist_eq_norm]; exact h2 a b).continuous
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x z => ultKN κ z • (g (x - z) - g x))
    (F' := fun x z => ultKN κ z • (fderiv ℝ g (x - z) - fderiv ℝ g x))
    (x₀ := x0) (s := ball x0 1)
    (bound := fun z => C0 * B2 * (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) z)
    (ball_mem_nhds x0 one_pos) ?_ ?_ ?_ ?_ ((ult_Phi_int hd hK).const_mul (C0 * B2)) ?_
  · exact Filter.Eventually.of_forall fun x => ult_near_meas hK.meas hgc x
  · exact ult_near_integrable hd hK hgc hB1 hLip x0
  · exact ult_near_meas hK.meas hfc x0
  · filter_upwards [u2_ae_ne_zero hd] with z hz x _
    refine ult_near_dom (G := Euc d →L[ℝ] F) hC0 hb hB2 hz ?_
    have := h2 (x - z) x
    simpa using this
  · refine Filter.Eventually.of_forall fun z x _ => ?_
    have h1' : HasFDerivAt (fun x : Euc d => g (x - z)) (fderiv ℝ g (x - z)) x := by
      have h2' : HasFDerivAt (fun x : Euc d => x - z) (ContinuousLinearMap.id ℝ (Euc d)) x :=
        (hasFDerivAt_id x).sub_const z
      have := HasFDerivAt.comp x (hg (x - z)).hasFDerivAt h2'
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    exact (h1'.sub (hg x).hasFDerivAt).const_smul (ultKN κ z)

lemma ult_near_clm [CompleteSpace F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F']
    (φ : F →L[ℝ] F') (κ : Euc d → ℝ) (g : Euc d → F) (x : Euc d)
    (hint : Integrable (fun z => ultKN κ z • (g (x - z) - g x)) volume) :
    φ (ultNear κ g x) = ultNear κ (fun y => φ (g y)) x := by
  unfold ultNear
  rw [← ContinuousLinearMap.integral_comp_comm φ hint]
  simp [map_smul, map_sub]

end Near

section Iter

lemma ult_iter_bounds {L A : ℝ} (hL0 : 0 ≤ L) (hA : 0 ≤ A) {k : ℕ} {h : Euc d → ℝ}
    (hdec : U2Dec (k + 1) L A h) : ∀ m ≤ k + 1, ∀ y, ‖iteratedFDeriv ℝ m h y‖ ≤ A := by
  intro m hm y
  refine (hdec.2 m hm y).trans ?_
  have := u2Wt_le_one (d := d) hL0 y
  nlinarith

lemma ult_iter_contDiff1 {L A : ℝ} {k : ℕ} {h : Euc d → ℝ} (hdec : U2Dec (k + 1) L A h) {m : ℕ}
    (hm : m + 1 ≤ k + 1) : ContDiff ℝ 1 (iteratedFDeriv ℝ m h) := by
  have := hdec.1.iteratedFDeriv_right (m := 1) (i := m) (by
    have : ((1 : ℕ) + m : ℕ) ≤ k + 1 := by omega
    exact_mod_cast this)
  exact this

lemma ult_iter_lip {L A : ℝ} (hL0 : 0 ≤ L) (hA : 0 ≤ A) {k : ℕ} {h : Euc d → ℝ}
    (hdec : U2Dec (k + 1) L A h) {m : ℕ} (hm : m + 1 ≤ k + 1) (a b : Euc d) :
    ‖iteratedFDeriv ℝ m h a - iteratedFDeriv ℝ m h b‖ ≤ A * ‖a - b‖ := by
  refine ult_lip_of_fderiv ((ult_iter_contDiff1 hdec hm).differentiable one_ne_zero)
    (fun y => ?_) a b
  rw [u2_norm_fderiv_iteratedFDeriv]
  exact ult_iter_bounds hL0 hA hdec (m + 1) hm y

lemma ult_lip0 {L A : ℝ} (hL0 : 0 ≤ L) (hA : 0 ≤ A) {k : ℕ} {h : Euc d → ℝ}
    (hdec : U2Dec (k + 1) L A h) (a b : Euc d) : ‖h a - h b‖ ≤ A * ‖a - b‖ := by
  have := ult_iter_lip hL0 hA hdec (m := 0) (by omega) a b
  rw [iteratedFDeriv_zero_eq_comp] at this
  simpa only [Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map] using this

lemma ult_iter_lip2 {L A : ℝ} (hL0 : 0 ≤ L) (hA : 0 ≤ A) {k : ℕ} {h : Euc d → ℝ}
    (hdec : U2Dec (k + 1) L A h) {m : ℕ} (hm : m + 2 ≤ k + 1) (a b : Euc d) :
    ‖fderiv ℝ (iteratedFDeriv ℝ m h) a - fderiv ℝ (iteratedFDeriv ℝ m h) b‖ ≤ A * ‖a - b‖ := by
  have h1 := ult_iter_lip hL0 hA hdec (m := m + 1) hm a b
  have e : ∀ y, fderiv ℝ (iteratedFDeriv ℝ m h) y =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Euc d) ℝ
        (iteratedFDeriv ℝ (m + 1) h y) := fun y => by
    rw [fderiv_iteratedFDeriv]; rfl
  have h2 := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Euc d) ℝ).norm_map
    (iteratedFDeriv ℝ (m + 1) h a - iteratedFDeriv ℝ (m + 1) h b)
  rw [LinearIsometryEquiv.map_sub] at h2
  rw [e a, e b, h2]
  exact h1

lemma ult_near_G_hasFDerivAt (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L A : ℝ}
    (hL0 : 0 ≤ L) (hA : 0 ≤ A) {k : ℕ} {h : Euc d → ℝ} (hdec : U2Dec (k + 1) L A h) {m : ℕ}
    (hm : m + 1 ≤ k) (x : Euc d) :
    HasFDerivAt (ultNear κ (iteratedFDeriv ℝ m h))
      (ultNear κ (fun y => fderiv ℝ (iteratedFDeriv ℝ m h) y) x) x := by
  have : CompleteSpace (Euc d [×m]→L[ℝ] ℝ) := inferInstance
  refine ult_near_hasFDerivAt hd hK
    ((ult_iter_contDiff1 hdec (m := m) (by omega)).differentiable one_ne_zero) hA hA (fun y => ?_)
    (ult_iter_lip2 hL0 hA hdec (by omega)) x
  rw [u2_norm_fderiv_iteratedFDeriv]
  exact ult_iter_bounds hL0 hA hdec (m + 1) (by omega) y

theorem ult_near_iter (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L A : ℝ}
    (hL0 : 0 ≤ L) (hA : 0 ≤ A) {k : ℕ} {h : Euc d → ℝ} (hdec : U2Dec (k + 1) L A h) :
    (∀ m ≤ k, ∀ x, iteratedFDeriv ℝ m (ultNear κ h) x = ultNear κ (iteratedFDeriv ℝ m h) x) ∧
      ContDiff ℝ k (ultNear κ h) := by
  have hcm : ∀ m ≤ k + 1, Continuous (iteratedFDeriv ℝ m h) := fun m hm =>
    hdec.1.continuous_iteratedFDeriv (by exact_mod_cast hm)
  have key : ∀ m ≤ k, ∀ x, iteratedFDeriv ℝ m (ultNear κ h) x =
      ultNear κ (iteratedFDeriv ℝ m h) x := by
    intro m
    induction m with
    | zero =>
      intro _ x
      have hint0 := ult_near_integrable hd hK hdec.1.continuous hA (ult_lip0 hL0 hA hdec) x
      have h0 := ult_near_clm
        ((continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)
        κ h x hint0
      rw [iteratedFDeriv_zero_eq_comp]
      exact h0
    | succ m ih =>
      intro hm x
      have hfun : iteratedFDeriv ℝ m (ultNear κ h) = ultNear κ (iteratedFDeriv ℝ m h) :=
        funext (ih (by omega))
      have hd' := ult_near_G_hasFDerivAt hd hK hL0 hA hdec hm x
      have : CompleteSpace (Euc d →L[ℝ] (Euc d [×m]→L[ℝ] ℝ)) := inferInstance
      have hint' := ult_near_integrable hd hK
        (((ult_iter_contDiff1 hdec (m := m) (by omega)).continuous_fderiv one_ne_zero)) hA
        (ult_iter_lip2 hL0 hA hdec (by omega)) x
      have h1 := ult_near_clm
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)
        κ (fun y => fderiv ℝ (iteratedFDeriv ℝ m h) y) x hint'
      rw [iteratedFDeriv_succ_eq_comp_left (f := ultNear κ h),
        iteratedFDeriv_succ_eq_comp_left (f := h)]
      simp only [Function.comp_apply]
      rw [hfun, hd'.fderiv]
      exact h1
  refine ⟨key, ?_⟩
  rw [contDiff_nat_iff_continuous_differentiable]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have hm' : m ≤ k := by exact_mod_cast hm
    have : (fun x => iteratedFDeriv ℝ m (ultNear κ h) x) = ultNear κ (iteratedFDeriv ℝ m h) :=
      funext (key m hm')
    rw [this]
    exact ult_near_continuous hd hK (hcm m (by omega)) hA (ult_iter_lip hL0 hA hdec (by omega))
  · have hm' : m + 1 ≤ k := by exact_mod_cast hm
    have : (fun x => iteratedFDeriv ℝ m (ultNear κ h) x) = ultNear κ (iteratedFDeriv ℝ m h) :=
      funext (key m (by omega))
    rw [this]
    exact fun x => (ult_near_G_hasFDerivAt hd hK hL0 hA hdec hm' x).differentiableAt

end Iter

section KOp

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The full cancellation operator `∫ κ(z) (g(x-z) - 1_{|z| ≤ 1/4} g(x)) dz`. -/
def ultK (κ : Euc d → ℝ) (g : Euc d → F) (x : Euc d) : F :=
  ultNear κ g x + u2Conv (ultKF κ) g x

end KOp

theorem ult_K_iter (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L A : ℝ}
    (hL : (d : ℝ) < L) (hA : 0 ≤ A) {k : ℕ} {h : Euc d → ℝ} (hdec : U2Dec (k + 1) L A h) :
    (∀ m ≤ k, ∀ x, iteratedFDeriv ℝ m (ultK κ h) x = ultK κ (iteratedFDeriv ℝ m h) x) ∧
      ContDiff ℝ k (ultK κ h) := by
  have hL0 := u2_wt_L0 hL
  have hdec' : U2Dec k L A h :=
    ⟨hdec.1.of_le (by exact_mod_cast Nat.le_succ k), fun m hm => hdec.2 m (by omega)⟩
  obtain ⟨hnf, hnc⟩ := ult_near_iter hd hK hL0 hA hdec
  obtain ⟨hff, hfc⟩ := u2_conv_iter (ult_far_U2Ker hd hK) hL hA hdec'
  refine ⟨fun m hm x => ?_, ?_⟩
  · have hsum : ultK κ h = ultNear κ h + u2Conv (ultKF κ) h := rfl
    have hmk : (m : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast hm
    rw [hsum]
    rw [iteratedFDeriv_add_apply ((hnc.of_le hmk).contDiffAt) ((hfc.of_le hmk).contDiffAt),
      hnf m hm x, hff m hm x]
    rfl
  · exact hnc.add hfc

lemma ult_K_integrable (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L A : ℝ}
    (hL : (d : ℝ) < L) (hA : 0 ≤ A) {h : Euc d → ℝ} (hdec : U2Dec 1 L A h) (x : Euc d) :
    Integrable (fun z => ultKN κ z • (h (x - z) - h x)) volume ∧
      Integrable (fun z => ultKF κ z • h (x - z)) volume := by
  have hL0 := u2_wt_L0 hL
  have hdec1 : U2Dec (0 + 1) L A h := hdec
  refine ⟨ult_near_integrable hd hK hdec.1.continuous hA (ult_lip0 hL0 hA hdec1) x, ?_⟩
  exact u2_conv_integrable (ult_far_U2Ker hd hK) hL hdec.1.continuous hA
    (fun y => by simpa using hdec.2 0 (Nat.zero_le _) y) x

lemma ult_K_clm {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (φ : F →L[ℝ] F') (κ : Euc d → ℝ) (g : Euc d → F) (x : Euc d)
    (hn : Integrable (fun z => ultKN κ z • (g (x - z) - g x)) volume)
    (hf : Integrable (fun z => ultKF κ z • g (x - z)) volume) :
    φ (ultK κ g x) = ultK κ (fun y => φ (g y)) x := by
  unfold ultK
  rw [map_add, ult_near_clm φ κ g x hn, u2_conv_clm φ (ultKF κ) g x hf]

end HRS.MS.Ul
