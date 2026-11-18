import HRS.MS.SA16StrongEven
import HRS.MS.SA16StrongWnorm
import HRS.MS.SA16StrongSL2

/-!
# S.A.16 SL1: `fracCut_difference_bound`

`fracCut δ u - fracCut η u = ∫ k(z) (u(x) - u(x-z)) dz` with the even kernel `k = kf δ - kf η`, supported in the
ball of radius `max δ η`, `|k z| ≤ |z|^(-d-θ)`.  The second-difference gain `sa16y_even_gain` applied to
`w = ∂^idx u` (the derivatives commute with `k ⋆`, `sa16j_conv_pd`) and the moment `sa16s_moment` give the bound.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv

section SL1
variable {d : ℕ}

/-- the even kernel `|z|^(-d-θ)` outside the ball of radius `a` -/
def sa16y_kf (d : ℕ) (θ a : ℝ) : Euc d → ℝ :=
  {z : Euc d | a < ‖z‖}.indicator (fun z => (‖z‖ ^ ((d : ℝ) + θ))⁻¹)

/-- the difference kernel -/
def sa16y_k (d : ℕ) (θ δ η : ℝ) : Euc d → ℝ := fun z => sa16y_kf d θ δ z - sa16y_kf d θ η z

lemma sa16y_kf_meas (θ a : ℝ) : Measurable (sa16y_kf d θ a) :=
  (measurable_norm.pow_const _).inv.indicator (measurableSet_lt measurable_const measurable_norm)

lemma sa16y_kf_neg (θ a : ℝ) (z : Euc d) : sa16y_kf d θ a (-z) = sa16y_kf d θ a z := by
  simp [sa16y_kf, Set.indicator]

lemma sa16y_kf_nonneg (θ a : ℝ) (z : Euc d) : 0 ≤ sa16y_kf d θ a z := by
  unfold sa16y_kf
  by_cases hz : z ∈ {z : Euc d | a < ‖z‖}
  · rw [Set.indicator_of_mem hz]; exact inv_nonneg.2 (Real.rpow_nonneg (norm_nonneg _) _)
  · rw [Set.indicator_of_notMem hz]

lemma sa16y_kf_zero {θ a : ℝ} (ha : 0 < a) : sa16y_kf d θ a 0 = 0 := by
  unfold sa16y_kf
  rw [Set.indicator_of_notMem]
  simpa using ha.le

lemma sa16y_kf_le {θ a : ℝ} (z : Euc d) : sa16y_kf d θ a z ≤ (‖z‖ ^ ((d : ℝ) + θ))⁻¹ := by
  unfold sa16y_kf
  by_cases hz : z ∈ {z : Euc d | a < ‖z‖}
  · rw [Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz]; exact inv_nonneg.2 (Real.rpow_nonneg (norm_nonneg _) _)

lemma sa16y_kf_int (hd : 1 ≤ d) {θ a : ℝ} (ha : 0 < a) (hθ : 0 < θ) :
    Integrable (sa16y_kf d θ a) := by
  have hr : (Module.finrank ℝ (Euc d) : ℝ) < (d : ℝ) + θ := by
    rw [finrank_euclideanSpace_fin]; linarith
  have h1 := integrable_one_add_norm (E := Euc d) (μ := volume) hr
  refine Integrable.mono' (h1.const_mul ((1 + a⁻¹) ^ ((d : ℝ) + θ)))
    (sa16y_kf_meas θ a).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (sa16y_kf_nonneg θ a z)]
  unfold sa16y_kf
  by_cases hz : z ∈ {z : Euc d | a < ‖z‖}
  · rw [Set.indicator_of_mem hz]
    have hz' : a < ‖z‖ := hz
    have hn : 0 < ‖z‖ := ha.trans hz'
    have hle : 1 + ‖z‖ ≤ (1 + a⁻¹) * ‖z‖ := by
      have : 1 ≤ a⁻¹ * ‖z‖ := by
        rw [← div_eq_inv_mul, le_div_iff₀ ha]; linarith
      nlinarith
    have hs : (0 : ℝ) ≤ (d : ℝ) + θ := by positivity
    have h2 : (1 + ‖z‖) ^ ((d : ℝ) + θ) ≤ ((1 + a⁻¹) * ‖z‖) ^ ((d : ℝ) + θ) :=
      Real.rpow_le_rpow (by positivity) hle hs
    rw [Real.mul_rpow (by positivity) hn.le] at h2
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀
      (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos (by positivity) _)]
    nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < 1 + ‖z‖ by positivity) ((d : ℝ) + θ)]
  · rw [Set.indicator_of_notMem hz]
    positivity

lemma sa16y_k_meas (θ δ η : ℝ) : Measurable (sa16y_k d θ δ η) :=
  (sa16y_kf_meas θ δ).sub (sa16y_kf_meas θ η)

lemma sa16y_k_neg (θ δ η : ℝ) (z : Euc d) : sa16y_k d θ δ η (-z) = sa16y_k d θ δ η z := by
  simp [sa16y_k, sa16y_kf_neg]

lemma sa16y_k_supp (θ δ η : ℝ) (z : Euc d) (hz : max δ η < ‖z‖) : sa16y_k d θ δ η z = 0 := by
  have h1 : z ∈ {z : Euc d | δ < ‖z‖} := lt_of_le_of_lt (le_max_left _ _) hz
  have h2 : z ∈ {z : Euc d | η < ‖z‖} := lt_of_le_of_lt (le_max_right _ _) hz
  simp [sa16y_k, sa16y_kf, Set.indicator_of_mem h1, Set.indicator_of_mem h2]

lemma sa16y_k_int (hd : 1 ≤ d) {θ δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) :
    Integrable (sa16y_k d θ δ η) :=
  (sa16y_kf_int hd hδ hθ).sub (sa16y_kf_int hd hη hθ)

lemma sa16y_k_abs_le (θ δ η : ℝ) (z : Euc d) :
    |sa16y_k d θ δ η z| ≤ (‖z‖ ^ ((d : ℝ) + θ))⁻¹ := by
  have h1 := sa16y_kf_nonneg (d := d) θ δ z
  have h2 := sa16y_kf_nonneg (d := d) θ η z
  have h3 := sa16y_kf_le (d := d) (θ := θ) (a := δ) z
  have h4 := sa16y_kf_le (d := d) (θ := θ) (a := η) z
  rw [abs_le]
  unfold sa16y_k
  constructor <;> linarith

lemma sa16y_k_moment_le {θ δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (z : Euc d) :
    |sa16y_k d θ δ η z| * ‖z‖ ^ 2 ≤ (closedBall (0 : Euc d) (max δ η)).indicator
      (fun z => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z := by
  by_cases hz : z ∈ closedBall (0 : Euc d) (max δ η)
  · rw [Set.indicator_of_mem hz]
    by_cases hz0 : ‖z‖ = 0
    · have : z = 0 := norm_eq_zero.1 hz0
      subst this
      have : sa16y_k d θ δ η 0 = 0 := by simp [sa16y_k, sa16y_kf_zero hδ, sa16y_kf_zero hη]
      rw [this]
      simp only [abs_zero, zero_mul, norm_zero]
      exact Real.rpow_nonneg le_rfl _
    · have hn : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
      calc |sa16y_k d θ δ η z| * ‖z‖ ^ 2 ≤ (‖z‖ ^ ((d : ℝ) + θ))⁻¹ * ‖z‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (sa16y_k_abs_le θ δ η z) (by positivity)
        _ = ‖z‖ ^ (2 - ((d : ℝ) + θ)) := by
            rw [Real.rpow_sub hn, Real.rpow_two, div_eq_mul_inv, mul_comm]
  · rw [Set.indicator_of_notMem hz, sa16y_k_supp θ δ η z (by simpa using hz)]
    simp

/-- the integral against a kernel of a difference -/
def sa16y_E (k w : Euc d → ℝ) : Euc d → ℝ := fun x => ∫ z, k z * (w x - w (x - z))

lemma sa16y_E_int {κ : Euc d → ℝ} (hκ : Integrable κ) {w : Euc d → ℝ} (hwc : Continuous w) {B : ℝ}
    (hwb : ∀ x, |w x| ≤ B) (x : Euc d) :
    Integrable (fun z => κ z * w (x - z)) := by
  refine Integrable.mono' (hκ.norm.mul_const B)
    (hκ.aestronglyMeasurable.mul (hwc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hwb _) (norm_nonneg _)

lemma sa16y_E_eq {k : Euc d → ℝ} (hk1 : Integrable k) {w : Euc d → ℝ} (hwc : Continuous w) {B : ℝ}
    (hwb : ∀ x, |w x| ≤ B) :
    sa16y_E k w = fun x => (∫ z, k z) * w x - sa16j_conv k w x := by
  funext x
  have : ∀ z, k z * (w x - w (x - z)) = k z * w x - k z * w (x - z) := fun z => by ring
  unfold sa16y_E sa16j_conv
  simp_rw [this]
  rw [integral_sub (hk1.mul_const _) (sa16y_E_int hk1 hwc hwb x), integral_mul_const]

lemma sa16y_fracCut_eq {θ a : ℝ} (u : Euc d → ℝ) (x : Euc d) :
    fracCut d θ a u x = ∫ z, sa16y_kf d θ a z * (u x - u (x - z)) := by
  have hS : MeasurableSet {z : Euc d | a < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  unfold fracCut sa16y_kf
  rw [← integral_indicator hS]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ {z : Euc d | a < ‖z‖}
  · simp only [Set.indicator_of_mem hz]; rw [div_eq_inv_mul]
  · simp only [Set.indicator_of_notMem hz]; simp

lemma sa16y_diff_eq (hd : 1 ≤ d) {θ δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ)
    (u : 𝓢(Euc d, ℝ)) :
    (fun x => fracCut d θ δ u x - fracCut d θ η u x) = sa16y_E (sa16y_k d θ δ η) (⇑u) := by
  obtain ⟨B, hB⟩ := sa16j_schwartz_bdd u
  funext x
  have hI : ∀ {a : ℝ}, 0 < a → Integrable (fun z => sa16y_kf d θ a z * (u x - u (x - z))) := by
    intro a ha
    have : ∀ z, sa16y_kf d θ a z * (u x - u (x - z)) =
        sa16y_kf d θ a z * u x - sa16y_kf d θ a z * u (x - z) := fun z => by ring
    simp_rw [this]
    exact ((sa16y_kf_int hd ha hθ).mul_const _).sub (sa16y_E_int (sa16y_kf_int hd ha hθ) u.continuous hB x)
  rw [sa16y_fracCut_eq, sa16y_fracCut_eq, ← integral_sub (hI hδ) (hI hη)]
  unfold sa16y_E sa16y_k
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  ring

/-- linearity of the coordinate derivative -/
lemma sa16y_pd_lin {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (c : ℝ) {j : ℕ}
    (idx : Fin j → Fin d) :
    partialDeriv idx (fun x => c * f x - g x) = fun x => c * partialDeriv idx f x - partialDeriv idx g x := by
  funext x
  have h : (fun x => c * f x - g x) = c • f - g := by funext y; simp
  unfold partialDeriv
  have hf' : ContDiffAt ℝ j f x := (hf.of_le (by exact_mod_cast le_top)).contDiffAt
  have hg' : ContDiffAt ℝ j g x := (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  have hcf : ContDiffAt ℝ j (c • f) x := hf'.const_smul c
  rw [h, iteratedFDeriv_sub_apply hcf hg', iteratedFDeriv_const_smul_apply hf']
  simp

lemma sa16y_E_smooth {k : Euc d → ℝ} {R : ℝ} (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hR : 0 ≤ R)
    (hk1 : Integrable k) (u : 𝓢(Euc d, ℝ)) : ContDiff ℝ ∞ (sa16y_E k (⇑u)) := by
  obtain ⟨B, hB⟩ := sa16j_schwartz_bdd u
  rw [sa16y_E_eq hk1 u.continuous hB]
  exact (contDiff_const.mul u.smooth').sub (sa16j_conv_contDiff hksupp hR hk1 u.smooth')

lemma sa16y_pd_E {k : Euc d → ℝ} {R : ℝ} (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hR : 0 ≤ R)
    (hk1 : Integrable k) (u : 𝓢(Euc d, ℝ)) {j : ℕ} (idx : Fin j → Fin d) :
    partialDeriv idx (sa16y_E k (⇑u)) = sa16y_E k (partialDeriv idx (⇑u)) := by
  obtain ⟨B, hB⟩ := sa16j_schwartz_bdd u
  have hu : ContDiff ℝ ∞ (⇑u) := u.smooth'
  have hw : partialDeriv idx (⇑u) = ⇑(LineDeriv.iteratedLineDerivOp
      (fun l => (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)) u) := sa16j_pd_schwartz u idx
  obtain ⟨B', hB'⟩ := sa16j_schwartz_bdd (LineDeriv.iteratedLineDerivOp
      (fun l => (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)) u)
  have hwc : Continuous (partialDeriv idx (⇑u)) := (sa16j_pd_smooth u.smooth' idx).continuous
  have hB'' : ∀ x, |partialDeriv idx (⇑u) x| ≤ B' := fun x => by rw [hw]; exact hB' x
  rw [sa16y_E_eq hk1 u.continuous hB, sa16y_E_eq hk1 hwc hB'',
    sa16y_pd_lin (f := ⇑u) (g := sa16j_conv k ⇑u) hu (sa16j_conv_contDiff hksupp hR hk1 hu) _ idx,
    sa16j_conv_pd hksupp hR hk1 j idx _ hu]

lemma sa16y_pd_cons {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) {j : ℕ} (a : Fin d) (idx : Fin j → Fin d)
    (y : Euc d) :
    partialDeriv (Fin.cons a idx : Fin (j + 1) → Fin d) g y =
      fderiv ℝ (partialDeriv idx g) y (EuclideanSpace.single a (1 : ℝ)) := by
  rw [sa16j_pd_succ hg]
  simp

lemma sa16y_pd2 {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) {j : ℕ} (r : Fin 2 → Fin d) (idx : Fin j → Fin d)
    (x : Euc d) :
    partialDeriv r (partialDeriv idx g) x =
      partialDeriv (Fin.cons (r 0) (Fin.cons (r 1) idx) : Fin (j + 2) → Fin d) g x := by
  have hh : ContDiff ℝ ∞ (partialDeriv idx g) := sa16j_pd_smooth hg idx
  have e1 : partialDeriv (fun l : Fin 1 => r l.succ) (partialDeriv idx g) =
      partialDeriv (Fin.cons (r 1) idx : Fin (j + 1) → Fin d) g := by
    funext y
    rw [sa16j_pd_succ hh (fun l : Fin 1 => r l.succ) y, sa16y_pd_cons hg]
    have : partialDeriv (fun l : Fin 0 => (fun l : Fin 1 => r l.succ) l.succ) (partialDeriv idx g) =
        partialDeriv idx g := by
      funext z; exact sa16j_pd_zero _ _ z
    rw [this]
    rfl
  rw [sa16j_pd_succ hh r x, e1, sa16y_pd_cons hg]

lemma sa16y_D2_le {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (m : ℕ) {j : ℕ} (hj : j ≤ m)
    (idx : Fin j → Fin d) (x : Euc d) :
    ‖iteratedFDeriv ℝ 2 (partialDeriv idx g) x‖ ≤ (d : ℝ) ^ 2 * ‖wJet (m + 2) g x‖ := by
  refine (sa16j_norm_iter_le (partialDeriv idx g) x 2).trans ?_
  have h1 : ∀ r : Fin 2 → Fin d, |partialDeriv r (partialDeriv idx g) x| ≤ ‖wJet (m + 2) g x‖ := by
    intro r
    rw [sa16y_pd2 hg r idx x]
    exact sa16j_pd_le_jet (m + 2) g x (by omega) _
  calc ∑ r : Fin 2 → Fin d, |partialDeriv r (partialDeriv idx g) x|
      ≤ ∑ r : Fin 2 → Fin d, ‖wJet (m + 2) g x‖ := Finset.sum_le_sum fun r _ => h1 r
    _ = (d : ℝ) ^ 2 * ‖wJet (m + 2) g x‖ := by
        simp [Finset.sum_const]

/-- the pointwise-in-`idx` bound for the second-difference operator -/
lemma sa16y_pd_even_bound (hd : 1 ≤ d) (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {k : Euc d → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hk : Measurable k) (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hk1 : Integrable k)
    (hkm : Integrable (fun z => |k z| * ‖z‖ ^ 2)) (heven : ∀ z, k (-z) = k z) (u : 𝓢(Euc d, ℝ))
    {j : ℕ} (hj : j ≤ m) (idx : Fin j → Fin d) :
    eLpNorm (partialDeriv idx (sa16y_E k (⇑u))) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (2 * (∫ z, |k z| * ‖z‖ ^ 2) * (d : ℝ) ^ 2) *
        eLpNorm (wJet (m + 2) (⇑u)) (ENNReal.ofReal p) volume := by
  have hp1 : 1 ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have hu : ContDiff ℝ ∞ (⇑u) := u.smooth'
  have hw : ContDiff ℝ ∞ (partialDeriv idx (⇑u)) := sa16j_pd_smooth hu idx
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x, |partialDeriv idx (⇑u) x| ≤ B := by
    rw [sa16j_pd_schwartz u idx]
    exact sa16j_schwartz_bdd _
  rw [sa16y_pd_E hksupp hR hk1 u idx]
  have hgain := sa16y_even_gain hp1 hk hk1 hkm heven (hw.of_le (by norm_num)) hB
  refine hgain.trans ?_
  have hdp : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  have hM0 : 0 ≤ ∫ z, |k z| * ‖z‖ ^ 2 := integral_nonneg fun z => by positivity
  have hmeas : AEStronglyMeasurable (fun x => ‖iteratedFDeriv ℝ 2 (partialDeriv idx (⇑u)) x‖) volume :=
    ((hw.continuous_iteratedFDeriv (m := 2) (by simp)).norm).aestronglyMeasurable
  have hle : eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 (partialDeriv idx (⇑u)) x‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((d : ℝ) ^ 2) * eLpNorm (wJet (m + 2) (⇑u)) (ENNReal.ofReal p) volume := by
    refine (eLpNorm_mono_ae_real hmeas (Eventually.of_forall fun x => (norm_norm _).le.trans
      (sa16y_D2_le hu m hj idx x))).trans ?_
    have : (fun x => (d : ℝ) ^ 2 * ‖wJet (m + 2) (⇑u) x‖) =
        (d : ℝ) ^ 2 • (fun x => ‖wJet (m + 2) (⇑u) x‖) := by
      funext x; simp
    rw [this, eLpNorm_const_smul, eLpNorm_norm _ (sa16j_jet_cont hu (m + 2)).aestronglyMeasurable]
    refine le_of_eq ?_
    rw [Real.enorm_eq_ofReal hdp]
  calc ENNReal.ofReal (2 * ∫ z, |k z| * ‖z‖ ^ 2) *
        eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 (partialDeriv idx (⇑u)) x‖) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (2 * ∫ z, |k z| * ‖z‖ ^ 2) *
          (ENNReal.ofReal ((d : ℝ) ^ 2) * eLpNorm (wJet (m + 2) (⇑u)) (ENNReal.ofReal p) volume) :=
        mul_le_mul' le_rfl hle
    _ = ENNReal.ofReal (2 * (∫ z, |k z| * ‖z‖ ^ 2) * (d : ℝ) ^ 2) *
          eLpNorm (wJet (m + 2) (⇑u)) (ENNReal.ofReal p) volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

theorem fracCut_difference_bound (d : ℕ) (hd : 1 ≤ d) (m : ℕ)
    (θ p : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) [Fact (2 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ δ η : ℝ, δ ∈ Ioc (0 : ℝ) 1 →
      η ∈ Ioc (0 : ℝ) 1 → ∀ u : SchwartzMap (Euc d) ℝ,
      wNormE m p (fun x => fracCut d θ δ u x-fracCut d θ η u x) ≤
        ENNReal.ofReal (C*(δ^(2-θ)+η^(2-θ))) * wNormE (m+2) p u := by
  obtain ⟨I₀, hI₀, hmom⟩ := sa16s_moment (d := d) hd hθ2
  set N : ℝ := (Fintype.card (WIndex d m) : ℝ) * (2 * (d : ℝ) ^ 2) with hN
  have hN0 : 0 ≤ N := by positivity
  refine ⟨N * I₀ + 1, by positivity, fun δ η hδ hη u => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hη0 : 0 < η := hη.1
  set R : ℝ := max δ η with hR
  have hR0 : 0 < R := lt_max_of_lt_left hδ0
  rw [sa16y_diff_eq hd hδ0 hη0 hθ0 u]
  obtain ⟨hBint, hBval⟩ := hmom R hR0
  have hkm : Integrable (fun z => |sa16y_k d θ δ η z| * ‖z‖ ^ 2) := by
    refine Integrable.mono' hBint ?_ (Eventually.of_forall fun z => ?_)
    · exact ((sa16y_k_meas θ δ η).abs.mul (measurable_norm.pow_const _)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact sa16y_k_moment_le hδ0 hη0 z
  have hMk : ∫ z, |sa16y_k d θ δ η z| * ‖z‖ ^ 2 ≤ R ^ (2 - θ) * I₀ := by
    rw [← hBval]
    exact integral_mono hkm hBint (fun z => sa16y_k_moment_le hδ0 hη0 z)
  have hM0 : 0 ≤ ∫ z, |sa16y_k d θ δ η z| * ‖z‖ ^ 2 := integral_nonneg fun z => by positivity
  have hu : ContDiff ℝ ∞ (⇑u) := u.smooth'
  have hSu : MemLp (sa16j_S d (m + 2) (⇑u)) (ENNReal.ofReal p) volume := sa16j_S_memLp (m + 2) p u
  have hW : wNormE (m + 2) p (⇑u) = eLpNorm (wJet (m + 2) (⇑u)) (ENNReal.ofReal p) volume :=
    sa16j_wNormE_eq d (m + 2) p hu hSu
  have hWfin : eLpNorm (wJet (m + 2) (⇑u)) (ENNReal.ofReal p) volume < ⊤ :=
    (sa16j_jet_memLp d (m + 2) p hu hSu).eLpNorm_lt_top
  have hsm := sa16y_E_smooth (k := sa16y_k d θ δ η) (R := R) (fun z hz => sa16y_k_supp θ δ η z hz)
    hR0.le (sa16y_k_int hd hδ0 hη0 hθ0) u
  have hmain := sa16y_wnorm_of_pd d m p hsm
    (K := ENNReal.ofReal (2 * (∫ z, |sa16y_k d θ δ η z| * ‖z‖ ^ 2) * (d : ℝ) ^ 2) *
      eLpNorm (wJet (m + 2) (⇑u)) (ENNReal.ofReal p) volume)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin)
    (fun {j} hj idx => sa16y_pd_even_bound hd m p hR0.le (sa16y_k_meas θ δ η)
      (fun z hz => sa16y_k_supp θ δ η z hz) (sa16y_k_int hd hδ0 hη0 hθ0) hkm
      (sa16y_k_neg θ δ η) u hj idx)
  refine hmain.trans ?_
  rw [hW, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hRle : R ^ (2 - θ) ≤ δ ^ (2 - θ) + η ^ (2 - θ) := by
    rcases max_choice δ η with h | h
    · rw [hR, h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hη0.le _)
    · rw [hR, h]; exact le_add_of_nonneg_left (Real.rpow_nonneg hδ0.le _)
  have hsum0 : 0 ≤ δ ^ (2 - θ) + η ^ (2 - θ) :=
    add_nonneg (Real.rpow_nonneg hδ0.le _) (Real.rpow_nonneg hη0.le _)
  calc (Fintype.card (WIndex d m) : ℝ) * (2 * (∫ z, |sa16y_k d θ δ η z| * ‖z‖ ^ 2) * (d : ℝ) ^ 2)
      = N * (∫ z, |sa16y_k d θ δ η z| * ‖z‖ ^ 2) := by rw [hN]; ring
    _ ≤ N * (R ^ (2 - θ) * I₀) := mul_le_mul_of_nonneg_left hMk hN0
    _ ≤ N * ((δ ^ (2 - θ) + η ^ (2 - θ)) * I₀) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRle hI₀) hN0
    _ ≤ (N * I₀ + 1) * (δ ^ (2 - θ) + η ^ (2 - θ)) := by nlinarith

end SL1

end HRS.Whole.AppendixA.Phase2SA16
