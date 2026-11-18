import HRS.MS.SA16CutK5
import HRS.MS.SA16JetSchwartz
import HRS.MS.SA16StrongSL2

/-!
# S.A.16 K8: `splice_h1_bound` (worker SA16U2)

Split the splice kernel at radius one.  The near part `k1` (`|z| ≤ 1`) is odd with
`∫ |k1| |z| ≤ I0` uniformly in `δ` (`sa16s_moment`), so `sa16j_odd_gain` bounds it by the `L^p` norm of
`∇(aZ)`; the far part `k2` (`|z| > 1`) is dominated by `|z|^{-(d+θ-1)}`, which is integrable since `θ > 1`,
so Young's inequality bounds it by `‖aZ‖_p`.  The gradient of `aZ` is controlled by `cbNorm 1 a` and the
weak norm `wNormE 1 p Z`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA Phase2SA16

section K8
variable {d : ℕ}

lemma sa16u2_odd (θ δ : ℝ) (i : Fin d) (z : Euc d) :
    spliceKernel d θ δ i (-z) = - spliceKernel d θ δ i z := by
  unfold spliceKernel
  simp only [norm_neg, PiLp.neg_apply]
  split_ifs <;> simp [neg_div, mul_neg]

/-- near part of the splice kernel -/
def sa16u2_k1 (d : ℕ) (θ δ : ℝ) (i : Fin d) : Euc d → ℝ :=
  (closedBall (0 : Euc d) 1).indicator (spliceKernel d θ δ i)

/-- far part of the splice kernel -/
def sa16u2_k2 (d : ℕ) (θ δ : ℝ) (i : Fin d) : Euc d → ℝ :=
  {z : Euc d | 1 < ‖z‖}.indicator (spliceKernel d θ δ i)

/-- the integrable majorant of the far part -/
def sa16u2_g (d : ℕ) (θ : ℝ) : Euc d → ℝ :=
  {z : Euc d | 1 < ‖z‖}.indicator (fun z => ‖z‖ ^ (-((d : ℝ) + θ - 1)))

lemma sa16u2_k12 (θ δ : ℝ) (i : Fin d) (z : Euc d) :
    sa16u2_k1 d θ δ i z + sa16u2_k2 d θ δ i z = spliceKernel d θ δ i z := by
  unfold sa16u2_k1 sa16u2_k2
  by_cases h : ‖z‖ ≤ 1
  · have h1 : z ∈ closedBall (0 : Euc d) 1 := by simpa using h
    have h2 : z ∉ {z : Euc d | 1 < ‖z‖} := by simpa using h
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
  · have h1 : z ∉ closedBall (0 : Euc d) 1 := by simpa using h
    have h2 : z ∈ {z : Euc d | 1 < ‖z‖} := by simpa using h
    rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]

lemma sa16u2_k1_meas (θ δ : ℝ) (i : Fin d) : Measurable (sa16u2_k1 d θ δ i) :=
  (sa16k5_ks_meas θ δ i).indicator measurableSet_closedBall

lemma sa16u2_k2_meas (θ δ : ℝ) (i : Fin d) : Measurable (sa16u2_k2 d θ δ i) :=
  (sa16k5_ks_meas θ δ i).indicator (measurableSet_lt measurable_const measurable_norm)

lemma sa16u2_g_meas (θ : ℝ) : Measurable (sa16u2_g d θ) :=
  (measurable_norm.pow_const _).indicator (measurableSet_lt measurable_const measurable_norm)

lemma sa16u2_g_nonneg (θ : ℝ) (z : Euc d) : 0 ≤ sa16u2_g d θ z :=
  Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z

lemma sa16u2_g_int (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) : Integrable (sa16u2_g d θ) := by
  unfold sa16u2_g
  rw [integrable_indicator_iff (measurableSet_lt measurable_const measurable_norm)]
  exact pvapi_integrableOn_rpow_outside hd (s := (d : ℝ) + θ - 1) (by linarith) one_pos

lemma sa16u2_k1_odd (θ δ : ℝ) (i : Fin d) (z : Euc d) :
    sa16u2_k1 d θ δ i (-z) = - sa16u2_k1 d θ δ i z := by
  unfold sa16u2_k1
  by_cases h : z ∈ closedBall (0 : Euc d) 1
  · have h' : -z ∈ closedBall (0 : Euc d) 1 := by simpa using h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h', sa16u2_odd]
  · have h' : -z ∉ closedBall (0 : Euc d) 1 := by simpa using h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h', neg_zero]

lemma sa16u2_k1_abs_le (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (i : Fin d) (z : Euc d) :
    |sa16u2_k1 d θ δ i z| ≤ sa16k5_D d θ δ z := by
  unfold sa16u2_k1
  by_cases h : z ∈ closedBall (0 : Euc d) 1
  · rw [Set.indicator_of_mem h]; exact sa16k5_ks_le_D hδ hθ i z
  · rw [Set.indicator_of_notMem h, abs_zero]; exact sa16k5_D_nonneg hδ z

/-- the first moment of the near kernel is bounded by the scaled moment -/
lemma sa16u2_k1_moment_le (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (i : Fin d) (z : Euc d) :
    |sa16u2_k1 d θ δ i z| * ‖z‖ ≤ (closedBall (0 : Euc d) 1).indicator
      (fun z => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z := by
  unfold sa16u2_k1
  by_cases h : z ∈ closedBall (0 : Euc d) 1
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    by_cases hz0 : ‖z‖ = 0
    · rw [hz0, mul_zero]; exact Real.rpow_nonneg le_rfl _
    · have hn : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
      calc |spliceKernel d θ δ i z| * ‖z‖ ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) * ‖z‖ :=
            mul_le_mul_of_nonneg_right (sa16k5_ks_bound hδ hθ i z) hn.le
        _ = ‖z‖ ^ (2 - ((d : ℝ) + θ)) := by
            rw [show 2 - ((d : ℝ) + θ) = (1 - ((d : ℝ) + θ)) + 1 by ring, Real.rpow_add hn, Real.rpow_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp

lemma sa16u2_k2_abs_le {θ δ : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ) (i : Fin d) (z : Euc d) :
    |sa16u2_k2 d θ δ i z| ≤ sa16u2_g d θ z := by
  unfold sa16u2_k2 sa16u2_g
  by_cases h : z ∈ {z : Euc d | 1 < ‖z‖}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    have := sa16k5_ks_bound hδ hθ i z
    rwa [show 1 - ((d : ℝ) + θ) = -((d : ℝ) + θ - 1) by ring] at this
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp

/-- the first moment of the near part, uniformly in `δ` -/
lemma sa16u2_moment1 (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (i : Fin d) {I0 : ℝ}
    (hint : Integrable (Set.indicator (closedBall (0 : Euc d) 1)
      (fun z => ‖z‖ ^ (2 - ((d : ℝ) + θ)))))
    (hI0 : ∫ z : Euc d, (closedBall (0 : Euc d) 1).indicator
      (fun z => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z = I0) :
    Integrable (fun z : Euc d => |sa16u2_k1 d θ δ i z| * ‖z‖) ∧
      ∫ z : Euc d, |sa16u2_k1 d θ δ i z| * ‖z‖ ≤ I0 := by
  have hnn : ∀ z : Euc d, 0 ≤ |sa16u2_k1 d θ δ i z| * ‖z‖ :=
    fun z => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hle : ∀ z : Euc d, |sa16u2_k1 d θ δ i z| * ‖z‖ ≤ (closedBall (0 : Euc d) 1).indicator
      (fun z => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z :=
    fun z => sa16u2_k1_moment_le hd hθ hδ i z
  have hmeas : Measurable (fun z : Euc d => |sa16u2_k1 d θ δ i z| * ‖z‖) :=
    (continuous_abs.measurable.comp (sa16u2_k1_meas θ δ i)).mul measurable_norm
  refine ⟨Integrable.mono' hint hmeas.aestronglyMeasurable (Eventually.of_forall fun z => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (hnn z)]; exact hle z
  · rw [← hI0]
    exact integral_mono_of_nonneg (Eventually.of_forall hnn) hint (Eventually.of_forall hle)

/-- `L^p` bound of the near part, via the odd gain estimate -/
lemma sa16u2_near (hd : 1 ≤ d) {θ δ p : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : 1 < θ) (hδ : 0 < δ) (hp : 1 ≤ p)
    (i : Fin d) {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) {B : ℝ} (hwb : ∀ x, ‖u x‖ ≤ B) {I0 : ℝ}
    (hint : Integrable (Set.indicator (closedBall (0 : Euc d) 1)
      (fun z => ‖z‖ ^ (2 - ((d : ℝ) + θ)))))
    (hI0 : ∫ z : Euc d, (closedBall (0 : Euc d) 1).indicator
      (fun z => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z = I0) :
    eLpNorm (fun x => ∫ z, sa16u2_k1 d θ δ i z * u (x - z)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal I0 * eLpNorm (fun x => ‖fderiv ℝ u x‖) (ENNReal.ofReal p) volume := by
  have hk1 : Integrable (sa16u2_k1 d θ δ i) :=
    Integrable.mono' (sa16k5_D_int hd hθ1 hδ) (sa16u2_k1_meas θ δ i).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact sa16u2_k1_abs_le hd hθ0 hδ i z)
  obtain ⟨hkm, hmom⟩ := sa16u2_moment1 hd hθ0 hδ i hint hI0
  have h := sa16j_odd_gain hp (sa16u2_k1_meas θ δ i) hk1 hkm (fun z => sa16u2_k1_odd θ δ i z) hu hwb
  simp only [smul_eq_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hmom) (by positivity))

/-- `L^p` bound of the far part, via Young's inequality -/
lemma sa16u2_far (hd : 1 ≤ d) {θ δ p : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : 1 < θ) (hδ : 0 < δ) (hp : 1 ≤ p)
    (i : Fin d) {u : Euc d → ℝ} (hu : Continuous u) :
    eLpNorm (fun x => ∫ z, sa16u2_k2 d θ δ i z * u (x - z)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (∫ z, sa16u2_g d θ z) * eLpNorm u (ENNReal.ofReal p) volume := by
  have hgi := sa16u2_g_int hd hθ1 (d := d)
  have hJ : ∫⁻ z, ENNReal.ofReal (sa16u2_g d θ z) = ENNReal.ofReal (∫ z, sa16u2_g d θ z) :=
    (ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall (sa16u2_g_nonneg θ))).symm
  have hF : ∀ x, ‖∫ z, sa16u2_k2 d θ δ i z * u (x - z)‖ₑ ≤
      ∫⁻ z, ENNReal.ofReal (sa16u2_g d θ z) * ‖u (x - z)‖ₑ := by
    intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
    rw [enorm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (sa16u2_k2_abs_le hδ hθ0 i z)
  have hFm : AEStronglyMeasurable (fun x => ∫ z, sa16u2_k2 d θ δ i z * u (x - z)) volume :=
    sa16k5_conv_aesm (sa16u2_k2_meas θ δ i) hu
  have key := elema_young (sa16u2_g_meas (d := d) θ) hu.measurable hFm hp hF
  rw [hJ] at key
  exact key

/-- `L^p` estimate of a function dominated pointwise by a multiple of a weight -/
lemma sa16u2_eLp_le {E : Type*} [NormedAddCommGroup E] {f : Euc d → ℝ} {W : Euc d → E} {c p : ℝ}
    (hc : 0 ≤ c) (hf : AEStronglyMeasurable f volume) (hW : AEStronglyMeasurable W volume)
    (h : ∀ x, ‖f x‖ ≤ c * ‖W x‖) :
    eLpNorm f (ENNReal.ofReal p) volume ≤ ENNReal.ofReal c * eLpNorm W (ENNReal.ofReal p) volume := by
  have h1 : eLpNorm f (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => c * ‖W x‖) (ENNReal.ofReal p) volume :=
    eLpNorm_mono_real hf h
  have h2 : (fun x => c * ‖W x‖) = c • (fun x => ‖W x‖) := by
    funext x; simp
  have h3 : eLpNorm (fun x => c * ‖W x‖) (ENNReal.ofReal p) volume =
      ENNReal.ofReal c * eLpNorm W (ENNReal.ofReal p) volume := by
    rw [h2, eLpNorm_const_smul, eLpNorm_norm W hW, Real.enorm_of_nonneg hc]
  exact h1.trans h3.le

/-- `‖Φ‖_{C_b^1}` dominates the sup of `|a|` -/
lemma sa16u2_cb_term {a : Euc d → ℝ} (ha : MemCb 1 a) (j : ℕ) (hj : j ≤ 1) (x : Euc d) :
    ‖iteratedFDeriv ℝ j a x‖ ≤ cbNorm 1 a := by
  unfold cbNorm
  have h1 : ‖iteratedFDeriv ℝ j a x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j a z‖ :=
    le_ciSup (ha.2 j hj) x
  have h2 : (⨆ z, ‖iteratedFDeriv ℝ j a z‖) ≤
      ∑ j' ∈ Finset.range (1 + 1), ⨆ z, ‖iteratedFDeriv ℝ j' a z‖ :=
    Finset.single_le_sum (f := fun j' => ⨆ z, ‖iteratedFDeriv ℝ j' a z‖)
      (fun j' _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  exact h1.trans h2

lemma sa16u2_abs_le_cb {a : Euc d → ℝ} (ha : MemCb 1 a) (x : Euc d) : |a x| ≤ cbNorm 1 a := by
  have h := sa16u2_cb_term ha 0 zero_le_one x
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

lemma sa16u2_fderiv_le_cb {a : Euc d → ℝ} (ha : MemCb 1 a) (x : Euc d) :
    ‖fderiv ℝ a x‖ ≤ cbNorm 1 a := by
  have h := sa16u2_cb_term ha 1 le_rfl x
  rwa [norm_iteratedFDeriv_one] at h

lemma sa16u2_zero_le_jet (g : Euc d → ℝ) (x : Euc d) : |g x| ≤ ‖wJet 1 g x‖ := by
  have h := sa16j_pd_le_jet 1 g x (j := 0) (Nat.zero_le _) (fun l => Fin.elim0 l)
  rwa [sa16j_pd_zero] at h

lemma sa16u2_jet_bound (g : Euc d → ℝ) (x : Euc d) :
    |g x| + ‖fderiv ℝ g x‖ ≤ (1 + (d : ℝ)) * ‖wJet 1 g x‖ := by
  have h0 := sa16u2_zero_le_jet g x
  have h1 : ‖fderiv ℝ g x‖ ≤ ∑ r : Fin 1 → Fin d, |partialDeriv r g x| := by
    have h := sa16j_norm_iter_le g x 1
    rwa [norm_iteratedFDeriv_one] at h
  have h2 : ∑ r : Fin 1 → Fin d, |partialDeriv r g x| ≤ ∑ r : Fin 1 → Fin d, ‖wJet 1 g x‖ :=
    Finset.sum_le_sum fun r _ => sa16j_pd_le_jet 1 g x le_rfl r
  have h3 : ∑ r : Fin 1 → Fin d, ‖wJet 1 g x‖ = (d : ℝ) * ‖wJet 1 g x‖ := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [add_mul, one_mul]
  linarith

/-- the gradient of `aZ` is controlled by the weak norm of `Z` -/
lemma sa16u2_grad_bound {a : Euc d → ℝ} (ha : MemCb 1 a) (Z : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    ‖fderiv ℝ (fun y => a y * Z y) x‖ ≤ (cbNorm 1 a * (1 + (d : ℝ))) * ‖wJet 1 (⇑Z) x‖ := by
  have hac : ContDiff ℝ 1 a := ha.1
  have hZ1 : ContDiff ℝ 1 (⇑Z) := Z.smooth'.of_le (by exact_mod_cast le_top)
  have hda : DifferentiableAt ℝ a x := (hac.differentiable one_ne_zero) x
  have hdz : DifferentiableAt ℝ (⇑Z) x := (hZ1.differentiable one_ne_zero) x
  have hfd : fderiv ℝ (fun y => a y * Z y) x = a x • fderiv ℝ (⇑Z) x + Z x • fderiv ℝ a x :=
    fderiv_mul hda hdz
  have h1 : ‖fderiv ℝ (fun y => a y * Z y) x‖ ≤
      |a x| * ‖fderiv ℝ (⇑Z) x‖ + |Z x| * ‖fderiv ℝ a x‖ := by
    rw [hfd]
    calc ‖a x • fderiv ℝ (⇑Z) x + Z x • fderiv ℝ a x‖
        ≤ ‖a x • fderiv ℝ (⇑Z) x‖ + ‖Z x • fderiv ℝ a x‖ := norm_add_le _ _
      _ = |a x| * ‖fderiv ℝ (⇑Z) x‖ + |Z x| * ‖fderiv ℝ a x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hA := sa16u2_abs_le_cb ha x
  have hB := sa16u2_fderiv_le_cb ha x
  have hC : 0 ≤ cbNorm 1 a := (norm_nonneg _).trans hB
  have hJ := sa16u2_jet_bound (⇑Z) x
  calc ‖fderiv ℝ (fun y => a y * Z y) x‖
      ≤ |a x| * ‖fderiv ℝ (⇑Z) x‖ + |Z x| * ‖fderiv ℝ a x‖ := h1
    _ ≤ cbNorm 1 a * ‖fderiv ℝ (⇑Z) x‖ + |Z x| * cbNorm 1 a :=
        add_le_add (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
    _ = cbNorm 1 a * (|Z x| + ‖fderiv ℝ (⇑Z) x‖) := by ring
    _ ≤ cbNorm 1 a * ((1 + (d : ℝ)) * ‖wJet 1 (⇑Z) x‖) := mul_le_mul_of_nonneg_left hJ hC
    _ = (cbNorm 1 a * (1 + (d : ℝ))) * ‖wJet 1 (⇑Z) x‖ := by ring

lemma sa16u2_int_conv {k : Euc d → ℝ} (hk : Measurable k) (hki : Integrable k) {u : Euc d → ℝ}
    (hu : Continuous u) {B : ℝ} (hB : ∀ x, ‖u x‖ ≤ B) (x : Euc d) :
    Integrable (fun z => k z * u (x - z)) := by
  refine Integrable.mono' (hki.norm.mul_const B)
    (hk.aestronglyMeasurable.mul (hu.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

end K8

/-- K8: no fractional Sobolev representation is needed for lower terms;
one ordinary solution derivative controls the order theta-1 operator. -/
theorem splice_h1_bound (d : ℕ) (hd : 1 ≤ d) (θ p : ℝ)
    (hθ1 : 1 < θ) (hθ2 : θ < 2) [Fact (2 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ i : Fin d,
      ∀ a : Euc d → ℝ, MemCb 1 a → ∀ Z : SchwartzMap (Euc d) ℝ,
      eLpNorm (spliceOdd d θ δ i (fun y => a y*Z y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C*cbNorm 1 a)*wNormE 1 p Z := by
  obtain ⟨I0, hI0, hmom⟩ := sa16s_moment (d := d) hd hθ2
  obtain ⟨hI1int, hI1eq⟩ := hmom 1 one_pos
  rw [Real.one_rpow, one_mul] at hI1eq
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp1 : 1 ≤ p := by linarith
  have hJnn : 0 ≤ ∫ z, sa16u2_g d θ z :=
    integral_nonneg fun z => sa16u2_g_nonneg θ z
  refine ⟨(I0 * (1 + (d : ℝ)) + ∫ z, sa16u2_g d θ z) + 1,
    add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg hI0 (by positivity)) hJnn) one_pos,
    fun δ hδ i a ha Z => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hC0 : 0 ≤ cbNorm 1 a := (norm_nonneg _).trans (sa16u2_cb_term ha 0 zero_le_one 0)
  obtain ⟨Bz, hBz⟩ := sa16j_schwartz_bdd Z
  have hZ1 : ContDiff ℝ 1 (⇑Z) := Z.smooth'.of_le (by exact_mod_cast le_top)
  have hac : ContDiff ℝ 1 a := ha.1
  set u : Euc d → ℝ := fun y => a y * Z y with hu
  have hu1 : ContDiff ℝ 1 u := hac.mul hZ1
  have huc : Continuous u := hu1.continuous
  have hub : ∀ x, ‖u x‖ ≤ cbNorm 1 a * Bz := fun x => by
    show ‖a x * Z x‖ ≤ _
    calc ‖a x * Z x‖ = |a x| * |Z x| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ cbNorm 1 a * Bz := mul_le_mul (sa16u2_abs_le_cb ha x) (hBz x) (abs_nonneg _) hC0
  have hsplit : spliceOdd d θ δ i u =
      (fun x => ∫ z, sa16u2_k1 d θ δ i z * u (x - z)) +
        (fun x => ∫ z, sa16u2_k2 d θ δ i z * u (x - z)) := by
    funext x
    simp only [Pi.add_apply]
    unfold spliceOdd
    rw [← integral_add
      (sa16u2_int_conv (sa16u2_k1_meas θ δ i) (Integrable.mono' (sa16k5_D_int hd hθ1 hδ0)
        (sa16u2_k1_meas θ δ i).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact sa16u2_k1_abs_le hd hθ0 hδ0 i z)) huc hub x)
      (sa16u2_int_conv (sa16u2_k2_meas θ δ i) (Integrable.mono' (sa16u2_g_int hd hθ1)
        (sa16u2_k2_meas θ δ i).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact sa16u2_k2_abs_le hδ0 hθ0 i z)) huc hub x)]
    congr 1
    funext z
    rw [← sa16u2_k12 θ δ i z]
    ring
  have hW : wNormE 1 p (⇑Z) = eLpNorm (wJet 1 (⇑Z)) (ENNReal.ofReal p) volume :=
    sa16j_wNormE_eq d 1 p Z.smooth' (sa16j_S_memLp 1 p Z)
  have hG : eLpNorm (fun x => ‖fderiv ℝ u x‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (cbNorm 1 a * (1 + (d : ℝ))) * wNormE 1 p (⇑Z) := by
    rw [hW]
    exact sa16u2_eLp_le (mul_nonneg hC0 (by positivity))
      (hu1.continuous_fderiv one_ne_zero).norm.aestronglyMeasurable
      (sa16j_jet_cont Z.smooth' 1).aestronglyMeasurable
      (fun x => by rw [norm_norm]; exact sa16u2_grad_bound ha Z x)
  have hU : eLpNorm u (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (cbNorm 1 a) * wNormE 1 p (⇑Z) := by
    rw [hW]
    refine sa16u2_eLp_le hC0 huc.aestronglyMeasurable
      (sa16j_jet_cont Z.smooth' 1).aestronglyMeasurable (fun x => ?_)
    show ‖a x * Z x‖ ≤ _
    calc ‖a x * Z x‖ = |a x| * |Z x| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ cbNorm 1 a * ‖wJet 1 (⇑Z) x‖ :=
          mul_le_mul (sa16u2_abs_le_cb ha x) (sa16u2_zero_le_jet (⇑Z) x) (abs_nonneg _) hC0
  have hF1 := sa16u2_near hd hθ0 hθ1 hδ0 hp1 i hu1 hub hI1int hI1eq
  have hF2 := sa16u2_far hd hθ0 hθ1 hδ0 hp1 i huc
  rw [hsplit]
  calc eLpNorm ((fun x => ∫ z, sa16u2_k1 d θ δ i z * u (x - z)) +
          (fun x => ∫ z, sa16u2_k2 d θ δ i z * u (x - z))) (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x => ∫ z, sa16u2_k1 d θ δ i z * u (x - z)) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => ∫ z, sa16u2_k2 d θ δ i z * u (x - z)) (ENNReal.ofReal p) volume :=
        eLpNorm_add_le (ENNReal.one_le_ofReal.2 hp1)
    _ ≤ ENNReal.ofReal I0 * (ENNReal.ofReal (cbNorm 1 a * (1 + (d : ℝ))) * wNormE 1 p (⇑Z)) +
          ENNReal.ofReal (∫ z, sa16u2_g d θ z) * (ENNReal.ofReal (cbNorm 1 a) * wNormE 1 p (⇑Z)) :=
        add_le_add (hF1.trans (mul_le_mul_of_nonneg_left hG (by positivity))) (hF2.trans (mul_le_mul_of_nonneg_left hU (by positivity)))
    _ = (ENNReal.ofReal (I0 * (cbNorm 1 a * (1 + (d : ℝ)))) +
          ENNReal.ofReal ((∫ z, sa16u2_g d θ z) * cbNorm 1 a)) * wNormE 1 p (⇑Z) := by
        rw [ENNReal.ofReal_mul hI0, ENNReal.ofReal_mul hJnn, add_mul]
        ring
    _ = ENNReal.ofReal (I0 * (cbNorm 1 a * (1 + (d : ℝ))) + (∫ z, sa16u2_g d θ z) * cbNorm 1 a) *
          wNormE 1 p (⇑Z) := by
        rw [ENNReal.ofReal_add (mul_nonneg hI0 (mul_nonneg hC0 (by positivity)))
          (mul_nonneg hJnn hC0)]
    _ ≤ ENNReal.ofReal (((I0 * (1 + (d : ℝ)) + ∫ z, sa16u2_g d θ z) + 1) * cbNorm 1 a) *
          wNormE 1 p (⇑Z) := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by positivity)
        have hexp : ((I0 * (1 + (d : ℝ)) + ∫ z, sa16u2_g d θ z) + 1) * cbNorm 1 a =
            I0 * (cbNorm 1 a * (1 + (d : ℝ))) + (∫ z, sa16u2_g d θ z) * cbNorm 1 a +
              cbNorm 1 a := by ring
        rw [hexp]
        linarith

end HRS.Whole.AppendixA.Phase2SA16Cutoff
