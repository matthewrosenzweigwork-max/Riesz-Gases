import HRS.MS.SA16JetSchwartz
import HRS.MS.CzPvAux1

/-!
# S.A.16 SL2: `oddCut_difference_bound`

`oddCut δ - oddCut η` is the convolution with the odd kernel `k = kr_δ - kr_η`, supported in the ball of radius
`max δ η` with `|k z| ≤ |z|^(1-d-θ)`.  The first moment of such a kernel is `≲ max(δ,η)^(2-θ)` (scaling), and the
generic estimate `sa16j_odd_wnorm` gives the bound with one derivative lost.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv

section SL2
variable {d : ℕ}

/-- the scaled first moment of the singular kernel on a ball -/
lemma sa16s_moment (hd : 1 ≤ d) {θ : ℝ} (hθ2 : θ < 2) :
    ∃ I₀ : ℝ, 0 ≤ I₀ ∧ ∀ ρ : ℝ, 0 < ρ →
      Integrable (fun z : Euc d => (closedBall (0 : Euc d) ρ).indicator
        (fun z => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z) ∧
      ∫ z : Euc d, (closedBall (0 : Euc d) ρ).indicator (fun z => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z =
        ρ ^ (2 - θ) * I₀ := by
  set e : ℝ := 2 - ((d : ℝ) + θ) with he
  set f : Euc d → ℝ := (closedBall (0 : Euc d) 1).indicator (fun w => ‖w‖ ^ e) with hf
  have hfint : Integrable f := by
    rw [hf, integrable_indicator_iff measurableSet_closedBall]
    have : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-((d : ℝ) + θ - 2))) (ball 0 2) :=
      pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) + θ - 2) (by linarith) 2
    have h2 : (fun z : Euc d => ‖z‖ ^ e) = fun z : Euc d => ‖z‖ ^ (-((d : ℝ) + θ - 2)) := by
      funext z; rw [he]; congr 1; ring
    rw [h2]
    exact this.mono_set (closedBall_subset_ball (by norm_num))
  refine ⟨∫ w, f w, integral_nonneg fun w => ?_, fun ρ hρ => ?_⟩
  · rw [hf]
    exact Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) w
  · have hpt : (fun z : Euc d => (closedBall (0 : Euc d) ρ).indicator (fun z => ‖z‖ ^ e) z) =
        fun z => ρ ^ e * f (ρ⁻¹ • z) := by
      funext z
      by_cases hz : z ∈ closedBall (0 : Euc d) ρ
      · have hz' : ‖z‖ ≤ ρ := by simpa using hz
        have hz1 : ρ⁻¹ • z ∈ closedBall (0 : Euc d) 1 := by
          rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hρ.le)]
          calc ρ⁻¹ * ‖z‖ ≤ ρ⁻¹ * ρ := mul_le_mul_of_nonneg_left hz' (inv_nonneg.2 hρ.le)
            _ = 1 := inv_mul_cancel₀ hρ.ne'
        rw [Set.indicator_of_mem hz, hf, Set.indicator_of_mem hz1, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hρ.le), Real.mul_rpow (inv_nonneg.2 hρ.le) (norm_nonneg _),
          Real.inv_rpow hρ.le, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hρ _).ne', one_mul]
      · have hz1 : ρ⁻¹ • z ∉ closedBall (0 : Euc d) 1 := by
          intro h
          apply hz
          rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hρ.le)] at h
          rw [mem_closedBall, dist_zero_right]
          have := mul_le_mul_of_nonneg_left h hρ.le
          rw [← mul_assoc, mul_inv_cancel₀ hρ.ne'] at this
          simpa using this
        rw [Set.indicator_of_notMem hz, hf, Set.indicator_of_notMem hz1, mul_zero]
    rw [hpt]
    refine ⟨(hfint.comp_smul (inv_ne_zero hρ.ne')).const_mul _, ?_⟩
    rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume f hρ.le,
      finrank_euclideanSpace_fin, smul_eq_mul]
    have : ρ ^ e * (ρ ^ d * ∫ w, f w) = ρ ^ (2 - θ) * ∫ w, f w := by
      rw [← mul_assoc, show ρ ^ d = ρ ^ (d : ℝ) from (Real.rpow_natCast ρ d).symm,
        ← Real.rpow_add hρ]
      congr 2
      rw [he]; ring
    exact this

/-- the coordinate odd kernel `z_i |z|^(-d-θ)` -/
def sa16s_g (d : ℕ) (θ : ℝ) (i : Fin d) : Euc d → ℝ := fun z => z i / ‖z‖ ^ ((d : ℝ) + θ)

/-- the same kernel outside the ball of radius `a` -/
def sa16s_kr (d : ℕ) (θ a : ℝ) (i : Fin d) : Euc d → ℝ :=
  {z : Euc d | a < ‖z‖}.indicator (sa16s_g d θ i)

lemma sa16s_g_bound (θ : ℝ) (i : Fin d) {z : Euc d} (hz : 0 < ‖z‖) :
    |sa16s_g d θ i z| ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by
  unfold sa16s_g
  rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hz _), Real.rpow_sub hz, Real.rpow_one]
  have : |z i| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z i
  exact div_le_div_of_nonneg_right this (Real.rpow_pos_of_pos hz _).le

lemma sa16s_g_neg (θ : ℝ) (i : Fin d) (z : Euc d) : sa16s_g d θ i (-z) = -sa16s_g d θ i z := by
  simp [sa16s_g, neg_div]

lemma sa16s_g_meas (θ : ℝ) (i : Fin d) : Measurable (sa16s_g d θ i) :=
  ((EuclideanSpace.proj i).continuous.measurable).div (measurable_norm.pow_const _)

lemma sa16s_kr_meas (θ a : ℝ) (i : Fin d) : Measurable (sa16s_kr d θ a i) :=
  (sa16s_g_meas θ i).indicator (measurableSet_lt measurable_const measurable_norm)

lemma sa16s_kernel_eq (θ : ℝ) (i : Fin d) (z : Euc d) :
    (‖z‖⁻¹ • z) i / ‖z‖ ^ ((d : ℝ) + θ - 1) = sa16s_g d θ i z := by
  by_cases hz : ‖z‖ = 0
  · have : z = 0 := norm_eq_zero.1 hz
    subst this
    simp [sa16s_g]
  · have hn : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    unfold sa16s_g
    rw [Real.rpow_sub_one hn.ne']
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp

lemma sa16s_kr_abs_le {θ a : ℝ} (hd : 1 ≤ d) (ha : 0 < a) (hθ : 0 < θ) (i : Fin d) (z : Euc d) :
    |sa16s_kr d θ a i z| ≤ a ^ (1 - ((d : ℝ) + θ)) := by
  unfold sa16s_kr
  by_cases hz : z ∈ {z : Euc d | a < ‖z‖}
  · rw [Set.indicator_of_mem hz]
    have hz' : a < ‖z‖ := hz
    refine (sa16s_g_bound θ i (ha.trans hz')).trans ?_
    exact Real.rpow_le_rpow_of_nonpos ha hz'.le (by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)
  · rw [Set.indicator_of_notMem hz, abs_zero]
    exact Real.rpow_nonneg ha.le _

lemma sa16s_oddCut_eq {θ a : ℝ} (hd : 1 ≤ d) (ha : 0 < a) (hθ : 0 < θ) (i : Fin d)
    (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    oddCut d θ a i u x = ∫ z, sa16s_kr d θ a i z * u (x - z) := by
  have hS : MeasurableSet {z : Euc d | a < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  unfold oddCut sa16s_kr
  simp_rw [sa16s_kernel_eq]
  rw [← integral_indicator hS]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Set.indicator_mul_left]

lemma sa16s_kr_int {θ a : ℝ} (hd : 1 ≤ d) (ha : 0 < a) (hθ : 0 < θ) (i : Fin d)
    (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    Integrable (fun z => sa16s_kr d θ a i z * u (x - z)) := by
  refine Integrable.mono' (((u.integrable (μ := volume)).comp_sub_left x).norm.const_mul
    (a ^ (1 - ((d : ℝ) + θ))))
    ((sa16s_kr_meas θ a i).aestronglyMeasurable.mul
      (u.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (sa16s_kr_abs_le hd ha hθ i z) (norm_nonneg _)

/-- the difference kernel -/
def sa16s_k (d : ℕ) (θ δ η : ℝ) (i : Fin d) : Euc d → ℝ :=
  fun z => sa16s_kr d θ δ i z - sa16s_kr d θ η i z

lemma sa16s_k_supp (θ δ η : ℝ) (i : Fin d) (z : Euc d) (hz : max δ η < ‖z‖) :
    sa16s_k d θ δ η i z = 0 := by
  have h1 : z ∈ {z : Euc d | δ < ‖z‖} := lt_of_le_of_lt (le_max_left _ _) hz
  have h2 : z ∈ {z : Euc d | η < ‖z‖} := lt_of_le_of_lt (le_max_right _ _) hz
  simp [sa16s_k, sa16s_kr, Set.indicator_of_mem h1, Set.indicator_of_mem h2]

lemma sa16s_k_odd (θ δ η : ℝ) (i : Fin d) (z : Euc d) :
    sa16s_k d θ δ η i (-z) = -sa16s_k d θ δ η i z := by
  unfold sa16s_k sa16s_kr
  simp only [Set.indicator, Set.mem_setOf_eq, norm_neg, sa16s_g_neg]
  split_ifs <;> simp

lemma sa16s_k_abs_le (θ δ η : ℝ) (i : Fin d) (z : Euc d) :
    |sa16s_k d θ δ η i z| ≤ |sa16s_g d θ i z| := by
  unfold sa16s_k sa16s_kr
  simp only [Set.indicator, Set.mem_setOf_eq]
  split_ifs <;> simp

lemma sa16s_k_int {θ δ η : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (i : Fin d) :
    Integrable (sa16s_k d θ δ η i) := by
  have hsupp : sa16s_k d θ δ η i = (closedBall (0 : Euc d) (max δ η)).indicator (sa16s_k d θ δ η i) := by
    funext z
    by_cases hz : z ∈ closedBall (0 : Euc d) (max δ η)
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, sa16s_k_supp θ δ η i z (by simpa using hz)]
  rw [hsupp, integrable_indicator_iff measurableSet_closedBall]
  refine Integrable.mono' (integrableOn_const (C := δ ^ (1 - ((d : ℝ) + θ)) + η ^ (1 - ((d : ℝ) + θ)))
    measure_closedBall_lt_top.ne) ?_ ?_
  · exact ((sa16s_kr_meas θ δ i).sub (sa16s_kr_meas θ η i)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun z _ => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add (sa16s_kr_abs_le hd hδ hθ i z) (sa16s_kr_abs_le hd hη hθ i z))

lemma sa16s_k_moment_le {θ δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (i : Fin d) (z : Euc d) :
    |sa16s_k d θ δ η i z| * ‖z‖ ≤ (closedBall (0 : Euc d) (max δ η)).indicator
      (fun z => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z := by
  by_cases hz : z ∈ closedBall (0 : Euc d) (max δ η)
  · rw [Set.indicator_of_mem hz]
    by_cases hz0 : ‖z‖ = 0
    · have : z = 0 := norm_eq_zero.1 hz0
      subst this
      have : sa16s_k d θ δ η i 0 = 0 := by
        unfold sa16s_k sa16s_kr
        have h1 : (0 : Euc d) ∉ {z : Euc d | δ < ‖z‖} := by simp [hδ.le]
        have h2 : (0 : Euc d) ∉ {z : Euc d | η < ‖z‖} := by simp [hη.le]
        simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      rw [this]
      simp only [abs_zero, zero_mul, norm_zero]
      exact Real.rpow_nonneg le_rfl _
    · have hn : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
      calc |sa16s_k d θ δ η i z| * ‖z‖ ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) * ‖z‖ :=
            mul_le_mul_of_nonneg_right ((sa16s_k_abs_le θ δ η i z).trans (sa16s_g_bound θ i hn))
              hn.le
        _ = ‖z‖ ^ (2 - ((d : ℝ) + θ)) := by
            rw [show 2 - ((d : ℝ) + θ) = (1 - ((d : ℝ) + θ)) + 1 by ring, Real.rpow_add hn,
              Real.rpow_one]
  · rw [Set.indicator_of_notMem hz, sa16s_k_supp θ δ η i z (by simpa using hz)]
    simp

theorem oddCut_difference_bound (d : ℕ) (hd : 1 ≤ d) (m : ℕ)
    (θ p : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) [Fact (2 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ δ η : ℝ, δ ∈ Ioc (0 : ℝ) 1 →
      η ∈ Ioc (0 : ℝ) 1 → ∀ (i : Fin d) (u : SchwartzMap (Euc d) ℝ),
      wNormE m p (fun x => oddCut d θ δ i u x-oddCut d θ η i u x) ≤
        ENNReal.ofReal (C*(δ^(2-θ)+η^(2-θ))) * wNormE (m+1) p u := by
  obtain ⟨I₀, hI₀, hmom⟩ := sa16s_moment (d := d) hd hθ2
  set N : ℝ := (Fintype.card (WIndex d m) : ℝ) * ((d : ℝ) ^ (m + 1)) with hN
  have hN0 : 0 ≤ N := by positivity
  refine ⟨N * I₀ + 1, by positivity, fun δ η hδ hη i u => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hη0 : 0 < η := hη.1
  set R : ℝ := max δ η with hR
  have hR0 : 0 < R := lt_max_of_lt_left hδ0
  have hfun : (fun x => oddCut d θ δ i u x - oddCut d θ η i u x) =
      sa16j_conv (sa16s_k d θ δ η i) (⇑u) := by
    funext x
    unfold sa16j_conv sa16s_k
    rw [sa16s_oddCut_eq hd hδ0 hθ0 i u x, sa16s_oddCut_eq hd hη0 hθ0 i u x,
      ← integral_sub (sa16s_kr_int hd hδ0 hθ0 i u x) (sa16s_kr_int hd hη0 hθ0 i u x)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  rw [hfun]
  obtain ⟨hBint, hBval⟩ := hmom R hR0
  have hkm : Integrable (fun z => |sa16s_k d θ δ η i z| * ‖z‖) := by
    refine Integrable.mono' hBint ?_ (Eventually.of_forall fun z => ?_)
    · exact ((sa16s_kr_meas θ δ i).sub (sa16s_kr_meas θ η i)).abs.mul measurable_norm
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact sa16s_k_moment_le hδ0 hη0 i z
  have hMk : ∫ z, |sa16s_k d θ δ η i z| * ‖z‖ ≤ R ^ (2 - θ) * I₀ := by
    rw [← hBval]
    exact integral_mono hkm hBint (fun z => sa16s_k_moment_le hδ0 hη0 i z)
  have hmain := sa16j_odd_wnorm d hd m p (R := R) hR0.le
    ((sa16s_kr_meas θ δ i).sub (sa16s_kr_meas θ η i)) (fun z hz => sa16s_k_supp θ δ η i z hz)
    (sa16s_k_int hd hδ0 hη0 hθ0 i) hkm (sa16s_k_odd θ δ η i) u
  refine hmain.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hRle : R ^ (2 - θ) ≤ δ ^ (2 - θ) + η ^ (2 - θ) := by
    rcases max_choice δ η with h | h
    · rw [hR, h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hη0.le _)
    · rw [hR, h]; exact le_add_of_nonneg_left (Real.rpow_nonneg hδ0.le _)
  have hsum0 : 0 ≤ δ ^ (2 - θ) + η ^ (2 - θ) :=
    add_nonneg (Real.rpow_nonneg hδ0.le _) (Real.rpow_nonneg hη0.le _)
  calc (Fintype.card (WIndex d m) : ℝ) * ((∫ z, |sa16s_k d θ δ η i z| * ‖z‖) * (d : ℝ) ^ (m + 1))
      = N * (∫ z, |sa16s_k d θ δ η i z| * ‖z‖) := by rw [hN]; ring
    _ ≤ N * (R ^ (2 - θ) * I₀) := mul_le_mul_of_nonneg_left hMk hN0
    _ ≤ N * ((δ ^ (2 - θ) + η ^ (2 - θ)) * I₀) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRle hI₀) hN0
    _ ≤ (N * I₀ + 1) * (δ ^ (2 - θ) + η ^ (2 - θ)) := by nlinarith

end SL2

end HRS.Whole.AppendixA.Phase2SA16
