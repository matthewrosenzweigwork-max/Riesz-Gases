import HRS.Commutator.Torus.Defs
import HRS.Commutator.Whole.Positive
import HRS.Commutator.Whole.ScaleAux

/-!
# T-POS helpers, part 1: the positive truncation `f_η` on `ℝ^d` (radial formula, scaling, bounds)

Packet `T-POS`.  Everything here is on `ℝ^d` (reusing `Whole.fTrunc`, `Whole.phiR`, ...):
the radial formula `f_η(x) = c_φ ∫_0^η t^{-s-1} φ(|x|/t) dt`, scaling `f_η(x) = η^{-s} f_1(x/η)`,
`f̂_η(ξ) = η^{d-s} f̂_1(ηξ)`, the pointwise bound `f_η(x) ≤ C η^{2d+4-s} |x|^{-(2d+4)}`
and continuity away from the origin.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

/-- `∫_{(0,η]} G = η ∫_{(0,1]} G(η u)`. -/
lemma tpos_Ioc_scale (G : ℝ → ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ t in Set.Ioc (0 : ℝ) η, G t = η * ∫ u in Set.Ioc (0 : ℝ) 1, G (η * u) := by
  rw [← intervalIntegral.integral_of_le hη.le, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left G hη.ne']
  simp only [mul_zero, mul_one, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul]

lemma tpos_fHatEta_eq (ξ : Euc d) : fHatEta d s η ξ =
    Whole.cPhi d s * ∫ t in Set.Ioc (0 : ℝ) η,
      t ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (t * ‖ξ‖) := by
  unfold fHatEta
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  have ht0 : 0 < t := ht.1
  rw [Whole.re_phiHat, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, Whole.alphaE_two_mul,
    Real.rpow_sub_one ht0.ne']
  ring

lemma tpos_fHatEta_scale (hη : 0 < η) (ξ : Euc d) :
    fHatEta d s η ξ = η ^ ((d : ℝ) - s) * Whole.f1Hat s (η • ξ) := by
  rw [tpos_fHatEta_eq, Whole.f1Hat_eq, tpos_Ioc_scale _ hη]
  have hn : ‖η • ξ‖ = η * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  rw [hn]
  have : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      (η * u) ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (η * u * ‖ξ‖) =
        η ^ ((d : ℝ) - s - 1) * (u ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (u * (η * ‖ξ‖))) := by
    intro u hu
    rw [Real.mul_rpow hη.le hu.1.le]
    have : η * u * ‖ξ‖ = u * (η * ‖ξ‖) := by ring
    rw [this]; ring
  rw [setIntegral_congr_fun measurableSet_Ioc this, integral_const_mul]
  have : η * η ^ ((d : ℝ) - s - 1) = η ^ ((d : ℝ) - s) := by
    conv_rhs => rw [show (d : ℝ) - s = ((d : ℝ) - s - 1) + 1 by ring, Real.rpow_add hη, Real.rpow_one]
    ring
  rw [← this]; ring

lemma tpos_fTrunc_eq (x : Euc d) :
    Whole.fTrunc s η x =
      Whole.cPhi d s * ∫ t in Set.Ioc (0 : ℝ) η, t ^ (-s - 1) * Whole.phiR d (‖x‖ / t) := by
  unfold Whole.fTrunc
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  exact Whole.integrand_eq ht.1 x

lemma tpos_fTrunc_scale (hη : 0 < η) (x : Euc d) :
    Whole.fTrunc s η x = η ^ (-s) * Whole.fTrunc s 1 (η⁻¹ • x) := by
  rw [tpos_fTrunc_eq, tpos_fTrunc_eq, tpos_Ioc_scale _ hη]
  have hn : ‖η⁻¹ • x‖ = ‖x‖ / η := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hη, inv_mul_eq_div]
  rw [hn]
  have : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      (η * u) ^ (-s - 1) * Whole.phiR d (‖x‖ / (η * u)) =
        η ^ (-s - 1) * (u ^ (-s - 1) * Whole.phiR d (‖x‖ / η / u)) := by
    intro u hu
    rw [Real.mul_rpow hη.le hu.1.le, div_div]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioc this, integral_const_mul]
  have : η * η ^ (-s - 1) = η ^ (-s) := by
    conv_rhs => rw [show -s = (-s - 1) + 1 by ring, Real.rpow_add hη, Real.rpow_one]
    ring
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, ← this]
  ring

lemma tpos_fTrunc_nonneg (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) (η : ℝ) (x : Euc d) :
    0 ≤ Whole.fTrunc s η x := by
  rw [tpos_fTrunc_eq]
  refine mul_nonneg (Whole.cPhi_pos d hs0 hs2).le (setIntegral_nonneg measurableSet_Ioc fun t ht => ?_)
  have := Whole.phiR_pos (d := d) (‖x‖ / t)
  have h0 : 0 < t := ht.1
  positivity

lemma tpos_integrand_le (hs2 : s < 2 * (d : ℝ) + 4) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    t ^ (-s - 1) * Whole.phiR d (r / t) ≤ r ^ (-(2 * (d : ℝ) + 4)) * t ^ (2 * (d : ℝ) + 3 - s) := by
  have h1 := Whole.phiR_le_pow (d := d) (div_pos hr ht)
  have h2 : (r / t) ^ (-(2 * (d : ℝ) + 4)) = r ^ (-(2 * (d : ℝ) + 4)) * t ^ (2 * (d : ℝ) + 4) := by
    rw [Real.div_rpow hr.le ht.le, Real.rpow_neg ht.le, div_inv_eq_mul]
  have h3 : t ^ (-s - 1) * t ^ (2 * (d : ℝ) + 4) = t ^ (2 * (d : ℝ) + 3 - s) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  calc t ^ (-s - 1) * Whole.phiR d (r / t) ≤ t ^ (-s - 1) * (r / t) ^ (-(2 * (d : ℝ) + 4)) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht.le _)
    _ = r ^ (-(2 * (d : ℝ) + 4)) * (t ^ (-s - 1) * t ^ (2 * (d : ℝ) + 4)) := by rw [h2]; ring
    _ = _ := by rw [h3]

lemma tpos_integrableOn_pow (hs2 : s < 2 * (d : ℝ) + 4) {η : ℝ} :
    IntegrableOn (fun t : ℝ => t ^ (2 * (d : ℝ) + 3 - s)) (Set.Ioc 0 η) := by
  by_cases hη : 0 ≤ η
  · have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := η) (r := 2 * (d : ℝ) + 3 - s)
      (by linarith)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hη).1 this
  · rw [Set.Ioc_eq_empty (by linarith)]
    exact integrableOn_empty

lemma tpos_integral_pow (hs2 : s < 2 * (d : ℝ) + 4) {η : ℝ} (hη : 0 < η) :
    ∫ t in Set.Ioc (0 : ℝ) η, t ^ (2 * (d : ℝ) + 3 - s) =
      η ^ (2 * (d : ℝ) + 4 - s) / (2 * (d : ℝ) + 4 - s) := by
  rw [← intervalIntegral.integral_of_le hη.le, integral_rpow (Or.inl (by linarith))]
  have e : 2 * (d : ℝ) + 3 - s + 1 = 2 * (d : ℝ) + 4 - s := by ring
  rw [e, Real.zero_rpow (by linarith)]
  simp

/-- The pointwise decay `f_η(x) ≤ C η^{2d+4-s} |x|^{-(2d+4)}`. -/
lemma tpos_fTrunc_le (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) {η : ℝ} (hη : 0 < η) {x : Euc d}
    (hx : x ≠ 0) :
    Whole.fTrunc s η x ≤
      Whole.cPhi d s / (2 * (d : ℝ) + 4 - s) * η ^ (2 * (d : ℝ) + 4 - s) *
        ‖x‖ ^ (-(2 * (d : ℝ) + 4)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [tpos_fTrunc_eq]
  have hcp := Whole.cPhi_pos d hs0 hs2
  have h := integral_mono_of_nonneg (μ := volume.restrict (Set.Ioc (0 : ℝ) η))
    (f := fun t => t ^ (-s - 1) * Whole.phiR d (‖x‖ / t))
    (g := fun t => ‖x‖ ^ (-(2 * (d : ℝ) + 4)) * t ^ (2 * (d : ℝ) + 3 - s))
    (by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0 : ℝ)) (b := η))] with t ht
      have := Whole.phiR_pos (d := d) (‖x‖ / t)
      have h0 : 0 < t := ht.1
      show 0 ≤ t ^ (-s - 1) * Whole.phiR d (‖x‖ / t)
      positivity)
    ((tpos_integrableOn_pow hs2).const_mul _)
    (by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0 : ℝ)) (b := η))] with t ht
      exact tpos_integrand_le hs2 hr ht.1)
  rw [integral_const_mul, tpos_integral_pow hs2 hη] at h
  calc Whole.cPhi d s * ∫ t in Set.Ioc (0 : ℝ) η, t ^ (-s - 1) * Whole.phiR d (‖x‖ / t)
      ≤ Whole.cPhi d s * (‖x‖ ^ (-(2 * (d : ℝ) + 4)) *
          (η ^ (2 * (d : ℝ) + 4 - s) / (2 * (d : ℝ) + 4 - s))) :=
        mul_le_mul_of_nonneg_left h hcp.le
    _ = _ := by ring


/-- Continuity of `f_η` away from the origin. -/
lemma tpos_fTrunc_continuousAt (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) (hη : 0 < η) {x0 : Euc d}
    (hx0 : x0 ≠ 0) : ContinuousAt (Whole.fTrunc s η : Euc d → ℝ) x0 := by
  have hr0 : 0 < ‖x0‖ := norm_pos_iff.2 hx0
  set a : ℝ := ‖x0‖ / 2 with ha
  have ha0 : 0 < a := by positivity
  have hcont := Whole.continuous_phiR (d := d)
  have heq : (Whole.fTrunc s η : Euc d → ℝ) = fun x => Whole.cPhi d s *
      ∫ t in Set.Ioc (0 : ℝ) η, t ^ (-s - 1) * Whole.phiR d (‖x‖ / t) := by
    funext x; exact tpos_fTrunc_eq x
  rw [heq]
  refine ContinuousAt.const_mul ?_ _
  refine continuousAt_of_dominated (μ := volume.restrict (Set.Ioc (0 : ℝ) η))
    (bound := fun t => a ^ (-(2 * (d : ℝ) + 4)) * t ^ (2 * (d : ℝ) + 3 - s)) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    have : Measurable (fun t : ℝ => t ^ (-s - 1) * Whole.phiR d (‖x‖ / t)) := by
      have := hcont.measurable
      fun_prop
    exact this.aestronglyMeasurable
  · have hball : ∀ᶠ x in 𝓝 x0, a ≤ ‖x‖ := by
      have : ContinuousAt (fun x : Euc d => ‖x‖) x0 := continuous_norm.continuousAt
      have h2 : a < ‖x0‖ := by rw [ha]; linarith
      exact this.eventually (Ioi_mem_nhds h2) |>.mono fun x hx => le_of_lt hx
    filter_upwards [hball] with x hx
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0 : ℝ)) (b := η))] with t ht
    have h0 : 0 < t := ht.1
    have hpos : 0 ≤ t ^ (-s - 1) * Whole.phiR d (‖x‖ / t) := by
      have := Whole.phiR_pos (d := d) (‖x‖ / t)
      positivity
    rw [Real.norm_of_nonneg hpos]
    calc t ^ (-s - 1) * Whole.phiR d (‖x‖ / t)
        ≤ ‖x‖ ^ (-(2 * (d : ℝ) + 4)) * t ^ (2 * (d : ℝ) + 3 - s) :=
          tpos_integrand_le hs2 (lt_of_lt_of_le ha0 hx) h0
      _ ≤ a ^ (-(2 * (d : ℝ) + 4)) * t ^ (2 * (d : ℝ) + 3 - s) := by
          have : ‖x‖ ^ (-(2 * (d : ℝ) + 4)) ≤ a ^ (-(2 * (d : ℝ) + 4)) :=
            Real.rpow_le_rpow_of_nonpos ha0 hx (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
          have h3 : 0 ≤ t ^ (2 * (d : ℝ) + 3 - s) := Real.rpow_nonneg h0.le _
          exact mul_le_mul_of_nonneg_right this h3
  · exact (tpos_integrableOn_pow hs2).const_mul _
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0 : ℝ)) (b := η))] with t ht
    have h0 : 0 < t := ht.1
    have : Continuous (fun x : Euc d => t ^ (-s - 1) * Whole.phiR d (‖x‖ / t)) := by
      have := hcont
      fun_prop
    exact this.continuousAt

lemma tpos_integrable_fTrunc (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    Integrable (Whole.fTrunc s η : Euc d → ℝ) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 := (Whole.fTrunc_integrable_aux (d := d) (s := s) (by linarith)).1
  have h2 : Integrable (fun x : Euc d => Whole.fTrunc s 1 (η⁻¹ • x)) :=
    h1.comp_smul (inv_ne_zero hη.ne')
  refine (h2.const_mul (η ^ (-s))).congr (Filter.Eventually.of_forall fun x => ?_)
  exact (tpos_fTrunc_scale hη x).symm

lemma tpos_integral_fTrunc (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    ∫ x : Euc d, Whole.fTrunc s η x =
      Whole.cPhi d s * (∫ x : Euc d, Whole.phi x) / ((d : ℝ) - s) * η ^ ((d : ℝ) - s) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 := (Whole.fTrunc_integrable_aux (d := d) (s := s) (by linarith)).2
  have e : ∀ x : Euc d, Whole.fTrunc s η x = η ^ (-s) * Whole.fTrunc s 1 (η⁻¹ • x) :=
    fun x => tpos_fTrunc_scale hη x
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : Euc d => Whole.fTrunc s 1 x) hη.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [h1]
  have : η ^ (-s) * η ^ d = η ^ ((d : ℝ) - s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hη]; congr 1; ring
  rw [← this]; ring

end HRS.Commutator.TorusNote
