import HRS.Commutator.Torus.TPOSAux5
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# T-POS helpers, part 6: Mellin transforms of Gaussian mixtures

The identity `ĝ(k) = tScale · c_φ ∫_0^∞ t^{d-s-1} φ̂(t|k|) dt` (the Fourier coefficients of the Riesz kernel versus
the Fourier side of the positive truncation).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

lemma tpos_gauss_integrable {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1) * Real.exp (-c * u ^ 2)) (Set.Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2) (s := a - 1) (b := c) (by linarith)
    (by norm_num) hc
  refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_two]

lemma tpos_gauss_mellin {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫ u in Set.Ioi (0 : ℝ), u ^ (a - 1) * Real.exp (-c * u ^ 2) =
      c ^ (-a / 2) * (1 / 2) * Real.Gamma (a / 2) := by
  have := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := a - 1) (b := c) (by norm_num)
    (by linarith) hc
  simp only [Real.rpow_two, sub_add_cancel] at this
  rw [← this]

lemma tpos_mixture_mellin {a : ℝ} (ha : 0 < a) {W c : ℝ → ℝ}
    (hW : ∀ v, 0 < v → 0 ≤ W v) (hc : ∀ v, 0 < v → 0 < c v) (hWm : Measurable W)
    (hcm : Measurable c)
    (hint : IntegrableOn (fun v => W v * c v ^ (-a / 2)) (Set.Ioi 0)) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1) * ∫ v in Set.Ioi (0 : ℝ), W v * Real.exp (-c v * u ^ 2))
        (Set.Ioi 0) ∧
      ∫ u in Set.Ioi (0 : ℝ), u ^ (a - 1) * ∫ v in Set.Ioi (0 : ℝ), W v * Real.exp (-c v * u ^ 2) =
        (1 / 2) * Real.Gamma (a / 2) * ∫ v in Set.Ioi (0 : ℝ), W v * c v ^ (-a / 2) := by
  set G : ℝ → ℝ → ℝ := fun u v => u ^ (a - 1) * (W v * Real.exp (-c v * u ^ 2)) with hG
  have hGm : Measurable (fun p : ℝ × ℝ => G p.1 p.2) := by
    simp only [hG]
    have h1 : Measurable (fun p : ℝ × ℝ => W p.2) := hWm.comp measurable_snd
    have h2 : Measurable (fun p : ℝ × ℝ => c p.2) := hcm.comp measurable_snd
    fun_prop
  have hslice : ∀ v, 0 < v → ∫ u in Set.Ioi (0 : ℝ), G u v =
      W v * (c v ^ (-a / 2) * (1 / 2) * Real.Gamma (a / 2)) := by
    intro v hv
    have : ∀ u : ℝ, G u v = W v * (u ^ (a - 1) * Real.exp (-c v * u ^ 2)) := fun u => by
      simp only [hG]; ring
    simp_rw [this]
    rw [integral_const_mul, tpos_gauss_mellin ha (hc v hv)]
  have hGint : Integrable (fun p : ℝ × ℝ => G p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hGm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with v hv
      have : (fun u : ℝ => G u v) = fun u => W v * (u ^ (a - 1) * Real.exp (-c v * u ^ 2)) := by
        funext u; simp only [hG]; ring
      rw [this]
      exact (tpos_gauss_integrable ha (hc v hv)).const_mul _
    · have h1 : Integrable (fun v : ℝ => W v * (c v ^ (-a / 2) * (1 / 2) * Real.Gamma (a / 2)))
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
        have := hint.mul_const ((1 / 2) * Real.Gamma (a / 2))
        refine this.congr (Filter.Eventually.of_forall fun v => ?_)
        simp only; ring
      refine h1.congr ?_
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with v hv
      have hnn : ∀ u ∈ Set.Ioi (0 : ℝ), ‖G u v‖ = G u v := by
        intro u hu
        have hu : 0 < u := hu
        have := hW v hv
        rw [Real.norm_of_nonneg]
        simp only [hG]
        have := Real.exp_pos (-c v * u ^ 2)
        positivity
      rw [setIntegral_congr_fun measurableSet_Ioi hnn, hslice v hv]
  have hswap := integral_integral_swap (f := G) hGint
  have e1 : ∀ u : ℝ, ∫ v in Set.Ioi (0 : ℝ), G u v =
      u ^ (a - 1) * ∫ v in Set.Ioi (0 : ℝ), W v * Real.exp (-c v * u ^ 2) := fun u => by
    simp only [hG]
    rw [integral_const_mul]
  refine ⟨?_, ?_⟩
  · have := hGint.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    exact e1 u
  · simp_rw [← e1]
    rw [hswap]
    rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => hslice v hv)]
    have : ∀ v : ℝ, W v * (c v ^ (-a / 2) * (1 / 2) * Real.Gamma (a / 2)) =
        ((1 / 2) * Real.Gamma (a / 2)) * (W v * c v ^ (-a / 2)) := fun v => by ring
    simp_rw [this]
    rw [integral_const_mul]


/-- `∫_0^∞ v^e e^{-v} dv = Γ(e+1)`. -/
lemma tpos_gamma_int {e : ℝ} (he : -1 < e) :
    ∫ v in Set.Ioi (0 : ℝ), v ^ e * Real.exp (-v) = Real.Gamma (e + 1) := by
  have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := e + 1) (r := 1) (by linarith) one_pos
  simp only [add_sub_cancel_right, one_mul, Real.one_rpow, div_one] at this
  rw [← this]

lemma tpos_gamma_integrable {e : ℝ} (he : -1 < e) :
    IntegrableOn (fun v : ℝ => v ^ e * Real.exp (-v)) (Set.Ioi 0) := by
  have := Whole.integrableOn_rpow_exp (a := e) (b := 1) he one_pos
  refine this.congr_fun (fun v _ => ?_) measurableSet_Ioi
  simp

/-- the weight of the Gaussian mixture of `φ` -/
def tposW1 (d : ℕ) (v : ℝ) : ℝ := (Real.Gamma ((d : ℝ) + 2))⁻¹ * (v ^ ((d : ℝ) + 1) * Real.exp (-v))

/-- the weight of the Gaussian mixture of `φ̂` -/
def tposW2 (d : ℕ) (v : ℝ) : ℝ :=
  (Real.Gamma ((d : ℝ) + 2))⁻¹ * (v ^ ((d : ℝ) + 1) * Real.exp (-v)) * (Real.pi / v) ^ ((d : ℝ) / 2)

lemma tposW1_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ tposW1 d v := by
  unfold tposW1
  have : 0 < Real.Gamma ((d : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

lemma tposW2_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ tposW2 d v := by
  unfold tposW2
  have : 0 < Real.Gamma ((d : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

lemma tposW1_measurable : Measurable (tposW1 d) := by
  unfold tposW1; fun_prop

lemma tposW2_measurable : Measurable (tposW2 d) := by
  unfold tposW2; fun_prop

lemma tpos_phiR_mixture (r : ℝ) :
    Whole.phiR d r = ∫ v in Set.Ioi (0 : ℝ), tposW1 d v * Real.exp (-v * r ^ 2) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (d : ℝ) + 2) (r := 1 + r ^ 2)
    (by positivity) (by positivity)
  have e : ∀ t : ℝ, tposW1 d t * Real.exp (-t * r ^ 2) =
      (Real.Gamma ((d : ℝ) + 2))⁻¹ * (t ^ ((d : ℝ) + 2 - 1) * Real.exp (-((1 + r ^ 2) * t))) := by
    intro t
    unfold tposW1
    have : t ^ ((d : ℝ) + 1) * Real.exp (-t) * Real.exp (-t * r ^ 2) =
        t ^ ((d : ℝ) + 2 - 1) * Real.exp (-((1 + r ^ 2) * t)) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring_nf
    calc (Real.Gamma ((d : ℝ) + 2))⁻¹ * (t ^ ((d : ℝ) + 1) * Real.exp (-t)) * Real.exp (-t * r ^ 2)
        = (Real.Gamma ((d : ℝ) + 2))⁻¹ * (t ^ ((d : ℝ) + 1) * Real.exp (-t) * Real.exp (-t * r ^ 2)) := by ring
      _ = _ := by rw [this]
  simp_rw [e]
  rw [integral_const_mul, h]
  have hG : 0 < Real.Gamma ((d : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  simp only [Whole.phiR]
  field_simp

lemma tpos_phiHatR_mixture (r : ℝ) :
    Whole.phiHatR d r = ∫ v in Set.Ioi (0 : ℝ), tposW2 d v * Real.exp (-(Real.pi ^ 2 / v) * r ^ 2) := by
  unfold Whole.phiHatR
  refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
  simp only [Whole.gmixHat, tposW2]
  have : -Real.pi ^ 2 * r ^ 2 / v = -(Real.pi ^ 2 / v) * r ^ 2 := by ring
  rw [this]; ring


lemma tposW1_mul {v : ℝ} (hv : 0 < v) :
    tposW1 d v * v ^ (-s / 2) =
      (Real.Gamma ((d : ℝ) + 2))⁻¹ * (v ^ ((d : ℝ) + 1 - s / 2) * Real.exp (-v)) := by
  unfold tposW1
  have : v ^ ((d : ℝ) + 1) * v ^ (-s / 2) = v ^ ((d : ℝ) + 1 - s / 2) := by
    rw [← Real.rpow_add hv]; congr 1; ring
  calc (Real.Gamma ((d : ℝ) + 2))⁻¹ * (v ^ ((d : ℝ) + 1) * Real.exp (-v)) * v ^ (-s / 2)
      = (Real.Gamma ((d : ℝ) + 2))⁻¹ * ((v ^ ((d : ℝ) + 1) * v ^ (-s / 2)) * Real.exp (-v)) := by ring
    _ = _ := by rw [this]

lemma tpos_Is (hs : 0 < s) (hsd : s < (d : ℝ) - 2) :
    ∫ r in Set.Ioi (0 : ℝ), r ^ (s - 1) * Whole.phiR d r =
      (1 / 2) * Real.Gamma (s / 2) * ((Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.Gamma ((d : ℝ) + 2 - s / 2)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hint : IntegrableOn (fun v : ℝ => tposW1 d v * (fun v : ℝ => v) v ^ (-s / 2)) (Set.Ioi 0) := by
    have : IntegrableOn (fun v : ℝ => (Real.Gamma ((d : ℝ) + 2))⁻¹ *
        (v ^ ((d : ℝ) + 1 - s / 2) * Real.exp (-v))) (Set.Ioi 0) :=
      (tpos_gamma_integrable (e := (d : ℝ) + 1 - s / 2) (by linarith)).const_mul
        (Real.Gamma ((d : ℝ) + 2))⁻¹
    refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
    exact (tposW1_mul (d := d) (s := s) hv).symm
  obtain ⟨_, h2⟩ := tpos_mixture_mellin (a := s) hs (W := tposW1 d) (c := fun v => v)
    (fun v hv => tposW1_nonneg hv) (fun v hv => hv) tposW1_measurable measurable_id hint
  have e1 : ∀ r : ℝ, Whole.phiR d r = ∫ v in Set.Ioi (0 : ℝ), tposW1 d v * Real.exp (-v * r ^ 2) :=
    tpos_phiR_mixture
  simp_rw [← e1] at h2
  rw [h2]
  have : ∫ v in Set.Ioi (0 : ℝ), tposW1 d v * v ^ (-s / 2) =
      (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.Gamma ((d : ℝ) + 2 - s / 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => tposW1_mul (d := d) (s := s) hv),
      integral_const_mul, tpos_gamma_int (by linarith)]
    congr 2; ring
  rw [this]


lemma tposW2_mul {v : ℝ} (hv : 0 < v) :
    tposW2 d v * (Real.pi ^ 2 / v) ^ (-((d : ℝ) - s) / 2) =
      (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (-((d : ℝ) - s)) *
        (v ^ ((d : ℝ) + 1 - s / 2) * Real.exp (-v)) := by
  unfold tposW2
  have hπ : 0 < Real.pi := Real.pi_pos
  have e1 : (Real.pi / v) ^ ((d : ℝ) / 2) = Real.pi ^ ((d : ℝ) / 2) * v ^ (-((d : ℝ) / 2)) := by
    rw [Real.div_rpow hπ.le hv.le, Real.rpow_neg hv.le, div_eq_mul_inv]
  have e2 : (Real.pi ^ 2 / v) ^ (-((d : ℝ) - s) / 2) =
      Real.pi ^ (-((d : ℝ) - s)) * v ^ (((d : ℝ) - s) / 2) := by
    rw [Real.div_rpow (by positivity) hv.le, ← Real.rpow_natCast Real.pi 2,
      ← Real.rpow_mul hπ.le, show -((d : ℝ) - s) / 2 = -(((d : ℝ) - s) / 2) by ring,
      Real.rpow_neg hv.le, div_inv_eq_mul]
    congr 2
    push_cast; ring
  have e3 : v ^ ((d : ℝ) + 1) * v ^ (-((d : ℝ) / 2)) * v ^ (((d : ℝ) - s) / 2) =
      v ^ ((d : ℝ) + 1 - s / 2) := by
    rw [← Real.rpow_add hv, ← Real.rpow_add hv]; congr 1; ring
  rw [e1, e2]
  calc (Real.Gamma ((d : ℝ) + 2))⁻¹ * (v ^ ((d : ℝ) + 1) * Real.exp (-v)) *
        (Real.pi ^ ((d : ℝ) / 2) * v ^ (-((d : ℝ) / 2))) *
        (Real.pi ^ (-((d : ℝ) - s)) * v ^ (((d : ℝ) - s) / 2))
      = (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (-((d : ℝ) - s)) *
        ((v ^ ((d : ℝ) + 1) * v ^ (-((d : ℝ) / 2)) * v ^ (((d : ℝ) - s) / 2)) * Real.exp (-v)) := by ring
    _ = _ := by rw [e3]

lemma tpos_Mval (hsd : s < (d : ℝ) - 2) (hs0 : 0 ≤ s) :
    IntegrableOn (fun u : ℝ => u ^ ((d : ℝ) - s - 1) * Whole.phiHatR d u) (Set.Ioi 0) ∧
    ∫ u in Set.Ioi (0 : ℝ), u ^ ((d : ℝ) - s - 1) * Whole.phiHatR d u =
      (1 / 2) * Real.Gamma (((d : ℝ) - s) / 2) * ((Real.Gamma ((d : ℝ) + 2))⁻¹ *
        Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (-((d : ℝ) - s)) * Real.Gamma ((d : ℝ) + 2 - s / 2)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : 0 < (d : ℝ) - s := by linarith
  have hint : IntegrableOn (fun v : ℝ => tposW2 d v * (fun v : ℝ => Real.pi ^ 2 / v) v ^ (-((d : ℝ) - s) / 2))
      (Set.Ioi 0) := by
    have : IntegrableOn (fun v : ℝ => (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2) *
        Real.pi ^ (-((d : ℝ) - s)) * (v ^ ((d : ℝ) + 1 - s / 2) * Real.exp (-v))) (Set.Ioi 0) :=
      (tpos_gamma_integrable (e := (d : ℝ) + 1 - s / 2) (by linarith)).const_mul _
    refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
    exact (tposW2_mul (d := d) (s := s) hv).symm
  have hcm : Measurable (fun v : ℝ => Real.pi ^ 2 / v) := by fun_prop
  obtain ⟨h1, h2⟩ := tpos_mixture_mellin (a := (d : ℝ) - s) ha (W := tposW2 d)
    (c := fun v => Real.pi ^ 2 / v) (fun v hv => tposW2_nonneg hv)
    (fun v hv => by positivity) tposW2_measurable hcm hint
  have e1 : ∀ r : ℝ, Whole.phiHatR d r = ∫ v in Set.Ioi (0 : ℝ), tposW2 d v *
      Real.exp (-(Real.pi ^ 2 / v) * r ^ 2) := tpos_phiHatR_mixture
  simp_rw [← e1] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2]
  have : ∫ v in Set.Ioi (0 : ℝ), tposW2 d v * (Real.pi ^ 2 / v) ^ (-((d : ℝ) - s) / 2) =
      (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (-((d : ℝ) - s)) *
        Real.Gamma ((d : ℝ) + 2 - s / 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => tposW2_mul (d := d) (s := s) hv),
      integral_const_mul, tpos_gamma_int (by linarith)]
    congr 2; ring
  rw [this]


lemma tpos_two_pi (s : ℝ) :
    (2 : ℝ) ^ ((d : ℝ) - s) * (2 * Real.pi) ^ (s - (d : ℝ)) = Real.pi ^ (-((d : ℝ) - s)) := by
  rw [Real.mul_rpow (by norm_num) Real.pi_pos.le, ← mul_assoc, ← Real.rpow_add (by norm_num)]
  have : (d : ℝ) - s + (s - (d : ℝ)) = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]
  congr 1; ring

lemma tpos_K (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    rieszConst d s * (2 * Real.pi) ^ (s - (d : ℝ)) = tScale s * Whole.cPhi d s *
      ((1 / 2) * Real.Gamma (((d : ℝ) - s) / 2) * ((Real.Gamma ((d : ℝ) + 2))⁻¹ *
        Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (-((d : ℝ) - s)) * Real.Gamma ((d : ℝ) + 2 - s / 2))) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hG3 : 0 < Real.Gamma ((d : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  have hG4 : 0 < Real.Gamma ((d : ℝ) + 2 - s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG1 : 0 < Real.Gamma (((d : ℝ) - s) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hπ : 0 < Real.pi := Real.pi_pos
  by_cases hs : s = 0
  · subst hs
    have hc : Whole.cPhi d 0 = 1 := by simp [Whole.cPhi]
    have hts : tScale 0 = 1 := by simp [tScale]
    rw [hc, hts]
    unfold rieszConst
    simp only [if_true]
    have h2 : (2 : ℝ) ^ ((d : ℝ) - 1) * (2 * Real.pi) ^ ((0 : ℝ) - (d : ℝ)) =
        (1 / 2) * Real.pi ^ (-((d : ℝ) - 0)) := by
      rw [Real.mul_rpow (by norm_num) Real.pi_pos.le, ← mul_assoc, ← Real.rpow_add (by norm_num)]
      have : (d : ℝ) - 1 + ((0 : ℝ) - (d : ℝ)) = -1 := by ring
      rw [this, Real.rpow_neg_one]
      have : Real.pi ^ ((0 : ℝ) - (d : ℝ)) = Real.pi ^ (-((d : ℝ) - 0)) := by congr 1; ring
      rw [this]; norm_num
    have e : (2 : ℝ) ^ ((d : ℝ) - 1) * Real.pi ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2) *
        (2 * Real.pi) ^ ((0 : ℝ) - (d : ℝ)) =
        ((2 : ℝ) ^ ((d : ℝ) - 1) * (2 * Real.pi) ^ ((0 : ℝ) - (d : ℝ))) *
          Real.pi ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2) := by ring
    rw [e, h2]
    have : ((d : ℝ) - 0) / 2 = (d : ℝ) / 2 := by ring
    have h4 : (d : ℝ) + 2 - 0 / 2 = (d : ℝ) + 2 := by ring
    rw [this, h4]
    field_simp
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hG2 : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
    have hts : tScale s = s := by simp [tScale, hs]
    have hc : Whole.cPhi d s = (s * ((1 / 2) * Real.Gamma (s / 2) * ((Real.Gamma ((d : ℝ) + 2))⁻¹ *
        Real.Gamma ((d : ℝ) + 2 - s / 2))))⁻¹ := by
      simp only [Whole.cPhi, hs, if_false]
      rw [tpos_Is hs' hsd]
    rw [hts, hc]
    unfold rieszConst
    simp only [hs, if_false]
    have h2 := tpos_two_pi (d := d) s
    have e : (2 : ℝ) ^ ((d : ℝ) - s) * Real.pi ^ ((d : ℝ) / 2) * Real.Gamma (((d : ℝ) - s) / 2) /
        Real.Gamma (s / 2) * (2 * Real.pi) ^ (s - (d : ℝ)) =
        ((2 : ℝ) ^ ((d : ℝ) - s) * (2 * Real.pi) ^ (s - (d : ℝ))) * Real.pi ^ ((d : ℝ) / 2) *
          Real.Gamma (((d : ℝ) - s) / 2) / Real.Gamma (s / 2) := by ring
    rw [e, h2]
    generalize Real.Gamma ((d : ℝ) + 2 - s / 2) = G4 at *
    generalize Real.Gamma (((d : ℝ) - s) / 2) = G1 at *
    generalize Real.Gamma (s / 2) = G2 at *
    generalize Real.Gamma ((d : ℝ) + 2) = G3 at *
    field_simp

/-- The Mellin identity: `ĝ(k) = tScale · c_φ ∫_0^∞ t^{d-s-1} φ̂(t|k|) dt`. -/
lemma tpos_rieszCoeff_mellin (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (k : Lattice d) (hk : k ≠ 0) :
    rieszCoeff d s k = tScale s * Whole.cPhi d s *
      ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (t * ‖Lattice.toEuc k‖) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr : 0 < ‖Lattice.toEuc k‖ := by
    have := one_le_enorm k hk
    exact lt_of_lt_of_le one_pos this
  set r := ‖Lattice.toEuc k‖ with hr_def
  set a : ℝ := (d : ℝ) - s with ha
  have hint := (tpos_Mval (d := d) (s := s) hsd hs0).2
  have hsub := integral_comp_mul_left_Ioi (fun u : ℝ => u ^ (a - 1) * Whole.phiHatR d u) 0 hr
  simp only [mul_zero, smul_eq_mul] at hsub
  have e1 : ∫ t in Set.Ioi (0 : ℝ), t ^ (a - 1) * Whole.phiHatR d (t * r) =
      r ^ (-(a - 1)) * ∫ t in Set.Ioi (0 : ℝ), (r * t) ^ (a - 1) * Whole.phiHatR d (r * t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := ht
    rw [Real.mul_rpow hr.le ht0.le, mul_comm t r]
    have : r ^ (-(a - 1)) * r ^ (a - 1) = 1 := by
      rw [← Real.rpow_add hr]; simp
    calc t ^ (a - 1) * Whole.phiHatR d (r * t)
        = (r ^ (-(a - 1)) * r ^ (a - 1)) * (t ^ (a - 1) * Whole.phiHatR d (r * t)) := by rw [this, one_mul]
      _ = _ := by ring
  have e2 : ∫ t in Set.Ioi (0 : ℝ), t ^ (a - 1) * Whole.phiHatR d (t * r) =
      r ^ (-a) * ∫ u in Set.Ioi (0 : ℝ), u ^ (a - 1) * Whole.phiHatR d u := by
    rw [e1, hsub]
    have : r ^ (-(a - 1)) * r⁻¹ = r ^ (-a) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hr]; congr 1; ring
    rw [← mul_assoc, this]
  have hK := tpos_K (d := d) hs0 hsd
  unfold rieszCoeff
  rw [if_neg hk]
  have hpow : (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) =
      (2 * Real.pi) ^ (s - (d : ℝ)) * r ^ (-a) := by
    have hen : Lattice.enorm k = r := rfl
    rw [hen, Real.mul_rpow (by positivity) hr.le]
    congr 2
    simp only [ha]; ring
  rw [hpow, show ((d : ℝ) - s - 1) = a - 1 by rw [ha], e2, hint]
  calc rieszConst d s * ((2 * Real.pi) ^ (s - (d : ℝ)) * r ^ (-a))
      = (rieszConst d s * (2 * Real.pi) ^ (s - (d : ℝ))) * r ^ (-a) := by ring
    _ = _ := by rw [hK]; ring

end HRS.Commutator.TorusNote
