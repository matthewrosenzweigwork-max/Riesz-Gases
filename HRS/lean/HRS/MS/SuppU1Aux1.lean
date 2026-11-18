import Mathlib

/-!
# U1 aux 1: the Riesz profile `Vs(t) = 1 + W_s(t)`, scaling and mollified-average estimates
(generic finite-dimensional real normed space, Haar measure).
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace HRS.Whole.U1

/-- the scalar profile `1 + W_s(t)`: `1 + t^{-s}` for `s ≠ 0`, `1 + (-log t)_+` for `s = 0`. -/
def u1Vs (s t : ℝ) : ℝ := 1 + (if s = 0 then max (-Real.log t) 0 else t ^ (-s))

lemma u1Vs_ge_one {s : ℝ} {t : ℝ} (ht : 0 ≤ t) : 1 ≤ u1Vs s t := by
  unfold u1Vs
  split_ifs
  · linarith [le_max_right (-Real.log t) 0]
  · have := Real.rpow_nonneg ht (-s); linarith

lemma u1Vs_zero {s : ℝ} : u1Vs s 0 = 1 := by
  unfold u1Vs
  split_ifs with h
  · simp
  · rw [Real.zero_rpow (by simpa using h)]; ring

lemma u1Vs_anti {s : ℝ} (hs : 0 ≤ s) {t t' : ℝ} (ht : 0 < t) (h : t ≤ t') :
    u1Vs s t' ≤ u1Vs s t := by
  unfold u1Vs
  split_ifs with h0
  · have := Real.log_le_log ht h
    have : max (-Real.log t') 0 ≤ max (-Real.log t) 0 := max_le_max (by linarith) le_rfl
    linarith
  · have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
    have : t' ^ (-s) ≤ t ^ (-s) := Real.rpow_le_rpow_of_nonpos ht h (by linarith)
    linarith

lemma u1Vs_submul {s : ℝ} (hs : 0 ≤ s) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    u1Vs s (a * b) ≤ u1Vs s a * u1Vs s b := by
  rcases hb.eq_or_lt with rfl | hb
  · rw [mul_zero, u1Vs_zero, mul_one]; exact u1Vs_ge_one ha.le
  unfold u1Vs
  split_ifs with h0
  · have hl : Real.log (a * b) = Real.log a + Real.log b := Real.log_mul ha.ne' hb.ne'
    have h1 : max (-Real.log (a * b)) 0 ≤ max (-Real.log a) 0 + max (-Real.log b) 0 := by
      apply max_le
      · rw [hl]; linarith [le_max_left (-Real.log a) 0, le_max_left (-Real.log b) 0]
      · linarith [le_max_right (-Real.log a) 0, le_max_right (-Real.log b) 0]
    nlinarith [le_max_right (-Real.log a) 0, le_max_right (-Real.log b) 0]
  · rw [Real.mul_rpow ha.le hb.le]
    have h1 := Real.rpow_nonneg ha.le (-s)
    have h2 := Real.rpow_nonneg hb.le (-s)
    nlinarith

lemma u1Vs_le_two {s : ℝ} (hs : 0 ≤ s) {t : ℝ} (ht : 1 ≤ t) : u1Vs s t ≤ 2 := by
  unfold u1Vs
  split_ifs with h0
  · have : Real.log t ≥ 0 := Real.log_nonneg ht
    have : max (-Real.log t) 0 = 0 := max_eq_right (by linarith)
    linarith
  · have : t ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
    linarith

lemma u1Vs_measurable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (s : ℝ) : Measurable (fun z : E => u1Vs s ‖z‖) := by
  unfold u1Vs
  by_cases h0 : s = 0
  · simp only [h0, ite_true]
    exact measurable_const.add ((Real.measurable_log.comp measurable_norm).neg.max measurable_const)
  · simp only [h0, ite_false]
    exact measurable_const.add (measurable_norm.pow_const _)

/-- for `t ∈ (0,1)`: `Vs t ≤ C t^{-κ}` when `s ≤ κ`, `κ > 0`. -/
lemma u1Vs_le_rpow {s κ : ℝ} (hs : 0 ≤ s) (hsκ : s ≤ κ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t < 1 → u1Vs s t ≤ C * t ^ (-κ) := by
  refine ⟨2 + 1 / κ, by positivity, fun t ht0 ht1 => ?_⟩
  have h1 : (1 : ℝ) ≤ t ^ (-κ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1.le (by linarith)
  unfold u1Vs
  split_ifs with h0
  · have hl : -Real.log t = (1 / κ) * Real.log (t ^ (-κ)) := by
      rw [Real.log_rpow ht0]; field_simp
    have hl2 : Real.log (t ^ (-κ)) ≤ t ^ (-κ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have hmax : max (-Real.log t) 0 ≤ (1 / κ) * t ^ (-κ) := by
      apply max_le
      · rw [hl]; have : (0:ℝ) ≤ 1 / κ := by positivity
        nlinarith
      · positivity
    nlinarith [one_div_pos.mpr hκ]
  · have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
    have : t ^ (-s) ≤ t ^ (-κ) := Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le (by linarith)
    nlinarith [one_div_pos.mpr hκ]


section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma u1_lintegral_ball_scale {a : ℝ} (ha : 0 < a) (g : E → ℝ≥0∞) :
    ∫⁻ x in ball (0:E) a, g x ∂μ
      = ENNReal.ofReal (a ^ Module.finrank ℝ E) * ∫⁻ x in ball (0:E) 1, g (a • x) ∂μ := by
  have hT : MeasurableEmbedding (fun x : E => a • x) :=
    (Homeomorph.smul (Units.mk0 a ha.ne')).measurableEmbedding
  have hpre : (fun x : E => a • x) ⁻¹' ball (0:E) a = ball 0 1 := by
    ext x
    simp only [mem_preimage, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hmap := Measure.map_addHaar_smul μ ha.ne'
  have key : ∫⁻ x in (fun x : E => a • x) ⁻¹' ball (0:E) a, g (a • x) ∂μ
      = ∫⁻ y in ball (0:E) a, g y ∂(Measure.map (fun x : E => a • x) μ) := by
    rw [hT.restrict_map, hT.lintegral_map]
  rw [hpre, hmap, Measure.restrict_smul, lintegral_smul_measure] at key
  rw [key, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- the local `r`-th power integral of the profile on the unit ball. -/
def u1J (s r : ℝ) : ℝ≥0∞ := ∫⁻ x in ball (0:E) 1, ENNReal.ofReal (u1Vs s ‖x‖ ^ r) ∂μ

lemma u1_integrableOn_Vs_pow {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (hrs : r * s < (Module.finrank ℝ E : ℝ)) :
    IntegrableOn (fun x : E => u1Vs s ‖x‖ ^ r) (ball (0:E) 1) μ := by
  have hd0 : (0:ℝ) < Module.finrank ℝ E := lt_of_le_of_lt (by positivity) hrs
  have hd : 1 ≤ Module.finrank ℝ E := by exact_mod_cast hd0
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set κ : ℝ := (s + (Module.finrank ℝ E : ℝ) / r) / 2 with hκ
  have hdr : r * s < (Module.finrank ℝ E : ℝ) := hrs
  have hsd : s < (Module.finrank ℝ E : ℝ) / r := by rw [lt_div_iff₀ hr]; linarith
  have hκ0 : 0 < κ := by
    have : 0 < (Module.finrank ℝ E : ℝ) / r := div_pos hd0 hr
    rw [hκ]; linarith
  have hsκ : s ≤ κ := by rw [hκ]; linarith
  have hrκ : r * κ < (Module.finrank ℝ E : ℝ) := by
    have : r * κ = (r * s + (Module.finrank ℝ E : ℝ)) / 2 := by
      rw [hκ]; field_simp
    rw [this]; linarith
  obtain ⟨C, hC0, hC⟩ := u1Vs_le_rpow hs hsκ hκ0
  refine integrableOn_ball_of_norm_le_rpow (C := C ^ r) (α := r * κ) (r := 1) hd hrκ ?_ ?_
  · have hnull : ∀ᵐ x ∂μ, x ≠ (0:E) := by
      have : μ {(0:E)} = 0 := measure_singleton 0
      simpa [ae_iff] using this
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hnull] with x hx hx0
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hxl : ‖x‖ < 1 := by simpa using hx
    have h1 := hC ‖x‖ hxn hxl
    have h0 : 0 ≤ u1Vs s ‖x‖ := by linarith [u1Vs_ge_one (s := s) hxn.le]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 r)]
    calc u1Vs s ‖x‖ ^ r ≤ (C * ‖x‖ ^ (-κ)) ^ r := Real.rpow_le_rpow h0 h1 hr.le
      _ = C ^ r * ‖x‖ ^ (-(r * κ)) := by
        rw [Real.mul_rpow hC0 (Real.rpow_nonneg hxn.le _), ← Real.rpow_mul hxn.le]
        congr 2; ring
  · exact ((u1Vs_measurable (E := E) s).pow_const r).aestronglyMeasurable

lemma u1J_lt_top {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (hrs : r * s < (Module.finrank ℝ E : ℝ)) : u1J μ s r < ⊤ := by
  have := u1_integrableOn_Vs_pow μ hs hr hrs
  have h2 := this.2
  unfold u1J
  have h3 : ∀ x : E, ENNReal.ofReal |u1Vs s ‖x‖ ^ r| = ENNReal.ofReal (u1Vs s ‖x‖ ^ r) := fun x => by
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith [u1Vs_ge_one (s := s) (t := ‖x‖) (norm_nonneg x)]) r)]
  simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs, h3] at h2
  exact h2



lemma u1_lintegral_Vs_ball {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x in ball (0:E) a, ENNReal.ofReal (u1Vs s ‖x‖ ^ r) ∂μ
      ≤ ENNReal.ofReal (a ^ Module.finrank ℝ E * u1Vs s a ^ r) * u1J μ s r := by
  rw [u1_lintegral_ball_scale μ ha, ENNReal.ofReal_mul (by positivity), mul_assoc]
  refine mul_le_mul_right ?_ _
  unfold u1J
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  have h1 : 0 < u1Vs s a := by linarith [u1Vs_ge_one (s := s) ha.le]
  have h2 : 0 < u1Vs s ‖x‖ := by linarith [u1Vs_ge_one (s := s) (norm_nonneg x)]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg h1.le r)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.mul_rpow h1.le h2.le]
  apply Real.rpow_le_rpow _ _ hr.le
  · linarith [u1Vs_ge_one (s := s) (norm_nonneg (a • x))]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact u1Vs_submul hs ha (norm_nonneg x)

/-- the mollified-average estimate: `∫_{|t| ≤ ε} Vs(|T t|) dt ≤ K ε^d Vs(|w|)` for a measure preserving
embedding `T` moving norms by at most `ε` (e.g. `t ↦ w + t`, `t ↦ w - t`). -/
lemma u1_avg_estimate {s : ℝ} (hs : 0 ≤ s) (hsd : s < (Module.finrank ℝ E : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : E → E) (w : E) (ε : ℝ), 0 < ε → w ≠ 0 →
      MeasurePreserving T μ μ → MeasurableEmbedding T → (∀ t : E, ‖t‖ ≤ ε → |‖T t‖ - ‖w‖| ≤ ε) →
      ∫⁻ t in closedBall (0:E) ε, ENNReal.ofReal (u1Vs s ‖T t‖) ∂μ
        ≤ ENNReal.ofReal (K * ε ^ Module.finrank ℝ E * u1Vs s ‖w‖) := by
  have hd0 : (0:ℝ) < Module.finrank ℝ E := lt_of_le_of_lt hs hsd
  have hd : 1 ≤ Module.finrank ℝ E := by exact_mod_cast hd0
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hJ : u1J μ s 1 < ⊤ := u1J_lt_top μ hs one_pos (by simpa using hsd)
  set m1 : ℝ := (μ (ball (0:E) 1)).toReal with hm1
  have hm1' : μ (ball (0:E) 1) = ENNReal.ofReal m1 := by
    rw [hm1, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  have hm1nn : 0 ≤ m1 := ENNReal.toReal_nonneg
  set J1 : ℝ := (u1J μ s 1).toReal with hJ1
  have hJ1' : u1J μ s 1 = ENNReal.ofReal J1 := by rw [hJ1, ENNReal.ofReal_toReal hJ.ne]
  have hJ1nn : 0 ≤ J1 := ENNReal.toReal_nonneg
  have hv12 : 0 ≤ u1Vs s (1/2) := by linarith [u1Vs_ge_one (s := s) (t := 1/2) (by norm_num)]
  refine ⟨max (m1 * u1Vs s (1/2)) (3 ^ Module.finrank ℝ E * J1), by positivity, ?_⟩
  intro T w ε hε hw hTm hTe hTn
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hVw : 1 ≤ u1Vs s ‖w‖ := u1Vs_ge_one (norm_nonneg w)
  by_cases hcase : 2 * ε ≤ ‖w‖
  · -- far from the origin
    have hpt : ∀ t ∈ closedBall (0:E) ε,
        ENNReal.ofReal (u1Vs s ‖T t‖) ≤ ENNReal.ofReal (u1Vs s (1/2) * u1Vs s ‖w‖) := by
      intro t ht
      have ht' : ‖t‖ ≤ ε := by simpa using ht
      have h1 := hTn t ht'
      have h2 : ‖w‖ / 2 ≤ ‖T t‖ := by
        have := (abs_le.mp h1).1; linarith
      apply ENNReal.ofReal_le_ofReal
      calc u1Vs s ‖T t‖ ≤ u1Vs s (‖w‖ / 2) := u1Vs_anti hs (by positivity) h2
        _ = u1Vs s ((1/2) * ‖w‖) := by congr 1; ring
        _ ≤ _ := u1Vs_submul hs (by norm_num) (norm_nonneg w)
    calc ∫⁻ t in closedBall (0:E) ε, ENNReal.ofReal (u1Vs s ‖T t‖) ∂μ
        ≤ ∫⁻ t in closedBall (0:E) ε, ENNReal.ofReal (u1Vs s (1/2) * u1Vs s ‖w‖) ∂μ :=
          setLIntegral_mono' measurableSet_closedBall hpt
      _ = ENNReal.ofReal (ε ^ Module.finrank ℝ E) * ENNReal.ofReal m1 *
            ENNReal.ofReal (u1Vs s (1/2) * u1Vs s ‖w‖) := by
          rw [setLIntegral_const, Measure.addHaar_closedBall μ _ hε.le, hm1', mul_comm]
      _ ≤ ENNReal.ofReal (max (m1 * u1Vs s (1/2)) (3 ^ Module.finrank ℝ E * J1) *
            ε ^ Module.finrank ℝ E * u1Vs s ‖w‖) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hε' : 0 ≤ ε ^ Module.finrank ℝ E := by positivity
          have := le_max_left (m1 * u1Vs s (1/2)) (3 ^ Module.finrank ℝ E * J1)
          nlinarith [mul_nonneg hε' (sub_nonneg.mpr this), mul_nonneg hm1nn hv12]
  · -- close to the origin
    replace hcase := not_le.mp hcase
    have hsub : closedBall (0:E) ε ⊆ T ⁻¹' ball (0:E) (3 * ε) := by
      intro t ht
      have ht' : ‖t‖ ≤ ε := by simpa using ht
      have h1 := hTn t ht'
      have := (abs_le.mp h1).2
      simp only [mem_preimage, mem_ball_zero_iff]; linarith
    calc ∫⁻ t in closedBall (0:E) ε, ENNReal.ofReal (u1Vs s ‖T t‖) ∂μ
        ≤ ∫⁻ t in T ⁻¹' ball (0:E) (3 * ε), ENNReal.ofReal (u1Vs s ‖T t‖) ∂μ :=
          lintegral_mono_set hsub
      _ = ∫⁻ y in ball (0:E) (3 * ε), ENNReal.ofReal (u1Vs s ‖y‖) ∂μ :=
          hTm.setLIntegral_comp_preimage_emb hTe (fun y => ENNReal.ofReal (u1Vs s ‖y‖)) _
      _ ≤ ENNReal.ofReal ((3 * ε) ^ Module.finrank ℝ E * u1Vs s (3 * ε)) * u1J μ s 1 := by
          have := u1_lintegral_Vs_ball μ hs one_pos (a := 3 * ε) (by positivity)
          simpa [Real.rpow_one] using this
      _ ≤ ENNReal.ofReal (max (m1 * u1Vs s (1/2)) (3 ^ Module.finrank ℝ E * J1) *
            ε ^ Module.finrank ℝ E * u1Vs s ‖w‖) := by
          have hv3 : 0 ≤ u1Vs s (3 * ε) := by
            linarith [u1Vs_ge_one (s := s) (t := 3 * ε) (by positivity)]
          rw [hJ1', ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hv3)]
          apply ENNReal.ofReal_le_ofReal
          have h3 : u1Vs s (3 * ε) ≤ u1Vs s ‖w‖ := u1Vs_anti hs hwn (by linarith)
          have hε' : 0 ≤ ε ^ Module.finrank ℝ E := by positivity
          have h4 := le_max_right (m1 * u1Vs s (1/2)) (3 ^ Module.finrank ℝ E * J1)
          rw [mul_pow]
          calc 3 ^ Module.finrank ℝ E * ε ^ Module.finrank ℝ E * u1Vs s (3 * ε) * J1
              ≤ 3 ^ Module.finrank ℝ E * ε ^ Module.finrank ℝ E * u1Vs s ‖w‖ * J1 := by
                gcongr
            _ = (3 ^ Module.finrank ℝ E * J1) * ε ^ Module.finrank ℝ E * u1Vs s ‖w‖ := by ring
            _ ≤ _ := by gcongr

end Haar

end HRS.Whole.U1
