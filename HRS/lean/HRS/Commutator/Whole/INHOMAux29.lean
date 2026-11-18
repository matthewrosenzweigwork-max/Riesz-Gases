import HRS.Commutator.Whole.INHOMAux28

/-!
# CMX-INHOM auxiliary 29: density of real Schwartz functions in real `L²`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma inhom_int_sq_le {f : Euc d → ℝ} (hf : MemLp f 2 volume) {ε : ℝ} (hε : 0 ≤ ε)
    (h : eLpNorm f 2 volume ≤ ENNReal.ofReal ε) : ∫ x, f x ^ 2 ≤ ε ^ 2 := by
  have h1 := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top
  rw [h1] at h
  have h2 := (ENNReal.ofReal_le_ofReal_iff hε).1 h
  simp only [ENNReal.toReal_ofNat] at h2
  set X : ℝ := ∫ x, ‖f x‖ ^ (2 : ℝ) with hX
  have hnn : 0 ≤ X := integral_nonneg fun x => by positivity
  have h3 : X = (X ^ ((2 : ℝ)⁻¹)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]; norm_num
  have h4 : X ≤ ε ^ 2 := by
    calc X = (X ^ ((2 : ℝ)⁻¹)) ^ 2 := h3
      _ ≤ ε ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hnn _) h2 2
  have h5 : ∫ x, f x ^ 2 = X := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [h5]; exact h4

lemma inhom_real_schwartz_approx {a : Euc d → ℝ} (ha : MemLp a 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : SchwartzMap (Euc d) ℂ) (a' : Euc d → ℝ), (∀ x, φ x = ((a' x : ℝ) : ℂ)) ∧
      ∫ x, (a x - a' x) ^ 2 ≤ ε ^ 2 := by
  have hmem : MemLp (fun x => ((a x : ℝ) : ℂ)) (ENNReal.ofReal 2) volume := by
    have : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by norm_num
    rw [this]; exact ha.ofReal
  obtain ⟨s, hs⟩ := PROD.prod_schwartz_dense (d := d) (p := 2) (by norm_num) hmem hε
  set φ : SchwartzMap (Euc d) ℂ := s.postcompCLM (𝕜 := ℝ) (Complex.ofRealCLM.comp Complex.reCLM) with hφ
  set a' : Euc d → ℝ := fun x => (s x).re with ha'
  have hφx : ∀ x, φ x = ((a' x : ℝ) : ℂ) := by
    intro x
    simp [hφ, ha', SchwartzMap.postcompCLM_apply]
  refine ⟨φ, a', hφx, ?_⟩
  obtain ⟨ha'c, -, -, -, ha'2⟩ := inhom_schw_props hφx
  have ha'm : MemLp a' 2 volume := (memLp_two_iff_integrable_sq ha'c.aestronglyMeasurable).2 ha'2
  have hsub : MemLp (fun x => a x - a' x) 2 volume := ha.sub ha'm
  refine inhom_int_sq_le hsub hε.le ?_
  refine le_trans ?_ (by simpa using hs)
  refine eLpNorm_mono_ae hsub.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have h1 : a x - a' x = -((s x - ((a x : ℝ) : ℂ)).re) := by simp [ha']
  rw [h1, norm_neg, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

/-- the limit step: `x ≤ P (R+η)² + A η` for all small `η` implies `x ≤ P R²`. -/
lemma inhom_limit_aux {x P R A : ℝ} (hP : 0 ≤ P) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (h : ∀ η : ℝ, 0 < η → η ≤ 1 → x ≤ P * (R + η) ^ 2 + A * η) : x ≤ P * R ^ 2 := by
  by_contra hcon
  push Not at hcon
  set δ : ℝ := x - P * R ^ 2 with hδ
  have hδ0 : 0 < δ := by linarith
  set B : ℝ := P * (2 * R + 1) + A + 1 with hB
  have hB0 : 0 < B := by positivity
  set η : ℝ := min 1 (δ / (2 * B)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ δ / (2 * B) := min_le_right _ _
  have h1 := h η hη0 hη1
  have h2 : η * B ≤ δ / 2 := by
    calc η * B ≤ δ / (2 * B) * B := by gcongr
      _ = δ / 2 := by field_simp
  nlinarith [mul_nonneg hP (sq_nonneg η), mul_le_mul_of_nonneg_left hη1 hη0.le,
    mul_nonneg hP hη0.le, mul_nonneg hR hη0.le, mul_nonneg hA hη0.le]

end HRS.Commutator.Whole
