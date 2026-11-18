import HRS.MC.CepH3C2

/-!
# Packet CEPH3, part C3: Donsker–Varadhan form of `F` and lower semicontinuity on a compact space
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH3

open HRS

variable {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]

/-- The Donsker–Varadhan functional. -/
def h3c_T (ν m : Measure α) (φ : C(α, ℝ)) : ℝ :=
  ∫ x, φ x ∂ν - Real.log (∫ x, Real.exp (φ x) ∂m)

lemma h3c_exp_integral_pos (m : Measure α) [IsFiniteMeasure m] (h0 : m univ ≠ 0) (φ : C(α, ℝ)) :
    0 < ∫ x, Real.exp (φ x) ∂m := by
  haveI : NeZero m := ⟨fun h => h0 (by simp [h])⟩
  refine integral_exp_pos ?_
  exact (Real.continuous_exp.comp φ.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Each Donsker–Varadhan term is below `F`. -/
theorem h3c_T_le_F (ν m : Measure α) [IsProbabilityMeasure ν] [IsFiniteMeasure m] (φ : C(α, ℝ)) :
    ((h3c_T ν m φ : ℝ) : EReal) ≤ h3c_F ν m := by
  by_cases h0 : m univ = 0
  · have hm : m = 0 := Measure.measure_univ_eq_zero.mp h0
    subst hm
    unfold h3c_F
    simp [klDiv_zero_right]
  have hc := h3c_normalised_isProb m h0
  have hDV := b15b_klDiv_eq_iSup ν ((m univ)⁻¹ • m)
  have hle : ENNReal.ofReal (∫ x, φ x ∂ν - Real.log (∫ x, Real.exp (φ x) ∂((m univ)⁻¹ • m))) ≤
      klDiv ν ((m univ)⁻¹ • m) := by
    rw [hDV]
    exact le_iSup (fun φ : C(α, ℝ) => ENNReal.ofReal (∫ x, φ x ∂ν -
      Real.log (∫ x, Real.exp (φ x) ∂((m univ)⁻¹ • m)))) φ
  have hint : ∫ x, Real.exp (φ x) ∂((m univ)⁻¹ • m) = ((m univ)⁻¹).toReal * ∫ x, Real.exp (φ x) ∂m := by
    rw [integral_smul_measure]; rfl
  have hpos := h3c_exp_integral_pos m h0 φ
  have hcpos : 0 < (m univ).toReal := ENNReal.toReal_pos h0 (measure_ne_top m _)
  have hlog : Real.log (∫ x, Real.exp (φ x) ∂((m univ)⁻¹ • m)) =
      Real.log (∫ x, Real.exp (φ x) ∂m) - Real.log (m univ).toReal := by
    rw [hint, ENNReal.toReal_inv, Real.log_mul (by positivity) hpos.ne', Real.log_inv]; ring
  rw [hlog] at hle
  unfold h3c_F h3c_T
  have h2 : (((∫ x, φ x ∂ν - (Real.log (∫ x, Real.exp (φ x) ∂m) - Real.log (m univ).toReal) : ℝ)) : EReal)
      ≤ ((ENNReal.ofReal (∫ x, φ x ∂ν - (Real.log (∫ x, Real.exp (φ x) ∂m) - Real.log (m univ).toReal)) :
        ℝ≥0∞) : EReal) := by
    rw [EReal.coe_ennreal_ofReal]; exact_mod_cast le_max_left _ _
  have h3 := h2.trans (by exact_mod_cast hle : ((ENNReal.ofReal (∫ x, φ x ∂ν - (Real.log (∫ x, Real.exp (φ x) ∂m) -
      Real.log (m univ).toReal)) : ℝ≥0∞) : EReal) ≤ (klDiv ν ((m univ)⁻¹ • m) : EReal))
  have h4 := EReal.sub_le_sub h3 (le_refl (((Real.log (m univ).toReal : ℝ)) : EReal))
  have e : (((∫ x, φ x ∂ν - (Real.log (∫ x, Real.exp (φ x) ∂m) - Real.log (m univ).toReal) : ℝ)) : EReal)
      - ((Real.log (m univ).toReal : ℝ) : EReal) = ((∫ x, φ x ∂ν - Real.log (∫ x, Real.exp (φ x) ∂m) : ℝ) : EReal) := by
    rw [← EReal.coe_sub]; congr 1; ring
  rwa [e] at h4

/-- `F` is the supremum of the Donsker–Varadhan terms. -/
theorem h3c_F_le_iSup (ν m : Measure α) [IsProbabilityMeasure ν] [IsFiniteMeasure m] (h0 : m univ ≠ 0) :
    h3c_F ν m ≤ ⨆ φ : C(α, ℝ), ((h3c_T ν m φ : ℝ) : EReal) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  have hnorm := h3c_normalised_isProb m h0
  have hcpos : 0 < (m univ).toReal := ENNReal.toReal_pos h0 (measure_ne_top m _)
  set L := Real.log (m univ).toReal with hL
  -- the zero function gives `-L ≤ c`
  have hT0 : h3c_T ν m 0 = -L := by
    simp [h3c_T, hL, measureReal_def]
  have hLc : -L ≤ c := by
    have : ((h3c_T ν m 0 : ℝ) : EReal) ≤ ⨆ φ : C(α, ℝ), ((h3c_T ν m φ : ℝ) : EReal) :=
      le_iSup (fun φ : C(α, ℝ) => ((h3c_T ν m φ : ℝ) : EReal)) 0
    have h2 := this.trans hc1.le
    rw [hT0] at h2
    exact_mod_cast h2
  have hbound : ∀ φ : C(α, ℝ), ∫ x, φ x ∂ν - Real.log (∫ x, Real.exp (φ x) ∂((m univ)⁻¹ • m)) ≤ c + L := by
    intro φ
    have hint : ∫ x, Real.exp (φ x) ∂((m univ)⁻¹ • m) =
        ((m univ)⁻¹).toReal * ∫ x, Real.exp (φ x) ∂m := by
      rw [integral_smul_measure]; rfl
    have hpos := h3c_exp_integral_pos m h0 φ
    have hlog : Real.log (∫ x, Real.exp (φ x) ∂((m univ)⁻¹ • m)) =
        Real.log (∫ x, Real.exp (φ x) ∂m) - L := by
      rw [hint, ENNReal.toReal_inv, Real.log_mul (by positivity) hpos.ne', Real.log_inv]; ring
    rw [hlog]
    have h1 : ((h3c_T ν m φ : ℝ) : EReal) ≤ (c : EReal) :=
      (le_iSup (fun φ : C(α, ℝ) => ((h3c_T ν m φ : ℝ) : EReal)) φ).trans hc1.le
    have h2 : h3c_T ν m φ ≤ c := by exact_mod_cast h1
    unfold h3c_T at h2
    linarith
  have hk : klDiv ν ((m univ)⁻¹ • m) ≤ ENNReal.ofReal (c + L) := by
    rw [b15b_klDiv_eq_iSup ν ((m univ)⁻¹ • m)]
    exact iSup_le fun φ => ENNReal.ofReal_le_ofReal (hbound φ)
  have hA : h3c_F ν m ≤ (c : EReal) := by
    unfold h3c_F
    have h1 : ((klDiv ν ((m univ)⁻¹ • m) : ℝ≥0∞) : EReal) ≤ ((ENNReal.ofReal (c + L) : ℝ≥0∞) : EReal) := by
      exact_mod_cast hk
    rw [EReal.coe_ennreal_ofReal] at h1
    have h2 := EReal.sub_le_sub h1 (le_refl ((L : ℝ) : EReal))
    refine h2.trans ?_
    rcases le_total (c + L) 0 with h | h
    · rw [max_eq_right (by exact_mod_cast h)]
      norm_cast
      linarith
    · rw [max_eq_left (by exact_mod_cast h), ← EReal.coe_sub]
      exact_mod_cast le_of_eq (by ring)
  exact absurd hc2 (not_lt.mpr hA)

/-- **Lower semicontinuity of `F`** along narrowly convergent probability measures and
narrowly convergent finite reference measures on a compact metric space. -/
theorem h3c_F_liminf (ν m : Measure α) [IsProbabilityMeasure ν] [IsFiniteMeasure m] (h0 : m univ ≠ 0)
    (νn mn : ℕ → Measure α) [∀ n, IsProbabilityMeasure (νn n)] [∀ n, IsFiniteMeasure (mn n)]
    (hν : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(νn n)) atTop (𝓝 (∫ x, φ x ∂ν)))
    (hm : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(mn n)) atTop (𝓝 (∫ x, φ x ∂m))) :
    h3c_F ν m ≤ liminf (fun n => h3c_F (νn n) (mn n)) atTop := by
  refine (h3c_F_le_iSup ν m h0).trans (iSup_le fun φ => ?_)
  have hexp : Continuous fun x => Real.exp (φ x) := Real.continuous_exp.comp φ.continuous
  have h1 := hν φ φ.continuous
  have h2 := hm _ hexp
  have ht : Tendsto (fun n => h3c_T (νn n) (mn n) φ) atTop (𝓝 (h3c_T ν m φ)) :=
    h1.sub (h2.log (h3c_exp_integral_pos m h0 φ).ne')
  have ht' : Tendsto (fun n => ((h3c_T (νn n) (mn n) φ : ℝ) : EReal)) atTop
      (𝓝 ((h3c_T ν m φ : ℝ) : EReal)) := (EReal.continuous_coe_iff.2 continuous_id).tendsto _ |>.comp ht
  rw [← ht'.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n => h3c_T_le_F (νn n) (mn n) φ)

end HRS.MC.CepH3
