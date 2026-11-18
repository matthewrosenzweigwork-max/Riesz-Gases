import HRS.Commutator.Whole.XLIAux34

/-!
# X-LI part 35: Marcinkiewicz interpolation for square functions of Hörmander kernel families
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma cheb_L4 {K : ℤ → 𝔼 → ℂ} (hKm : ∀ j, Measurable (K j)) {C4 : ℝ≥0}
    (hC4 : ∀ F : 𝔼 → ℂ, Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) →
      ∫⁻ x, sqS (fun j => cv (K j) F) x ^ (2 : ℝ) ≤ C4 * ∫⁻ x, ‖F x‖ₑ ^ (2 * (2 : ℝ)))
    {g : 𝔼 → ℂ} (hgm : Measurable g) (hgi : Integrable g) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hgb : ∀ x, ‖g x‖ₑ ≤ M) (t : ℝ≥0∞) :
    t ^ 2 * volume {x | t < sqS (fun j => cv (K j) g) x} ≤
      C4 * ∫⁻ x, ‖g x‖ₑ ^ (2 * (2 : ℝ)) := by
  have h1 := hC4 g hgm hgi M hM hgb
  have hmeas : Measurable (fun x => sqS (fun j => cv (K j) g) x ^ (2 : ℝ)) :=
    (sqS_measurable (fun j => measurable_cv (hKm j) hgm)).pow_const _
  have hcheb := mul_meas_ge_le_lintegral₀ (μ := (volume : Measure 𝔼)) hmeas.aemeasurable (t ^ 2)
  have hsub : {x | t < sqS (fun j => cv (K j) g) x} ⊆
      {x | t ^ 2 ≤ sqS (fun j => cv (K j) g) x ^ (2 : ℝ)} := by
    intro x hx
    have : t ≤ sqS (fun j => cv (K j) g) x := hx.le
    show t ^ 2 ≤ _
    rw [ENNReal.rpow_two]; gcongr
  calc t ^ 2 * volume {x | t < sqS (fun j => cv (K j) g) x}
      ≤ t ^ 2 * volume {x | t ^ 2 ≤ sqS (fun j => cv (K j) g) x ^ (2 : ℝ)} :=
        mul_le_mul_right (measure_mono hsub) _
    _ ≤ ∫⁻ x, sqS (fun j => cv (K j) g) x ^ (2 : ℝ) := hcheb
    _ ≤ _ := h1

/-- the Marcinkiewicz distribution estimate -/
lemma dist_estimate {K : ℤ → 𝔼 → ℂ} (hKm : ∀ j, Measurable (K j)) (hKi : ∀ j, Integrable (K j)) {C4 : ℝ≥0}
    (hC4 : ∀ F : 𝔼 → ℂ, Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) →
      ∫⁻ x, sqS (fun j => cv (K j) F) x ^ (2 : ℝ) ≤ C4 * ∫⁻ x, ‖F x‖ₑ ^ (2 * (2 : ℝ)))
    {Cw : ℝ≥0∞}
    (hweak : ∀ F : 𝔼 → ℂ, Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) → ∀ l : ℝ≥0∞, l ≠ 0 → l ≠ ⊤ →
        l * volume {x | l ^ 2 < sqS (fun j => cv (K j) F) x} ≤ Cw * ∫⁻ x, ‖F x‖ₑ)
    {F : 𝔼 → ℂ} (hF : Measurable F) (hFi : Integrable F) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hFB : ∀ x, ‖F x‖ₑ ≤ B) {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal t ^ 2 < sqS (fun j => cv (K j) F) x} ≤
      (16 * C4) * (ENNReal.ofReal (t ^ (-4 : ℝ)) *
        ∫⁻ x, (if ‖F x‖ₑ ≤ ENNReal.ofReal t then ‖F x‖ₑ ^ 4 else 0)) +
      (2 * Cw) * (ENNReal.ofReal (t ^ (-1 : ℝ)) *
        ∫⁻ x, (if ENNReal.ofReal t < ‖F x‖ₑ then ‖F x‖ₑ else 0)) := by
  set l : ℝ≥0∞ := ENNReal.ofReal t with hl
  set q : ℝ≥0∞ := ENNReal.ofReal (t / 2) with hq
  have hlq : l = 2 * q := by
    rw [hl, hq, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  have hq0 : q ≠ 0 := by
    rw [hq]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  set S₁ : Set 𝔼 := {x | ‖F x‖ₑ ≤ l} with hS₁
  have hS₁m : MeasurableSet S₁ := measurableSet_le hF.enorm measurable_const
  set F₁ : 𝔼 → ℂ := S₁.indicator F with hF₁
  set F₂ : 𝔼 → ℂ := S₁ᶜ.indicator F with hF₂
  have hF₁m : Measurable F₁ := hF.indicator hS₁m
  have hF₂m : Measurable F₂ := hF.indicator hS₁m.compl
  have hF₁i : Integrable F₁ := hFi.indicator hS₁m
  have hF₂i : Integrable F₂ := hFi.indicator hS₁m.compl
  have hF₁B : ∀ x, ‖F₁ x‖ₑ ≤ B := fun x => by
    by_cases hx : x ∈ S₁
    · rw [hF₁, Set.indicator_of_mem hx]; exact hFB x
    · rw [hF₁, Set.indicator_of_notMem hx]; simp
  have hF₂B : ∀ x, ‖F₂ x‖ₑ ≤ B := fun x => by
    by_cases hx : x ∈ S₁ᶜ
    · rw [hF₂, Set.indicator_of_mem hx]; exact hFB x
    · rw [hF₂, Set.indicator_of_notMem hx]; simp
  have hnorm_le : ∀ (z : ℂ), ‖z‖ₑ ≤ B → ‖z‖ ≤ B.toReal := fun z h => by
    rw [← ofReal_norm] at h; exact (ENNReal.ofReal_le_iff_le_toReal hB).1 h
  have hcv : ∀ j x, cv (K j) F x = cv (K j) F₁ x + cv (K j) F₂ x := by
    intro j x
    have hFe : F = fun y => F₁ y + F₂ y := by
      funext y; rw [hF₁, hF₂]
      have := congrFun (Set.indicator_self_add_compl S₁ F) y
      simpa using this.symm
    rw [hFe]
    exact cv_add_of_bdd (hKi j) hF₁m hF₂m (fun y => hnorm_le _ (hF₁B y))
      (fun y => hnorm_le _ (hF₂B y)) x
  have hsub : {x | l ^ 2 < sqS (fun j => cv (K j) F) x} ⊆
      {x | q ^ 2 < sqS (fun j => cv (K j) F₁) x} ∪ {x | q ^ 2 < sqS (fun j => cv (K j) F₂) x} := by
    intro x hx
    by_contra hcon
    simp only [mem_union, mem_setOf_eq, not_or, not_lt] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have := sqS_add_le (fun j => cv (K j) F) (fun j => cv (K j) F₁) (fun j => cv (K j) F₂) hcv x
    have h3 : sqS (fun j => cv (K j) F) x ≤ l ^ 2 := by
      calc sqS (fun j => cv (K j) F) x ≤ 2 * sqS (fun j => cv (K j) F₁) x +
            2 * sqS (fun j => cv (K j) F₂) x := this
        _ ≤ 2 * q ^ 2 + 2 * q ^ 2 := by gcongr
        _ = l ^ 2 := by rw [hlq]; ring
    exact absurd hx (not_lt.2 h3)
  -- the two pieces
  have hA1 : q ^ 4 * volume {x | q ^ 2 < sqS (fun j => cv (K j) F₁) x} ≤
      C4 * ∫⁻ x, (if ‖F x‖ₑ ≤ l then ‖F x‖ₑ ^ 4 else 0) := by
    have h := cheb_L4 hKm hC4 hF₁m hF₁i hB hF₁B (q ^ 2)
    rw [show (q ^ 2) ^ 2 = q ^ 4 by ring] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ S₁
    · rw [hF₁, Set.indicator_of_mem hx, if_pos (show ‖F x‖ₑ ≤ l from hx)]
      rw [show (2 * (2 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    · rw [hF₁, Set.indicator_of_notMem hx, if_neg (show ¬ ‖F x‖ₑ ≤ l from hx)]
      simp
  have hA2 : q * volume {x | q ^ 2 < sqS (fun j => cv (K j) F₂) x} ≤
      Cw * ∫⁻ x, (if l < ‖F x‖ₑ then ‖F x‖ₑ else 0) := by
    have h := hweak F₂ hF₂m hF₂i B hB hF₂B q hq0 hqt
    refine h.trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ S₁
    · have : ¬ l < ‖F x‖ₑ := not_lt.2 hx
      rw [hF₂, Set.indicator_of_notMem (by simpa using hx), if_neg this]; simp
    · have : l < ‖F x‖ₑ := not_le.1 hx
      rw [hF₂, Set.indicator_of_mem (by simpa using hx), if_pos this]
  have e4 : ENNReal.ofReal (t ^ (-4 : ℝ)) * 16 * q ^ 4 = 1 := by
    rw [hq, ← ENNReal.ofReal_pow (by positivity), show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← ENNReal.ofReal_mul (by positivity)]
    have : t ^ (-4 : ℝ) * 16 * (t / 2) ^ 4 = 1 := by
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_natCast]
      field_simp
      norm_num
    rw [this]; simp
  have e1 : ENNReal.ofReal (t ^ (-1 : ℝ)) * 2 * q = 1 := by
    rw [hq, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← ENNReal.ofReal_mul (by positivity)]
    have : t ^ (-1 : ℝ) * 2 * (t / 2) = 1 := by
      rw [Real.rpow_neg_one]
      field_simp
    rw [this]; simp
  calc volume {x | l ^ 2 < sqS (fun j => cv (K j) F) x}
      ≤ volume ({x | q ^ 2 < sqS (fun j => cv (K j) F₁) x} ∪
          {x | q ^ 2 < sqS (fun j => cv (K j) F₂) x}) := measure_mono hsub
    _ ≤ volume {x | q ^ 2 < sqS (fun j => cv (K j) F₁) x} +
          volume {x | q ^ 2 < sqS (fun j => cv (K j) F₂) x} := measure_union_le _ _
    _ ≤ (16 * C4) * (ENNReal.ofReal (t ^ (-4 : ℝ)) *
          ∫⁻ x, (if ‖F x‖ₑ ≤ l then ‖F x‖ₑ ^ 4 else 0)) +
        (2 * Cw) * (ENNReal.ofReal (t ^ (-1 : ℝ)) *
          ∫⁻ x, (if l < ‖F x‖ₑ then ‖F x‖ₑ else 0)) := by
        refine add_le_add ?_ ?_
        · calc volume {x | q ^ 2 < sqS (fun j => cv (K j) F₁) x}
              = (ENNReal.ofReal (t ^ (-4 : ℝ)) * 16 * q ^ 4) *
                  volume {x | q ^ 2 < sqS (fun j => cv (K j) F₁) x} := by rw [e4, one_mul]
            _ = (ENNReal.ofReal (t ^ (-4 : ℝ)) * 16) * (q ^ 4 *
                  volume {x | q ^ 2 < sqS (fun j => cv (K j) F₁) x}) := by ring
            _ ≤ (ENNReal.ofReal (t ^ (-4 : ℝ)) * 16) *
                  (C4 * ∫⁻ x, (if ‖F x‖ₑ ≤ l then ‖F x‖ₑ ^ 4 else 0)) :=
                mul_le_mul_right hA1 _
            _ = _ := by ring
        · calc volume {x | q ^ 2 < sqS (fun j => cv (K j) F₂) x}
              = (ENNReal.ofReal (t ^ (-1 : ℝ)) * 2 * q) *
                  volume {x | q ^ 2 < sqS (fun j => cv (K j) F₂) x} := by rw [e1, one_mul]
            _ = (ENNReal.ofReal (t ^ (-1 : ℝ)) * 2) * (q *
                  volume {x | q ^ 2 < sqS (fun j => cv (K j) F₂) x}) := by ring
            _ ≤ (ENNReal.ofReal (t ^ (-1 : ℝ)) * 2) *
                  (Cw * ∫⁻ x, (if l < ‖F x‖ₑ then ‖F x‖ₑ else 0)) :=
                mul_le_mul_right hA2 _
            _ = _ := by ring

/-- **Marcinkiewicz interpolation**: `E1At` for all `1/2 < s < 2` from `E1At 2` and Hörmander's
condition -/
theorem E1At_of_horm (hd : 1 ≤ d) {K : ℤ → 𝔼 → ℂ} (hKm : ∀ j, Measurable (K j))
    (hKi : ∀ j, Integrable (K j)) (h4 : E1At K 2) {H : ℝ≥0∞} (hH : H ≠ ⊤) (hHorm : HormK K H)
    {s : ℝ} (hs1 : 1 / 2 < s) (hs2 : s < 2) : E1At K s := by
  obtain ⟨Cw, hCw, hweak⟩ := cz_weak hd hKm hKi h4 hH hHorm
  obtain ⟨C4, hC4⟩ := h4
  set u : ℝ := 2 * s with hu
  have hu1 : 1 < u := by rw [hu]; linarith
  have hu4 : u < 4 := by rw [hu]; linarith
  have hbig : ENNReal.ofReal u * (16 * (C4 : ℝ≥0∞) * ENNReal.ofReal (1 / (4 - u)) +
      2 * Cw * ENNReal.ofReal (1 / (u - 1))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top) ENNReal.ofReal_ne_top,
       ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hCw) ENNReal.ofReal_ne_top⟩)
  refine ⟨(ENNReal.ofReal u * (16 * (C4 : ℝ≥0∞) * ENNReal.ofReal (1 / (4 - u)) +
      2 * Cw * ENNReal.ofReal (1 / (u - 1)))).toNNReal, fun F hF hFi B hB hFB => ?_⟩
  rw [ENNReal.coe_toNNReal hbig]
  have hWm : Measurable (fun x => sqS (fun j => cv (K j) F) x ^ (1 / 2 : ℝ)) :=
    (sqS_measurable (fun j => measurable_cv (hKm j) hF)).pow_const _
  have hlb := layer_bound (W := fun x => sqS (fun j => cv (K j) F) x ^ (1 / 2 : ℝ))
    (f := fun x => ‖F x‖ₑ) hWm hF.enorm (fun x => ne_top_of_le_ne_top hB (hFB x)) hu1 hu4
    (A4 := 16 * C4) (A1 := 2 * Cw) (fun t ht => by
      refine le_trans (measure_mono ?_) (dist_estimate hKm hKi hC4 hweak hF hFi hB hFB ht)
      intro x hx
      have hx' : ENNReal.ofReal t < sqS (fun j => cv (K j) F) x ^ (1 / 2 : ℝ) := hx
      show ENNReal.ofReal t ^ 2 < _
      by_contra hcon
      have h1 := not_lt.1 hcon
      have h2 := ENNReal.rpow_le_rpow h1 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      have h3 : (ENNReal.ofReal t ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal t := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      rw [h3] at h2
      exact absurd hx' (not_lt.2 h2))
  have hconv : ∫⁻ x, sqS (fun j => cv (K j) F) x ^ s =
      ∫⁻ x, (sqS (fun j => cv (K j) F) x ^ (1 / 2 : ℝ)) ^ u := by
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [hu]; ring
  rw [hconv]
  refine hlb.trans (le_of_eq ?_)
  ring

end HRS.Commutator.Whole.XLI
