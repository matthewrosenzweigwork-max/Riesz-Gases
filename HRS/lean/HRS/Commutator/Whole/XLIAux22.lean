import HRS.Commutator.Whole.XLIAux21

/-!
# X-LI part 22: the bilinear estimate for finite exponents
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma Md_le_of_le {f : 𝔼 → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ y, f y ≤ c) (x : 𝔼) :
    cmxHLS_Md f x ≤ c := by
  unfold cmxHLS_Md
  refine iSup_le fun j => ?_
  have h0 := cmxHLS_vol_closedBall_ne_zero x (zpow_pos (by norm_num : (0 : ℝ) < 2) j)
  have h1 := cmxHLS_vol_closedBall_ne_top x ((2 : ℝ) ^ j)
  calc (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ * ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y
      ≤ (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ * (c * volume (closedBall x ((2 : ℝ) ^ j))) := by
        refine mul_le_mul_right ?_ _
        calc ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y ≤ ∫⁻ y in closedBall x ((2 : ℝ) ^ j), c :=
              lintegral_mono h
          _ = c * volume (closedBall x ((2 : ℝ) ^ j)) := by simp [mul_comm]
    _ = c := by
        rw [mul_comm c, ← mul_assoc, ENNReal.inv_mul_cancel h0 h1, one_mul]

section Bil

variable (α : ℝ)

/-- the maximal function of `|ψ|` -/
def Mx (ψ : SchwartzMap 𝔼 ℂ) (y : 𝔼) : ℝ≥0∞ := cmxHLS_Md (fun z => ‖ψ z‖ₑ) y

lemma Mx_meas (ψ : SchwartzMap 𝔼 ℂ) : Measurable (Mx ψ) :=
  cmxHLS_Md_measurable ψ.continuous.measurable.enorm

lemma Gs_le (ψ : SchwartzMap 𝔼 ℂ) (j : ℤ) (y : 𝔼) : Gs ψ j y ≤ 4 * (KP d * Mx ψ y) := by
  have h : ∀ l : ℤ, Gc ψ l y ≤ KP d * Mx ψ y := fun l =>
    CvP_le l ψ.continuous.measurable.enorm y
  unfold Gs
  calc Gc ψ (j + -3) y + Gc ψ (j + -2) y + Gc ψ (j + -1) y + Gc ψ j y
      ≤ KP d * Mx ψ y + KP d * Mx ψ y + KP d * Mx ψ y + KP d * Mx ψ y :=
        add_le_add (add_le_add (add_le_add (h _) (h _)) (h _)) (h _)
    _ = 4 * (KP d * Mx ψ y) := by ring

lemma QQ_le (φ ψ : SchwartzMap 𝔼 ℂ) (y : 𝔼) :
    QQ α φ ψ y ≤ sqS (fun j => Fj α φ j) y * (4 * (KP d * Mx ψ y)) ^ 2 := by
  unfold QQ sqS hh
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [mul_pow]
  gcongr
  exact Gs_le ψ j y

/-- Hölder's inequality for products of powers -/
lemma holder_pow {X M : 𝔼 → ℝ≥0∞} (hX : Measurable X) (hM : Measurable M) {s p q t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hp : 0 < p) (hq : 0 < q) (hsum : s / p + t / q = 1) :
    ∫⁻ x, X x ^ s * M x ^ t ≤ (∫⁻ x, X x ^ p) ^ (s / p) * (∫⁻ x, M x ^ q) ^ (t / q) := by
  have hP : 1 < p / s := by
    have h1 : s / p < 1 := by
      have : 0 < t / q := by positivity
      linarith
    rw [lt_div_iff₀ hs]
    rw [div_lt_one hp] at h1
    linarith
  have hconj : (p / s).HolderConjugate (q / t) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hP, ?_⟩
    rw [inv_div, inv_div]
    exact hsum
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj (f := fun x => X x ^ s)
    (g := fun x => M x ^ t) (hX.pow_const _).aemeasurable (hM.pow_const _).aemeasurable
  have e1 : ∀ x, (X x ^ s) ^ (p / s) = X x ^ p := by
    intro x; rw [← ENNReal.rpow_mul]; congr 1; field_simp
  have e2 : ∀ x, (M x ^ t) ^ (q / t) = M x ^ q := by
    intro x; rw [← ENNReal.rpow_mul]; congr 1; field_simp
  simp only [e1, e2, one_div, inv_div] at h
  exact h

lemma sch_enorm_bdd (F : SchwartzMap 𝔼 ℂ) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ x, ‖F x‖ₑ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := sch_bdd F
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun x => ?_⟩
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hC x)

/-- **the bilinear estimate for finite exponents** -/
lemma BILIN_fin (hd : 1 ≤ d) {r u v : ℝ} (hr : 1 < r) (hu : 1 < u) (hv : 1 < v)
    (huv : 1 / u + 1 / v = 1 / r)
    (hE : E1At (fun j => dK (Ths (-α) : ℤ → 𝔼 → ℂ) j) (u / 2)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ ψ : SchwartzMap 𝔼 ℂ,
      ∫⁻ x, QQ α φ ψ x ^ (r / 2) ≤
        C * ((∫⁻ x, ‖Fm α φ x‖ₑ ^ u) ^ (r / u) * (∫⁻ x, ‖ψ x‖ₑ ^ v) ^ (r / v)) := by
  obtain ⟨CE, hCE⟩ := hE
  obtain ⟨CM, hCM⟩ := Mx_strong hd hv
  have hr0 : 0 < r := by linarith
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  set s : ℝ := r / 2 with hs
  have hs0 : 0 < s := by positivity
  set c4 : ℝ≥0∞ := 4 * KP d with hc4
  have hc4ne : c4 ≠ ⊤ := ENNReal.mul_ne_top (by simp) KP_ne_top
  have hsum : s / (u / 2) + 2 * s / v = 1 := by
    have : s / (u / 2) + 2 * s / v = r * (1 / u + 1 / v) := by
      rw [hs]; field_simp
    rw [this, huv]; field_simp
  refine ⟨c4 ^ (2 * s) * ((CE : ℝ≥0∞) ^ (r / u) * (CM : ℝ≥0∞) ^ (r / v)), ?_, fun φ ψ => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hc4ne)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp))
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)))
  set X : 𝔼 → ℝ≥0∞ := sqS (fun j => Fj α φ j) with hX
  have hFjm : ∀ j, Measurable (Fj α φ j) := fun j => Fj_meas α φ j
  have hXm : Measurable X := sqS_measurable hFjm
  have hpt : ∀ x, QQ α φ ψ x ^ s ≤ c4 ^ (2 * s) * (X x ^ s * Mx ψ x ^ (2 * s)) := by
    intro x
    have h1 := ENNReal.rpow_le_rpow (QQ_le α φ ψ x) hs0.le
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, hc4]
    have e1 : ((4 * (KP d * Mx ψ x)) ^ 2) ^ s = (4 * KP d) ^ (2 * s) * Mx ψ x ^ (2 * s) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      rw [show (4 * (KP d * Mx ψ x)) = (4 * KP d) * Mx ψ x by ring]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      norm_num
    rw [e1]; ring
  have hcmeas : Measurable (Mx ψ) := Mx_meas ψ
  calc ∫⁻ x, QQ α φ ψ x ^ s ≤ ∫⁻ x, c4 ^ (2 * s) * (X x ^ s * Mx ψ x ^ (2 * s)) :=
        lintegral_mono hpt
    _ = c4 ^ (2 * s) * ∫⁻ x, X x ^ s * Mx ψ x ^ (2 * s) :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hc4ne)
    _ ≤ c4 ^ (2 * s) * ((∫⁻ x, X x ^ (u / 2)) ^ (s / (u / 2)) *
          (∫⁻ x, Mx ψ x ^ v) ^ (2 * s / v)) := by
        refine mul_le_mul_right ?_ _
        exact holder_pow hXm hcmeas hs0 (by positivity) (by positivity) hv0 hsum
    _ ≤ c4 ^ (2 * s) * ((CE * ∫⁻ x, ‖Fm α φ x‖ₑ ^ u) ^ (r / u) *
          (CM * ∫⁻ x, ‖ψ x‖ₑ ^ v) ^ (r / v)) := by
        refine mul_le_mul_right ?_ _
        have hE1 : ∫⁻ x, X x ^ (u / 2) ≤ CE * ∫⁻ x, ‖Fm α φ x‖ₑ ^ u := by
          obtain ⟨B, hB, hBd⟩ := sch_enorm_bdd (Fm α φ)
          have := hCE (⇑(Fm α φ)) (Fm α φ).continuous.measurable (Fm α φ).integrable B hB hBd
          have e : 2 * (u / 2) = u := by ring
          rw [e] at this
          exact this
        have hM1 : ∫⁻ x, Mx ψ x ^ v ≤ CM * ∫⁻ x, ‖ψ x‖ₑ ^ v := hCM _ ψ.continuous.measurable.enorm
        have e1 : s / (u / 2) = r / u := by rw [hs]; field_simp
        have e2 : 2 * s / v = r / v := by rw [hs]; field_simp
        rw [e1, e2]
        exact mul_le_mul' (ENNReal.rpow_le_rpow hE1 (by positivity))
          (ENNReal.rpow_le_rpow hM1 (by positivity))
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg (CE : ℝ≥0∞) _ (by positivity : (0 : ℝ) ≤ r / u),
          ENNReal.mul_rpow_of_nonneg (CM : ℝ≥0∞) _ (by positivity : (0 : ℝ) ≤ r / v)]
        ring

end Bil

end HRS.Commutator.Whole.XLI
