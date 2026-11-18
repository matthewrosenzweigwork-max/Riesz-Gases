import HRS.Sections.IIDAux15

/-!
# IID helper chain, part 16: clipping, densities `(1 + s b')ρ`, and elementary rate comparisons.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section Final

open HRS.InitialDataAux

variable {d : ℕ}

lemma clip_exists {b : Torus d → ℝ} (hbm : Measurable b) (hbL : MemLp b ⊤ (volume : Measure (Torus d))) :
    ∃ b' : Torus d → ℝ, Measurable b' ∧
      (∀ x, |b' x| ≤ (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal) ∧ b =ᵐ[volume] b' := by
  set B : ℝ := (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal with hB
  have hne : eLpNorm b ⊤ (volume : Measure (Torus d)) ≠ ⊤ := hbL.eLpNorm_lt_top.ne
  have hae : ∀ᵐ x ∂(volume : Measure (Torus d)), |b x| ≤ B := by
    have := ae_le_eLpNormEssSup (f := b) (μ := (volume : Measure (Torus d)))
    have e : eLpNorm b ⊤ (volume : Measure (Torus d)) = eLpNormEssSup b (volume : Measure (Torus d)) :=
      eLpNorm_exponent_top hbm.aestronglyMeasurable
    rw [← e] at this
    filter_upwards [this] with x hx
    have h2 : ENNReal.ofReal |b x| ≤ eLpNorm b ⊤ (volume : Measure (Torus d)) := by
      rw [← Real.enorm_eq_ofReal_abs]; simpa using hx
    exact (ENNReal.ofReal_le_iff_le_toReal hne).1 h2
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  refine ⟨fun x => if |b x| ≤ B then b x else 0, ?_, fun x => ?_, ?_⟩
  · exact Measurable.ite (measurableSet_le hbm.abs measurable_const) hbm measurable_const
  · by_cases h : |b x| ≤ B
    · simp [h]
    · simp [h, hB0]
  · filter_upwards [hae] with x hx
    simp [hx]

lemma qd_prob {ρ b' : Torus d → ℝ} (hρ : IsProbDensity ρ) (hb'm : Measurable b') {B s : ℝ}
    (hB : ∀ x, |b' x| ≤ B) (hs : |s| * B ≤ 1 / 2) (h0 : ∫ x, ρ x * b' x = 0) :
    IsProbDensity (fun x => (1 + s * b' x) * ρ x) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hsb : ∀ x, |s * b' x| ≤ 1 / 2 := fun x => by
    rw [abs_mul]
    calc |s| * |b' x| ≤ |s| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
      _ ≤ _ := hs
  refine ⟨fun x => ?_, ?_, ?_⟩
  · exact mul_nonneg (by linarith [abs_le.1 (hsb x)]) (hρ.nonneg x)
  · exact (measurable_const.add (measurable_const.mul hb'm)).mul hρ.measurable
  · have i2 : Integrable (fun x => ρ x * b' x) := integrable_mul_bdd (integrable_of_pd hρ) hb'm hB
    have e : ∀ x, (1 + s * b' x) * ρ x = ρ x + s * (ρ x * b' x) := fun x => by ring
    simp_rw [e]
    rw [integral_add (integrable_of_pd hρ) (i2.const_mul s), integral_const_mul, h0, hρ.integral_one]
    ring

lemma qd_ge {ρ b' : Torus d → ℝ} (hρ : IsProbDensity ρ) {c : ℝ} (hρc : ∀ x, c ≤ ρ x) {B s : ℝ}
    (hB : ∀ x, |b' x| ≤ B) (hs : |s| * B ≤ 1 / 2) (x : Torus d) :
    c / 2 ≤ (1 + s * b' x) * ρ x := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have : |s * b' x| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |s| * |b' x| ≤ |s| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
      _ ≤ _ := hs
  have h1 : 1 / 2 ≤ 1 + s * b' x := by linarith [abs_le.1 this]
  have h2 : c ≤ ρ x := hρc x
  nlinarith [hρ.nonneg x]

lemma qd_close {ρ b' : Torus d → ℝ} (hρ : IsProbDensity ρ) {B s : ℝ} (hB : ∀ x, |b' x| ≤ B) (x : Torus d) :
    |(1 + s * b' x) * ρ x - ρ x| ≤ (|s| * B) * ρ x := by
  have : (1 + s * b' x) * ρ x - ρ x = (s * b' x) * ρ x := by ring
  rw [this, abs_mul, abs_of_nonneg (hρ.nonneg x), abs_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)) (hρ.nonneg x)

lemma inv_sqrt_le_e2 {m : ℝ} (hm : (d : ℝ) / 2 < m) {N : ℕ} (hN : 1 ≤ N) :
    1 / Real.sqrt N ≤ (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : 0 < m := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have : 1 / Real.sqrt N = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hN0.le, one_div]
  rw [this]
  refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
  have h : (m - (d : ℝ) / 2) / (2 * m) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  linarith

lemma inv_sqrt_le_W {m : ℝ} (hm : (d : ℝ) / 2 < m) {N : ℕ} (hN : 1 ≤ N) :
    1 / Real.sqrt N ≤ (Real.log (Real.exp 1 * N) / Real.sqrt N) ^
      ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hs1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hm0 : 0 < m := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set Λ := Real.log (Real.exp 1 * N) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
    have : 0 ≤ Real.log N := Real.log_nonneg hN1
    linarith
  set θ := (m - (d : ℝ) / 2) / (m + (d : ℝ) / 2) with hθ
  have hθ0 : 0 < θ := div_pos (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by linarith)]; linarith
  have hx : 1 / Real.sqrt N ≤ Λ / Real.sqrt N := by gcongr
  rcases le_total 1 (Λ / Real.sqrt N) with h | h
  · calc 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hs]; exact hs1
      _ ≤ _ := Real.one_le_rpow h hθ0.le
  · calc 1 / Real.sqrt N ≤ Λ / Real.sqrt N := hx
      _ = (Λ / Real.sqrt N) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge (by positivity) h hθ1

lemma CB.mono' {m : ℝ} {ν γ : Measure (NegSobolev d m)} {J M J' M' : ℝ} (h : CB ν γ J M)
    (hJ : J ≤ J') (hM : M ≤ M') : CB ν γ J' M' := by
  obtain ⟨π, hπ, hp, a, b⟩ := h
  exact ⟨π, hπ, hp, a.trans (ENNReal.ofReal_le_ofReal hJ), b.trans (ENNReal.ofReal_le_ofReal hM)⟩

end Final

end HRS.IID
