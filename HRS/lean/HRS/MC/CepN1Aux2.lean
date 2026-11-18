import HRS.MC.CepN1Aux1

/-!
# Packet CEPN1, part 2: dyadic grids, sup-control of a pre-Brownian path on `[0,h]`
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepN1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The dyadic grid point `h k / 2^n`. -/
def cepn1_dy (h : ℝ≥0) (n k : ℕ) : ℝ≥0 := h * ((k : ℝ≥0) / 2 ^ n)

theorem cepn1_dy_double (h : ℝ≥0) (n k : ℕ) : cepn1_dy h (n + 1) (2 * k) = cepn1_dy h n k := by
  unfold cepn1_dy
  push_cast
  rw [pow_succ]
  congr 1
  field_simp

theorem cepn1_dy_last (h : ℝ≥0) (n : ℕ) : cepn1_dy h n (2 ^ n) = h := by
  unfold cepn1_dy
  push_cast
  field_simp

theorem cepn1_dy_mono (h : ℝ≥0) (n : ℕ) : Monotone fun k => cepn1_dy h n (min k (2 ^ n)) := by
  intro k l hkl
  show h * (((min k (2 ^ n) : ℕ) : ℝ≥0) / 2 ^ n) ≤ h * (((min l (2 ^ n) : ℕ) : ℝ≥0) / 2 ^ n)
  gcongr

theorem cepn1_dy_le (h : ℝ≥0) (n k : ℕ) (hk : k ≤ 2 ^ n) : cepn1_dy h n k ≤ h := by
  calc cepn1_dy h n k ≤ cepn1_dy h n (2 ^ n) := by
        unfold cepn1_dy
        gcongr
    _ = h := cepn1_dy_last h n


theorem cepn1_max_dy [IsProbabilityMeasure P] {Z : ℝ≥0 → Ω → ℝ} (hZ : IsPreBrownianReal Z P)
    (h : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (ρ ^ 2) * P {ω | ∃ n k : ℕ, k ≤ 2 ^ n ∧ ρ < |Z (cepn1_dy h n k) ω|} ≤
      ENNReal.ofReal h := by
  set G : ℕ → Set Ω := fun n => {ω | ∃ k : ℕ, k ≤ 2 ^ n ∧ ρ < |Z (cepn1_dy h n k) ω|} with hG
  have hU : {ω | ∃ n k : ℕ, k ≤ 2 ^ n ∧ ρ < |Z (cepn1_dy h n k) ω|} = ⋃ n, G n := by
    ext ω; simp [hG]
  have hmono : Monotone G := by
    refine monotone_nat_of_le_succ fun n ω => ?_
    rintro ⟨k, hk, hk2⟩
    exact ⟨2 * k, by rw [pow_succ]; omega, by rwa [cepn1_dy_double]⟩
  rw [hU, hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  have key := cepn1_max hZ (fun k => cepn1_dy h n (min k (2 ^ n))) (cepn1_dy_mono h n) hρ (2 ^ n)
  have hsub : G n ⊆ {ω | ∃ k ≤ 2 ^ n, ρ < |Z ((fun k => cepn1_dy h n (min k (2 ^ n))) k) ω|} := by
    rintro ω ⟨k, hk, hk2⟩
    exact ⟨k, hk, by simpa [min_eq_left hk] using hk2⟩
  calc ENNReal.ofReal (ρ ^ 2) * P (G n)
      ≤ ENNReal.ofReal (ρ ^ 2) * P {ω | ∃ k ≤ 2 ^ n,
          ρ < |Z ((fun k => cepn1_dy h n (min k (2 ^ n))) k) ω|} :=
        mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ ENNReal.ofReal ((fun k => cepn1_dy h n (min k (2 ^ n))) (2 ^ n)) := key
    _ = ENNReal.ofReal h := by simp [cepn1_dy_last]

/-- A continuous path bounded by `ρ` on all dyadic grid points of `[0,h]` is bounded by `ρ` on `[0,h]`. -/
theorem cepn1_dy_dense {z : ℝ≥0 → ℝ} (hz : Continuous z) {h : ℝ≥0} {ρ : ℝ}
    (hA : ∀ n k : ℕ, k ≤ 2 ^ n → |z (cepn1_dy h n k)| ≤ ρ) (s : ℝ≥0) (hs : s ≤ h) : |z s| ≤ ρ := by
  rcases eq_or_ne h 0 with rfl | hh
  · have : s = 0 := le_antisymm hs bot_le
    subst this
    simpa [cepn1_dy] using hA 0 0 (by simp)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast pos_iff_ne_zero.2 hh
  -- floor approximants
  let kk : ℕ → ℕ := fun n => ⌊(s : ℝ) / h * 2 ^ n⌋₊
  have hkk : ∀ n, kk n ≤ 2 ^ n := by
    intro n
    have : (s : ℝ) / h * 2 ^ n ≤ 2 ^ n := by
      have h1 : (s : ℝ) / h ≤ 1 := by
        rw [div_le_one hhpos]; exact_mod_cast hs
      nlinarith [pow_pos (two_pos : (0:ℝ) < 2) n]
    show ⌊(s : ℝ) / h * 2 ^ n⌋₊ ≤ 2 ^ n
    exact Nat.floor_le_of_le (by exact_mod_cast this)
  have hlim : Tendsto (fun n => cepn1_dy h n (kk n)) atTop (𝓝 s) := by
    rw [← NNReal.tendsto_coe]
    have hc : ∀ n, ((cepn1_dy h n (kk n) : ℝ≥0) : ℝ) = h * ((kk n : ℝ) / 2 ^ n) := by
      intro n; simp [cepn1_dy]
    simp_rw [hc]
    have hlo : ∀ n, (s : ℝ) - h / 2 ^ n ≤ h * ((kk n : ℝ) / 2 ^ n) := by
      intro n
      have h2 : (s : ℝ) / h * 2 ^ n - 1 ≤ kk n := by
        have := Nat.lt_floor_add_one ((s : ℝ) / h * 2 ^ n)
        linarith
      have hp : (0 : ℝ) < 2 ^ n := by positivity
      have : (s : ℝ) = h * ((s : ℝ) / h) := by field_simp
      rw [mul_div_assoc', le_div_iff₀ hp]
      calc ((s : ℝ) - h / 2 ^ n) * 2 ^ n = h * ((s : ℝ) / h * 2 ^ n - 1) := by
            field_simp
        _ ≤ h * kk n := by gcongr
    have hhi : ∀ n, h * ((kk n : ℝ) / 2 ^ n) ≤ s := by
      intro n
      have h2 : (kk n : ℝ) ≤ (s : ℝ) / h * 2 ^ n := Nat.floor_le (by positivity)
      have hp : (0 : ℝ) < 2 ^ n := by positivity
      rw [mul_div_assoc', div_le_iff₀ hp]
      calc h * kk n ≤ h * ((s : ℝ) / h * 2 ^ n) := by gcongr
        _ = s * 2 ^ n := by field_simp
    have hl : Tendsto (fun n : ℕ => (s : ℝ) - h / 2 ^ n) atTop (𝓝 s) := by
      have : Tendsto (fun n : ℕ => (h : ℝ) / 2 ^ n) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv, ← inv_pow] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul (h : ℝ)
      simpa using tendsto_const_nhds.sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hhi
  have hc := (continuous_abs.comp hz).tendsto s
  have := hc.comp hlim
  exact le_of_tendsto' this fun n => hA n _ (hkk n)

end HRS.MC.CepN1
