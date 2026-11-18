import HRS.Commutator.Whole.ExternalAuxHLS2

/-!
# Hardy–Littlewood–Sobolev inequality in kernel form (packet X-HLS, part 3)
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **HLS, kernel form**: `‖I_σ f‖_q ≲ ‖f‖_p` for `1 < p < q < ∞`, `1/q = 1/p - σ/d`. -/
theorem cmxHLS_kernel (hd : 1 ≤ d) {σ p q : ℝ} (hσ : 0 < σ) (hp : 1 < p) (hpq : p < q)
    (hrel : 1 / q = 1 / p - σ / d) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝔼 → ℝ≥0, Measurable f →
      ∫⁻ x, cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x ^ q ≤
        ENNReal.ofReal C * (∫⁻ y, (f y : ℝ≥0∞) ^ p) ^ (q / p) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hθq : p / q = 1 - σ * p / d := by
    have : p / q = p * (1 / q) := by ring
    rw [this, hrel]; field_simp
  have hσp : σ * p < d := by
    have h1 : 0 < p / q := by positivity
    rw [hθq] at h1
    have : σ * p / d < 1 := by linarith
    rwa [div_lt_one hdpos] at this
  obtain ⟨C₀, hC₀t, hC₀0, hC₀⟩ := cmxHLS_hedberg (d := d) hσ hp hσp
  obtain ⟨CM, hCM, hM⟩ := cmxHLS_strong hd hp
  set θ : ℝ := σ * p / d with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : (1 - θ) * q = p := by
    rw [← hθq]; field_simp
  have hθq' : θ * q = q - p := by linarith
  refine ⟨(C₀ ^ q * ENNReal.ofReal CM).toReal, ?_, fun f hf => ?_⟩
  · refine ENNReal.toReal_pos ?_ ?_
    · exact mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 hC₀0) hC₀t).ne' (by simpa using hCM)
    · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le hC₀t) ENNReal.ofReal_ne_top
  set F : 𝔼 → ℝ≥0∞ := fun y => (f y : ℝ≥0∞) with hF
  have hFm : Measurable F := hf.coe_nnreal_ennreal
  set S : ℝ≥0∞ := ∫⁻ y, F y ^ p with hS
  have hCfin : C₀ ^ q * ENNReal.ofReal CM ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le hC₀t) ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_toReal hCfin]
  by_cases hST : S = ⊤
  · rw [hST, ENNReal.top_rpow_of_pos (by positivity), ENNReal.mul_top]
    · exact le_top
    · exact (mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 hC₀0) hC₀t).ne' (by simpa using hCM))
  by_cases hS0 : S = 0
  · -- `F = 0` a.e., so `I F = 0`
    have hF0 : ∀ᵐ y ∂volume, F y = 0 := by
      have h1 := (lintegral_eq_zero_iff (hFm.pow_const p)).1 hS0
      filter_upwards [h1] with y hy
      have hy' : F y = 0 ∧ 0 < p ∨ F y = ⊤ ∧ p < 0 := by
        simpa [ENNReal.rpow_eq_zero_iff] using hy
      rcases hy' with h | h
      · exact h.1
      · exact absurd h.2 (by linarith)
    have hI : ∀ x, cmxHLS_I σ F x = 0 := by
      intro x
      unfold cmxHLS_I
      rw [lintegral_eq_zero_iff']
      · filter_upwards [hF0] with y hy
        simp [hy]
      · exact ((((measurable_const.sub measurable_id).norm.pow_const _).ennreal_ofReal).mul
          hFm).aemeasurable
    simp only [hI, ENNReal.zero_rpow_of_pos hq0]
    simp
  -- main case
  have hpt : ∀ x, cmxHLS_I σ F x ^ q ≤
      C₀ ^ q * S ^ (θ * q / p) * (cmxHLS_Md F x) ^ p := by
    intro x
    have h1 := hC₀ F hFm hS0 hST x
    have h2 := ENNReal.rpow_le_rpow h1 hq0.le
    refine h2.trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hθ1]
    rw [show 1 / p * (θ * q) = θ * q / p by ring]
    ring
  calc ∫⁻ x, cmxHLS_I σ F x ^ q
      ≤ ∫⁻ x, C₀ ^ q * S ^ (θ * q / p) * (cmxHLS_Md F x) ^ p := lintegral_mono hpt
    _ = C₀ ^ q * S ^ (θ * q / p) * ∫⁻ x, (cmxHLS_Md F x) ^ p := by
        rw [lintegral_const_mul']
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le hC₀t)
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) hST)
    _ ≤ C₀ ^ q * S ^ (θ * q / p) * (ENNReal.ofReal CM * S) := by
        gcongr
        exact hM f hf
    _ = C₀ ^ q * ENNReal.ofReal CM * S ^ (q / p) := by
        have h3 : S ^ (q / p) = S ^ (θ * q / p) * S := by
          have : q / p = θ * q / p + 1 := by
            rw [hθq']; field_simp; ring
          rw [this, ENNReal.rpow_add _ _ hS0 hST, ENNReal.rpow_one]
        rw [h3]; ring

end HRS.Commutator.Whole
