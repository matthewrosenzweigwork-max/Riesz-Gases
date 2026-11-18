import HRS.Commutator.Torus.TEN2Aux9
import HRS.Commutator.Torus.TEN2Aux2

/-!
# Torus energy layer (packet T-EN2), helper part 10: the background Sobolev sum against `‖μ‖²_{f_η}`

Prefix `ten2_`.  `η^{-s} sobSqT η (-α) ρ̂ ≤ η^{d-s} + c_b⁻¹ ∬ f_η ρ ρ` (zero mode `|ρ̂(0)| = 1` plus the coercivity
`tScale f̂_η(k) ≥ c_b η^{d-s}(1+4π²η²|k|²)^{-α}`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d N : ℕ} {s η : ℝ}

theorem ten2_fTorus_integrable (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    Integrable (fTorus s η : Torus d → ℝ) := by
  obtain ⟨-, -, -, hlift⟩ := tpos_coef_formula hd hs0 hsd η hη
  have hG : Continuous (gTorus s η) := HRS.Torus.continuous_of_continuous_lift hlift
  have hR : Integrable (periodicRiesz d s) :=
    HRS.KernelAux.integrable_periodicRiesz (by omega) hs0 (by linarith)
  exact ten_fTorus_integrable hR hG (by omega)

/-- The quadratic form `‖μ‖²_{f_η} ≥ 0`. -/
theorem ten2_quad_nonneg (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {cb : ℝ}
    (hcb : ∀ k : Lattice d, k ≠ 0 → cb * η ^ ((d : ℝ) - s) *
      (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s)) ≤
        tScale s * fHatEta d s η (Lattice.toEuc k)) (hcb0 : 0 < cb) (hη : 0 < η)
    {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) :
    0 ≤ ∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y := by
  obtain ⟨hcf, -, -, -⟩ := tpos_coef_formula hd hs0 hsd η hη
  have hf := ten2_fTorus_integrable hd hs0 hsd hη
  have hquad := ten2_quadform hf hρ hcf
  refine hquad.nonneg fun k => mul_nonneg ?_ (sq_nonneg _)
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false]
    have h1 := hcb k hk
    have h2 : 0 ≤ cb * η ^ ((d : ℝ) - s) *
        (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s)) := by positivity
    linarith

theorem ten2_sobSq_le (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {cb : ℝ}
    (hcb : ∀ k : Lattice d, k ≠ 0 → cb * η ^ ((d : ℝ) - s) *
      (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s)) ≤
        tScale s * fHatEta d s η (Lattice.toEuc k)) (hcb0 : 0 < cb) (hη : 0 < η)
    {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) :
    ENNReal.ofReal (η ^ (-s)) * sobSqT η (-Whole.alphaE d s) (fun k => Torus.fcoef ρ k) ≤
      ENNReal.ofReal (η ^ ((d : ℝ) - s) + cb⁻¹ * ∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y) := by
  obtain ⟨hcf, -, -, -⟩ := tpos_coef_formula hd hs0 hsd η hη
  have hf := ten2_fTorus_integrable hd hs0 hsd hη
  have hquad := ten2_quadform hf hρ hcf
  set ck : Lattice d → ℝ := fun k => if k = 0 then 0 else tScale s * fHatEta d s η (Lattice.toEuc k) with hck
  have hck_nn : ∀ k, 0 ≤ ck k := by
    intro k
    by_cases hk : k = 0
    · simp [hck, hk]
    · simp only [hck, hk, if_false]
      have h1 := hcb k hk
      have h2 : 0 ≤ cb * η ^ ((d : ℝ) - s) *
          (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s)) := by positivity
      linarith
  set I := ∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y with hI
  set κ : ℝ := cb⁻¹ * η ^ (-((d : ℝ) - s)) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set a : Lattice d → ℝ := fun k => (if k = 0 then 1 else 0) + κ * (ck k * ‖Torus.fcoef ρ k‖ ^ 2) with ha
  have hasum : HasSum a (1 + κ * I) := (hasSum_ite_eq (0 : Lattice d) (1 : ℝ)).add (hquad.mul_left κ)
  have hann : ∀ k, 0 ≤ a k := fun k => by
    simp only [ha]
    have : 0 ≤ κ * (ck k * ‖Torus.fcoef ρ k‖ ^ 2) :=
      mul_nonneg hκ0 (mul_nonneg (hck_nn k) (sq_nonneg _))
    split_ifs <;> linarith
  have hmean : ‖Torus.fcoef ρ 0‖ = 1 := by
    rw [Torus.fcoef_zero]
    have : Torus.mean ρ = 1 := hρ.mass
    rw [this]; simp
  have hwk : ∀ k : Lattice d, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^
      (-(Whole.alphaE d s))) * ‖Torus.fcoef ρ k‖ₑ ^ 2 ≤ ENNReal.ofReal (a k) := by
    intro k
    have hsq : ‖Torus.fcoef ρ k‖ₑ ^ 2 = ENNReal.ofReal (‖Torus.fcoef ρ k‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [hsq, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hk : k = 0
    · subst hk
      have : Lattice.enorm (0 : Lattice d) = 0 := by
        simp [Lattice.enorm, ten2_toEuc_zero]
      simp only [ha, hck, this, hmean, if_true]
      simp
    · simp only [ha, hk, if_false, zero_add, hck]
      have h1 := hcb k hk
      set w := (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s)) with hw
      have hηp : 0 < η ^ ((d : ℝ) - s) := Real.rpow_pos_of_pos hη _
      have hw1 : w ≤ κ * tScale s * fHatEta d s η (Lattice.toEuc k) := by
        have : w * (cb * η ^ ((d : ℝ) - s)) ≤ tScale s * fHatEta d s η (Lattice.toEuc k) := by
          nlinarith
        have h3 : κ * (cb * η ^ ((d : ℝ) - s)) = 1 := by
          rw [hκ, Real.rpow_neg hη.le]
          field_simp
        calc w = w * (κ * (cb * η ^ ((d : ℝ) - s))) := by rw [h3, mul_one]
          _ = κ * (w * (cb * η ^ ((d : ℝ) - s))) := by ring
          _ ≤ κ * (tScale s * fHatEta d s η (Lattice.toEuc k)) := mul_le_mul_of_nonneg_left this hκ0
          _ = _ := by ring
      calc w * ‖Torus.fcoef ρ k‖ ^ 2 ≤ κ * tScale s * fHatEta d s η (Lattice.toEuc k) * ‖Torus.fcoef ρ k‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hw1 (sq_nonneg _)
        _ = κ * (tScale s * fHatEta d s η (Lattice.toEuc k) * ‖Torus.fcoef ρ k‖ ^ 2) := by ring
  unfold sobSqT
  calc ENNReal.ofReal (η ^ (-s)) * (ENNReal.ofReal (η ^ d) * ∑' k : Lattice d,
        ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s))) *
          ‖Torus.fcoef ρ k‖ₑ ^ 2)
      ≤ ENNReal.ofReal (η ^ (-s)) * (ENNReal.ofReal (η ^ d) * ∑' k : Lattice d, ENNReal.ofReal (a k)) := by
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
        exact ENNReal.tsum_le_tsum hwk
    _ = ENNReal.ofReal (η ^ (-s)) * (ENNReal.ofReal (η ^ d) * ENNReal.ofReal (1 + κ * I)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hann hasum.summable, hasum.tsum_eq]
    _ = ENNReal.ofReal (η ^ (-s) * (η ^ d * (1 + κ * I))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (η ^ ((d : ℝ) - s) + cb⁻¹ * I) := by
        congr 1
        have h1 : η ^ (-s) * η ^ d = η ^ ((d : ℝ) - s) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hη]; congr 1; ring
        have h2 : η ^ ((d : ℝ) - s) * κ = cb⁻¹ := by
          rw [hκ, ← mul_assoc, mul_comm (η ^ ((d : ℝ) - s)), mul_assoc, ← Real.rpow_add hη]
          simp
        calc η ^ (-s) * (η ^ d * (1 + κ * I)) = (η ^ (-s) * η ^ d) * (1 + κ * I) := by ring
          _ = η ^ ((d : ℝ) - s) + (η ^ ((d : ℝ) - s) * κ) * I := by rw [h1]; ring
          _ = _ := by rw [h2]

end HRS.Commutator.TorusNote
