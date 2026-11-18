import HRS.MC.QRVocab

/-!
# QRAsm, auxiliary file 5: the choice `L ≈ exp(γ t)` (TeX L9190-9192) and exponent bookkeeping
-/

noncomputable section

namespace HRS.MC.QRSpec.Asm

/-- The choice of the cutoff: for `t ≥ 0` there is `L ≥ 1` with
`a₁ L^{-θ/2} + a₂ e^{-c₀t/2} L^{m} ≤ C' e^{-c't}`. -/
lemma asm_choose_L {a1 a2 θ mm c0 : ℝ} (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hθ : 0 < θ) (hmm : 0 ≤ mm)
    (hc0 : 0 < c0) :
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∀ t : ℝ, 0 ≤ t → ∃ L : ℕ, 1 ≤ L ∧
      a1 * (L : ℝ) ^ (-(θ / 2)) + a2 * Real.exp (-c0 * t / 2) * (L : ℝ) ^ mm ≤
        C' * Real.exp (-c' * t) := by
  set γ : ℝ := c0 / (4 * (mm + 1)) with hγ
  have hmm1 : 0 < mm + 1 := by linarith
  have hγ0 : 0 < γ := by positivity
  set c1 : ℝ := γ * θ / 2 with hc1
  set c2 : ℝ := c0 / 4 with hc2
  have hc10 : 0 < c1 := by positivity
  have hc20 : 0 < c2 := by positivity
  refine ⟨a1 + a2 * 2 ^ mm + 1, min c1 c2, by positivity, lt_min hc10 hc20, fun t ht => ?_⟩
  have hE1 : 1 ≤ Real.exp (γ * t) := Real.one_le_exp (by positivity)
  have hEpos : 0 < Real.exp (γ * t) := Real.exp_pos _
  set L : ℕ := ⌈Real.exp (γ * t)⌉₊ with hL
  have hLge : Real.exp (γ * t) ≤ (L : ℝ) := Nat.le_ceil _
  have hLle : (L : ℝ) ≤ 2 * Real.exp (γ * t) := by
    have := Nat.ceil_lt_add_one hEpos.le
    linarith
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) ≤ L := hE1.trans hLge
    exact_mod_cast this
  refine ⟨L, hL1, ?_⟩
  have hLpos : 0 < (L : ℝ) := hEpos.trans_le hLge
  -- first term
  have h1 : (L : ℝ) ^ (-(θ / 2)) ≤ Real.exp (-(min c1 c2) * t) := by
    have : (L : ℝ) ^ (-(θ / 2)) ≤ (Real.exp (γ * t)) ^ (-(θ / 2)) :=
      Real.rpow_le_rpow_of_nonpos hEpos hLge (by linarith)
    refine this.trans ?_
    rw [← Real.exp_mul]
    refine Real.exp_le_exp.2 ?_
    have : min c1 c2 ≤ c1 := min_le_left _ _
    nlinarith [mul_nonneg ht (sub_nonneg.2 this)]
  -- second term
  have h2 : Real.exp (-c0 * t / 2) * (L : ℝ) ^ mm ≤ 2 ^ mm * Real.exp (-(min c1 c2) * t) := by
    have h3 : (L : ℝ) ^ mm ≤ (2 * Real.exp (γ * t)) ^ mm := Real.rpow_le_rpow hLpos.le hLle hmm
    rw [Real.mul_rpow (by norm_num) hEpos.le, ← Real.exp_mul] at h3
    have h4 : Real.exp (γ * t * mm) ≤ Real.exp (c0 * t / 4) := by
      refine Real.exp_le_exp.2 ?_
      have : γ * mm ≤ c0 / 4 := by
        rw [hγ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith [mul_nonneg ht (sub_nonneg.2 this)]
    calc Real.exp (-c0 * t / 2) * (L : ℝ) ^ mm ≤ Real.exp (-c0 * t / 2) * (2 ^ mm * Real.exp (c0 * t / 4)) :=
          mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 (by positivity)))
            (Real.exp_pos _).le
      _ = 2 ^ mm * Real.exp (-(c0 * t / 4)) := by
          rw [← mul_assoc, mul_comm (Real.exp _) (2 ^ mm), mul_assoc, ← Real.exp_add]
          congr 2; ring
      _ ≤ 2 ^ mm * Real.exp (-(min c1 c2) * t) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
          have : min c1 c2 ≤ c2 := min_le_right _ _
          nlinarith [mul_nonneg ht (sub_nonneg.2 this)]
  have hexp0 : 0 ≤ Real.exp (-(min c1 c2) * t) := (Real.exp_pos _).le
  calc a1 * (L : ℝ) ^ (-(θ / 2)) + a2 * Real.exp (-c0 * t / 2) * (L : ℝ) ^ mm
      = a1 * (L : ℝ) ^ (-(θ / 2)) + a2 * (Real.exp (-c0 * t / 2) * (L : ℝ) ^ mm) := by ring
    _ ≤ a1 * Real.exp (-(min c1 c2) * t) + a2 * (2 ^ mm * Real.exp (-(min c1 c2) * t)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha1) (mul_le_mul_of_nonneg_left h2 ha2)
    _ ≤ (a1 + a2 * 2 ^ mm + 1) * Real.exp (-(min c1 c2) * t) := by nlinarith

end HRS.MC.QRSpec.Asm

end
