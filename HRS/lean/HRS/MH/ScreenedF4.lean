import HRS.MH.ScreenedDefs

/-! Packet F4 of `B:lem:screened` (S.B.4): proof of the statement of `flowCell_weight` in `ScreenedSpec.lean`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem f4_box_norm_le (v : Euc d) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) : ‖v‖ ≤ Real.sqrt d := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [Real.norm_eq_abs, sq_abs]; nlinarith [hv i]
    _ = d := by simp

theorem f4_jb_le_one_add (c : Euc d) : jbracket c ≤ 1 + ‖c‖ := by
  unfold jbracket
  calc Real.sqrt (1 + ‖c‖ ^ 2) ≤ Real.sqrt ((1 + ‖c‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg c])
    _ = 1 + ‖c‖ := Real.sqrt_sq (by positivity)

theorem f4_norm_le_jb (y : Euc d) : ‖y‖ ≤ jbracket y := by
  unfold jbracket
  calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg y)).symm
    _ ≤ Real.sqrt (1 + ‖y‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)

theorem f4_one_le_jb (y : Euc d) : 1 ≤ jbracket y := by
  unfold jbracket
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖y‖ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖y‖])

/-- **F4** (size S).  Weight comparison on cells: `⟨z'⟩ ≤ (L + L B + √d + 1) ⟨y⟩` for `y ∈ Q_{z'}`
(`‖Φ y‖ ≤ ‖Φ y - Φ 0‖ + ‖Φ 0‖ ≤ L‖y‖ + L‖Ψ 0‖`, `‖Φ y - z'‖ ≤ √d`). -/
theorem flowCell_weight_proof (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hbij : Function.Bijective (Ψ τ))
    (hlipi : ∀ x y, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ L * ‖x - y‖)
    (horig : ‖Ψ τ 0‖ ≤ B) :
    ∀ (z : Fin d → ℤ) (y : Euc d), y ∈ flowCell Ψ τ z →
      jbracket (latticePt z) ≤ (L + L * B + Real.sqrt d + 1) * jbracket y := by
  intro z y hy
  unfold flowCell at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have hΦy : Function.invFun (Ψ τ) y = x := by
    rw [← hxy]; exact Function.leftInverse_invFun hbij.injective x
  have h0 : Function.invFun (Ψ τ) (Ψ τ 0) = 0 := Function.leftInverse_invFun hbij.injective 0
  have hΦ0 : ‖Function.invFun (Ψ τ) 0‖ ≤ L * B := by
    have h := hlipi 0 (Ψ τ 0)
    rw [h0, sub_zero, zero_sub, norm_neg] at h
    exact le_trans h (mul_le_mul_of_nonneg_left horig hL)
  have hbox : ‖x - latticePt z‖ ≤ Real.sqrt d := f4_box_norm_le _ hx
  have hΦlip : ‖Function.invFun (Ψ τ) y‖ ≤ L * ‖y‖ + L * B := by
    have h1 := hlipi y 0
    simp only [sub_zero] at h1
    have h2 := norm_sub_norm_le (Function.invFun (Ψ τ) y) (Function.invFun (Ψ τ) 0)
    linarith
  rw [hΦy] at hΦlip
  have hsplit : ‖latticePt z‖ ≤ ‖x‖ + ‖x - latticePt z‖ := by
    have h := norm_sub_norm_le (latticePt z) x
    rw [norm_sub_rev] at h
    linarith
  have hJ1 := f4_one_le_jb y
  have hJn := f4_norm_le_jb y
  have hc := f4_jb_le_one_add (latticePt z)
  have hq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  calc jbracket (latticePt z) ≤ 1 + ‖latticePt z‖ := hc
    _ ≤ (L + L * B + Real.sqrt d + 1) * jbracket y := by
        nlinarith [mul_nonneg hL (sub_nonneg.2 hJn), mul_nonneg (mul_nonneg hL hB) (sub_nonneg.2 hJ1),
          mul_nonneg hq (sub_nonneg.2 hJ1)]

end HRS.MH.Screened
