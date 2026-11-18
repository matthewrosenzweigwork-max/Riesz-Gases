import HRS.MC.S7PIDRFour

/-!
# Packet PI-D, `s7_PID_gradprod`: proof (`s7_PID_gradprod_proof`)

Statement verbatim from `HRS/MC/S7PIDPlan.lean` (`HRS.MC.Sec7.PIDPlan.s7_PID_gradprod`); the tie is in `S7PIDRTie.lean`.
Constant `C = 2(1+2^r)`, valid for every `d` (for `d = 0` the index type is empty and everything is vacuous).

Route: with `φ = ∇e_k·∇e_l`, `|φ| ≤ 2⟨k⟩⟨l⟩` (`S7PIDR_gradProd_abs_le`), so `∫φ² ≤ 4X²`, `X = ⟨k⟩⟨l⟩`; Bessel
(`Torus.hasSum_sq_coeff`) bounds `∑_n |φ̂_n|²` by `∫φ²`; `φ̂_n = 0` unless `n ∈ {±k±l}` where `⟨n⟩^{2r} ≤ (2X²)^r`
(`S7PIDR_jp_sq_le_of_InS`); and `f_n² ≤ 2(cos²+sin²)` for the real coefficients.  Hence
`mean² + ∑_n ⟨n⟩^{2r} f_n² ≤ (1 + 2W)∫φ²` with `W = (2X²)^r = 2^r (X^r)²`, and the square root is `≤ 2(1+2^r) X^{r+1}`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDR

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

theorem S7PIDR_alg (P Q X T W : ℝ) (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hW : W = P * Q ^ 2)
    (hT : T ≤ (2 * X) ^ 2) : T + 2 * W * T ≤ (2 * (1 + P) * (Q * X)) ^ 2 := by
  have hQ2 : 1 ≤ Q ^ 2 := by nlinarith
  have hW0 : 0 ≤ 1 + 2 * W := by
    rw [hW]
    nlinarith [mul_nonneg (sub_nonneg.2 hP) (sq_nonneg Q)]
  have h2 : 1 + 2 * W ≤ (1 + P) ^ 2 * Q ^ 2 := by
    rw [hW]
    nlinarith [sq_nonneg P, mul_nonneg (sq_nonneg P) (sub_nonneg.2 hQ2)]
  have h3 : (1 + 2 * W) * T ≤ (1 + 2 * W) * (2 * X) ^ 2 := mul_le_mul_of_nonneg_left hT hW0
  have h4 : (1 + 2 * W) * (2 * X) ^ 2 ≤ (1 + P) ^ 2 * Q ^ 2 * (2 * X) ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have h5 : T + 2 * W * T = (1 + 2 * W) * T := by ring
  rw [h5]
  calc (1 + 2 * W) * T ≤ (1 + P) ^ 2 * Q ^ 2 * (2 * X) ^ 2 := h3.trans h4
    _ = (2 * (1 + P) * (Q * X)) ^ 2 := by ring

theorem S7PIDR_main (r : ℝ) (hr : 0 ≤ r) (k l : NonzeroLattice d) :
    MemSobolev r (gradProd k l) ∧
      sobolevNorm r (gradProd k l) ≤
        2 * (1 + 2 ^ r) * Lattice.jp k.1 ^ (r + 1) * Lattice.jp l.1 ^ (r + 1) := by
  have hjk : 1 ≤ Lattice.jp k.1 := Torus.jp_ge_one _
  have hjl : 1 ≤ Lattice.jp l.1 := Torus.jp_ge_one _
  have hk0 : 0 ≤ Lattice.jp k.1 := by linarith
  have hl0 : 0 ≤ Lattice.jp l.1 := by linarith
  have hX1 : 1 ≤ Lattice.jp k.1 * Lattice.jp l.1 := one_le_mul_of_one_le_of_one_le hjk hjl
  have hX0 : 0 ≤ Lattice.jp k.1 * Lattice.jp l.1 := by linarith
  have hXne : Lattice.jp k.1 * Lattice.jp l.1 ≠ 0 := by linarith
  -- the function `φ = ∇e_k·∇e_l`: continuous, bounded, in L²
  have hcont := S7PIDR_gradProd_continuous k l
  have hL2 : MemLp (gradProd k l) 2 volume :=
    MemLp.of_bound hcont.aestronglyMeasurable (2 * (Lattice.jp k.1 * Lattice.jp l.1))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact S7PIDR_gradProd_abs_le k l x)
  have hint : Integrable (gradProd k l) := hL2.integrable one_le_two
  have hB := Torus.hasSum_sq_coeff hL2
  have hT4 : ∫ x, gradProd k l x ^ 2 ≤ (2 * (Lattice.jp k.1 * Lattice.jp l.1)) ^ 2 := by
    have h := integral_mono hL2.integrable_sq
      (integrable_const ((2 * (Lattice.jp k.1 * Lattice.jp l.1)) ^ 2))
      (fun x => by
        have h1 := S7PIDR_gradProd_abs_le k l x
        have h2 : gradProd k l x ^ 2 = |gradProd k l x| ^ 2 := (sq_abs _).symm
        rw [h2]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2)
    simpa using h
  set T : ℝ := ∫ x, gradProd k l x ^ 2 with hTdef
  set W : ℝ := (2 * (Lattice.jp k.1 * Lattice.jp l.1) ^ 2) ^ r with hWdef
  have hW0 : 0 ≤ W := Real.rpow_nonneg (by positivity) _
  -- frequencies `n ∈ {±k±l}` have weight at most `W`
  have hwS : ∀ n : Lattice d, S7PIDR_InS k.1 l.1 n → Lattice.jp n ^ (2 * r) ≤ W := by
    intro n hn
    rw [S7PIDR_rpow_sq _ (Torus.jp_pos n).le r]
    exact Real.rpow_le_rpow (sq_nonneg _) (S7PIDR_jp_sq_le_of_InS k.1 l.1 n hn) hr
  -- termwise bound `⟨n⟩^{2r} f_n² ≤ 2 W (cos² + sin²)(n)`
  have hfw : ∀ n : NonzeroLattice d,
      Lattice.jp n.1 ^ (2 * r) * Torus.funRealCoeff (gradProd k l) n ^ 2 ≤
        2 * W * (Torus.cosCoeff (gradProd k l) n.1 ^ 2 + Torus.sinCoeff (gradProd k l) n.1 ^ 2) := by
    intro n
    have h2 := S7PIDR_f_sq_le (gradProd k l) n
    have hw0 : 0 ≤ Lattice.jp n.1 ^ (2 * r) := Real.rpow_nonneg (Torus.jp_pos n.1).le _
    by_cases hS : S7PIDR_InS k.1 l.1 n.1
    · have h1 := hwS n.1 hS
      calc Lattice.jp n.1 ^ (2 * r) * Torus.funRealCoeff (gradProd k l) n ^ 2
          ≤ W * Torus.funRealCoeff (gradProd k l) n ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ ≤ W * (2 * (Torus.cosCoeff (gradProd k l) n.1 ^ 2 + Torus.sinCoeff (gradProd k l) n.1 ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 hW0
        _ = 2 * W * (Torus.cosCoeff (gradProd k l) n.1 ^ 2 + Torus.sinCoeff (gradProd k l) n.1 ^ 2) := by
            ring
    · have hc := S7PIDR_c2_zero k l n.1 hS hint
      have hf0 : Torus.funRealCoeff (gradProd k l) n ^ 2 ≤ 0 := by
        rw [hc] at h2
        linarith
      calc Lattice.jp n.1 ^ (2 * r) * Torus.funRealCoeff (gradProd k l) n ^ 2
          ≤ Lattice.jp n.1 ^ (2 * r) * 0 := mul_le_mul_of_nonneg_left hf0 hw0
        _ = 2 * W * (Torus.cosCoeff (gradProd k l) n.1 ^ 2 + Torus.sinCoeff (gradProd k l) n.1 ^ 2) := by
            rw [hc]
            ring
  have hsumc : Summable (fun n : Lattice d =>
      2 * W * (Torus.cosCoeff (gradProd k l) n ^ 2 + Torus.sinCoeff (gradProd k l) n ^ 2)) :=
    hB.summable.mul_left (2 * W)
  have hsumNZ_g : Summable (fun n : NonzeroLattice d =>
      2 * W * (Torus.cosCoeff (gradProd k l) n.1 ^ 2 + Torus.sinCoeff (gradProd k l) n.1 ^ 2)) :=
    hsumc.subtype (fun n : Lattice d => n ≠ 0)
  have hsumNZ : Summable (fun n : NonzeroLattice d =>
      Lattice.jp n.1 ^ (2 * r) * Torus.funRealCoeff (gradProd k l) n ^ 2) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos n.1).le _) (sq_nonneg _)) hfw hsumNZ_g
  have hle1 : ∑' n : NonzeroLattice d, Lattice.jp n.1 ^ (2 * r) * Torus.funRealCoeff (gradProd k l) n ^ 2 ≤
      ∑' n : NonzeroLattice d,
        2 * W * (Torus.cosCoeff (gradProd k l) n.1 ^ 2 + Torus.sinCoeff (gradProd k l) n.1 ^ 2) :=
    Summable.tsum_le_tsum hfw hsumNZ hsumNZ_g
  have hle2 : ∑' n : NonzeroLattice d,
        2 * W * (Torus.cosCoeff (gradProd k l) n.1 ^ 2 + Torus.sinCoeff (gradProd k l) n.1 ^ 2) ≤
      ∑' n : Lattice d, 2 * W * (Torus.cosCoeff (gradProd k l) n ^ 2 + Torus.sinCoeff (gradProd k l) n ^ 2) :=
    Summable.tsum_subtype_le _ _ (fun n => mul_nonneg (by positivity) (by positivity)) hsumc
  have hle3 : ∑' n : Lattice d, 2 * W * (Torus.cosCoeff (gradProd k l) n ^ 2 + Torus.sinCoeff (gradProd k l) n ^ 2)
      = 2 * W * T := by
    rw [tsum_mul_left, hB.tsum_eq]
  -- the zero mode and the total
  have hmean : Torus.mean (gradProd k l) ^ 2 ≤
      Torus.cosCoeff (gradProd k l) 0 ^ 2 + Torus.sinCoeff (gradProd k l) 0 ^ 2 := by
    rw [S7PIDR_mean_eq_cos]
    nlinarith [sq_nonneg (Torus.sinCoeff (gradProd k l) 0)]
  have hc0T : Torus.cosCoeff (gradProd k l) 0 ^ 2 + Torus.sinCoeff (gradProd k l) 0 ^ 2 ≤ T :=
    le_hasSum hB 0 (fun j _ => by positivity)
  have hsobsq : Torus.mean (gradProd k l) ^ 2 +
      ∑' n : NonzeroLattice d, Lattice.jp n.1 ^ (2 * r) * Torus.funRealCoeff (gradProd k l) n ^ 2 ≤
        T + 2 * W * T := by
    linarith
  -- the algebra: `T ≤ 4X²`, `W = 2^r (X^r)²`
  have hWQ : W = 2 ^ r * ((Lattice.jp k.1 * Lattice.jp l.1) ^ r) ^ 2 := by
    rw [hWdef, Real.mul_rpow (by norm_num) (by positivity),
      show (Lattice.jp k.1 * Lattice.jp l.1) ^ 2 =
        (Lattice.jp k.1 * Lattice.jp l.1) * (Lattice.jp k.1 * Lattice.jp l.1) by ring,
      Real.mul_rpow hX0 hX0]
    ring
  have hP1 : (1 : ℝ) ≤ 2 ^ r := Real.one_le_rpow (by norm_num) hr
  have hQ1 : (1 : ℝ) ≤ (Lattice.jp k.1 * Lattice.jp l.1) ^ r := Real.one_le_rpow hX1 hr
  have hineq := le_trans hsobsq
    (S7PIDR_alg (2 ^ r) ((Lattice.jp k.1 * Lattice.jp l.1) ^ r) (Lattice.jp k.1 * Lattice.jp l.1) T W
      hP1 hQ1 hWQ hT4)
  have hRHS : 2 * (1 + 2 ^ r) * Lattice.jp k.1 ^ (r + 1) * Lattice.jp l.1 ^ (r + 1) =
      2 * (1 + 2 ^ r) * ((Lattice.jp k.1 * Lattice.jp l.1) ^ r * (Lattice.jp k.1 * Lattice.jp l.1)) := by
    rw [mul_assoc (2 * (1 + 2 ^ r)), ← Real.mul_rpow hk0 hl0, Real.rpow_add_one hXne]
  refine ⟨⟨hL2, hsumNZ⟩, ?_⟩
  unfold sobolevNorm
  rw [hRHS]
  refine (Real.sqrt_le_sqrt hineq).trans (le_of_eq (Real.sqrt_sq ?_))
  exact mul_nonneg (by positivity)
    (mul_nonneg (Real.rpow_nonneg hX0 _) hX0)

/-- **Packet PI-D, `s7_PID_gradprod` (`∇e_k·∇e_l` in `H^r`)**: verbatim statement of `HRS.MC.Sec7.PIDPlan.s7_PID_gradprod`. -/
theorem s7_PID_gradprod_proof (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k l : NonzeroLattice d, MemSobolev r (gradProd k l) ∧
      sobolevNorm r (gradProd k l) ≤ C * Lattice.jp k.1 ^ (r + 1) * Lattice.jp l.1 ^ (r + 1) :=
  ⟨2 * (1 + 2 ^ r), by positivity, fun k l => S7PIDR_main r hr k l⟩

end HRS.MC.Sec7.S7PIDR

end
