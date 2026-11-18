import HRS.Main.A8PAux43

/-!
# Packet A8P, part 44: from the `K`-sums to the stated bound `statBound`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_K_arith {K c0 Λ₁ t X : ℝ} (hK : 0 ≤ K) (hKb : K ≤ c0 * Real.exp (|Λ₁| * t) * X)
    (hc00 : 0 ≤ c0) (hc0 : c0 ≤ 2) (hX : 0 ≤ X) (ht : 0 ≤ t) :
    K + K ^ 2 ≤ 4 * Real.exp ((2 * |Λ₁| + 1) * t) * X * (1 + X) := by
  set e : ℝ := Real.exp (|Λ₁| * t) with he
  set E : ℝ := Real.exp ((2 * |Λ₁| + 1) * t) with hE
  have he1 : 1 ≤ e := Real.one_le_exp (mul_nonneg (abs_nonneg _) ht)
  have heE : e ≤ E := Real.exp_le_exp.2 (by nlinarith [abs_nonneg Λ₁])
  have he2 : e ^ 2 ≤ E := by
    rw [he, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; nlinarith [abs_nonneg Λ₁])
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have h1 : K ≤ 2 * E * X := by
    calc K ≤ c0 * e * X := hKb
      _ ≤ 2 * E * X := by
          have : c0 * e ≤ 2 * E := mul_le_mul hc0 heE (by positivity) (by norm_num)
          exact mul_le_mul_of_nonneg_right this hX
  have h2 : K ^ 2 ≤ 4 * E * X ^ 2 := by
    have hb0 : 0 ≤ c0 * e * X := by positivity
    calc K ^ 2 ≤ (c0 * e * X) ^ 2 := pow_le_pow_left₀ hK hKb 2
      _ = c0 ^ 2 * e ^ 2 * X ^ 2 := by ring
      _ ≤ 4 * E * X ^ 2 := by
          have h3 : c0 ^ 2 ≤ 4 := by nlinarith
          have : c0 ^ 2 * e ^ 2 ≤ 4 * E := mul_le_mul h3 he2 (by positivity) (by norm_num)
          exact mul_le_mul_of_nonneg_right this (sq_nonneg X)
  nlinarith [mul_nonneg hE0 hX, mul_nonneg hE0 (sq_nonneg X)]

theorem a8p_Ksum_const (Λ₁ t : ℝ) {ι : Type*} [Fintype ι] (φ : ι → Torus d → ℝ) :
    ∑ a, a8pK Λ₁ t (φ a) = Real.exp (|Λ₁| * t) * ∑ a, sobolevNorm (PDE.mStar d : ℝ) (φ a) := by
  rw [Finset.mul_sum]
  rfl

theorem a8p_Ksum_complex (Λ₁ : ℝ) {n : ℕ} (ts : Fin (n + 1) → ℝ) (hts : Monotone ts)
    (φ : Fin (n + 1) → Torus d → ℂ) :
    ∑ ab : Fin (n + 1) × Bool, a8pK Λ₁ (ts ab.1) (realImParts φ ab) ≤
      2 * Real.exp (|Λ₁| * ts (Fin.last n)) * ∑ a, sobolevNormC (PDE.mStar d : ℝ) (φ a) := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Fintype.sum_bool]
  dsimp only
  have hre : realImParts φ (a, false) = fun x => (φ a x).re := by funext x; simp [realImParts]
  have him : realImParts φ (a, true) = fun x => (φ a x).im := by funext x; simp [realImParts]
  have hC : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ Real.sqrt (x ^ 2 + y ^ 2) ∧ y ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
    intro x y hx hy
    exact ⟨Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg y]), Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg x])⟩
  have hr0 : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) (fun x => (φ a x).re) := Real.sqrt_nonneg _
  have hi0 : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) (fun x => (φ a x).im) := Real.sqrt_nonneg _
  have h1 := hC _ _ hr0 hi0
  unfold a8pK
  rw [hre, him]
  have hexp : Real.exp (|Λ₁| * ts a) ≤ Real.exp (|Λ₁| * ts (Fin.last n)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hts (Fin.le_last a)) (abs_nonneg _))
  have hC' : sobolevNormC (PDE.mStar d : ℝ) (φ a) =
      Real.sqrt (sobolevNorm (PDE.mStar d : ℝ) (fun x => (φ a x).re) ^ 2 +
        sobolevNorm (PDE.mStar d : ℝ) (fun x => (φ a x).im) ^ 2) := rfl
  rw [hC']
  have he0 : 0 ≤ Real.exp (|Λ₁| * ts a) := (Real.exp_pos _).le
  calc Real.exp (|Λ₁| * ts a) * sobolevNorm (PDE.mStar d : ℝ) (fun x => (φ a x).im) +
        Real.exp (|Λ₁| * ts a) * sobolevNorm (PDE.mStar d : ℝ) (fun x => (φ a x).re)
      = Real.exp (|Λ₁| * ts a) * (sobolevNorm (PDE.mStar d : ℝ) (fun x => (φ a x).im) +
          sobolevNorm (PDE.mStar d : ℝ) (fun x => (φ a x).re)) := by ring
    _ ≤ Real.exp (|Λ₁| * ts (Fin.last n)) * (2 * Real.sqrt (sobolevNorm (PDE.mStar d : ℝ) (fun x => (φ a x).re) ^ 2 +
        sobolevNorm (PDE.mStar d : ℝ) (fun x => (φ a x).im) ^ 2)) := by
          refine mul_le_mul hexp (by linarith [h1.1, h1.2]) (by positivity) (Real.exp_pos _).le
    _ = _ := by ring

end HRS.Main.A8P
