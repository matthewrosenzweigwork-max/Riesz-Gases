import HRS.Uniform.Q54Aux20

/-!
# EQP7D: the decay chain with uniform constants (support for P7.7)

`HRS.Uniform.Q54.decay_chain` produces the constant `Cr` only inside an existential, so it cannot be
applied with one constant for all `β`.  `eqevo_decay_chain` is the same argument with the constant
written out: `Cr` depends only on `n`, `Cj`, `cj`, `C` and the smoothing constants `Ms i`, not on the
evolution `Vev`.  The rate is `cj` itself.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQEvoChain

open HRS HRS.PDE HRS.Uniform.Q48b HRS.Uniform.Q54

variable {d : ℕ}

/-- Uniform decay chain: the witness `Cr` is fixed by the data, before the evolution `Vev`. -/
theorem eqevo_decay_chain {r j δ cj Cj C : ℝ} (n : ℕ) (hδ : 0 < δ) (hn : j = r + n * δ)
    (hcj : 0 < cj) (Ms : ℕ → ℝ) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ (Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r),
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp (C * (t - u))) →
      (∀ s r' t : ℝ, 0 ≤ s → s ≤ r' → r' ≤ t → (Vev t r').comp (Vev r' s) = Vev t s) →
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → WB2 j j (Cj * Real.exp (-cj * (t - u))) (q48bMat r (Vev t u))) →
      (∀ i : ℕ, i < n → ∀ s : ℝ, 0 ≤ s →
        WB2 (j - ((i : ℝ) + 1) * δ) (j - (i : ℝ) * δ) (Ms i) (q48bMat r (Vev (s + 1) s))) →
      ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cj * (t - u)) := by
  set P : ℕ → ℝ := fun i => ∏ k ∈ Finset.range i, Ms k with hP
  have hP0 : P 0 = 1 := by simp [hP]
  have hPs : ∀ i : ℕ, P (i + 1) = P i * Ms i := fun i => by
    simp [hP, Finset.prod_range_succ]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrj : r ≤ j := by rw [hn]; nlinarith
  refine ⟨|Cj * P n| * Real.exp (cj * n) + Real.exp ((|C| + cj) * n) + 1, by positivity,
    fun Vev hbd hcoc htop hsm => ?_⟩
  have hind : ∀ i : ℕ, i ≤ n → ∀ u t : ℝ, 0 ≤ u → u + i ≤ t → ∀ x : NegSobolev d r,
      fsq (j - (i : ℝ) * δ) (Vev t u x) ≤
        (Cj * P i) ^ 2 * Real.exp (-2 * cj * (t - u - i)) * fsq j x := by
    intro i
    induction i with
    | zero =>
      intro _ u t hu hut x
      have h := (fsq_le_of_wb2 (Vev t u) (htop u t hu (by simpa using hut)) hrj x).2
      simp only [Nat.cast_zero, zero_mul, sub_zero, hP0, mul_one]
      refine h.trans (le_of_eq ?_)
      rw [mul_pow, exp_sq']
      congr 2
      ring
    | succ i ih =>
      intro hi u t hu hut x
      have hi' : i ≤ n := by omega
      have hi1 : (((i + 1 : ℕ)) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
      rw [hi1] at hut ⊢
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hs0 : 0 ≤ t - 1 := by linarith
      have hus : u ≤ t - 1 := by linarith
      have hcoc' := hcoc u (t - 1) t hu hus (by linarith)
      have hVx : Vev t u x = Vev (t - 1 + 1) (t - 1) (Vev (t - 1) u x) := by
        have := congrArg (fun L => L x) hcoc'
        simp only [ContinuousLinearMap.comp_apply] at this
        rw [show t - 1 + 1 = t by ring]
        exact this.symm
      have hbi : r ≤ j - (i : ℝ) * δ := by
        have hile : (i : ℝ) ≤ n := by exact_mod_cast hi'
        rw [hn]; nlinarith
      have h1 := (fsq_le_of_wb2 (Vev (t - 1 + 1) (t - 1)) (hsm i (by omega) (t - 1) hs0) hbi
        (Vev (t - 1) u x)).2
      have h2 := ih hi' u (t - 1) hu (by linarith) x
      rw [hVx]
      calc fsq (j - ((i : ℝ) + 1) * δ) (Vev (t - 1 + 1) (t - 1) (Vev (t - 1) u x))
          ≤ Ms i ^ 2 * fsq (j - (i : ℝ) * δ) (Vev (t - 1) u x) := h1
        _ ≤ Ms i ^ 2 * ((Cj * P i) ^ 2 * Real.exp (-2 * cj * (t - 1 - u - i)) * fsq j x) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = (Cj * P (i + 1)) ^ 2 * Real.exp (-2 * cj * (t - u - ((i : ℝ) + 1))) * fsq j x := by
            rw [hPs, show t - 1 - u - (i : ℝ) = t - u - ((i : ℝ) + 1) by ring]
            ring
  have hCn := hind n le_rfl
  have hr : j - (n : ℝ) * δ = r := by rw [hn]; ring
  have hCn0 : 0 ≤ |Cj * P n| := abs_nonneg _
  intro u t hu hut
  by_cases hcase : u + n ≤ t
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have h := hCn u t hu hcase x
    rw [hr, fsq_self, ← sq_abs (Cj * P n)] at h
    have hx : fsq j x ≤ ‖x‖ ^ 2 := by
      have := fsq_le_of_le (le_refl r) hrj x
      rwa [fsq_self] at this
    have h' : ‖Vev t u x‖ ^ 2 ≤ (|Cj * P n| * Real.exp (-cj * (t - u - n)) * ‖x‖) ^ 2 := by
      calc ‖Vev t u x‖ ^ 2 ≤ |Cj * P n| ^ 2 * Real.exp (-2 * cj * (t - u - n)) * fsq j x := h
        _ ≤ |Cj * P n| ^ 2 * Real.exp (-2 * cj * (t - u - n)) * ‖x‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hx (by positivity)
        _ = _ := by
            rw [mul_pow, mul_pow, exp_sq']
            congr 3
            ring
    have h'' := le_of_sq_le_sq h' (mul_nonneg (mul_nonneg hCn0 (Real.exp_pos _).le) (norm_nonneg x))
    have e : |Cj * P n| * Real.exp (-cj * (t - u - n))
        = (|Cj * P n| * Real.exp (cj * n)) * Real.exp (-cj * (t - u)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [e] at h''
    have hK1 : |Cj * P n| * Real.exp (cj * n) ≤
        |Cj * P n| * Real.exp (cj * n) + Real.exp ((|C| + cj) * n) + 1 := by
      have := Real.exp_pos ((|C| + cj) * n)
      linarith
    refine h''.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 (Real.exp_pos _).le) (norm_nonneg x)
  · rw [not_le] at hcase
    have hlt : t - u ≤ n := by linarith
    have hb := hbd u t hu hut
    have hexp0 : 0 < Real.exp (-cj * (t - u)) := Real.exp_pos _
    have h1 : Real.exp (C * (t - u)) ≤ Real.exp (|C| * n) := exp_mul_le C (by linarith) hlt
    have h2 : Real.exp (|C| * n) ≤ Real.exp ((|C| + cj) * n) * Real.exp (-cj * (t - u)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : cj * (t - u) ≤ cj * n := mul_le_mul_of_nonneg_left hlt hcj.le
      nlinarith
    have hK2 : Real.exp ((|C| + cj) * n) ≤
        |Cj * P n| * Real.exp (cj * n) + Real.exp ((|C| + cj) * n) + 1 := by
      have := mul_nonneg hCn0 (Real.exp_pos (cj * n)).le
      linarith
    exact (hb.trans (h1.trans h2)).trans (mul_le_mul_of_nonneg_right hK2 hexp0.le)

end HRS.MD.EQEvoChain
