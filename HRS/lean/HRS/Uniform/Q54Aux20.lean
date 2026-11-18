import HRS.Uniform.Q54Aux17

/-!
# Q54, part 20: exponential decay at a low level from decay at a high level and unit-time smoothing

Abstract operator statement.  `V^{t,u}` is a cocycle of bounded operators on `E_r`, quasi-contractive, with the finite block
decay bound at the top level `j = r + nδ` (`WB2 j j (C_j e^{-c_j (t-u)})`) and the block smoothing bound over unit time
`‖V^{s+1,s}‖_{E_{a+δ} → E_a} ≤ M` at the levels `a = j - (i+1) δ`.  Then `‖V^{t,u}‖_{E_r → E_r} ≤ C e^{-c (t-u)}`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.Uniform.Q48b

variable {d : ℕ}

theorem exp_sq' (x : ℝ) : Real.exp x ^ 2 = Real.exp (2 * x) := by
  rw [sq, ← Real.exp_add]; ring_nf

theorem decay_chain {r j δ cj Cj C : ℝ} (n : ℕ) (hδ : 0 < δ) (hn : j = r + n * δ)
    (Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r)
    (hbd : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp (C * (t - u)))
    (hcoc : ∀ s r' t : ℝ, 0 ≤ s → s ≤ r' → r' ≤ t → (Vev t r').comp (Vev r' s) = Vev t s)
    (hCj : 0 ≤ Cj) (hcj : 0 < cj)
    (htop : ∀ u t : ℝ, 0 ≤ u → u ≤ t →
      WB2 j j (Cj * Real.exp (-cj * (t - u))) (q48bMat r (Vev t u)))
    (hsm : ∀ i : ℕ, i < n → ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 ≤ s →
      WB2 (j - ((i : ℝ) + 1) * δ) (j - (i : ℝ) * δ) M (q48bMat r (Vev (s + 1) s))) :
    ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t →
      ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrj : r ≤ j := by rw [hn]; nlinarith
  have hind : ∀ i : ℕ, i ≤ n → ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ u t : ℝ, 0 ≤ u → u + i ≤ t →
      ∀ x : NegSobolev d r, fsq (j - (i : ℝ) * δ) (Vev t u x) ≤
        Ci ^ 2 * Real.exp (-2 * cj * (t - u - i)) * fsq j x := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨Cj, hCj, fun u t hu hut x => ?_⟩
      have h := (fsq_le_of_wb2 (Vev t u) (htop u t hu (by simpa using hut)) hrj x).2
      simp only [Nat.cast_zero, zero_mul, sub_zero]
      refine h.trans (le_of_eq ?_)
      rw [mul_pow, exp_sq']
      congr 2
      ring
    | succ i ih =>
      intro hi
      obtain ⟨Ci, hCi, hCi'⟩ := ih (by omega)
      obtain ⟨M, hM0, hM⟩ := hsm i (by omega)
      refine ⟨M * Ci, mul_nonneg hM0 hCi, fun u t hu hut x => ?_⟩
      have hi1 : (((i + 1 : ℕ) : ℝ)) = (i : ℝ) + 1 := by push_cast; ring
      rw [hi1] at hut ⊢
      have hs0 : 0 ≤ t - 1 := by
        have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        linarith
      have hus : u ≤ t - 1 := by
        have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        linarith
      have hcoc' := hcoc u (t - 1) t hu hus (by linarith)
      have hVx : Vev t u x = Vev (t - 1 + 1) (t - 1) (Vev (t - 1) u x) := by
        have := congrArg (fun L => L x) hcoc'
        simp only [ContinuousLinearMap.comp_apply] at this
        rw [show t - 1 + 1 = t by ring]
        exact this.symm
      have hbi : r ≤ j - (i : ℝ) * δ := by
        have hile : (i : ℝ) ≤ n := by exact_mod_cast (by omega : i ≤ n)
        rw [hn]; nlinarith
      have h1 := (fsq_le_of_wb2 (Vev (t - 1 + 1) (t - 1)) (hM (t - 1) hs0) hbi (Vev (t - 1) u x)).2
      have h2 := hCi' u (t - 1) hu (by linarith) x
      rw [hVx]
      calc fsq (j - ((i : ℝ) + 1) * δ) (Vev (t - 1 + 1) (t - 1) (Vev (t - 1) u x))
          ≤ M ^ 2 * fsq (j - (i : ℝ) * δ) (Vev (t - 1) u x) := h1
        _ ≤ M ^ 2 * (Ci ^ 2 * Real.exp (-2 * cj * (t - 1 - u - i)) * fsq j x) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg M)
        _ = (M * Ci) ^ 2 * Real.exp (-2 * cj * (t - u - ((i : ℝ) + 1))) * fsq j x := by
            rw [show t - 1 - u - (i : ℝ) = t - u - ((i : ℝ) + 1) by ring]; ring
  obtain ⟨Cn, hCn0, hCn⟩ := hind n le_rfl
  have hr : j - (n : ℝ) * δ = r := by rw [hn]; ring
  set K1 : ℝ := Cn * Real.exp (cj * n) with hK1
  set K2 : ℝ := Real.exp ((|C| + cj) * n) with hK2
  refine ⟨max K1 K2 + 1, cj, by positivity, hcj, fun u t hu hut => ?_⟩
  have hK1' : K1 ≤ max K1 K2 + 1 := (le_max_left _ _).trans (by linarith)
  have hK2' : K2 ≤ max K1 K2 + 1 := (le_max_right _ _).trans (by linarith)
  have hexp0 : 0 < Real.exp (-cj * (t - u)) := Real.exp_pos _
  by_cases hcase : u + n ≤ t
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have h := hCn u t hu hcase x
    rw [hr, fsq_self] at h
    have hx : fsq j x ≤ ‖x‖ ^ 2 := by
      have := fsq_le_of_le (le_refl r) hrj x
      rwa [fsq_self] at this
    have h' : ‖Vev t u x‖ ^ 2 ≤ (Cn * Real.exp (-cj * (t - u - n)) * ‖x‖) ^ 2 := by
      calc ‖Vev t u x‖ ^ 2 ≤ Cn ^ 2 * Real.exp (-2 * cj * (t - u - n)) * fsq j x := h
        _ ≤ Cn ^ 2 * Real.exp (-2 * cj * (t - u - n)) * ‖x‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hx (by positivity)
        _ = _ := by
            rw [mul_pow, mul_pow, exp_sq']
            congr 3
            ring
    have h'' := le_of_sq_le_sq h' (by positivity)
    have e : Cn * Real.exp (-cj * (t - u - n)) = K1 * Real.exp (-cj * (t - u)) := by
      rw [hK1, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [e] at h''
    refine h''.trans ?_
    have : K1 * Real.exp (-cj * (t - u)) ≤ (max K1 K2 + 1) * Real.exp (-cj * (t - u)) :=
      mul_le_mul_of_nonneg_right hK1' hexp0.le
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  · push Not at hcase
    have hlt : t - u ≤ n := by linarith
    have hb := hbd u t hu hut
    have h1 : Real.exp (C * (t - u)) ≤ Real.exp (|C| * n) := exp_mul_le C (by linarith) hlt
    have h2 : Real.exp (|C| * n) ≤ K2 * Real.exp (-cj * (t - u)) := by
      rw [hK2, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : cj * (t - u) ≤ cj * n := mul_le_mul_of_nonneg_left hlt hcj.le
      nlinarith
    exact (hb.trans (h1.trans h2)).trans (mul_le_mul_of_nonneg_right hK2' hexp0.le)

end HRS.Uniform.Q54
