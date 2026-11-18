import HRS.MS.FeatDecAux7

/-!
# S8.5 `feature_decay`, part 8 (S85 packet): symbol bounds of the weights `⟨x⟩^r`

`s85_jb_sym`: `‖D^i ⟨·⟩^r (x)‖ ≤ C_{i,r} ⟨x⟩^{r-i}` for every real `r` (induction on `i`, `D⟨x⟩^r = r⟨x⟩^{r-2} ⟨x,·⟩`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole

variable {d : ℕ}

theorem s85_jbpow_eq (x : Euc d) (r : ℝ) : jbracket x ^ r = (1 + ‖x‖ ^ 2) ^ (r / 2) := by
  unfold jbracket
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem s85_jbpow_contDiff (r : ℝ) : ContDiff ℝ ∞ (fun x : Euc d => jbracket x ^ r) := by
  simp_rw [s85_jbpow_eq]
  exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Euc d) (r / 2)).1

theorem s85_jbpow_fderiv (r : ℝ) (x : Euc d) :
    fderiv ℝ (fun x : Euc d => jbracket x ^ r) x = (r * jbracket x ^ (r - 2)) • innerSL ℝ x := by
  have h0 : (fun x : Euc d => jbracket x ^ r) = fun x : Euc d => (1 + ‖x‖ ^ 2) ^ (r / 2) := by
    funext y; exact s85_jbpow_eq y r
  rw [h0]
  have h1 : HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2) ((2 : ℝ) • innerSL ℝ x) x := by
    have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have e : ((2 : ℕ) • innerSL ℝ x : Euc d →L[ℝ] ℝ) = (2 : ℝ) • innerSL ℝ x := by
      rw [two_smul, two_smul]
    rw [e] at h
    exact h
  have h2 := (h1.const_add 1).rpow_const (p := r / 2) (Or.inl (by positivity))
  rw [h2.fderiv]
  rw [smul_smul]
  congr 1
  have e3 : jbracket x ^ (r - 2) = (1 + ‖x‖ ^ 2) ^ (r / 2 - 1) := by
    rw [s85_jbpow_eq]; congr 1; ring
  rw [e3]
  ring

theorem s85_innerSL_iter (k : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun x : Euc d => (innerSL ℝ x : Euc d →L[ℝ] ℝ)) x‖ ≤
      jbracket x ^ ((1 : ℝ) - k) := by
  have hcd : ContDiff ℝ ∞ (fun x : Euc d => (innerSL ℝ x : Euc d →L[ℝ] ℝ)) :=
    (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).contDiff
  have hjb1 : 1 ≤ jbracket x := HRS.MS.Adj.ad1_one_le_jb x
  rcases k with _ | k
  · rw [norm_iteratedFDeriv_zero]
    simp only [Nat.cast_zero, sub_zero, Real.rpow_one]
    have : ‖(innerSL ℝ x : Euc d →L[ℝ] ℝ)‖ = ‖x‖ := innerSL_apply_norm ℝ x
    rw [this]
    unfold jbracket
    exact Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg x])
  · have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun x : Euc d => (innerSL ℝ x : Euc d →L[ℝ] ℝ))
      (x := x) (n := k)
    have e : fderiv ℝ (fun x : Euc d => (innerSL ℝ x : Euc d →L[ℝ] ℝ)) = fun _ => innerSL ℝ := by
      funext y
      exact (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).fderiv
    rw [← h1, e]
    rcases k with _ | k
    · rw [norm_iteratedFDeriv_zero]
      have : (1 : ℝ) - ((0 + 1 : ℕ) : ℝ) = 0 := by norm_num
      rw [this, Real.rpow_zero]
      exact norm_innerSL_le ℝ
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      rw [Pi.zero_apply, norm_zero]
      exact (Real.rpow_pos_of_pos (by linarith) _).le

theorem s85_jb_sym (i : ℕ) : ∀ l ≤ i, ∀ r : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc d,
    ‖iteratedFDeriv ℝ l (fun x : Euc d => jbracket x ^ r) x‖ ≤ C * jbracket x ^ (r - l) := by
  induction i with
  | zero =>
    intro l hl r
    have : l = 0 := by omega
    subst this
    refine ⟨1, zero_le_one, fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    simp only [Nat.cast_zero, sub_zero, one_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (u2_jb_pos x).le _)]
  | succ i ih =>
    intro l hl r
    rcases Nat.lt_or_ge l (i + 1) with hlt | hge
    · exact ih l (by omega) r
    · have hl' : l = i + 1 := by omega
      subst hl'
      -- the induction hypothesis for `r - 2` and all orders `≤ i`
      have hIH := fun l' (hl' : l' ≤ i) => ih l' hl' (r - 2)
      choose! C hC0 hC using hIH
      refine ⟨∑ l' ∈ Finset.range (i + 1), (i.choose l' : ℝ) * (|r| * C l'), ?_, fun x => ?_⟩
      · exact Finset.sum_nonneg fun l' _ => mul_nonneg (by positivity)
          (mul_nonneg (abs_nonneg _) (hC0 l' (by have := Finset.mem_range.1 ‹_›; omega)))
      · have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun x : Euc d => jbracket x ^ r)
          (x := x) (n := i)
        rw [← h1]
        have e : fderiv ℝ (fun x : Euc d => jbracket x ^ r) =
            fun x => (r * jbracket x ^ (r - 2)) • innerSL ℝ x := funext (s85_jbpow_fderiv r)
        rw [e]
        have hf : ContDiff ℝ ∞ (fun x : Euc d => r * jbracket x ^ (r - 2)) :=
          contDiff_const.mul (s85_jbpow_contDiff (r - 2))
        have hg : ContDiff ℝ ∞ (fun x : Euc d => (innerSL ℝ x : Euc d →L[ℝ] ℝ)) :=
          (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).contDiff
        have hsm := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := ∞) hf hg x (n := i)
          (by exact_mod_cast le_top)
        refine hsm.trans ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun l hl => ?_
        have hli : l ≤ i := by have := Finset.mem_range.1 hl; omega
        have hfl : ‖iteratedFDeriv ℝ l (fun x : Euc d => r * jbracket x ^ (r - 2)) x‖ ≤
            |r| * (C l * jbracket x ^ (r - 2 - l)) := by
          have e2 : iteratedFDeriv ℝ l (fun x : Euc d => r * jbracket x ^ (r - 2)) x =
              r • iteratedFDeriv ℝ l (fun x : Euc d => jbracket x ^ (r - 2)) x :=
            iteratedFDeriv_const_smul_apply (a := r)
              ((s85_jbpow_contDiff (r - 2)).of_le (by exact_mod_cast le_top)).contDiffAt
          rw [e2, norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hC l hli x) (abs_nonneg _)
        have hgl := s85_innerSL_iter (i - l) x
        have hjb : 0 < jbracket x := u2_jb_pos x
        calc (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun x : Euc d => r * jbracket x ^ (r - 2)) x‖ *
              ‖iteratedFDeriv ℝ (i - l) (fun x : Euc d => (innerSL ℝ x : Euc d →L[ℝ] ℝ)) x‖
            ≤ (i.choose l : ℝ) * (|r| * (C l * jbracket x ^ (r - 2 - l))) *
              jbracket x ^ ((1 : ℝ) - ((i - l : ℕ) : ℝ)) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hfl (by positivity)) hgl
                (norm_nonneg _) (by
                  have := hC0 l hli
                  positivity)
          _ = (i.choose l : ℝ) * (|r| * C l) * jbracket x ^ (r - ((i + 1 : ℕ) : ℝ)) := by
              have e3 : jbracket x ^ (r - 2 - (l : ℝ)) * jbracket x ^ ((1 : ℝ) - ((i - l : ℕ) : ℝ)) =
                  jbracket x ^ (r - ((i + 1 : ℕ) : ℝ)) := by
                rw [← Real.rpow_add hjb]
                congr 1
                have : ((i - l : ℕ) : ℝ) = (i : ℝ) - l := by
                  rw [Nat.cast_sub hli]
                push_cast
                rw [this]; ring
              calc _ = (i.choose l : ℝ) * (|r| * C l) *
                    (jbracket x ^ (r - 2 - (l : ℝ)) * jbracket x ^ ((1 : ℝ) - ((i - l : ℕ) : ℝ))) := by
                    ring
                _ = _ := by rw [e3]

end HRS.MS.S85
