import HRS.MS.FixEqP3Aux2

/-!
# S5.7 `fixed_equation` (worker S57P), part 15: Hermite expansion of oscillator test functions through the propagator

For `φ ∈ Σ^m` (`IsOscTest m φ`, `m > J + d`) put `b_α = λ_α^{m/2} ⟨φ,h_α⟩`, so that `φ = ∑_α b_α φ_α` with `φ_α = oscTestFun m α`.
`s57p_hermite_series`: the series converges in `C^R_b`, with the tail estimate `∑_{α ∉ F} |b_α| C_j λ_α^{(J-m)/2}` for the
`n`-th derivative of `φ - ∑_{α ∈ F} b_α φ_α`.
`s57p_prop_partial`: `U^{r,t}` of a finite combination of the features is the combination of the `U^{r,t} φ_α`.
`s57p_prop_expand`: `U^{r,t}φ - ∑_{α ∈ F} b_α U^{r,t}φ_α → 0` in `C^i_b`, uniformly in `r ≤ t ≤ T`, as `F ↑`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem s57p_osc_jets {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (hd : 1 ≤ d) (m : ℝ) (J R : ℕ) (hJ : 3 * R + 9 ≤ J) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ n ≤ R, ∀ x,
      ‖iteratedFDeriv ℝ n (oscTestFun m α) x‖ ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
  have hceil : ⌈(1 + (R : ℝ)) / 2⌉₊ ≤ R + 1 := by
    rw [Nat.ceil_le]; push_cast
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  obtain ⟨C0, hC0, hosc⟩ := s55_osc_bounds hθ m 0 R 1 (by norm_num) J (by omega) (by omega)
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨(d : ℝ) ^ R * C0, by positivity, fun α => ?_⟩
  obtain ⟨hsm, -, hdec⟩ := hosc α
  have hφR : ContDiff ℝ ((R : ℕ) : WithTop ℕ∞) (oscTestFun m α) := s55_cd_of_inf R hsm
  have hΛ0 : 0 ≤ C0 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    mul_nonneg hC0 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  have hnorm := s55f_decay_to_norm hφR hdec
  rw [max_eq_left hΛ0] at hnorm
  refine ⟨hsm, fun n hn x => ?_⟩
  calc ‖iteratedFDeriv ℝ n (oscTestFun m α) x‖ ≤ (d : ℝ) ^ n * (C0 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) :=
        (hnorm n hn x).1
    _ ≤ (d : ℝ) ^ R * (C0 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1' hn) hΛ0
    _ = ((d : ℝ) ^ R * C0) * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by ring

/-- the coefficients `b_α = λ_α^{m/2} ⟨φ,h_α⟩` -/
def s57pb (d : ℕ) (m : ℝ) (φ : Euc d → ℝ) (α : MultiIndex d) : ℝ :=
  oscEigenvalue d α ^ (m / 2) * Whole.hermiteCoeff φ α

/-- the partial sum `∑_{α ∈ F} b_α φ_α` -/
def s57pP (d : ℕ) (m : ℝ) (φ : Euc d → ℝ) (F : Finset (MultiIndex d)) (y : Euc d) : ℝ :=
  ∑ α ∈ F, s57pb d m φ α * oscTestFun m α y

theorem s57p_hermite_series (hd : 1 ≤ d) {m : ℝ} {J R : ℕ} (hm : (J : ℝ) + d < m) {Cj : ℝ} (hCj : 0 ≤ Cj)
    (hj : ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ n ≤ R, ∀ x,
      ‖iteratedFDeriv ℝ n (oscTestFun m α) x‖ ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    {φ : Euc d → ℝ} (hφ : IsOscTest m φ) :
    Summable (fun α : MultiIndex d => |s57pb d m φ α| * (Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))) ∧
    (∀ x, φ x = ∑' α, s57pb d m φ α * oscTestFun m α x) ∧
    ∀ F : Finset (MultiIndex d), ∀ n ≤ R, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => φ y - s57pP d m φ F y) x‖ ≤
        ∑' α, (if α ∈ F then 0 else |s57pb d m φ α| * (Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))) := by
  set e : ℝ := ((J : ℝ) - m) / 2 with he
  set g : MultiIndex d → ℝ := fun α => Cj * oscEigenvalue d α ^ e with hg
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdm : (d : ℝ) < m := by linarith
  have hsumJ : Summable fun α : MultiIndex d => oscEigenvalue d α ^ ((J : ℝ) - m) := by
    have h := (summable_oscEigenvalue_rpow_iff (d := d) (by omega) (m - J)).2 (by linarith)
    simpa [neg_sub] using h
  have hg2 : Summable fun α : MultiIndex d => (g α) ^ 2 := by
    have : ∀ α : MultiIndex d, (g α) ^ 2 = Cj ^ 2 * oscEigenvalue d α ^ ((J : ℝ) - m) := by
      intro α
      rw [hg]
      simp only
      rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
    simp_rw [this]
    exact hsumJ.mul_left _
  have hb2 : ∀ α, (s57pb d m φ α) ^ 2 = oscEigenvalue d α ^ m * Whole.hermiteCoeff φ α ^ 2 := by
    intro α
    unfold s57pb
    rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
  have hsum : Summable fun α : MultiIndex d => |s57pb d m φ α| * g α := by
    refine Summable.of_nonneg_of_le (fun α => mul_nonneg (abs_nonneg _) (mul_nonneg hCj
      (Real.rpow_nonneg (oscEv_pos α).le _))) (fun α => ?_) ((hφ.2.2.add hg2).div_const 2)
    have h1 := two_mul_le_add_sq |s57pb d m φ α| (g α)
    rw [sq_abs, hb2] at h1
    linarith
  have hexp : ∀ x, φ x = ∑' α, s57pb d m φ α * oscTestFun m α x := by
    intro x
    rw [OscDual.hermite_expansion_of_summable hφ.1.continuous hφ.2.1 (OscDual.summable_abs_hermiteCoeff hdm hφ.2) x]
    refine tsum_congr fun α => ?_
    unfold s57pb oscTestFun
    have h := rpow_neg_half_mul m (oscEigenvalue d α) (oscEv_pos α)
    calc Whole.hermiteCoeff φ α * hermiteFunD α x
        = (oscEigenvalue d α ^ (-(m / 2)) * oscEigenvalue d α ^ (m / 2)) *
            (Whole.hermiteCoeff φ α * hermiteFunD α x) := by rw [h, one_mul]
      _ = _ := by ring
  refine ⟨hsum, hexp, fun F n hn x => ?_⟩
  -- the tail series
  set u : MultiIndex d → Euc d → ℝ := fun α y => if α ∈ F then 0 else s57pb d m φ α * oscTestFun m α y with hu
  set v : ℕ → MultiIndex d → ℝ := fun _ α => if α ∈ F then 0 else |s57pb d m φ α| * g α with hv
  have hud : ∀ α, ContDiff ℝ (R : ℕ∞) (u α) := by
    intro α
    by_cases hα : α ∈ F
    · simp only [hu, hα, if_true]; exact contDiff_const
    · simp only [hu, hα, if_false]
      exact contDiff_const.mul ((hj α).1.of_le (by exact_mod_cast le_top))
  have hvs : ∀ k : ℕ, (k : ℕ∞) ≤ (R : ℕ∞) → Summable (v k) := by
    intro k _
    have : v k = fun α => if α ∈ F then 0 else |s57pb d m φ α| * g α := rfl
    rw [this]
    exact Summable.of_nonneg_of_le (fun α => by
      by_cases hα : α ∈ F
      · simp [hα]
      · simp only [hα, if_false]
        exact mul_nonneg (abs_nonneg _) (mul_nonneg hCj (Real.rpow_nonneg (oscEv_pos α).le _)))
      (fun α => by
        by_cases hα : α ∈ F
        · simp only [hα, if_true]
          exact mul_nonneg (abs_nonneg _) (mul_nonneg hCj (Real.rpow_nonneg (oscEv_pos α).le _))
        · simp only [hα, if_false, le_refl]) hsum
  have hbd : ∀ (k : ℕ) (α : MultiIndex d) (y : Euc d), (k : ℕ∞) ≤ (R : ℕ∞) →
      ‖iteratedFDeriv ℝ k (u α) y‖ ≤ v k α := by
    intro k α y hk
    have hk' : k ≤ R := by exact_mod_cast hk
    by_cases hα : α ∈ F
    · have : u α = fun _ => (0 : ℝ) := by funext z; simp [hu, hα]
      rw [this]
      simp only [hv, hα, if_true]
      rcases k with _ | k
      · simp
      · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
    · have : u α = fun z => s57pb d m φ α * oscTestFun m α z := by funext z; simp [hu, hα]
      rw [this]
      simp only [hv, hα, if_false]
      have hc : ContDiff ℝ k (oscTestFun m α) := (hj α).1.of_le (by exact_mod_cast le_top)
      have h1 := s57p_norm_const_mul hc (s57pb d m φ α) y
      exact h1.trans (mul_le_mul_of_nonneg_left ((hj α).2 k hk' y) (abs_nonneg _))
  have hsumf : ∀ y, Summable fun α => s57pb d m φ α * oscTestFun m α y := by
    intro y
    refine Summable.of_norm_bounded hsum fun α => ?_
    have hc0 : ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞) (oscTestFun m α) := (hj α).1.of_le (by exact_mod_cast le_top)
    have := s57p_norm_const_mul hc0 (s57pb d m φ α) y
    rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left (by
      have := (hj α).2 0 (Nat.zero_le _) y
      rwa [norm_iteratedFDeriv_zero] at this) (abs_nonneg _))
  have hfun : (fun y => φ y - s57pP d m φ F y) = fun y => ∑' α, u α y := by
    funext y
    have h1 : ∑' α, u α y = ∑' α, s57pb d m φ α * oscTestFun m α y -
        ∑' α, (if α ∈ F then s57pb d m φ α * oscTestFun m α y else 0) := by
      rw [← (hsumf y).tsum_sub (summable_of_ne_finset_zero (s := F) (fun α hα => by simp [hα]))]
      refine tsum_congr fun α => ?_
      by_cases hα : α ∈ F <;> simp [hu, hα]
    rw [h1, ← hexp y, tsum_eq_sum (s := F) (fun α hα => by simp [hα])]
    simp only [s57pP]
    congr 1
    exact (Finset.sum_congr rfl fun α hα => by simp [hα]).symm
  rw [hfun, iteratedFDeriv_tsum_apply hud hvs hbd (by exact_mod_cast hn) x]
  exact tsum_of_norm_bounded ((hvs 0 (by simp)).hasSum) (fun α => hbd n α x (by exact_mod_cast hn))

end HRS.MS.FixEq
