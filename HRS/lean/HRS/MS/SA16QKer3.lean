import HRS.MS.SA16QKer2

/-!
# S.A.16 (SA16Q), E6 part 3: bounds and limits of the smoothed kernels

For `0 < ε ≤ 1` and `y ≠ 0`:
`|K1E| ≤ γ |y|^{-(s+1)}`, `|K2E| ≤ γ (s+3) |y|^{-(s+2)}`, `|gE| ≤ |g| + (1 + |y|)`,
and the three families converge (as `ε = 1/(n+1) → 0`) to the `ε = 0` kernels.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA

section KernBounds
variable {d : ℕ}

def sa16q_eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma sa16q_eps_pos (n : ℕ) : 0 < sa16q_eps n := by unfold sa16q_eps; positivity

lemma sa16q_eps_le_one (n : ℕ) : sa16q_eps n ≤ 1 := by
  unfold sa16q_eps
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma sa16q_eps_tendsto : Tendsto sa16q_eps atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma sa16q_coord_le (y : Euc d) (i : Fin d) : |y i| ≤ ‖y‖ := by
  have := PiLp.norm_apply_le y i
  simpa [Real.norm_eq_abs] using this

lemma sa16q_rpow_sq {y : Euc d} (hy : y ≠ 0) (c : ℝ) :
    (‖y‖ ^ 2) ^ c = ‖y‖ ^ (2 * c) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg y)]
  norm_num

lemma sa16q_t_le {y : Euc d} (hy : y ≠ 0) {ε : ℝ} (c : ℝ) (hc : c ≤ 0) :
    (‖y‖ ^ 2 + ε ^ 2) ^ c ≤ ‖y‖ ^ (2 * c) := by
  have hpos : 0 < ‖y‖ ^ 2 := by positivity
  rw [← sa16q_rpow_sq hy]
  exact Real.rpow_le_rpow_of_nonpos hpos (by nlinarith [sq_nonneg ε]) hc

lemma sa16q_K1E_bound {s : ℝ} (hs : 0 ≤ s) (ε : ℝ) (i : Fin d) {y : Euc d} (hy : y ≠ 0) :
    |sa16q_K1E s ε i y| ≤ sa16q_gam s * ‖y‖ ^ (-(s + 1)) := by
  have hg := sa16q_gam_pos hs
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  unfold sa16q_K1E
  have h1 : (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1) ≤ ‖y‖ ^ (2 * (-(s / 2) - 1)) :=
    sa16q_t_le hy _ (by linarith)
  have h2 : 0 ≤ (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1) := Real.rpow_nonneg (by positivity) _
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos hg, abs_of_nonneg h2]
  calc sa16q_gam s * |y i| * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1)
      ≤ sa16q_gam s * ‖y‖ * ‖y‖ ^ (2 * (-(s / 2) - 1)) := by
        gcongr
        exact sa16q_coord_le y i
    _ = sa16q_gam s * ‖y‖ ^ (-(s + 1)) := by
        have hh : 1 + 2 * (-(s / 2) - 1) ≠ 0 := by intro h; linarith
        rw [mul_assoc, ← Real.rpow_one_add' hy0.le hh]
        congr 2; ring

lemma sa16q_K2E_bound {s : ℝ} (hs : 0 ≤ s) (ε : ℝ) (i j : Fin d) {y : Euc d} (hy : y ≠ 0) :
    |sa16q_K2E s ε i j y| ≤ sa16q_gam s * (s + 3) * ‖y‖ ^ (-(s + 2)) := by
  have hg := sa16q_gam_pos hs
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  unfold sa16q_K2E
  have h1 : (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1) ≤ ‖y‖ ^ (2 * (-(s / 2) - 1)) :=
    sa16q_t_le hy _ (by linarith)
  have h1' : (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 2) ≤ ‖y‖ ^ (2 * (-(s / 2) - 2)) :=
    sa16q_t_le hy _ (by linarith)
  have h2 : 0 ≤ (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1) := Real.rpow_nonneg (by positivity) _
  have h2' : 0 ≤ (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 2) := Real.rpow_nonneg (by positivity) _
  have e1 : ‖y‖ ^ (2 * (-(s / 2) - 1)) = ‖y‖ ^ (-(s + 2)) := by congr 1; ring
  have e2 : ‖y‖ ^ 2 * ‖y‖ ^ (2 * (-(s / 2) - 2)) = ‖y‖ ^ (-(s + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy0]; congr 1; push_cast; ring
  have hA : |-(sa16q_gam s) * (if i = j then (1 : ℝ) else 0) * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1)| ≤
      sa16q_gam s * ‖y‖ ^ (-(s + 2)) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos hg, abs_of_nonneg h2]
    have : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    calc sa16q_gam s * |(if i = j then (1 : ℝ) else 0)| * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1)
        ≤ sa16q_gam s * 1 * ‖y‖ ^ (2 * (-(s / 2) - 1)) := by gcongr
      _ = _ := by rw [e1]; ring
  have hB : |sa16q_gam s * (s + 2) * y i * y j * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 2)| ≤
      sa16q_gam s * (s + 2) * ‖y‖ ^ (-(s + 2)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hg, abs_of_pos (by linarith : 0 < s + 2),
      abs_of_nonneg h2']
    have hyi := sa16q_coord_le y i
    have hyj := sa16q_coord_le y j
    calc sa16q_gam s * (s + 2) * |y i| * |y j| * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 2)
        ≤ sa16q_gam s * (s + 2) * ‖y‖ * ‖y‖ * ‖y‖ ^ (2 * (-(s / 2) - 2)) := by gcongr
      _ = sa16q_gam s * (s + 2) * (‖y‖ ^ 2 * ‖y‖ ^ (2 * (-(s / 2) - 2))) := by ring
      _ = _ := by rw [e2]
  calc |-(sa16q_gam s) * (if i = j then (1 : ℝ) else 0) * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1) +
        sa16q_gam s * (s + 2) * y i * y j * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 2)|
      ≤ _ := abs_add_le _ _
    _ ≤ sa16q_gam s * ‖y‖ ^ (-(s + 2)) + sa16q_gam s * (s + 2) * ‖y‖ ^ (-(s + 2)) := add_le_add hA hB
    _ = _ := by ring

lemma sa16q_gE_bound {s : ℝ} (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {y : Euc d} (hy : y ≠ 0) :
    |sa16q_gE s ε y| ≤ |rieszKernel d s y| + (1 + ‖y‖) := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hpos : 0 < ‖y‖ ^ 2 := by positivity
  have hpos' : 0 < ‖y‖ ^ 2 + ε ^ 2 := by positivity
  have hlt : ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg ε]
  rw [sa16q_rk_eq]
  unfold sa16q_gE sa16q_Phi
  split_ifs with h0
  · -- logarithmic case
    have h1 : Real.log (‖y‖ ^ 2) ≤ Real.log (‖y‖ ^ 2 + ε ^ 2) := Real.log_le_log hpos hlt
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith
    have h2 : Real.log (‖y‖ ^ 2 + ε ^ 2) ≤ Real.log ((1 + ‖y‖) ^ 2) := by
      refine Real.log_le_log hpos' ?_
      nlinarith [sq_nonneg ε, norm_nonneg y]
    have h3 : Real.log ((1 + ‖y‖) ^ 2) = 2 * Real.log (1 + ‖y‖) := by
      rw [Real.log_pow]; norm_num
    have h4 : Real.log (1 + ‖y‖) ≤ ‖y‖ := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ‖y‖)
      linarith
    by_cases hsign : 0 ≤ -Real.log (‖y‖ ^ 2 + ε ^ 2) / 2
    · rw [abs_of_nonneg hsign]
      have : -Real.log (‖y‖ ^ 2 + ε ^ 2) / 2 ≤ |-Real.log (‖y‖ ^ 2) / 2| := by
        refine le_trans ?_ (le_abs_self _)
        linarith
      linarith [norm_nonneg y]
    · push Not at hsign
      rw [abs_of_neg hsign]
      have : Real.log (‖y‖ ^ 2 + ε ^ 2) / 2 ≤ ‖y‖ := by linarith
      have : 0 ≤ |-Real.log (‖y‖ ^ 2) / 2| := abs_nonneg _
      linarith
  · have h1 : (‖y‖ ^ 2 + ε ^ 2) ^ (-s / 2) ≤ (‖y‖ ^ 2) ^ (-s / 2) := by
      have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
      exact Real.rpow_le_rpow_of_nonpos hpos hlt (by linarith)
    have h2 : 0 ≤ (‖y‖ ^ 2 + ε ^ 2) ^ (-s / 2) := Real.rpow_nonneg hpos'.le _
    have h3 : 0 ≤ (‖y‖ ^ 2) ^ (-s / 2) := Real.rpow_nonneg hpos.le _
    rw [abs_of_nonneg h2, abs_of_nonneg h3]
    linarith [norm_nonneg y]

lemma sa16q_gE_tendsto {s : ℝ} {y : Euc d} (hy : y ≠ 0) :
    Tendsto (fun n => sa16q_gE s (sa16q_eps n) y) atTop (𝓝 (rieszKernel d s y)) := by
  have hpos : 0 < ‖y‖ ^ 2 := by have := norm_pos_iff.2 hy; positivity
  have hc : ContinuousAt (fun ε : ℝ => sa16q_Phi s (‖y‖ ^ 2 + ε ^ 2)) 0 := by
    have h1 : ContinuousAt (fun ε : ℝ => ‖y‖ ^ 2 + ε ^ 2) 0 := by fun_prop
    have h2 : ContinuousAt (sa16q_Phi s) (‖y‖ ^ 2 + (0 : ℝ) ^ 2) := by
      refine sa16q_Phi_cont ?_
      simpa using hpos
    exact h2.comp (f := fun ε : ℝ => ‖y‖ ^ 2 + ε ^ 2) h1
  have := hc.tendsto.comp sa16q_eps_tendsto
  rw [sa16q_rk_eq]
  simpa [sa16q_gE, Function.comp_def] using this

lemma sa16q_K1E_tendsto {s : ℝ} (i : Fin d) {y : Euc d} (hy : y ≠ 0) :
    Tendsto (fun n => sa16q_K1E s (sa16q_eps n) i y) atTop (𝓝 (sa16q_K1E s 0 i y)) := by
  have hpos : 0 < ‖y‖ ^ 2 := by have := norm_pos_iff.2 hy; positivity
  have hc : ContinuousAt (fun ε : ℝ => sa16q_K1E s ε i y) 0 := by
    unfold sa16q_K1E
    have h1 : ContinuousAt (fun ε : ℝ => (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1)) 0 := by
      have h0 : ContinuousAt (fun ε : ℝ => ‖y‖ ^ 2 + ε ^ 2) 0 := by fun_prop
      exact (Real.continuousAt_rpow_const _ _ (Or.inl (by simpa using hpos.ne'))).comp
        (f := fun ε : ℝ => ‖y‖ ^ 2 + ε ^ 2) h0
    exact continuousAt_const.mul h1
  exact hc.tendsto.comp sa16q_eps_tendsto

lemma sa16q_K2E_tendsto {s : ℝ} (i j : Fin d) {y : Euc d} (hy : y ≠ 0) :
    Tendsto (fun n => sa16q_K2E s (sa16q_eps n) i j y) atTop (𝓝 (sa16q_K2E s 0 i j y)) := by
  have hpos : 0 < ‖y‖ ^ 2 := by have := norm_pos_iff.2 hy; positivity
  have hc : ContinuousAt (fun ε : ℝ => sa16q_K2E s ε i j y) 0 := by
    unfold sa16q_K2E
    have h0 : ContinuousAt (fun ε : ℝ => ‖y‖ ^ 2 + ε ^ 2) 0 := by fun_prop
    have h1 : ContinuousAt (fun ε : ℝ => (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1)) 0 :=
      (Real.continuousAt_rpow_const _ _ (Or.inl (by simpa using hpos.ne'))).comp
        (f := fun ε : ℝ => ‖y‖ ^ 2 + ε ^ 2) h0
    have h2 : ContinuousAt (fun ε : ℝ => (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 2)) 0 :=
      (Real.continuousAt_rpow_const _ _ (Or.inl (by simpa using hpos.ne'))).comp
        (f := fun ε : ℝ => ‖y‖ ^ 2 + ε ^ 2) h0
    exact (continuousAt_const.mul h1).add (continuousAt_const.mul h2)
  exact hc.tendsto.comp sa16q_eps_tendsto

end KernBounds

end HRS.Whole.AppendixA.Phase2SA16Q
