import HRS.MS.R26T8AP11f10

/-!
# S8.2 T8A P11f (part 11): joint jets of a conormal pair function away from the diagonal
`r26t8a_f11_joint_far`: `Conormal K b M σ A F`, `j ≤ K`, `|u-y| ≥ 1/4` give `‖D^j (uncurry F) (u,y)‖ ≤ CJ A jb(u)^M jb(y)^M`
with `CJ` independent of `A`, `F`, `u`, `y`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f11_joint_far {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (K b : ℕ) (M σ : ℝ) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ (A : ℝ), 0 ≤ A → ∀ {F : Euc d → Euc d → ℝ}, Conormal K b M σ A F →
      ∀ j ≤ K, ∀ u y : Euc d, 1 / 4 ≤ ‖u - y‖ →
        ‖iteratedFDeriv ℝ j (Function.uncurry F) (u, y)‖ ≤ CJ * A * HRS.MS.Phase2S82.pairWeight M u y := by
  have hq : ∀ q ∈ Finset.range (K + 1), ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 / 4 ≤ r →
      1 + (min 1 r) ^ (-(σ + q)) * (1 + |Real.log (min 1 r)|) ^ b ≤ C := fun q _ =>
    r26t8a_f10_env_bdd b (σ + q)
  choose! C hC0 hC using hq
  set CE : ℝ := ∑ q ∈ Finset.range (K + 1), C q with hCE
  have hCE0 : 0 ≤ CE := Finset.sum_nonneg fun q hq => hC0 q hq
  have hCEq : ∀ q ∈ Finset.range (K + 1), C q ≤ CE := fun q hq =>
    Finset.single_le_sum (f := C) (fun q hq => hC0 q hq) hq
  refine ⟨4 ^ K * CE, by positivity, ?_⟩
  intro A hA F hF j hj u y huy
  have hu : u ≠ y := by
    intro h; rw [h, sub_self, norm_zero] at huy; linarith
  refine (r26t8a_p11f_joint_jet hchi hA hF hj hu).trans ?_
  have hpw0 : 0 ≤ HRS.MS.Phase2S82.pairWeight M u y := by
    unfold HRS.MS.Phase2S82.pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hApw : 0 ≤ A * HRS.MS.Phase2S82.pairWeight M u y := mul_nonneg hA hpw0
  have hterm : ∀ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * (A * HRS.MS.Phase2S82.pairWeight M u y *
      (1 + (min 1 ‖u - y‖) ^ (-(σ + q)) * (1 + |Real.log (min 1 ‖u - y‖)|) ^ b)) ≤
      (j.choose q : ℝ) * (A * HRS.MS.Phase2S82.pairWeight M u y * CE) := by
    intro q hq
    have hq' : q ∈ Finset.range (K + 1) := by
      rw [Finset.mem_range] at hq ⊢; omega
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hApw) (Nat.cast_nonneg _)
    exact (hC q hq' ‖u - y‖ huy).trans (hCEq q hq')
  have hsum : ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * (A * HRS.MS.Phase2S82.pairWeight M u y * CE) =
      2 ^ j * (A * HRS.MS.Phase2S82.pairWeight M u y * CE) := by
    rw [← Finset.sum_mul]
    have : ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) = 2 ^ j := by exact_mod_cast Nat.sum_range_choose j
    rw [this]
  have h2j : (2 : ℝ) ^ j ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hj
  calc (2 : ℝ) ^ j * ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * (A * HRS.MS.Phase2S82.pairWeight M u y *
        (1 + (min 1 ‖u - y‖) ^ (-(σ + q)) * (1 + |Real.log (min 1 ‖u - y‖)|) ^ b))
      ≤ 2 ^ j * (2 ^ j * (A * HRS.MS.Phase2S82.pairWeight M u y * CE)) := by
        refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum hterm).trans (le_of_eq hsum)) (by positivity)
    _ ≤ 2 ^ K * (2 ^ K * (A * HRS.MS.Phase2S82.pairWeight M u y * CE)) := by
        have hx : 0 ≤ A * HRS.MS.Phase2S82.pairWeight M u y * CE := mul_nonneg hApw hCE0
        exact mul_le_mul h2j (mul_le_mul_of_nonneg_right h2j hx) (by positivity) (by positivity)
    _ = 4 ^ K * CE * A * HRS.MS.Phase2S82.pairWeight M u y := by
        have : (4 : ℝ) ^ K = 2 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
        rw [this]; ring

end HRS.MS.R26T8A
