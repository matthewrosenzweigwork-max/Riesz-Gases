import HRS.MS.R26T8AA00c

/-!
# S8.2 T8A A00: `r26t8a_corrector_gradient_difference` (Pro contract, verbatim)
Case split: if `‖x-z‖ ≥ max(‖x-y‖,‖z-y‖)/3` use the gradient field; otherwise the segment `[x,z]` stays at distance `≥ min(‖x-y‖,‖z-y‖)/2`
from `y` and the mean value theorem with the Hessian field (A00b) applies.  `M' = M`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 3200000 in
theorem r26t8a_corrector_gradient_difference (d : ℕ) (hd : 2 ≤ d)
    (a beta M : ℝ) (hM : 0 ≤ M) :
    ∃ C M' : ℝ, 0 ≤ C ∧ M ≤ M' ∧ ∀ rho f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      ∀ Q : Euc d → Euc d → ℝ, PairCorrector a beta rho M A f Q →
      ∀ x y z : Euc d, x ≠ y → z ≠ y →
        ‖pairGradX Q x y - pairGradX Q z y‖ ≤
          C * A * jbracket x ^ M' * jbracket y ^ M' * jbracket z ^ M' * ‖x - z‖ * (pole x y + pole z y) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : (1 : ℝ) ≤ criticalS d := by unfold criticalS; linarith
  set s : ℝ := criticalS d with hsdef
  set R0 : ℝ := ‖r26t8a_Rz d‖ with hR0
  have hR00 : 0 ≤ R0 := norm_nonneg (r26t8a_Rz d)
  have h2s : (1 : ℝ) ≤ 2 ^ s := Real.one_le_rpow (by norm_num) (by linarith)
  refine ⟨6 + 2 ^ s * R0, M, by positivity, le_rfl, ?_⟩
  intro rho f A hA Q hQ x y z hxy hzy
  set ℓ : ℝ := ‖x - z‖ with hℓ
  set p : ℝ := ‖x - y‖ with hp
  set q : ℝ := ‖z - y‖ with hq
  have hp0 : 0 < p := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hq0 : 0 < q := norm_pos_iff.2 (sub_ne_zero.2 hzy)
  have hℓ0 : 0 ≤ ℓ := norm_nonneg _
  have jx : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s83_one_le_jb x) hM
  have jy : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s83_one_le_jb y) hM
  have jz : 1 ≤ jbracket z ^ M := Real.one_le_rpow (s83_one_le_jb z) hM
  have hpX : pole x y = 1 + min 1 p ^ (-s) := rfl
  have hpZ : pole z y = 1 + min 1 q ^ (-s) := rfl
  have hpoleX : 0 ≤ pole x y := by
    rw [hpX]; have := Real.rpow_nonneg (le_min zero_le_one hp0.le) (-s); linarith
  have hpoleZ : 0 ≤ pole z y := by
    rw [hpZ]; have := Real.rpow_nonneg (le_min zero_le_one hq0.le) (-s); linarith
  have hRX : smallRadius x y = min 1 p := rfl
  have hRZ : smallRadius z y = min 1 q := rfl
  have hge : ∀ (u : Euc d), ‖pairGradX Q u y‖ ≤ ‖pairGradX Q u y‖ + ‖pairGradY Q u y‖ := fun u =>
    le_add_of_nonneg_right (norm_nonneg _)
  by_cases hA3 : p / 3 ≤ ℓ ∧ q / 3 ≤ ℓ
  · -- near field
    obtain ⟨hpl, hql⟩ := hA3
    have gx := (hge x).trans (hQ.gradient x y hxy)
    have gz := (hge z).trans (hQ.gradient z y hzy)
    rw [hRX] at gx
    rw [hRZ] at gz
    have nx := r26t8a_a00_near hs1 hp0 hpl
    have nz := r26t8a_a00_near hs1 hq0 hql
    have hpw : ∀ (u : Euc d), 0 ≤ HRS.MS.Phase2S82.pairWeight M u y := fun u =>
      mul_nonneg (Real.rpow_nonneg (s83_jb_pos u).le _) (Real.rpow_nonneg (s83_jb_pos y).le _)
    have hxb : ‖pairGradX Q x y‖ ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * (6 * ℓ * pole x y) := by
      refine gx.trans ?_
      rw [hpX]
      have h0 : 0 ≤ A * HRS.MS.Phase2S82.pairWeight M x y := mul_nonneg hA (hpw x)
      calc A * HRS.MS.Phase2S82.pairWeight M x y * (1 + min 1 p ^ (1 - s))
          ≤ A * HRS.MS.Phase2S82.pairWeight M x y * (6 * ℓ * (1 + min 1 p ^ (-s))) :=
            mul_le_mul_of_nonneg_left nx h0
        _ ≤ _ := by
            have hw : HRS.MS.Phase2S82.pairWeight M x y ≤ jbracket x ^ M * jbracket y ^ M * jbracket z ^ M := by
              unfold HRS.MS.Phase2S82.pairWeight
              nlinarith [mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le M) (Real.rpow_nonneg (s83_jb_pos y).le M)]
            have hp1 : 0 ≤ 6 * ℓ * (1 + min 1 p ^ (-s)) := by
              have := Real.rpow_nonneg (le_min zero_le_one hp0.le) (-s); positivity
            calc A * HRS.MS.Phase2S82.pairWeight M x y * (6 * ℓ * (1 + min 1 p ^ (-s)))
                ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * (6 * ℓ * (1 + min 1 p ^ (-s))) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hA) hp1
              _ = _ := by ring
    have hzb : ‖pairGradX Q z y‖ ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * (6 * ℓ * pole z y) := by
      refine gz.trans ?_
      rw [hpZ]
      have h0 : 0 ≤ A * HRS.MS.Phase2S82.pairWeight M z y := mul_nonneg hA (hpw z)
      calc A * HRS.MS.Phase2S82.pairWeight M z y * (1 + min 1 q ^ (1 - s))
          ≤ A * HRS.MS.Phase2S82.pairWeight M z y * (6 * ℓ * (1 + min 1 q ^ (-s))) :=
            mul_le_mul_of_nonneg_left nz h0
        _ ≤ _ := by
            have hw : HRS.MS.Phase2S82.pairWeight M z y ≤ jbracket x ^ M * jbracket y ^ M * jbracket z ^ M := by
              unfold HRS.MS.Phase2S82.pairWeight
              nlinarith [mul_nonneg (Real.rpow_nonneg (s83_jb_pos z).le M) (Real.rpow_nonneg (s83_jb_pos y).le M)]
            have hp1 : 0 ≤ 6 * ℓ * (1 + min 1 q ^ (-s)) := by
              have := Real.rpow_nonneg (le_min zero_le_one hq0.le) (-s); positivity
            calc A * HRS.MS.Phase2S82.pairWeight M z y * (6 * ℓ * (1 + min 1 q ^ (-s)))
                ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * (6 * ℓ * (1 + min 1 q ^ (-s))) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hA) hp1
              _ = _ := by ring
    have hJ : 0 ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) := by
      have := Real.rpow_nonneg (s83_jb_pos x).le M
      have := Real.rpow_nonneg (s83_jb_pos y).le M
      have := Real.rpow_nonneg (s83_jb_pos z).le M
      positivity
    calc ‖pairGradX Q x y - pairGradX Q z y‖ ≤ ‖pairGradX Q x y‖ + ‖pairGradX Q z y‖ := norm_sub_le _ _
      _ ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * (6 * ℓ * pole x y) +
          A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * (6 * ℓ * pole z y) := add_le_add hxb hzb
      _ = 6 * (A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * ℓ * (pole x y + pole z y)) := by ring
      _ ≤ (6 + 2 ^ s * R0) * (A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * ℓ * (pole x y + pole z y)) := by
          have : 0 ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * ℓ * (pole x y + pole z y) := by positivity
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 ^ s) hR00]
      _ = _ := by ring
  · -- far field: mean value theorem along the segment
    have hB : ℓ < p / 2 ∧ ℓ < q / 2 := by
      have t1 : p ≤ q + ℓ := by
        have h := norm_sub_le_norm_sub_add_norm_sub x z y
        show ‖x - y‖ ≤ ‖z - y‖ + ‖x - z‖
        linarith
      have t2 : q ≤ p + ℓ := by
        have h := norm_sub_le_norm_sub_add_norm_sub z x y
        rw [norm_sub_rev z x] at h
        show ‖z - y‖ ≤ ‖x - y‖ + ‖x - z‖
        linarith
      rcases not_and_or.1 hA3 with h | h
      · have : ℓ < p / 3 := not_le.1 h
        constructor <;> linarith
      · have : ℓ < q / 3 := not_le.1 h
        constructor <;> linarith
    obtain ⟨hlp, hlq⟩ := hB
    have hseg : ∀ w ∈ segment ℝ x z, p / 2 ≤ ‖w - y‖ := by
      intro w hw
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
      have e : α • x + β • z - x = β • (z - x) := by
        have : α = 1 - β := by linarith
        subst this; module
      have h1 : ‖α • x + β • z - x‖ ≤ ℓ := by
        rw [e, norm_smul, Real.norm_of_nonneg hβ, hℓ, norm_sub_rev z x]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
      have h2 : p ≤ ‖α • x + β • z - y‖ + ‖α • x + β • z - x‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub x (α • x + β • z) y
        rw [norm_sub_rev x (α • x + β • z)] at this
        have e2 : p = ‖x - y‖ := rfl
        linarith
      linarith
    have hne : ∀ w ∈ segment ℝ x z, w ≠ y := by
      intro w hw hwy
      have := hseg w hw
      rw [hwy, sub_self, norm_zero] at this
      linarith
    set Cb : ℝ := R0 * A * (jbracket x ^ M * jbracket z ^ M * jbracket y ^ M) * (2 ^ s * pole x y) with hCb
    have hbound : ∀ w ∈ segment ℝ x z, ‖fderiv ℝ (fun w' => pairGradX Q w' y) w‖ ≤ Cb := by
      intro w hw
      have hdw := (r26t8a_a00_grad_deriv hQ (hne w hw)).2
      refine hdw.trans ?_
      have hjw : jbracket w ^ M ≤ jbracket x ^ M * jbracket z ^ M := by
        calc jbracket w ^ M ≤ (jbracket x * jbracket z) ^ M :=
              Real.rpow_le_rpow (s83_jb_pos w).le (r26t8a_a00_jb_seg hw) hM
          _ = _ := Real.mul_rpow (s83_jb_pos x).le (s83_jb_pos z).le
      have hrw : (1 + smallRadius w y ^ (-criticalS d)) ≤ 2 ^ s * pole x y := by
        have hl : min 1 p / 2 ≤ smallRadius w y := by
          unfold smallRadius
          refine le_min ?_ ?_
          · have := min_le_left 1 p; linarith
          · have := min_le_right 1 p; have := hseg w hw; linarith
        have hpos : 0 < min 1 p / 2 := by have := lt_min zero_lt_one hp0; linarith
        have h1 : smallRadius w y ^ (-s) ≤ (min 1 p / 2) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos hpos hl (by linarith)
        have h2 : (min 1 p / 2) ^ (-s) = 2 ^ s * min 1 p ^ (-s) := by
          rw [Real.div_rpow (by have := lt_min zero_lt_one hp0; linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
            Real.rpow_neg (le_min zero_le_one hp0.le)]
          field_simp
        rw [hpX]
        have hn : 0 ≤ min 1 p ^ (-s) := Real.rpow_nonneg (le_min zero_le_one hp0.le) _
        show 1 + smallRadius w y ^ (-s) ≤ _
        nlinarith [h1, h2, h2s]
      have hpw : HRS.MS.Phase2S82.pairWeight M w y ≤ jbracket x ^ M * jbracket z ^ M * jbracket y ^ M := by
        unfold HRS.MS.Phase2S82.pairWeight
        calc jbracket w ^ M * jbracket y ^ M ≤ (jbracket x ^ M * jbracket z ^ M) * jbracket y ^ M :=
              mul_le_mul_of_nonneg_right hjw (Real.rpow_nonneg (s83_jb_pos y).le _)
          _ = _ := rfl
      have hpw0 : 0 ≤ HRS.MS.Phase2S82.pairWeight M w y :=
        mul_nonneg (Real.rpow_nonneg (s83_jb_pos w).le _) (Real.rpow_nonneg (s83_jb_pos y).le _)
      have h1w : 0 ≤ 1 + smallRadius w y ^ (-criticalS d) := by
        have := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg (w - y))) (-criticalS d); unfold smallRadius; linarith
      rw [hCb]
      calc R0 * (A * HRS.MS.Phase2S82.pairWeight M w y * (1 + smallRadius w y ^ (-criticalS d)))
          ≤ R0 * (A * (jbracket x ^ M * jbracket z ^ M * jbracket y ^ M) * (2 ^ s * pole x y)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hpw hA) hrw h1w
              (mul_nonneg hA (by
                have := Real.rpow_nonneg (s83_jb_pos x).le M
                have := Real.rpow_nonneg (s83_jb_pos y).le M
                have := Real.rpow_nonneg (s83_jb_pos z).le M
                positivity))) hR00
        _ = _ := by ring
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fun w' => pairGradX Q w' y) (fun w hw => (r26t8a_a00_grad_deriv hQ (hne w hw)).1) hbound
      (convex_segment x z) (left_mem_segment ℝ x z) (right_mem_segment ℝ x z)
    rw [norm_sub_rev] at hmvt
    have hz' : ‖z - x‖ = ℓ := by rw [hℓ, norm_sub_rev]
    rw [hz'] at hmvt
    refine hmvt.trans ?_
    have hJ : 0 ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) := by
      have := Real.rpow_nonneg (s83_jb_pos x).le M
      have := Real.rpow_nonneg (s83_jb_pos y).le M
      have := Real.rpow_nonneg (s83_jb_pos z).le M
      positivity
    have hX : 0 ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * ℓ := mul_nonneg hJ hℓ0
    calc Cb * ℓ = (2 ^ s * R0) * (A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * ℓ * pole x y) := by
          rw [hCb]; ring
      _ ≤ (6 + 2 ^ s * R0) * (A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * ℓ * (pole x y + pole z y)) := by
          have h1 : 0 ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * ℓ * pole x y := mul_nonneg hX hpoleX
          have h2 : 0 ≤ A * (jbracket x ^ M * jbracket y ^ M * jbracket z ^ M) * ℓ * pole z y := mul_nonneg hX hpoleZ
          have hc : 0 ≤ 2 ^ s * R0 := mul_nonneg (by linarith) hR00
          nlinarith [mul_nonneg hc h2, mul_nonneg (by norm_num : (0:ℝ) ≤ 6) h1, mul_nonneg (by norm_num : (0:ℝ) ≤ 6) h2]
      _ = _ := by ring

end HRS.MS.R26T8A
