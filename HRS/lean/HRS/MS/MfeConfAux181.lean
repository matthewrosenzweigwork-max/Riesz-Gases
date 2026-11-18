import HRS.MS.MfeConfAux180

/-!
# S.B.1 (SB5), R1b (part 2): uniform bound of `v_r(0)` and the one-body remainder bound

`sb1_V0`: `‖v_r(0)‖ ≤ V0` uniformly in `r ∈ [0,T]` (via the fixed kernel `k_0`).
`sb1_Bone_bound`: `|Bone| ≤ ε (1+K_r) A` from the smallness `E0`, `E1` of the force defect.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)

include H hT

theorem sb1_V0 : ∃ V0 : ℝ, 0 ≤ V0 ∧ ∀ r ∈ Set.Icc (0 : ℝ) T, ‖Whole.mfeTransportW D (ρ r) 0‖ ≤ V0 := by
  have hs0 := H.tr.hs0
  have hk4 := sb1kM_isKernel (d := d) D.s hs0 0
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 hs0
  have hUc : Continuous fun s => ‖sb1_lv_U D (sb1kM d D.s 0) hT ρ s 0‖ :=
    ((sb1_lv_U_cont H hT hk4).comp (Continuous.prodMk_left (0 : Euc d))).norm
  obtain ⟨Umax, hUm0, hUm⟩ := sb1_lv_bdd_of_cont hT hUc (fun s => by
    simp only [sb1_lv_U, sb1_lv_rb_cl])
  have hBF : 0 ≤ sb1BF d D.s C := sb1BF_nonneg hs0 H.tr.hC
  have hLg : 0 ≤ Lg := (norm_nonneg _).trans (hRg.gbd 0)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨Umax + d * (Lg + sb1BF d D.s C), by positivity, fun r hr => ?_⟩
  have h1 := sb1_lv_e_norm H hT hk4 hRg r 0
  have h2 := norm_sub_le (sb1_lv_U D (sb1kM d D.s 0) hT ρ r 0)
    (sb1_lv_U D (sb1kM d D.s 0) hT ρ r 0 - Whole.mfeTransportW D (sb1_lv_rb hT ρ r) 0)
  have h3 := hUm r
  rw [sub_sub_cancel] at h2
  rw [abs_of_nonneg (norm_nonneg _)] at h3
  rw [sb1_lv_rb_mem hT ρ hr] at h1 h2
  linarith

theorem sb1_Bone_bound {r₀ : ℝ} {k : Euc d → ℝ} (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) {V0 : ℝ}
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (hV0 : ‖Whole.mfeTransportW D (ρ r) 0‖ ≤ V0) {Kr ε ε1 : ℝ}
    (hK : 0 ≤ Kr) (hL : ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ ε1)
    (E0 : ∀ x, ‖sb1_lv_e D k hT ρ r x‖ ≤ ε * sb1w ((d : ℝ) + 3) x)
    (E1 : ∀ x, |∑ j, sb1_lv_cv (sb1_lv_hjj k j) (ρ r) x - ∑ j, fderiv ℝ (sb1F d D.s (ρ r) j) x (sb1e j)| ≤ ε)
    (x : Euc d) :
    |sb1_lv_Bone D k hT ρ r x| ≤ ε * (1 + Kr) *
      (1 + D.invβ⁻¹ * d * (V0 + ‖fderiv ℝ D.V 0‖ + ε1 + B + 1)) := by
  have hVB := H.tr.V
  rw [sb1_Bone_eq H hT hk4 hθ hr x]
  set c0 : ℝ := V0 + ‖fderiv ℝ D.V 0‖ + ε1 + B + 1 with hc0
  have hB0 : 0 ≤ B := hVB.B_nonneg
  have hV00 : 0 ≤ V0 := (norm_nonneg _).trans hV0
  have hG0 := norm_nonneg (fderiv ℝ D.V 0)
  have hε10 : 0 ≤ ε1 := hε0.trans hε1
  have hc01 : 1 ≤ c0 := by rw [hc0]; linarith
  have hθi : 0 ≤ D.invβ⁻¹ := (inv_pos.2 hθ).le
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set W : ℝ := sb1w ((d : ℝ) + 3) x with hW
  have hW0 : 0 < W := sb1w_pos _ _
  have hW1 : W ≤ 1 := sb1w_le_one (by positivity) _
  have hWx : W * ‖x‖ ≤ 1 := by
    have := sb1w_succ ((d : ℝ) + 2) x
    have e : (d : ℝ) + 2 + 1 = (d : ℝ) + 3 := by ring
    rw [e] at this
    have h2 : sb1w ((d : ℝ) + 2) x ≤ 1 := sb1w_le_one (by positivity) _
    nlinarith [norm_nonneg x]
  have hvn : ‖Whole.mfeTransportW D (ρ r) x‖ ≤ V0 + Kr * ‖x‖ := by
    have h1 := norm_le_insert' (Whole.mfeTransportW D (ρ r) x) (Whole.mfeTransportW D (ρ r) 0)
    have h2 := hL x 0
    rw [sub_zero] at h2
    linarith
  have hterm : ∀ j, |sb1_lv_e D k hT ρ r x j * (sb1_lv_U D k hT ρ r x j - fderiv ℝ D.V x (sb1e j))| ≤
      ε * (1 + Kr) * c0 := by
    intro j
    have hej : |sb1_lv_e D k hT ρ r x j| ≤ ε * W := by
      have := PiLp.norm_apply_le (sb1_lv_e D k hT ρ r x) j
      rw [Real.norm_eq_abs] at this
      exact this.trans (E0 x)
    have hUj : sb1_lv_U D k hT ρ r x j = Whole.mfeTransportW D (ρ r) x j + sb1_lv_e D k hT ρ r x j := by
      unfold sb1_lv_e; rw [sb1_lv_rb_mem hT ρ hr]; simp
    have hvj : |Whole.mfeTransportW D (ρ r) x j| ≤ V0 + Kr * ‖x‖ := by
      have := PiLp.norm_apply_le (Whole.mfeTransportW D (ρ r) x) j
      rw [Real.norm_eq_abs] at this
      exact this.trans hvn
    have hdV := sb1_lv_dV_bound hVB j x
    have hb : |sb1_lv_U D k hT ρ r x j - fderiv ℝ D.V x (sb1e j)| ≤
        V0 + Kr * ‖x‖ + ε * W + (‖fderiv ℝ D.V 0‖ + B * ‖x‖) := by
      rw [hUj]
      calc |Whole.mfeTransportW D (ρ r) x j + sb1_lv_e D k hT ρ r x j - fderiv ℝ D.V x (sb1e j)|
          ≤ |Whole.mfeTransportW D (ρ r) x j| + |sb1_lv_e D k hT ρ r x j| + |fderiv ℝ D.V x (sb1e j)| := by
            have h1 := abs_sub (Whole.mfeTransportW D (ρ r) x j + sb1_lv_e D k hT ρ r x j) (fderiv ℝ D.V x (sb1e j))
            have h2 := abs_add_le (Whole.mfeTransportW D (ρ r) x j) (sb1_lv_e D k hT ρ r x j)
            linarith
        _ ≤ _ := by linarith
    rw [abs_mul]
    have hp0 : 0 ≤ |sb1_lv_U D k hT ρ r x j - fderiv ℝ D.V x (sb1e j)| := abs_nonneg _
    have hεW : ε * W ≤ ε1 := by nlinarith
    calc |sb1_lv_e D k hT ρ r x j| * |sb1_lv_U D k hT ρ r x j - fderiv ℝ D.V x (sb1e j)|
        ≤ (ε * W) * (V0 + Kr * ‖x‖ + ε * W + (‖fderiv ℝ D.V 0‖ + B * ‖x‖)) :=
          mul_le_mul hej hb hp0 (by positivity)
      _ = ε * ((V0 + ε * W + ‖fderiv ℝ D.V 0‖) * W + (Kr + B) * (W * ‖x‖)) := by ring
      _ ≤ ε * ((V0 + ε1 + ‖fderiv ℝ D.V 0‖) * 1 + (Kr + B) * 1) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hε0
          · exact mul_le_mul (by linarith) hW1 hW0.le (by linarith)
          · exact mul_le_mul_of_nonneg_left hWx (by linarith)
      _ ≤ ε * (1 + Kr) * c0 := by
          rw [hc0]; nlinarith [mul_nonneg hε0 hK, mul_nonneg hε0 hV00, mul_nonneg hε0 hG0, mul_nonneg hε0 hε10,
            mul_nonneg hε0 hB0, mul_nonneg (mul_nonneg hε0 hK) hV00, mul_nonneg (mul_nonneg hε0 hK) hG0,
            mul_nonneg (mul_nonneg hε0 hK) hε10, mul_nonneg (mul_nonneg hε0 hK) hB0]
  have hsum : |∑ j, sb1_lv_e D k hT ρ r x j * (sb1_lv_U D k hT ρ r x j - fderiv ℝ D.V x (sb1e j))| ≤
      d * (ε * (1 + Kr) * c0) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hterm j).trans (le_of_eq ?_)
    simp
  calc |(∑ j, sb1_lv_cv (sb1_lv_hjj k j) (ρ r) x - ∑ j, fderiv ℝ (sb1F d D.s (ρ r) j) x (sb1e j)) +
        D.invβ⁻¹ * ∑ j, sb1_lv_e D k hT ρ r x j * (sb1_lv_U D k hT ρ r x j - fderiv ℝ D.V x (sb1e j))|
      ≤ ε + D.invβ⁻¹ * (d * (ε * (1 + Kr) * c0)) := by
        refine (abs_add_le _ _).trans (add_le_add (E1 x) ?_)
        rw [abs_mul, abs_of_nonneg hθi]
        exact mul_le_mul_of_nonneg_left hsum hθi
    _ ≤ ε * (1 + Kr) * (1 + D.invβ⁻¹ * d * c0) := by
        have : ε ≤ ε * (1 + Kr) := by nlinarith [mul_nonneg hε0 hK]
        nlinarith [this]

end Main

end HRS.MS.MfeConf
