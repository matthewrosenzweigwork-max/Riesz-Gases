import HRS.MS.MovLinAux17

/-!
# MOV-LIN, part 9: smoothing for the `L²_0`-adjoint by duality (sequence level)

Namespace `HRS.MS.MovLin`, helpers `movlin_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

`movlin_adj_seq`: if `u ∈ Σ^0` is orthogonal to `e₁ = √ρ` and `⟨u,y⟩ = ⟨j z_w, G_0(t) y⟩` for all `y ⊥ e₁`, with
`z_w ∈ Σ^{ρ'}` (`0 ≤ ρ'`), then `u = j z` with `z ∈ Σ^σ` and `‖z‖ ≤ C t^{-(σ-ρ')/2} ‖z_w‖` (`ρ' ≤ σ`, `0 < t ≤ 1`).
Proof: the duality criterion `movlin_dual_crit`, the smoothing `movlin_smooth` at the negative levels `-σ → -ρ'`, and
the splitting `y = y_K + κ e₁` (the `e₁`-part costs a constant).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

section AdjSeq

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

set_option maxHeartbeats 1600000 in
lemma movlin_adj_seq (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) {ρ' σ : ℝ} (hρ' : 0 ≤ ρ') (hρσ : ρ' ≤ σ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ (zw : OscSpace d ρ') (u : OscSpace d 0),
      inner ℝ (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ)) u = 0 →
      (∀ y : OscSpace d 0, inner ℝ (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ)) y = 0 →
        inner ℝ u y = inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t y)) →
      ∃ z : OscSpace d σ, mov2d_j (hρ'.trans hρσ) z = u ∧ ‖z‖ ≤ Cc * t ^ (-((σ - ρ') / 2)) * ‖zw‖ := by
  have hσ : 0 ≤ σ := hρ'.trans hρσ
  obtain ⟨C, hC0, hC⟩ := movlin_smooth H (show -σ ≤ -ρ' by linarith)
  obtain ⟨N0, hN0, hN⟩ := movlin_G_bound1 H 0
  set e1 : OscSpace d 0 := OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ) with he1
  set zE : OscSpace d σ := OscSpace.ofFun σ (⇑ψ0 : Euc d → ℝ) with hzE
  have hjE : mov2d_j hσ zE = e1 := mov2d_j_ofFun hσ (memOsc_schwartz σ ψ0)
  refine ⟨C + ‖zE‖ * N0 / ‖e1‖, by positivity, fun t ht zw u hu1 hpair => ?_⟩
  have hexp : -((σ - ρ') / 2) ≤ 0 := by linarith
  have hone : 1 ≤ t ^ (-((σ - ρ') / 2)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 hexp
  refine movlin_dual_crit hσ u (by positivity) (fun y => ?_)
  set ny : ℝ := ‖mov2d_j (neg_nonpos.2 hσ) y‖ with hny
  have hny0 : 0 ≤ ny := norm_nonneg _
  have hzw0 : 0 ≤ ‖zw‖ := norm_nonneg _
  set κ : ℝ := inner ℝ e1 y / ‖e1‖ ^ 2 with hκ
  have hκ0 : inner ℝ e1 (y - κ • e1) = 0 := by
    by_cases he : e1 = 0
    · simp [he]
    · have : ‖e1‖ ^ 2 ≠ 0 := by positivity
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hκ]
      field_simp
      ring
  have hue : inner ℝ u e1 = 0 := by rw [real_inner_comm]; exact hu1
  have hdec : inner ℝ u y = inner ℝ u (y - κ • e1) := by
    rw [inner_sub_right, inner_smul_right, hue]; ring
  have hp := hpair (y - κ • e1) hκ0
  have hG : mov2d_G H 0 t (y - κ • e1) = mov2d_G H 0 t y - κ • mov2d_G H 0 t e1 := by
    rw [map_sub, map_smul]
  rw [hG] at hp
  have hp2 : inner ℝ u (y - κ • e1) = inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t y) -
      κ * inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t e1) := by
    rw [hp, inner_sub_right, inner_smul_right]
  -- first term
  obtain ⟨z'', hz''1, hz''2⟩ := hC t ht (mov2d_j (neg_nonpos.2 hσ) y)
  have hh1 : -σ ≤ -ρ' := by linarith
  have hz'' : mov2d_j (neg_nonpos.2 hρ') (mov2d_G H 0 t y) = z'' := by
    apply movlin_j_inj hh1
    rw [movlin_j_comp (neg_nonpos.2 hρ') hh1, hz''1]
    exact (mov2d_G_compat H (neg_nonpos.2 hσ) ht.1.le y)
  have hT1 : |inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t y)| ≤ ‖zw‖ * (C * t ^ (-((σ - ρ') / 2)) * ny) := by
    have e := movlin_j_inner hρ' zw (mov2d_G H 0 t y)
    have e' : inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t y) = movlin_pr zw (mov2d_j (neg_nonpos.2 hρ') (mov2d_G H 0 t y)) := e
    rw [e', hz'']
    refine (movlin_pr_abs_le zw z'').trans ?_
    have hz3 : ‖z''‖ ≤ C * t ^ (-((σ - ρ') / 2)) * ny := by
      have : -((-ρ' - -σ) / 2) = -((σ - ρ') / 2) := by ring
      rw [this] at hz''2
      exact hz''2
    exact mul_le_mul_of_nonneg_left hz3 hzw0
  -- second term
  have hT2 : |κ * inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t e1)| ≤ ‖zE‖ * N0 / ‖e1‖ * ‖zw‖ * ny := by
    by_cases he : e1 = 0
    · simp [he]
    · have hpos : 0 < ‖e1‖ := norm_pos_iff.2 he
      have h1 : |inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t e1)| ≤ ‖zw‖ * (N0 * ‖e1‖) := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        have hj : ‖mov2d_j hρ' zw‖ ≤ ‖zw‖ :=
          ((mov2d_j hρ').le_opNorm zw).trans (by
            simpa using mul_le_mul_of_nonneg_right (mov2d_j_norm_le (d := d) hρ') hzw0)
        have hg : ‖mov2d_G H 0 t e1‖ ≤ N0 * ‖e1‖ :=
          ((mov2d_G H 0 t).le_opNorm e1).trans
            (mul_le_mul_of_nonneg_right (hN t ⟨ht.1.le, ht.2⟩) (norm_nonneg _))
        exact mul_le_mul hj hg (norm_nonneg _) hzw0
      have h2 : |inner ℝ e1 y| ≤ ‖zE‖ * ny := by
        have e : inner ℝ e1 y = movlin_pr zE (mov2d_j (neg_nonpos.2 hσ) y) := by
          rw [← hjE]; exact movlin_j_inner hσ zE y
        rw [e]; exact movlin_pr_abs_le _ _
      have hκabs : |κ| = |inner ℝ e1 y| / ‖e1‖ ^ 2 := by
        rw [hκ, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖e1‖ ^ 2)]
      rw [abs_mul, hκabs]
      calc |inner ℝ e1 y| / ‖e1‖ ^ 2 * |inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t e1)|
          ≤ (‖zE‖ * ny) / ‖e1‖ ^ 2 * (‖zw‖ * (N0 * ‖e1‖)) := by
            apply mul_le_mul (div_le_div_of_nonneg_right h2 (by positivity)) h1 (abs_nonneg _) (by positivity)
        _ = ‖zE‖ * N0 / ‖e1‖ * ‖zw‖ * ny := by field_simp
  -- combine
  rw [movlin_pr_zero, hdec, hp2]
  have hK2 : 0 ≤ ‖zE‖ * N0 / ‖e1‖ := by positivity
  have habs : |inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t y) - κ * inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t e1)| ≤
      ‖zw‖ * (C * t ^ (-((σ - ρ') / 2)) * ny) + ‖zE‖ * N0 / ‖e1‖ * ‖zw‖ * ny := by
    calc _ ≤ |inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t y)| + |κ * inner ℝ (mov2d_j hρ' zw) (mov2d_G H 0 t e1)| :=
          abs_sub _ _
      _ ≤ _ := add_le_add hT1 hT2
  refine habs.trans ?_
  have : ‖zE‖ * N0 / ‖e1‖ * ‖zw‖ * ny ≤ ‖zE‖ * N0 / ‖e1‖ * t ^ (-((σ - ρ') / 2)) * ‖zw‖ * ny := by
    have h0 : 0 ≤ ‖zE‖ * N0 / ‖e1‖ * ‖zw‖ * ny := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hone h0]
  nlinarith

end AdjSeq

end HRS.MS.MovLin
