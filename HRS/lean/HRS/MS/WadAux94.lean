import HRS.MS.WadAux93

/-!
# S8.3, packet S8E-5, part 5: decay of the sections and the pointwise tensor bound for `s85_Ulim`

`s8e_G_cm`: `x' ↦ U_t(R x')(y)` lies in `C_M`.  `s8e_tensor_pt`: for `t ≥ 1`, doubly centered `R` with
`|Q| ≤ N0`: `|U_t[x' ↦ U_t(R x')(y)](x)| ≤ C_d e^{-ct}(C_d e^{-ct} + m_M) N_0 ⟨x⟩^M⟨y⟩^M`, `m_M = ∫⟨·⟩^M dμ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_R_wt_x {M : ℝ} {R : Euc d → Euc d → ℝ} {N : ℝ} {x : Euc d}
    (hN : ∀ y, |s8e_Qa M R (x, y)| ≤ N) : Wt M (N * jbracket x ^ M) (R x) := fun y => by
  rw [Real.norm_eq_abs, s8e_R_eq M R x y, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos x).le M), abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos y).le M)]
  have := hN y
  have h1 := Real.rpow_nonneg (s83_jb_pos x).le M
  have h2 := Real.rpow_nonneg (s83_jb_pos y).le M
  calc jbracket x ^ M * jbracket y ^ M * |s8e_Qa M R (x, y)| ≤ jbracket x ^ M * jbracket y ^ M * N :=
        mul_le_mul_of_nonneg_left this (mul_nonneg h1 h2)
    _ = _ := by ring

theorem s8e_G_cm (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {Cd c : ℝ} (hCd : 0 ≤ Cd)
    (h2a : S8e2a a β M ρβ Cd c) {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R)
    (hdc : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R) {t : ℝ} (ht : 1 ≤ t) (y : Euc d) :
    MemCM M (fun x' => s85_Ulim a β ρβ M t (R x') y) := by
  refine ⟨s8e_G_cont hd ha hβ hρ hMpos hCd h2a hR hdc ht y, ?_⟩
  set κ : ℝ := Cd * Real.exp (-c * t) * jbracket y ^ M with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg (mul_nonneg hCd (Real.exp_pos _).le) (Real.rpow_nonneg (s83_jb_pos y).le _)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε / (2 * (κ + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρ, hρ'⟩ := s8e_Q_sup_decay hR hη0
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop ρ] with x' hx'
  have hb := h2a ht (s8e_R_cm hR x') (s8e_R_wt_x (fun y' => hρ' x' y' hx') ) y
  rw [s8e_projMean_centered (hdc.2 x')] at hb
  have hjx := Real.rpow_pos_of_pos (s83_jb_pos x') M
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hjx, div_lt_iff₀ hjx]
  refine lt_of_le_of_lt hb ?_
  have e : Cd * Real.exp (-c * t) * (η * jbracket x' ^ M) * jbracket y ^ M = κ * η * jbracket x' ^ M := by
    rw [hκ]; ring
  rw [e]
  refine mul_lt_mul_of_pos_right ?_ hjx
  rw [hη, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

theorem s8e_Ulim_projMean (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {t : ℝ} (ht : 1 ≤ t) {G : Euc d → ℝ}
    (hG : MemCM M G) (x : Euc d) :
    s85_Ulim a β ρβ M t G x = s85_Ulim a β ρβ M t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) G) x +
      HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) G := by
  have H : S85Hyp d a β t M ρβ := ⟨hd, ha, hβ, by linarith, hMpos.le, hρ⟩
  have h1 := s85_Ulim_lin H (by linarith) le_rfl (s8d_memCM_const hMpos 1) hG
    (-(HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) G)) x
  have h2 := s8d_Ulim_one H hMpos (by linarith) le_rfl x
  have e : (fun y => -(HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) G) * (fun _ : Euc d => (1 : ℝ)) y + G y) =
      HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) G := by
    funext y; unfold HRS.Whole.projMean; ring
  rw [e, h2] at h1
  linarith

end HRS.MS.Wad
