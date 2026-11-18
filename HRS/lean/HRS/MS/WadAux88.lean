import HRS.MS.WadAux87
import HRS.MS.WadAux71

/-!
# S8.3, packet S8E-4, part 4: clause (3) of `weighted_adjoint_decay` for `j = 1`

`s8e_clause3_one`: for `0 ≤ t ≤ T` and `f ∈ C_M^1`: `U_t f ∈ C_M^1` and
`‖U_t f‖_{C_M^1} ≤ K ‖f‖_{C_M^1}` (`U_t = s85_Ulim`; transfers to every `IsWeightedSemigroup` by `s85_semigroup_unique`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_clause3_one {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {t : ℝ}, 0 ≤ t → t ≤ T → ∀ {f : Euc d → ℝ}, MemCMj M 1 f →
      MemCMj M 1 (s85_Ulim a β ρβ M t f) ∧
        weightedSupE 1 (-M) (s85_Ulim a β ρβ M t f) ≤ ENNReal.ofReal K * weightedSupE 1 (-M) f := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨Kl, hKl0, hKl⟩ := s8e_ulim_lip H
  obtain ⟨Kb, hKb0, hKb⟩ := s85_Ulim_wsup H
  obtain ⟨_, _, hsm⟩ := s8d_smoothing H hMpos
  set c3 : ℝ := (3 : ℝ) ^ M with hc3
  have hc30 : 1 ≤ c3 := Real.one_le_rpow (by norm_num) hM
  set cΨ : ℝ := 1 + c3 * (d * c3 + 1) with hcΨ
  refine ⟨max 1 (max Kb (Kl * cΨ * c3)), le_max_left _ _, ?_⟩
  intro t ht htT f hf
  have hfM : MemCM M f := s8e_memCM_of_j hf
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    have : s85_Ulim a β ρβ M 0 f = f := funext fun x => s85_Ulim_at_zero H hfM x
    rw [this]
    refine ⟨hf, ?_⟩
    exact le_mul_of_one_le_left bot_le (by
      rw [ENNReal.one_le_ofReal]; exact le_max_left _ _)
  have hwt0 := s83_wt_of_memCM hfM
  obtain ⟨hmem, -, -⟩ := hsm htpos htT hfM hwt0
  refine ⟨hmem, ?_⟩
  by_cases hfin : weightedSupE 1 (-M) f = ⊤
  · rw [hfin, ENNReal.mul_top (by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact lt_of_lt_of_le one_pos (le_max_left _ _))]
    exact le_top
  set Φ : ℝ := (weightedSupE 1 (-M) f).toReal with hΦ
  have hΦ0 : 0 ≤ Φ := ENNReal.toReal_nonneg
  obtain ⟨hb0, hb1⟩ := s8e_wsup1_bounds hfin
  have hfd : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  -- weighted Lipschitz bound of `f`
  have hLf : ∀ y z : Euc d, ‖z‖ < 1 / 4 → |f (y + z) - f y| ≤ (d * Φ * c3) * ‖z‖ * jbracket y ^ M := by
    intro y z hz
    have hmv := (convex_ball y (1 / 4 : ℝ)).norm_image_sub_le_of_norm_fderiv_le (f := f)
      (C := d * Φ * (c3 * jbracket y ^ M)) (fun w _ => hfd w)
      (fun w hw => (hb1 w).trans (by
        calc (d : ℝ) * Φ * jbracket w ^ M ≤ d * Φ * (c3 * jbracket y ^ M) :=
              mul_le_mul_of_nonneg_left (s84_jb_ball hM hw) (by positivity)
          _ ≤ _ := le_rfl))
      (mem_ball_self (by norm_num)) (show y + z ∈ ball y (1 / 4) by
        rw [mem_ball_iff_norm]; simpa using hz)
    rw [add_sub_cancel_left, Real.norm_eq_abs] at hmv
    refine hmv.trans (le_of_eq ?_)
    ring
  have hΛ0 : 0 ≤ (d : ℝ) * Φ * c3 := by positivity
  have hlip := @hKl t Φ ((d : ℝ) * Φ * c3) f htpos htT hfM hb0 hΛ0 hLf
  -- gradient bound
  have hU1 : ContDiff ℝ 1 (s85_Ulim a β ρβ M t f) := hmem.1
  have hgrad : ∀ x, ‖fderiv ℝ (s85_Ulim a β ρβ M t f) x‖ ≤ (Kl * cΨ * c3 * Φ) * jbracket x ^ M := by
    intro x
    have hjx := Real.rpow_nonneg (s83_jb_pos x).le M
    have hB : 0 ≤ Kl * cΨ * c3 * Φ * jbracket x ^ M := by positivity
    refine s84_fderiv_le_of_lip (u := s85_Ulim a β ρβ M t f) (x := x) (ε := 1 / 16)
      (by norm_num) hB (hU1.differentiable (by norm_num)).differentiableAt (fun y hy y' hy' => ?_)
    rw [mem_ball_iff_norm] at hy hy'
    have hζ : ‖y' - y‖ < 1 / 8 := by
      calc ‖y' - y‖ ≤ ‖y' - x‖ + ‖x - y‖ := norm_sub_le_norm_sub_add_norm_sub y' x y
        _ < 1 / 16 + 1 / 16 := by rw [norm_sub_rev x y]; linarith
        _ = 1 / 8 := by norm_num
    have h1 := hlip (y' - y) hζ y
    rw [add_sub_cancel] at h1
    refine h1.trans ?_
    have hyx : jbracket y ^ M ≤ c3 * jbracket x ^ M :=
      s84_jb_ball hM (by rw [mem_ball_iff_norm]; linarith)
    have hn := norm_nonneg (y' - y)
    calc Kl * (Φ + c3 * (d * Φ * c3 + Φ)) * ‖y' - y‖ * jbracket y ^ M
        ≤ Kl * (Φ + c3 * (d * Φ * c3 + Φ)) * ‖y' - y‖ * (c3 * jbracket x ^ M) :=
          mul_le_mul_of_nonneg_left hyx (by positivity)
      _ = (Kl * cΨ * c3 * Φ * jbracket x ^ M) * ‖y' - y‖ := by rw [hcΨ]; ring
  -- zero order bound
  have hzero : weightedSupE 0 (-M) f ≤ ENNReal.ofReal Φ := (s83_wsup0_le_iff hΦ0 f).2 hb0
  have hU0 : weightedSupE 0 (-M) (s85_Ulim a β ρβ M t f) ≤ ENNReal.ofReal (Kb * Φ) := by
    refine (hKb ht htT hfM).trans ?_
    rw [ENNReal.ofReal_mul hKb0]
    exact mul_le_mul' le_rfl hzero
  have hU0' := (s83_wsup0_le_iff (mul_nonneg hKb0 hΦ0) _).1 hU0
  have hUp : ∀ x, ‖s85_Ulim a β ρβ M t f x‖ ≤ (Kb * Φ) * jbracket x ^ M := fun x => by
    rw [Real.norm_eq_abs]
    exact hU0' x
  set K : ℝ := max 1 (max Kb (Kl * cΨ * c3)) with hK
  have hK1 : Kb ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK2 : Kl * cΨ * c3 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hK0 : 0 ≤ K := (zero_le_one).trans (le_max_left _ _)
  refine (s8d_wsup1_le (B := K * Φ) (fun x => ?_) (fun x => ?_)).trans ?_
  · exact (hUp x).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hΦ0)
      (Real.rpow_nonneg (s83_jb_pos x).le _))
  · exact (hgrad x).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hΦ0)
      (Real.rpow_nonneg (s83_jb_pos x).le _))
  · rw [ENNReal.ofReal_mul hK0, hΦ, ENNReal.ofReal_toReal hfin]

end HRS.MS.Wad
