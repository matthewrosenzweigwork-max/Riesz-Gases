import HRS.MS.TransOpAux12

/-!
# S611 packet P2f: strong continuity of `c ↦ Λ_c` and joint continuity
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- The basis element `e_β` of `B_m`: `coord (e_β) γ = δ_{βγ}`. -/
def s611_e1 (M : ℝ) (β : MultiIndex d) : OscDual d M :=
  (lp.single 2 β (1 : ℝ) : lp (fun _ : MultiIndex d => ℝ) 2)

theorem s611_e1_coord (M : ℝ) (β γ : MultiIndex d) :
    OscDual.coord (s611_e1 M β) γ = if γ = β then 1 else 0 := by
  unfold s611_e1 OscDual.coord
  simp [lp.single_apply, Pi.single_apply]

theorem s611_eval_e1 (M : ℝ) (β : MultiIndex d) (φ : Euc d → ℝ) :
    OscDual.eval (s611_e1 M β) φ = oscEigenvalue d β ^ (M / 2) * hermiteCoeff φ β := by
  unfold OscDual.eval
  rw [tsum_eq_single β]
  · unfold OscDual.hermiteCoeff; rw [s611_e1_coord]; simp
  · intro γ hγ
    unfold OscDual.hermiteCoeff
    rw [s611_e1_coord, if_neg hγ]; simp

theorem s611_hermiteCoeff_translate_eq (β α : MultiIndex d) (c : Euc d) :
    hermiteCoeff (fun x => hermiteFunD α (x + c)) β =
      hermiteCoeff (fun y => hermiteFunD β (y - c)) α := by
  unfold hermiteCoeff
  rw [← s611_integral_translate (fun y => hermiteFunD β (y - c) * hermiteFunD α y) c]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [add_sub_cancel_right]
  ring

theorem s611_K_continuous (m : ℕ) : Continuous (fun c : Euc d => s611_K m c) := by
  unfold s611_K
  have : ∀ j : Fin d, Continuous (fun c : Euc d => c j) := fun j => by fun_prop
  fun_prop

theorem s611_Lam_e1_dist_le (m : ℕ) (hm : 1 ≤ m) (β : MultiIndex d) (c c₀ : Euc d) :
    ‖s611_Lam m hm c (s611_e1 (m : ℝ) β) - s611_Lam m hm c₀ (s611_e1 (m : ℝ) β)‖ ≤
      Real.sqrt (oscEigenvalue d β ^ (m : ℝ) *
        ∫ y, (hermiteFunD β (y - c) - hermiteFunD β (y - c₀)) ^ 2) := by
  rw [OscDual.norm_eq_coord]
  apply Real.sqrt_le_sqrt
  set g : Euc d → ℝ := fun y => hermiteFunD β (y - c) - hermiteFunD β (y - c₀) with hg
  have hL1 : ∀ z : Euc d, MemLp (fun y => hermiteFunD β (y - z)) 2 (volume : Measure (Euc d)) := fun z => by
    have := s611_memLp_translate (memLp_hermiteFunD β) (-z)
    simpa [sub_eq_add_neg] using this
  have hgL : MemLp g 2 (volume : Measure (Euc d)) := (hL1 c).sub (hL1 c₀)
  obtain ⟨hs, hp⟩ := hermite_parseval_aux g hgL
  have hcoef : ∀ α, hermiteCoeff g α =
      hermiteCoeff (fun x => hermiteFunD α (x + c)) β - hermiteCoeff (fun x => hermiteFunD α (x + c₀)) β := by
    intro α
    rw [s611_hermiteCoeff_translate_eq, s611_hermiteCoeff_translate_eq]
    unfold hermiteCoeff
    rw [← integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hg]; ring
    · exact (hL1 c).integrable_mul (memLp_hermiteFunD α)
    · exact (hL1 c₀).integrable_mul (memLp_hermiteFunD α)
  have hcD : ∀ α, OscDual.coord (s611_Lam m hm c (s611_e1 (m : ℝ) β) -
      s611_Lam m hm c₀ (s611_e1 (m : ℝ) β)) α ^ 2 ≤
      oscEigenvalue d β ^ (m : ℝ) * hermiteCoeff g α ^ 2 := by
    intro α
    have h1 : OscDual.hermiteCoeff (s611_Lam m hm c (s611_e1 (m : ℝ) β) -
        s611_Lam m hm c₀ (s611_e1 (m : ℝ) β)) α =
        oscEigenvalue d β ^ ((m : ℝ) / 2) * hermiteCoeff g α := by
      rw [sub_eq_add_neg, ← neg_one_smul ℝ (s611_Lam m hm c₀ (s611_e1 (m : ℝ) β)),
        OscDual.hermiteCoeff_add, OscDual.hermiteCoeff_smul, s611_hermiteCoeff_Lam, s611_hermiteCoeff_Lam,
        s611_eval_e1, s611_eval_e1, hcoef]
      ring
    have h2 := OscDual.hermiteCoeff_sq (s611_Lam m hm c (s611_e1 (m : ℝ) β) -
        s611_Lam m hm c₀ (s611_e1 (m : ℝ) β)) α
    rw [h1, mul_pow, rpow_half_sq _ _ (oscEv_pos β)] at h2
    have hpos : 0 < oscEigenvalue d α ^ (-(m : ℝ)) := Real.rpow_pos_of_pos (oscEv_pos α) _
    have hle : oscEigenvalue d α ^ (-(m : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (oscEv_one_le α) (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
    have hnn : 0 ≤ oscEigenvalue d β ^ (m : ℝ) * hermiteCoeff g α ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (oscEv_pos β).le _) (sq_nonneg _)
    nlinarith
  calc ∑' α, OscDual.coord (s611_Lam m hm c (s611_e1 (m : ℝ) β) -
      s611_Lam m hm c₀ (s611_e1 (m : ℝ) β)) α ^ 2
      ≤ ∑' α, oscEigenvalue d β ^ (m : ℝ) * hermiteCoeff g α ^ 2 :=
        Summable.tsum_le_tsum hcD (OscDual.coord_sq_summable' _) (hs.mul_left _)
    _ = oscEigenvalue d β ^ (m : ℝ) * ∫ y, (hermiteFunD β (y - c) - hermiteFunD β (y - c₀)) ^ 2 := by
        rw [tsum_mul_left, hp]

theorem s611_Lam_e1_tendsto (m : ℕ) (hm : 1 ≤ m) (β : MultiIndex d) (c₀ : Euc d) :
    Tendsto (fun c : Euc d => s611_Lam m hm c (s611_e1 (m : ℝ) β)) (𝓝 c₀)
      (𝓝 (s611_Lam m hm c₀ (s611_e1 (m : ℝ) β))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun c => norm_nonneg _) (fun c => s611_Lam_e1_dist_le m hm β c c₀) ?_
  have h := s611_l2_continuity β c₀
  have h2 := (Real.continuous_sqrt.tendsto (oscEigenvalue d β ^ (m : ℝ) * 0)).comp
    (h.const_mul (oscEigenvalue d β ^ (m : ℝ)))
  simpa [Function.comp_def] using h2

end HRS.MS.TransOp

end
