import HRS.MS.Fp81S21RespRecon15

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- Each cosine observation of the response window is continuous in the
spatial point. -/
theorem fp81s21_respRecon_obs_continuous (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∀ a : ℝ, 0 ≤ a → ∀ j : ℕ,
          Continuous (fun x => fp81s21_cosRecon_obs26 p (responseWindow R a x) j) := by
  obtain ⟨δc, Co, co, hc, hchalf, hco, hcommon⟩ := fp81s21_common_radius p
  obtain ⟨δw, hw, hwhalf, hwin⟩ := fp81s21_responseWindow_continuous p
  obtain ⟨δg, hg, hghalf, hgen⟩ := fp81s21_responseWindow_genuine p
  let D := min δc (min δw δg)
  have hDc : D ≤ δc := min_le_left _ _
  have hDw : D ≤ δw := (min_le_right _ _).trans (min_le_left _ _)
  have hDg : D ≤ δg := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨D, lt_min hc (lt_min hw hg), hDc.trans hchalf,
    fun δ hδ hδle R hγ a ha j => ?_⟩
  have hδh := hδle.trans (hDc.trans hchalf)
  obtain ⟨hclaims, -, hterm, -⟩ := hcommon δ hδ (hδle.trans hDc) R.ρβ R.thermal
  obtain ⟨C, hC, hmode⟩ := fp81s21_response_mode_bound_of_orbits hδ hδh R hγ hclaims hterm
  have hwc := hwin δ hδ (hδle.trans hDw) R hγ a ha
  let n := (r26t3_feature_enum p.d j).1
  let α := (r26t3_feature_enum p.d j).2
  let A : ℝ := (1 + (n : ℝ) ^ 2) ^ (3 / 8 : ℝ)
  let K : ℝ := Real.sqrt (2 / p.T) * (C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α))
  let F : Euc p.d → ℝ → ℝ := fun x t => r26t3_cosine p.T n t *
    fp81s21_cosRecon_coordExt (responseWindow R a x) α t
  have hcos : ∀ t, r26t3_cosine p.T n t = r2CosBasis p.T n t := by
    intro t
    unfold r26t3_cosine r2CosBasis
    split_ifs <;> simp [one_div]
  have hcoscont : Continuous (r26t3_cosine p.T n) := by
    have he : r26t3_cosine p.T n = r2CosBasis p.T n := funext hcos
    rw [he]
    exact HRS.MS.R2WinOrb.s103_cosBasis_continuous p.T n
  have htime (x : Euc p.d) : ContinuousOn
      (fp81s21_cosRecon_coordExt (responseWindow R a x) α) (Icc (0 : ℝ) p.T) := by
    apply continuousOn_iff_continuous_restrict.mpr
    have h := (HRS.MS.R2Interp.s102_coordCLM
      (m := (wholeSpaceIndex p.d : ℝ)) α).continuous.comp (responseWindow R a x).continuous
    have he : (Icc (0 : ℝ) p.T).domRestrict
        (fp81s21_cosRecon_coordExt (responseWindow R a x) α) =
        (fun t => OscDual.coord (OscPath.at' (responseWindow R a x) t) α) := by
      funext t
      simp [Set.domRestrict, fp81s21_cosRecon_coordExt, t.2]
    rw [he]
    exact h
  have hFx (t : ℝ) (ht : t ∈ Icc (0 : ℝ) p.T) : Continuous (fun x => F x t) := by
    have h := ((HRS.MS.R2Interp.s102_coordCLM
      (m := (wholeSpaceIndex p.d : ℝ)) α).comp (ContinuousMap.evalCLM ℝ ⟨t, ht⟩)).continuous.comp hwc
    have he : (fun x => F x t) = (fun x => r26t3_cosine p.T n t *
        OscDual.coord (OscPath.at' (responseWindow R a x) ⟨t, ht⟩) α) := by
      funext x
      have ht' : 0 ≤ t ∧ t ≤ p.T := ht
      simp [F, fp81s21_cosRecon_coordExt, ht']
    rw [he]
    exact continuous_const.mul h
  have hFb (x : Euc p.d) : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) p.T)), ‖F x t‖ ≤ K := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    obtain ⟨-, -, hcoord⟩ := hgen δ hδ (hδle.trans hDg) R hγ a ha x
    have htime' : 0 ≤ a + t := add_nonneg ha ht.1
    have hb := hmode (a + t) htime' α x
    have hcb := s11p_cos_bound p.hT n t
    rw [← hcos t] at hcb
    have hD0 : 0 ≤ C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α) := by
      exact mul_nonneg hC (mul_nonneg (abs_nonneg _) (HRS.MS.R2WinOrb.s103_b_nonneg α))
    dsimp [F, K]
    rw [abs_mul]
    simp only [fp81s21_cosRecon_coordExt, ht, dif_pos]
    rw [hcoord ⟨t, ht⟩ α]
    exact mul_le_mul hcb hb (abs_nonneg _) (Real.sqrt_nonneg _)
  have hFcont : Continuous (fun x => ∫ t in Icc (0 : ℝ) p.T, F x t) := by
    refine continuous_of_dominated (bound := fun _ => K) ?_ hFb (integrable_const _) ?_
    · intro x
      exact (hcoscont.continuousOn.mul (htime x)).aestronglyMeasurable measurableSet_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hFx t ht
  change Continuous (fun x => A * ∫ t in Icc (0 : ℝ) p.T, F x t)
  exact continuous_const.mul hFcont

#print axioms fp81s21_respRecon_obs_continuous

end HRS.Fp81.S21
end
