import HRS.MS.Fp81S21RespRecon14

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- The cosine analysis coordinate of the response window equals the
response of qwin almost everywhere under the initial reference measure. -/
theorem fp81s21_respRecon_obs_ae (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∀ a : ℝ, 0 ≤ a → ∀ j : ℕ,
          (fun x => fp81s21_cosRecon_obs26 p (responseWindow R a x) j)
            =ᵐ[r26t3_mu R 0] r26t3_a R (r26t3_qwin R a j) := by
  obtain ⟨δi, hi, hihalf, hinter⟩ := fp81s21_respRecon_qwin_interchange_ae p
  obtain ⟨δg, hg, hghalf, hgen⟩ := fp81s21_responseWindow_genuine p
  obtain ⟨δo, ho, hohalf, horbit⟩ := fp81s21_respRecon_orbit_bounds p
  let D := min δi (min δg δo)
  have hDi : D ≤ δi := min_le_left _ _
  have hDg : D ≤ δg := (min_le_right _ _).trans (min_le_left _ _)
  have hDo : D ≤ δo := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨D, lt_min hi (lt_min hg ho), hDi.trans hihalf,
    fun δ hδ hδle R hγ a ha j => ?_⟩
  have hδh := hδle.trans (hDi.trans hihalf)
  let n := (r26t3_feature_enum p.d j).1
  let α := (r26t3_feature_enum p.d j).2
  let A : ℝ := (1 + (n : ℝ) ^ 2) ^ (3 / 8 : ℝ)
  obtain ⟨B, hB, hreg, hcont⟩ := horbit δ hδ (hδle.trans hDo) R a ha α
  filter_upwards [hinter δ hδ (hδle.trans hDi) R hγ a ha j] with x hx
  obtain ⟨-, -, hcoord⟩ := hgen δ hδ (hδle.trans hDg) R hγ a ha x
  rw [hx]
  change A * (∫ t in Icc (0 : ℝ) p.T, r26t3_cosine p.T n t *
    fp81s21_cosRecon_coordExt (responseWindow R a x) α t) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hm := (hreg t ht).1
  have hsmul := fp81s21_response_smul hδ hδh R hγ
    (r26t3_U R 0 (a + t) (oscTestFun (wholeSpaceIndex p.d : ℝ) α))
    hm (A * r26t3_cosine p.T n t) x
  have he : ((A * r26t3_cosine p.T n t) •
      r26t3_U R 0 (a + t) (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) =
      (fun y => A * r26t3_cosine p.T n t *
        r26t3_U R 0 (a + t) (oscTestFun (wholeSpaceIndex p.d : ℝ) α) y) := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  rw [he] at hsmul
  rw [hsmul]
  have hcoord' := hcoord ⟨t, ht⟩ α
  simp only [fp81s21_cosRecon_coordExt, ht, dif_pos]
  rw [hcoord']
  simp only [r26t3_U, Subtype.coe_mk]
  ring

#print axioms fp81s21_respRecon_obs_ae

end HRS.Fp81.S21
end
