import HRS.MS.Fp81S21RespRecon18
import HRS.MS.S21H2_S09

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21 HRS.MS.S21E HRS.MC.E213O

/-- The synthesized cubic response tensor is the initial window tensor. -/
theorem fp81s21_respRecon_initialKappa (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∀ a : ℝ, 0 ≤ a → ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
          tensorPow' 3
            (s21gPhi (r26t3_feature_enum p.d) p.hT ((wholeSpaceIndex p.d : ℕ) : ℝ))
            (s21eKappa0 (r26t3_mu R 0) (fp81s21_initial_ellv R (r26t3_qwin R a))) =
              initialKappa R a := by
  obtain ⟨δp, hp, hphalf, hpath⟩ := fp81s21_respRecon_path p
  obtain ⟨δq, hq, hqhalf, hqwin⟩ := fp81s21_qwin_uniform p
  refine ⟨min δp δq, lt_min hp hq, (min_le_left _ _).trans hphalf,
    fun δ hδ hδle R hγ a ha _ => ?_⟩
  have hδh := hδle.trans ((min_le_left δp δq).trans hphalf)
  obtain ⟨_, _, hfamily⟩ := hqwin δ hδ (hδle.trans (min_le_right _ _)) R
  have hstat := r26t3_static_tensor hδ hδh R hγ (r26t3_qwin R a) ((hfamily a ha).1)
  have hmeas : AEStronglyMeasurable (fp81s21_initial_ellv R (r26t3_qwin R a))
      (r26t3_mu R 0) := by
    exact hstat.1.aestronglyMeasurable
  have hint : Integrable (fun x => ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ *
      ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ *
      ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖) (r26t3_mu R 0) := by
    apply hstat.2.2.1.congr
    filter_upwards with x
    simp only [r26t3_ell, fp81s21_initial_ellv, pow_three, mul_assoc]
  rw [fp81s21_respRecon_tensor_map (r26t3_mu R 0) _ _ hmeas hint]
  change s21eKappa0 (r26t3_mu R 0) (fun x =>
      s21gPhi (r26t3_feature_enum p.d) p.hT ((wholeSpaceIndex p.d : ℕ) : ℝ)
        (fp81s21_initial_ellv R (r26t3_qwin R a) x)) =
    s21eKappa0 (r26t3_mu R 0) (responseWindow R a)
  congr 1
  funext x
  exact hpath δ hδ (hδle.trans (min_le_left _ _)) R hγ a ha x

#print axioms fp81s21_respRecon_initialKappa

end HRS.Fp81.S21
end
