import HRS.MS.Fp81S21JointG
import HRS.MS.Fp81S21JointT

/-! The fixed Gaussian linear projection tail for every time representative. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The selected canonical linear projection profile applies to every genuine
representative, not only the representative selected by the producer. -/
theorem fp81s21_jointG_linear_projection_tail
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εG εB : ℕ → ℝ) (S : fp81s21_GaussianPhysical31 p R Es E εG εB)
    (G : GaussianRealization R) (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (V : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hV : fp81s21_TimeL2Rep G.P
      (fp81s21_gaussian_embedFamily p Es E (S.qsηG G)) S.MηG a H V)
    (m : ℕ) :
    fp81s21_SqErr G.P V (fun ω => fp81s21_timeProject H m (V ω))
      (Real.sqrt (H * S.MηG) * εG m) := by
  let q := fp81s21_gaussian_embedFamily p Es E (S.qsηG G)
  have hq : Measurable (Function.uncurry q) :=
    (S.gaussian_linear G).coefficients.weak_momentRep.1
  obtain ⟨U, hU, htail⟩ := (S.gaussian_linear G).coefficients.time_sections a ha H hH
  have heq : V =ᵐ[G.P] U :=
    fp81s21_TimeL2Rep_eq_ae G.P q q S.MηG S.MηG a H V U hq hq ha
      (fun _ _ => Filter.Eventually.of_forall (fun _ => rfl)) hV hU
  have he : (fun ω => ‖V ω - fp81s21_timeProject H m (V ω)‖ ^ 2) =ᵐ[G.P]
      (fun ω => ‖U ω - fp81s21_timeProject H m (U ω)‖ ^ 2) := by
    filter_upwards [heq] with ω hω
    rw [hω]
  exact ⟨(htail m).1.1.congr he.symm, (integral_congr_ae he).le.trans (htail m).1.2⟩

#print axioms fp81s21_jointG_linear_projection_tail
end HRS.Fp81.S21
end
