import HRS.MS.Fp81S21MovingFuture4
import HRS.MS.Fp81S21MovingGram
import HRS.MS.Fp81S21MovingStd2
import HRS.MS.Fp81S21MovingInputs2
import HRS.MS.Fp81S21SLin
import HRS.MS.R2InterpAux40

/-!
# HRS S2.1(iii), packet 12a: moving heat projection regularity

The future is selected once for each physical trajectory.  At every positive horizon we
assemble the moving density and orbit inputs on that horizon and apply the generic S102
Lipschitz-projection estimate.  The conclusion uses the exact `S102LipProj` interface, so its
cutoff-time variables range over the full horizon.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- For every physical trajectory in one common small-radius regime, select its moving future
family and obtain the projected heat time-Lipschitz bound on every positive horizon. -/
theorem fp81s21_moving_heat_lipProj (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ future : (H : ℝ) → ℝ →
            Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
          (∀ H v, IsProbabilityMeasure (future H v)) ∧
          (∀ H : ℝ, 0 < H → ∀ v ∈ Icc (0 : ℝ) H,
            IsR2FutureGaussian (r26t3_coeff R)
              (wholeSpaceIndex p.d : ℝ) H v (future H v)) ∧
          (∀ H : ℝ, ∀ hH : 0 < H,
            S102LipProj (future H)
              (fun L => s102_Pj H hH L)) := by
  obtain ⟨δc, Co, co, hδc, hδcHalf, hco, hcommon⟩ := fp81s21_common_radius p
  obtain ⟨δt, -, -, hδt, hδtHalf, -, htrajectory⟩ :=
    fp81s21_moving_trajectory_fields p
  obtain ⟨δf, hδf, hδfHalf, hfuture⟩ := fp81s21_movingFuture_exists p
  let δ0 : ℝ := min δc (min δt δf)
  have hδ0 : 0 < δ0 := lt_min hδc (lt_min hδt hδf)
  have hδ0Half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδcHalf
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R
  have hδc' : δ ≤ δc := hδle.trans (min_le_left _ _)
  have hδt' : δ ≤ δt := hδle.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδf' : δ ≤ δf := hδle.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨future, hfutureProb, hfutureR2⟩ := hfuture δ hδ hδf' R
  refine ⟨future, hfutureProb, hfutureR2, ?_⟩
  intro H hH
  have hphys := htrajectory δ hδ hδt' R H hH
  obtain ⟨hν, hρint, hρnn, hcls, -, -, -, hgauss, hρmom⟩ := hphys
  obtain ⟨hclaims, -, hterm, -⟩ := hcommon δ hδ hδc' R.ρβ R.thermal
  obtain ⟨c, hD⟩ := fp81s21_moving_s101data_of_common p R hH hclaims hterm
  have hGramCont := fp81s21_moving_gram_continuous_of_fields
    p R hδ (hδle.trans hδ0Half) hH hρnn hgauss hcls
  let hs : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH :=
    ⟨hD, hν, hρint, hρnn, hcls, hGramCont⟩
  obtain ⟨Mρ, hMρ⟩ := hρmom
  have hρmom' : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun x => (r26t3_coeff R).ρ u x * jbracket x ^
        (2 * ((p.d : ℝ) + 2))) ∧
      (∫ x, (r26t3_coeff R).ρ u x * jbracket x ^
        (2 * ((p.d : ℝ) + 2))) ≤ Mρ := by
    intro u hu
    exact hMρ u hu
  have hlin := fp81s21_S102Lin p R H
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide) p.hd
  have hPw : 0 ≤ (p.d : ℝ) + 2 := by positivity
  have hr : (p.d : ℝ) / 2 + 1 < (2 * p.d + 8 : ℕ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hdreal : (0 : ℝ) ≤ (p.d : ℝ) := by positivity
    nlinarith
  have hγp : ∀ v : ℝ, IsProbabilityMeasure (future H v) := fun v => hfutureProb H v
  have hγ : ∀ v ∈ Icc (0 : ℝ) H,
      IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H v
        (future H v) := fun v hv => hfutureR2 H hH v hv
  exact s102_lipProj hd1 hPw hr hP hs.hD hlin hH hν Mρ hρint hρnn
    (by
      intro u hu
      simpa [r26t3_coeff] using hρmom' u hu)
    (fun L => fp81s21_moving_gramInt hs L)
    (future H) hγp hγ

#print axioms HRS.Fp81.S21.fp81s21_moving_heat_lipProj

end HRS.Fp81.S21

end
