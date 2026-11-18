import HRS.MS.Fp81S21WindowFeature13

/-!
# S2.1 packet 15c: applying the positive trace estimate

This removes the conditional positive-derivative input from the previous
assembly lemma by deriving it from the wR33 moving-orbit data.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.MS.CovMeas
open HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.FixEq

/-- The S101 positive-order trace estimate for a moving observation window,
with the exponential feature bound discharged from wR33 data. -/
theorem fp81s21_window_feature_trace_bound_pos_of_decay_data
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {Cs0 cdec : ℝ} (hCs0 : 0 ≤ Cs0) (hcdec : 0 < cdec)
    (hsumb : Summable (s104_b p.d))
    (hdecay : fp81s21_WindowOrbitDecay p R Cs0 cdec) :
    ∃ Cmix : ℝ, 0 ≤ Cmix ∧ Cs0 ≤ Cmix ∧
      ∀ a : ℝ, 0 ≤ a → ∀ v : ℝ, v ∈ Icc (0 : ℝ) (a + p.T) →
      ∀ c : MultiIndex p.d → ℝ,
        S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (a + p.T) (2 * p.d + 8) c →
      ∀ {P : ℝ}, (p.d : ℝ) < 2 * P →
      ∀ {η : (Euc p.d → ℝ) → ℝ},
        IsBoundedLinearOnE (2 * p.d + 8) P η →
      ∀ (Dc : KSpace p.d (wholeSpaceIndex p.d : ℝ) p.T →L[ℝ]
        KSpace p.d (wholeSpaceIndex p.d : ℝ) p.T →L[ℝ] ℝ),
        (∀ u w, Dc u w = η
          (s101Fm (fp81s21_window_feature (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) p.T a v) (s101Rk u w))) →
        ENNReal.ofReal (HRS.traceNormForm Dc) ≤
          dualNormE (2 * p.d + 8) P η *
            ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
              ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                (fp81s21_window_feature_Bpos p.d (2 * p.d + 8) p.T
                  Cmix cdec a v) ^ 2)) := by
  obtain ⟨Cmix, hmix0, hmixCs, hPosAll⟩ :=
    fp81s21_window_feature_hpos_of_decay_data p R hterm hCs0 hcdec hsumb hdecay
  refine ⟨Cmix, hmix0, hmixCs, ?_⟩
  intro a ha v hv c hD P hP η hη Dc hDc
  have hPos := hPosAll a ha v hv c hD
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hAmp := fp81s21_window_orbit_amplitude_sq_sum (d := p.d)
    Cmix cdec a v hmix0 hsumb
  have hcoeff : 0 ≤ 2 + (p.d : ℝ) ^ (2 * p.d + 9) *
      ((volume.restrict (Icc (0 : ℝ) p.T)) Set.univ).toReal ^
        (1 / 2 : ℝ) := by positivity
  have hBpos : 0 ≤ fp81s21_window_feature_Bpos p.d (2 * p.d + 8) p.T
      Cmix cdec a v := by
    unfold fp81s21_window_feature_Bpos
    exact mul_nonneg hcoeff hAmp.1
  have horb : ∀ α : MultiIndex p.d,
      S104nOrbit (r26t3_coeff R)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) (a + p.T) := by
    intro α
    exact s104b_orbit_of_termRegGen hterm R.admissible R.resulting α
      (a + p.T) (by linarith [ha, p.hT.le])
  have hterminal : ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
      propagatorW (r26t3_coeff R) v v
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x =
          oscTestFun (wholeSpaceIndex p.d : ℝ) α x := by
    intro α x
    have hcl := HRS.MS.Fcau.propagatorW_isClassical ((horb α).ex0 v hv)
    simpa using congrFun hcl.terminal x
  simpa using
    (fp81s21_window_feature_trace_bound_pos_of_data
      (hd := hd1) (C := r26t3_coeff R)
      (m := (wholeSpaceIndex p.d : ℝ)) (H := p.T) (a := a) (v := v)
      (r := 2 * p.d + 8) (c := c) p.hT ha hv hD hterminal hP hη hBpos hPos Dc hDc)

#print axioms fp81s21_window_feature_trace_bound_pos_of_decay_data

end HRS.Fp81.S21

end
