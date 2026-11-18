import HRS.MS.Fp81S21WindowFeature14

/-!
# S2.1 packet 15c: deriving the trace package from wR33

This final wrapper obtains the trajectory-dependent amplitudes and decay rate
directly from the common moving-orbit theorem, then fixes them before the
observation window and noise time.
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

/-- End-to-end positive trace package for an observation window.  The
trajectory constants come from wR33 and are quantified before `a` and `v`;
the returned feature amplitude is exactly the bound consumed by packet 15d. -/
theorem fp81s21_window_feature_trace_bound_pos_from_wR33
    (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁,
      ∃ Cs0 cdec Cmix : ℝ,
        0 ≤ Cs0 ∧ 0 < cdec ∧ Summable (s104_b p.d) ∧
        0 ≤ Cmix ∧ Cs0 ≤ Cmix ∧
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
  obtain ⟨δ0, hδ0, hδ0half, hdecayAll⟩ :=
    fp81s21_moving_observation_window_orbit_decay p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hterm
  obtain ⟨Cs0, cdec, hCs0, hcdec, hsumb, _, hdecayRaw⟩ :=
    hdecayAll δ hδ hδle R
  have hdecay : fp81s21_WindowOrbitDecay p R Cs0 cdec := by
    dsimp [fp81s21_WindowOrbitDecay]
    exact hdecayRaw
  obtain ⟨Cmix, hmix0, hmixCs, htrace⟩ :=
    fp81s21_window_feature_trace_bound_pos_of_decay_data
      p R hterm hCs0 hcdec hsumb hdecay
  exact ⟨Cs0, cdec, Cmix, hCs0, hcdec, hsumb,
    hmix0, hmixCs, htrace⟩

#print axioms fp81s21_window_feature_trace_bound_pos_from_wR33

end HRS.Fp81.S21

end
