import HRS.MS.Fp81S21WindowFeature12

/-!
# S2.1 packet 15c: exponential positive-order feature bound

This specializes the coordinate estimate to the wR33 trajectory constants.
The feature multiplier depends on dimension and window length, while the
trajectory amplitudes and decay rate are fixed before the window start and
noise time.
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

/-- The feature-level version of `fp81s21_window_Bpos`; the extra factor is
the contribution of the two endpoint slots and the L² middle slot. -/
def fp81s21_window_feature_Bpos (d r : ℕ) (H Cs0 cdec a v : ℝ) : ℝ :=
  (2 + (d : ℝ) ^ (r + 1) *
      ((volume.restrict (Icc (0 : ℝ) H)) Set.univ).toReal ^ (1 / 2 : ℝ)) *
    fp81s21_window_Bpos d Cs0 cdec a v

/-- Moving-orbit decay gives the positive-order feature bound required by the
trace estimate.  The constants are fixed by the trajectory before `a` and `v`;
`hD` supplies only the qualitative S101 envelope needed for regularity. -/
theorem fp81s21_window_feature_hpos_of_decay_data
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
        ∀ j : ℕ, 1 ≤ j → j ≤ 2 * p.d + 9 → ∀ x : Euc p.d,
          ‖iteratedFDeriv ℝ j
            (fp81s21_window_feature (r26t3_coeff R)
              (wholeSpaceIndex p.d : ℝ) p.T a v) x‖ ≤
            fp81s21_window_feature_Bpos p.d (2 * p.d + 8) p.T
              Cmix cdec a v := by
  obtain ⟨Cmix, hmix0, hmixCs, hcoord⟩ :=
    fp81s21_window_coordinate_pos_bounds p R hterm hCs0 hcdec hdecay
  refine ⟨Cmix, hmix0, hmixCs, ?_⟩
  intro a ha v hv c hD j hj1 hjk x
  let m : ℝ := wholeSpaceIndex p.d
  let r : ℕ := 2 * p.d + 8
  let q : MultiIndex p.d → ℝ := fun α =>
    Cmix * s104_b p.d α * Real.exp (-cdec * max (a - v) 0)
  have hAmp := fp81s21_window_orbit_amplitude_sq_sum (d := p.d)
    Cmix cdec a v hmix0 hsumb
  have hqq : Summable (fun α : MultiIndex p.d => q α ^ 2) := by
    simpa [q] using hAmp.2.1
  have horb : ∀ α : MultiIndex p.d,
      S104nOrbit (r26t3_coeff R)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) (a + p.T) := by
    intro α
    exact s104b_orbit_of_termRegGen hterm R.admissible R.resulting α
      (a + p.T) (by linarith [ha, p.hT.le])
  have hterminal : ∀ α : MultiIndex p.d, ∀ y : Euc p.d,
      propagatorW (r26t3_coeff R) v v
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) y =
          oscTestFun (wholeSpaceIndex p.d : ℝ) α y := by
    intro α y
    have hclass := HRS.MS.Fcau.propagatorW_isClassical
      ((horb α).ex0 v hv)
    simpa using congrFun hclass.terminal y
  have hparts := hcoord a ha v hv
  have hApos : ∀ α : MultiIndex p.d, ∀ j ≤ r + 1, 1 ≤ j → ∀ y,
      ‖iteratedFDeriv ℝ j (fun y => if v ≤ a then
        propagatorW (r26t3_coeff R) v a
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α) y
        else oscTestFun (wholeSpaceIndex p.d : ℝ) α y) y‖ ≤ q α := by
    intro α j hj hj1 y
    have h := (hparts α).1 j hj1 (by simpa [r] using hj) y
    simpa [q, m, r] using h
  have hDpos : ∀ t ∈ Icc (0 : ℝ) p.T, ∀ α : MultiIndex p.d,
      ∀ j ≤ r + 1, 1 ≤ j → ∀ y,
        ‖iteratedFDeriv ℝ j (fun y => if v < a + t then
          s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
            (a + p.T) v (a + t) α y else 0) y‖ ≤ q α := by
    intro t ht α j hj hj1 y
    have h := ((hparts α).2.1 t ht) j hj1 (by simpa [r] using hj) y
    simpa [q, m, r] using h
  have hBpos : ∀ α : MultiIndex p.d, ∀ j ≤ r + 1, 1 ≤ j → ∀ y,
      ‖iteratedFDeriv ℝ j (fun y => if a < v then
        oscTestFun (wholeSpaceIndex p.d : ℝ) α y else 0) y‖ ≤ q α := by
    intro α j hj hj1 y
    have h := ((hparts α).2.2) j hj1 (by simpa [r] using hj) y
    simpa [q, m, r] using h
  have hfeature := fp81s21_window_feature_pos_of_coordinate_bounds
    (d := p.d) (C := r26t3_coeff R) (m := m) (H := p.T) (a := a) (v := v)
    (r := r) (c := c) (q := q) (le_trans (by norm_num) p.hd) p.hT ha hv hD
    hterminal hqq hApos hBpos hDpos
  have hQ : Real.sqrt (∑' α : MultiIndex p.d, q α ^ 2) =
      fp81s21_window_Bpos p.d Cmix cdec a v := by
    rw [hAmp.2.2, Real.sqrt_sq_eq_abs, abs_of_nonneg hAmp.1]
  have hres := hfeature.2 j (by simpa [r] using hjk) hj1 x
  have hcoef : 0 ≤ (2 + (p.d : ℝ) ^ (r + 1) *
      ((volume.restrict (Icc (0 : ℝ) p.T)) Set.univ).toReal ^
        (1 / 2 : ℝ)) := by positivity
  have hout := hres.trans_eq (congrArg
    (fun z : ℝ => (2 + (p.d : ℝ) ^ (r + 1) *
      ((volume.restrict (Icc (0 : ℝ) p.T)) Set.univ).toReal ^
        (1 / 2 : ℝ)) * z) hQ)
  simpa [fp81s21_window_feature_Bpos, r] using hout

#print axioms fp81s21_window_feature_hpos_of_decay_data

end HRS.Fp81.S21

end
