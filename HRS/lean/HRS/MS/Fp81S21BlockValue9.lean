import HRS.MS.Fp81S21BlockValue8

/-!
# S2.1(iii), packet 15d-4: pointwise cutoff evaluation

This records the covariance form with the two clipped observation cutoffs.
Outside their common active region the reconstructed feature cancels, so the
form vanishes; on the common region it is the shifted gradient pairing.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath

variable {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
variable {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}

/-- The window covariance form on conditionally clipped finite observations
is zero unless both physical observation cutoffs are active, and on their
intersection it equals the shifted gradient pairing. The propagator
linearity assumption remains an explicit input. -/
theorem fp81s21_windowD_combo_gradient_cutoff
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (a + H))
    {ta tb : ℝ} (hta : ta ∈ Icc (0 : ℝ) H) (htb : tb ∈ Icc (0 : ℝ) H)
    (Sa Sb : Finset (MultiIndex d)) (ca cb : MultiIndex d → ℝ) :
    fp81s21_windowD C m H a z v
        (s101Pc m H ta Sa ca +
          (if v ≤ a + ta then s101Qc m H Sa ca else 0))
        (s101Pc m H tb Sb cb +
          (if v ≤ a + tb then s101Qc m H Sb cb else 0)) =
      if v ≤ a + ta ∧ v ≤ a + tb then
        2 * C.ν * z v (fun x => inner ℝ
          (gradient (propagatorW C v (a + ta)
            (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x)
          (gradient (propagatorW C v (a + tb)
            (fun y => ∑ α ∈ Sb, cb α * oscTestFun m α y)) x))
      else 0 := by
  classical
  obtain ⟨cData, hdata⟩ := s101_data_of_horb D.fp81s21_hd D.fp81s21_horb
  have hreg := fp81s21_window_feature_contDiff_full_of_data
    D.fp81s21_hd D.fp81s21_hH a D.fp81s21_ha v hv hdata
    (D.fp81s21_hterminal v hv)
  have hΓdiff : Differentiable ℝ (fun x => fp81s21_window_feature C m H a v x) :=
    hreg.1.differentiable (by exact_mod_cast Nat.succ_ne_zero r)
  let Γ := fp81s21_window_feature C m H a v
  let Ua := s101Pc m H ta Sa ca +
    (if v ≤ a + ta then s101Qc m H Sa ca else 0)
  let Ub := s101Pc m H tb Sb cb +
    (if v ≤ a + tb then s101Qc m H Sb cb else 0)
  have hUa : ∀ x, inner ℝ (Γ x) Ua =
      if v ≤ a + ta then
        propagatorW C v (a + ta)
          (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y) x
      else 0 := by
    intro x
    have h := fp81s21_window_feature_B_cancellation_combo
      D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb
      D.fp81s21_hterminal hlin hv hta Sa ca x
    simpa [Γ, Ua] using h
  have hUb : ∀ x, inner ℝ (Γ x) Ub =
      if v ≤ a + tb then
        propagatorW C v (a + tb)
          (fun y => ∑ α ∈ Sb, cb α * oscTestFun m α y) x
      else 0 := by
    intro x
    have h := fp81s21_window_feature_B_cancellation_combo
      D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb
      D.fp81s21_hterminal hlin hv htb Sb cb x
    simpa [Γ, Ub] using h
  have hraw := (fp81s21_windowD_data
    D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb
    D.fp81s21_hterminal D.fp81s21_hz D.fp81s21_hP hv
    (D.fp81s21_hPos v hv)).1 Ua Ub
  have hzero_test : IsR2WeightedTest r P (fun _ : Euc d => 0) :=
    ⟨contDiff_const, HRS.MS.FixEq.s57p_E_zero_fun D.fp81s21_hP⟩
  have hzero : z v (fun _ : Euc d => 0) = 0 := by
    have hlin0 := ((D.fp81s21_hz).1 v hv).1
      (fun _ : Euc d => 0) (fun _ : Euc d => 0) hzero_test hzero_test
    have hsumzero :
        (fun _ : Euc d => (0 : ℝ)) + (fun _ : Euc d => 0) =
          (fun _ : Euc d => 0) := by
      funext x
      simp
    rw [hsumzero] at hlin0
    have heq : z v (fun _ : Euc d => 0) =
        z v (fun _ : Euc d => 0) + z v (fun _ : Euc d => 0) := hlin0
    linarith
  rw [hraw, s101_Fm_Rk_eq_inner hΓdiff hUa hUb]
  by_cases hA : v ≤ a + ta <;> by_cases hB : v ≤ a + tb <;>
    simp [hA, hB, hzero]

#print axioms fp81s21_windowD_combo_gradient_cutoff

end HRS.Fp81.S21

end
