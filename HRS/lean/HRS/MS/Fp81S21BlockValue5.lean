import HRS.MS.Fp81S21BlockValue4

/-!
# S2.1(iii), packet 15d-4: gradient-pairing identification

Under both shifted cutoffs, the two finite-combination window features are
exactly the shifted propagated observations. The existing generic `Fm` lemma
then identifies their rank-one covariance form with the gradient pairing.
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

/-- The pointwise window covariance form on the two reconstructed finite
observations equals `2*C.ν` times the shifted gradient pairing. `hlin` is a
separate input because the choice-defined propagator does not store it. -/
theorem fp81s21_windowD_combo_gradient
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (a + H))
    {ta tb : ℝ} (hta : ta ∈ Icc (0 : ℝ) H) (htb : tb ∈ Icc (0 : ℝ) H)
    (hva : v ≤ a + ta) (hvb : v ≤ a + tb)
    (Sa Sb : Finset (MultiIndex d)) (ca cb : MultiIndex d → ℝ) :
    fp81s21_windowD C m H a z v
        (s101Pc m H ta Sa ca + s101Qc m H Sa ca)
        (s101Pc m H tb Sb cb + s101Qc m H Sb cb) =
      2 * C.ν * z v (fun x => inner ℝ
        (gradient (propagatorW C v (a + ta)
          (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x)
        (gradient (propagatorW C v (a + tb)
          (fun y => ∑ α ∈ Sb, cb α * oscTestFun m α y)) x)) := by
  obtain ⟨cData, hdata⟩ := s101_data_of_horb D.fp81s21_hd D.fp81s21_horb
  have hreg := fp81s21_window_feature_contDiff_full_of_data
    D.fp81s21_hd D.fp81s21_hH a D.fp81s21_ha v hv hdata
    (D.fp81s21_hterminal v hv)
  have hΓdiff : Differentiable ℝ (fun x => fp81s21_window_feature C m H a v x) :=
    hreg.1.differentiable (by exact_mod_cast Nat.succ_ne_zero r)
  let Ua := s101Pc m H ta Sa ca + s101Qc m H Sa ca
  let Ub := s101Pc m H tb Sb cb + s101Qc m H Sb cb
  have hUa : ∀ x, inner ℝ (fp81s21_window_feature C m H a v x) Ua =
      propagatorW C v (a + ta)
        (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y) x := by
    intro x
    have h := fp81s21_window_feature_B_cancellation_combo
      D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb
      D.fp81s21_hterminal hlin hv hta Sa ca x
    simpa [Ua, hva] using h
  have hUb : ∀ x, inner ℝ (fp81s21_window_feature C m H a v x) Ub =
      propagatorW C v (a + tb)
        (fun y => ∑ α ∈ Sb, cb α * oscTestFun m α y) x := by
    intro x
    have h := fp81s21_window_feature_B_cancellation_combo
      D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb
      D.fp81s21_hterminal hlin hv htb Sb cb x
    simpa [Ub, hvb] using h
  have hraw := (fp81s21_windowD_data
    D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb
    D.fp81s21_hterminal D.fp81s21_hz D.fp81s21_hP hv
    (D.fp81s21_hPos v hv)).1 Ua Ub
  rw [hraw, s101_Fm_Rk_eq_inner hΓdiff hUa hUb]

#print axioms fp81s21_windowD_combo_gradient

end HRS.Fp81.S21

end
