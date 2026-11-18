import HRS.MS.Fp81S21BlockValue9

/-!
# S2.1(iii), packet 15d-4: raw density to shifted gradients

The raw almost-everywhere specification of the local density, combined with
pointwise B-cancellation, gives the exact physical cutoff integrand on the
unit clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath

/-- Almost everywhere on the unit clock, the localized density on the two
conditional reconstructed observations is the exact shifted gradient
integrand, supported on the block and the intersection of both physical
observation cutoffs. -/
theorem fp81s21_windowLocal_cutoff_gradient_ae
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ)
    {I : Set ℝ} (k : ℕ)
    {ta tb : ℝ} (hta : ta ∈ Icc (0 : ℝ) H) (htb : tb ∈ Icc (0 : ℝ) H)
    (Sa Sb : Finset (MultiIndex d)) (ca cb : MultiIndex d → ℝ) :
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)),
      let v := (k : ℝ) + s
      fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) s
        (s101Pc m H ta Sa ca +
          (if v ≤ a + ta then s101Qc m H Sa ca else 0))
        (s101Pc m H tb Sb cb +
          (if v ≤ a + tb then s101Qc m H Sb cb else 0)) =
      if v ∈ I ∩ Icc (0 : ℝ) (a + H) ∧ v ≤ a + ta ∧ v ≤ a + tb then
        2 * C.ν * z v (fun x => inner ℝ
          (gradient (propagatorW C v (a + ta)
            (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x)
          (gradient (propagatorW C v (a + tb)
            (fun y => ∑ α ∈ Sb, cb α * oscTestFun m α y)) x))
      else 0 := by
  filter_upwards [fp81s21_windowLocal_ae_raw_spec D I k, ae_restrict_mem measurableSet_Icc] with s hs hs01
  dsimp
  let v := (k : ℝ) + s
  let Ua := s101Pc m H ta Sa ca +
    (if v ≤ a + ta then s101Qc m H Sa ca else 0)
  let Ub := s101Pc m H tb Sb cb +
    (if v ≤ a + tb then s101Qc m H Sb cb else 0)
  have hraw := hs Ua Ub
  have hlocal := fp81s21_windowLocalD_apply I k C m H a z D.fp81s21_ha
    (le_of_lt D.fp81s21_hH) s Ua Ub
  by_cases hloc : v ∈ I ∩ Icc (0 : ℝ) (a + H)
  · have hv : v ∈ Icc (0 : ℝ) (a + H) := hloc.2
    have hgrad := fp81s21_windowD_combo_gradient_cutoff D hlin hv hta htb Sa Sb ca cb
    have hwindow := (fp81s21_windowD_data
      D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb
      D.fp81s21_hterminal D.fp81s21_hz D.fp81s21_hP hv
      (D.fp81s21_hPos v hv)).1 Ua Ub
    have hloc' : (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H) := by
      simpa [v] using hloc
    rw [hraw]
    simp only [if_pos hloc']
    rw [← hwindow, hgrad]
    simp [hloc, v]
  · rw [hlocal]
    simp [hs01, v, hloc]

#print axioms fp81s21_windowLocal_cutoff_gradient_ae

end HRS.Fp81.S21

end
