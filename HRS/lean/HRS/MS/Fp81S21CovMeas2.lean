import HRS.MS.Fp81S21CovMeas

/-!
# S2.1(iii), packet 16a: linearity of physical block values

These statements use explicit localized inputs for the resulting field. This
keeps the mathematical contract honest while full addition closure of
`IsR2L1F` remains conditional on dual-norm measurability.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas

/-- Localized covariance block values add when localized inputs for both
summands and their sum are supplied. -/
theorem fp81s21_blockValue_add
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z z' : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (D' : fp81s21_WindowLocalInput C m H a r P z' Cmix cdec)
    (Dsum : fp81s21_WindowLocalInput C m H a r P (z + z') Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    fp81s21_blockValue Dsum I k = fp81s21_blockValue D I k + fp81s21_blockValue D' I k := by
  let Dloc : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD I k C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH) s
  let Dloc' : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD I k C m H a z' D'.fp81s21_ha (le_of_lt D'.fp81s21_hH) s
  let DlocSum : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD I k C m H a (z + z') Dsum.fp81s21_ha
      (le_of_lt Dsum.fp81s21_hH) s
  let DlocPair : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    (1 : ℝ) • Dloc s + (1 : ℝ) • Dloc' s
  let Q := fp81s21_blockCovariance (KSpace d m H)
  let Rc := fp81s21_blockRecon (d := d) (m := m)
    (le_of_lt D.fp81s21_hH) a k
  have hA : S101Adm C m (a + H) r P z :=
    ⟨D.fp81s21_hd, D.fp81s21_hP, D.fp81s21_horb,
      D.fp81s21_hz.1, D.fp81s21_hm⟩
  have hA' : S101Adm C m (a + H) r P z' :=
    ⟨D'.fp81s21_hd, D'.fp81s21_hP, D'.fp81s21_horb,
      D'.fp81s21_hz.1, D'.fp81s21_hm⟩
  have hlocAdd := fp81s21_windowLocal_add_ae hA hA'
    D.fp81s21_ha D.fp81s21_hH I k
  have htrace : IsTraceDensityL1 1 Dloc :=
    fp81s21_windowLocal_isTraceDensityL1 D hI k
  have htrace' : IsTraceDensityL1 1 Dloc' :=
    fp81s21_windowLocal_isTraceDensityL1 D' hI k
  have htraceSum : IsTraceDensityL1 1 DlocSum :=
    fp81s21_windowLocal_isTraceDensityL1 Dsum hI k
  have htracePair : IsTraceDensityL1 1 DlocPair := by
    have hlin := HRS.Uniform.Q45.isTraceDensityL1_lin
      htrace htrace' (1 : ℝ) 1
    simpa [DlocPair, zero_smul] using hlin
  have hlocAdd' : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)),
      DlocSum s = DlocPair s := by
    filter_upwards [hlocAdd] with s hs
    simpa [DlocSum, DlocPair, one_smul] using hs
  have hQcongr := fp81s21_unitCov_congr (fp81s21_blockCovariance_props (KSpace d m H))
    htraceSum htracePair hlocAdd' (I := Icc (0 : ℝ) 1) measurableSet_Icc
  have hQlin := (fp81s21_blockCovariance_props (KSpace d m H)).lin
    Dloc Dloc' htrace htrace' 1 1 (Icc (0 : ℝ) 1) measurableSet_Icc
  apply Subtype.ext
  change fp81s21_blockPsi Rc (Q DlocSum (Icc (0 : ℝ) 1)) =
    fp81s21_blockPsi Rc (Q Dloc (Icc (0 : ℝ) 1)) +
      fp81s21_blockPsi Rc (Q Dloc' (Icc (0 : ℝ) 1))
  rw [hQcongr]
  have hQlin' : Q (fun s => Dloc s + Dloc' s) (Icc (0 : ℝ) 1) =
      Q Dloc (Icc (0 : ℝ) 1) + Q Dloc' (Icc (0 : ℝ) 1) := by
    simpa [Q] using hQlin
  have hQlin'' : Q DlocPair (Icc (0 : ℝ) 1) =
      Q Dloc (Icc (0 : ℝ) 1) + Q Dloc' (Icc (0 : ℝ) 1) := by
    simpa [DlocPair, Q, zero_smul] using hQlin
  change fp81s21_blockPsi Rc (Q DlocPair (Icc (0 : ℝ) 1)) = _
  rw [hQlin'']
  exact fp81s21_blockPsi_add Rc _ _

/-- Localized covariance block values scale when localized inputs for the
original and scaled fields are supplied. -/
theorem fp81s21_blockValue_smul
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P c : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (Dsmul : fp81s21_WindowLocalInput C m H a r P (c • z) Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    fp81s21_blockValue Dsmul I k = c • fp81s21_blockValue D I k := by
  let Dloc : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD I k C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH) s
  let DlocSmul : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD I k C m H a (c • z) Dsmul.fp81s21_ha
      (le_of_lt Dsmul.fp81s21_hH) s
  let DlocPair : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    c • Dloc s + (0 : ℝ) • Dloc s
  let Q := fp81s21_blockCovariance (KSpace d m H)
  let Rc := fp81s21_blockRecon (d := d) (m := m)
    (le_of_lt D.fp81s21_hH) a k
  have hA : S101Adm C m (a + H) r P z :=
    ⟨D.fp81s21_hd, D.fp81s21_hP, D.fp81s21_horb,
      D.fp81s21_hz.1, D.fp81s21_hm⟩
  have hlocSmul := fp81s21_windowLocal_smul_ae hA
    D.fp81s21_ha D.fp81s21_hH c I k
  have htrace : IsTraceDensityL1 1 Dloc :=
    fp81s21_windowLocal_isTraceDensityL1 D hI k
  have htraceSmul : IsTraceDensityL1 1 DlocSmul :=
    fp81s21_windowLocal_isTraceDensityL1 Dsmul hI k
  have htracePair : IsTraceDensityL1 1 DlocPair := by
    have hlin := HRS.Uniform.Q45.isTraceDensityL1_lin
      htrace htrace (c : ℝ) 0
    change IsTraceDensityL1 1 (fun s => c • Dloc s + (0 : ℝ) • Dloc s)
    exact hlin
  have hlocSmul' : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)),
      DlocSmul s = DlocPair s := by
    filter_upwards [hlocSmul] with s hs
    have hs' : DlocSmul s = c • Dloc s := by
      simpa [DlocSmul, Dloc, Pi.smul_apply] using hs
    calc
      DlocSmul s = c • Dloc s := hs'
      _ = DlocPair s := by
        ext u v
        simp only [DlocPair, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]
        ring
  have hQcongr := fp81s21_unitCov_congr (fp81s21_blockCovariance_props (KSpace d m H))
    htraceSmul htracePair hlocSmul' (I := Icc (0 : ℝ) 1) measurableSet_Icc
  have hQlin := (fp81s21_blockCovariance_props (KSpace d m H)).lin
    Dloc Dloc htrace htrace c 0 (Icc (0 : ℝ) 1) measurableSet_Icc
  apply Subtype.ext
  change fp81s21_blockPsi Rc (Q DlocSmul (Icc (0 : ℝ) 1)) =
    c • fp81s21_blockPsi Rc (Q Dloc (Icc (0 : ℝ) 1))
  rw [hQcongr]
  have hQlin' : Q DlocPair (Icc (0 : ℝ) 1) =
      c • Q Dloc (Icc (0 : ℝ) 1) + (0 : ℝ) • Q Dloc (Icc (0 : ℝ) 1) := by
    change Q (fun s => c • Dloc s + (0 : ℝ) • Dloc s) (Icc (0 : ℝ) 1) = _
    exact hQlin
  change fp81s21_blockPsi Rc (Q DlocPair (Icc (0 : ℝ) 1)) = _
  rw [hQlin']
  calc
    fp81s21_blockPsi Rc
        (c • Q Dloc (Icc (0 : ℝ) 1) + (0 : ℝ) • Q Dloc (Icc (0 : ℝ) 1)) =
        fp81s21_blockPsi Rc (c • Q Dloc (Icc (0 : ℝ) 1)) +
          fp81s21_blockPsi Rc ((0 : ℝ) • Q Dloc (Icc (0 : ℝ) 1)) :=
      fp81s21_blockPsi_add Rc _ _
    _ = c • fp81s21_blockPsi Rc (Q Dloc (Icc (0 : ℝ) 1)) +
        (0 : ℝ) • fp81s21_blockPsi Rc (Q Dloc (Icc (0 : ℝ) 1)) := by
      rw [fp81s21_blockPsi_smul Rc c _, fp81s21_blockPsi_smul Rc 0 _]
    _ = c • fp81s21_blockPsi Rc (Q Dloc (Icc (0 : ℝ) 1)) := by
      ext M
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
      ring

#print axioms fp81s21_blockValue_add
#print axioms fp81s21_blockValue_smul

end HRS.Fp81.S21

end
