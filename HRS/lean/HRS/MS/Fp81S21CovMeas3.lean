import HRS.MS.Fp81S21CovMeas2

/-!
# S2.1(iii), packet 16a: set laws for covariance block values

The set-additivity statement allows an overlap of measure zero, so it covers
both disjoint measurable sets and interval conventions that differ at a
shared endpoint. The null-set congruence is stated for measurable sets whose
symmetric difference is Lebesgue null.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators symmDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas

/-- Block values are linear for a linear combination of fields whenever the
localized input for the resulting field is available. -/
theorem fp81s21_blockValue_add_smul
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P c : ℝ}
    {z z' : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (D' : fp81s21_WindowLocalInput C m H a r P z' Cmix cdec)
    (hmeasNorm : AEMeasurable
      (fun u => dualNormE r P (z u)) (volume.restrict (Icc (0 : ℝ) (a + H))))
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    fp81s21_blockValue
        (fp81s21_windowLocalInput_add_of_aemeasurable_dualNorm
          D (fp81s21_windowLocalInput_smul D' c) hmeasNorm) I k =
      fp81s21_blockValue D I k + c • fp81s21_blockValue D' I k := by
  let Dsmul := fp81s21_windowLocalInput_smul D' c
  let Dcomb := fp81s21_windowLocalInput_add_of_aemeasurable_dualNorm
    D Dsmul hmeasNorm
  calc
    fp81s21_blockValue Dcomb I k =
        fp81s21_blockValue D I k + fp81s21_blockValue Dsmul I k :=
      fp81s21_blockValue_add D Dsmul Dcomb hI k
    _ = fp81s21_blockValue D I k + c • fp81s21_blockValue D' I k := by
      rw [fp81s21_blockValue_smul D' Dsmul hI k]

/-- Physical scalar closure immediately transfers to the covariance block
value without a separately supplied scaled input. -/
theorem fp81s21_blockValue_smul_auto
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P c : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    fp81s21_blockValue (fp81s21_windowLocalInput_smul D c) I k =
      c • fp81s21_blockValue D I k := by
  exact fp81s21_blockValue_smul D
    (fp81s21_windowLocalInput_smul D c) hI k

/-- Localized unit-clock densities for a union agree almost everywhere with
the sum of the two densities when the physical overlap is null. -/
private theorem fp81s21_windowLocalD_union_ae
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I I' : Set ℝ} (hOverlap : volume (I ∩ I') = 0) (k : ℕ) :
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)),
      fp81s21_windowLocalD (I ∪ I') k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s =
        fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s +
        fp81s21_windowLocalD I' k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s := by
  let J : Set ℝ := Icc (k : ℝ) ((k : ℝ) + 1)
  have hae : ∀ᵐ v ∂volume, v ∉ I ∩ I' := by
    rw [ae_iff]
    simpa using hOverlap
  have hblock : ∀ᵐ v ∂(volume.restrict J), v ∉ I ∩ I' := by
    rw [ae_restrict_iff' (by simp [J] : MeasurableSet J)]
    filter_upwards [hae] with v hv hJ
    exact hv
  have hunit := (fp81s21_window_shift_measurePreserving (k : ℝ) 1).quasiMeasurePreserving.ae hblock
  filter_upwards [hunit, ae_restrict_mem measurableSet_Icc] with s hsnot hs
  by_cases ht : (k : ℝ) + s ∈ Icc (0 : ℝ) (a + H)
  · by_cases hI : (k : ℝ) + s ∈ I
    · have hI' : (k : ℝ) + s ∉ I' := by
        intro h
        exact hsnot ⟨hI, h⟩
      ext u v
      simp only [add_apply, fp81s21_windowLocalD_apply]
      simp [hs, ht, hI, hI']
    · by_cases hI' : (k : ℝ) + s ∈ I'
      · ext u v
        simp only [add_apply, fp81s21_windowLocalD_apply]
        simp [hs, ht, hI, hI']
      · ext u v
        simp only [add_apply, fp81s21_windowLocalD_apply]
        simp [hs, ht, hI, hI']
  · ext u v
    simp only [add_apply, fp81s21_windowLocalD_apply]
    simp [hs, ht]

/-- A measurable-set union has additive covariance block value whenever the
overlap has measure zero. In particular, this includes the shared-endpoint
case for interval conventions such as `Ioc` and `Icc`. -/
theorem fp81s21_blockValue_union
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I I' : Set ℝ} (hI : MeasurableSet I) (hI' : MeasurableSet I')
    (hOverlap : volume (I ∩ I') = 0) (k : ℕ) :
    fp81s21_blockValue D (I ∪ I') k =
      fp81s21_blockValue D I k + fp81s21_blockValue D I' k := by
  let Dloc : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD I k C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH) s
  let Dloc' : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD I' k C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH) s
  let DlocUnion : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD (I ∪ I') k C m H a z D.fp81s21_ha
      (le_of_lt D.fp81s21_hH) s
  let DlocPair : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    (1 : ℝ) • Dloc s + (1 : ℝ) • Dloc' s
  let Q := fp81s21_blockCovariance (KSpace d m H)
  let Rc := fp81s21_blockRecon (d := d) (m := m)
    (le_of_lt D.fp81s21_hH) a k
  have htrace : IsTraceDensityL1 1 Dloc :=
    fp81s21_windowLocal_isTraceDensityL1 D hI k
  have htrace' : IsTraceDensityL1 1 Dloc' :=
    fp81s21_windowLocal_isTraceDensityL1 D hI' k
  have htraceUnion : IsTraceDensityL1 1 DlocUnion :=
    fp81s21_windowLocal_isTraceDensityL1 D (hI.union hI') k
  have htracePair : IsTraceDensityL1 1 DlocPair := by
    have hlin := HRS.Uniform.Q45.isTraceDensityL1_lin
      htrace htrace' (1 : ℝ) 1
    simpa [DlocPair] using hlin
  have hlocal : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)),
      DlocUnion s = DlocPair s := by
    have htranslated := fp81s21_windowLocalD_union_ae D hOverlap k
    simpa only [DlocUnion, Dloc, Dloc', DlocPair, one_smul] using htranslated
  have hQcongr := fp81s21_unitCov_congr
    (fp81s21_blockCovariance_props (KSpace d m H))
    htraceUnion htracePair hlocal (I := Icc (0 : ℝ) 1) measurableSet_Icc
  have hQlin := (fp81s21_blockCovariance_props (KSpace d m H)).lin
    Dloc Dloc' htrace htrace' (1 : ℝ) 1 (Icc (0 : ℝ) 1) measurableSet_Icc
  have hQlin' : Q DlocPair (Icc (0 : ℝ) 1) =
      Q Dloc (Icc (0 : ℝ) 1) + Q Dloc' (Icc (0 : ℝ) 1) := by
    simpa [DlocPair, Q] using hQlin
  apply Subtype.ext
  change fp81s21_blockPsi Rc (Q DlocUnion (Icc (0 : ℝ) 1)) =
    fp81s21_blockPsi Rc (Q Dloc (Icc (0 : ℝ) 1)) +
      fp81s21_blockPsi Rc (Q Dloc' (Icc (0 : ℝ) 1))
  rw [hQcongr, hQlin']
  exact fp81s21_blockPsi_add Rc _ _

/-- Changing a measurable physical set on a Lebesgue-null symmetric
 difference leaves its localized covariance block value unchanged. -/
theorem fp81s21_blockValue_congr_null
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I I' : Set ℝ} (hI : MeasurableSet I) (hI' : MeasurableSet I')
    (hnull : volume (I ∆ I') = 0) (k : ℕ) :
    fp81s21_blockValue D I k = fp81s21_blockValue D I' k := by
  let Dloc : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD I k C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH) s
  let Dloc' : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD I' k C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH) s
  let J : Set ℝ := Icc (k : ℝ) ((k : ℝ) + 1)
  let Q := fp81s21_blockCovariance (KSpace d m H)
  let Rc := fp81s21_blockRecon (d := d) (m := m)
    (le_of_lt D.fp81s21_hH) a k
  have hae : ∀ᵐ v ∂volume, v ∉ I ∆ I' := by
    rw [ae_iff]
    simpa using hnull
  have hblock : ∀ᵐ v ∂(volume.restrict J), v ∉ I ∆ I' := by
    rw [ae_restrict_iff' (by simp [J] : MeasurableSet J)]
    filter_upwards [hae] with v hv hJ
    exact hv
  have hunit := (fp81s21_window_shift_measurePreserving (k : ℝ) 1).quasiMeasurePreserving.ae hblock
  have hlocal : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)), Dloc s = Dloc' s := by
    filter_upwards [hunit, ae_restrict_mem measurableSet_Icc] with s hsnull hsClock
    have hset : ((k : ℝ) + s ∈ I) ↔ ((k : ℝ) + s ∈ I') := by
      constructor
      · intro hmem
        by_contra hnot
        exact hsnull (Set.mem_symmDiff.mpr (Or.inl ⟨hmem, hnot⟩))
      · intro hmem
        by_contra hnot
        exact hsnull (Set.mem_symmDiff.mpr (Or.inr ⟨hmem, hnot⟩))
    simp [Dloc, Dloc', fp81s21_windowLocalD, hsClock, hset]
  have htrace : IsTraceDensityL1 1 Dloc :=
    fp81s21_windowLocal_isTraceDensityL1 D hI k
  have htrace' : IsTraceDensityL1 1 Dloc' :=
    fp81s21_windowLocal_isTraceDensityL1 D hI' k
  have hQcongr := fp81s21_unitCov_congr
    (fp81s21_blockCovariance_props (KSpace d m H))
    htrace htrace' hlocal (I := Icc (0 : ℝ) 1) measurableSet_Icc
  apply Subtype.ext
  change fp81s21_blockPsi Rc (Q Dloc (Icc (0 : ℝ) 1)) =
    fp81s21_blockPsi Rc (Q Dloc' (Icc (0 : ℝ) 1))
  rw [hQcongr]

#print axioms fp81s21_blockValue_add_smul
#print axioms fp81s21_blockValue_smul_auto
#print axioms fp81s21_blockValue_union
#print axioms fp81s21_blockValue_congr_null

end HRS.Fp81.S21

end
