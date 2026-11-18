import HRS.MS.Fp81S21CovBlockAPI

/-!
# S2.1(iii), packet 16a: covariance-field closure

Scalar closure follows from the displayed dual-norm scaling bound. Addition
uses the dual-norm triangle inequality, and its integral step explicitly
requires almost-everywhere measurability of one summand's dual-norm function.
That measurability is not part of `IsR2L1F` or `WindowLocalInput`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.R2WinErr

/-- The dual norm is subadditive on the full function space used by its
definition. -/
lemma fp81s21_dualNormE_add_le {d r : ℕ} {P : ℝ}
    (η η' : (Euc d → ℝ) → ℝ) :
    dualNormE r P (fun f => η f + η' f) ≤ dualNormE r P η + dualNormE r P η' := by
  unfold dualNormE
  refine iSup_le fun f => iSup_le fun hf => ?_
  have hnum : ENNReal.ofReal |η f + η' f| ≤
      ENNReal.ofReal |η f| + ENNReal.ofReal |η' f| := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
  have hratio :
      ENNReal.ofReal |η f + η' f| / weightedSobolevE r P f ≤
        ENNReal.ofReal |η f| / weightedSobolevE r P f +
          ENNReal.ofReal |η' f| / weightedSobolevE r P f := by
    calc
      _ ≤ (ENNReal.ofReal |η f| + ENNReal.ofReal |η' f|) /
          weightedSobolevE r P f :=
        ENNReal.div_le_div_right hnum (weightedSobolevE r P f)
      _ = _ := ENNReal.add_div
  exact hratio.trans (add_le_add
    (le_iSup₂_of_le f hf le_rfl)
    (le_iSup₂_of_le f hf le_rfl))

/-- Addition closure for `IsR2L1F` when the first density's dual-norm
function is a.e. measurable. This side condition is used only to apply
`lintegral_add_left'`; pointwise norm subadditivity alone does not justify
the integral step. -/
theorem fp81s21_IsR2L1F_add_of_aemeasurable_dualNorm
    {d r : ℕ} {P T : ℝ} {z z' : ℝ → (Euc d → ℝ) → ℝ}
    (hz : IsR2L1F r P T z) (hz' : IsR2L1F r P T z')
    (hmeasNorm : AEMeasurable
      (fun u => dualNormE r P (z u)) (volume.restrict (Icc (0 : ℝ) T))) :
    IsR2L1F r P T (z + z') := by
  unfold IsR2L1F at hz hz' ⊢
  rcases hz with ⟨hzlin, hzmeas, hzint⟩
  rcases hz' with ⟨hz'lin, hz'meas, hz'int⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨hadd, hsmul, M, hM⟩ := hzlin u hu
    obtain ⟨hadd', hsmul', M', hM'⟩ := hz'lin u hu
    refine ⟨?_, ?_, M + M', ?_⟩
    · intro f g hf hg
      simp only [Pi.add_apply]
      rw [hadd f g hf hg, hadd' f g hf hg]
      ring
    · intro c f hf
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsmul c f hf, hsmul' c f hf]
      ring
    · intro f hf
      simp only [Pi.add_apply]
      calc
        |z u f + z' u f| ≤ |z u f| + |z' u f| := abs_add_le _ _
        _ ≤ M * (weightedSobolevE r P f).toReal +
            M' * (weightedSobolevE r P f).toReal := add_le_add (hM f hf) (hM' f hf)
        _ = (M + M') * (weightedSobolevE r P f).toReal := by ring
  · intro f hf
    change Measurable (fun u : ℝ => z u f + z' u f)
    exact (hzmeas f hf).add (hz'meas f hf)
  · have htriangle : ∀ u,
        dualNormE r P ((z + z') u) ≤ dualNormE r P (z u) + dualNormE r P (z' u) := by
      intro u
      change dualNormE r P (fun f => z u f + z' u f) ≤ _
      exact fp81s21_dualNormE_add_le (z u) (z' u)
    apply lt_of_le_of_lt ?_ (ENNReal.add_lt_top.mpr ⟨hzint, hz'int⟩)
    calc
      (∫⁻ u in Icc (0 : ℝ) T, dualNormE r P ((z + z') u)) ≤
          ∫⁻ u in Icc (0 : ℝ) T,
            dualNormE r P (z u) + dualNormE r P (z' u) :=
        setLIntegral_mono' measurableSet_Icc (fun u _ => htriangle u)
      _ = (∫⁻ u in Icc (0 : ℝ) T, dualNormE r P (z u)) +
          ∫⁻ u in Icc (0 : ℝ) T, dualNormE r P (z' u) := by
        rw [lintegral_add_left' hmeasNorm]

/-- Scalar closure of `IsR2L1F`, with no extra measurability hypothesis. -/
theorem fp81s21_IsR2L1F_smul
    {d r : ℕ} {P T c : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ}
    (hz : IsR2L1F r P T z) : IsR2L1F r P T (c • z) := by
  unfold IsR2L1F at hz ⊢
  rcases hz with ⟨hzlin, hzmeas, hzint⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨hadd, hsmul, M, hM⟩ := hzlin u hu
    refine ⟨?_, ?_, |c| * |M|, ?_⟩
    · intro f g hf hg
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hadd f g hf hg]
      ring
    · intro b f hf
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hsmul b f hf]
      ring
    · intro f hf
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        |c * z u f| = |c| * |z u f| := abs_mul _ _
        _ ≤ |c| * (M * (weightedSobolevE r P f).toReal) :=
          mul_le_mul_of_nonneg_left (hM f hf) (abs_nonneg _)
        _ ≤ |c| * (|M| * (weightedSobolevE r P f).toReal) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg)
            (abs_nonneg _)
        _ = (|c| * |M|) * (weightedSobolevE r P f).toReal := by ring
  · intro f hf
    simpa only [Pi.smul_apply, smul_eq_mul] using (hzmeas f hf).const_mul c
  · have hbound : ∀ u,
        dualNormE r P ((c • z) u) ≤ ENNReal.ofReal |c| * dualNormE r P (z u) := by
      intro u
      change dualNormE r P (fun f => c * z u f) ≤ _
      exact s101_dualNormE_smul_le (r := r) (P := P) c (z u)
    have hconst : ENNReal.ofReal |c| < ⊤ := ENNReal.ofReal_lt_top
    apply lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hconst hzint)
    calc
      (∫⁻ u in Icc (0 : ℝ) T, dualNormE r P ((c • z) u)) ≤
          ∫⁻ u in Icc (0 : ℝ) T, ENNReal.ofReal |c| * dualNormE r P (z u) :=
        setLIntegral_mono' measurableSet_Icc (fun u _ => hbound u)
      _ = ENNReal.ofReal |c| *
          (∫⁻ u in Icc (0 : ℝ) T, dualNormE r P (z u)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The localized physical input is closed under scalar multiplication. -/
theorem fp81s21_windowLocalInput_smul
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec) (c : ℝ) :
    fp81s21_WindowLocalInput C m H a r P (c • z) Cmix cdec := by
  refine {
    fp81s21_hd := D.fp81s21_hd
    fp81s21_hH := D.fp81s21_hH
    fp81s21_ha := D.fp81s21_ha
    fp81s21_horb := D.fp81s21_horb
    fp81s21_hterminal := D.fp81s21_hterminal
    fp81s21_hz := fp81s21_IsR2L1F_smul D.fp81s21_hz
    fp81s21_hP := D.fp81s21_hP
    fp81s21_hm := HRS.MS.CovMeas.s101_meas_smul c D.fp81s21_hm
    fp81s21_hCmix := D.fp81s21_hCmix
    fp81s21_hcdec := D.fp81s21_hcdec
    fp81s21_hPos := D.fp81s21_hPos
  }

/-- The localized physical input is closed under addition provided the first
field's dual-norm density is a.e. measurable. -/
theorem fp81s21_windowLocalInput_add_of_aemeasurable_dualNorm
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z z' : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (D' : fp81s21_WindowLocalInput C m H a r P z' Cmix cdec)
    (hmeasNorm : AEMeasurable
      (fun u => dualNormE r P (z u)) (volume.restrict (Icc (0 : ℝ) (a + H)))) :
    fp81s21_WindowLocalInput C m H a r P (z + z') Cmix cdec := by
  refine {
    fp81s21_hd := D.fp81s21_hd
    fp81s21_hH := D.fp81s21_hH
    fp81s21_ha := D.fp81s21_ha
    fp81s21_horb := D.fp81s21_horb
    fp81s21_hterminal := D.fp81s21_hterminal
    fp81s21_hz := fp81s21_IsR2L1F_add_of_aemeasurable_dualNorm
      D.fp81s21_hz D'.fp81s21_hz hmeasNorm
    fp81s21_hP := D.fp81s21_hP
    fp81s21_hm := HRS.MS.CovMeas.s101_meas_add D.fp81s21_hm D'.fp81s21_hm
    fp81s21_hCmix := D.fp81s21_hCmix
    fp81s21_hcdec := D.fp81s21_hcdec
    fp81s21_hPos := D.fp81s21_hPos
  }

#print axioms fp81s21_dualNormE_add_le
#print axioms fp81s21_IsR2L1F_add_of_aemeasurable_dualNorm
#print axioms fp81s21_IsR2L1F_smul
#print axioms fp81s21_windowLocalInput_add_of_aemeasurable_dualNorm
#print axioms fp81s21_windowLocalInput_smul

end HRS.Fp81.S21

end
