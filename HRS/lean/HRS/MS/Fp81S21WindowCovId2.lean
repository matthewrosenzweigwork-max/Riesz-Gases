import HRS.MS.Fp81S21WindowCovId
import HRS.MC.E213U2
import HRS.MS.ProClosureS111WindowRestriction
import HRS.MS.R2InterpAux13

/-! Restriction transports the full covariance specification to a window. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.Sec7 HRS.MS.R2Interp HRS.MC.E213O

/-- A full-horizon covariance value restricts to the shifted window value. -/
theorem fp81s21_restrict_isWindowJValue {d : ℕ} {m T a : ℝ}
    (C : WholeCoeff d) (ha : 0 ≤ a)
    (z : ℝ → (Euc d → ℝ) → ℝ) (I : Set ℝ)
    {J : TensorDual (OscPath d m (a + T)) 2}
    (hJ : IsR2JValue C m (a + T) z I J) :
    fp81s21_IsWindowJValue C m T a z I
      (tensorPow' 2 (HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := d) (m := m) (T := T) (H := a + T) ha le_rfl) J) := by
  classical
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := d) (m := m) (T := T) (H := a + T) ha le_rfl
  refine ⟨HRS.MC.E213U2.e213u2_tensorPow'_mem 2 W hJ.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  have hta' : a + ta ∈ Icc (0 : ℝ) (a + T) :=
    ⟨add_nonneg ha hta.1, by linarith [hta.2]⟩
  have htb' : a + tb ∈ Icc (0 : ℝ) (a + T) :=
    ⟨add_nonneg ha htb.1, by linarith [htb.2]⟩
  have hpath : ∀ (w : OscPath d m (a + T)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
      r2PathAt (W w) t = r2PathAt w (a + t) := by
    intro w t ht
    rw [s102_r2PathAt_of_mem _ ht,
      s102_r2PathAt_of_mem _ ⟨add_nonneg ha ht.1, by linarith [ht.2]⟩]
    rfl
  have hl₁' : ∀ w, (l₁.comp W) w = OscDual.eval (r2PathAt w (a + ta)) φa := by
    intro w
    rw [ContinuousLinearMap.comp_apply, hl₁, hpath w ta hta]
  have hl₂' : ∀ w, (l₂.comp W) w = OscDual.eval (r2PathAt w (a + tb)) φb := by
    intro w
    rw [ContinuousLinearMap.comp_apply, hl₂, hpath w tb htb]
  have hM : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]).compContinuousLinearMap
      (fun _ => W) = (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
        ![l₁.comp W, l₂.comp W] := by
    ext x
    simp [Fin.prod_univ_two]
  change tensorPow' 2 W J _ = _
  rw [tensorPow'_apply, hM]
  exact hJ.2 _ _ _ _ _ _ hφa hφb hta' htb' hl₁' hl₂'

/-- The restricted full covariance agrees with every specified window value. -/
theorem fp81s21_restrict_eq_windowJValue {d : ℕ} {m T a : ℝ}
    (C : WholeCoeff d) (hT : 0 < T) (ha : 0 ≤ a)
    (z : ℝ → (Euc d → ℝ) → ℝ) (I : Set ℝ)
    {J : TensorDual (OscPath d m (a + T)) 2}
    {Jw : TensorDual (OscPath d m T) 2}
    (hJ : IsR2JValue C m (a + T) z I J)
    (hJw : fp81s21_IsWindowJValue C m T a z I Jw) :
    tensorPow' 2 (HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := d) (m := m) (T := T) (H := a + T) ha le_rfl) J = Jw :=
  fp81s21_window_J_unique C hT z I (fp81s21_restrict_isWindowJValue C ha z I hJ) hJw

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_restrict_isWindowJValue
#print axioms HRS.Fp81.S21.fp81s21_restrict_eq_windowJValue
