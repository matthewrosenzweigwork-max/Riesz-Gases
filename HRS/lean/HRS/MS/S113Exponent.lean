import HRS.Whole.Round2Moving

/-!
# S11.3.U1 (GPT-6 Pro breakdown, packet U1): one class-uniform exponent from a uniform bound on `∫ L`

Namespace `HRS.MS.S113BD`, prefix `s113_`.  Proves `s113_uniform_exponent` exactly as in the breakdown contract.
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MS.S113BD

/-- The denominator `1 - (1 - p₀⁻¹) exp(-I/c_L)` of the variable exponent. -/
def s113_den (cL p₀ I : ℝ) : ℝ := 1 - (1 - p₀⁻¹) * Real.exp (-(cL⁻¹) * I)

theorem s113_den_mono {cL p₀ : ℝ} (hcL : 0 < cL) (hp₀ : 1 < p₀) {I J : ℝ} (h : I ≤ J) :
    s113_den cL p₀ I ≤ s113_den cL p₀ J := by
  unfold s113_den
  have hq : 0 ≤ 1 - p₀⁻¹ := by
    have : p₀⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp₀.le
    linarith
  have : Real.exp (-(cL⁻¹) * J) ≤ Real.exp (-(cL⁻¹) * I) := by
    apply Real.exp_le_exp.2
    have : 0 < cL⁻¹ := inv_pos.2 hcL
    nlinarith
  nlinarith

theorem s113_den_zero {cL p₀ : ℝ} : s113_den cL p₀ 0 = p₀⁻¹ := by
  unfold s113_den; simp

theorem s113_den_lt_one {cL p₀ : ℝ} (hp₀ : 1 < p₀) (I : ℝ) : s113_den cL p₀ I < 1 := by
  unfold s113_den
  have : 0 < 1 - p₀⁻¹ := by
    have : p₀⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp₀
    linarith
  have := Real.exp_pos (-(cL⁻¹) * I)
  nlinarith

theorem s113_den_pos {cL p₀ : ℝ} (hcL : 0 < cL) (hp₀ : 1 < p₀) {I : ℝ} (hI : 0 ≤ I) :
    0 < s113_den cL p₀ I := by
  have h0 : 0 < p₀⁻¹ := inv_pos.2 (by linarith)
  have := s113_den_mono hcL hp₀ hI
  rw [s113_den_zero] at this
  linarith

theorem s113_uniform_exponent (cL p₀ B : ℝ)
    (hcL : 0 < cL) (hp₀ : 1 < p₀) (hB : 0 ≤ B)
    (L : ℝ → ℝ) (hL0 : ∀ t, 0 ≤ t → 0 ≤ L t)
    (hLi : Integrable L (volume.restrict (Set.Ioi (0 : ℝ))))
    (hLB : (∫ t in Set.Ioi (0 : ℝ), L t) ≤ B) :
    let pstar := (1 - (1 - p₀⁻¹) * Real.exp (-(cL⁻¹) * B))⁻¹
    1 < pstar ∧ pstar ≤ HRS.Whole.r2MovExponentInf cL p₀ L ∧
      ∀ t : ℝ, 0 ≤ t →
        HRS.Whole.r2MovExponentInf cL p₀ L ≤ HRS.Whole.r2MovExponent cL p₀ L t ∧
        HRS.Whole.r2MovExponent cL p₀ L t ≤ p₀ := by
  intro pstar
  have hL0' : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ L t := fun t ht => hL0 t (le_of_lt ht)
  have hIinf0 : 0 ≤ ∫ t in Set.Ioi (0 : ℝ), L t :=
    setIntegral_nonneg measurableSet_Ioi hL0'
  have hDB : 0 < s113_den cL p₀ B := s113_den_pos hcL hp₀ hB
  have hDinf : 0 < s113_den cL p₀ (∫ t in Set.Ioi (0 : ℝ), L t) := s113_den_pos hcL hp₀ hIinf0
  have hpstar : pstar = (s113_den cL p₀ B)⁻¹ := rfl
  have hinf : HRS.Whole.r2MovExponentInf cL p₀ L = (s113_den cL p₀ (∫ t in Set.Ioi (0 : ℝ), L t))⁻¹ := rfl
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · rw [hpstar]; exact one_lt_inv₀ hDB |>.2 (s113_den_lt_one hp₀ B)
  · rw [hpstar, hinf]
    exact inv_anti₀ hDinf (s113_den_mono hcL hp₀ hLB)
  · have hIt : HRS.Whole.r2MovExponent cL p₀ L t =
        (s113_den cL p₀ (∫ r in Set.Icc (0 : ℝ) t, L r))⁻¹ := rfl
    have hIt0 : 0 ≤ ∫ r in Set.Icc (0 : ℝ) t, L r :=
      setIntegral_nonneg measurableSet_Icc (fun r hr => hL0 r hr.1)
    have hItinf : (∫ r in Set.Icc (0 : ℝ) t, L r) ≤ ∫ r in Set.Ioi (0 : ℝ), L r := by
      rw [integral_Icc_eq_integral_Ioc]
      exact setIntegral_mono_set hLi ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hL0'))
        (Filter.Eventually.of_forall fun x hx => Set.Ioc_subset_Ioi_self hx)
    have hDt : 0 < s113_den cL p₀ (∫ r in Set.Icc (0 : ℝ) t, L r) := s113_den_pos hcL hp₀ hIt0
    refine ⟨?_, ?_⟩
    · rw [hinf, hIt]
      exact inv_anti₀ hDt (s113_den_mono hcL hp₀ hItinf)
    · rw [hIt]
      have := s113_den_mono hcL hp₀ hIt0
      rw [s113_den_zero] at this
      have h0 : 0 < p₀⁻¹ := inv_pos.2 (by linarith)
      calc (s113_den cL p₀ (∫ r in Set.Icc (0 : ℝ) t, L r))⁻¹ ≤ (p₀⁻¹)⁻¹ := inv_anti₀ h0 this
        _ = p₀ := inv_inv p₀

end HRS.MS.S113BD
