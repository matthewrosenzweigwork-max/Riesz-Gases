import HRS.MS.WadAux38

/-!
# S8.3, packet D7 (Route A), part 4: linearity of the classical solutions

`s85_sol_smul`: scalar multiples of `S84Sol` are `S84Sol`.  With `s84_sol_sub` and uniqueness
(`s84_apriori_sub` with `Φ = 0`) this gives `s85_cl_lin`: the frozen classical solution depends linearly on
the datum.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s85_conv_smul (G : Euc d → Euc d) (c : ℝ) (u : Euc d → ℝ) (x : Euc d) :
    convGradConvW G (fun y => c * u y) x = c • convGradConvW G u x := by
  unfold convGradConvW
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases h : ‖x - y‖ ≤ 1 / 4
  · simp only [h, if_true]
    rw [← mul_sub, mul_smul]
  · simp only [h, if_false]
    rw [mul_smul]

theorem s85_gradient_smul {h : Euc d → ℝ} (hd : Differentiable ℝ h) (c : ℝ) (y : Euc d) :
    gradient (fun y => c * h y) y = c • gradient h y := by
  unfold gradient
  rw [fderiv_const_mul (hd y) c]
  simp

theorem s85_Bop_smul {ρ : Euc d → ℝ} {h : Euc d → ℝ} (hd : Differentiable ℝ h) (c : ℝ) (x : Euc d) :
    s84_Bop ρ (fun y => c * h y) x = c * s84_Bop ρ h x := by
  unfold s84_Bop
  have e1 : inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x)) (gradient (fun y => c * h y) x) =
      c * inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
        (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x)) (gradient h x) := by
    rw [s85_gradient_smul hd, inner_smul_right]
  have e2 : ∀ j : Fin d, (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
      (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient (fun y => c * h y) y)) j) x) j =
      c * (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
        (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) x) j := by
    intro j
    have hfun : (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient (fun y => c * h y) y)) j) =
        (fun y => c * (ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j)) := by
      funext y
      rw [s85_gradient_smul hd, s84_matVec_neg_T, s84_matVec_neg_T]
      simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hfun, s85_conv_smul]
    simp
  rw [e1, Finset.sum_congr rfl fun j _ => e2 j, ← Finset.mul_sum]
  ring

theorem s85_P_smul {a ν : ℝ} (τ c : ℝ) (f : Euc d → ℝ) (x : Euc d) :
    s83_P a ν τ (fun y => c * f y) x = c * s83_P a ν τ f x := by
  have e : (fun y => c * f y) = c • f := by funext y; simp
  unfold s83_P
  rw [e]
  simpa using congrFun (s83_G_smul (d := d) (s83_mc a τ) (s83_ms a ν τ) c f) x

theorem s85_sol_smul {ρ : Euc d → ℝ} {a ν t M Φ : ℝ} {w : ℝ → Euc d → ℝ} (ha : 0 < a) (hν : 0 < ν)
    (sol : S84Sol ρ a ν t M Φ w) (c : ℝ) : S84Sol ρ a ν t M (|c| * Φ) (fun r y => c * w r y) := by
  have hdiff : ∀ r ∈ Set.Icc (0 : ℝ) t, Differentiable ℝ (w r) := fun r hr =>
    (sol.c2 r hr).differentiable (by norm_num)
  have hlin : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ y, s84_Bop ρ (fun y => c * w s y) y = c * s84_Bop ρ (w s) y :=
    fun s hs y => s85_Bop_smul (hdiff s hs) c y
  obtain ⟨K, p, hq⟩ := sol.hqb
  obtain ⟨B1, B2, hB⟩ := sol.bdd
  refine ⟨fun r hr => contDiff_const.mul (sol.c2 r hr), ?_, ⟨|c| * K, p, fun s hs y => ?_⟩, ?_,
    continuous_const.mul sol.term_cont, ?_, ⟨|c| * B1, |c| * B2, fun r hr y => ?_⟩⟩
  · have := (continuousOn_const (c := c)).mul sol.hqc
    refine this.congr fun q hq' => ?_
    exact hlin q.1 hq'.1 q.2
  · rw [hlin s hs y, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hq s hs y) (abs_nonneg c)
  · intro r hr x
    have hrt : r ≤ t := hr.2
    have hI : (∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (fun y => c * w s y) y) x) =
        c * ∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le hrt] at hs
      have hs' : s ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.trans hs.1, hs.2⟩
      have hfun : (fun y => s84_Bop ρ (fun y => c * w s y) y) = fun y => c * s84_Bop ρ (w s) y :=
        funext (hlin s hs')
      show s83_P a ν (s - r) (fun y => s84_Bop ρ (fun y => c * w s y) y) x = _
      rw [hfun]
      exact s85_P_smul (s - r) c _ x
    show c * w r x = s83_P a ν (t - r) (fun y => c * w t y) x +
      ∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (fun y => c * w s y) y) x
    rw [hI, s85_P_smul, sol.mild r hr x]; ring
  · intro y
    show ‖c * w t y‖ ≤ |c| * Φ * jbracket y ^ M
    rw [Real.norm_eq_abs, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using sol.term_wt y) (abs_nonneg c)
  · have d1 : Differentiable ℝ (w r) := hdiff r hr
    have dd1 : Differentiable ℝ (fderiv ℝ (w r)) :=
      ((sol.c2 r hr).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have e1 : fderiv ℝ (fun y => c * w r y) = fun y => c • fderiv ℝ (w r) y := by
      funext y; exact fderiv_const_mul (d1 y) c
    rw [e1]
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB r hr y).1 (abs_nonneg c)
    · have e2 : fderiv ℝ (fun y => c • fderiv ℝ (w r) y) y = c • fderiv ℝ (fderiv ℝ (w r)) y :=
        fderiv_const_smul (dd1 y) c
      rw [e2]
      refine (ContinuousLinearMap.opNorm_smul_le c (fderiv ℝ (fderiv ℝ (w r)) y)).trans ?_
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB r hr y).2 (abs_nonneg c)

/-- **Linearity of the frozen classical solutions in the datum.** -/
theorem s85_cl_lin (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 < t) {c : ℝ}
    {φ₁ φ₂ φ : Euc d → ℝ} {w₁ w₂ w : ℝ → Euc d → ℝ}
    (h₁ : IsClassicalAdjointW (critCoeff d a β ρβ) t φ₁ w₁)
    (h₂ : IsClassicalAdjointW (critCoeff d a β ρβ) t φ₂ w₂)
    (h : IsClassicalAdjointW (critCoeff d a β ρβ) t φ w) (hφ : ∀ y, φ y = c * φ₁ y + φ₂ y)
    {r : ℝ} (hr : r ∈ Set.Icc 0 t) (y : Euc d) : w r y = c * w₁ r y + w₂ r y := by
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  obtain ⟨Φ₁, hΦ₁⟩ := s85_cl_wt (M := 0) le_rfl ht.le h₁
  obtain ⟨Φ₂, hΦ₂⟩ := s85_cl_wt (M := 0) le_rfl ht.le h₂
  obtain ⟨Φ, hΦ⟩ := s85_cl_wt (M := 0) le_rfl ht.le h
  have s₁ := s84_sol_of_classical a β ha hβ ρβ ht h₁ hΦ₁
  have s₂ := s84_sol_of_classical a β ha hβ ρβ ht h₂ hΦ₂
  have s := s84_sol_of_classical a β ha hβ ρβ ht h hΦ
  have sc₁ := s85_sol_smul ha hν s₁ c
  have sc₂ := s85_sol_smul ha hν s₂ (-1)
  have hg := s84_thermal_gaussReg hd ha hβ hρ
  have sd := s84_sol_sub hd ha hν hg (M := 0) (Φ := Φ) le_rfl ht sc₁ sc₂ (by
    intro y
    have e : c * w₁ t y - -1 * w₂ t y = φ y := by
      rw [h₁.terminal, h₂.terminal, hφ y]; ring
    show ‖c * w₁ t y - -1 * w₂ t y‖ ≤ Φ * jbracket y ^ (0 : ℝ)
    rw [e]; exact hΦ y)
  obtain ⟨K, hK0, hK⟩ := s84_apriori_sub hd ha hν ht (M := 0) le_rfl hg
  have hdiffT : Wt 0 0 (fun y => w t y - (c * w₁ t y - (-1 * w₂ t y))) := by
    intro y
    show ‖w t y - (c * w₁ t y - (-1 * w₂ t y))‖ ≤ 0 * jbracket y ^ (0 : ℝ)
    have : w t y - (c * w₁ t y - (-1 * w₂ t y)) = 0 := by
      rw [h.terminal, h₁.terminal, h₂.terminal, hφ y]; ring
    rw [this]; simp
  have := hK ht le_rfl s sd hdiffT r hr y
  simp only [mul_zero, zero_mul, abs_nonpos_iff] at this
  linarith

end HRS.MS.Wad
