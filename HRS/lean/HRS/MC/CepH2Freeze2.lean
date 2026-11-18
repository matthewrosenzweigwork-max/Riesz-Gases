import HRS.MC.CepH2Freeze1

/-!
# CEPH2, G1 (b): freezing the potential outside the tube `‖P⊥ z‖ < n`
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- The model quadratic. -/
def h2_Q (c C : ℝ) (z : Ch N) : ℝ := c * ‖h2_perp z‖ ^ 2 - C

theorem h2_contDiff_Q (c C : ℝ) : ContDiff ℝ 2 (h2_Q (N := N) c C) := by
  unfold h2_Q
  exact ((h2_contDiff_perp_sq.of_le (by norm_num)).const_smul c).sub contDiff_const

theorem h2_Q_periodic (c C : ℝ) (z : Ch N) : h2_Q c C (z + cep_diag N) = h2_Q c C z := by
  unfold h2_Q
  have := h2_perp_add_diag z 1
  rw [one_smul] at this
  rw [this]

theorem h2_hasGradientAt_Q (c C : ℝ) (x : Ch N) : HasGradientAt (h2_Q c C) ((2 * c) • h2_perp x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hq : HasFDerivAt (fun x : Ch N => ‖h2_perp x‖ ^ 2)
      ((2 • innerSL ℝ (h2_perp x)).comp (h2_permL N : Ch N →L[ℝ] Ch N)) x := by
    have := (hasStrictFDerivAt_norm_sq (h2_permL N x)).hasFDerivAt.comp x (h2_permL N).hasFDerivAt
    exact this
  have h1 := (hq.const_mul c).sub_const C
  have e : (InnerProductSpace.toDual ℝ (Ch N)) ((2 * c) • h2_perp x) =
      c • ((2 • innerSL ℝ (h2_perp x)).comp (h2_permL N : Ch N →L[ℝ] Ch N)) := by
    ext w
    simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      h2_permL_apply, innerSL_apply_apply, smul_eq_mul, real_inner_smul_left, nsmul_eq_mul]
    rw [h2_inner_perp]
    push_cast
    ring
  rw [e]
  exact h1

theorem h2_gradient_Q (c C : ℝ) (x : Ch N) : gradient (h2_Q c C) x = (2 * c) • h2_perp x :=
  (h2_hasGradientAt_Q c C x).gradient

theorem h2_lipschitz_gradient_Q {c : ℝ} (hc : 0 ≤ c) (C : ℝ) :
    LipschitzWith (Real.toNNReal (2 * c)) (gradient (h2_Q (N := N) c C)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [h2_gradient_Q, dist_eq_norm, ← smul_sub, norm_smul, ← h2_perp_sub, Real.norm_eq_abs,
    Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * c)]
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (h2_norm_perp_le _) (by positivity)

theorem h2_infDist_le (z : Ch N) : Metric.infDist z (cep_Alcove N) ≤ ‖h2_perp z‖ + Real.sqrt N := by
  obtain ⟨w', hw'⟩ := h2_alcove_nonempty (N := N)
  set m : ℝ := h2_mean z - h2_mean w' with hm
  have hw : w' + m • cep_diag N ∈ cep_Alcove N := by
    refine ⟨fun k l hkl => ?_, fun k l => ?_⟩
    · simp only [PiLp.add_apply, PiLp.smul_apply, cep_diag_apply, smul_eq_mul, mul_one]
      linarith [hw'.1 k l hkl]
    · simp only [PiLp.add_apply, PiLp.smul_apply, cep_diag_apply, smul_eq_mul, mul_one]
      linarith [hw'.2 k l]
  have h1 : z - (w' + m • cep_diag N) = h2_perp z - h2_perp w' := by
    have e1 : z = h2_perp z + h2_mean z • cep_diag N := by rw [h2_perp_eq]; abel
    have e2 : w' = h2_perp w' + h2_mean w' • cep_diag N := by rw [h2_perp_eq]; abel
    conv_lhs => rw [e1, e2]
    simp only [hm, sub_smul]
    abel
  refine (Metric.infDist_le_dist_of_mem hw).trans ?_
  rw [dist_eq_norm, h1]
  refine (norm_sub_le _ _).trans ?_
  have := h2_alcove_perp_le hw'
  linarith

theorem cepH2_freeze {U : Ch N → ℝ} (hU : ContDiff ℝ 2 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z) :
    ∃ (Un : ℕ → Ch N → ℝ) (K : ℕ → ℝ≥0), (∀ n, ContDiff ℝ 2 (Un n)) ∧ (∀ n z, Un n (z + cep_diag N) = Un n z) ∧
      (∀ n, LipschitzWith (K n) (gradient (Un n))) ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ n z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Un n z) ∧
      (∀ (n : ℕ) (z : Ch N), ‖h2_perp z‖ < (n : ℝ) → Un n z = U z) ∧ (∀ n z, Un n z ≤ U z) := by
  obtain ⟨c, C, hc, hQ⟩ := h2_U_lower hconf
  set φ : ℕ → Ch N → ℝ := fun n z => h2_chi ((n : ℝ) + 1) z * (U z - h2_Q c C z) with hφ
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hφd : ∀ n, ContDiff ℝ 2 (φ n) := fun n =>
    ((h2_contDiff_chi ((n : ℝ) + 1)).of_le (by norm_num)).mul (hU.sub (h2_contDiff_Q c C))
  have hφper : ∀ (n : ℕ) (z : Ch N), φ n (z + cep_diag N) = φ n z := fun n z => by
    simp only [hφ, h2_chi_periodic, hUper, h2_Q_periodic]
  have hφfar : ∀ (n : ℕ) (z : Ch N), 2 * ((n : ℝ) + 1) < ‖h2_perp z‖ → φ n z = 0 := fun n z hz => by
    simp only [hφ]
    rw [h2_chi_eq_zero (hRpos n) hz.le, zero_mul]
  have hB : ∀ n, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ (φ n)) x‖ ≤ B := fun n =>
    h2_bdd_fderiv2 (hφd n) (hφper n) (hφfar n)
  choose B hB0 hBb using hB
  refine ⟨fun n z => h2_Q c C z + φ n z, fun n => Real.toNNReal (2 * c) + Real.toNNReal (B n), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n => (h2_contDiff_Q c C).add (hφd n)
  · exact fun n z => by simp only [h2_Q_periodic, hφper]
  · intro n
    have hl1 := h2_lipschitz_gradient_Q hc.le C (N := N)
    have hl2 := h2_lipschitz_gradient (hφd n) (hB0 n) (hBb n)
    have hsum : gradient (fun z => h2_Q c C z + φ n z) = fun x => gradient (h2_Q c C) x + gradient (φ n) x := by
      funext x
      have h1 : DifferentiableAt ℝ (h2_Q c C) x := ((h2_contDiff_Q c C).differentiable (by simp)) x
      have h2 : DifferentiableAt ℝ (φ n) x := ((hφd n).differentiable (by simp)) x
      simp only [gradient]
      have e : (fun z => h2_Q c C z + φ n z) = h2_Q c C + φ n := rfl
      rw [e, fderiv_add h1 h2, map_add]
    rw [hsum]
    exact hl1.add hl2
  · refine ⟨c / 2, C + c * N, by positivity, fun n z => ?_⟩
    have h1 := h2_infDist_le z
    have hd : 0 ≤ Metric.infDist z (cep_Alcove N) := Metric.infDist_nonneg
    have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
    have h2 : Metric.infDist z (cep_Alcove N) ^ 2 ≤ 2 * ‖h2_perp z‖ ^ 2 + 2 * N := by
      have : Metric.infDist z (cep_Alcove N) ^ 2 ≤ (‖h2_perp z‖ + Real.sqrt N) ^ 2 :=
        pow_le_pow_left₀ hd h1 2
      nlinarith [sq_nonneg (‖h2_perp z‖ - Real.sqrt N)]
    have h3 : 0 ≤ φ n z := by
      simp only [hφ]
      exact mul_nonneg (h2_chi_nonneg _ _) (by unfold h2_Q; linarith [hQ z])
    show c / 2 * Metric.infDist z (cep_Alcove N) ^ 2 - (C + c * N) ≤ h2_Q c C z + φ n z
    unfold h2_Q
    nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
  · intro n z hz
    have : h2_chi ((n : ℝ) + 1) z = 1 := h2_chi_eq_one (hRpos n) (by linarith)
    simp only [hφ, this, one_mul]
    ring
  · intro n z
    have h0 : 0 ≤ U z - h2_Q c C z := by unfold h2_Q; linarith [hQ z]
    have h1 : h2_chi ((n : ℝ) + 1) z * (U z - h2_Q c C z) ≤ U z - h2_Q c C z := by
      calc _ ≤ 1 * (U z - h2_Q c C z) := mul_le_mul_of_nonneg_right (h2_chi_le_one _ _) h0
        _ = _ := one_mul _
    simp only [hφ]
    linarith

end HRS.MC.CepH2
