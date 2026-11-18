import HRS.MS.SpecAux75

/-!
# S8L: derivative of the entropy along the Gaussian interpolation (S8.7, Gaussian log-Sobolev)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_Lam_ent_deriv`: for `f ≥ δ > 0` in the bounded `C¹` class,
`d/dθ ∫ P_θ f log P_θ f dγ = -sin θ cos θ ∫ ‖P_θ Df‖² / P_θ f dγ` (from `s8p_KL` with `ψ = log P_θ f + 1`).
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {f : V → ℝ} {M0 M1 : ℝ}

theorem s8p_Pt_fderiv (hf : S8pBdd f M0 M1) (θ : ℝ) (x : V) :
    fderiv ℝ (s8p_Pt f θ) x = Real.cos θ • s8p_Pd f θ x := (s8p_Pt_hasFDerivAt hf θ x).fderiv

theorem s8p_Pt_contDiff (hf : S8pBdd f M0 M1) (θ : ℝ) : ContDiff ℝ 1 (s8p_Pt f θ) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (s8p_Pt_hasFDerivAt hf θ x).differentiableAt, ?_⟩
  have : fderiv ℝ (s8p_Pt f θ) = fun x => Real.cos θ • s8p_Pd f θ x := funext (s8p_Pt_fderiv hf θ)
  rw [this]
  exact (continuous_const : Continuous fun _ : V => Real.cos θ).smul (s8p_Pd_continuous hf θ)

theorem s8p_Pd_toDual (L : V →L[ℝ] ℝ) : L ((InnerProductSpace.toDual ℝ V).symm L) = ‖L‖ ^ 2 := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := (InnerProductSpace.toDual ℝ V).symm L) (y := L)
  rw [← h, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]

/-- The test function `ψ = log P_θ f + 1` for the entropy functional. -/
def s8p_psi (f : V → ℝ) (θ : ℝ) (x : V) : ℝ := Real.log (s8p_Pt f θ x) + 1

theorem s8p_psi_bdd {δ : ℝ} (hδ0 : 0 < δ) (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x) (θ : ℝ) :
    S8pBdd (s8p_psi f θ) (|Real.log δ| + |Real.log M0| + 1) (M1 / δ) := by
  have hP : ∀ x, δ ≤ s8p_Pt f θ x ∧ s8p_Pt f θ x ≤ M0 := fun x =>
    ⟨s8p_Pt_ge hf hδ θ x, (le_abs_self _).trans (s8p_Pt_abs_le hf θ x)⟩
  have hpos : ∀ x, 0 < s8p_Pt f θ x := fun x => lt_of_lt_of_le hδ0 (hP x).1
  have hd : ∀ x, HasFDerivAt (s8p_psi f θ) ((s8p_Pt f θ x)⁻¹ • (Real.cos θ • s8p_Pd f θ x)) x := fun x => by
    have := ((s8p_Pt_hasFDerivAt hf θ x).log (hpos x).ne').add_const 1
    exact this
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt, ?_⟩
    have : fderiv ℝ (s8p_psi f θ) = fun x => (s8p_Pt f θ x)⁻¹ • (Real.cos θ • s8p_Pd f θ x) :=
      funext fun x => (hd x).fderiv
    rw [this]
    exact ((s8p_Pt_continuous hf θ).inv₀ (fun x => (hpos x).ne')).smul
      ((continuous_const : Continuous fun _ : V => Real.cos θ).smul (s8p_Pd_continuous hf θ))
  · unfold s8p_psi
    have h1 : |Real.log (s8p_Pt f θ x)| ≤ |Real.log δ| + |Real.log M0| := by
      rw [abs_le]
      have h2 := Real.log_le_log hδ0 (hP x).1
      have h3 := Real.log_le_log (hpos x) (hP x).2
      constructor
      · have := neg_abs_le (Real.log δ); have := abs_nonneg (Real.log M0); linarith
      · have := le_abs_self (Real.log M0); have := abs_nonneg (Real.log δ); linarith
    calc _ ≤ |Real.log (s8p_Pt f θ x)| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ _ := by simp; linarith
  · rw [(hd x).fderiv, norm_smul, norm_smul, norm_inv, Real.norm_of_nonneg (hpos x).le, Real.norm_eq_abs]
    have h1 := Real.abs_cos_le_one θ
    have h2 := s8p_Pd_norm_le hf θ x
    have h3 : δ⁻¹ ≥ (s8p_Pt f θ x)⁻¹ := inv_anti₀ hδ0 (hP x).1
    calc (s8p_Pt f θ x)⁻¹ * (|Real.cos θ| * ‖s8p_Pd f θ x‖) ≤ δ⁻¹ * (1 * M1) :=
          mul_le_mul h3 (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) (by positivity) (by positivity)
      _ = M1 / δ := by ring


theorem s8p_ent_Phi {δ M : ℝ} (hδ : 0 < δ) :
    S8pPhi (fun t => t * Real.log t) (fun t => Real.log t + 1) δ M
      ((M + 1) * (|Real.log δ| + |Real.log M| + 1)) where
  pos := hδ
  deriv'c := fun t ht => (Real.continuousAt_log (ne_of_gt ht)).continuousWithinAt.add continuousWithinAt_const
  deriv := fun t ht => Real.hasDerivAt_mul_log ht.ne'
  bd := fun t h1 h2 => by
    have ht : 0 < t := lt_of_lt_of_le hδ h1
    have hM : 0 < M := lt_of_lt_of_le ht h2
    have hl : |Real.log t| ≤ |Real.log δ| + |Real.log M| := by
      rw [abs_le]
      have a1 := Real.log_le_log hδ h1
      have a2 := Real.log_le_log ht h2
      constructor
      · have := neg_abs_le (Real.log δ); have := abs_nonneg (Real.log M); linarith
      · have := le_abs_self (Real.log M); have := abs_nonneg (Real.log δ); linarith
    have hl0 := abs_nonneg (Real.log δ)
    have hl1 := abs_nonneg (Real.log M)
    constructor
    · rw [abs_mul, abs_of_pos ht]
      nlinarith [abs_nonneg (Real.log t)]
    · calc |Real.log t + 1| ≤ |Real.log t| + 1 := by
            refine (abs_add_le _ _).trans ?_; simp
        _ ≤ _ := by nlinarith

/-- **Derivative of the entropy along the interpolation**. -/
theorem s8p_Lam_ent_deriv {δ : ℝ} (hδ0 : 0 < δ) (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x) (θ : ℝ) :
    HasDerivAt (fun θ => ∫ x, (s8p_Pt f θ x * Real.log (s8p_Pt f θ x)) * s8p_gd x)
      (-(Real.sin θ * Real.cos θ * ∫ x, ‖s8p_Pd f θ x‖ ^ 2 / s8p_Pt f θ x * s8p_gd x)) θ := by
  have h := s8p_Lam_hasDerivAt hf hδ (s8p_ent_Phi hδ0) θ
  convert h using 1
  have hP : ∀ x, δ ≤ s8p_Pt f θ x := fun x => s8p_Pt_ge hf hδ θ x
  have hpos : ∀ x, 0 < s8p_Pt f θ x := fun x => lt_of_lt_of_le hδ0 (hP x)
  have hk := s8p_KL hf (s8p_psi_bdd hδ0 hf hδ θ) θ
  have e1 : ∫ x, (Real.log (s8p_Pt f θ x) + 1) * s8p_Pth f θ x * s8p_gd x =
      ∫ x, s8p_psi f θ x * s8p_Pth f θ x * s8p_gd x := rfl
  rw [e1, hk]
  have hd : ∀ x, fderiv ℝ (s8p_psi f θ) x = (s8p_Pt f θ x)⁻¹ • (Real.cos θ • s8p_Pd f θ x) := fun x => by
    have := ((s8p_Pt_hasFDerivAt hf θ x).log (hpos x).ne').add_const 1
    exact this.fderiv
  have e2 : ∀ x, s8p_Pd f θ x (s8p_w (s8p_psi f θ) x) * s8p_gd x =
      Real.cos θ * (‖s8p_Pd f θ x‖ ^ 2 / s8p_Pt f θ x * s8p_gd x) := fun x => by
    unfold s8p_w
    rw [hd x]
    have : (InnerProductSpace.toDual ℝ V).symm ((s8p_Pt f θ x)⁻¹ • (Real.cos θ • s8p_Pd f θ x)) =
        ((s8p_Pt f θ x)⁻¹ * Real.cos θ) • (InnerProductSpace.toDual ℝ V).symm (s8p_Pd f θ x) := by
      rw [← smul_assoc, smul_eq_mul]
      simp
    rw [this, map_smul, s8p_Pd_toDual, smul_eq_mul]
    field_simp
  simp_rw [e2]
  rw [integral_const_mul]
  ring

end HRS.MS.Spec
