import HRS.Equilibrium.Parametrix.PXFIDAuxF

/-!
# Packet PX-FID, file G: integration by parts without diagonal flux, for one slice
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

/-- Pointwise bound for `B u` of a singular slice. -/
theorem SingSlice.abs_Bop_le {β : ℝ} (hβ : 0 < β) {V ρ : Torus d → ℝ} {M : ℝ}
    (hM : ∀ x, ‖Torus.grad V x + forceField d s ρ x‖ ≤ M) {K : ℝ} (hK : 0 ≤ K) (hs1 : 1 ≤ s)
    {ã : Euc d} {u : Torus d → ℝ} (hu : SingSlice s K ã u) (x : Torus d) (hx : x ≠ Torus.mk ã) :
    ‖Bop d s V β ρ u x‖ ≤ (β⁻¹ * d * K + M * K) * wEnv s x (Torus.mk ã) := by
  have h1 := hu.abs_laplacian_le x hx
  have h2 := hu.norm_grad_le hK hs1 x hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
  unfold Bop
  rw [Real.norm_eq_abs]
  have h3 : |inner ℝ (Torus.grad V x + forceField d s ρ x) (Torus.grad u x)| ≤
      M * (K * wEnv s x (Torus.mk ã)) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hM x) h2 (norm_nonneg _) hM0)
  have h4 : |β⁻¹ * Torus.laplacian u x| ≤ β⁻¹ * (d * K * wEnv s x (Torus.mk ã)) := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hβ)]
    exact mul_le_mul_of_nonneg_left h1 (inv_pos.2 hβ).le
  calc |β⁻¹ * Torus.laplacian u x - inner ℝ (Torus.grad V x + forceField d s ρ x) (Torus.grad u x)|
      ≤ |β⁻¹ * Torus.laplacian u x| +
        |inner ℝ (Torus.grad V x + forceField d s ρ x) (Torus.grad u x)| := abs_sub _ _
    _ ≤ β⁻¹ * (d * K * wEnv s x (Torus.mk ã)) + M * (K * wEnv s x (Torus.mk ã)) := add_le_add h4 h3
    _ = (β⁻¹ * d * K + M * K) * wEnv s x (Torus.mk ã) := by ring

/-- **Integration by parts without diagonal flux** for a slice with a point singularity. -/
theorem ibp_singular (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β)
    {V ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    (hforce : ∀ x, ρ x • (Torus.grad V x + forceField d s ρ x) = -β⁻¹ • Torus.grad ρ x)
    {M : ℝ} (hM : ∀ x, ‖Torus.grad V x + forceField d s ρ x‖ ≤ M)
    {K : ℝ} (hK : 0 ≤ K) (ã : Euc d) {u : Torus d → ℝ} (hu : SingSlice s K ã u)
    {ϕ : Torus d → ℝ} (hϕ : Torus.IsSmooth ϕ) :
    Integrable (Bop d s V β ρ u) (withDensityReal ρ) ∧
    Integrable (fun x => ‖Torus.grad u x‖) (withDensityReal ρ) ∧
    Integrable (fun x => inner ℝ (Torus.grad u x) (Torus.grad ϕ x)) (withDensityReal ρ) ∧
    ∫ x, Bop d s V β ρ u x * ϕ x ∂(withDensityReal ρ) =
      -β⁻¹ * ∫ x, inner ℝ (Torus.grad u x) (Torus.grad ϕ x) ∂(withDensityReal ρ) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hρc : Continuous ρ := Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ∞ (Torus.lift ρ) from hρ.smooth).continuous
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, ∀ x, ρ x ≤ Λ := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
    exact ⟨C, fun x => (le_abs_self _).trans (by simpa using hC x (Set.mem_univ x))⟩
  obtain ⟨Mϕ, hMϕ⟩ := exists_abs_le_of_smooth hϕ
  obtain ⟨Gϕ, hGϕ⟩ := exists_norm_grad_le_of_smooth hϕ
  obtain ⟨Cθ, hCθ0, hCθ⟩ := exists_norm_grad_theta_le d
  have hMϕ0 : 0 ≤ Mϕ := (abs_nonneg _).trans (hMϕ 0)
  have hGϕ0 : 0 ≤ Gϕ := (norm_nonneg _).trans (hGϕ 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set μ := withDensityReal ρ with hμ
  set CB : ℝ := β⁻¹ * d * K + M * K with hCB
  have hCB0 : 0 ≤ CB := by rw [hCB]; positivity
  have hw1 : ∀ x : Torus d, 1 ≤ wEnv s x (Torus.mk ã) := fun x => PairCorrAux.one_le_wEnv s x _
  -- measurability
  have mBu : Measurable (Bop d s V β ρ u) := measurable_Bop V ρ u
  have mgu : Measurable (Torus.grad u) := measurable_grad u
  have mgϕ : Measurable (Torus.grad ϕ) := measurable_grad ϕ
  have mϕ : Measurable ϕ := measurable_of_isSmooth hϕ
  have mIn : Measurable (fun x => inner ℝ (Torus.grad u x) (Torus.grad ϕ x)) := mgu.inner mgϕ
  -- integrability of the three fixed functions
  have hBu_int : Integrable (Bop d s V β ρ u) μ :=
    integrable_of_le_wEnv hd hcrit hΛ (Torus.mk ã) mBu.aestronglyMeasurable CB
      (fun x hx => hu.abs_Bop_le hβ hM hK hs1 x hx)
  have hgu_int : Integrable (fun x => ‖Torus.grad u x‖) μ :=
    integrable_of_le_wEnv hd hcrit hΛ (Torus.mk ã) mgu.norm.aestronglyMeasurable K
      (fun x hx => by
        rw [norm_norm]; exact hu.norm_grad_le hK hs1 x hx)
  have hIn_int : Integrable (fun x => inner ℝ (Torus.grad u x) (Torus.grad ϕ x)) μ :=
    integrable_of_le_wEnv hd hcrit hΛ (Torus.mk ã) mIn.aestronglyMeasurable (K * Gϕ)
      (fun x hx => by
        rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        have h1 := hu.norm_grad_le hK hs1 x hx
        calc ‖Torus.grad u x‖ * ‖Torus.grad ϕ x‖ ≤ (K * wEnv s x (Torus.mk ã)) * Gϕ :=
              mul_le_mul h1 (hGϕ x) (norm_nonneg _) (by have := hw1 x; positivity)
          _ = K * Gϕ * wEnv s x (Torus.mk ã) := by ring)
  refine ⟨hBu_int, hgu_int, hIn_int, ?_⟩
  -- the three cut-off families
  set F1 : ℝ → Torus d → ℝ := fun ε x => theta ε ã x * ϕ x * Bop d s V β ρ u x with hF1
  set F2 : ℝ → Torus d → ℝ := fun ε x => theta ε ã x * inner ℝ (Torus.grad ϕ x) (Torus.grad u x)
    with hF2
  set F3 : ℝ → Torus d → ℝ := fun ε x =>
    ϕ x * inner ℝ (Torus.grad (theta ε ã) x) (Torus.grad u x) with hF3
  have mF1 : ∀ ε, Measurable (F1 ε) := fun ε => ((measurable_theta ε ã).mul mϕ).mul mBu
  have mF2 : ∀ ε, Measurable (F2 ε) := fun ε =>
    (measurable_theta ε ã).mul (mgϕ.inner mgu)
  have mF3 : ∀ ε, Measurable (F3 ε) := fun ε =>
    mϕ.mul (((measurable_grad (theta ε ã)).inner mgu))
  have b1 : ∀ ε x, x ≠ Torus.mk ã → ‖F1 ε x‖ ≤ Mϕ * CB * wEnv s x (Torus.mk ã) := by
    intro ε x hx
    have h := hu.abs_Bop_le hβ hM hK hs1 x hx
    simp only [hF1]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (theta_nonneg ε ã x)]
    rw [Real.norm_eq_abs] at h
    calc theta ε ã x * |ϕ x| * |Bop d s V β ρ u x| ≤ 1 * Mϕ * (CB * wEnv s x (Torus.mk ã)) :=
          mul_le_mul (mul_le_mul (theta_le_one ε ã x) (hMϕ x) (abs_nonneg _) zero_le_one) h
            (abs_nonneg _) (by positivity)
      _ = Mϕ * CB * wEnv s x (Torus.mk ã) := by ring
  have b2 : ∀ ε x, x ≠ Torus.mk ã → ‖F2 ε x‖ ≤ Gϕ * K * wEnv s x (Torus.mk ã) := by
    intro ε x hx
    have h1 := hu.norm_grad_le hK hs1 x hx
    simp only [hF2]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (theta_nonneg ε ã x)]
    calc theta ε ã x * |inner ℝ (Torus.grad ϕ x) (Torus.grad u x)|
        ≤ 1 * (‖Torus.grad ϕ x‖ * ‖Torus.grad u x‖) :=
          mul_le_mul (theta_le_one ε ã x) (abs_real_inner_le_norm _ _) (abs_nonneg _) zero_le_one
      _ ≤ 1 * (Gϕ * (K * wEnv s x (Torus.mk ã))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hGϕ x) h1 (norm_nonneg _) hGϕ0) zero_le_one
      _ = Gϕ * K * wEnv s x (Torus.mk ã) := by ring
  have b3 : ∀ ε, 0 < ε → ε ≤ 1 → ∀ x, x ≠ Torus.mk ã →
      ‖F3 ε x‖ ≤ Mϕ * (2 * Cθ * K) * wEnv s x (Torus.mk ã) := fun ε hε hε1 x hx =>
    F3_bound hs1 hK hCθ0 hMϕ0 hε hε1 hCθ hu hMϕ x hx
  have hwi := integrable_wEnv_mu hd hcrit hΛ (Torus.mk ã)
  have iF1 : ∀ ε, Integrable (F1 ε) μ := fun ε =>
    integrable_of_le_wEnv hd hcrit hΛ (Torus.mk ã) (mF1 ε).aestronglyMeasurable _ (b1 ε)
  have iF2 : ∀ ε, Integrable (F2 ε) μ := fun ε =>
    integrable_of_le_wEnv hd hcrit hΛ (Torus.mk ã) (mF2 ε).aestronglyMeasurable _ (b2 ε)
  have iF3 : ∀ ε, 0 < ε → ε ≤ 1 → Integrable (F3 ε) μ := fun ε hε hε1 =>
    integrable_of_le_wEnv hd hcrit hΛ (Torus.mk ã) (mF3 ε).aestronglyMeasurable _ (b3 ε hε hε1)
  -- the identity for every small cut-off
  have hid : ∀ ε, 0 < ε → ε ≤ 1 →
      β * ∫ x, F1 ε x ∂μ + ∫ x, F2 ε x ∂μ + ∫ x, F3 ε x ∂μ = 0 := fun ε hε hε1 =>
    cutoff_identity hd1 hβ.ne' hρ hforce hε ã hu.smooth hϕ (iF1 ε) (iF2 ε) (iF3 ε hε hε1)
  -- limits
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  have hev : ∀ᶠ ε in l, 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε using hε
  have hlim_pt : ∀ x, x ≠ Torus.mk ã → ∀ᶠ ε in l, 0 < ε ∧ ε < 2 * Torus.eucDist x (Torus.mk ã) := by
    intro x hx
    have hD0 : 0 < Torus.eucDist x (Torus.mk ã) := by
      rcases (Real.sqrt_nonneg _ : 0 ≤ Torus.eucDist x (Torus.mk ã)).lt_or_eq with h | h
      · exact h
      · exact absurd ((PairCorrAux.eucDist_eq_zero' _ _).1 h.symm) hx
    filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 2 * Torus.eucDist x (Torus.mk ã))]
      with ε hε using hε
  have theta_one : ∀ x, x ≠ Torus.mk ã → ∀ᶠ ε in l, theta ε ã x = 1 := by
    intro x hx
    filter_upwards [hlim_pt x hx] with ε hε
    have h := theta_eq_one hε.1 ã (Torus.rep x) (by
      rw [Torus.mk_rep]; linarith [hε.2])
    rwa [Torus.mk_rep] at h
  have T1 : Tendsto (fun ε => ∫ x, F1 ε x ∂μ) l (𝓝 (∫ x, ϕ x * Bop d s V β ρ u x ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => Mϕ * CB * wEnv s x (Torus.mk ã)) ?_ ?_ (hwi.const_mul _) ?_
    · exact Filter.Eventually.of_forall fun ε => (mF1 ε).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ε => by
        filter_upwards [ae_ne_withDensity hd1 ρ (Torus.mk ã)] with x hx using b1 ε x hx
    · filter_upwards [ae_ne_withDensity hd1 ρ (Torus.mk ã)] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [theta_one x hx] with ε hε
      simp [hF1, hε]
  have T2 : Tendsto (fun ε => ∫ x, F2 ε x ∂μ) l
      (𝓝 (∫ x, inner ℝ (Torus.grad ϕ x) (Torus.grad u x) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => Gϕ * K * wEnv s x (Torus.mk ã)) ?_ ?_ (hwi.const_mul _) ?_
    · exact Filter.Eventually.of_forall fun ε => (mF2 ε).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ε => by
        filter_upwards [ae_ne_withDensity hd1 ρ (Torus.mk ã)] with x hx using b2 ε x hx
    · filter_upwards [ae_ne_withDensity hd1 ρ (Torus.mk ã)] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [theta_one x hx] with ε hε
      simp [hF2, hε]
  have T3 : Tendsto (fun ε => ∫ x, F3 ε x ∂μ) l (𝓝 (∫ x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => Mϕ * (2 * Cθ * K) * wEnv s x (Torus.mk ã)) ?_ ?_ (hwi.const_mul _) ?_
    · exact Filter.Eventually.of_forall fun ε => (mF3 ε).aestronglyMeasurable
    · filter_upwards [hev] with ε hε
      filter_upwards [ae_ne_withDensity hd1 ρ (Torus.mk ã)] with x hx using
        b3 ε hε.1 hε.2 x hx
    · filter_upwards [ae_ne_withDensity hd1 ρ (Torus.mk ã)] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim_pt x hx] with ε hε
      have hg := grad_theta_zero hε.1 ã x (by linarith [hε.2])
      simp [hF3, hg]
  have hT := (T1.const_mul β).add T2 |>.add T3
  have hzero : Tendsto (fun ε => β * ∫ x, F1 ε x ∂μ + ∫ x, F2 ε x ∂μ + ∫ x, F3 ε x ∂μ) l (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with ε hε using (hid ε hε.1 hε.2).symm
  have hu := tendsto_nhds_unique hzero hT
  simp only [integral_zero, add_zero] at hu
  have e1 : ∫ x, Bop d s V β ρ u x * ϕ x ∂μ = ∫ x, ϕ x * Bop d s V β ρ u x ∂μ := by
    simp_rw [mul_comm]
  have e2 : ∫ x, inner ℝ (Torus.grad u x) (Torus.grad ϕ x) ∂μ =
      ∫ x, inner ℝ (Torus.grad ϕ x) (Torus.grad u x) ∂μ := by
    simp_rw [real_inner_comm]
  rw [e1, e2]
  have hβ0 : β ≠ 0 := hβ.ne'
  field_simp
  linarith

end HRS.Parx.PXFID

end
