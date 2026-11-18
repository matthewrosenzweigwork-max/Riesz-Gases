import HRS.MS.S81G_Sing
import HRS.MS.MfeConfAux115

/-!
# S81G, packet G2: the regularised Gibbs laws `Γ_M = sb1Gam D k_M N` converge to the singular Gibbs law `Γ`

`k_M = sb1kM d s M` is the truncated Riesz kernel (equal to `g` off the ball of radius `1/(M+1)`, `≤ g`).
* `s81g_Z_ge`: `Z ≤ Z_M`; `s81g_Z_tendsto`: `Z_M → Z`;
* `s81g_gam_setwise`: `Γ_M(A) → Γ(A)` for every measurable `A` (setwise convergence);
* `s81g_gam_dom`: `(Z/Z_M) Γ ≤ Γ_M` (one-sided domination).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.MS.MfeConf HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S81G

variable {d N : ℕ}

/-- standing hypotheses on the dynamics -/
structure S81Hyp (D : Whole.WholeDyn d) : Prop where
  s_nonneg : 0 ≤ D.s
  d_pos : 1 ≤ d
  invβ_pos : 0 < D.invβ
  V_cont : Continuous D.V
  conf : ∃ cV CV : ℝ, 0 < cV ∧ ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x

variable {D : Whole.WholeDyn d}

theorem s81g_sing_meas (H : S81Hyp D) : Measurable (sb1Hs D (Whole.rieszKernel d D.s) N) :=
  s81g_Hs_meas D (s81g_riesz_meas D.s) H.V_cont N

theorem s81g_reg_meas (H : S81Hyp D) (M : ℕ) : Measurable (sb1Hs D (sb1kM d D.s M) N) :=
  s81g_Hs_meas D (sb1kM_isKernel D.s H.s_nonneg M).smooth.continuous.measurable H.V_cont N

theorem s81g_sing_gz_pos (H : S81Hyp D) : 0 < sb1Gz D (Whole.rieszKernel d D.s) N := by
  obtain ⟨cV, CV, hcV, hV⟩ := H.conf
  exact s81g_gz_pos H.invβ_pos (s81g_sing_meas H) (s81g_riesz_lower H.s_nonneg) hcV hV

theorem s81g_reg_gz_pos (H : S81Hyp D) (M : ℕ) : 0 < sb1Gz D (sb1kM d D.s M) N := by
  obtain ⟨cV, CV, hcV, hV⟩ := H.conf
  exact s81g_gz_pos H.invβ_pos (s81g_reg_meas H M) (sb1kM_isKernel D.s H.s_nonneg M).lower hcV hV

theorem s81g_sing_prob (H : S81Hyp D) : IsProbabilityMeasure (sb1Gam D (Whole.rieszKernel d D.s) N) := by
  obtain ⟨cV, CV, hcV, hV⟩ := H.conf
  exact s81g_gam_prob H.invβ_pos (s81g_sing_meas H) (s81g_riesz_lower H.s_nonneg) hcV hV

theorem s81g_reg_prob (H : S81Hyp D) (M : ℕ) : IsProbabilityMeasure (sb1Gam D (sb1kM d D.s M) N) := by
  obtain ⟨cV, CV, hcV, hV⟩ := H.conf
  exact s81g_gam_prob H.invβ_pos (s81g_reg_meas H M) (sb1kM_isKernel D.s H.s_nonneg M).lower hcV hV

/-- a.e. configuration, the regularised Hamiltonian eventually equals the singular one -/
theorem s81g_Hs_eventually (H : S81Hyp D) :
    ∀ᵐ Z : Whole.EucConfig d N ∂(volume : Measure (Whole.EucConfig d N)), ∀ᶠ M : ℕ in atTop,
      sb1Hs D (sb1kM d D.s M) N Z = sb1Hs D (Whole.rieszKernel d D.s) N Z := by
  filter_upwards [sb1_ae_inj (N := N) H.d_pos] with Z hZ
  have h : ∀ i j : Fin N, i ≠ j → ∀ᶠ M : ℕ in atTop,
      sb1kM d D.s M (Z i - Z j) = Whole.rieszKernel d D.s (Z i - Z j) := fun i j hij => by
    have hne : Z i - Z j ≠ 0 := sub_ne_zero.2 (hZ i j hij)
    filter_upwards [sb1kM_eventually_eq D.s H.s_nonneg hne] with M hM using hM.eq_of_nhds
  have h2 : ∀ᶠ M : ℕ in atTop, ∀ i j : Fin N, i ≠ j →
      sb1kM d D.s M (Z i - Z j) = Whole.rieszKernel d D.s (Z i - Z j) := by
    rw [Filter.eventually_all]; intro i; rw [Filter.eventually_all]; intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun M h => absurd hij h
    · filter_upwards [h i j hij] with M hM _ using hM
  filter_upwards [h2] with M hM
  have hsum : p4k_pairSum (sb1kM d D.s M) N Z = p4k_pairSum (Whole.rieszKernel d D.s) N Z := by
    unfold p4k_pairSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    exact hM i j (Finset.ne_of_mem_erase hj).symm
  unfold sb1Hs
  rw [hsum]

/-- the Gaussian majorant of the Boltzmann weights, uniform in the kernel -/
def s81gF (D : Whole.WholeDyn d) (N : ℕ) (cV CV : ℝ) (x : Whole.EucConfig d N) : ℝ :=
  Real.exp (D.invβ⁻¹ * (N * CV + (N : ℝ) ^ 2 / cV)) * Real.exp (-(D.invβ⁻¹ * cV / 2 * ‖x‖ ^ 2))

theorem s81gF_int (H : S81Hyp D) {cV CV : ℝ} (hcV : 0 < cV) :
    Integrable (s81gF D N cV CV) := by
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 H.invβ_pos
  exact (p4g_integrable_gauss_pi (c := D.invβ⁻¹ * cV / 2) (by positivity)).const_mul _

theorem s81gF_nonneg (cV CV : ℝ) (x : Whole.EucConfig d N) : 0 ≤ s81gF D N cV CV x :=
  mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

theorem s81g_Gw_le_F (H : S81Hyp D) {k : Euc d → ℝ} (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) (x : Whole.EucConfig d N) :
    sb1Gw D k N x ≤ s81gF D N cV CV x :=
  sb1_Gw_le H.invβ_pos hlow hcV hV x

theorem s81g_Z_ge (H : S81Hyp D) (M : ℕ) :
    sb1Gz D (Whole.rieszKernel d D.s) N ≤ sb1Gz D (sb1kM d D.s M) N := by
  obtain ⟨cV, CV, hcV, hV⟩ := H.conf
  unfold sb1Gz
  refine integral_mono_ae ?_ ?_ ?_
  · exact s81g_Gw_int H.invβ_pos (s81g_sing_meas H) (s81g_riesz_lower H.s_nonneg) hcV hV
  · exact s81g_Gw_int H.invβ_pos (s81g_reg_meas H M) (sb1kM_isKernel D.s H.s_nonneg M).lower hcV hV
  · exact sb1_sing_le D H.invβ_pos H.s_nonneg H.d_pos M

theorem s81g_Z_tendsto (H : S81Hyp D) :
    Tendsto (fun M : ℕ => sb1Gz D (sb1kM d D.s M) N) atTop (𝓝 (sb1Gz D (Whole.rieszKernel d D.s) N)) := by
  obtain ⟨cV, CV, hcV, hV⟩ := H.conf
  unfold sb1Gz
  refine tendsto_integral_of_dominated_convergence (s81gF D N cV CV)
    (fun M => (s81g_Gw_meas (s81g_reg_meas H M)).aestronglyMeasurable) (s81gF_int H hcV)
    (fun M => Eventually.of_forall fun Z => ?_) ?_
  · show ‖Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s M) N Z)‖ ≤ s81gF D N cV CV Z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact s81g_Gw_le_F H (sb1kM_isKernel D.s H.s_nonneg M).lower hcV hV Z
  · filter_upwards [s81g_Hs_eventually (N := N) H] with Z hZ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hZ] with M hM
    rw [hM]

theorem s81g_gam_setwise (H : S81Hyp D) {A : Set (Whole.EucConfig d N)} (hA : MeasurableSet A) :
    Tendsto (fun M : ℕ => sb1Gam D (sb1kM d D.s M) N A) atTop
      (𝓝 (sb1Gam D (Whole.rieszKernel d D.s) N A)) := by
  obtain ⟨cV, CV, hcV, hV⟩ := H.conf
  have hzs := s81g_sing_gz_pos (N := N) H
  have hZt := s81g_Z_tendsto (N := N) H
  unfold sb1Gam sb1Dm
  simp only [withDensity_apply _ hA]
  refine tendsto_lintegral_of_dominated_convergence
    (fun x => ENNReal.ofReal (s81gF D N cV CV x / sb1Gz D (Whole.rieszKernel d D.s) N)) ?_ ?_ ?_ ?_
  · intro M
    exact (((s81g_Gw_meas (s81g_reg_meas H M)).div_const _)).ennreal_ofReal
  · intro M
    refine Eventually.of_forall fun x => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    unfold sb1Gq
    have h1 := s81g_Gw_le_F H (sb1kM_isKernel D.s H.s_nonneg M).lower hcV hV x
    have hzM := s81g_reg_gz_pos (N := N) H M
    have hge := s81g_Z_ge (N := N) H M
    calc Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s M) N x) / sb1Gz D (sb1kM d D.s M) N
        ≤ s81gF D N cV CV x / sb1Gz D (sb1kM d D.s M) N :=
          div_le_div_of_nonneg_right h1 hzM.le
      _ ≤ s81gF D N cV CV x / sb1Gz D (Whole.rieszKernel d D.s) N :=
          div_le_div_of_nonneg_left (s81gF_nonneg cV CV x) hzs hge
  · have hi : Integrable (fun x => s81gF D N cV CV x / sb1Gz D (Whole.rieszKernel d D.s) N) :=
      (s81gF_int H hcV).div_const _
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x =>
      div_nonneg (s81gF_nonneg cV CV x) hzs.le)]
    exact ENNReal.ofReal_lt_top
  · refine ae_restrict_of_ae ?_
    filter_upwards [s81g_Hs_eventually (N := N) H] with Z hZ
    refine ENNReal.tendsto_ofReal ?_
    unfold sb1Gq
    have h1 : Tendsto (fun M : ℕ => Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s M) N Z)) atTop
        (𝓝 (Real.exp (-D.invβ⁻¹ * sb1Hs D (Whole.rieszKernel d D.s) N Z))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hZ] with M hM
      rw [hM]
    exact h1.div hZt hzs.ne'

theorem s81g_gam_dom (H : S81Hyp D) (M : ℕ) :
    ENNReal.ofReal (sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N) •
        sb1Gam D (Whole.rieszKernel d D.s) N ≤ sb1Gam D (sb1kM d D.s M) N := by
  have hzs := s81g_sing_gz_pos (N := N) H
  have hzM := s81g_reg_gz_pos (N := N) H M
  have hzs' := hzs.ne'
  have hzM' := hzM.ne'
  unfold sb1Gam sb1Dm
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_mono ?_
  filter_upwards [sb1_sing_le D H.invβ_pos H.s_nonneg H.d_pos (N := N) M] with Z hZ
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (div_nonneg hzs.le hzM.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold sb1Gq
  have : sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N *
      (Real.exp (-D.invβ⁻¹ * sb1Hs D (Whole.rieszKernel d D.s) N Z) / sb1Gz D (Whole.rieszKernel d D.s) N) =
      Real.exp (-D.invβ⁻¹ * sb1Hs D (Whole.rieszKernel d D.s) N Z) / sb1Gz D (sb1kM d D.s M) N := by
    field_simp
  rw [this]
  exact div_le_div_of_nonneg_right hZ hzM.le

end HRS.MS.S81G
