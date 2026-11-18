import HRS.MS.S82UC2

/-!
# S8.2 A01 (S82U): integrability hypotheses of the abstract Jmean for `ψ_y = ∇_1 Q(·, y)`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

lemma u_gt_section_measurable {d : ℕ} (Q : Euc d → Euc d → ℝ) (y : Euc d) :
    Measurable (fun w => s82p2_gt Q w y) :=
  (s82p2_gt_measurable Q).comp (measurable_id.prodMk measurable_const)

lemma u_gt_section_measurable' {d : ℕ} (Q : Euc d → Euc d → ℝ) (x : Euc d) :
    Measurable (fun z => s82p2_gt Q x z) :=
  (s82p2_gt_measurable Q).comp (measurable_const.prodMk measurable_id)

theorem u_psi_ok {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} {Gc c : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hQ : PairCorrector a beta rho M A f Q) (hG : 0 ≤ Gc) (hc : 0 < c)
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho) (y : Euc d) :
    Integrable (fun z => rho z * ‖s82p2_gt Q z y‖) ∧
    Integrable (fun p : Euc d × Euc d => rho p.1 * rho p.2 *
      (‖rieszKernelGrad d (criticalS d) (p.1 - p.2)‖ * ‖s82p2_gt Q p.2 y - s82p2_gt Q p.1 y‖))
      ((volume : Measure (Euc d)).prod volume) := by
  have hρm := hρ.measurable
  have hρ0 := hρ.nonneg
  have hgm := u_gt_section_measurable Q y
  have hae : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ y := by
    have : Nontrivial (Euc d) := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      simp; omega
    exact compl_mem_ae_iff.mpr (measure_singleton y)
  constructor
  · -- first claim
    have h1 := u_int_pole hd (by linarith : 0 ≤ M) hG hc hρ hρG y
    have h2 : Integrable (fun z => ‖s82p2_gt Q z y‖) (HRS.Whole.withDensityReal rho) := by
      have hb := h1.const_mul (A * jbracket y ^ M)
      refine Integrable.mono' hb hgm.norm.aestronglyMeasurable ?_
      have hmu : ∀ᵐ z ∂(HRS.Whole.withDensityReal rho), z ≠ y := s82t_mu_ae_ne hd rho y
      filter_upwards [hmu] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have := u_gt_bound_W hd hA hQ hz (W := Phase2S82.pairWeight M z y) le_rfl
      refine this.trans ?_
      unfold Phase2S82.pairWeight
      rw [u_pole_symm z y]
      have := (u_jb_rpow_pos M z).le
      have := (u_jb_rpow_pos M y).le
      nlinarith [mul_nonneg (mul_nonneg hA (u_jb_rpow_pos M y).le) (mul_nonneg (u_jb_rpow_pos M z).le
        (by linarith [u_pole_pos y z] : (0:ℝ) ≤ pole y z))]
    exact u_int_dens hρ h2
  · -- product claim
    set Ce := HRS.Whole.movtr_sigma (criticalS d) * (2 ^ M * 2 ^ criticalS d + 6) with hCe
    have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
    have hCe0 : 0 ≤ Ce := mul_nonneg (s82t_sigma_nonneg _ hs0) (by positivity)
    have hT1 := u_prod_int hd (by linarith : 0 ≤ 2 * M) hG hc hρ hρG y
    have hT2 := hT1.swap
    have henv : Integrable (fun p : Euc d × Euc d => Ce * (A * jbracket y ^ (2 * M)) *
        ((rho p.1 * rho p.2 * (jbracket p.1 ^ (2 * M) * jbracket p.2 ^ (2 * M) *
            (pole p.1 p.2 * pole p.1 y))) +
          ((fun p : Euc d × Euc d => rho p.1 * rho p.2 * (jbracket p.1 ^ (2 * M) * jbracket p.2 ^ (2 * M) *
            (pole p.1 p.2 * pole p.1 y))) ∘ Prod.swap) p))
        ((volume : Measure (Euc d)).prod volume) :=
      (hT1.add hT2).const_mul _
    have hG' : Measurable (rieszKernelGrad d (criticalS d)) :=
      HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
    have hsub : Measurable (fun p : Euc d × Euc d => p.1 - p.2) := measurable_fst.sub measurable_snd
    have hgs1 : Measurable (fun p : Euc d × Euc d => s82p2_gt Q p.1 y) := hgm.comp measurable_fst
    have hgs2 : Measurable (fun p : Euc d × Euc d => s82p2_gt Q p.2 y) := hgm.comp measurable_snd
    have hmeas : Measurable (fun p : Euc d × Euc d => rho p.1 * rho p.2 *
        (‖rieszKernelGrad d (criticalS d) (p.1 - p.2)‖ * ‖s82p2_gt Q p.2 y - s82p2_gt Q p.1 y‖)) :=
      ((hρm.comp measurable_fst).mul (hρm.comp measurable_snd)).mul
        ((hG'.comp hsub).norm.mul (hgs2.sub hgs1).norm)
    refine Integrable.mono' henv hmeas.aestronglyMeasurable ?_
    have hae1 : ∀ᵐ p : Euc d × Euc d ∂((volume : Measure (Euc d)).prod volume), p.1 ≠ y :=
      Measure.quasiMeasurePreserving_fst.ae hae
    have hae2 : ∀ᵐ p : Euc d × Euc d ∂((volume : Measure (Euc d)).prod volume), p.2 ≠ y :=
      Measure.quasiMeasurePreserving_snd.ae hae
    filter_upwards [hae1, hae2] with p hp1 hp2
    have hnn : 0 ≤ rho p.1 * rho p.2 *
        (‖rieszKernelGrad d (criticalS d) (p.1 - p.2)‖ * ‖s82p2_gt Q p.2 y - s82p2_gt Q p.1 y‖) :=
      mul_nonneg (mul_nonneg (hρ0 _) (hρ0 _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hrhs0 : 0 ≤ Ce * (A * jbracket y ^ (2 * M)) *
        ((rho p.1 * rho p.2 * (jbracket p.1 ^ (2 * M) * jbracket p.2 ^ (2 * M) *
            (pole p.1 p.2 * pole p.1 y))) +
          ((fun p : Euc d × Euc d => rho p.1 * rho p.2 * (jbracket p.1 ^ (2 * M) * jbracket p.2 ^ (2 * M) *
            (pole p.1 p.2 * pole p.1 y))) ∘ Prod.swap) p) := by
      refine mul_nonneg (mul_nonneg hCe0 (mul_nonneg hA (u_jb_rpow_pos _ y).le)) (add_nonneg ?_ ?_)
      · exact mul_nonneg (mul_nonneg (hρ0 _) (hρ0 _)) (mul_nonneg (mul_nonneg (u_jb_rpow_pos _ _).le
          (u_jb_rpow_pos _ _).le) (mul_nonneg (by linarith [u_pole_pos p.1 p.2]) (by linarith [u_pole_pos p.1 y])))
      · exact mul_nonneg (mul_nonneg (hρ0 _) (hρ0 _)) (mul_nonneg (mul_nonneg (u_jb_rpow_pos _ _).le
          (u_jb_rpow_pos _ _).le) (mul_nonneg (by linarith [u_pole_pos p.swap.1 p.swap.2]) (by linarith [u_pole_pos p.swap.1 y])))
    by_cases hp : p.1 = p.2
    · have : s82p2_gt Q p.2 y - s82p2_gt Q p.1 y = 0 := by rw [hp]; simp
      rw [this, norm_zero, mul_zero, mul_zero]
      exact hrhs0
    · have hedge := u_edge_norm hd hM hA hQ (u := p.1) (v := p.2) (w := y) hp hp1 hp2
      rw [norm_sub_rev (s82p2_gt Q p.2 y) (s82p2_gt Q p.1 y)]
      have e : Ce * (A * jbracket y ^ (2 * M)) *
        ((rho p.1 * rho p.2 * (jbracket p.1 ^ (2 * M) * jbracket p.2 ^ (2 * M) *
            (pole p.1 p.2 * pole p.1 y))) +
          ((fun p : Euc d × Euc d => rho p.1 * rho p.2 * (jbracket p.1 ^ (2 * M) * jbracket p.2 ^ (2 * M) *
            (pole p.1 p.2 * pole p.1 y))) ∘ Prod.swap) p) =
        rho p.1 * rho p.2 * (Ce * (A * uW M p.1 p.2 y * (pole p.1 p.2 * (pole p.1 y + pole p.2 y)))) := by
        simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
        rw [u_pole_symm p.2 p.1]
        unfold uW
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hedge (mul_nonneg (hρ0 _) (hρ0 _))

end HRS.MS.S82U
