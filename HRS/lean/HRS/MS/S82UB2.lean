import HRS.MS.S82UB1

/-!
# S8.2 A01 (S82U): the antisymmetric double integral
`∬ ρ(x)ρ(z) <∇g(x-z), ψ(z) - ψ(x)> = -2 ∫ ρ <ψ, F_μ>`, by truncating `|x-z| > ε`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

lemma u_Fe_measurable {d : ℕ} {ε : ℝ} {rho : Euc d → ℝ} (hρ : Measurable rho) :
    Measurable (uFe ε rho) := by
  have hG := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hsub : Measurable (fun p : Euc d × Euc d => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hF : Measurable (fun p : Euc d × Euc d =>
      if ε < ‖p.1 - p.2‖ then rho p.2 • rieszKernelGrad d (criticalS d) (p.1 - p.2) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const (measurable_norm.comp hsub))
      ((hρ.comp measurable_snd).smul (hG.comp hsub)) measurable_const
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- The truncated reflection identity `∫_x 1_{|x-z|>ε} ρ(x) ∇g(x-z) dx = -F_ε(z)`. -/
lemma u_Fe_reflect {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (rho : Euc d → ℝ) (z : Euc d) :
    ∫ x, (if ε < ‖x - z‖ then rho x • rieszKernelGrad d (criticalS d) (x - z) else 0) = -uFe ε rho z := by
  unfold uFe
  rw [← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show (if ε < ‖x - z‖ then rho x • rieszKernelGrad d (criticalS d) (x - z) else 0) =
    -(if ε < ‖z - x‖ then rho x • rieszKernelGrad d (criticalS d) (z - x) else 0)
  rw [norm_sub_rev z x]
  by_cases h : ε < ‖x - z‖
  · have hne : x ≠ z := fun e => by rw [e, sub_self, norm_zero] at h; linarith
    rw [if_pos h, if_pos h, u_grad_odd hne, smul_neg, neg_neg]
  · rw [if_neg h, if_neg h]; simp

theorem u_dsym {d : ℕ} (hd : 2 ≤ d) {rho : Euc d → ℝ} {Λ : ℝ} (hF : UForce d rho Λ)
    {ψ : Euc d → Euc d} (hψm : Measurable ψ) (hψ1 : Integrable (fun z => rho z * ‖ψ z‖))
    (hD : Integrable (fun p : Euc d × Euc d =>
      rho p.1 * rho p.2 * (‖rieszKernelGrad d (criticalS d) (p.1 - p.2)‖ * ‖ψ p.2 - ψ p.1‖))
      ((volume : Measure (Euc d)).prod volume)) :
    ∫ p : Euc d × Euc d, rho p.1 * rho p.2 *
        inner ℝ (rieszKernelGrad d (criticalS d) (p.1 - p.2)) (ψ p.2 - ψ p.1)
        ∂((volume : Measure (Euc d)).prod volume) =
      -2 * ∫ x, rho x * inner ℝ (ψ x) (forceMean rho x) := by
  set Gf := rieszKernelGrad d (criticalS d) with hGf
  have hρm := hF.prob.measurable
  have hρ0 := hF.prob.nonneg
  have hint : Integrable rho := integrable_of_integral_eq_one hF.prob.integral_one
  have hG : Measurable Gf := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hsub : Measurable (fun p : Euc d × Euc d => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hGs : Measurable (fun p : Euc d × Euc d => Gf (p.1 - p.2)) := hG.comp hsub
  have hψ1' : Measurable (fun p : Euc d × Euc d => ψ p.1) := hψm.comp measurable_fst
  have hψ2' : Measurable (fun p : Euc d × Euc d => ψ p.2) := hψm.comp measurable_snd
  have hr1 : Measurable (fun p : Euc d × Euc d => rho p.1) := hρm.comp measurable_fst
  have hr2 : Measurable (fun p : Euc d × Euc d => rho p.2) := hρm.comp measurable_snd
  set e : Euc d × Euc d → ℝ := fun p => rho p.1 * rho p.2 *
    inner ℝ (Gf (p.1 - p.2)) (ψ p.2 - ψ p.1) with he
  set a1 : Euc d × Euc d → ℝ := fun p => rho p.1 * rho p.2 * inner ℝ (Gf (p.1 - p.2)) (ψ p.2) with ha1
  set a2 : Euc d × Euc d → ℝ := fun p => rho p.1 * rho p.2 * inner ℝ (Gf (p.1 - p.2)) (ψ p.1) with ha2
  have hea : ∀ p, e p = a1 p - a2 p := fun p => by
    simp only [he, ha1, ha2, inner_sub_right]; ring
  have hem : Measurable e := (hr1.mul hr2).mul (Measurable.inner hGs (hψ2'.sub hψ1'))
  have ha1m : Measurable a1 := (hr1.mul hr2).mul (Measurable.inner hGs hψ2')
  have ha2m : Measurable a2 := (hr1.mul hr2).mul (Measurable.inner hGs hψ1')
  -- the truncated pieces
  have trunc : ∀ ε : ℝ, 0 < ε → ∫ p, (if ε < ‖p.1 - p.2‖ then e p else 0)
        ∂((volume : Measure (Euc d)).prod volume) =
      -2 * ∫ x, rho x * inner ℝ (ψ x) (uFe ε rho x) := by
    intro ε hε
    set c := HRS.Whole.movtr_sigma (criticalS d) * ε ^ (-criticalS d - 1) with hc
    have hc0 : 0 ≤ c := mul_nonneg (s82t_sigma_nonneg _ (by unfold criticalS; positivity))
      (Real.rpow_nonneg hε.le _)
    have hm : MeasurableSet {p : Euc d × Euc d | ε < ‖p.1 - p.2‖} :=
      measurableSet_lt measurable_const (measurable_norm.comp hsub)
    have hI1 : Integrable (fun p : Euc d × Euc d => if ε < ‖p.1 - p.2‖ then a1 p else 0)
        ((volume : Measure (Euc d)).prod volume) := by
      refine Integrable.mono' ((hint.mul_prod hψ1).const_mul c)
        (Measurable.ite hm ha1m measurable_const).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      by_cases h : ε < ‖p.1 - p.2‖
      · rw [if_pos h, ha1]
        simp only
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hρ0 _), abs_of_nonneg (hρ0 _)]
        have h1 := abs_real_inner_le_norm (Gf (p.1 - p.2)) (ψ p.2)
        have h2 := u_G_norm_le hε h
        have h3 : |inner ℝ (Gf (p.1 - p.2)) (ψ p.2)| ≤ c * ‖ψ p.2‖ :=
          h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
        calc rho p.1 * rho p.2 * |inner ℝ (Gf (p.1 - p.2)) (ψ p.2)|
            ≤ rho p.1 * rho p.2 * (c * ‖ψ p.2‖) :=
              mul_le_mul_of_nonneg_left h3 (mul_nonneg (hρ0 _) (hρ0 _))
          _ = c * (rho p.1 * (rho p.2 * ‖ψ p.2‖)) := by ring
      · rw [if_neg h]; simp only [norm_zero]
        exact mul_nonneg hc0 (mul_nonneg (hρ0 _) (mul_nonneg (hρ0 _) (norm_nonneg _)))
    have hI2 : Integrable (fun p : Euc d × Euc d => if ε < ‖p.1 - p.2‖ then a2 p else 0)
        ((volume : Measure (Euc d)).prod volume) := by
      refine Integrable.mono' ((hψ1.mul_prod hint).const_mul c)
        (Measurable.ite hm ha2m measurable_const).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      by_cases h : ε < ‖p.1 - p.2‖
      · rw [if_pos h, ha2]
        simp only
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hρ0 _), abs_of_nonneg (hρ0 _)]
        have h1 := abs_real_inner_le_norm (Gf (p.1 - p.2)) (ψ p.1)
        have h2 := u_G_norm_le hε h
        have h3 : |inner ℝ (Gf (p.1 - p.2)) (ψ p.1)| ≤ c * ‖ψ p.1‖ :=
          h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
        calc rho p.1 * rho p.2 * |inner ℝ (Gf (p.1 - p.2)) (ψ p.1)|
            ≤ rho p.1 * rho p.2 * (c * ‖ψ p.1‖) :=
              mul_le_mul_of_nonneg_left h3 (mul_nonneg (hρ0 _) (hρ0 _))
          _ = c * ((rho p.1 * ‖ψ p.1‖) * rho p.2) := by ring
      · rw [if_neg h]; simp only [norm_zero]
        exact mul_nonneg hc0 (mul_nonneg (mul_nonneg (hρ0 _) (norm_nonneg _)) (hρ0 _))
    have hsplit : (fun p : Euc d × Euc d => if ε < ‖p.1 - p.2‖ then e p else 0) =
        fun p => (if ε < ‖p.1 - p.2‖ then a1 p else 0) - (if ε < ‖p.1 - p.2‖ then a2 p else 0) := by
      funext p
      by_cases h : ε < ‖p.1 - p.2‖
      · simp only [if_pos h, hea]
      · simp only [if_neg h, sub_zero]
    -- ∫ t2
    have hT2 : ∫ p, (if ε < ‖p.1 - p.2‖ then a2 p else 0) ∂((volume : Measure (Euc d)).prod volume) =
        ∫ x, rho x * inner ℝ (ψ x) (uFe ε rho x) := by
      rw [integral_prod _ hI2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      have hpt : ∀ z : Euc d, (if ε < ‖x - z‖ then a2 (x, z) else 0) =
          rho x * inner ℝ (ψ x) (if ε < ‖x - z‖ then rho z • Gf (x - z) else 0) := by
        intro z
        by_cases h : ε < ‖x - z‖
        · simp only [if_pos h, ha2, inner_smul_right]
          rw [real_inner_comm (ψ x) (Gf (x - z))]; ring
        · simp [h]
      simp_rw [hpt]
      rw [integral_const_mul, integral_inner (u_trunc_integrable hε hF.prob x)]
      rfl
    have hT1 : ∫ p, (if ε < ‖p.1 - p.2‖ then a1 p else 0) ∂((volume : Measure (Euc d)).prod volume) =
        -∫ x, rho x * inner ℝ (ψ x) (uFe ε rho x) := by
      rw [integral_prod_symm _ hI1]
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      have hpt : ∀ x : Euc d, (if ε < ‖x - z‖ then a1 (x, z) else 0) =
          rho z * inner ℝ (ψ z) (if ε < ‖x - z‖ then rho x • Gf (x - z) else 0) := by
        intro x
        by_cases h : ε < ‖x - z‖
        · simp only [if_pos h, ha1, inner_smul_right]
          rw [real_inner_comm (ψ z) (Gf (x - z))]; ring
        · simp [h]
      simp_rw [hpt]
      have hint' : Integrable (fun x : Euc d => if ε < ‖x - z‖ then rho x • Gf (x - z) else 0) := by
        have := (u_trunc_integrable hε hF.prob z)
        have h2 : Integrable (fun x : Euc d => if ε < ‖z - x‖ then rho x • Gf (z - x) else 0) := this
        have h3 := h2.neg
        refine h3.congr (Eventually.of_forall fun x => ?_)
        simp only [Pi.neg_apply]
        rw [norm_sub_rev z x]
        by_cases h : ε < ‖x - z‖
        · have hne : x ≠ z := fun e => by rw [e, sub_self, norm_zero] at h; linarith
          have hodd := u_grad_odd hne
          rw [← hGf] at hodd
          rw [if_pos h, if_pos h, hodd, smul_neg, neg_neg]
        · rw [if_neg h, if_neg h]; simp
      rw [integral_const_mul, integral_inner hint', u_Fe_reflect hε.le rho z]
      simp [inner_neg_right]
    rw [hsplit, integral_sub hI1 hI2, hT1, hT2]; ring
  -- limit of the truncated double integral
  have hlim1 : Tendsto (fun ε : ℝ => ∫ p, (if ε < ‖p.1 - p.2‖ then e p else 0)
      ∂((volume : Measure (Euc d)).prod volume)) (𝓝[>] 0)
      (𝓝 (∫ p, e p ∂((volume : Measure (Euc d)).prod volume))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p : Euc d × Euc d => rho p.1 * rho p.2 * (‖Gf (p.1 - p.2)‖ * ‖ψ p.2 - ψ p.1‖))
      (Eventually.of_forall fun ε => ?_) ?_ hD ?_
    · exact (Measurable.ite (measurableSet_lt measurable_const (measurable_norm.comp hsub)) hem
        measurable_const).aestronglyMeasurable
    · refine Eventually.of_forall fun ε => Eventually.of_forall fun p => ?_
      have hb : |e p| ≤ rho p.1 * rho p.2 * (‖Gf (p.1 - p.2)‖ * ‖ψ p.2 - ψ p.1‖) := by
        simp only [he]
        rw [abs_mul, abs_of_nonneg (mul_nonneg (hρ0 _) (hρ0 _))]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (mul_nonneg (hρ0 _) (hρ0 _))
      by_cases h : ε < ‖p.1 - p.2‖
      · rw [if_pos h, Real.norm_eq_abs]; exact hb
      · rw [if_neg h, norm_zero]
        exact mul_nonneg (mul_nonneg (hρ0 _) (hρ0 _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · refine Eventually.of_forall fun p => ?_
      by_cases hp : p.1 = p.2
      · have : e p = 0 := by simp [he, hp]
        simp [this]
      · have hzpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp)
        have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ‖p.1 - p.2‖ :=
          (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hzpos))
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [this] with ε hε
        simp [hε]
  -- limit of the truncated force integral
  obtain ⟨K1, hK1⟩ := u_Fe_bdd hd hF
  have hlim2 : Tendsto (fun ε : ℝ => ∫ x, rho x * inner ℝ (ψ x) (uFe ε rho x)) (𝓝[>] 0)
      (𝓝 (∫ x, rho x * inner ℝ (ψ x) (forceMean rho x))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => K1 * (rho x * ‖ψ x‖))
      (Eventually.of_forall fun ε => ?_) ?_ (hψ1.const_mul K1) ?_
    · exact (hρm.mul (Measurable.inner hψm (u_Fe_measurable hρm))).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 _)]
      have h1 := abs_real_inner_le_norm (ψ x) (uFe ε rho x)
      have h2 := hK1 ε hε.1 x
      calc rho x * |inner ℝ (ψ x) (uFe ε rho x)| ≤ rho x * (‖ψ x‖ * K1) :=
            mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))) (hρ0 _)
        _ = K1 * (rho x * ‖ψ x‖) := by ring
    · refine Eventually.of_forall fun x => ?_
      exact (tendsto_const_nhds.inner (u_Fe_tendsto hd hF x)).const_mul (rho x)
  have hlim2' := hlim2.const_mul (-2)
  have hfin : Tendsto (fun ε : ℝ => ∫ p, (if ε < ‖p.1 - p.2‖ then e p else 0)
      ∂((volume : Measure (Euc d)).prod volume)) (𝓝[>] 0)
      (𝓝 (-2 * ∫ x, rho x * inner ℝ (ψ x) (forceMean rho x))) := by
    refine hlim2'.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (trunc ε hε.1).symm
  exact tendsto_nhds_unique hlim1 hfin

end HRS.MS.S82U
