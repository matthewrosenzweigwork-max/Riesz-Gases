import HRS.MS.R26T8AP11g15
import HRS.MS.R26T8AP11g16
import HRS.MS.R26T8AP11g12

/-!
# S8.2 T8A P11g (part 17): the mean of the `x`-averaged row vanishes
If `∫ ρ(y) R(u,y) dy = 0` for all `u`, then `∫ (∫ oneJ(R(·,z)) dμ) dμ(z) = 0`.
By the row identity `m(z) = -∫ ⟨F, ∇_xR(·,z)⟩ dμ = ∫ R(u,z) div(ρF)(u) du` (field IBP), Fubini and row centring.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_g17_mean_zero (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ) (ha : 0 < a)
    (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {R : Euc d → Euc d → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hQ : Conormal (k + 2) b M (sigma - 2) A R) (hcan : ∀ u, ∫ y, rho y * R u y = 0) :
    ∫ z, (∫ x, oneJ (critCoeff d a beta rho) (fun u => R u z) x ∂(HRS.Whole.withDensityReal rho))
      ∂(HRS.Whole.withDensityReal rho) = 0 := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith) ha hbeta
      hrho).1
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  have hrho0 : ∀ x, 0 ≤ rho x := hprob.nonneg
  have hρc : Continuous rho := hρs.continuous
  -- the field `w = ρ F`
  obtain ⟨hFs, hFb⟩ := r26t8a_thermal_force d hd a beta ha hbeta rho hrho
  obtain ⟨CF0, hCF00, hCF0⟩ := hFb 0
  obtain ⟨CF1, hCF10, hCF1⟩ := hFb 1
  have hF0 : ∀ u, ‖forceMean rho u‖ ≤ CF0 := fun u => by
    have := hCF0 u
    rw [norm_iteratedFDeriv_zero] at this
    linarith [norm_nonneg (fderiv ℝ (iteratedFDeriv ℝ 0 (forceMean rho)) u u)]
  have hF1 : ∀ u, ‖fderiv ℝ (forceMean rho) u‖ ≤ CF1 := fun u => by
    have := hCF1 u
    rw [norm_iteratedFDeriv_one] at this
    linarith [norm_nonneg (fderiv ℝ (iteratedFDeriv ℝ 1 (forceMean rho)) u u)]
  set w : Euc d → Euc d := fun u => rho u • forceMean rho u with hwdef
  have hw1 : ContDiff ℝ 1 w :=
    (hρs.of_le (by exact_mod_cast le_top)).smul (hFs.of_le (by exact_mod_cast le_top))
  have hwb : ∀ u, ‖w u‖ ≤ (C * CF0) * Real.exp (-c * ‖u‖ ^ 2) := fun u => by
    simp only [hwdef]
    rw [norm_smul, Real.norm_eq_abs]
    calc |rho u| * ‖forceMean rho u‖ ≤ (C * Real.exp (-c * ‖u‖ ^ 2)) * CF0 :=
          mul_le_mul (hb u).1 (hF0 u) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hdwb : ∀ u, ‖fderiv ℝ w u‖ ≤ (C * CF1 + C * CF0) * Real.exp (-c * ‖u‖ ^ 2) := fun u => by
    have hdρ : DifferentiableAt ℝ rho u := (hρs.differentiable (by simp)) u
    have hdF : DifferentiableAt ℝ (forceMean rho) u := (hFs.differentiable (by simp)) u
    simp only [hwdef]
    rw [fderiv_fun_smul hdρ hdF]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖rho u • fderiv ℝ (forceMean rho) u‖ ≤ |rho u| * ‖fderiv ℝ (forceMean rho) u‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    have e2 : ‖(fderiv ℝ rho u).smulRight (forceMean rho u)‖ ≤ ‖fderiv ℝ rho u‖ * ‖forceMean rho u‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
    have h1 : |rho u| * ‖fderiv ℝ (forceMean rho) u‖ ≤ (C * Real.exp (-c * ‖u‖ ^ 2)) * CF1 :=
      mul_le_mul (hb u).1 (hF1 u) (norm_nonneg _) (by positivity)
    have h2 : ‖fderiv ℝ rho u‖ * ‖forceMean rho u‖ ≤ (C * Real.exp (-c * ‖u‖ ^ 2)) * CF0 :=
      mul_le_mul (hb u).2 (hF0 u) (norm_nonneg _) (by positivity)
    nlinarith
  set divw : Euc d → ℝ := fun u => ∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j with hdivw
  have hdivwc : Continuous divw := by
    refine continuous_finset_sum _ fun j _ => ?_
    have hj : Continuous fun v : Euc d => v j := (EuclideanSpace.proj j).continuous
    exact hj.comp ((hw1.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdivb : ∀ u, |divw u| ≤ d * ((C * CF1 + C * CF0) * Real.exp (-c * ‖u‖ ^ 2)) := fun u =>
    (r26t8a_divh_le w u).trans (mul_le_mul_of_nonneg_left (hdwb u) (by positivity))
  -- the row identity: `m z = ∫ R u z * divw u`
  have hm : ∀ z : Euc d, ∫ x, oneJ (critCoeff d a beta rho) (fun u => R u z) x
      ∂(HRS.Whole.withDensityReal rho) = ∫ u, R u z * divw u := by
    intro z
    rw [(r26t8a_g5_row d hd k b a beta M sigma ha hbeta hM hsd rho hrho R A hA hQ z).2,
      r26t8a_f25_wd_integral hprob]
    obtain ⟨-, -, hfld⟩ := r26t8a_g16_ibp_gauss hd k b hM hsd hA hQ z hw1 hc (by positivity)
      (by positivity) hwb hdwb
    have h2 : ∀ u, rho u * inner ℝ (forceMean rho u) (pairGradX R u z) =
        ∑ j : Fin d, w u j * r26t8a_dx j R u z := by
      intro u
      simp only [hwdef, PiLp.smul_apply, smul_eq_mul, pairGradX, PiLp.inner_apply, RCLike.inner_apply,
        conj_trivial, movtr_gradient_apply, r26t8a_dx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [h2]
    rw [hfld, neg_neg]
  -- Fubini
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_p10a_poly_gauss M hc
  set a' : Euc d → ℝ := fun y => rho y * jbracket y ^ M with ha'
  have ha'0 : ∀ y, 0 ≤ a' y := fun y => mul_nonneg (hrho0 y) (Real.rpow_nonneg (s83_jb_pos y).le _)
  have ha'c : Continuous a' := hρc.mul (s85_jb_rpow_continuous M)
  have ha'b : ∀ y, a' y ≤ C * Cp * Real.exp (-(c / 2) * ‖y‖ ^ 2) := by
    intro y
    have h1 : jbracket y ^ M ≤ (1 + ‖y‖) ^ M :=
      Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_one_add y) hM
    have h2 := hCp ‖y‖ (norm_nonneg _)
    have h3 : rho y ≤ C * Real.exp (-c * ‖y‖ ^ 2) := (le_abs_self _).trans (hb y).1
    calc a' y = rho y * jbracket y ^ M := rfl
      _ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (1 + ‖y‖) ^ M :=
          mul_le_mul h3 h1 (Real.rpow_nonneg (s83_jb_pos y).le _) (by positivity)
      _ = C * ((1 + ‖y‖) ^ M * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ ≤ C * (Cp * Real.exp (-(c / 2) * ‖y‖ ^ 2)) := mul_le_mul_of_nonneg_left h2 hC
      _ = _ := by ring
  have hKa : ∀ y, a' y ≤ C * Cp := fun y => by
    refine (ha'b y).trans ?_
    have : Real.exp (-(c / 2) * ‖y‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])
    have h0 : 0 ≤ C * Cp := by positivity
    nlinarith
  have ha'i : Integrable a' := by
    refine Integrable.mono' ((r26t8a_p10a_gauss_int (d := d) (b := c / 2) (by linarith)).const_mul (C * Cp))
      ha'c.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (ha'0 y)]; exact ha'b y
  obtain ⟨sp, hsp⟩ : ∃ sp : ℝ, sp = max (sigma - 2) 0 := ⟨_, rfl⟩
  have hsp0 : 0 ≤ sp := by rw [hsp]; exact le_max_right _ _
  have hsp1 : sigma - 2 ≤ sp := by rw [hsp]; exact le_max_left _ _
  have hspd : sp < d := by rw [hsp]; exact max_lt (by linarith) (by linarith)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (sp + d) / 2 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsd2 : s < d := by rw [hs]; linarith
  have hσs : sigma - 2 < s := by rw [hs]; linarith
  obtain ⟨Cq, hCq0, hCq⟩ := r26t8a_f25_pt_bound (d := d) b hσs hs0
  set W2 : Euc d → ℝ := fun u => A * Cq * jbracket u ^ M * divw u with hW2
  have hW2c : Continuous W2 := (continuous_const.mul (s85_jb_rpow_continuous M)).mul hdivwc
  have hW2i : Integrable W2 := by
    obtain ⟨Cp2, hCp20, hCp2⟩ := r26t8a_p10a_poly_gauss M hc
    refine Integrable.mono' ((r26t8a_p10a_gauss_int (d := d) (b := c / 2) (by linarith)).const_mul
      (A * Cq * (d * ((C * CF1 + C * CF0) * Cp2)))) hW2c.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 : jbracket u ^ M ≤ (1 + ‖u‖) ^ M :=
      Real.rpow_le_rpow (s83_jb_pos u).le (s83_jb_le_one_add u) hM
    have h2 := hCp2 ‖u‖ (norm_nonneg _)
    have hj0 : 0 ≤ jbracket u ^ M := Real.rpow_nonneg (s83_jb_pos u).le _
    have hE := Real.exp_pos (-c * ‖u‖ ^ 2)
    rw [Real.norm_eq_abs, hW2]
    simp only
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ A * Cq * jbracket u ^ M)]
    have hd0 := hdivb u
    calc A * Cq * jbracket u ^ M * |divw u|
        ≤ A * Cq * jbracket u ^ M * (d * ((C * CF1 + C * CF0) * Real.exp (-c * ‖u‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hd0 (by positivity)
      _ ≤ A * Cq * (1 + ‖u‖) ^ M * (d * ((C * CF1 + C * CF0) * Real.exp (-c * ‖u‖ ^ 2))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
      _ = A * Cq * (d * (C * CF1 + C * CF0)) * ((1 + ‖u‖) ^ M * Real.exp (-c * ‖u‖ ^ 2)) := by ring
      _ ≤ A * Cq * (d * (C * CF1 + C * CF0)) * (Cp2 * Real.exp (-(c / 2) * ‖u‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hdom2 := (r26t8a_g3_prod_int hd hs0 hsd2 ha'0 hKa ha'c ha'i hW2i).2
  have hRc : ContinuousOn (Function.uncurry R) {p : Euc d × Euc d | p.1 ≠ p.2} := hQ.1.continuousOn
  have hoffm : MeasurableSet {p : Euc d × Euc d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hres : (volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2} =
      volume.prod volume := Measure.restrict_eq_self_of_ae_mem (r26t8a_g11_diag_null hd)
  have hae2 : ∀ᵐ p : Euc d × Euc d ∂(volume.prod volume), p.1 ≠ p.2 := r26t8a_g11_diag_null hd
  have hRcs : ContinuousOn (fun p : Euc d × Euc d => R p.2 p.1) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hRc.comp (continuous_snd.prodMk continuous_fst).continuousOn (fun p hp => Ne.symm hp)
  have hRms : AEStronglyMeasurable (fun p : Euc d × Euc d => R p.2 p.1) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => R p.2 p.1)
        ((volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2}) :=
      hRcs.aestronglyMeasurable hoffm
    rw [hres] at h1
    exact h1
  have hG2 : Integrable (fun p : Euc d × Euc d => rho p.1 * (R p.2 p.1 * divw p.2)) (volume.prod volume) := by
    refine Integrable.mono' hdom2 ?_ ?_
    · exact ((hρc.comp continuous_fst).aestronglyMeasurable).mul
        (hRms.mul (hdivwc.comp continuous_snd).aestronglyMeasurable)
    · filter_upwards [hae2] with p hp
      have hpt := hCq hA hQ p.2 p.1 (Ne.symm hp)
      have hr0 : 0 ≤ 1 + ‖p.1 - p.2‖ ^ (-s) := by
        have := Real.rpow_nonneg (norm_nonneg (p.1 - p.2)) (-s); linarith
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hrho0 p.1)]
      have hn : ‖p.2 - p.1‖ = ‖p.1 - p.2‖ := norm_sub_rev _ _
      rw [hn] at hpt
      have hW : |W2 p.2| = A * Cq * jbracket p.2 ^ M * |divw p.2| := by
        rw [hW2]; simp only
        rw [abs_mul, abs_of_nonneg (by have := Real.rpow_nonneg (s83_jb_pos p.2).le M; positivity)]
      rw [hW]
      have hpw : HRS.MS.Phase2S82.pairWeight M p.2 p.1 = jbracket p.2 ^ M * jbracket p.1 ^ M := rfl
      rw [hpw] at hpt
      calc rho p.1 * (|R p.2 p.1| * |divw p.2|)
          ≤ rho p.1 * ((A * Cq * (jbracket p.2 ^ M * jbracket p.1 ^ M) * (1 + ‖p.1 - p.2‖ ^ (-s))) * |divw p.2|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpt (abs_nonneg _)) (hrho0 _)
        _ = _ := by rw [ha']; ring
  have hswap : ∫ y, ∫ u, rho y * (R u y * divw u) = ∫ u, ∫ y, rho y * (R u y * divw u) :=
    integral_integral_swap (f := fun y u => rho y * (R u y * divw u)) hG2
  have hzero : ∀ u, ∫ y, rho y * (R u y * divw u) = 0 := by
    intro u
    have : ∀ y, rho y * (R u y * divw u) = (rho y * R u y) * divw u := fun y => by ring
    simp only [this]
    rw [integral_mul_const, hcan u, zero_mul]
  rw [r26t8a_f25_wd_integral hprob]
  calc ∫ z, rho z * ∫ x, oneJ (critCoeff d a beta rho) (fun u => R u z) x ∂(HRS.Whole.withDensityReal rho)
      = ∫ z, ∫ u, rho z * (R u z * divw u) := by
        congr 1; funext z
        rw [hm z, ← integral_const_mul]
    _ = ∫ u, ∫ y, rho y * (R u y * divw u) := hswap
    _ = 0 := by simp only [hzero, integral_zero]

end HRS.MS.R26T8A
