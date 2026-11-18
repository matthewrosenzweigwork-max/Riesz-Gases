import HRS.MS.R26T8AA01i
import HRS.MS.R26T8AP11g16
import HRS.MS.R26T8AP11g17
import HRS.MS.R26T8AP11f8

/-!
# S8.2 T8A A01 (part j): the derivative of a centred row vanishes
If `∫ ρ(z) Q(u,z) dz = 0` for all `u` (`Q` conormal, `ρ` thermal), then `∫ ρ(z) ∂_{x_j}Q(x,z) dz = 0` for every `x`.
Weak form (test function `φ`, field IBP `r26t8a_g10_ibp_field`, Fubini twice) plus continuity of the row of `dx_j Q` (row lemma).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_a01_row_deriv (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ) (ha : 0 < a)
    (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {Q : Euc d → Euc d → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hQ : Conormal (k + 2) b M (sigma - 2) A Q) (hcan : ∀ u, ∫ y, rho y * Q u y = 0) (j : Fin d) (x : Euc d) :
    ∫ z, rho z * r26t8a_dx j Q x z = 0 := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith) ha hbeta
      hrho).1
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  have hrho0 : ∀ x, 0 ≤ rho x := hprob.nonneg
  have hρc : Continuous rho := hρs.continuous
  -- `dx j Q` is conormal
  have hdx : Conormal (k + 1) b M (sigma - 2 + 1) (2 * A) (r26t8a_dx j Q) :=
    r26t8a_f8_dx_conormal hchi hA (k := k + 1) hQ j
  have hdx0 : Conormal 0 b M (sigma - 1) (2 * A) (r26t8a_dx j Q) := by
    have := r26t8a_conormal_mono (k := 0) (k' := k + 1) (by omega) hdx
    have e : sigma - 2 + 1 = sigma - 1 := by ring
    rw [e] at this; exact this
  -- continuity of the row of `dx j Q`
  have hrowc : Continuous (fun x => ∫ z, rho z * r26t8a_dx j Q x z) := by
    obtain ⟨Cρ, cρ, hCρ, hcρ, hρb⟩ := r26t8a_f23_rho_unif (ρ := rho)
      (HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith) ha hbeta hrho).2 0
    obtain ⟨Kp, hKp0, hKp⟩ := r26t8a_f25_rho_poly hCρ hcρ hρb (M + (d : ℝ) + 1)
    obtain ⟨Crow, hCrow0, hrow⟩ := r26t8a_row_lemma hd 0 b M (sigma - 1) hM (by linarith) Kp hKp0
    have := (hrow rho (hρs.of_le (by exact_mod_cast le_top)) hKp (r26t8a_dx j Q) (2 * A) (by positivity) hdx0).1
    exact this.continuous
  -- weights
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
  obtain ⟨sp, hsp⟩ : ∃ sp : ℝ, sp = max (sigma - 1) 0 := ⟨_, rfl⟩
  have hsp0 : 0 ≤ sp := by rw [hsp]; exact le_max_right _ _
  have hsp1 : sigma - 1 ≤ sp := by rw [hsp]; exact le_max_left _ _
  have hspd : sp < d := by rw [hsp]; exact max_lt (by linarith) (by linarith)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (sp + d) / 2 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsd2 : s < d := by rw [hs]; linarith
  have hσs : sigma - 1 < s := by rw [hs]; linarith
  have hσs2 : sigma - 2 < s := by linarith
  obtain ⟨Cq1, hCq10, hCq1⟩ := r26t8a_f25_pt_bound (d := d) b hσs hs0
  obtain ⟨Cq2, hCq20, hCq2⟩ := r26t8a_f25_pt_bound (d := d) b hσs2 hs0
  -- joint measurability
  have hoffm : MeasurableSet {p : Euc d × Euc d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hres : (volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2} =
      volume.prod volume := Measure.restrict_eq_self_of_ae_mem (r26t8a_g11_diag_null hd)
  have hae2 : ∀ᵐ p : Euc d × Euc d ∂(volume.prod volume), p.1 ≠ p.2 := r26t8a_g11_diag_null hd
  have hDm : AEStronglyMeasurable (fun p : Euc d × Euc d => r26t8a_dx j Q p.1 p.2) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (Function.uncurry (r26t8a_dx j Q))
        ((volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2}) :=
      hdx.1.continuousOn.aestronglyMeasurable hoffm
    rw [hres] at h1
    exact h1
  have hQm : AEStronglyMeasurable (fun p : Euc d × Euc d => Q p.1 p.2) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (Function.uncurry Q)
        ((volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2}) :=
      hQ.1.continuousOn.aestronglyMeasurable hoffm
    rw [hres] at h1
    exact h1
  -- weak identity
  have hweak : ∀ φ : Euc d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x * ∫ z, rho z * r26t8a_dx j Q x z = 0 := by
    intro φ hφ hφc
    set ψ : Euc d → ℝ := fun x => fderiv ℝ φ x (EuclideanSpace.single j 1) with hψ
    have hψc : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψs : HasCompactSupport ψ := by
      have := (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) (by simp)
      exact this
    -- first product
    set W1 : Euc d → ℝ := fun x => 2 * A * Cq1 * (φ x * jbracket x ^ M) with hW1
    have hW1c : Continuous W1 := continuous_const.mul (hφ.continuous.mul (s85_jb_rpow_continuous M))
    have hW1s : HasCompactSupport W1 := (hφc.mul_right (f' := fun x => jbracket x ^ M)).mul_left
    have hW1i : Integrable W1 := hW1c.integrable_of_hasCompactSupport hW1s
    have hdom1 := (r26t8a_g3_prod_int hd hs0 hsd2 ha'0 hKa ha'c ha'i hW1i).1
    have hF1 : Integrable (fun p : Euc d × Euc d => φ p.1 * (rho p.2 * r26t8a_dx j Q p.1 p.2)) (volume.prod volume) := by
      refine Integrable.mono' hdom1 ?_ ?_
      · exact ((hφ.continuous.comp continuous_fst).aestronglyMeasurable).mul
          (((hρc.comp continuous_snd).aestronglyMeasurable).mul hDm)
      · filter_upwards [hae2] with p hp
        have hpt := hCq1 (by positivity : 0 ≤ 2 * A) hdx0 p.1 p.2 hp
        have hr0 : 0 ≤ 1 + ‖p.1 - p.2‖ ^ (-s) := by
          have := Real.rpow_nonneg (norm_nonneg (p.1 - p.2)) (-s); linarith
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hrho0 p.2)]
        have hW : |W1 p.1| = 2 * A * Cq1 * (jbracket p.1 ^ M * |φ p.1|) := by
          rw [hW1]; simp only
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * A * Cq1), abs_mul,
            abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos p.1).le _)]
          ring
        rw [hW]
        have hpw : HRS.MS.Phase2S82.pairWeight M p.1 p.2 = jbracket p.1 ^ M * jbracket p.2 ^ M := rfl
        rw [hpw] at hpt
        calc |φ p.1| * (rho p.2 * |r26t8a_dx j Q p.1 p.2|)
            ≤ |φ p.1| * (rho p.2 * (2 * A * Cq1 * (jbracket p.1 ^ M * jbracket p.2 ^ M) * (1 + ‖p.1 - p.2‖ ^ (-s)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpt (hrho0 _)) (abs_nonneg _)
          _ = _ := by rw [ha']; ring
    have hswap1 : ∫ x, ∫ z, φ x * (rho z * r26t8a_dx j Q x z) = ∫ z, ∫ x, φ x * (rho z * r26t8a_dx j Q x z) :=
      integral_integral_swap (f := fun x z => φ x * (rho z * r26t8a_dx j Q x z)) hF1
    -- second product
    set W2 : Euc d → ℝ := fun x => A * Cq2 * (jbracket x ^ M * ψ x) with hW2
    have hW2c : Continuous W2 := continuous_const.mul ((s85_jb_rpow_continuous M).mul hψc)
    have hW2s : HasCompactSupport W2 := (hψs.mul_left (f := fun x => jbracket x ^ M)).mul_left
    have hW2i : Integrable W2 := hW2c.integrable_of_hasCompactSupport hW2s
    have hdom2 := (r26t8a_g3_prod_int hd hs0 hsd2 ha'0 hKa ha'c ha'i hW2i).2
    have hRcs : ContinuousOn (fun p : Euc d × Euc d => Q p.2 p.1) {p : Euc d × Euc d | p.1 ≠ p.2} :=
      hQ.1.continuousOn.comp (continuous_snd.prodMk continuous_fst).continuousOn (fun p hp => Ne.symm hp)
    have hQms : AEStronglyMeasurable (fun p : Euc d × Euc d => Q p.2 p.1) (volume.prod volume) := by
      have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => Q p.2 p.1)
          ((volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2}) :=
        hRcs.aestronglyMeasurable hoffm
      rw [hres] at h1
      exact h1
    have hG2 : Integrable (fun p : Euc d × Euc d => rho p.1 * (Q p.2 p.1 * ψ p.2)) (volume.prod volume) := by
      refine Integrable.mono' hdom2 ?_ ?_
      · exact ((hρc.comp continuous_fst).aestronglyMeasurable).mul
          (hQms.mul (hψc.comp continuous_snd).aestronglyMeasurable)
      · filter_upwards [hae2] with p hp
        have hpt := hCq2 hA hQ p.2 p.1 (Ne.symm hp)
        have hr0 : 0 ≤ 1 + ‖p.1 - p.2‖ ^ (-s) := by
          have := Real.rpow_nonneg (norm_nonneg (p.1 - p.2)) (-s); linarith
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hrho0 p.1)]
        have hn : ‖p.2 - p.1‖ = ‖p.1 - p.2‖ := norm_sub_rev _ _
        rw [hn] at hpt
        have hW : |W2 p.2| = A * Cq2 * (jbracket p.2 ^ M * |ψ p.2|) := by
          rw [hW2]; simp only
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ A * Cq2), abs_mul,
            abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos p.2).le _)]
        rw [hW]
        have hpw : HRS.MS.Phase2S82.pairWeight M p.2 p.1 = jbracket p.2 ^ M * jbracket p.1 ^ M := rfl
        rw [hpw] at hpt
        calc rho p.1 * (|Q p.2 p.1| * |ψ p.2|)
            ≤ rho p.1 * ((A * Cq2 * (jbracket p.2 ^ M * jbracket p.1 ^ M) * (1 + ‖p.1 - p.2‖ ^ (-s))) * |ψ p.2|) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpt (abs_nonneg _)) (hrho0 _)
          _ = _ := by rw [ha']; ring
    have hswap2 : ∫ z, ∫ x, rho z * (Q x z * ψ x) = ∫ x, ∫ z, rho z * (Q x z * ψ x) :=
      integral_integral_swap (f := fun z x => rho z * (Q x z * ψ x)) hG2
    have hzero : ∀ x, ∫ z, rho z * (Q x z * ψ x) = 0 := by
      intro x
      have : ∀ z, rho z * (Q x z * ψ x) = (rho z * Q x z) * ψ x := fun z => by ring
      simp only [this]
      rw [integral_mul_const, hcan x, zero_mul]
    -- field IBP in the first variable
    have hw1 : ∀ z, ∫ x, φ x * r26t8a_dx j Q x z = -∫ x, Q x z * ψ x := by
      intro z
      set w : Euc d → Euc d := fun x => φ x • EuclideanSpace.single j (1 : ℝ) with hw
      have hw1c : ContDiff ℝ 1 w := (hφ.of_le (by exact_mod_cast le_top)).smul contDiff_const
      have hwc : HasCompactSupport w := (hφc.smul_right (f' := fun _ => (EuclideanSpace.single j (1 : ℝ) : Euc d)))
      obtain ⟨-, -, hfld⟩ := r26t8a_g10_ibp_field hd k b hM hsd hA hQ z hw1c hwc
      have e1 : ∀ x, ∑ i : Fin d, w x i * r26t8a_dx i Q x z = φ x * r26t8a_dx j Q x z := by
        intro x
        simp only [hw, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply]
        simp
      have e2 : ∀ x, ∑ i : Fin d, fderiv ℝ w x (EuclideanSpace.single i 1) i = ψ x := by
        intro x
        have hdφ : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
        have : fderiv ℝ w x = (fderiv ℝ φ x).smulRight (EuclideanSpace.single j (1 : ℝ) : Euc d) :=
          fderiv_smul_const hdφ _
        simp only [this, ContinuousLinearMap.smulRight_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply, hψ]
        simp
      simp only [e1, e2] at hfld
      exact hfld
    calc ∫ x, φ x * ∫ z, rho z * r26t8a_dx j Q x z
        = ∫ x, ∫ z, φ x * (rho z * r26t8a_dx j Q x z) := by
          congr 1; funext x; rw [← integral_const_mul]
      _ = ∫ z, ∫ x, φ x * (rho z * r26t8a_dx j Q x z) := hswap1
      _ = ∫ z, rho z * ∫ x, φ x * r26t8a_dx j Q x z := by
          congr 1; funext z; rw [← integral_const_mul]; congr 1; funext x; ring
      _ = ∫ z, ∫ x, rho z * (-(Q x z * ψ x)) := by
          congr 1; funext z; rw [hw1 z, ← integral_neg, ← integral_const_mul]
      _ = -∫ z, ∫ x, rho z * (Q x z * ψ x) := by
          rw [← integral_neg]; congr 1; funext z; rw [← integral_neg]; congr 1; funext x; ring
      _ = 0 := by rw [hswap2]; simp only [hzero, integral_zero, neg_zero]
  have hae0 : ∀ᵐ x : Euc d ∂volume, ∫ z, rho z * r26t8a_dx j Q x z = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hrowc.locallyIntegrable ?_
    intro g hg hgc
    simpa only [smul_eq_mul] using hweak g hg hgc
  have := (hrowc.ae_eq_iff_eq volume continuous_const).1 hae0
  exact congrFun this x

end HRS.MS.R26T8A
