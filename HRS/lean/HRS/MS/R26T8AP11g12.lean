import HRS.MS.R26T8AP11g11

/-!
# S8.2 T8A P11g (part 12): the weak identity for the `y`-averaged source
If `∫ ρ(y) Q(u,y) dy = 0` for all `u`, then for every smooth compactly supported `φ`:
`∫ φ(u) ∫ ρ(y) Stil ρ Q u y dy du = 0`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_g12_weak (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ) (ha : 0 < a)
    (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {Q : Euc d → Euc d → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hQ : Conormal (k + 2) b M (sigma - 2) A Q) (hcan : ∀ u, ∫ y, rho y * Q u y = 0)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ u, φ u * ∫ y, rho y * r26t8a_Stil rho Q u y = 0 := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith) ha hbeta
      hrho).1
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  obtain ⟨e, K, c', he0, hed, hK0, hc', hSb⟩ :=
    r26t8a_g8_S_bound hd k b hM hsd hρs hC hc (fun x => (hb x).1) (fun x => (hb x).2)
  have hrho0 : ∀ x, 0 ≤ rho x := hprob.nonneg
  have hρc : Continuous rho := hρs.continuous
  have hρK : ∀ x, rho x ≤ C := fun x => by
    refine (le_abs_self _).trans ((hb x).1.trans ?_)
    have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])
    nlinarith
  -- the weight `a(y) = ρ(y) jb(y)^M`
  set a' : Euc d → ℝ := fun y => rho y * jbracket y ^ M with ha'
  have ha'0 : ∀ y, 0 ≤ a' y := fun y => mul_nonneg (hrho0 y) (Real.rpow_nonneg (s83_jb_pos y).le _)
  have ha'c : Continuous a' := hρc.mul (s85_jb_rpow_continuous M)
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_p10a_poly_gauss M hc
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
  -- joint measurability of `Stil`
  have hQk : ContDiffOn ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} := hQ.1
  have hSc : ContinuousOn (Function.uncurry (r26t8a_Stil rho Q)) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    (r26t8a_f12_Stil_contDiffOn hQk hρs).continuousOn
  have hQc : ContinuousOn (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} := hQ.1.continuousOn
  have hoffm : MeasurableSet {p : Euc d × Euc d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hres : (volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2} =
      volume.prod volume := Measure.restrict_eq_self_of_ae_mem (r26t8a_g11_diag_null hd)
  have hSm : AEStronglyMeasurable (fun p : Euc d × Euc d => r26t8a_Stil rho Q p.1 p.2) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (Function.uncurry (r26t8a_Stil rho Q))
        ((volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2}) :=
      hSc.aestronglyMeasurable hoffm
    rw [hres] at h1
    exact h1
  have hQm : AEStronglyMeasurable (fun p : Euc d × Euc d => Q p.1 p.2) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (Function.uncurry Q)
        ((volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2}) :=
      hQc.aestronglyMeasurable hoffm
    rw [hres] at h1
    exact h1
  have hae2 : ∀ᵐ p : Euc d × Euc d ∂(volume.prod volume), p.1 ≠ p.2 := r26t8a_g11_diag_null hd
  -- the test function
  obtain ⟨Bφ, hBφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨Bφ', hBφ'⟩ := (hφ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hφc.fderiv (𝕜 := ℝ))
  have hopenf : ∀ y : Euc d, IsOpen ({y}ᶜ : Set (Euc d)) := fun y => isClosed_singleton.isOpen_compl
  have hf2 : ∀ y : Euc d, ContDiffOn ℝ 2 (fun v => Q v y) {y}ᶜ := by
    intro y
    have hg : ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fun v : Euc d => (v, y)) :=
      contDiff_id.prodMk contDiff_const
    have hmaps : Set.MapsTo (fun v : Euc d => (v, y)) {y}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
      fun v hv => by simpa using hv
    have := hQ.1.comp hg.contDiffOn hmaps
    exact this.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))
  have hfat : ∀ u y : Euc d, u ≠ y → ContDiffAt ℝ 2 (fun v => Q v y) u := fun u y hu =>
    (hf2 y).contDiffAt ((hopenf y).mem_nhds (by simpa using hu))
  have hStil : ∀ u y : Euc d, u ≠ y → r26t8a_Stil rho Q u y = r26t8a_divSource rho Q u y := fun u y hu =>
    (r26t8a_f9_divSource_eq (hfat u y hu)).symm
  -- part 1: product integrability of `φ u * (ρ y * Stil u y)`
  have hF1 : Integrable (fun p : Euc d × Euc d => φ p.1 * (rho p.2 * r26t8a_Stil rho Q p.1 p.2))
      (volume.prod volume) := by
    set W1 : Euc d → ℝ := fun u => K * A * (φ u * Real.exp (-c' * ‖u‖ ^ 2)) with hW1
    have hW1c : Continuous W1 := by
      refine continuous_const.mul (hφ.continuous.mul ?_)
      exact Real.continuous_exp.comp (continuous_const.mul ((continuous_norm).pow 2))
    have hW1s : HasCompactSupport W1 := by
      have : HasCompactSupport (fun u => φ u * Real.exp (-c' * ‖u‖ ^ 2)) := hφc.mul_right
      exact this.mul_left
    have hW1i : Integrable W1 := hW1c.integrable_of_hasCompactSupport hW1s
    have hdom := (r26t8a_g3_prod_int hd he0 hed ha'0 hKa ha'c ha'i hW1i).1
    refine Integrable.mono' hdom ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => φ p.1) (volume.prod volume) :=
        (hφ.continuous.comp continuous_fst).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => rho p.2) (volume.prod volume) :=
        (hρc.comp continuous_snd).aestronglyMeasurable
      exact h1.mul (h2.mul hSm)
    · filter_upwards [hae2] with p hp
      have hSb' := hSb A hA Q hQ p.2 p.1 hp
      rw [hStil p.1 p.2 hp]
      have hE0 : 0 < Real.exp (-c' * ‖p.1‖ ^ 2) := Real.exp_pos _
      have hr0 : 0 ≤ 1 + ‖p.1 - p.2‖ ^ (-e) := by
        have := Real.rpow_nonneg (norm_nonneg (p.1 - p.2)) (-e); linarith
      have hJ0 : 0 ≤ jbracket p.2 ^ M := Real.rpow_nonneg (s83_jb_pos p.2).le _
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hrho0 p.2)]
      have hW : |W1 p.1| = K * A * (|φ p.1| * Real.exp (-c' * ‖p.1‖ ^ 2)) := by
        rw [hW1]; simp only
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ K * A), abs_mul, abs_of_nonneg hE0.le]
      rw [hW]
      calc |φ p.1| * (rho p.2 * |r26t8a_divSource rho Q p.1 p.2|)
          ≤ |φ p.1| * (rho p.2 * (K * A * jbracket p.2 ^ M * Real.exp (-c' * ‖p.1‖ ^ 2) *
              (1 + ‖p.1 - p.2‖ ^ (-e)))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSb' (hrho0 _)) (abs_nonneg _)
        _ = _ := by rw [ha']; ring
  -- the field `w = ρ ∇φ`
  set w : Euc d → Euc d := fun u => rho u • gradient φ u with hwdef
  have hgradc : ContDiff ℝ 1 (gradient φ) := by
    rw [r26t8a_gradient_eq_Rz]
    have hφ2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) φ := contDiff_infty.1 hφ 2
    have hDφ : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fderiv ℝ φ) :=
      hφ2.fderiv_right (m := ((1 : ℕ) : WithTop ℕ∞)) (by norm_cast)
    have := (r26t8a_Rz d).contDiff.comp hDφ
    exact_mod_cast this
  have hw1 : ContDiff ℝ 1 w := (hρs.of_le (by exact_mod_cast le_top)).smul hgradc
  have hgradcs : HasCompactSupport (gradient φ) := by
    have := (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => r26t8a_Rz d L) (map_zero _)
    rw [r26t8a_gradient_eq_Rz]
    exact this
  have hwc : HasCompactSupport w := hgradcs.smul_left (f := rho)
  set divw : Euc d → ℝ := fun u => ∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j with hdivw
  have hdivwc : Continuous divw := by
    refine continuous_finset_sum _ fun j _ => ?_
    have hj : Continuous fun v : Euc d => v j := (EuclideanSpace.proj j).continuous
    exact hj.comp ((hw1.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdivws : HasCompactSupport divw := by
    have := (hwc.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Euc d →L[ℝ] Euc d => ∑ j : Fin d, L (EuclideanSpace.single j 1) j) (by simp)
    exact this
  -- per-`y` identity
  have hrow : ∀ y : Euc d, ∫ u, φ u * r26t8a_Stil rho Q u y = ∫ u, Q u y * divw u := by
    intro y
    obtain ⟨τ, H⟩ := r26t8a_p10a_hyp hd hM hsd hA hQ hρs hC hc (fun x => (hb x).1) (fun x => (hb x).2) y
    obtain ⟨-, -, hibp⟩ := r26t8a_g2_ibp H (hφ.of_le (by exact_mod_cast le_top)) (B0 := Bφ) (B1 := Bφ') (fun u => by
      have := hBφ u; rwa [Real.norm_eq_abs] at this) hBφ'
    obtain ⟨-, -, hfld⟩ := r26t8a_g10_ibp_field hd k b hM hsd hA hQ y hw1 hwc
    have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
    have h1 : ∫ u, φ u * r26t8a_Stil rho Q u y =
        ∫ u, φ u * r26t8a_divh (fun w => rho w • gradient (fun v => Q v y) w) u := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with u hu
      rw [hStil u y hu, ← r26t8a_p10a_divh_eq (hρs.differentiable (by simp)) (hfat u y hu)]
    have h2 : ∀ u, ∑ j : Fin d, fderiv ℝ φ u (EuclideanSpace.single j 1) *
        (rho u • gradient (fun v => Q v y) u) j = ∑ j : Fin d, w u j * r26t8a_dx j Q u y := by
      intro u
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hwdef, PiLp.smul_apply, smul_eq_mul, movtr_gradient_apply, r26t8a_dx]
      ring
    rw [h1, hibp]
    simp only [h2]
    rw [hfld, neg_neg]
  -- product integrability of `ρ(y) Q(u,y) div w(u)` (variables `(y, u)`)
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
  have hW2s : HasCompactSupport W2 := hdivws.mul_left
  have hW2i : Integrable W2 := hW2c.integrable_of_hasCompactSupport hW2s
  have hdom2 := (r26t8a_g3_prod_int hd hs0 hsd2 ha'0 hKa ha'c ha'i hW2i).2
  have hQcs : ContinuousOn (fun p : Euc d × Euc d => Q p.2 p.1) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQc.comp (continuous_snd.prodMk continuous_fst).continuousOn (fun p hp => Ne.symm hp)
  have hQms : AEStronglyMeasurable (fun p : Euc d × Euc d => Q p.2 p.1) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => Q p.2 p.1)
        ((volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2}) :=
      hQcs.aestronglyMeasurable hoffm
    rw [hres] at h1
    exact h1
  have hG2 : Integrable (fun p : Euc d × Euc d => rho p.1 * (Q p.2 p.1 * divw p.2)) (volume.prod volume) := by
    refine Integrable.mono' hdom2 ?_ ?_
    · exact ((hρc.comp continuous_fst).aestronglyMeasurable).mul
        (hQms.mul (hdivwc.comp continuous_snd).aestronglyMeasurable)
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
      calc rho p.1 * (|Q p.2 p.1| * |divw p.2|)
          ≤ rho p.1 * ((A * Cq * (jbracket p.2 ^ M * jbracket p.1 ^ M) * (1 + ‖p.1 - p.2‖ ^ (-s))) * |divw p.2|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpt (abs_nonneg _)) (hrho0 _)
        _ = _ := by rw [ha']; ring
  have hswap2 : ∫ y, ∫ u, rho y * (Q u y * divw u) = ∫ u, ∫ y, rho y * (Q u y * divw u) :=
    integral_integral_swap (f := fun y u => rho y * (Q u y * divw u)) hG2
  have hzero : ∀ u, ∫ y, rho y * (Q u y * divw u) = 0 := by
    intro u
    have : ∀ y, rho y * (Q u y * divw u) = (rho y * Q u y) * divw u := fun y => by ring
    simp only [this]
    rw [integral_mul_const, hcan u, zero_mul]
  have hswap1 : ∫ u, ∫ y, φ u * (rho y * r26t8a_Stil rho Q u y) =
      ∫ y, ∫ u, φ u * (rho y * r26t8a_Stil rho Q u y) :=
    integral_integral_swap (f := fun u y => φ u * (rho y * r26t8a_Stil rho Q u y)) hF1
  calc ∫ u, φ u * ∫ y, rho y * r26t8a_Stil rho Q u y
      = ∫ u, ∫ y, φ u * (rho y * r26t8a_Stil rho Q u y) := by
        congr 1; funext u; rw [← integral_const_mul]
    _ = ∫ y, ∫ u, φ u * (rho y * r26t8a_Stil rho Q u y) := hswap1
    _ = ∫ y, rho y * ∫ u, φ u * r26t8a_Stil rho Q u y := by
        congr 1; funext y
        rw [← integral_const_mul]
        congr 1; funext u; ring
    _ = ∫ y, rho y * ∫ u, Q u y * divw u := by simp only [hrow]
    _ = ∫ y, ∫ u, rho y * (Q u y * divw u) := by
        congr 1; funext y; rw [integral_const_mul]
    _ = ∫ u, ∫ y, rho y * (Q u y * divw u) := hswap2
    _ = 0 := by simp only [hzero, integral_zero]

end HRS.MS.R26T8A
