import HRS.MS.R26T8AP11g12
import HRS.MS.R26T8AP10a

/-!
# S8.2 T8A P11g (part 13): the `y`-average of `oneJ(Q(x,·))` vanishes for canonical `Q`
If `∫ ρ(y) Q(u,y) dy = 0` for all `u`: `y ↦ ρ(y) oneJ(Q(·,y))(x)` is integrable with integral `0`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_g13_canon_row (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ) (ha : 0 < a)
    (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {Q : Euc d → Euc d → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hQ : Conormal (k + 2) b M (sigma - 2) A Q) (hcan : ∀ u, ∫ y, rho y * Q u y = 0) (x : Euc d) :
    Integrable (fun y => rho y * oneJ (critCoeff d a beta rho) (fun u => Q u y) x) ∧
    ∫ y, rho y * oneJ (critCoeff d a beta rho) (fun u => Q u y) x = 0 := by
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
  -- the y-average is integrable
  have hs0c : 0 < criticalS d := by unfold criticalS; linarith
  have hsdc : criticalS d < d := by unfold criticalS; linarith
  have hker : ∀ w : Euc d, rieszKernel d (criticalS d) w = ‖w‖ ^ (-criticalS d) := fun w => by
    rw [rieszKernel, if_neg hs0c.ne']
  have hdomF : ∀ (W : Euc d → ℝ), Integrable W → (∀ u, 0 ≤ W u) → AEStronglyMeasurable W volume →
      ∀ (G : Euc d × Euc d → ℝ), AEStronglyMeasurable G (volume.prod volume) →
      (∀ p : Euc d × Euc d, p.1 ≠ p.2 → ‖G p‖ ≤ W p.1 * (a' p.2 * (1 + ‖p.1 - p.2‖ ^ (-e)))) →
      Integrable G (volume.prod volume) := by
    intro W hWi hW0 hWm G hGm hGb
    have hdom := (r26t8a_g3_prod_int hd he0 hed ha'0 hKa ha'c ha'i hWi).1
    refine Integrable.mono' hdom hGm ?_
    filter_upwards [hae2] with p hp
    refine (hGb p hp).trans (le_of_eq ?_)
    rw [abs_of_nonneg (hW0 p.1)]
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
  -- generic domination
  have hdomF : ∀ (W : Euc d → ℝ), Integrable W → (∀ u, 0 ≤ W u) →
      ∀ (G : Euc d × Euc d → ℝ), AEStronglyMeasurable G (volume.prod volume) →
      (∀ p : Euc d × Euc d, p.1 ≠ p.2 → ‖G p‖ ≤ W p.1 * (a' p.2 * (1 + ‖p.1 - p.2‖ ^ (-e)))) →
      Integrable G (volume.prod volume) := by
    intro W hWi hW0 G hGm hGb
    have hdom := (r26t8a_g3_prod_int hd he0 hed ha'0 hKa ha'c ha'i hWi).1
    refine Integrable.mono' hdom hGm ?_
    filter_upwards [hae2] with p hp
    refine (hGb p hp).trans (le_of_eq ?_)
    rw [abs_of_nonneg (hW0 p.1)]
  -- the pointwise estimate of `ρ(y) Stil`
  have hE0 : ∀ u : Euc d, 0 < Real.exp (-c' * ‖u‖ ^ 2) := fun u => Real.exp_pos _
  have hSbd : ∀ p : Euc d × Euc d, p.1 ≠ p.2 → ‖rho p.2 * r26t8a_Stil rho Q p.1 p.2‖ ≤
      (K * A * Real.exp (-c' * ‖p.1‖ ^ 2)) * (a' p.2 * (1 + ‖p.1 - p.2‖ ^ (-e))) := by
    intro p hp
    have hSb' := hSb A hA Q hQ p.2 p.1 hp
    rw [hStil p.1 p.2 hp, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hrho0 p.2)]
    calc rho p.2 * |r26t8a_divSource rho Q p.1 p.2|
        ≤ rho p.2 * (K * A * jbracket p.2 ^ M * Real.exp (-c' * ‖p.1‖ ^ 2) * (1 + ‖p.1 - p.2‖ ^ (-e))) :=
          mul_le_mul_of_nonneg_left hSb' (hrho0 _)
      _ = _ := by rw [ha']; ring
  have hF0m : AEStronglyMeasurable (fun p : Euc d × Euc d => rho p.2 * r26t8a_Stil rho Q p.1 p.2) (volume.prod volume) :=
    (hρc.comp continuous_snd).aestronglyMeasurable.mul hSm
  have hW0i : Integrable (fun u : Euc d => K * A * Real.exp (-c' * ‖u‖ ^ 2)) :=
    (r26t8a_p10a_gauss_int (d := d) hc').const_mul _
  have hF0 : Integrable (fun p : Euc d × Euc d => rho p.2 * r26t8a_Stil rho Q p.1 p.2) (volume.prod volume) :=
    hdomF _ hW0i (fun u => by have := hE0 u; positivity) _ hF0m hSbd
  have hSgi : Integrable (fun u => ∫ y, rho y * r26t8a_Stil rho Q u y) := hF0.integral_prod_left
  have hSg0 : ∀ᵐ u : Euc d ∂volume, ∫ y, rho y * r26t8a_Stil rho Q u y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hSgi.locallyIntegrable ?_
    intro g hg hgc
    simpa only [smul_eq_mul] using r26t8a_g12_weak d hd k b a beta M sigma ha hbeta hM hsd hrho hA hQ hcan hg hgc
  -- the kernel-weighted product
  set W3 : Euc d → ℝ := fun u => ‖x - u‖ ^ (-criticalS d) * (K * A * Real.exp (-c' * ‖u‖ ^ 2)) with hW3
  have hW3m : Measurable (fun u : Euc d => ‖x - u‖ ^ (-criticalS d)) :=
    ((measurable_const.sub measurable_id).norm).pow_const _
  have hW3nn : ∀ u, 0 ≤ W3 u := fun u => by
    have := hE0 u
    have h2 := Real.rpow_nonneg (norm_nonneg (x - u)) (-criticalS d)
    simp only [hW3]; positivity
  have hW3i : Integrable W3 := by
    have hdm := (r26t8a_p10a_gp_dom hd hs0c hsdc x hc').const_mul (K * A)
    refine Integrable.mono' hdm ?_ (Filter.Eventually.of_forall fun u => ?_)
    · exact (hW3m.aestronglyMeasurable).mul (by
        have : Continuous fun u : Euc d => K * A * Real.exp (-c' * ‖u‖ ^ 2) :=
          continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul ((continuous_norm).pow 2)))
        exact this.aestronglyMeasurable)
    · rw [Real.norm_of_nonneg (hW3nn u)]
      have h2 := Real.rpow_nonneg (norm_nonneg (x - u)) (-criticalS d)
      have hn : ‖x - u‖ = ‖u - x‖ := norm_sub_rev _ _
      have hE := hE0 u
      simp only [hW3]
      rw [hn]
      have : ‖u - x‖ ^ (-criticalS d) ≤ 1 + ‖u - x‖ ^ (-criticalS d) := by linarith
      calc ‖u - x‖ ^ (-criticalS d) * (K * A * Real.exp (-c' * ‖u‖ ^ 2))
          ≤ (1 + ‖u - x‖ ^ (-criticalS d)) * (K * A * Real.exp (-c' * ‖u‖ ^ 2)) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = K * A * (Real.exp (-c' * ‖u‖ ^ 2) * (1 + ‖u - x‖ ^ (-criticalS d))) := by ring
  have hF3m : AEStronglyMeasurable
      (fun p : Euc d × Euc d => ‖x - p.1‖ ^ (-criticalS d) * (rho p.2 * r26t8a_Stil rho Q p.1 p.2))
      (volume.prod volume) :=
    ((hW3m.comp measurable_fst).aestronglyMeasurable).mul hF0m
  have hF3 : Integrable
      (fun p : Euc d × Euc d => ‖x - p.1‖ ^ (-criticalS d) * (rho p.2 * r26t8a_Stil rho Q p.1 p.2))
      (volume.prod volume) := by
    refine hdomF W3 hW3i hW3nn _ hF3m fun p hp => ?_
    have h2 := Real.rpow_nonneg (norm_nonneg (x - p.1)) (-criticalS d)
    rw [norm_mul, Real.norm_of_nonneg h2]
    have := hSbd p hp
    calc ‖x - p.1‖ ^ (-criticalS d) * ‖rho p.2 * r26t8a_Stil rho Q p.1 p.2‖
        ≤ ‖x - p.1‖ ^ (-criticalS d) * ((K * A * Real.exp (-c' * ‖p.1‖ ^ 2)) *
            (a' p.2 * (1 + ‖p.1 - p.2‖ ^ (-e)))) := mul_le_mul_of_nonneg_left this h2
      _ = _ := by simp only [hW3]; ring
  -- identification of the row
  have hae_y : ∀ᵐ y : Euc d ∂volume, y ≠ x := compl_mem_ae_iff.mpr (measure_singleton x)
  have hrowF : ∀ y : Euc d, y ≠ x → ∫ u, ‖x - u‖ ^ (-criticalS d) * (rho y * r26t8a_Stil rho Q u y) =
      rho y * oneJ (critCoeff d a beta rho) (fun u => Q u y) x := by
    intro y hy
    obtain ⟨-, hid⟩ := r26t8a_conormal_potential_ibp d hd k b a beta M sigma ha hbeta hM hsd rho hrho Q A hA
      hQ x y (Ne.symm hy)
    rw [hid, ← integral_const_mul]
    have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    rw [hker, hStil u y hu]; ring
  have hInt : Integrable (fun y => rho y * oneJ (critCoeff d a beta rho) (fun u => Q u y) x) := by
    have := hF3.integral_prod_right
    refine this.congr ?_
    filter_upwards [hae_y] with y hy
    exact hrowF y hy
  refine ⟨hInt, ?_⟩
  have hswap : ∫ u, ∫ y, ‖x - u‖ ^ (-criticalS d) * (rho y * r26t8a_Stil rho Q u y) =
      ∫ y, ∫ u, ‖x - u‖ ^ (-criticalS d) * (rho y * r26t8a_Stil rho Q u y) :=
    integral_integral_swap (f := fun u y => ‖x - u‖ ^ (-criticalS d) * (rho y * r26t8a_Stil rho Q u y)) hF3
  have hlhs : ∫ u, ∫ y, ‖x - u‖ ^ (-criticalS d) * (rho y * r26t8a_Stil rho Q u y) = 0 := by
    have : ∀ᵐ u : Euc d ∂volume, ∫ y, ‖x - u‖ ^ (-criticalS d) * (rho y * r26t8a_Stil rho Q u y) = 0 := by
      filter_upwards [hSg0] with u hu
      rw [integral_const_mul, hu, mul_zero]
    rw [integral_congr_ae this, integral_zero]
  have hrhs : ∫ y, ∫ u, ‖x - u‖ ^ (-criticalS d) * (rho y * r26t8a_Stil rho Q u y) =
      ∫ y, rho y * oneJ (critCoeff d a beta rho) (fun u => Q u y) x := by
    refine integral_congr_ae ?_
    filter_upwards [hae_y] with y hy
    exact hrowF y hy
  rw [← hrhs, ← hswap, hlhs]

end HRS.MS.R26T8A
