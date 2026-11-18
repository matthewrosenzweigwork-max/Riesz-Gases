import HRS.MS.R26T8AP11g9

/-!
# S8.2 T8A P11g (part 10): integration by parts of a conormal function against a compactly supported field
For `w` `C^1` with compact support and `Q` conormal (pole order `σ-2 < d-1`):
`∫ ∑_j w_j ∂_jQ(·,y) = - ∫ Q(·,y) div w`.  (`r26t8a_g2_ibp` with `Γ = 1` and `h = Q(·,y) w`.)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_g10_ibp_field (hd : 2 ≤ d) (k b : ℕ) {M σ A : ℝ} (hM : 0 ≤ M) (hσ : σ < d) (hA : 0 ≤ A)
    {Q : Euc d → Euc d → ℝ} (hQ : Conormal (k + 2) b M (σ - 2) A Q) (y : Euc d)
    {w : Euc d → Euc d} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) :
    Integrable (fun u => ∑ j : Fin d, w u j * r26t8a_dx j Q u y) ∧
    Integrable (fun u => Q u y * ∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j) ∧
    ∫ u, ∑ j : Fin d, w u j * r26t8a_dx j Q u y =
      -∫ u, Q u y * ∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j := by
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max (σ - 2) 0 := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact le_max_right _ _
  have hm1 : σ - 2 ≤ m := by rw [hm]; exact le_max_left _ _
  have hmd : m < d - 1 := by rw [hm]; exact max_lt (by linarith) (by linarith)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (d - 1 - m) / 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = m + η := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  have hτd : τ + 1 < d := by rw [hτ, hη] at *; linarith
  obtain ⟨K0, hK00, hK0⟩ := r26t8a_p10a_Tj_bound hchi (k := k) (b := b) (M := M) (σ := σ - 2) hM
    (j := 0) (by omega) (e := τ) (by rw [hτ]; push_cast; linarith) hτ0
  obtain ⟨K1, hK10, hK1⟩ := r26t8a_p10a_Tj_bound hchi (k := k) (b := b) (M := M) (σ := σ - 2) hM
    (j := 1) (by omega) (e := τ + 1) (by rw [hτ]; push_cast; linarith) (by linarith)
  set f : Euc d → ℝ := fun v => Q v y with hf
  have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
  have hf1 : ContDiffOn ℝ 1 f {y}ᶜ := by
    have hg : ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fun v : Euc d => (v, y)) :=
      contDiff_id.prodMk contDiff_const
    have hmaps : Set.MapsTo (fun v : Euc d => (v, y)) {y}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
      fun v hv => by simpa using hv
    have := hQ.1.comp hg.contDiffOn hmaps
    exact this.of_le (by exact_mod_cast (by omega : 1 ≤ k + 2))
  have hfc : ContinuousOn f {y}ᶜ := hf1.continuousOn
  have hDfc : ContinuousOn (fderiv ℝ f) {y}ᶜ := hf1.continuousOn_fderiv_of_isOpen hopen (by simp)
  obtain ⟨D1, hD10, hD1⟩ := r26t8a_g9_gauss_compact hw.continuous hwc
  obtain ⟨D2, hD20, hD2⟩ := r26t8a_g9_gauss_compact (hw.continuous_fderiv (by simp)) (hwc.fderiv (𝕜 := ℝ))
  have hDwc : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by simp)
  have hjy : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
  set J : ℝ := jbracket y ^ M with hJ
  have hT0 : ∀ u, u ≠ y → |f u| ≤ K0 * A * J * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-τ)) := fun u hu => by
    have := hK0 A hA hQ y u hu
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hT1 : ∀ u, u ≠ y → ‖fderiv ℝ f u‖ ≤
      K1 * A * J * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-(τ + 1))) := fun u hu => by
    have := hK1 A hA hQ y u hu
    rwa [norm_iteratedFDeriv_one] at this
  have hdxle : ∀ (u : Euc d) (j : Fin d), |fderiv ℝ f u (EuclideanSpace.single j 1)| ≤ ‖fderiv ℝ f u‖ := by
    intro u j
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ f u (EuclideanSpace.single j 1)‖
        ≤ ‖fderiv ℝ f u‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ := (fderiv ℝ f u).le_opNorm _
      _ ≤ _ := by rw [r26t8a_norm_single, mul_one]
  have hdwle : ∀ (u : Euc d) (j : Fin d),
      |(fderiv ℝ w u (EuclideanSpace.single j 1)) j| ≤ ‖fderiv ℝ w u‖ := by
    intro u j
    refine (r26t8a_abs_coord_le _ _).trans ?_
    calc ‖fderiv ℝ w u (EuclideanSpace.single j 1)‖
        ≤ ‖fderiv ℝ w u‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ := (fderiv ℝ w u).le_opNorm _
      _ ≤ _ := by rw [r26t8a_norm_single, mul_one]
  -- the hypotheses of the cut-off integration by parts for `h' = f • w`
  set h' : Euc d → Euc d := fun u => f u • w u with hh'
  have hH : R26P10Hyp d y τ h' := by
    refine ⟨hd, hτ0, hτd, hf1.smul hw.contDiffOn, ?_, ?_⟩
    · refine r26t8a_p10a_gp_of_poly (M := M) (c := 1) (D := K0 * A * J * D1) one_pos
        (by positivity) fun u hu => ?_
      rw [abs_of_nonneg (norm_nonneg _), hh', norm_smul, Real.norm_eq_abs]
      have h1 := hT0 u hu
      have h2 := hD1 u
      have hp : 0 ≤ (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-τ)) := by positivity
      calc |f u| * ‖w u‖ ≤ (K0 * A * J * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-τ))) *
            (D1 * Real.exp (-1 * ‖u‖ ^ 2)) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · refine r26t8a_p10a_gp_of_poly (M := M) (c := 1) (D := (2 * K0 * D2 + K1 * D1) * A * J) one_pos
        (by positivity) fun u hu => ?_
      rw [abs_of_nonneg (norm_nonneg _)]
      have hdf : DifferentiableAt ℝ f u :=
        (hf1.contDiffAt (hopen.mem_nhds (by simpa using hu))).differentiableAt (by simp)
      have hdw : DifferentiableAt ℝ w u := (hw.differentiable (by simp)) u
      have hfd : ‖fderiv ℝ h' u‖ ≤ |f u| * ‖fderiv ℝ w u‖ + ‖fderiv ℝ f u‖ * ‖w u‖ := by
        rw [hh', fderiv_fun_smul hdf hdw]
        refine (norm_add_le _ _).trans ?_
        have e1 : ‖f u • fderiv ℝ w u‖ ≤ |f u| * ‖fderiv ℝ w u‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        have e2 : ‖(fderiv ℝ f u).smulRight (w u)‖ ≤ ‖fderiv ℝ f u‖ * ‖w u‖ := by
          rw [ContinuousLinearMap.norm_smulRight_apply]
        linarith
      have hn : 0 < ‖u - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hu)
      have hp := r26t8a_g8_pow hn hτ0.le
      set P : ℝ := (1 + ‖u‖) ^ M with hP
      set q : ℝ := 1 + ‖u - y‖ ^ (-(τ + 1)) with hq
      set E : ℝ := Real.exp (-1 * ‖u‖ ^ 2) with hEd
      have hP0 : 0 ≤ P := Real.rpow_nonneg (by positivity) _
      have hq0 : 0 ≤ q := by
        have := Real.rpow_nonneg (norm_nonneg (u - y)) (-(τ + 1)); linarith
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      have hKAJ : 0 ≤ A * J := mul_nonneg hA hjy
      have h1 : |f u| ≤ K0 * A * J * P * (2 * q) := by
        refine (hT0 u hu).trans ?_
        have : 0 ≤ K0 * A * J * P := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hp this]
      calc ‖fderiv ℝ h' u‖ ≤ |f u| * ‖fderiv ℝ w u‖ + ‖fderiv ℝ f u‖ * ‖w u‖ := hfd
        _ ≤ (K0 * A * J * P * (2 * q)) * (D2 * E) + (K1 * A * J * P * q) * (D1 * E) :=
            add_le_add (mul_le_mul h1 (hD2 u) (norm_nonneg _) (by positivity))
              (mul_le_mul (hT1 u hu) (hD1 u) (norm_nonneg _) (by positivity))
        _ = _ := by ring
  obtain ⟨-, -, hI3⟩ := r26t8a_g2_ibp hH (Γ := fun _ => (1 : ℝ)) contDiff_const (B0 := 1) (B1 := 0)
    (fun u => by simp) (fun u => by simp)
  have hI3' : ∫ u, r26t8a_divh h' u = 0 := by simpa using hI3
  -- identify the divergence
  have hdivEq : ∀ u, u ≠ y → r26t8a_divh h' u =
      (∑ j : Fin d, w u j * r26t8a_dx j Q u y) +
        Q u y * ∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j := by
    intro u hu
    have hdf : DifferentiableAt ℝ f u :=
      (hf1.contDiffAt (hopen.mem_nhds (by simpa using hu))).differentiableAt (by simp)
    have hdw : DifferentiableAt ℝ w u := (hw.differentiable (by simp)) u
    unfold r26t8a_divh
    rw [hh', fderiv_fun_smul hdf hdw, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, r26t8a_dx]
    ring
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
  -- integrability of the two pieces
  have gP1 : R26P10GP y (τ + 1) (fun u => ∑ j : Fin d, w u j * r26t8a_dx j Q u y) := by
    refine r26t8a_p10a_gp_of_poly (M := M) (c := 1) (D := d * D1 * K1 * A * J) one_pos (by positivity)
      fun u hu => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hP0 : 0 ≤ (1 + ‖u‖) ^ M := Real.rpow_nonneg (by positivity) _
    have hq0 : 0 ≤ 1 + ‖u - y‖ ^ (-(τ + 1)) := by
      have := Real.rpow_nonneg (norm_nonneg (u - y)) (-(τ + 1)); linarith
    calc ∑ j : Fin d, |w u j * r26t8a_dx j Q u y|
        ≤ ∑ j : Fin d, (D1 * Real.exp (-1 * ‖u‖ ^ 2)) *
            (K1 * A * J * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-(τ + 1)))) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul ((r26t8a_abs_coord_le _ _).trans (hD1 u)) ((hdxle u j).trans (hT1 u hu))
            (abs_nonneg _) (by positivity)
      _ = _ := by simp; ring
  have gP2 : R26P10GP y τ (fun u => Q u y * ∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j) := by
    refine r26t8a_p10a_gp_of_poly (M := M) (c := 1) (D := d * D2 * K0 * A * J) one_pos (by positivity)
      fun u hu => ?_
    rw [abs_mul]
    have hsum : |∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j| ≤ d * (D2 * Real.exp (-1 * ‖u‖ ^ 2)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j : Fin d, |fderiv ℝ w u (EuclideanSpace.single j 1) j|
          ≤ ∑ j : Fin d, D2 * Real.exp (-1 * ‖u‖ ^ 2) := Finset.sum_le_sum fun j _ => (hdwle u j).trans (hD2 u)
        _ = _ := by simp
    have hP0 : 0 ≤ (1 + ‖u‖) ^ M := Real.rpow_nonneg (by positivity) _
    calc |f u| * |∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j|
        ≤ (K0 * A * J * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-τ))) * (d * (D2 * Real.exp (-1 * ‖u‖ ^ 2))) :=
          mul_le_mul (hT0 u hu) hsum (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hm1 : AEStronglyMeasurable (fun u => ∑ j : Fin d, w u j * r26t8a_dx j Q u y) volume := by
    refine r26t8a_p10a_aesm hd y ?_
    refine continuousOn_finset_sum _ fun j _ => ?_
    have hj : Continuous fun v : Euc d => v j := (EuclideanSpace.proj j).continuous
    exact (hj.comp hw.continuous).continuousOn.mul (by
      have : ContinuousOn (fun u => fderiv ℝ f u (EuclideanSpace.single j 1)) {y}ᶜ :=
        hDfc.clm_apply continuousOn_const
      exact this)
  have hm2 : AEStronglyMeasurable (fun u => Q u y * ∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j) volume := by
    refine r26t8a_p10a_aesm hd y ?_
    have hs : ContinuousOn (fun u => ∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j) {y}ᶜ := by
      refine continuousOn_finset_sum _ fun j _ => ?_
      have hj : Continuous fun v : Euc d => v j := (EuclideanSpace.proj j).continuous
      exact (hj.comp (hDwc.clm_apply continuous_const)).continuousOn
    exact hfc.mul hs
  have iP1 := r26t8a_p10a_gp_integrable (y := y) (τ := τ + 1) hd (by linarith) (by linarith) gP1 hm1
  have iP2 := r26t8a_p10a_gp_integrable (y := y) (τ := τ) hd hτ0 (by linarith) gP2 hm2
  refine ⟨iP1, iP2, ?_⟩
  have hcongr : (fun u => r26t8a_divh h' u) =ᵐ[volume] fun u =>
      (∑ j : Fin d, w u j * r26t8a_dx j Q u y) +
        Q u y * ∑ j : Fin d, fderiv ℝ w u (EuclideanSpace.single j 1) j := by
    filter_upwards [hae] with u hu using hdivEq u hu
  have h0 : ∫ u, r26t8a_divh h' u = 0 := hI3'
  rw [integral_congr_ae hcongr, integral_add iP1 iP2] at h0
  linarith

end HRS.MS.R26T8A
