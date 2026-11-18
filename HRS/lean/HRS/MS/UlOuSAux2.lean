import HRS.MS.UlOuSAux1
import HRS.Prob.Gaussian

/-!
# UL-3, part 2 (UlOuSAux2): the derivative gain `H^{n} → H^{n+1}` for Gaussian averages

(docstring: see `UlOuS.lean`.)  Helper lemmas carry the prefix `ul3_`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW

variable {d : ℕ}


/-- Stein's identity for the standard Gaussian of `Euc d`: `E[w_i F(w)] = E[∂_i F(w)]`. -/
theorem ul3_stein_std {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) {B M : ℝ} (hB : ∀ w, |F w| ≤ B)
    (hM : ∀ w, ‖fderiv ℝ F w‖ ≤ M) (i : Fin d) :
    ∫ w, w i * F w ∂(stdGaussian (Euc d)) =
      ∫ w, fderiv ℝ F w (EuclideanSpace.single i 1) ∂(stdGaussian (Euc d)) := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by
      exact (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).mul hF.continuous).aestronglyMeasurable),
    integral_map (by fun_prop) (by
      refine Continuous.aestronglyMeasurable ?_
      exact ((continuous_eval_const (EuclideanSpace.single i (1 : ℝ))).comp
        (hF.continuous_fderiv one_ne_zero))),
    ]
  set Ft : (Fin d → ℝ) → ℝ := fun z => F (WithLp.toLp 2 z) with hFt
  set Ft' : (Fin d → ℝ) → ℝ := fun z => fderiv ℝ F (WithLp.toLp 2 z) (EuclideanSpace.single i 1) with hFt'
  have hFtc : Continuous Ft := hF.continuous.comp (PiLp.continuous_toLp 2 _)
  have hFtc' : Continuous Ft' :=
    ((continuous_eval_const (EuclideanSpace.single i (1 : ℝ))).comp
        (hF.continuous_fderiv one_ne_zero)).comp (PiLp.continuous_toLp 2 _)
  have hd : ∀ z : Fin d → ℝ, HasDerivAt (fun x => Ft (Function.update z i x)) (Ft' z) (z i) := by
    intro z
    have hγ : HasDerivAt (fun x : ℝ => (WithLp.toLp 2 z : Euc d) + (x - z i) • EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ)) (z i) := by
      have := ((hasDerivAt_id (z i)).sub_const (z i)).smul_const (EuclideanSpace.single i (1 : ℝ))
      simpa using this.const_add (WithLp.toLp 2 z : Euc d)
    have hFd : HasFDerivAt F (fderiv ℝ F (WithLp.toLp 2 z)) ((WithLp.toLp 2 z : Euc d) +
        (z i - z i) • EuclideanSpace.single i (1 : ℝ)) := by
      have := (hF.differentiable one_ne_zero (WithLp.toLp 2 z)).hasFDerivAt
      simpa using this
    have := hFd.comp_hasDerivAt (z i) hγ
    have e : (fun x => Ft (Function.update z i x)) =
        F ∘ fun x : ℝ => (WithLp.toLp 2 z : Euc d) + (x - z i) • EuclideanSpace.single i (1 : ℝ) := by
      funext x
      simp only [hFt, Function.comp]
      congr 1
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update, hk, EuclideanSpace.single_apply]
    rw [e]
    exact this
  have h1 : Integrable Ft (HRS.Contr.gpi d) :=
    HRS.Contr.integrable_of_poly (C := B) (k := 0) hFtc.aestronglyMeasurable (fun z => by simpa using hB _)
  have h2 : Integrable (fun z : Fin d → ℝ => z i * Ft z) (HRS.Contr.gpi d) := by
    refine HRS.Contr.integrable_of_poly (C := B) (k := 1)
      (((continuous_apply i).mul hFtc).aestronglyMeasurable) (fun z => ?_)
    rw [abs_mul]
    have h3 : |z i| ≤ 1 + ‖z‖ := by
      have := norm_le_pi_norm z i
      rw [Real.norm_eq_abs] at this; linarith [norm_nonneg z]
    have h4 : |Ft z| ≤ B := hB _
    have h5 : 0 ≤ B := (abs_nonneg _).trans h4
    calc |z i| * |Ft z| ≤ (1 + ‖z‖) * B := mul_le_mul h3 h4 (abs_nonneg _) (by positivity)
      _ = B * (1 + ‖z‖) ^ 1 := by ring
  have h3 : Integrable Ft' (HRS.Contr.gpi d) := by
    refine HRS.Contr.integrable_of_poly (C := M) (k := 0) hFtc'.aestronglyMeasurable (fun z => ?_)
    have := (ContinuousLinearMap.le_opNorm (fderiv ℝ F (WithLp.toLp 2 z)) (EuclideanSpace.single i (1 : ℝ)))
    simp only [EuclideanSpace.norm_single, norm_one, mul_one] at this
    have h4 : |fderiv ℝ F (WithLp.toLp 2 z) (EuclideanSpace.single i (1 : ℝ))| ≤ M := by
      rw [← Real.norm_eq_abs]; exact this.trans (hM _)
    simpa [hFt'] using h4
  exact HRS.Contr.stein_pi i hd h1 h2 h3



/-- one derivative on the Fourier side: `‖v‖_{H^{n+1}} ≤ ‖v‖_{H^n} + ∑_j ‖∂_j v‖_{H^n}` for `v ∈ C_c^1` -/
theorem ul3_sobE_succ (n : ℕ) {v : Euc d → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    sobolevNormE ((n + 1 : ℕ) : ℝ) v ≤ sobolevNormE (n : ℝ) v +
      ∑ j : Fin d, sobolevNormE (n : ℝ) (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) := by
  set vj : Fin d → Euc d → ℝ := fun j x => fderiv ℝ v x (EuclideanSpace.single j 1) with hvj
  have hvc : Continuous v := hv.continuous
  have hv2 : MemLp v 2 volume := hvc.memLp_of_hasCompactSupport hc
  have hv1 : Integrable v volume := hvc.integrable_of_hasCompactSupport hc
  have hvjc : ∀ j, Continuous (vj j) := fun j =>
    (continuous_eval_const (EuclideanSpace.single j (1 : ℝ))).comp (hv.continuous_fderiv one_ne_zero)
  have hvjcs : ∀ j, HasCompactSupport (vj j) := fun j =>
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single j (1 : ℝ))) (by simp)
  have hvj2 : ∀ j, MemLp (vj j) 2 volume := fun j => (hvjc j).memLp_of_hasCompactSupport (hvjcs j)
  have hvj1 : ∀ j, Integrable (vj j) volume := fun j => (hvjc j).integrable_of_hasCompactSupport (hvjcs j)
  set Fv : Euc d → ℂ := fun w => ((v w : ℝ) : ℂ) with hFv
  set Fj : Fin d → Euc d → ℂ := fun j w => ((vj j w : ℝ) : ℂ) with hFj
  have hnorm : ∀ j w, ‖𝓕 (Fj j) w‖ = 2 * Real.pi * |w j| * ‖𝓕 Fv w‖ := by
    intro j w
    have := ul0_fourier_partial_eq (m := 1) hv hc (n := 1) le_rfl (fun _ => j) w
    have e : partialDeriv (fun _ : Fin 1 => j) v = vj j := by
      funext x
      simp [partialDeriv, hvj, iteratedFDeriv_one_apply]
    rw [e] at this
    simpa [pow_one, Finset.prod_const, mul_assoc] using this
  have hcont : Continuous (𝓕 Fv) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).continuous₂ hv1.ofReal
  have hwt : ∀ ξ : Euc d, wt ξ = 1 + ∑ j : Fin d, (2 * Real.pi * |ξ j|) ^ 2 := by
    intro ξ
    unfold wt
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, mul_pow, ← Finset.mul_sum]
    ring
  have hsq : sobolevNormE ((n + 1 : ℕ) : ℝ) v ^ 2 = sobolevNormE (n : ℝ) v ^ 2 +
      ∑ j : Fin d, sobolevNormE (n : ℝ) (vj j) ^ 2 := by
    rw [um_sobE_sq hv2, um_sobE_sq hv2]
    have hj : ∀ j, sobolevNormE (n : ℝ) (vj j) ^ 2 =
        ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (n : ℝ) * (2 * Real.pi * |ξ j| * ‖𝓕 Fv ξ‖) ^ 2) := by
      intro j
      rw [um_sobE_sq (hvj2 j)]
      refine lintegral_congr_ae ?_
      filter_upwards [um_L1L2 (hvj1 j) (hvj2 j)] with ξ hξ
      rw [hξ]
      congr 3
      exact hnorm j ξ
    simp only [hj]
    have hA : ∀ s : ℝ, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 v ξ‖ ^ 2) =
        ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖𝓕 Fv ξ‖ ^ 2) := by
      intro s
      refine lintegral_congr_ae ?_
      filter_upwards [um_L1L2 hv1 hv2] with ξ hξ
      rw [hξ]
    rw [hA, hA]
    have hpt : ∀ ξ : Euc d, wt ξ ^ (((n + 1 : ℕ) : ℝ)) * ‖𝓕 Fv ξ‖ ^ 2 =
        wt ξ ^ (n : ℝ) * ‖𝓕 Fv ξ‖ ^ 2 +
          ∑ j : Fin d, wt ξ ^ (n : ℝ) * (2 * Real.pi * |ξ j| * ‖𝓕 Fv ξ‖) ^ 2 := by
      intro ξ
      have h1 : wt ξ ^ (((n + 1 : ℕ) : ℝ)) = wt ξ ^ (n : ℝ) * wt ξ := by
        rw [Nat.cast_succ, Real.rpow_add (wt_pos ξ), Real.rpow_one]
      have hs : ∑ j : Fin d, (2 * Real.pi * |ξ j| * ‖𝓕 Fv ξ‖) ^ 2 = (wt ξ - 1) * ‖𝓕 Fv ξ‖ ^ 2 := by
        rw [hwt ξ]
        simp only [mul_pow, ← Finset.sum_mul]
        ring
      rw [h1, ← Finset.mul_sum, hs]
      ring
    have hn0 : ∀ ξ : Euc d, 0 ≤ wt ξ ^ (n : ℝ) * ‖𝓕 Fv ξ‖ ^ 2 := fun ξ =>
      mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _)
    have hj0 : ∀ j (ξ : Euc d), 0 ≤ wt ξ ^ (n : ℝ) * (2 * Real.pi * |ξ j| * ‖𝓕 Fv ξ‖) ^ 2 := fun j ξ =>
      mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _)
    simp_rw [hpt]
    have hmeas0 : Measurable fun ξ : Euc d => ENNReal.ofReal (wt ξ ^ (n : ℝ) * ‖𝓕 Fv ξ‖ ^ 2) :=
      ENNReal.measurable_ofReal.comp (((continuous_wt_rpow (n : ℝ)).mul (hcont.norm.pow 2)).measurable)
    have hmeasj : ∀ j : Fin d, Measurable fun ξ : Euc d =>
        ENNReal.ofReal (wt ξ ^ (n : ℝ) * (2 * Real.pi * |ξ j| * ‖𝓕 Fv ξ‖) ^ 2) := fun j =>
      ENNReal.measurable_ofReal.comp (((continuous_wt_rpow (n : ℝ)).mul
        ((((continuous_const.mul ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _) |>.abs))).mul
          hcont.norm).pow 2)).measurable)
    have e1 : ∀ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (n : ℝ) * ‖𝓕 Fv ξ‖ ^ 2 +
        ∑ j : Fin d, wt ξ ^ (n : ℝ) * (2 * Real.pi * |ξ j| * ‖𝓕 Fv ξ‖) ^ 2) =
        ENNReal.ofReal (wt ξ ^ (n : ℝ) * ‖𝓕 Fv ξ‖ ^ 2) +
          ∑ j : Fin d, ENNReal.ofReal (wt ξ ^ (n : ℝ) * (2 * Real.pi * |ξ j| * ‖𝓕 Fv ξ‖) ^ 2) := by
      intro ξ
      rw [ENNReal.ofReal_add (hn0 ξ) (Finset.sum_nonneg fun j _ => hj0 j ξ),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => hj0 j ξ)]
    simp_rw [e1]
    rw [lintegral_add_left hmeas0, lintegral_finsetSum _ fun j _ => hmeasj j]
  have hfin : sobolevNormE ((n + 1 : ℕ) : ℝ) v ^ 2 ≤
      (sobolevNormE (n : ℝ) v + ∑ j : Fin d, sobolevNormE (n : ℝ) (vj j)) ^ 2 := by
    rw [hsq]
    calc _ ≤ sobolevNormE (n : ℝ) v ^ 2 + (∑ j : Fin d, sobolevNormE (n : ℝ) (vj j)) ^ 2 := by
          gcongr
          exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => bot_le)
      _ ≤ _ := by
          rw [add_sq, add_right_comm]
          exact le_self_add
  exact (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).1 hfin


/-- change of cutoff: `sup_z ‖a(·-z) u‖_{H^m} ≲ ‖u‖_{H^m_uloc}` for any `a ∈ C_c^∞` -/
theorem ul3_cutoff_change (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (a : Euc d → ℝ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Euc d) (u : Euc d → ℝ),
      sobolevNormE (m : ℝ) (fun x => a (x - z) * u x) ≤ ENNReal.ofReal C * ulocNormE m χ u := by
  obtain ⟨R0, hR0⟩ := hac.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R0' : ℝ := max R0 0 + 1 with hR0'
  have hR0pos : 0 < R0' := by positivity
  obtain ⟨Y, hY⟩ := HRS.MS.UlocCut.uc_cover (fun y : Euc d => y)
    (fun p => ⟨p, by simpa using one_pos⟩) R0'
  obtain ⟨C, hC, h⟩ := ul0_key m a χ ha hac hχ.1 hχ.2.1 Y R0' 0 R0' hR0pos (by linarith)
    (fun p hp => by
      have : p ∈ tsupport a := subset_tsupport _ hp
      have := hR0 this
      simp only [Metric.mem_closedBall, dist_zero_right] at this
      linarith [le_max_left R0 0])
    (fun p hp => by
      obtain ⟨y, hy, hpy⟩ := hY p hp
      exact ⟨y, hy, hχ.2.2.2.2 _ (by simpa using hpy.le)⟩)
  refine ⟨C * Y.card + 1, by positivity, fun z u => ?_⟩
  refine (h z z (by simp) u).trans ?_
  have : ∑ y ∈ Y, sobolevNormE (m : ℝ) (fun x => χ (x - (z + y)) * u x) ≤
      Y.card • ulocNormE m χ u :=
    Finset.sum_le_card_nsmul _ _ _ fun y _ => le_iSup (fun z : Euc d =>
      sobolevNormE (m : ℝ) fun x => χ (x - z) * u x) (z + y)
  calc _ ≤ ENNReal.ofReal C * (Y.card • ulocNormE m χ u) := by gcongr
    _ = ENNReal.ofReal (C * Y.card) * ulocNormE m χ u := by
        rw [nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul hC.le]
        simp
    _ ≤ ENNReal.ofReal (C * Y.card + 1) * ulocNormE m χ u := by
        gcongr
        linarith

/-- the derivative of an `IsUlocCutoff` function is smooth and compactly supported -/
theorem ul3_cutoff_deriv {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (j : Fin d) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (EuclideanSpace.single j (1 : ℝ))) ∧
      HasCompactSupport (fun x => fderiv ℝ χ x (EuclideanSpace.single j (1 : ℝ))) := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.1.fderiv_right (by simp)
    exact h1.clm_apply contDiff_const
  · exact (hχ.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single j (1 : ℝ)))
      (by simp)


theorem ul3_memCb_const (m : ℕ) (t : ℝ) : HRS.MemCb m (fun _ : Euc d => t) ∧
    HRS.cbNorm m (fun _ : Euc d => t) ≤ |t| := by
  refine ⟨⟨contDiff_const, fun j hj => ⟨|t|, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    cases j with
    | zero => simp
    | succ j => simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
  · unfold HRS.cbNorm
    refine le_trans (Finset.sum_le_sum (g := fun j => if j = 0 then |t| else 0) fun j _ => ?_) ?_
    · cases j with
      | zero => simp [ciSup_const]
      | succ j => simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
    · simp [Finset.sum_ite_eq']

/-- scalar multiples -/
theorem ul3_scalar (m : ℕ) (χ : Euc d → ℝ) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ (t : ℝ) (u : Euc d → ℝ),
      ulocNormE m χ (fun x => t * u x) ≤ ENNReal.ofReal (Cs * |t|) * ulocNormE m χ u := by
  obtain ⟨C, hC, h⟩ := ulocNormE_mul_cb m χ
  refine ⟨C, hC, fun t u => ?_⟩
  refine (h (fun _ => t) (ul3_memCb_const m t).1 u).trans ?_
  gcongr
  exact (ul3_memCb_const m t).2


/-- the averaging bound for a finite (not necessarily probability) measure -/
theorem ul3_avg_finite (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) {Cs : ℝ}
    (hCs : ∀ (t : ℝ) (u : Euc d → ℝ), ulocNormE m χ (fun x => t * u x) ≤
      ENNReal.ofReal (Cs * |t|) * ulocNormE m χ u)
    (ρ : Measure (Euc d)) [IsFiniteMeasure ρ] (h : Euc d → ℝ) (hm : Measurable h) (B : ℝ)
    (hB : ∀ x, |h x| ≤ B) :
    ulocNormE m χ (fun x => ∫ y, h (x + y) ∂ρ) ≤
      ENNReal.ofReal (Cs * ρ.real Set.univ) * ulocNormE m χ h := by
  by_cases hM : ρ Set.univ = 0
  · have hρ : ρ = 0 := Measure.measure_univ_eq_zero.1 hM
    subst hρ
    have e : (fun x => ∫ y, h (x + y) ∂(0 : Measure (Euc d))) = fun x => (0 : ℝ) * h x := by
      funext x; simp
    rw [e]
    simpa using hCs 0 h
  · have hMtop : ρ Set.univ ≠ ⊤ := measure_ne_top ρ _
    set p : Measure (Euc d) := (ρ Set.univ)⁻¹ • ρ with hp
    haveI : IsProbabilityMeasure p := ⟨by
      simp [hp, Measure.smul_apply, ENNReal.inv_mul_cancel hM hMtop]⟩
    have hρp : ρ = (ρ Set.univ) • p := by
      rw [hp, smul_smul, ENNReal.mul_inv_cancel hM hMtop, one_smul]
    have e : (fun x => ∫ y, h (x + y) ∂ρ) =
        fun x => ρ.real Set.univ * ∫ y, h (x + y) ∂p := by
      funext x
      conv_lhs => rw [hρp]
      rw [integral_smul_measure, smul_eq_mul]
      rfl
    rw [e]
    refine (hCs _ _).trans ?_
    rw [abs_of_nonneg measureReal_nonneg]
    gcongr
    exact ulocNormE_avg_le m χ hχ p h hm B hB


/-- the weighted Gaussian average `x ↦ E[h(x + S W) ⟪c, W⟫]` -/
def ul3_wavg (S : Euc d →L[ℝ] Euc d) (c : Euc d) (h : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ w, h (x + S w) * ⟪c, w⟫ ∂(stdGaussian (Euc d))

/-- the averaging bound for a nonnegative Gaussian weight -/
theorem ul3_wavg_part (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) {Cs : ℝ}
    (hCs : ∀ (t : ℝ) (u : Euc d → ℝ), ulocNormE m χ (fun x => t * u x) ≤
      ENNReal.ofReal (Cs * |t|) * ulocNormE m χ u)
    (S : Euc d →L[ℝ] Euc d) (k : Euc d → ℝ) (hk0 : ∀ w, 0 ≤ k w) (hkc : Continuous k)
    (hki : Integrable k (stdGaussian (Euc d))) (h : Euc d → ℝ) (hm : Measurable h) (B : ℝ)
    (hB : ∀ x, |h x| ≤ B) :
    ulocNormE m χ (fun x => ∫ w, h (x + S w) * k w ∂(stdGaussian (Euc d))) ≤
      ENNReal.ofReal (Cs * ∫ w, k w ∂(stdGaussian (Euc d))) * ulocNormE m χ h := by
  set γ := stdGaussian (Euc d) with hγ
  set f : Euc d → ℝ≥0∞ := fun w => ENNReal.ofReal (k w) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp hkc.measurable
  have hflt : ∀ᵐ w ∂γ, f w < ⊤ := Filter.Eventually.of_forall fun w => ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (γ.withDensity f) :=
    isFiniteMeasure_withDensity_ofReal hki.hasFiniteIntegral
  set ρ : Measure (Euc d) := (γ.withDensity f).map S with hρ
  have hSm : Measurable S := S.continuous.measurable
  haveI : IsFiniteMeasure ρ := Measure.isFiniteMeasure_map _ _
  have hint : ∀ x, ∫ y, h (x + y) ∂ρ = ∫ w, h (x + S w) * k w ∂γ := by
    intro x
    have hAE : AEStronglyMeasurable (fun y : Euc d => h (x + y)) (γ.withDensity f |>.map S) :=
      (hm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    rw [hρ, integral_map (f := fun y : Euc d => h (x + y)) hSm.aemeasurable hAE,
      integral_withDensity_eq_integral_toReal_smul hfm hflt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hf, smul_eq_mul, ENNReal.toReal_ofReal (hk0 w)]
    ring
  have hmass : ρ.real Set.univ = ∫ w, k w ∂γ := by
    rw [measureReal_def, hρ, Measure.map_apply hSm MeasurableSet.univ, Set.preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hk0) hkc.aestronglyMeasurable]
  have := ul3_avg_finite m χ hχ hCs ρ h hm B hB
  rw [hmass] at this
  simpa only [hint] using this

/-- **signed Gaussian averages**: `‖E[h(·+SW)⟪c,W⟫]‖_{H^m_uloc} ≲ ‖c‖ ‖h‖_{H^m_uloc}` -/
theorem ul3_wavg_bound (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) {Cs : ℝ} (hCs0 : 0 ≤ Cs)
    (hCs : ∀ (t : ℝ) (u : Euc d → ℝ), ulocNormE m χ (fun x => t * u x) ≤
      ENNReal.ofReal (Cs * |t|) * ulocNormE m χ u)
    (S : Euc d →L[ℝ] Euc d) (c : Euc d) (h : Euc d → ℝ) (hm : Measurable h) (B : ℝ)
    (hB : ∀ x, |h x| ≤ B) :
    ulocNormE m χ (ul3_wavg S c h) ≤
      ENNReal.ofReal (Cs * (1 + Cs) * (‖c‖ * ∫ w, ‖w‖ ∂(stdGaussian (Euc d)))) * ulocNormE m χ h := by
  set γ := stdGaussian (Euc d) with hγ
  set kp : Euc d → ℝ := fun w => max (⟪c, w⟫) 0 with hkp
  set km : Euc d → ℝ := fun w => max (-⟪c, w⟫) 0 with hkm
  have hnorm : Integrable (fun w : Euc d => ‖w‖) γ := (IsGaussian.integrable_id (μ := γ)).norm
  have hκc : Continuous (fun w : Euc d => ⟪c, w⟫) := continuous_const.inner continuous_id
  have hkpc : Continuous kp := hκc.max continuous_const
  have hkmc : Continuous km := hκc.neg.max continuous_const
  have hbdd : ∀ w : Euc d, |⟪c, w⟫| ≤ ‖c‖ * ‖w‖ := fun w => by
    simpa using abs_real_inner_le_norm c w
  have hkpb : ∀ w, kp w ≤ ‖c‖ * ‖w‖ := fun w =>
    max_le ((le_abs_self _).trans (hbdd w)) (by positivity)
  have hkmb : ∀ w, km w ≤ ‖c‖ * ‖w‖ := fun w =>
    max_le ((neg_le_abs _).trans (hbdd w)) (by positivity)
  have hkpi : Integrable kp γ := (hnorm.const_mul ‖c‖).mono' hkpc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]; exact hkpb w)
  have hkmi : Integrable km γ := (hnorm.const_mul ‖c‖).mono' hkmc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]; exact hkmb w)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hS : Measurable S := S.continuous.measurable
  have hint : ∀ (k : Euc d → ℝ), Continuous k → Integrable k γ → ∀ x : Euc d,
      Integrable (fun w => h (x + S w) * k w) γ := by
    intro k hkc hki x
    refine (hki.norm.const_mul B).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact ((hm.comp (measurable_const.add hS)).mul hkc.measurable).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  have hsplit : ul3_wavg S c h = fun x => (∫ w, h (x + S w) * kp w ∂γ) +
      (-1 : ℝ) * ∫ w, h (x + S w) * km w ∂γ := by
    funext x
    unfold ul3_wavg
    have := integral_sub (hint kp hkpc hkpi x) (hint km hkmc hkmi x)
    rw [neg_one_mul, ← sub_eq_add_neg, ← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hkp, hkm]
    rw [← mul_sub, max_zero_sub_max_neg_zero_eq_self]
  rw [hsplit]
  refine (ul0_ulocNormE_add m χ _ _).trans ?_
  have h1 := ul3_wavg_part m χ hχ hCs S kp (fun w => le_max_right _ _) hkpc hkpi h hm B hB
  have h2 := ul3_wavg_part m χ hχ hCs S km (fun w => le_max_right _ _) hkmc hkmi h hm B hB
  have h3 := hCs (-1) (fun x => ∫ w, h (x + S w) * km w ∂γ)
  have hIp : ∫ w, kp w ∂γ ≤ ‖c‖ * ∫ w, ‖w‖ ∂γ := by
    rw [← integral_const_mul]; exact integral_mono hkpi (hnorm.const_mul _) hkpb
  have hIm : ∫ w, km w ∂γ ≤ ‖c‖ * ∫ w, ‖w‖ ∂γ := by
    rw [← integral_const_mul]; exact integral_mono hkmi (hnorm.const_mul _) hkmb
  set U := ulocNormE m χ h with hU
  calc _ ≤ ENNReal.ofReal (Cs * ∫ w, kp w ∂γ) * U +
        ENNReal.ofReal (Cs * |(-1 : ℝ)|) * (ENNReal.ofReal (Cs * ∫ w, km w ∂γ) * U) := by
        gcongr
        exact h3.trans (by gcongr)
    _ = ENNReal.ofReal (Cs * ∫ w, kp w ∂γ + Cs * (Cs * ∫ w, km w ∂γ)) * U := by
        have hn1 : 0 ≤ ∫ w, kp w ∂γ := integral_nonneg fun w => (le_max_right _ _ : (0 : ℝ) ≤ kp w)
        have hn2 : 0 ≤ ∫ w, km w ∂γ := integral_nonneg fun w => (le_max_right _ _ : (0 : ℝ) ≤ km w)
        rw [abs_neg, abs_one, mul_one, ← mul_assoc, ← ENNReal.ofReal_mul hCs0, ← add_mul,
          ← ENNReal.ofReal_add (mul_nonneg hCs0 hn1) (mul_nonneg hCs0 (mul_nonneg hCs0 hn2))]
    _ ≤ _ := by
        gcongr
        have e : Cs * (1 + Cs) * (‖c‖ * ∫ w, ‖w‖ ∂γ) =
            Cs * (‖c‖ * ∫ w, ‖w‖ ∂γ) + Cs * (Cs * (‖c‖ * ∫ w, ‖w‖ ∂γ)) := by ring
        rw [e]
        gcongr


/-- the Gaussian average is `C¹` with the derivative given by the Gaussian-weighted average -/
theorem ul3_avg_deriv {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) {B M : ℝ} (hB : ∀ y, |h y| ≤ B)
    (hM : ∀ y, ‖fderiv ℝ h y‖ ≤ M) (S : Euc d →L[ℝ] Euc d) :
    ContDiff ℝ 1 (fun x => ∫ w, h (x + S w) ∂(stdGaussian (Euc d))) ∧
      ∀ (c : Euc d) (j : Fin d), S c = EuclideanSpace.single j 1 → ∀ x,
        fderiv ℝ (fun x => ∫ w, h (x + S w) ∂(stdGaussian (Euc d))) x (EuclideanSpace.single j 1) =
          ul3_wavg S c h x := by
  set γ := stdGaussian (Euc d) with hγ
  have hSc : Continuous S := S.continuous
  have hhc : Continuous h := hh.continuous
  have hdc : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hdiff : ∀ y, DifferentiableAt ℝ h y := fun y => (hh.differentiable one_ne_zero) y
  have hd : ∀ x, HasFDerivAt (fun x => ∫ w, h (x + S w) ∂γ) (∫ w, fderiv ℝ h (x + S w) ∂γ) x := by
    intro x₀
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x w => h (x + S w))
      (F' := fun x w => fderiv ℝ h (x + S w)) (bound := fun _ => M) (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x =>
        (hhc.comp (continuous_const.add hSc)).aestronglyMeasurable
    · exact Integrable.of_bound (hhc.comp (continuous_const.add hSc)).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hB _)
    · exact (hdc.comp (continuous_const.add hSc)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun w x _ => hM _
    · exact integrable_const M
    · refine Filter.Eventually.of_forall fun w x _ => ?_
      have := (hdiff (x + S w)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (S w))
      exact this
  have hdx : ∀ x, fderiv ℝ (fun x => ∫ w, h (x + S w) ∂γ) x = ∫ w, fderiv ℝ h (x + S w) ∂γ :=
    fun x => (hd x).fderiv
  refine ⟨?_, ?_⟩
  · rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt, ?_⟩
    have : fderiv ℝ (fun x => ∫ w, h (x + S w) ∂γ) = fun x => ∫ w, fderiv ℝ h (x + S w) ∂γ :=
      funext hdx
    rw [this]
    refine continuous_of_dominated (bound := fun _ => M)
      (fun x => (hdc.comp (continuous_const.add hSc)).aestronglyMeasurable)
      (fun x => Filter.Eventually.of_forall fun w => hM _) (integrable_const M)
      (Filter.Eventually.of_forall fun w => hdc.comp (continuous_id.add continuous_const))
  · intro c j hc x
    have hint : ∀ x : Euc d, Integrable (fun w => fderiv ℝ h (x + S w)) γ := fun x =>
      Integrable.of_bound (hdc.comp (continuous_const.add hSc)).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun w => hM _)
    rw [hdx x, ContinuousLinearMap.integral_apply (hint x)]
    -- Stein
    have hst : ∀ i : Fin d, ∫ w, w i * h (x + S w) ∂γ =
        ∫ w, fderiv ℝ h (x + S w) (S (EuclideanSpace.single i 1)) ∂γ := by
      intro i
      have hF : ContDiff ℝ 1 (fun w => h (x + S w)) := hh.comp (contDiff_const.add S.contDiff)
      have hFd : ∀ w, fderiv ℝ (fun w => h (x + S w)) w = (fderiv ℝ h (x + S w)).comp S := by
        intro w
        have := (hdiff (x + S w)).hasFDerivAt.comp w ((S.hasFDerivAt).const_add x)
        exact this.fderiv
      have := ul3_stein_std hF (B := B) (M := M * ‖S‖) (fun w => hB _) (fun w => by
        rw [hFd]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))) i
      simpa [hFd] using this
    have hcexp : c = ∑ i : Fin d, c i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    have hbnd : ∀ i : Fin d, Integrable (fun w => fderiv ℝ h (x + S w) (S (EuclideanSpace.single i 1))) γ :=
      fun i => Integrable.of_bound
        ((hdc.comp (continuous_const.add hSc)).clm_apply continuous_const).aestronglyMeasurable
        (M * ‖S (EuclideanSpace.single i (1 : ℝ))‖) (Filter.Eventually.of_forall fun w => by
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
    have hfun : ∀ w, fderiv ℝ h (x + S w) (EuclideanSpace.single j 1) =
        ∑ i : Fin d, c i * fderiv ℝ h (x + S w) (S (EuclideanSpace.single i 1)) := by
      intro w
      rw [← hc]
      conv_lhs => rw [hcexp]
      simp only [map_sum, map_smul, smul_eq_mul]
    simp_rw [hfun]
    rw [integral_finsetSum _ (fun i _ => (hbnd i).const_mul (c i))]
    unfold ul3_wavg
    have hsum : ∀ w, h (x + S w) * ⟪c, w⟫ = ∑ i : Fin d, c i * (w i * h (x + S w)) := by
      intro w
      rw [PiLp.inner_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    simp_rw [hsum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_const_mul, hst i]
    · intro i _
      refine Integrable.const_mul ?_ _
      refine ((IsGaussian.integrable_id (μ := γ)).norm.mul_const B).mono'
        ((((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).mul
          (hhc.comp (continuous_const.add hSc))).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun w => ?_)
      rw [norm_mul]
      refine mul_le_mul ?_ (by simpa [Real.norm_eq_abs] using hB _) (norm_nonneg _) (norm_nonneg _)
      exact PiLp.norm_apply_le w i


open scoped MatrixOrder in
/-- `‖Sξ‖² = ⟪ξ, Cv ξ⟫` for `S = Cv^{1/2}` -/
theorem ul3_S_norm_sq {Cv : Matrix (Fin d) (Fin d) ℝ} (hCv : Cv.PosSemidef) (ξ : Euc d) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Cv)) ξ‖ ^ 2 = ξ ⬝ᵥ Cv *ᵥ ξ := by
  have hsa : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Cv)) :=
    (CFC.sqrt_nonneg Cv).isSelfAdjoint.map _
  rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_right, hsa.adjoint_eq,
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    CFC.sqrt_mul_sqrt_self _ hCv.nonneg, Matrix.inner_toEuclideanCLM]

open scoped MatrixOrder in
/-- every vector is the image of a controlled preimage under `S = Cv^{1/2}` when `Cv ≥ μ² > 0` -/
theorem ul3_S_preimage {Cv : Matrix (Fin d) (Fin d) ℝ} (hCv : Cv.PosSemidef) {μ2 : ℝ} (hμ : 0 < μ2)
    (hbd : ∀ ξ : Euc d, μ2 * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ Cv *ᵥ ξ) (v : Euc d) :
    ∃ c : Euc d, (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Cv)) c = v ∧ ‖c‖ ≤ ‖v‖ / Real.sqrt μ2 := by
  set S := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Cv) with hS
  have hinj : Function.Injective (S : Euc d →ₗ[ℝ] Euc d) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ξ hξ
    have h0 : ‖S ξ‖ ^ 2 = 0 := by
      have : S ξ = 0 := hξ
      rw [this]; simp
    rw [hS, ul3_S_norm_sq hCv] at h0
    have h1 : μ2 * ‖ξ‖ ^ 2 ≤ 0 := by
      have := hbd ξ
      linarith
    have h3 : ‖ξ‖ ^ 2 ≤ 0 := by
      by_contra hcon
      rw [not_le] at hcon
      nlinarith
    exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h3 (sq_nonneg _)))
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.1 hinj) v
  refine ⟨c, hc, ?_⟩
  have hSc : S c = v := hc
  have h1 : μ2 * ‖c‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← hSc, hS, ul3_S_norm_sq hCv]; exact hbd c
  rw [le_div_iff₀ (Real.sqrt_pos.2 hμ)]
  refine abs_le_of_sq_le_sq' ?_ (norm_nonneg _) |>.2
  rw [mul_pow, Real.sq_sqrt hμ.le]
  nlinarith


/-- **one-derivative gain for the Gaussian average** (`h ∈ C_b^1`):
`‖x ↦ E h(x+SW)‖_{H^{n+1}_uloc} ≲ (1+κ) ‖h‖_{H^n_uloc}`, where every `e_j` has a preimage of norm
`≤ κ` under `S`. -/
theorem ul3_avg_gain (n : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Euc d →L[ℝ] Euc d) (κ : ℝ), 0 ≤ κ →
      (∀ j : Fin d, ∃ c : Euc d, S c = EuclideanSpace.single j 1 ∧ ‖c‖ ≤ κ) →
      ∀ (h : Euc d → ℝ), ContDiff ℝ 1 h → ∀ B M : ℝ, (∀ y, |h y| ≤ B) → (∀ y, ‖fderiv ℝ h y‖ ≤ M) →
        ulocNormE (n + 1) χ (fun x => ∫ w, h (x + S w) ∂(stdGaussian (Euc d))) ≤
          ENNReal.ofReal (C * (1 + κ)) * ulocNormE n χ h := by
  obtain ⟨Cs, hCs0, hCs⟩ := ul3_scalar n χ
  set Cm : ℝ := ∫ w, ‖w‖ ∂(stdGaussian (Euc d)) with hCm
  have hCm0 : 0 ≤ Cm := integral_nonneg fun w => norm_nonneg _
  have hcut : ∀ j : Fin d, ∃ C : ℝ, 0 < C ∧ ∀ (z : Euc d) (u : Euc d → ℝ),
      sobolevNormE (n : ℝ) (fun x => fderiv ℝ χ (x - z) (EuclideanSpace.single j (1 : ℝ)) * u x) ≤
        ENNReal.ofReal C * ulocNormE n χ u := fun j =>
    ul3_cutoff_change n χ hχ _ (ul3_cutoff_deriv hχ j).1 (ul3_cutoff_deriv hχ j).2
  choose Cj hCj0 hCj using hcut
  set Cc : ℝ := ∑ j, Cj j with hCc
  set Cw : ℝ := Cs * (1 + Cs) * Cm with hCw
  have hCw0 : 0 ≤ Cw := mul_nonneg (mul_nonneg hCs0.le (by linarith)) hCm0
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun j _ => (hCj0 j).le
  have hdCw : 0 ≤ (d : ℝ) * Cw := mul_nonneg (Nat.cast_nonneg d) hCw0
  refine ⟨1 + Cc + d * Cw + 1, by linarith, fun S κ hκ hpre h hh B M hB hM => ?_⟩
  set γ := stdGaussian (Euc d) with hγ
  set a : Euc d → ℝ := fun x => ∫ w, h (x + S w) ∂γ with ha
  obtain ⟨haC1, hader⟩ := ul3_avg_deriv hh hB hM S
  choose c hcS hcn using hpre
  have hhm : Measurable h := hh.continuous.measurable
  set U : ℝ≥0∞ := ulocNormE n χ h with hU
  -- averaging bound for `a`
  have hSm : Measurable S := S.continuous.measurable
  have haU : ∀ m : ℕ, ulocNormE m χ a ≤ ulocNormE m χ h := by
    intro m
    haveI : IsProbabilityMeasure (γ.map S) := (Measure.isProbabilityMeasure_map_iff hSm.aemeasurable).2 inferInstance
    have := ulocNormE_avg_le m χ hχ (γ.map S) h hhm B hB
    have e : (fun x => ∫ y, h (x + y) ∂(γ.map S)) = a := by
      funext x
      exact integral_map (f := fun y : Euc d => h (x + y)) hSm.aemeasurable
        (hhm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    rwa [e] at this
  refine iSup_le fun z => ?_
  set χz : Euc d → ℝ := fun x => χ (x - z) with hχz
  have hχzs : ContDiff ℝ ∞ χz := hχ.1.comp (contDiff_id.sub contDiff_const)
  have hχzc : HasCompactSupport χz := hχ.2.1.comp_homeomorph (Homeomorph.subRight z)
  set v : Euc d → ℝ := fun x => χz x * a x with hv
  have hv1 : ContDiff ℝ 1 v := (hχzs.of_le (by exact_mod_cast le_top)).mul haC1
  have hvc : HasCompactSupport v := hχzc.mul_right
  have hstep := ul3_sobE_succ n hv1 hvc
  have hvd : ∀ (j : Fin d) (x : Euc d), fderiv ℝ v x (EuclideanSpace.single j 1) =
      fderiv ℝ χ (x - z) (EuclideanSpace.single j (1 : ℝ)) * a x + χz x * ul3_wavg S (c j) h x := by
    intro j x
    have h1 : HasFDerivAt χz (fderiv ℝ χ (x - z)) x := by
      have := (hχ.1.differentiable (by simp) (x - z)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const z)
      exact this
    have h2 : HasFDerivAt a (fderiv ℝ a x) x :=
      ((haC1.differentiable one_ne_zero) x).hasFDerivAt
    have h3 : fderiv ℝ (fun x => χz x * a x) x = χz x • fderiv ℝ a x + a x • fderiv ℝ χ (x - z) :=
      (h1.mul h2).fderiv
    have e : v = fun x => χz x * a x := rfl
    rw [e, h3]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hader (c j) j (hcS j) x]
    ring
  have hbound1 : sobolevNormE (n : ℝ) v ≤ U := by
    refine (le_iSup (fun z : Euc d => sobolevNormE (n : ℝ) fun x => χ (x - z) * a x) z).trans ?_
    exact haU n
  have hbound2 : ∀ j : Fin d, sobolevNormE (n : ℝ) (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) ≤
      ENNReal.ofReal (Cj j + Cw * κ) * U := by
    intro j
    have e : (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) = fun x =>
        fderiv ℝ χ (x - z) (EuclideanSpace.single j (1 : ℝ)) * a x +
          χ (x - z) * ul3_wavg S (c j) h x := by
      funext x; exact hvd j x
    rw [e]
    refine (HRS.MS.UlocCut.uc_tri _ _ _).trans ?_
    have t1 : sobolevNormE (n : ℝ) (fun x => fderiv ℝ χ (x - z) (EuclideanSpace.single j (1 : ℝ)) * a x) ≤
        ENNReal.ofReal (Cj j) * U := (hCj j z a).trans (by gcongr; exact haU n)
    have t2 : sobolevNormE (n : ℝ) (fun x => χ (x - z) * ul3_wavg S (c j) h x) ≤
        ENNReal.ofReal (Cw * κ) * U := by
      refine (le_iSup (fun z : Euc d => sobolevNormE (n : ℝ) fun x => χ (x - z) * ul3_wavg S (c j) h x) z).trans ?_
      refine (ul3_wavg_bound n χ hχ hCs0.le hCs S (c j) h hhm B hB).trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      rw [hCw]
      calc Cs * (1 + Cs) * (‖c j‖ * Cm) ≤ Cs * (1 + Cs) * (κ * Cm) := by
            gcongr; exact hcn j
        _ = Cs * (1 + Cs) * Cm * κ := by ring
    calc _ ≤ ENNReal.ofReal (Cj j) * U + ENNReal.ofReal (Cw * κ) * U := add_le_add t1 t2
      _ = ENNReal.ofReal (Cj j + Cw * κ) * U := by
          rw [← add_mul, ← ENNReal.ofReal_add (hCj0 j).le (by positivity)]
  have hsum : ∑ j : Fin d, sobolevNormE (n : ℝ) (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) ≤
      ∑ j : Fin d, ENNReal.ofReal (Cj j + Cw * κ) * U := Finset.sum_le_sum fun j _ => hbound2 j
  calc sobolevNormE ((n + 1 : ℕ) : ℝ) v
      ≤ sobolevNormE (n : ℝ) v + ∑ j : Fin d,
          sobolevNormE (n : ℝ) (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) := hstep
    _ ≤ U + ∑ j : Fin d, ENNReal.ofReal (Cj j + Cw * κ) * U := add_le_add hbound1 hsum
    _ = ENNReal.ofReal (1 + (Cc + d * Cw * κ)) * U := by
        rw [← Finset.sum_mul, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
          add_mul, one_mul]
        congr 1
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by have := hCj0 j; positivity)]
        congr 1
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, hCc]
        ring
    _ ≤ ENNReal.ofReal ((1 + Cc + d * Cw + 1) * (1 + κ)) * U := by
        gcongr
        nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hCw0) hκ,
          Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hCj0 j).le)]


/-- the Gaussian multiplier `e^{-λτ u}` against `(1+u)^α`, uniformly in `τ ∈ (0,T]` -/
theorem ul3_gauss_sup {lam : ℝ} (hlam : 0 < lam) (T : ℝ) {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ τ ∈ Set.Ioc (0 : ℝ) T, ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ α * Real.exp (-(lam * τ * u)) ≤ A * τ ^ (-α) := by
  set T' : ℝ := max T 1 with hT'
  have hT1 : 1 ≤ T' := le_max_right _ _
  refine ⟨2 * T' ^ 2 + 4 / lam ^ 2, by positivity, fun τ hτ u hu => ?_⟩
  have hτ0 : 0 < τ := hτ.1
  set s : ℝ := lam * τ * u with hs
  have hs0 : 0 ≤ s := by positivity
  have h1 : 1 + u ≤ (T' + s / lam) / τ := by
    rw [le_div_iff₀ hτ0]
    have : s / lam * 1 = τ * u := by rw [hs]; field_simp
    nlinarith [hτ.2, le_max_left T 1]
  have hX1 : 1 ≤ T' + s / lam := by have := div_nonneg hs0 hlam.le; linarith
  have h2 : (1 + u) ^ α ≤ τ ^ (-α) * (T' + s / lam) ^ 2 := by
    calc (1 + u) ^ α ≤ ((T' + s / lam) / τ) ^ α := Real.rpow_le_rpow (by linarith) h1 hα.le
      _ = τ ^ (-α) * (T' + s / lam) ^ α := by
          rw [Real.div_rpow (by linarith) hτ0.le, Real.rpow_neg hτ0.le]; field_simp
      _ ≤ τ ^ (-α) * (T' + s / lam) ^ 2 := by
          gcongr
          calc (T' + s / lam) ^ α ≤ (T' + s / lam) ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hX1 hα2
            _ = _ := by norm_cast
  have h3 : s ^ 2 * Real.exp (-s) ≤ 2 := by
    have := Real.quadratic_le_exp_of_nonneg hs0
    have hexp : 0 < Real.exp s := Real.exp_pos s
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hexp]
    nlinarith [sq_nonneg s]
  have h4 : (T' + s / lam) ^ 2 * Real.exp (-s) ≤ 2 * T' ^ 2 + 4 / lam ^ 2 := by
    have he1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he0 : 0 ≤ Real.exp (-s) := (Real.exp_pos _).le
    calc (T' + s / lam) ^ 2 * Real.exp (-s)
        ≤ (2 * T' ^ 2 + 2 * (s / lam) ^ 2) * Real.exp (-s) := by
          gcongr; nlinarith [sq_nonneg (T' - s / lam)]
      _ = 2 * T' ^ 2 * Real.exp (-s) + 2 / lam ^ 2 * (s ^ 2 * Real.exp (-s)) := by
          field_simp
      _ ≤ 2 * T' ^ 2 * 1 + 2 / lam ^ 2 * 2 := by
          gcongr
      _ = _ := by ring
  calc (1 + u) ^ α * Real.exp (-(lam * τ * u))
      ≤ τ ^ (-α) * (T' + s / lam) ^ 2 * Real.exp (-s) := by
        rw [← hs]; gcongr
    _ = τ ^ (-α) * ((T' + s / lam) ^ 2 * Real.exp (-s)) := by ring
    _ ≤ τ ^ (-α) * (2 * T' ^ 2 + 4 / lam ^ 2) := by gcongr
    _ = _ := by ring


/-- the Fourier transform of a translation average is the characteristic function times `ĥ` -/
theorem ul3_avg_fourier (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (h : Euc d → ℝ)
    (hm : Measurable h) (hi : Integrable h volume) :
    Integrable (fun x => ∫ y, h (x + y) ∂μ) volume ∧ ∀ ξ : Euc d,
      𝓕 (fun x : Euc d => ((∫ y, h (x + y) ∂μ : ℝ) : ℂ)) ξ =
        (∫ y, Complex.exp (↑(2 * Real.pi * ⟪y, ξ⟫) * Complex.I) ∂μ) *
          𝓕 (fun x : Euc d => ((h x : ℝ) : ℂ)) ξ := by
  have hFm : Measurable (Function.uncurry fun (x y : Euc d) => h (x + y)) :=
    hm.comp (measurable_fst.add measurable_snd)
  have hFint : Integrable (Function.uncurry fun (x y : Euc d) => h (x + y)) (volume.prod μ) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => hi.comp_add_right y, ?_⟩
    have : (fun y => ∫ x, ‖h (x + y)‖ ∂(volume : Measure (Euc d))) = fun _ => ∫ x, ‖h x‖ := by
      funext y; exact integral_add_right_eq_self (fun x => ‖h x‖) y
    simp only [Function.uncurry_apply_pair]; rw [this]; exact integrable_const _
  refine ⟨hFint.integral_prod_left, fun ξ => ?_⟩
  simp only [Real.fourier_eq']
  set E : Euc d → ℂ := fun x => Complex.exp ((↑(-2 * Real.pi * ⟪x, ξ⟫) * Complex.I)) with hE
  have hEc : Continuous E := by
    rw [hE]; fun_prop
  have hEn : ∀ x, ‖E x‖ = 1 := fun x => by
    rw [hE]; exact Complex.norm_exp_ofReal_mul_I _
  have step1 : ∀ x : Euc d, E x • (((∫ y, h (x + y) ∂μ : ℝ) : ℂ)) =
      ∫ y, E x • (((h (x + y) : ℝ) : ℂ)) ∂μ := by
    intro x
    rw [integral_smul, integral_complex_ofReal]
  have hint : Integrable (Function.uncurry fun (x y : Euc d) => E x • (((h (x + y) : ℝ) : ℂ)))
      (volume.prod μ) := by
    refine Integrable.mono' hFint.norm ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact (hEc.comp continuous_fst).measurable.smul (Complex.measurable_ofReal.comp
        (hm.comp (measurable_fst.add measurable_snd)))
    · show ‖E p.1 • (((h (p.1 + p.2) : ℝ) : ℂ))‖ ≤ ‖h (p.1 + p.2)‖
      rw [norm_smul, hEn, one_mul, Complex.norm_real]
  have hswap := integral_integral_swap hint
  have hinner : ∀ y : Euc d, ∫ x, E x • (((h (x + y) : ℝ) : ℂ)) =
      Complex.exp (↑(2 * Real.pi * ⟪y, ξ⟫) * Complex.I) * ∫ x, E x • (((h x : ℝ) : ℂ)) := by
    intro y
    have := integral_add_right_eq_self (μ := (volume : Measure (Euc d)))
      (fun x' : Euc d => E (x' - y) • (((h x' : ℝ) : ℂ))) y
    simp only [add_sub_cancel_right] at this
    rw [this, ← smul_eq_mul, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hE, smul_smul, ← Complex.exp_add]
    congr 2
    rw [inner_sub_left]
    push_cast
    ring
  refine (integral_congr_ae (Filter.Eventually.of_forall step1)).trans ?_
  rw [hswap]
  simp_rw [hinner]
  exact integral_mul_const _ _


/-- `|charFun (ouLaw τ) (2πξ)|² ≤ exp(-λ τ (4π²|ξ|²))` -/
theorem ul3_ou_charFun_sq (Q : Matrix (Fin d) (Fin d) ℝ) {ν τ lam : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (hbd : ∀ ξ : Euc d, lam * τ * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ ouCov Q ν τ *ᵥ ξ) (ξ : Euc d) :
    ‖charFun (ouLaw Q ν τ) ((2 * Real.pi) • ξ)‖ ^ 2 ≤ Real.exp (-(lam * τ * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2))) := by
  rw [ou_charFun Q hν hτ, Complex.norm_exp]
  have e : ((2 * Real.pi) • ξ).ofLp ⬝ᵥ ouCov Q ν τ *ᵥ ((2 * Real.pi) • ξ).ofLp =
      (2 * Real.pi) ^ 2 * (ξ.ofLp ⬝ᵥ ouCov Q ν τ *ᵥ ξ.ofLp) := by
    show ((2 * Real.pi) • ξ.ofLp) ⬝ᵥ ouCov Q ν τ *ᵥ ((2 * Real.pi) • ξ.ofLp) = _
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
  rw [e, ← Real.exp_nat_mul]
  simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re]
  apply Real.exp_le_exp.2
  have := hbd ξ
  push_cast
  nlinarith [Real.pi_pos, sq_nonneg Real.pi]

end HRS.MS.Ul
