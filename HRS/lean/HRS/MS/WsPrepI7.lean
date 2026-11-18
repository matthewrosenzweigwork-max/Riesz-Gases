import HRS.MS.WsPrepI6

/-!
# S21T packet 7: the i.i.d. initial comparison (`β₀ = 0`) and the assembly of INIT

* `s21i_gauss_coord0`, `s21i_firstMarginal_pi`, `s21i_smooth_of_w1`, `s21i_rate`: the Gaussian coordinate second moments, the first marginal of a
  product, `d_{C_b²} ≤ W_1`, and the exponent algebra for `Q = ⌈N^{2/17}⌉`, `ε = N^{-7/34}`.
* `s21i_iid`: for the product preparation and every window start the law of `K_bw` is within `C N^{-3/34}` of `Φ_* γ` in `d_{C_b²}` and in `W_1`
  (finite-rank projection of rank `≲ Q²` with tails `Q^{-3/4}`, Gaussian smoothing and the Lindeberg replacement `w1_iid_gauss` in `ℝ^p`).
* `s21i_init_iid`, `s21i_init`: `S21InitWin` for `β₀ = 0` and for every `β₀ ≥ 0` (the latter conditional on the tilt class when `β₀ > 0`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

theorem s21i_gauss_coord0 {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) (μ0 : Measure (Euc d))
    [IsProbabilityMeasure μ0] {γ : Measure SeqL2} [IsGaussian γ] (hγ0 : ∫ z, id z ∂γ = 0)
    (hcov : ∀ x y, covarianceBilin γ x y = covarianceBilin (μ0.map (s21iY φ μ0)) x y) (k : ℕ) :
    ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂γ ≤ ENNReal.ofReal (4 * cbNorm J (φ k) ^ 2) := by
  set Y := s21iY φ μ0 with hYdef
  have hY : Measurable Y := s21iY_meas hφ μ0
  haveI hμY : IsProbabilityMeasure (μ0.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have hYmem : MemLp id 2 (μ0.map Y) := by
    refine MemLp.of_bound aestronglyMeasurable_id (2 * featureSum J φ) ?_
    exact (ae_map_iff (μ := μ0) hY.aemeasurable
      (p := fun v : SeqL2 => ‖v‖ ≤ 2 * featureSum J φ)
      (isClosed_le continuous_norm continuous_const).measurableSet).2
      (ae_of_all _ fun x => s21iY_norm hφ μ0 x)
  have hYmean : ∫ z, id z ∂(μ0.map Y) = 0 := by
    rw [integral_map hY.aemeasurable aestronglyMeasurable_id]
    exact s21iY_mean hφ μ0
  have hmemγ : MemLp id 2 γ := IsGaussian.memLp_two_id
  have hint : Integrable (fun z : SeqL2 => SeqL2.coord z k ^ 2) γ := by
    have h1 : MemLp (fun z : SeqL2 => SeqL2.coord z k) 2 γ :=
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) k).comp_memLp' hmemγ
    exact h1.integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcv := hcov (s21hSingle k) (s21hSingle k)
  rw [covarianceBilin_apply hmemγ, hγ0, covarianceBilin_apply hYmem, hYmean] at hcv
  simp only [id, sub_zero, s21h_inner_single] at hcv
  have e1 : ∫ z, SeqL2.coord z k ^ 2 ∂γ = ∫ z, SeqL2.coord z k * SeqL2.coord z k ∂γ := by simp [sq]
  have hfm : AEStronglyMeasurable (fun z : SeqL2 => SeqL2.coord z k * SeqL2.coord z k) (μ0.map Y) :=
    (((s21h_continuous_coord k).mul (s21h_continuous_coord k)) :
      Continuous fun z : SeqL2 => SeqL2.coord z k * SeqL2.coord z k).aestronglyMeasurable
  rw [e1, hcv, integral_map hY.aemeasurable hfm]
  have hb1 : ∀ x, |φ k x| ≤ cbNorm J (φ k) := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 k) x
    rwa [Real.norm_eq_abs] at this
  have hb2 : |HRS.Whole.pair μ0 (φ k)| ≤ cbNorm J (φ k) := by
    have := norm_integral_le_of_norm_le_const (μ := μ0) (f := φ k) (C := cbNorm J (φ k))
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hb1 x)
    simpa [HRS.Whole.pair, Real.norm_eq_abs, Measure.real] using this
  calc ∫ x, SeqL2.coord (Y x) k * SeqL2.coord (Y x) k ∂μ0 ≤ ∫ _x, 4 * cbNorm J (φ k) ^ 2 ∂μ0 := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => mul_self_nonneg _) (integrable_const _)
          (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [hYdef, s21iY_coord hφ]
        have h3 : |φ k x - HRS.Whole.pair μ0 (φ k)| ≤ 2 * cbNorm J (φ k) :=
          (abs_sub _ _).trans (by linarith [hb1 x, hb2])
        calc (φ k x - HRS.Whole.pair μ0 (φ k)) * (φ k x - HRS.Whole.pair μ0 (φ k))
            = |φ k x - HRS.Whole.pair μ0 (φ k)| * |φ k x - HRS.Whole.pair μ0 (φ k)| := (abs_mul_abs_self _).symm
          _ ≤ (2 * cbNorm J (φ k)) * (2 * cbNorm J (φ k)) := mul_self_le_mul_self (abs_nonneg _) h3
          _ = 4 * cbNorm J (φ k) ^ 2 := by ring
    _ = 4 * cbNorm J (φ k) ^ 2 := by simp

theorem s21i_firstMarginal_pi {N : ℕ} (hN : 1 ≤ N) (μ0 : Measure (Euc d)) [IsProbabilityMeasure μ0] :
    HRS.Whole.firstMarginal (Measure.pi fun _ : Fin N => μ0) = μ0 := by
  have : HRS.Whole.firstMarginal (Measure.pi fun _ : Fin N => μ0) =
      (Measure.pi fun _ : Fin N => μ0).map (fun X : EucConfig d N => X ⟨0, by omega⟩) := by
    unfold HRS.Whole.firstMarginal; rw [dif_pos (by omega)]
  rw [this]
  have h := Measure.pi_map_eval (μ := fun _ : Fin N => μ0) (⟨0, by omega⟩ : Fin N)
  simp only [measure_univ, Finset.prod_const_one, one_smul] at h
  exact h

theorem s21i_smooth_of_w1 {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
    (a b : Measure B) [IsProbabilityMeasure a] [IsProbabilityMeasure b] {X : ℝ} (hX : 0 ≤ X)
    (h : wassersteinE 1 a b ≤ ENNReal.ofReal X) : smoothDist 2 a b ≤ X := by
  have h1 := smoothDist_one_le_wasserstein a b
  have h2 := (ENNReal.ofReal_le_ofReal_iff hX).1 (h1.trans h)
  exact (smoothDist_succ_le 1 _ _).trans h2

theorem s21i_rate {n : ℝ} (hn : 1 ≤ n) {K τ B c : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ) {Q p : ℕ}
    (hQ1 : n ^ ((2 : ℝ) / 17) ≤ Q) (hQ2 : (Q : ℝ) ≤ 2 * n ^ ((2 : ℝ) / 17)) (hp : (p : ℝ) ≤ K * (Q : ℝ) ^ 2) :
    τ / (Q : ℝ) ^ ((3 : ℝ) / 4) ≤ τ * n ^ (-(3 : ℝ) / 34) ∧
    n ^ (-(7 : ℝ) / 34) * Real.sqrt p ≤ 2 * Real.sqrt K * n ^ (-(3 : ℝ) / 34) ∧
    2 / (n ^ (-(7 : ℝ) / 34)) ^ 2 * (c * ((Real.sqrt n)⁻¹ * B ^ 3)) = 2 * c * B ^ 3 * n ^ (-(3 : ℝ) / 34) := by
  have hn0 : 0 < n := by linarith
  have hq0 : 0 < n ^ ((2 : ℝ) / 17) := Real.rpow_pos_of_pos hn0 _
  refine ⟨?_, ?_, ?_⟩
  · have h1 : n ^ ((3 : ℝ) / 34) ≤ (Q : ℝ) ^ ((3 : ℝ) / 4) := by
      calc n ^ ((3 : ℝ) / 34) = (n ^ ((2 : ℝ) / 17)) ^ ((3 : ℝ) / 4) := by
            rw [← Real.rpow_mul hn0.le]; congr 1; ring
        _ ≤ (Q : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow hq0.le hQ1 (by norm_num)
    have h2 : 0 < n ^ ((3 : ℝ) / 34) := Real.rpow_pos_of_pos hn0 _
    calc τ / (Q : ℝ) ^ ((3 : ℝ) / 4) ≤ τ / n ^ ((3 : ℝ) / 34) := div_le_div_of_nonneg_left hτ h2 h1
      _ = τ * n ^ (-(3 : ℝ) / 34) := by
          rw [div_eq_mul_inv, show -(3 : ℝ) / 34 = -((3 : ℝ) / 34) by ring, Real.rpow_neg hn0.le]
  · have hQ0 : (0 : ℝ) ≤ Q := hq0.le.trans hQ1
    have hsp : Real.sqrt p ≤ Real.sqrt K * (2 * n ^ ((2 : ℝ) / 17)) := by
      calc Real.sqrt p ≤ Real.sqrt (K * (Q : ℝ) ^ 2) := Real.sqrt_le_sqrt hp
        _ = Real.sqrt K * (Q : ℝ) := by rw [Real.sqrt_mul hK, Real.sqrt_sq hQ0]
        _ ≤ Real.sqrt K * (2 * n ^ ((2 : ℝ) / 17)) := by gcongr
    have hm : n ^ (-(7 : ℝ) / 34) * n ^ ((2 : ℝ) / 17) = n ^ (-(3 : ℝ) / 34) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    calc n ^ (-(7 : ℝ) / 34) * Real.sqrt p ≤ n ^ (-(7 : ℝ) / 34) * (Real.sqrt K * (2 * n ^ ((2 : ℝ) / 17))) :=
          mul_le_mul_of_nonneg_left hsp (Real.rpow_nonneg hn0.le _)
      _ = 2 * Real.sqrt K * (n ^ (-(7 : ℝ) / 34) * n ^ ((2 : ℝ) / 17)) := by ring
      _ = 2 * Real.sqrt K * n ^ (-(3 : ℝ) / 34) := by rw [hm]
  · have e1 : (n ^ (-(7 : ℝ) / 34)) ^ 2 = n ^ (-(7 : ℝ) / 17) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; push_cast; ring
    have hs : (Real.sqrt n)⁻¹ = n ^ (-(1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hn0.le]
    have hd : 2 / n ^ (-(7 : ℝ) / 17) = 2 * n ^ ((7 : ℝ) / 17) := by
      rw [show -(7 : ℝ) / 17 = -((7 : ℝ) / 17) by ring, Real.rpow_neg hn0.le, div_inv_eq_mul]
    have hm2 : n ^ ((7 : ℝ) / 17) * n ^ (-(1 : ℝ) / 2) = n ^ (-(3 : ℝ) / 34) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    rw [e1, hd, hs]
    calc 2 * n ^ ((7 : ℝ) / 17) * (c * (n ^ (-(1 : ℝ) / 2) * B ^ 3))
        = 2 * c * B ^ 3 * (n ^ ((7 : ℝ) / 17) * n ^ (-(1 : ℝ) / 2)) := by ring
      _ = 2 * c * B ^ 3 * n ^ (-(3 : ℝ) / 34) := by rw [hm2]

set_option maxHeartbeats 3200000 in
/-- The i.i.d. initial comparison at the window start `bw`: both distances are at most `C N^{-3/34}`. -/
theorem s21i_iid (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {T : ℝ} (hT : 0 < T) {Corb : ℝ}
    (hCorb : 0 ≤ Corb) :
    ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ (C : WholeCoeff d), S21iOrb d T C Corb →
      ∀ (μ0 : Measure (Euc d)) [IsProbabilityMeasure μ0], ∀ N : ℕ, 2 ≤ N → ∀ bw : ℝ, 0 ≤ bw →
      ∃ γ0 : Measure (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T), IsProbabilityMeasure γ0 ∧
        (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
          (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) μ0 0
            (propagatorW C 0 (bw + ts i) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
            (propagatorW C 0 (bw + ts j) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j)))).PosSemidef ∧
          γ0.map (fun w : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => (WithLp.toLp 2 fun i =>
              OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
            multivariateGaussian 0 (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) μ0 0
              (propagatorW C 0 (bw + ts i) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
              (propagatorW C 0 (bw + ts j) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))))) ∧
        smoothDist 2 ((HRS.Whole.modulatedGibbs (rieszKernel d s) N 0 μ0).map
            (s21iK C ((wholeSpaceIndex d : ℕ) : ℝ) T μ0 bw)) γ0 ≤
          Ci * (N : ℝ) ^ (-(3 : ℝ) / 34) ∧
        wassersteinE 1 ((HRS.Whole.modulatedGibbs (rieszKernel d s) N 0 μ0).map
            (s21iK C ((wholeSpaceIndex d : ℕ) : ℝ) T μ0 bw)) γ0 ≤
          ENNReal.ofReal (Ci * (N : ℝ) ^ (-(3 : ℝ) / 34)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨σ⟩ := s11p_exists_equiv (d := d)
  have hγ0 : 5 * (d : ℝ) / 4 < 3 * (d : ℝ) + 30 := by linarith
  obtain ⟨K, τ₀, hK, hτ₀, hbox⟩ := s21h_box_osc hd1 σ hγ0 (fun k => s21iW d Corb (σ k))
    (fun k => s21i_W_nonneg hCorb (σ k)) (A := Corb) (fun k => by
      have e : s21iB d (σ k).2 = oscEigenvalue d (σ k).2 ^ (-(3 * (d : ℝ) + 30)) := by
        unfold s21iB; congr 1; push_cast; ring
      unfold s21iW; rw [e]; exact le_of_eq (by ring))
  obtain ⟨cJ, hcJdef⟩ : ∃ cJ : ℝ, cJ = s11p_cJ T := ⟨_, rfl⟩
  have hcJ0 : 0 < cJ := by rw [hcJdef]; exact s11p_cJ_pos T
  obtain ⟨S0, hS0def⟩ : ∃ S0 : ℝ, S0 = s21iS0 d Corb := ⟨_, rfl⟩
  have hS00 : 0 ≤ S0 := by rw [hS0def]; exact tsum_nonneg fun q => s21i_W_nonneg hCorb q
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * S0 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = 2 * τ₀ := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  obtain ⟨c4', hc4'⟩ : ∃ c4' : ℝ, c4' = 2 + HRS.Yurinskii.c4 / 2 := ⟨_, rfl⟩
  have hc4'0 : 0 ≤ c4' := by
    have := HRS.Yurinskii.c4_nonneg
    rw [hc4']; positivity
  obtain ⟨Ci, hCi⟩ : ∃ Ci : ℝ, Ci = cJ * (2 * τ + 4 * Real.sqrt K + 2 * c4' * B ^ 3) := ⟨_, rfl⟩
  have hCi0 : 0 ≤ Ci := by rw [hCi]; positivity
  refine ⟨Ci, hCi0, ?_⟩
  intro C horb μ0 _ N hN bw hbw
  have hN1 : 1 ≤ N := by omega
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  obtain ⟨D, hD, hDw⟩ := s21i_orb_data hd1 horb bw hbw
  have hU := s21i_series_of_orb hT horb hbw D hD
  obtain ⟨hφ, hSle, hcbw⟩ := s21i_family hd1 horb hbw D hD hDw σ
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℕ → Euc d → ℝ, φ = fun j => D.f (σ j) := ⟨_, rfl⟩
  have hSle' : featureSum (4 * d + 42) φ ≤ S0 := by rw [hφdef, hS0def]; exact hSle
  have hcbw2 : ∀ k, cbNorm (4 * d + 42) (φ k) ≤ s21iW d Corb (σ k) := fun k => by rw [hφdef]; exact hcbw k
  rw [← hφdef] at hφ
  have hU' : S11pSeries D T (fun α u x => propagatorW C 0 (bw + u)
      (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x) := hU
  obtain ⟨γ, hγp, hγg, hγcov⟩ := s21i_gauss_iid hφ μ0
  haveI hGg : IsGaussian γ := hγg.1
  have hγ0' : ∫ z, id z ∂γ = 0 := HRS.HilbertCLTAux.gaussian_mean_zero hγg
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : SeqL2 →L[ℝ] OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T,
      Φ = s21gPhi σ hT ((wholeSpaceIndex d : ℕ) : ℝ) := ⟨_, rfl⟩
  have hΦn : ‖Φ‖ ≤ cJ := by rw [hΦdef, hcJdef]; exact s21gPhi_norm_le σ hT _
  obtain ⟨P, hP⟩ : ∃ P : Measure (EucConfig d N), P = Measure.pi fun _ : Fin N => μ0 := ⟨_, rfl⟩
  haveI hPp : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hfm0 : Measurable (featureVec φ μ0 : EucConfig d N → SeqL2) := S45.s45_feature_measurable hN1 hφ
  have hpath : ∀ x : EucConfig d N, s21iK C ((wholeSpaceIndex d : ℕ) : ℝ) T μ0 bw x =
      Φ (featureVec φ μ0 x) := fun x => by
    rw [hΦdef, hφdef]; exact s21i_path_eq hT bw D hU' σ (by rw [← hφdef]; exact hφ) μ0 hN1 x
  obtain ⟨μ, hμdef⟩ : ∃ μ : Measure SeqL2, μ = P.map (featureVec φ μ0) := ⟨_, rfl⟩
  haveI hμp : IsProbabilityMeasure μ := by
    rw [hμdef]; exact (Measure.isProbabilityMeasure_map_iff hfm0.aemeasurable).2 inferInstance
  have hmapeq : P.map (s21iK C ((wholeSpaceIndex d : ℕ) : ℝ) T μ0 bw) = μ.map Φ := by
    rw [hμdef, Measure.map_map Φ.continuous.measurable hfm0]
    congr 1
    funext x
    exact hpath x
  have hγpm : IsProbabilityMeasure (γ.map Φ) :=
    (Measure.isProbabilityMeasure_map_iff Φ.continuous.measurable.aemeasurable).2 inferInstance
  haveI hμΦ : IsProbabilityMeasure (μ.map Φ) :=
    (Measure.isProbabilityMeasure_map_iff Φ.continuous.measurable.aemeasurable).2 inferInstance
  -- the main estimate
  have hmain : wassersteinE 1 (μ.map Φ) (γ.map Φ) ≤ ENNReal.ofReal (Ci * (N : ℝ) ^ (-(3 : ℝ) / 34)) := by
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (N : ℝ) ^ ((2 : ℝ) / 17) := ⟨_, rfl⟩
    have hq1 : 1 ≤ q := by rw [hq]; exact Real.one_le_rpow hn (by norm_num)
    obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = ⌈q⌉₊ := ⟨_, rfl⟩
    have hQ1 : q ≤ Q := by rw [hQdef]; exact Nat.le_ceil _
    have hQ2 : (Q : ℝ) ≤ 2 * q := by
      have : (Q : ℝ) < q + 1 := by rw [hQdef]; exact Nat.ceil_lt_add_one (by linarith)
      linarith
    have hQ0 : 1 ≤ Q := by
      have : (1 : ℝ) ≤ Q := hq1.trans hQ1
      exact_mod_cast this
    obtain ⟨I, hI, hT'⟩ := hbox Q hQ0
    obtain ⟨c, e, hc, he, hce⟩ := s21h_scheme_of_subspace (s21hSpan I)
    have hpI : (Module.finrank ℝ (s21hSpan I) : ℝ) ≤ K * (Q : ℝ) ^ 2 := by
      rw [s21h_finrank_span]; exact hI
    -- tails
    have hw0 : ∀ k, 0 ≤ s21iW d Corb (σ k) := fun k => s21i_W_nonneg hCorb (σ k)
    have hWσ : Summable fun k => s21iW d Corb (σ k) := (Equiv.summable_iff σ).2 (s21i_W_summable hd1 Corb)
    have hsc0 : ∀ k, 0 ≤ 4 * s21iW d Corb (σ k) ^ 2 := fun k => by positivity
    have hsum : Summable fun k => 4 * s21iW d Corb (σ k) ^ 2 := (S45.s45_summable_sq hw0 hWσ).mul_left 4
    have hcb0 : ∀ k, 0 ≤ cbNorm (4 * d + 42) (φ k) := fun k => HRS.MS.Tc5.tc5_cb_nonneg _ _
    have hcbw' : ∀ k, cbNorm (4 * d + 42) (φ k) ^ 2 ≤ s21iW d Corb (σ k) ^ 2 := fun k =>
      pow_le_pow_left₀ (hcb0 k) (hcbw2 k) 2
    have hexch : HRS.Whole.IsExchangeable P := by
      have := HRS.Whole.modulatedGibbs_isExchangeable (N := N) (rieszKernel d s) 0 μ0
        (fun x => HRS.Whole.rieszKernel_neg x)
      rw [s11iid_gibbs_zero] at this
      rwa [hP]
    have hν : HRS.Whole.firstMarginal P = μ0 := by rw [hP]; exact s21i_firstMarginal_pi hN1 μ0
    have hsμ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂μ ≤
        ENNReal.ofReal (4 * s21iW d Corb (σ k) ^ 2) := fun k => by
      have h := s21i_particle_coord (μ0 := μ0) (Cs := 1) hN zero_le_one hexch
        (fun f hf hf2 => by rw [hP]; simpa using s21i_iid_linear hN1 hf hf2) hφ k
      rw [hν, ← hμdef] at h
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      nlinarith [hcbw' k]
    have hsγ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂γ ≤
        ENNReal.ofReal (4 * s21iW d Corb (σ k) ^ 2) := fun k =>
      (s21i_gauss_coord0 hφ μ0 hγ0' hγcov k).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hcbw' k) (by norm_num)))
    have hT'' : ∑' k : ℕ, (if k ∈ I then 0 else 4 * s21iW d Corb (σ k) ^ 2) ≤
        τ ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2) := by
      have e' : (∑' k : ℕ, (if k ∈ I then 0 else 4 * s21iW d Corb (σ k) ^ 2)) =
          4 * ∑' k : ℕ, (if k ∈ I then 0 else s21iW d Corb (σ k) ^ 2) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        split_ifs <;> simp
      rw [e', hτ, mul_pow, mul_div_assoc]
      have : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [this]
      exact mul_le_mul_of_nonneg_left hT' (by norm_num)
    have hμt := s21i_tail μ hτ0 _ hsc0 hsum hsμ hQ0 hT''
    have hγt := s21i_tail γ hτ0 _ hsc0 hsum hsγ hQ0 hT''
    simp_rw [← hce] at hμt hγt
    -- the middle leg
    have hε : 0 < (N : ℝ) ^ (-(7 : ℝ) / 34) := Real.rpow_pos_of_pos (by linarith) _
    have hYB : ∀ x, ‖s21iY φ μ0 x‖ ≤ B := fun x =>
      (s21iY_norm hφ μ0 x).trans (by rw [hB]; linarith [hSle'])
    have hmid0 := s21i_mid_iid (s21iY φ μ0) (s21iY_meas hφ μ0) hYB (s21iY_mean hφ μ0) hN1 γ hγ0' hγcov c hc hε
    have hμeq : μ = (Measure.pi fun _ : Fin N => μ0).map
        (fun X : Fin N → Euc d => (Real.sqrt N)⁻¹ • ∑ i, s21iY φ μ0 (X i)) := by
      rw [hμdef, hP]; congr 1; funext X; exact s21i_featureVec_eq hφ μ0 hN1 X
    rw [← hμeq, ← hc4'] at hmid0
    have hr := s21i_rate (n := (N : ℝ)) hn (K := K) (τ := τ) (B := B) (c := c4') hK hτ0
      (by rw [← hq]; exact hQ1) (by rw [← hq]; exact hQ2) hpI
    obtain ⟨hr1, hr2, hr3⟩ := hr
    have hsch := s21i_w1_scheme Φ μ γ c e he hμt hγt hmid0
    refine hsch.trans ?_
    obtain ⟨bb, hbb⟩ : ∃ bb : ℝ, bb = τ / (Q : ℝ) ^ ((3 : ℝ) / 4) := ⟨_, rfl⟩
    obtain ⟨mm, hmm⟩ : ∃ mm : ℝ, mm = 2 * (N : ℝ) ^ (-(7 : ℝ) / 34) * Real.sqrt (Module.finrank ℝ (s21hSpan I)) +
      2 / ((N : ℝ) ^ (-(7 : ℝ) / 34)) ^ 2 * (c4' * ((Real.sqrt N)⁻¹ * B ^ 3)) := ⟨_, rfl⟩
    have hbb0 : 0 ≤ bb := by rw [hbb]; positivity
    have hmm0 : 0 ≤ mm := by rw [hmm]; positivity
    rw [← hbb, ← hmm, ← ENNReal.ofReal_add hbb0 hmm0, ← ENNReal.ofReal_add (add_nonneg hbb0 hmm0) hbb0,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hnn : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 34) := Real.rpow_nonneg (by linarith) _
    have hsum' : bb + mm + bb ≤ (2 * τ + 4 * Real.sqrt K + 2 * c4' * B ^ 3) * (N : ℝ) ^ (-(3 : ℝ) / 34) := by
      have e2 : mm = 2 * ((N : ℝ) ^ (-(7 : ℝ) / 34) * Real.sqrt (Module.finrank ℝ (s21hSpan I))) +
          2 / ((N : ℝ) ^ (-(7 : ℝ) / 34)) ^ 2 * (c4' * ((Real.sqrt N)⁻¹ * B ^ 3)) := by
        rw [hmm]; ring
      rw [hbb, e2]
      nlinarith [hr1, hr2, hr3]
    calc ‖Φ‖ * (bb + mm + bb) ≤ cJ * (bb + mm + bb) := by
          exact mul_le_mul_of_nonneg_right hΦn (by positivity)
      _ ≤ cJ * ((2 * τ + 4 * Real.sqrt K + 2 * c4' * B ^ 3) * (N : ℝ) ^ (-(3 : ℝ) / 34)) :=
          mul_le_mul_of_nonneg_left hsum' hcJ0.le
      _ = Ci * (N : ℝ) ^ (-(3 : ℝ) / 34) := by rw [hCi]; ring
  refine ⟨γ.map Φ, hγpm, ?_, ?_, ?_⟩
  · have := s21i_fdd0 (m := ((wholeSpaceIndex d : ℕ) : ℝ)) hT hU' σ (by rw [← hφdef]; exact hφ) (rieszKernel d s) μ0 hγ0'
      (by rw [hφdef] at hγcov; exact hγcov)
    rw [hΦdef]
    exact this
  · rw [s11iid_gibbs_zero, ← hP, hmapeq]
    exact s21i_smooth_of_w1 _ _ (by rw [hCi]; positivity) hmain
  · rw [s11iid_gibbs_zero, ← hP, hmapeq]
    exact hmain

theorem s21i_init_iid (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T : ℝ} (hT : 0 < T) {εstar c₁ C₁ Corb : ℝ} (horb : S21iOrbClass d s a β T εstar c₁ C₁ Corb) :
    ∃ Cinit : ℝ, 0 ≤ Cinit ∧ S21InitWin d s a β 0 T εstar c₁ C₁ Cinit := by
  by_cases hne : ∃ (ρβ : Euc d → ℝ), IsThermalEquilibrium d s a β ρβ ∧ ∃ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      IsAdmissiblePerturbation ρβ εstar ε ψ ∧ IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ
  swap
  · refine ⟨0, le_rfl, fun ρβ hρβ ε ψ hψ ρ hρ => absurd ⟨ρβ, hρβ, ε, ψ, ρ, hψ, hρ⟩ hne⟩
  obtain ⟨ρβ₁, hρβ₁, ε₁, ψ₁, ρ₁, hψ₁, hρ₁⟩ := hne
  have hCorb : 0 ≤ Corb := (horb ρβ₁ hρβ₁ ε₁ ψ₁ hψ₁ ρ₁ hρ₁).1
  obtain ⟨Ci, hCi, hI⟩ := s21i_iid hd hs0 hsd hT hCorb
  refine ⟨Ci, hCi, fun ρβ hρβ ε ψ hψ ρ hρ N hN bw hbw => ?_⟩
  have hρ0 : HRS.Whole.IsProbDensity (ρ 0) := (hρ.global 0).density 0 ⟨le_rfl, le_rfl⟩
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal (ρ 0)) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ0
  obtain ⟨γ0, hγ0, hfdd, hsm, hw1⟩ := hI _ (horb ρβ hρβ ε ψ hψ ρ hρ) (HRS.Whole.withDensityReal (ρ 0)) N hN bw hbw
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hrate : Ci * (N : ℝ) ^ (-(3 : ℝ) / 34) ≤
      Ci * (Real.sqrt N * HRS.deltaN d s N + iN d s 0 N) := by
    have hi : iN d s 0 N = (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 6))) := by simp [iN]
    have hdelta : 0 < HRS.deltaN d s N := s21_deltaN_pos hs0 hsd N (by omega)
    have hexp : -(3 : ℝ) / 34 ≤ -(1 / (4 * (d : ℝ) + 6)) := by
      have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have h1 : (N : ℝ) ^ (-(3 : ℝ) / 34) ≤ (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 6))) :=
      Real.rpow_le_rpow_of_exponent_le hN1 hexp
    rw [hi]
    refine mul_le_mul_of_nonneg_left (h1.trans ?_) hCi
    have : 0 ≤ Real.sqrt N * HRS.deltaN d s N := by positivity
    linarith
  refine ⟨γ0, hγ0, hfdd, hsm.trans hrate, ?_⟩
  refine hw1.trans (ENNReal.ofReal_le_ofReal ?_)
  refine hrate.trans (le_of_eq ?_)
  simp [iN, jN]

/-- INIT: the initial comparison for every preparation parameter `β₀ ≥ 0`, from the S10.3 orbit input and (for `β₀ > 0`) the uniform tilt class. -/
theorem s21i_init (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β β₀ : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hβ₀ : 0 ≤ β₀) {T : ℝ} (hT : 0 < T) {εstar c₁ C₁ Corb : ℝ}
    (horb : S21iOrbClass d s a β T εstar c₁ C₁ Corb)
    (htilt : 0 < β₀ → S21iTiltClass d s a β β₀ (4 * d + 42) εstar) :
    ∃ Cinit : ℝ, 0 ≤ Cinit ∧ S21InitWin d s a β β₀ T εstar c₁ C₁ Cinit := by
  rcases hβ₀.eq_or_lt with h | h
  · subst h
    exact s21i_init_iid hd hs0 hsd ha hβ hT horb
  · exact s21i_init_gibbs hd hs0 hsd ha hβ h hT horb (htilt h)

end HRS.MS.S21
