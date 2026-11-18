import HRS.MS.Fp81S21RawIncr
import HRS.MS.S21G2_S12F

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Classical Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111T HRS.MS.S111X2

private theorem fp81s21_enorm_fourth_real (x : ℝ) :
    ‖x‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (x ^ 4) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x) (by norm_num)]
  congr 1
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.norm_eq_abs]
  calc
    |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
    _ = (x ^ 2) ^ 2 := by rw [sq_abs]
    _ = x ^ 4 := by ring

/-- A raw coordinate increment is the series observation of the feature
increment, and its centered Gaussian law has exactly that feature variance.
The same witness-independent bound gives the fourth moment required by the
coordinate-to-norm adapter. -/
theorem fp81s21_raw_scalar_increment_fourth
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
      Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (Z0 : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ))
    (hParseval : ∀ h h' : GaussianFeatureHilbert,
      HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h')
        (inner ℝ h h'))
    (hstd : HRS.IsStdGaussianSeq P ξ)
    (hWmeas : ∀ h, Measurable (W h))
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun m : ℕ =>
      ∫ ω, (s21g2_s11a_S ξ (fun n => inner ℝ (e n) h) m ω - W h ω) ^ 2 ∂P)
        atTop (𝓝 0))
    (hJoint : ∀ (n : ℕ) (τ : Fin n → ℝ)
      (φ : Fin n → Euc p.d → ℝ),
      (∀ i, 0 ≤ τ i) →
      (∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) →
      HRS.IsCenteredGaussian
        (P.map fun ω i => W (J (fp81s21_combinedFeature p R hK
          (τ i) (φ i))) ω))
    (hZmeas : ∀ u : ℝ, Measurable (Z0 u))
    (hcoord : ∀ u : ℝ, 0 ≤ u → ∀ᵐ ω ∂P, ∀ α : MultiIndex p.d,
      OscDual.coord (Z0 u ω) α =
        W (J (fp81s21_combinedFeature p R hK u
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) ω)
    (s t H : ℝ) (hs : s ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (α : MultiIndex p.d) (L : MultiIndex p.d → ℝ)
    (hL0 : 0 ≤ L α)
    (hInc : ‖fp81s21_combinedFeature p R hK t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
      fp81s21_combinedFeature p R hK s
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2 ≤ L α * |t - s|) :
    (∀ᵐ ω ∂P,
      OscDual.coord (Z0 t ω) α - OscDual.coord (Z0 s ω) α =
        W (J (fp81s21_combinedFeature p R hK t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
          fp81s21_combinedFeature p R hK s
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) ω) ∧
    HRS.IsCenteredGaussian
      (P.map fun ω => OscDual.coord (Z0 t ω) α - OscDual.coord (Z0 s ω) α) ∧
    P.map (fun ω => OscDual.coord (Z0 t ω) α - OscDual.coord (Z0 s ω) α) =
      gaussianReal 0 (Real.toNNReal
        (‖fp81s21_combinedFeature p R hK t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
          fp81s21_combinedFeature p R hK s
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2)) ∧
    (∫ ω, (OscDual.coord (Z0 t ω) α - OscDual.coord (Z0 s ω) α) ^ 2 ∂P) =
      ‖fp81s21_combinedFeature p R hK t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
        fp81s21_combinedFeature p R hK s
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2 ∧
    ∫⁻ ω, ‖OscDual.coord (Z0 t ω) α - OscDual.coord (Z0 s ω) α‖ₑ ^
        (4 : ℝ) ∂P ≤ ENNReal.ofReal (3 * (L α * |t - s|) ^ 2) := by
  let ψ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let Ft := fp81s21_combinedFeature p R hK t ψ
  let Fs := fp81s21_combinedFeature p R hK s ψ
  let Dt : Ω → ℝ := fun ω => OscDual.coord (Z0 t ω) α - OscDual.coord (Z0 s ω) α
  let times : Fin 2 → ℝ := fun i => if i = 0 then t else s
  let vec : Ω → Fin 2 → ℝ := fun ω i =>
    W (J (fp81s21_combinedFeature p R hK (times i) ψ)) ω
  let ell : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1
  let Dser : Ω → ℝ := fun ω => ell (vec ω)
  have hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) ψ :=
    HRS.MS.GenPath.s56_isOscTest _ α
  have ht0 : 0 ≤ t := ht.1
  have hs0 : 0 ≤ s := hs.1
  have htimes : ∀ i : Fin 2, 0 ≤ times i := by
    intro i
    fin_cases i <;> simp [times, ht0, hs0]
  have htests : ∀ i : Fin 2, IsOscTest (wholeSpaceIndex p.d : ℝ) ψ :=
    fun _ => hψ
  have hJvec : HRS.IsCenteredGaussian (P.map vec) := by
    exact hJoint 2 times (fun _ => ψ) htimes htests
  have hvecMeas : Measurable vec := by
    apply measurable_pi_iff.2
    intro i
    exact hWmeas (J (fp81s21_combinedFeature p R hK (times i) ψ))
  have hmapDser : P.map Dser = (P.map vec).map ell := by
    rw [Measure.map_map ell.continuous.measurable hvecMeas]
    rfl
  have hDserCentered : HRS.IsCenteredGaussian (P.map Dser) := by
    rw [hmapDser]
    exact HRS.MS.R26T3.s21g2_s12_cg_map hJvec ell
  have hcoordDiff : Dt =ᵐ[P] fun ω =>
      W (J (fp81s21_combinedFeature p R hK t ψ)) ω -
        W (J (fp81s21_combinedFeature p R hK s ψ)) ω := by
    filter_upwards [hcoord t ht0, hcoord s hs0] with ω hωt hωs
    simp only [Dt, hωt α, hωs α, ψ]
  have hDserEq : Dser =ᵐ[P] fun ω =>
      W (J (fp81s21_combinedFeature p R hK t ψ)) ω -
        W (J (fp81s21_combinedFeature p R hK s ψ)) ω := by
    filter_upwards [] with ω
    simp [Dser, ell, vec, times, ψ]
  have hDae : Dt =ᵐ[P] Dser := hcoordDiff.trans hDserEq.symm
  have hDmeas : Measurable Dt := by
    dsimp [Dt]
    exact ((s111t_coordCLM p.d (wholeSpaceIndex p.d : ℝ) α).continuous.measurable.comp
      (hZmeas t)).sub
        ((s111t_coordCLM p.d (wholeSpaceIndex p.d : ℝ) α).continuous.measurable.comp
          (hZmeas s))
  have hDcent : HRS.IsCenteredGaussian (P.map Dt) := by
    rw [Measure.map_congr hDae]
    exact hDserCentered
  have hSeriesLinear : W (J (Ft - Fs)) =ᵐ[P]
      fun ω => W (J Ft) ω - W (J Fs) ω := by
    have hmap : J (Ft - Fs) = J Ft + (-1 : ℝ) • J Fs := by
      rw [map_sub]
      rw [sub_eq_add_neg, neg_one_smul]
    rw [hmap]
    simpa [sub_eq_add_neg] using
      fp81s21_series_linear e ξ W hstd hW2 hWlim (J Ft) (J Fs) (-1)
  have hTargetAE : Dt =ᵐ[P] fun ω => W (J (Ft - Fs)) ω := by
    filter_upwards [hcoordDiff, hSeriesLinear] with ω hω hlin
    calc
      Dt ω = W (J Ft) ω - W (J Fs) ω := hω
      _ = W (J (Ft - Fs)) ω := hlin.symm
  have hSecond : (∫ ω, Dt ω ^ 2 ∂P) = ‖Ft - Fs‖ ^ 2 := by
    calc
      ∫ ω, Dt ω ^ 2 ∂P =
          ∫ ω, (W (J Ft) ω - W (J Fs) ω) ^ 2 ∂P := by
        apply integral_congr_ae
        exact hcoordDiff.mono fun ω hω =>
          congrArg (fun x : ℝ => x ^ 2) hω
      _ = ‖J Ft - J Fs‖ ^ 2 :=
        fp81s21_series_distance e ξ W hParseval hstd hW2 hWlim (J Ft) (J Fs)
      _ = ‖Ft - Fs‖ ^ 2 := by
        rw [← map_sub, J.norm_map]
  have hDmean : ∫ x : ℝ, x ∂P.map Dt = 0 := by
    simpa using hDcent.2 (ContinuousLinearMap.id ℝ ℝ)
  have hVar : ProbabilityTheory.variance (id : ℝ → ℝ) (P.map Dt) =
      ‖Ft - Fs‖ ^ 2 := by
    calc
      ProbabilityTheory.variance (id : ℝ → ℝ) (P.map Dt) =
          ∫ x : ℝ, x ^ 2 ∂P.map Dt := by
        simpa [id] using (ProbabilityTheory.variance_of_integral_eq_zero
          (μ := P.map Dt) (X := id) measurable_id'.aemeasurable hDmean)
      _ = ∫ ω, Dt ω ^ 2 ∂P :=
        integral_map hDmeas.aemeasurable
          (continuous_pow 2).aestronglyMeasurable
      _ = ‖Ft - Fs‖ ^ 2 := hSecond
  letI : IsGaussian (P.map Dt) := hDcent.1
  have hDlaw : P.map Dt = gaussianReal 0
      (Real.toNNReal (‖Ft - Fs‖ ^ 2)) := by
    have h := IsGaussian.map_eq_gaussianReal
      (μ := P.map Dt) (ContinuousLinearMap.id ℝ ℝ)
    have hmean' : ∫ x : ℝ, (ContinuousLinearMap.id ℝ ℝ) x ∂P.map Dt = 0 := by
      simpa using hDmean
    have hvar' : ProbabilityTheory.variance (ContinuousLinearMap.id ℝ ℝ)
        (P.map Dt) = ‖Ft - Fs‖ ^ 2 := by simpa using hVar
    rw [hmean', hvar'] at h
    simpa using h
  have hDfourIntegrable : Integrable (fun ω => Dt ω ^ 4) P := by
    have hmem : MemLp (id : ℝ → ℝ) 4 (P.map Dt) :=
      IsGaussian.memLp_id (P.map Dt) 4 (by norm_num)
    have hfour : Integrable (fun x : ℝ => x ^ 4) (P.map Dt) := by
      have hnorm := hmem.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
      have heq : (fun x : ℝ => ‖id x‖ ^ 4) = fun x => x ^ 4 := by
        funext x
        simp only [id, Real.norm_eq_abs]
        calc
          |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
          _ = (x ^ 2) ^ 2 := by rw [sq_abs]
          _ = x ^ 4 := by ring
      rw [heq] at hnorm
      exact hnorm
    exact (integrable_map_measure
      (continuous_pow 4).aestronglyMeasurable hDmeas.aemeasurable).1 hfour
  have hRealFourth : (∫ ω, Dt ω ^ 4 ∂P) =
      3 * (‖Ft - Fs‖ ^ 2) ^ 2 := by
    calc
      ∫ ω, Dt ω ^ 4 ∂P =
          ∫ x : ℝ, x ^ 4 ∂P.map Dt :=
        (integral_map hDmeas.aemeasurable
          (continuous_pow 4).aestronglyMeasurable).symm
      _ = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0
          (Real.toNNReal (‖Ft - Fs‖ ^ 2)) := by rw [hDlaw]
      _ = (Real.toNNReal (‖Ft - Fs‖ ^ 2) : ℝ) ^ 2 * HRS.Yurinskii.c4 :=
        HRS.Yurinskii.integral_pow4_gaussianReal _
      _ = 3 * (‖Ft - Fs‖ ^ 2) ^ 2 := by
        rw [show HRS.Yurinskii.c4 = 3 from HRS.gauss_m4,
          Real.coe_toNNReal (‖Ft - Fs‖ ^ 2) (sq_nonneg _)]
        ring
  have hEnorm : ∫⁻ ω, ‖Dt ω‖ₑ ^ (4 : ℝ) ∂P =
      ENNReal.ofReal (3 * (‖Ft - Fs‖ ^ 2) ^ 2) := by
    calc
      ∫⁻ ω, ‖Dt ω‖ₑ ^ (4 : ℝ) ∂P =
          ∫⁻ ω, ENNReal.ofReal (Dt ω ^ 4) ∂P := by
        apply lintegral_congr
        exact fun ω => fp81s21_enorm_fourth_real (Dt ω)
      _ = ENNReal.ofReal (∫ ω, Dt ω ^ 4 ∂P) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hDfourIntegrable
          (ae_of_all _ fun ω => by positivity)
      _ = _ := by rw [hRealFourth]
  refine ⟨hTargetAE, hDcent, hDlaw, hSecond, ?_⟩
  rw [hEnorm]
  apply ENNReal.ofReal_le_ofReal
  have hnorm0 : 0 ≤ ‖Ft - Fs‖ ^ 2 := sq_nonneg _
  nlinarith [hInc]

#print axioms fp81s21_raw_scalar_increment_fourth

end HRS.Fp81.S21

end
