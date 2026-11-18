import HRS.MS.WsInitGAux11

/-!
# S21 packet G, part 12: the structural output `s21g_struct` and the smooth half `s21g_init_smooth`

`s21g_struct` (interface for packet H, the `W_1` half): for the stationary quadratic data (`d ≥ 2`, `0 ≤ s < d`, `a, β, T > 0`, `ρ` the thermal equilibrium) there are
* a summable `C_b^J` family `φ` (`J = ⌊d/2⌋+3`, the cosine orbit tests of the enumeration `σ`), a centred Gaussian `γ` on `ℓ²` with the susceptibility
  covariances of `φ`, the static conclusion `StaticFieldConclusion` for every `N ≥ 2`, and a bounded linear map `Φ : ℓ² → C([0,T];B_m)`,
  `‖Φ‖ ≤ c_J`, with `A(k_0)(x) = Φ(featureVec φ (HRS.Whole.firstMarginal P_{N,β}) x)` for every configuration `x`;
* the finite-dimensional laws of `γ_0 = Φ_* γ`: `multivariateGaussian 0 (HRS.Whole.susceptibilityCov(U^{0,t_i}φ_{α_i}, U^{0,t_j}φ_{α_j}))`, positive semidefinite.

`s21g_init_smooth`: the smooth half of `S21InitAt` (WsStatAux34) with `s21IP` unfolded.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s21g_struct (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T : ℝ} (hT : 0 < T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ (φ : ℕ → Euc d → ℝ) (γ : Measure SeqL2)
      (Φ : SeqL2 →L[ℝ] OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T) (Cst : ℝ),
      IsSummableFeatureFamily (s21gJ d) φ ∧ IsProbabilityMeasure γ ∧ ‖Φ‖ ≤ s11p_cJ T ∧
      IsCenteredGaussianSeq γ (fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β
        (φ i) (φ j)) ∧
      (∀ N : ℕ, 2 ≤ N → StaticFieldConclusion d s N (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)
        (HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)) (s21gJ d) φ γ Cst) ∧
      (∀ N : ℕ, 2 ≤ N → ∀ x : EucConfig d N,
        s56EvalPath hT.le (s56k0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
          ((wholeSpaceIndex d : ℕ) : ℝ) T (Real.sqrt N) (HRS.Whole.empirical x)
          (HRS.Whole.meanEmpirical (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β))) =
        Φ (featureVec φ (HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)) x)) ∧
      (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
        (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts i)
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts j)
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j)))).PosSemidef ∧
        (γ.map Φ).map (fun w : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => (WithLp.toLp 2 fun i =>
            OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
          multivariateGaussian 0 (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
            (HRS.Whole.withDensityReal ρ) β
            (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts i)
              (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
            (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts j)
              (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))))) := by
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  set m : ℝ := ((wholeSpaceIndex d : ℕ) : ℝ) with hm
  obtain ⟨hmem, hsum, hcont⟩ := s21g_stat_cos hd hs0 hsd ha hβ hT hρ
  obtain ⟨σ⟩ := s11p_exists_equiv (d := d)
  set φ : ℕ → Euc d → ℝ := fun j => r2CosOrbitTest C m T (σ j).1 (σ j).2 with hφdef
  have hφ : IsSummableFeatureFamily (s21gJ d) φ :=
    ⟨fun j => hmem _ _, (Equiv.summable_iff σ (f := fun q : ℕ × MultiIndex d =>
      cbNorm (s21gJ d) (r2CosOrbitTest C m T q.1 q.2))).2 hsum⟩
  -- thermal data and the Gaussian
  obtain ⟨Cth, c, BU, hTh⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  obtain ⟨L, hL⟩ := S45.s45_thermal_logmoment2 hTh
  have hM : ∀ x, thermalDensity d s a β x ≤ Cth := fun x => (le_abs_self _).trans
    ((hTh.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hTh.hc])
      nlinarith [hTh.C0]))
  obtain ⟨-, γ, hγ⟩ := S45.exists_gaussian_feature_proof hd hs0 hsd (s21gJ d) (s21gJ_gt d)
    (thermalDensity d s a β) hTh.prob Cth hM β hβ φ hφ L (fun _ => hL)
  haveI hGg : IsGaussian γ := hγ.1.1
  obtain ⟨Cst, hCst⟩ := S45.quadratic_static_field_proof hd hs0 hsd a β ha hβ (s21gJ d) (s21gJ_gt d)
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal (thermalDensity d s a β)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTh.prob
  have hνρ : HRS.Whole.withDensityReal ρ = HRS.Whole.withDensityReal (thermalDensity d s a β) := by rw [hρeq]
  refine ⟨φ, γ, s21gPhi σ hT m, Cst, hφ, inferInstance, s21gPhi_norm_le σ hT m, hγ, ?_, ?_, ?_⟩
  · intro N hN
    exact hCst φ hφ N hN γ hγ
  · intro N hN x
    exact (s21g_path_eq hd hs0 hsd ha hβ hT hρ σ hN x)
  · intro p ts hts αs
    obtain ⟨K, hK⟩ := S45.s45_kdata (by omega) hs0 hsd hTh.prob hM (fun _ => hL)
    set ν := HRS.Whole.withDensityReal (thermalDensity d s a β) with hν
    -- the coefficient vectors and the functions
    set w : Fin p → SeqL2 := fun i => s21gVec σ hT (ts i) (αs i) with hw
    set ψ : Fin p → Euc d → ℝ := fun i => propagatorW C 0 (ts i) (oscTestFun m (αs i)) with hψ
    have hDS := s11p_series C m hT hmem hsum hcont
    have hψm : ∀ i, MemLp (ψ i) 2 ν := fun i => by
      obtain ⟨Cb, hCb⟩ := s11p_U_bound hT hDS (αs i) (ts i) (hts i)
      exact MemLp.of_bound (s11p_U_continuous hT hDS (αs i) (ts i) (hts i)).aestronglyMeasurable Cb
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCb x)
    have hser : ∀ i x, HasSum (fun j => SeqL2.coord (w i) j * φ j x) (ψ i x) := fun i x =>
      s21g_series hT hmem hsum hcont σ (ts i) (hts i) (αs i) x
    have hcovij : ∀ i j, covarianceBilin γ (w i) (w j) =
        HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (ψ i) (ψ j) := by
      intro i j
      have hmean : ∫ z, id z ∂γ = 0 := HRS.HilbertCLTAux.gaussian_mean_zero hγ.1
      have h := s21g_cov hK hβ hφ (γ := γ) hγ (w i) (w j) (hψm i) (hψm j) (hser i) (hser j)
      rw [covarianceBilin_apply IsGaussian.memLp_two_id, hmean]
      simp only [id, sub_zero]
      rw [hνρ]
      exact h.2
    have hmean : ∫ z, id z ∂γ = 0 := HRS.HilbertCLTAux.gaussian_mean_zero hγ.1
    obtain ⟨hPSD, hlaw⟩ := s21g_fdd_gaussian γ hmean w
    have e : (Matrix.of fun i j => covarianceBilin γ (w i) (w j)) =
        Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (ψ i) (ψ j) := by
      ext i j; exact hcovij i j
    rw [e] at hPSD hlaw
    refine ⟨hPSD, ?_⟩
    have hFm : Measurable (fun w : OscPath d m T => (WithLp.toLp 2 fun i =>
        OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) := by
      have h1 : Continuous fun w : OscPath d m T => (WithLp.toLp 2 fun i =>
          OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p)) := by
        refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
        exact s11p_coord_at_continuous m T ⟨ts i, hts i⟩ (αs i)
      exact h1.measurable
    rw [Measure.map_map hFm (s21gPhi σ hT m).continuous.measurable]
    convert hlaw using 2
    funext z
    ext i
    simp only [Function.comp_apply]
    rw [s21gAw_apply, s21gPhi_coord_inner]

end HRS.MS.S21
