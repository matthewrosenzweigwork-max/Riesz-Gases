import HRS.MS.WsInitKAux1
import HRS.MS.WsInitGAux12

/-!
# S21 packet K, part 2: the structural output of packet G with the enumeration exposed, and the product decay of the cosine tests

`s21k_decay`: `cbNorm_J(f_{n,alpha}) <= A (1+n)^{-5/4} lambda_alpha^{-gamma0}` with `gamma0 = (m - I)/2 > 5d/4` (explicit weight of `s21k_orbit_stat`).
`s21k_struct`: `s21g_struct` (WsInitGAux12) with the additional conjunct that the family `phi` is `j |-> f_{sigma j}` for an enumeration `sigma`
(the proof of `s21g_struct` repeated with `sigma` recorded in the statement).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS HRS.Whole HRS.MS.GenPath HRS.MS.Ul HRS.MS.S52B HRS.MS.S53
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s21k_decay (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {T : ℝ} (hT : 0 < T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ A γ₀ : ℝ, 5 * (d : ℝ) / 4 < γ₀ ∧ ∀ (n : ℕ) (α : MultiIndex d),
      cbNorm (s21gJ d) (r2CosOrbitTest ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T n α) ≤ A * ((1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * oscEigenvalue d α ^ (-γ₀)) := by
  obtain ⟨K, G0, G1, G2, G3, Orb⟩ := s21k_orbit_stat hd hs0 hsd ha hβ hT.le hρ
  obtain ⟨-, -, -, B1, hB1, hdec⟩ := s21g_orbit_cos_full hT Orb
  have hb := s21g_index_bound hd s hs0 hsd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨B1, (((wholeSpaceIndex d : ℕ) : ℝ) - ((s52bIdx d s (s21gK0 d + 4) : ℕ) : ℝ)) / 2, by linarith,
    fun n α => ?_⟩
  refine (hdec n α).trans (le_of_eq ?_)
  rw [show -((((wholeSpaceIndex d : ℕ) : ℝ) - ((s52bIdx d s (s21gK0 d + 4) : ℕ) : ℝ)) / 2) =
    (((s52bIdx d s (s21gK0 d + 4) : ℕ) : ℝ) - ((wholeSpaceIndex d : ℕ) : ℝ)) / 2 by ring]
  ring

theorem s21k_struct (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
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
              (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))))) ∧
      ∃ σ : ℕ ≃ ℕ × MultiIndex d, ∀ j, φ j = r2CosOrbitTest ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T (σ j).1 (σ j).2 := by
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
  refine ⟨φ, γ, s21gPhi σ hT m, Cst, hφ, inferInstance, s21gPhi_norm_le σ hT m, hγ, ?_, ?_, ?_, ⟨σ, fun j => rfl⟩⟩
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
