import HRS.MS.WsInitGAux10

/-!
# S21 packet G, part 11: the centred initial path of the stationary Gibbs law is `Φ(featureVec)`

`s21g_path_eq`: for every configuration `x` (`N ≥ 2`), `A(k_0)` with `k_0 = s56k0 C m T √N (HRS.Whole.empirical x) (HRS.Whole.meanEmpirical P)` equals
`Φ (featureVec φ (HRS.Whole.firstMarginal P) x)`, where `φ_j = f_{σ j}` are the cosine orbit tests and `Φ = s21gPhi σ`.
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

theorem s21g_path_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T : ℝ} (hT : 0 < T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ)
    (σ : ℕ ≃ ℕ × MultiIndex d) {N : ℕ} (hN : 2 ≤ N) (x : EucConfig d N) :
    s56EvalPath hT.le (s56k0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T
        (Real.sqrt N) (HRS.Whole.empirical x)
        (HRS.Whole.meanEmpirical (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β))) =
      s21gPhi σ hT ((wholeSpaceIndex d : ℕ) : ℝ)
        (featureVec (fun j => r2CosOrbitTest ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
          ((wholeSpaceIndex d : ℕ) : ℝ) T (σ j).1 (σ j).2)
          (HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)) x) := by
  have hN1 : 1 ≤ N := by omega
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  set m : ℝ := ((wholeSpaceIndex d : ℕ) : ℝ) with hm
  set P := HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β with hP
  obtain ⟨hmem, hsum, hcont⟩ := s21g_stat_cos hd hs0 hsd ha hβ hT hρ
  have hφ : IsSummableFeatureFamily (s21gJ d) (fun j => r2CosOrbitTest C m T (σ j).1 (σ j).2) :=
    ⟨fun j => hmem _ _, (Equiv.summable_iff σ (f := fun q : ℕ × MultiIndex d =>
      cbNorm (s21gJ d) (r2CosOrbitTest C m T q.1 q.2))).2 hsum⟩
  -- the static facts for `P`
  obtain ⟨Cs, -, hS⟩ := S45.s45_static_all hd hs0 hsd ha hβ
  have hSN := hS N hN
  haveI hPp : IsProbabilityMeasure P := hSN.prob
  have hmean : HRS.Whole.meanEmpirical P = HRS.Whole.firstMarginal P := HRS.Whole.meanEmpirical_eq_firstMarginal P hSN.exch hN1
  haveI hνp : IsProbabilityMeasure (HRS.Whole.meanEmpirical P) := HRS.Whole.meanEmpirical_isProbabilityMeasure P hN1
  obtain ⟨M₂, hM₂0, -, hM₂mom⟩ := s21_second_moment_stationary hd hs0 hsd ha hβ
  have hνint : Integrable (fun z : Euc d => ‖z‖) (HRS.Whole.meanEmpirical P) := by
    have h := s21g_meanEmp_norm_integrable (d := d) (N := N) (by omega) P (id : EucConfig d N → EucConfig d N)
      measurable_id (lt_of_le_of_lt (hM₂mom N hN P id measurable_id (by simp [HRS.law, hP])) ENNReal.ofReal_lt_top)
    simpa using h
  -- the setup
  obtain ⟨θ, Λ, K, hθ, hvalid, C₀thr, hthr0, hSetup⟩ := s21_setup_family hd hs0 hsd ha hβ hT hρ
  obtain ⟨S, hρ', hinv', hκ', hCadj⟩ := hSetup C₀thr le_rfl
  have hbv : (s21Bounds d s a β T θ Λ K C₀thr).Valid :=
    s56_valid_of_eq hvalid (s21Bounds_eq s a β T θ Λ K C₀thr)
  have hcoeff : S.coeff N = C := by
    rw [s21_coeff_setup S hρ' hinv' N, ← s21_dyn_eq]
  have hCadjN := hCadj N
  have hNint : Integrable (fun z : Euc d => ‖z‖) (HRS.Whole.empirical x) :=
    HRS.Whole.Q09A.integrable_empirical hN1 x _
  haveI : IsProbabilityMeasure (HRS.Whole.empirical x) := HRS.Whole.empirical_isProbabilityMeasure (by omega) x
  refine ContinuousMap.ext fun t => ?_
  refine s11p_ext_coord fun α => ?_
  change OscDual.coord (OscPath.at' (s56EvalPath hT.le (s56k0 C m T (Real.sqrt N) (HRS.Whole.empirical x)
    (HRS.Whole.meanEmpirical P))) t) α = OscDual.coord (OscPath.at' (s21gPhi σ hT m
      (featureVec (fun j => r2CosOrbitTest C m T (σ j).1 (σ j).2) (HRS.Whole.firstMarginal P) x)) t) α
  have ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) (s21Bounds d s a β T θ Λ K C₀thr).T := t.2
  have e1 := s21g_k0_eval (s21Bounds d s a β T θ Λ K C₀thr) hbv S N hN1 hCadjN (Real.sqrt N)
    (HRS.Whole.empirical x) (HRS.Whole.meanEmpirical P) hNint hνint ht α
  rw [hcoeff] at e1
  have hL : OscPath.at' (s56EvalPath hT.le (s56k0 C m T (Real.sqrt N) (HRS.Whole.empirical x)
    (HRS.Whole.meanEmpirical P))) t = (s56k0 C m T (Real.sqrt N) (HRS.Whole.empirical x)
    (HRS.Whole.meanEmpirical P)).evalA (t : ℝ) := rfl
  rw [hL, s21gPhi_coord]
  have e2 : (s21gTheta σ (featureVec (fun j => r2CosOrbitTest C m T (σ j).1 (σ j).2) (HRS.Whole.firstMarginal P) x)) =
      s21gTheta σ (featureVec (fun j => r2CosOrbitTest C m T (σ j).1 (σ j).2) (HRS.Whole.meanEmpirical P) x) := by
    rw [hmean]
  rw [e2]
  have e3 : ∀ n : ℕ, (s21gTheta σ (featureVec (fun j => r2CosOrbitTest C m T (σ j).1 (σ j).2)
      (HRS.Whole.meanEmpirical P) x)).c (n, α) = Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (r2CosOrbitTest C m T n α) -
        HRS.Whole.pair (HRS.Whole.meanEmpirical P) (r2CosOrbitTest C m T n α)) := fun n =>
    s21g_Theta_feature σ hφ hN1 (HRS.Whole.meanEmpirical P) x n α
  simp_rw [e3]
  rw [← s21g_coord_series hT hmem hsum hcont hN1 (HRS.Whole.meanEmpirical P) x t.2 α]
  exact e1

end HRS.MS.S21
