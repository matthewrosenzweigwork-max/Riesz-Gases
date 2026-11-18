import HRS.MS.R2ObsAux8
import HRS.Whole.Round2

/-!
# S9.10 path row: proof of `HRS.Whole.r2_static_observation_path`

Worker S910.  `r2_static_observation_path_proof : type_of% @HRS.Whole.r2_static_observation_path` (tie in `R2ObsTie.lean`).

Route: `hcont` of the iid row is derived (`s910_hcont`, uniqueness of the classical adjoint solution for the stationary thermal
coefficient); the cosine orbit tests `f_{n,α}` (`s11p_orbitData`) give, with the scaling `c_J`, the summable feature family
`ψ_n = c_J f_{σ n}` on `H = K = ℓ²(ℕ × ℕ^d)` with the basis `s11p_basis σ`; the FAMILY row `r2_static_observation_family_proof` gives the
Gaussian, the tensor and the uniform expansion in `K`; everything is pushed forward by the cosine synthesis map `J` of norm `≤ 1`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

noncomputable section

namespace HRS.MS.R2Obs

open S99 S45 HRS.Whole
open HRS (Euc cbNorm MemCb)

set_option maxHeartbeats 4000000 in
theorem r2_static_observation_path_proof : type_of% @HRS.Whole.r2_static_observation_path := by
  intro d s hd hs0 hs a β γ ha hβ hγ T hT k m hk hm ρ hρ hex hmem hsum
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hρeq := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  subst hρeq
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => thermalDensity d s a β) with hC
  have hJk : J1 d ≤ k := by unfold J1; exact hk
  set f : ℕ × MultiIndex d → Euc d → ℝ := fun q => r2CosOrbitTest C (m : ℝ) T q.1 q.2 with hf
  have hf1 : ∀ q, MemCb (J1 d) (f q) := fun q => s910_memCb_mono hJk (hmem q.1 q.2)
  have hsum1 : Summable fun q => cbNorm (J1 d) (f q) :=
    Summable.of_nonneg_of_le (fun q => HRS.MS.Tc5.tc5_cb_nonneg _ _) (fun q => s910_cbNorm_mono hJk _) hsum
  have hcont : ∀ (α : MultiIndex d) (x : Euc d),
      ContinuousOn (fun t => propagatorW C 0 t (oscTestFun (m : ℝ) α) x) (Set.Icc (0 : ℝ) T) := fun α x =>
    s910_hcont hd hs0 hsd ha hβ T hρ (hex α T ⟨hT.le, le_rfl⟩) x
  have hU : ∀ (α : MultiIndex d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → ∀ x : Euc d,
      HasSum (fun n => s11p_kap n * r2CosBasis T n t * f (n, α) x) (propagatorW C 0 t (oscTestFun (m : ℝ) α) x) :=
    fun α t ht x => s11p_orbit_hasSum C (m : ℝ) hT hmem hsum hcont α x t ht
  obtain ⟨σ⟩ := s11p_exists_equiv (d := d)
  set c := s11p_cJ T with hcdef
  set ψ : ℕ → Euc d → ℝ := fun n x => c * f (σ n) x with hψ
  have hψmem : ∀ n, MemCb (4 * d + 40) (ψ n) := fun n => (HRS.MS.Tc5.tc5_cb_smul c (hf1 (σ n))).1
  have hψsum : Summable fun n => cbNorm (4 * d + 40) (ψ n) := by
    refine Summable.of_nonneg_of_le (fun n => HRS.MS.Tc5.tc5_cb_nonneg _ _)
      (fun n => (HRS.MS.Tc5.tc5_cb_smul c (hf1 (σ n))).2) ?_
    exact ((Equiv.summable_iff σ).2 hsum1).mul_left |c|
  have hφ : IsSummableFeatureFamily (J1 d) ψ := ⟨hψmem, hψsum⟩
  obtain ⟨E⟩ := s910_env hd hs0 hs ha hβ hγ hφ
  haveI hμprob : IsProbabilityMeasure (HRS.Whole.withDensityReal (thermalDensity d s a β)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.hT.prob
  obtain ⟨G, hGp, hGg, hGcov, ⟨Kb, hKb⟩, -, hmeas, hedge⟩ :=
    @r2_static_observation_family_proof.{0} d s (s11p_K d) _ _ _ _ _ _ hd hs0 hs a β γ ha hβ hγ
      (s11p_basis σ) ψ hψmem hψsum (thermalDensity d s a β) hρ
  haveI := hGp
  set J := s11p_J hT (m : ℝ) (d := d) with hJ
  have hEllc : Continuous (r2EllH (s11p_basis σ) ψ (rieszKernel d s) (thermalMeasure d s a β) γ) :=
    s910_ell_cont hd hs0 hs ha hβ hγ E _
  -- the path `ℓ_x^0`
  have hellfun : ∀ (x : Euc d) (t : Set.Icc (0 : ℝ) T),
      r2EllFun C (rieszKernel d s) (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ (m : ℝ) x t =
        OscPath.at' (J (r2EllH (s11p_basis σ) ψ (rieszKernel d s)
          (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x)) t := fun x t => by
    unfold r2EllFun
    have : (fun α => responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ
        (propagatorW C 0 (t : ℝ) (oscTestFun (m : ℝ) α)) x) = fun α => OscDual.coord (OscPath.at' (J
          (r2EllH (s11p_basis σ) ψ (rieszKernel d s) (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x)) t) α :=
      funext fun α => (s910_ell_path hd hs0 hs ha hβ hγ hT hf1 hsum1
        (U := fun α t x => propagatorW C 0 t (oscTestFun (m : ℝ) α) x) hU σ (m : ℝ) E x t α).symm
    rw [this, s11p_ellVec_coord]
  have hpathE : ∀ x, r2EllPath C (rieszKernel d s) (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ (m : ℝ) T x =
      J (r2EllH (s11p_basis σ) ψ (rieszKernel d s) (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x) :=
    fun x => s11p_windowPathOf_eq (m : ℝ) T _ _ (fun t => hellfun x t)
  -- the initial path
  have hinitfun : ∀ N : ℕ, 2 ≤ N → ∀ (X : EucConfig d N) (t : Set.Icc (0 : ℝ) T),
      r2InitFun C (m : ℝ) (HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal (thermalDensity d s a β))) X t =
        OscPath.at' (J (r2FieldH (s11p_basis σ) ψ (HRS.Whole.modulatedGibbs (rieszKernel d s) N γ
          (HRS.Whole.withDensityReal (thermalDensity d s a β))) X)) t := fun N hN2 X t => by
    have hN1 : 1 ≤ N := by omega
    haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (E.hS N hN2).prob
    have hPe : HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal (thermalDensity d s a β)) =
        S46.s46_P d s a β γ N := (s99_P_eq hd hs0 hs ha hβ hγ N).symm
    rw [hPe]
    unfold r2InitFun
    have : (fun α => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (propagatorW C 0 (t : ℝ) (oscTestFun (m : ℝ) α)) -
        HRS.Whole.pair (HRS.Whole.meanEmpirical (S46.s46_P d s a β γ N)) (propagatorW C 0 (t : ℝ) (oscTestFun (m : ℝ) α)))) =
        fun α => OscDual.coord (OscPath.at' (J (r2FieldH (s11p_basis σ) ψ (S46.s46_P d s a β γ N) X)) t) α :=
      funext fun α => (s910_field_path hd hs0 hs ha hβ hγ hT hf1 hsum1
        (U := fun α t x => propagatorW C 0 t (oscTestFun (m : ℝ) α) x) hU σ (m : ℝ) hN1 (S46.s46_P d s a β γ N)
        (E.hS N hN2).exch hφ X t α).symm
    rw [this, s11p_ellVec_coord]
  have hpathI : ∀ N : ℕ, 2 ≤ N → ∀ X : EucConfig d N,
      r2InitPath C (m : ℝ) T (HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal (thermalDensity d s a β))) X =
        J (r2FieldH (s11p_basis σ) ψ (HRS.Whole.modulatedGibbs (rieszKernel d s) N γ
          (HRS.Whole.withDensityReal (thermalDensity d s a β))) X) := fun N hN2 X =>
    s11p_windowPathOf_eq (m : ℝ) T _ _ (fun t => hinitfun N hN2 X t)
  have hbdJ : ∀ x, ‖J (r2EllH (s11p_basis σ) ψ (rieszKernel d s) (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x)‖ ≤ Kb :=
    fun x => (J.le_opNorm _).trans (by
      calc ‖J‖ * ‖r2EllH (s11p_basis σ) ψ (rieszKernel d s) (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x‖
          ≤ 1 * Kb := mul_le_mul (s11p_J_norm_le hT (m : ℝ)) (hKb x) (norm_nonneg _) zero_le_one
        _ = Kb := one_mul _)
  unfold R2InitPathEdgeworth
  refine ⟨G.map J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · have := hGg.1
    refine ⟨inferInstance, fun L => ?_⟩
    rw [integral_map J.continuous.aemeasurable L.continuous.aestronglyMeasurable]
    simpa using hGg.2 (L.comp J)
  · intro t t' α α'
    have key := s910_gauss_int hGg (s11p_vec hT t α) (s11p_vec hT t' α')
    have hF : Continuous fun w : OscPath d (m : ℝ) T =>
        OscDual.coord (OscPath.at' w t) α * OscDual.coord (OscPath.at' w t') α' :=
      (s11p_coord_at_continuous (m : ℝ) T t α).mul (s11p_coord_at_continuous (m : ℝ) T t' α')
    have hFJ : (fun z => OscDual.coord (OscPath.at' (J z) t) α * OscDual.coord (OscPath.at' (J z) t') α') =
        fun z => inner ℝ (s11p_vec hT t α) z * inner ℝ (s11p_vec hT t' α') z :=
      funext fun z => by rw [s11p_inner_vec hT (m : ℝ) z t α, s11p_inner_vec hT (m : ℝ) z t' α']
    refine ⟨?_, ?_⟩
    · rw [integrable_map_measure hF.aestronglyMeasurable J.continuous.aemeasurable]
      exact (show Integrable (fun z => OscDual.coord (OscPath.at' (J z) t) α *
          OscDual.coord (OscPath.at' (J z) t') α') G by rw [hFJ]; exact key.1)
    · rw [integral_map J.continuous.aemeasurable hF.aestronglyMeasurable]
      show ∫ z, OscDual.coord (OscPath.at' (J z) t) α * OscDual.coord (OscPath.at' (J z) t') α' ∂G = _
      rw [hFJ]
      exact s910_path_cov hd hs0 hsd ha hβ hγ hT hf1 hsum1
        (U := fun α t x => propagatorW C 0 t (oscTestFun (m : ℝ) α) x) hU σ hGg
        (fun n m => (hGcov n m).2) t t' t.2 t'.2 α α'
  · intro x
    have : (fun t : Set.Icc (0 : ℝ) T => r2EllFun C (rieszKernel d s)
        (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ (m : ℝ) x t) = fun t => OscPath.at' (J
          (r2EllH (s11p_basis σ) ψ (rieszKernel d s) (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x)) t :=
      funext (hellfun x)
    rw [this]
    exact (show C(Set.Icc (0 : ℝ) T, OscDual d (m : ℝ)) from J _).continuous
  · intro N hN X
    have : (fun t : Set.Icc (0 : ℝ) T => r2InitFun C (m : ℝ) (HRS.Whole.modulatedGibbs (rieszKernel d s) N γ
        (HRS.Whole.withDensityReal (thermalDensity d s a β))) X t) = fun t => OscPath.at' (J
          (r2FieldH (s11p_basis σ) ψ (HRS.Whole.modulatedGibbs (rieszKernel d s) N γ
            (HRS.Whole.withDensityReal (thermalDensity d s a β))) X)) t := funext (hinitfun N hN X)
    rw [this]
    exact (show C(Set.Icc (0 : ℝ) T, OscDual d (m : ℝ)) from J _).continuous
  · exact ⟨Kb, fun x => by rw [hpathE]; exact hbdJ x⟩
  · simp only [hpathE]
    exact s910_tensor (HRS.Whole.withDensityReal (thermalDensity d s a β)) _
      (J.continuous.comp hEllc) (Cb := Kb) hbdJ
  · intro N hN
    have : r2InitPath C (m : ℝ) T (HRS.Whole.modulatedGibbs (rieszKernel d s) N γ
        (HRS.Whole.withDensityReal (thermalDensity d s a β))) =
        fun X => J (r2FieldH (s11p_basis σ) ψ (HRS.Whole.modulatedGibbs (rieszKernel d s) N γ
          (HRS.Whole.withDensityReal (thermalDensity d s a β))) X) := funext (hpathI N hN)
    rw [this]
    exact J.continuous.measurable.comp (hmeas N hN)
  · intro ε hε
    obtain ⟨N₀, hN₀⟩ := hedge ε hε
    refine ⟨N₀, fun N hN hN2 Φ hΦ => ?_⟩
    have hΦ' : (Φ ∘ J) ∈ HRS.CbUnitBall (s11p_K d) 5 := HRS.cbUnitBall_comp_clm J (s11p_J_norm_le hT (m : ℝ)) hΦ
    have h := hN₀ N hN hN2 (Φ ∘ J) hΦ'
    have hΦc : Continuous Φ := hΦ.1.continuous
    have e1 : ∫ X, Φ (r2InitPath C (m : ℝ) T (HRS.Whole.modulatedGibbs (rieszKernel d s) N γ
        (HRS.Whole.withDensityReal (thermalDensity d s a β))) X)
          ∂(HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal (thermalDensity d s a β))) =
        ∫ X, (Φ ∘ J) (r2FieldH (s11p_basis σ) ψ (HRS.Whole.modulatedGibbs (rieszKernel d s) N γ
          (HRS.Whole.withDensityReal (thermalDensity d s a β))) X)
          ∂(HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal (thermalDensity d s a β))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      simp only [Function.comp_apply]
      rw [hpathI N hN2 X]
    have e2 : ∫ F, Φ F ∂(G.map J) = ∫ F, (Φ ∘ J) F ∂G :=
      integral_map J.continuous.aemeasurable hΦc.aestronglyMeasurable
    set ℓ : Euc d → OscPath d (m : ℝ) T := fun x => J (r2EllH (s11p_basis σ) ψ (rieszKernel d s)
      (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x) with hℓ
    have hcont3 : Continuous fun q : OscPath d (m : ℝ) T × Euc d =>
        iteratedFDeriv ℝ 3 Φ q.1 ![ℓ q.2, ℓ q.2, ℓ q.2] := by
      have h1 : Continuous fun q : OscPath d (m : ℝ) T × Euc d => iteratedFDeriv ℝ 3 Φ q.1 :=
        (hΦ.1.continuous_iteratedFDeriv (by norm_num)).comp continuous_fst
      have hv : Continuous fun q : OscPath d (m : ℝ) T × Euc d =>
          (![ℓ q.2, ℓ q.2, ℓ q.2] : Fin 3 → OscPath d (m : ℝ) T) := by
        refine continuous_pi fun i => ?_
        fin_cases i <;> exact (J.continuous.comp hEllc).comp continuous_snd
      exact h1.eval hv
    have hsm : StronglyMeasurable fun F : OscPath d (m : ℝ) T =>
        ∫ x, iteratedFDeriv ℝ 3 Φ F ![ℓ x, ℓ x, ℓ x] ∂(HRS.Whole.withDensityReal (thermalDensity d s a β)) :=
      StronglyMeasurable.integral_prod_right (f := fun F x => iteratedFDeriv ℝ 3 Φ F ![ℓ x, ℓ x, ℓ x])
        hcont3.stronglyMeasurable
    have e3 : ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F ![ℓ x, ℓ x, ℓ x]
          ∂(HRS.Whole.withDensityReal (thermalDensity d s a β)) ∂(G.map J) =
        ∫ F, ∫ x, iteratedFDeriv ℝ 3 (Φ ∘ J) F ![r2EllH (s11p_basis σ) ψ (rieszKernel d s)
          (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x, r2EllH (s11p_basis σ) ψ (rieszKernel d s)
          (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x, r2EllH (s11p_basis σ) ψ (rieszKernel d s)
          (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x]
          ∂(HRS.Whole.withDensityReal (thermalDensity d s a β)) ∂G := by
      rw [integral_map J.continuous.aemeasurable hsm.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [J.iteratedFDeriv_comp_right hΦ.1 z (by norm_num : ((3 : ℕ) : WithTop ℕ∞) ≤ 5),
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr 1
      funext i
      fin_cases i <;> rfl
    simp only [hpathE]
    rw [e1, e2, e3]
    exact h

end HRS.MS.R2Obs

end
