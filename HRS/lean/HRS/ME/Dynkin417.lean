import HRS.Sections.Sec4
import HRS.Stochastic.SelectedLawFKE
import HRS.Stochastic.LyonsZhengSpec
import HRS.Equilibrium.PairCorrection
import HRS.MD.Stat

/-!
# Packet M2s (row 4.17): Dynkin's formula for smooth compactly supported test functions

Proof of `dynkin_smooth` of `HRS/ME/Spec417.lean` (statement copied verbatim as `dynkin_smooth_proof`).
Helpers carry the prefix `dyn417_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-! ### Part A: the generator of the particle dynamics as the Itô drift of `configLift` -/

theorem dyn417_gradient_fun {N : ℕ} (F : Config d N → ℝ) (Y : Fin N → Euc d) (i : Fin N) :
    (fun u : Euc d => F (Function.update (fun j => Torus.mk (Y j)) i
        ((fun j => Torus.mk (Y j)) i + Torus.mk u)))
      = fun u => configLift (fun _ => F) 0 (Y + Pi.single i u) := by
  funext u
  unfold configLift
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp [Torus.mk_add]
  · simp [Function.update_of_ne h, Pi.single_apply, h]

theorem dyn417_fderiv2_affine {N : ℕ} (f : (Fin N → Euc d) → ℝ) (hf : ContDiff ℝ 2 f)
    (Y : Fin N → Euc d) (L : Euc d →L[ℝ] (Fin N → Euc d)) (v w : Euc d) :
    fderiv ℝ (fderiv ℝ (fun u : Euc d => f (Y + L u))) 0 v w
      = fderiv ℝ (fderiv ℝ f) Y (L v) (L w) := by
  have hh : ContDiff ℝ 2 (fun z : Fin N → Euc d => f (Y + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have hg : (fun u : Euc d => f (Y + L u)) = (fun z : Fin N → Euc d => f (Y + z)) ∘ L := rfl
  have h3 : iteratedFDeriv ℝ 2 (fun u : Euc d => f (Y + L u)) 0
      = (iteratedFDeriv ℝ 2 f Y).compContinuousLinearMap (fun _ => L) := by
    rw [hg, ContinuousLinearMap.iteratedFDeriv_comp_right L hh 0 (by norm_num), map_zero,
      iteratedFDeriv_comp_add_left (𝕜 := ℝ), add_zero]
  calc fderiv ℝ (fderiv ℝ (fun u : Euc d => f (Y + L u))) 0 v w
      = iteratedFDeriv ℝ 2 (fun u : Euc d => f (Y + L u)) 0 ![v, w] := by
        rw [iteratedFDeriv_two_apply (𝕜 := ℝ)]; rfl
    _ = iteratedFDeriv ℝ 2 f Y (fun i => L (![v, w] i)) := by
        rw [h3, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    _ = fderiv ℝ (fderiv ℝ f) Y (L v) (L w) := by
        rw [iteratedFDeriv_two_apply (𝕜 := ℝ)]; rfl

theorem dyn417_configLap_eq {N : ℕ} (F : Config d N → ℝ)
    (hF : ContDiff ℝ 2 (configLift (fun _ => F) 0)) (Y : Fin N → Euc d) (i : Fin N) :
    configLap F (fun j => Torus.mk (Y j)) i
      = ∑ j : Fin d, fderiv ℝ (fderiv ℝ (configLift (fun _ => F) 0)) Y
          (Pi.single i (EuclideanSpace.single j 1)) (Pi.single i (EuclideanSpace.single j 1)) := by
  unfold configLap
  rw [dyn417_gradient_fun F Y i, HRS.laplacian_eq_sum_fderiv]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact dyn417_fderiv2_affine (configLift (fun _ => F) 0) hF Y
    (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) _ _

theorem dyn417_inner_configGrad {N : ℕ} (F : Config d N → ℝ)
    (hF : Differentiable ℝ (configLift (fun _ => F) 0)) (Y : Fin N → Euc d) (i : Fin N) (w : Euc d) :
    inner ℝ w (configGrad F (fun j => Torus.mk (Y j)) i)
      = fderiv ℝ (configLift (fun _ => F) 0) Y (Pi.single i w) := by
  unfold configGrad
  rw [dyn417_gradient_fun F Y i, gradient, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have hA : HasFDerivAt (fun u : Euc d => Y + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) u)
      (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) 0 :=
    (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i).hasFDerivAt.const_add Y
  have hf : HasFDerivAt (configLift (fun _ => F) 0)
      (fderiv ℝ (configLift (fun _ => F) 0) (Y + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) 0))
      (Y + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) 0) :=
    (hF _).hasFDerivAt
  have hc := hf.comp (0 : Euc d) hA
  have hc' : HasFDerivAt (fun u : Euc d => configLift (fun _ => F) 0 (Y + Pi.single i u))
      ((fderiv ℝ (configLift (fun _ => F) 0) (Y + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) 0)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i)) 0 := hc
  rw [hc'.fderiv]
  simp

theorem dyn417_matVec_neg_one (v : Euc d) :
    Torus.matVec (-(1 : Matrix (Fin d) (Fin d) ℝ)) v = -v := by
  unfold Torus.matVec
  ext j
  simp [Matrix.toEuclideanLin, Matrix.mulVec]

theorem dyn417_pi_split {N : ℕ} (v : Fin N → Euc d) : v = ∑ i, Pi.single i (v i) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem dyn417_fkeIto_eq {s : ℝ} (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β) {N : ℕ}
    (D : DynData d) (hDs : D.s = s) (hDV : D.V = V) (hDM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hDi : D.invβ = β⁻¹) (F : Config d N → ℝ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0)) (T r : ℝ)
    (Y : Fin N → Euc d) :
    fkeIto D T (fun _ => F) r Y = particleGen d s V β F (fun j => Torus.mk (Y j)) := by
  have hF2 : ContDiff ℝ 2 (configLift (fun _ => F) 0) := hF.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hD1 : Differentiable ℝ (configLift (fun _ => F) 0) := hF.differentiable (by simp)
  have hinv : D.invβ = β⁻¹ := hDi
  have hMn : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ) := hDM
  have hDs' : D.s = s := hDs
  have hDV' : D.V = V := hDV
  have hcl : ∀ r' : ℝ, configLift (fun _ => F) r' = configLift (fun _ => F) 0 := fun _ => rfl
  unfold fkeIto
  have h0 : derivWithin (fun r' => configLift (fun _ => F) r' Y) (Set.Icc 0 T) r = 0 := by
    have : (fun r' => configLift (fun _ => F) r' Y) = Function.const ℝ (configLift (fun _ => F) 0 Y) :=
      rfl
    rw [this]
    exact congrFun (derivWithin_const (Set.Icc 0 T) (configLift (fun _ => F) 0 Y)) r
  rw [h0, zero_add, hcl r]
  have hsq : Real.sqrt (2 * D.invβ)
      * Real.sqrt (2 * D.invβ) = 2 * β⁻¹ := by
    rw [Real.mul_self_sqrt (by rw [hinv]; positivity), hinv]
  have hc2 : (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (configLift (fun _ => F) 0)) Y
        (liftedNoise D k) (liftedNoise D k)
      = β⁻¹ * ∑ i : Fin N, configLap F (fun j => Torus.mk (Y j)) i := by
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dyn417_configLap_eq F hF2 Y i]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [liftedNoise, ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
    linear_combination (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ (configLift (fun _ => F) 0)) Y
      (Pi.single i (EuclideanSpace.single j 1)) (Pi.single i (EuclideanSpace.single j 1))) * hsq
  have hdi : ∀ i : Fin N, particleDrift D (fun j => Torus.mk (Y j)) i
      = -(Torus.grad V (Torus.mk (Y i)) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
          periodicRieszGrad d s (Torus.mk (Y i) - Torus.mk (Y j))) := by
    intro i
    unfold particleDrift
    rw [hMn, hDV', hDs']
    simp only [dyn417_matVec_neg_one, Finset.sum_neg_distrib, smul_neg]
    abel
  have hkey : ∀ i : Fin N, fderiv ℝ (configLift (fun _ => F) 0) Y
      (Pi.single i (driftVec D (fun j => Torus.mk (Y j)) i))
      = -inner ℝ (Torus.grad V (Torus.mk (Y i)) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
          periodicRieszGrad d s (Torus.mk (Y i) - Torus.mk (Y j)))
          (configGrad F (fun j => Torus.mk (Y j)) i) := by
    intro i
    rw [← dyn417_inner_configGrad F hD1 Y i]
    show inner ℝ (particleDrift D (fun j => Torus.mk (Y j)) i)
      (configGrad F (fun j => Torus.mk (Y j)) i) = _
    rw [hdi i, inner_neg_left]
  have hsum : fderiv ℝ (configLift (fun _ => F) 0) Y (driftVec D
      (fun j => Torus.mk (Y j)))
      = ∑ i, fderiv ℝ (configLift (fun _ => F) 0) Y
          (Pi.single i (driftVec D (fun j => Torus.mk (Y j)) i)) := by
    conv_lhs => rw [dyn417_pi_split (driftVec D (fun j => Torus.mk (Y j)))]
    rw [map_sum]
  rw [hsum, hc2]
  simp only [hkey]
  unfold particleGen
  rw [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

/-! ### Part B: pathwise Itô formula for the constant-in-time test function -/

theorem dyn417_isC12 {N : ℕ} (F : Config d N → ℝ) (T : ℝ)
    (hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0)) :
    IsC12On T Set.univ (configLift (fun _ => F)) := by
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (configLift (fun _ => F) 0)) :=
    (contDiff_infty_iff_fderiv.1 hFc).2
  have hcd : Continuous (fderiv ℝ (configLift (fun _ => F) 0)) :=
    hFc.continuous_fderiv (by simp)
  have hcd2 : Continuous (fderiv ℝ (fderiv ℝ (configLift (fun _ => F) 0))) :=
    hD.continuous_fderiv (by simp)
  have hdz : ∀ (x : Fin N → Euc d) (t : ℝ),
      derivWithin (fun r => configLift (fun _ => F) r x) (Set.Icc 0 T) t = 0 := fun x t =>
    congrFun (derivWithin_const (Set.Icc 0 T) (configLift (fun _ => F) 0 x)) t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hFc.continuous.comp continuous_snd).continuousOn
  · intro t _ x _
    exact (hFc.differentiable (by simp) x).hasFDerivAt
  · intro t _ x _
    exact (hD.differentiable (by simp) x).hasFDerivAt
  · exact (hcd.comp continuous_snd).continuousOn
  · exact (hcd2.comp continuous_snd).continuousOn
  · intro x _ t _
    have h0 := hdz x t
    rw [h0]
    exact hasDerivWithinAt_const t _ _
  · have e : (fun p : ℝ × (Fin N → Euc d) =>
        derivWithin (fun r => configLift (fun _ => F) r p.2) (Set.Icc 0 T) p.1) = fun _ => 0 := by
      funext p
      exact hdz p.2 p.1
    rw [e]
    exact continuousOn_const

theorem dyn417_fkeRef_progL2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} (D : DynData d)
    (hF : IsFilteredSolution P ℱ W' W X) {T : ℝ} (hT : 0 ≤ T) (Φ : ℝ → Config d N → ℝ)
    (hΦ : IsC12On T Set.univ (configLift Φ)) :
    IsProgressiveL2 P ℱ (fun s ω k => fkeRef D T Φ X s ω k) := by
  obtain ⟨C1, hC1⟩ := bounded_of_periodic (T := T) (fun s Y => fderiv ℝ (configLift Φ s) Y)
    hΦ.cont_fderiv (fun s Y v hv => fderiv_configLift_add_lattice Φ s hv Y)
  exact IsProgressiveL2.of_bounded P (isProgressive_fkeRef hF.progressive hT D Φ hΦ)
    (max C1 0 * ∑ j : Fin N × Fin d, ‖liftedNoise D j‖)
    (fun s ω k => fkeRef_bound hT D Φ hC1 s ω k)

theorem dyn417_ito {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {s : ℝ} (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β) (D : DynData d) (hDs : D.s = s)
    (hDV : D.V = V) (hDM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hDi : D.invβ = β⁻¹)
    (hV2 : Torus.IsCk 2 D.V)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {H : ℝ}
    (hH : 0 ≤ H) (hC : IsContactStrongSolution P D H X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (F : Config d N → ℝ) (hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0)) :
    ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ H →
      F (X τ ω) = F (X 0 ω)
        + (∫ r in Set.Icc (0 : ℝ) τ, particleGen d s V β F (X (Real.toNNReal r) ω))
        + itoIntegral P ℱ W' (fun r ω k => fkeRef D H (fun _ => F) X r ω k) (τ : ℝ) ω := by
  have hΦc := dyn417_isC12 F H hFc
  have hlift := hC.ae_lift_eq hF
  have hI0 : ∀ᵐ ω ∂P, IntegrableOn (fun r : ℝ => driftProc D X (Real.toNNReal r) ω) (Set.Icc 0 H) :=
    hC.ae_integrableOn_drift hH le_rfl
  have hint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ H →
      intPart D X τ ω = ∫ r in Set.Icc (0 : ℝ) (τ : ℝ), driftProc D X (Real.toNNReal r) ω := by
    filter_upwards [hI0] with ω hω τ hτ
    exact intPart_eq_integral ω τ (hω.mono_set (Set.Icc_subset_Icc le_rfl hτ))
  have hlift' : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ H →
      X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i) := by
    filter_upwards [hlift, hint] with ω h1 h2 τ hτ
    rw [h1 τ hτ]
    funext i
    simp only [liftProcM, liftProc, h2 τ hτ]
  have hZint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ H →
      liftProcM D W' X τ ω = liftProcM D W' X 0 ω
        + (∫ r in Set.Icc (0 : ℝ) τ, driftProc D X (Real.toNNReal r) ω)
        + ∑ k, (W' τ ω k - W' 0 ω k) • liftedNoise D k := by
    filter_upwards [hint] with ω hω τ hτ
    rw [liftProcM_zero ω]
    simp only [liftProcM]
    rw [hω τ hτ]
  have hX₀ : ∀ t : ℝ, Measurable[ℱ t] (liftProcM D W' X 0) := by
    intro t
    have e : liftProcM D W' X 0 = fun ω => fun i => Torus.rep (X 0 ω i) :=
      funext fun ω => liftProcM_zero ω
    rw [e]
    have hg : Measurable (fun x : Config d N => fun i => Torus.rep (x i)) :=
      measurable_pi_iff.2 fun i => (measurable_torusRep d).comp (measurable_pi_apply i)
    exact hg.comp (hF.measurable_init t)
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hF.brownian (T := H) hH
    (configLift (fun _ => F)) hΦc (liftedNoise D) (liftProcM D W' X) (measurable_liftProcM hV2 hF)
    hX₀ (driftProc D X) (isProgressive_driftProc hV2 hF) hI0 hZint
  have hΨL2 := dyn417_fkeRef_progL2 D hF hH (fun _ => F) hΦc
  obtain ⟨N0, hN0m, hN0P, hN0⟩ := exists_null_of_ae (P := P)
    (p := fun ω => ∀ τ : ℝ≥0, (τ : ℝ) ≤ H → X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i)) hlift'
  have hMart : ∀ᵐ ω ∂P, ∀ τ : ℝ, localItoIntegral P ℱ W'
        (itoIntegrand H Set.univ (configLift (fun _ => F)) (ofNNRealTime (liftProcM D W' X))
          (fun _ _ => liftedNoise D)) τ ω
        = itoIntegral P ℱ W' (fun r ω k => fkeRef D H (fun _ => F) X r ω k) τ ω := by
    have hcongr := localItoIntegral_congr_null hF.brownian hΨL2.locL2 hN0m hN0P
      (Ψ := itoIntegrand H Set.univ (configLift (fun _ => F)) (ofNNRealTime (liftProcM D W' X))
        (fun _ _ => liftedNoise D))
      (fun s ω hω => by
        funext k
        exact itoIntegrand_eq_fkeRef D (fun _ => F) W' X ω (hN0 ω hω) s k)
      (fun s hs ω => by
        have hn : s ∉ Set.Icc (0:ℝ) H := fun h => absurd h.1 (not_le.2 hs)
        funext k
        simp [itoIntegrand, hn])
      (fun s hs ω => by
        have hn : s ∉ Set.Icc (0:ℝ) H := fun h => absurd h.1 (not_le.2 hs)
        funext k
        simp [fkeRef, hn])
    have hloc := localItoIntegral_eq_itoIntegral hF.brownian hΨL2
    filter_upwards [hcongr, hloc] with ω h1 h2
    intro τ
    rw [h1 τ, h2 τ]
  have hdrift : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0:ℝ) H,
      itoDrift H (configLift (fun _ => F)) (ofNNRealTime (liftProcM D W' X))
        (ofNNRealTime (driftProc D X)) (fun _ _ => liftedNoise D) r ω
        = particleGen d s V β F (X (Real.toNNReal r) ω) := by
    filter_upwards [hlift'] with ω hω r hr
    have hx : X (Real.toNNReal r) ω = fun j => Torus.mk (liftProcM D W' X (Real.toNNReal r) ω j) :=
      hω _ (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
    rw [itoDrift_eq_fkeIto D H (fun _ => F) (liftProcM D W' X) X ω r hx]
    have e : ∀ i, Torus.mk (liftProcM D W' X (Real.toNNReal r) ω i)
        = Torus.mk (repC (X (Real.toNNReal r) ω) i) := by
      intro i
      show _ = Torus.mk (Torus.rep (X (Real.toNNReal r) ω i))
      rw [Torus.mk_rep]
      exact (congrFun hx i).symm
    rw [fkeIto_eq_of_mk D H (fun _ => F) r e,
      dyn417_fkeIto_eq V β hβ D hDs hDV hDM hDi F hFc H r (repC (X (Real.toNNReal r) ω)), mk_repC]
  filter_upwards [hito, hlift', hdrift, hMart] with ω hωito hω hωd hωM
  intro τ hτ
  have h := hωito.2 τ hτ
  have hL : configLift (fun _ => F) (τ : ℝ) (liftProcM D W' X τ ω) = F (X τ ω) := by
    rw [hω τ hτ]
    rfl
  have hL0 : configLift (fun _ => F) 0 (liftProcM D W' X 0 ω) = F (X 0 ω) := by
    rw [hω 0 (by simpa using hH)]
    rfl
  have hI : ∫ r in Set.Icc (0 : ℝ) (τ : ℝ),
      itoDrift H (configLift (fun _ => F)) (ofNNRealTime (liftProcM D W' X))
        (ofNNRealTime (driftProc D X)) (fun _ _ => liftedNoise D) r ω
        = ∫ r in Set.Icc (0 : ℝ) (τ : ℝ), particleGen d s V β F (X (Real.toNNReal r) ω) :=
    setIntegral_congr_fun measurableSet_Icc fun r hr => hωd r ⟨hr.1, hr.2.trans hτ⟩
  rw [hI, hL, hL0, hωM (τ : ℝ)] at h
  exact h

/-! ### Part C: energy identities and the pointwise integrand -/

theorem dyn417_cl_const {N : ℕ} (F : Config d N → ℝ) (r : ℝ) :
    configLift (fun _ => F) r = configLift (fun _ => F) 0 := rfl

theorem dyn417_enorm_sq_real (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

theorem dyn417_norm_sq_euc (g : Euc d) :
    ‖g‖ ^ 2 = ∑ j : Fin d, (inner ℝ (EuclideanSpace.single j 1) g) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.inner_single_left]
  simp [Real.norm_eq_abs, sq_abs]

theorem dyn417_enorm_sq_euc (g : Euc d) :
    ‖g‖ₑ ^ 2 = ∑ j : Fin d, ‖inner ℝ (EuclideanSpace.single j 1) g‖ₑ ^ 2 := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg g), dyn417_norm_sq_euc g,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dyn417_enorm_sq_real]

/-- The squared configuration gradient, as a lintegrand-friendly function of the configuration. -/
def dyn417G {N : ℕ} (F : Config d N → ℝ) (x : Config d N) : ℝ≥0∞ :=
  ∑ i, ‖configGrad F x i‖ₑ ^ 2

theorem dyn417_grad_sum {N : ℕ} (F : Config d N → ℝ)
    (hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0)) (Y : Fin N → Euc d) :
    ∑ i, ‖configGrad F (fun j => Torus.mk (Y j)) i‖ₑ ^ 2
      = ∑ k : Fin N × Fin d,
          ‖fderiv ℝ (configLift (fun _ => F) 0) Y (configBasis d N k)‖ₑ ^ 2 := by
  have hD1 : Differentiable ℝ (configLift (fun _ => F) 0) := hFc.differentiable (by simp)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dyn417_enorm_sq_euc]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dyn417_inner_configGrad F hD1 Y i (EuclideanSpace.single j 1)]
  rfl

theorem dyn417_G_eq {N : ℕ} (F : Config d N → ℝ)
    (hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0)) (x : Config d N) :
    dyn417G F x = ∑ k : Fin N × Fin d,
      ‖fderiv ℝ (configLift (fun _ => F) 0) (repC x) (configBasis d N k)‖ₑ ^ 2 := by
  have h := dyn417_grad_sum F hFc (repC x)
  rw [mk_repC] at h
  exact h

theorem dyn417_noise_sum {N : ℕ} (D : DynData d) (β : ℝ) (hβ : 0 < β) (hDi : D.invβ = β⁻¹)
    (L : (Fin N → Euc d) →L[ℝ] ℝ) :
    ∑ k : Fin N × Fin d, ‖L (liftedNoise D k)‖ₑ ^ 2
      = ENNReal.ofReal (2 * β⁻¹) * ∑ k : Fin N × Fin d, ‖L (configBasis d N k)‖ₑ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : Real.sqrt (2 * D.invβ) ^ 2 = 2 * β⁻¹ := by
    rw [Real.sq_sqrt (by rw [hDi]; positivity), hDi]
  have e : liftedNoise D k = Real.sqrt (2 * D.invβ) • configBasis d N k := rfl
  rw [e, map_smul, smul_eq_mul, enorm_mul, mul_pow, dyn417_enorm_sq_real, hc]

theorem dyn417_pointwise {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (D : DynData d) (β : ℝ)
    (hβ : 0 < β) (hDi : D.invβ = β⁻¹) (F : Config d N → ℝ)
    (hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0))
    {X : ℝ≥0 → Ω → Config d N} {H : ℝ} {s : ℝ} (hs : s ∈ Set.Icc 0 H) (ω : Ω) :
    ∑ k, ‖fkeRef D H (fun _ => F) X s ω k‖ₑ ^ 2
      = ENNReal.ofReal (2 * β⁻¹) * dyn417G F (X (Real.toNNReal s) ω) := by
  unfold fkeRef
  simp only [if_pos hs]
  rw [clampTI_of_mem hs, dyn417_cl_const F s, dyn417_G_eq F hFc,
    dyn417_noise_sum D β hβ hDi]

theorem dyn417_iso {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (D : DynData d) (β : ℝ) (hβ : 0 < β) (hDi : D.invβ = β⁻¹) (F : Config d N → ℝ)
    (hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0))
    {X : ℝ≥0 → Ω → Config d N} {H : ℝ} (hXm : ∀ r : ℝ≥0, Measurable (X r))
    (hXj : Measurable (fun p : ℝ × Ω => ofNNRealTime X p.1 p.2))
    (μ : Measure (Config d N)) (hstat : ∀ r : ℝ≥0, (r : ℝ) ≤ H → P.map (X r) = μ)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htH : t ≤ H) :
    sqIntegralOn P (fun s ω => Set.indicator (Set.Ioc u t)
        (fun _ => fun k => fkeRef D H (fun _ => F) X s ω k) s) t
      = ENNReal.ofReal (2 * β⁻¹) * ENNReal.ofReal (t - u) * ∫⁻ x, dyn417G F x ∂μ := by
  have hG : Measurable (dyn417G F) := by
    have hcd : Continuous (fderiv ℝ (configLift (fun _ => F) 0)) := hFc.continuous_fderiv (by simp)
    have e : dyn417G F = fun x => ∑ k : Fin N × Fin d,
        ‖fderiv ℝ (configLift (fun _ => F) 0) (repC x) (configBasis d N k)‖ₑ ^ 2 := by
      funext x
      exact dyn417_G_eq F hFc x
    rw [e]
    refine Finset.measurable_sum _ fun k _ => ?_
    have hm : Measurable (fun x : Config d N => fderiv ℝ (configLift (fun _ => F) 0) (repC x)) :=
      hcd.measurable.comp measurable_repC
    exact ((hm.apply_continuousLinearMap (configBasis d N k)).enorm).pow_const 2
  have hGs : Measurable (fun p : ℝ × Ω => dyn417G F (ofNNRealTime X p.1 p.2)) := hG.comp hXj
  set c := ENNReal.ofReal (2 * β⁻¹) with hc
  have hmeasQ : Measurable (fun q : ℝ × Ω =>
      if q.1 ∈ Set.Ioc u t then c * dyn417G F (ofNNRealTime X q.1 q.2) else 0) :=
    Measurable.ite (measurableSet_Ioc.preimage measurable_fst) (measurable_const.mul hGs)
      measurable_const
  have hunc : Function.uncurry (fun (ω : Ω) (s : ℝ) => Set.indicator (Set.Ioc u t)
      (fun s => c * dyn417G F (ofNNRealTime X s ω)) s)
      = fun p : Ω × ℝ => if p.2 ∈ Set.Ioc u t then c * dyn417G F (ofNNRealTime X p.2 p.1) else 0 := by
    funext p
    simp [Function.uncurry, Set.indicator_apply]
  have hpt : ∀ ω : Ω, ∀ s ∈ Set.Icc 0 t,
      ∑ k, ‖Set.indicator (Set.Ioc u t) (fun _ => fun k => fkeRef D H (fun _ => F) X s ω k) s k‖ₑ ^ 2
        = Set.indicator (Set.Ioc u t) (fun s => c * dyn417G F (ofNNRealTime X s ω)) s := by
    intro ω s hs
    by_cases hsI : s ∈ Set.Ioc u t
    · have hsH : s ∈ Set.Icc 0 H := ⟨by linarith [hsI.1, hu], by linarith [hsI.2, hs.2]⟩
      simp only [Set.indicator_of_mem hsI]
      exact dyn417_pointwise D β hβ hDi F hFc hsH ω
    · simp [Set.indicator_of_notMem hsI]
  unfold sqIntegralOn
  have step1 : ∀ ω : Ω, ∫⁻ s in Set.Icc 0 t, ∑ k, ‖Set.indicator (Set.Ioc u t)
        (fun _ => fun k => fkeRef D H (fun _ => F) X s ω k) s k‖ₑ ^ 2
      = ∫⁻ s in Set.Icc 0 t, Set.indicator (Set.Ioc u t)
          (fun s => c * dyn417G F (ofNNRealTime X s ω)) s := fun ω =>
    setLIntegral_congr_fun measurableSet_Icc (fun s hs => hpt ω s hs)
  rw [lintegral_congr step1]
  have hmeas : AEMeasurable (Function.uncurry (fun (ω : Ω) (s : ℝ) => Set.indicator (Set.Ioc u t)
      (fun s => c * dyn417G F (ofNNRealTime X s ω)) s)) (P.prod (volume.restrict (Set.Icc 0 t))) := by
    rw [hunc]
    exact (hmeasQ.comp measurable_swap).aemeasurable
  rw [lintegral_lintegral_swap hmeas]
  have step2 : ∀ s ∈ Set.Icc 0 t, ∫⁻ ω, Set.indicator (Set.Ioc u t)
      (fun s => c * dyn417G F (ofNNRealTime X s ω)) s ∂P
      = Set.indicator (Set.Ioc u t) (fun _ => c * ∫⁻ x, dyn417G F x ∂μ) s := by
    intro s hs
    by_cases hsI : s ∈ Set.Ioc u t
    · have hsH : (Real.toNNReal s : ℝ) ≤ H := by
        rw [Real.coe_toNNReal _ (by linarith [hsI.1, hu])]
        linarith [hsI.2, hs.2]
      simp only [Set.indicator_of_mem hsI, ofNNRealTime_apply]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_map hG (hXm _),
        hstat _ hsH]
    · simp [Set.indicator_of_notMem hsI]
  rw [setLIntegral_congr_fun measurableSet_Icc step2]
  rw [lintegral_indicator_const measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hu le_rfl) |>.trans
      (le_refl _)), Real.volume_Ioc]
  ring

theorem dyn417_setInt_interval (g : ℝ → ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ∫ r in Set.Icc (0 : ℝ) v, g r = ∫ r in (0 : ℝ)..v, g r := by
  rw [intervalIntegral.integral_of_le hv, integral_Icc_eq_integral_Ioc]

/-- Doob's maximal inequality for the stochastic remainder on `[u, t]`, with the Dynkin identity
`F(X^v) - F(X^u) - ∫_u^v G = M_v - M_u` obtained from the pathwise Itô identity. -/
theorem dyn417_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {X : ℝ≥0 → Ω → Config d N}
    {H s : ℝ} (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β) (D : DynData d) (hDi : D.invβ = β⁻¹)
    (hW : IsBrownianFiltration P ℱ W') (F : Config d N → ℝ)
    (hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0))
    (hXm : ∀ r : ℝ≥0, Measurable (X r))
    (hXj : Measurable (fun p : ℝ × Ω => ofNNRealTime X p.1 p.2))
    (μ : Measure (Config d N)) (hstat : ∀ r : ℝ≥0, (r : ℝ) ≤ H → P.map (X r) = μ)
    (hΨ0 : IsProgressiveL2 P ℱ (fun r ω k => fkeRef D H (fun _ => F) X r ω k))
    (hM : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ H →
      F (X τ ω) = F (X 0 ω)
        + (∫ r in Set.Icc (0 : ℝ) τ, particleGen d s V β F (X (Real.toNNReal r) ω))
        + itoIntegral P ℱ W' (fun r ω k => fkeRef D H (fun _ => F) X r ω k) (τ : ℝ) ω)
    (hint : ∀ᵐ ω ∂P, IntervalIntegrable
      (fun r : ℝ => particleGen d s V β F (X r.toNNReal ω)) volume 0 H)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htH : t ≤ H) :
    ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
        ((F (X v.toNNReal ω) - F (X u.toNNReal ω) -
          ∫ r in u..v, particleGen d s V β F (X r.toNNReal ω)) ^ 2) ∂P
      ≤ ENNReal.ofReal (8 * β⁻¹ * (t - u)) * ∫⁻ Y, dyn417G F Y ∂μ := by
  have hH0 : 0 ≤ H := hu.trans (hut.trans htH)
  have hΨ'L2 : IsProgressiveL2 P ℱ (fun r ω => Set.indicator (Set.Ioc u t)
      (fun _ => fun k => fkeRef D H (fun _ => F) X r ω k) r) := by
    have e : (fun r ω => Set.indicator (Set.Ioc u t)
        (fun _ => fun k => fkeRef D H (fun _ => F) X r ω k) r)
        = restrictFun (fun r ω k => fkeRef D H (fun _ => F) X r ω k) u t Set.univ := by
      funext r ω
      simp [restrictFun, Set.indicator]
    rw [e]
    exact IsProgressiveL2.restrictFun hΨ0 MeasurableSet.univ
  have hI := itoIntegral_indicator_Ioc hW hΨ0 hu hut
  have hDoob := lintegral_iSup_itoIntegral_sq_le hW hΨ'L2 t
  have hiso := dyn417_iso D β hβ hDi F hFc hXm hXj μ hstat hu hut htH
  have hgood : ∀ᵐ ω ∂P, ∀ v ∈ ratTimes u (t - u), ENNReal.ofReal
        ((F (X v.toNNReal ω) - F (X u.toNNReal ω) -
          ∫ r in u..v, particleGen d s V β F (X r.toNNReal ω)) ^ 2)
      ≤ (⨆ τ ∈ Set.Icc (0 : ℝ) t, ‖itoIntegral P ℱ W' (fun r ω =>
          Set.indicator (Set.Ioc u t) (fun _ => fun k => fkeRef D H (fun _ => F) X r ω k) r) τ ω‖ₑ) ^ 2 := by
    filter_upwards [hM, hint, hI] with ω hMω hintω hIω
    intro v hv
    have hvI : v ∈ Set.Icc u t := by
      have h1 := hv.1
      have h2 : u + (t - u) = t := by ring
      rw [h2] at h1
      exact h1
    have hv0 : 0 ≤ v := hu.trans hvI.1
    have hvH : v ≤ H := hvI.2.trans htH
    have hu0 : 0 ≤ u := hu
    have huH : u ≤ H := hut.trans htH
    have hMv := hMω v.toNNReal (by rw [Real.coe_toNNReal _ hv0]; exact hvH)
    have hMu := hMω u.toNNReal (by rw [Real.coe_toNNReal _ hu0]; exact huH)
    rw [Real.coe_toNNReal _ hv0, dyn417_setInt_interval _ hv0] at hMv
    rw [Real.coe_toNNReal _ hu0, dyn417_setInt_interval _ hu0] at hMu
    have hint0u : IntervalIntegrable (fun r : ℝ => particleGen d s V β F (X r.toNNReal ω))
        volume 0 u :=
      hintω.mono_set (by rw [Set.uIcc_of_le hu0, Set.uIcc_of_le hH0]; exact Set.Icc_subset_Icc le_rfl huH)
    have huv : IntervalIntegrable (fun r : ℝ => particleGen d s V β F (X r.toNNReal ω))
        volume u v :=
      hintω.mono_set (by
        rw [Set.uIcc_of_le hvI.1, Set.uIcc_of_le hH0]
        exact Set.Icc_subset_Icc (hu0) hvH)
    have hsplit : ∫ r in (0 : ℝ)..v, particleGen d s V β F (X r.toNNReal ω)
        = (∫ r in (0 : ℝ)..u, particleGen d s V β F (X r.toNNReal ω))
          + (∫ r in u..v, particleGen d s V β F (X r.toNNReal ω)) :=
      (intervalIntegral.integral_add_adjacent_intervals hint0u huv).symm
    have hIv := hIω v
    rw [min_eq_left hvI.2, min_eq_right hvI.1] at hIv
    have hdiff : F (X v.toNNReal ω) - F (X u.toNNReal ω)
        - ∫ r in u..v, particleGen d s V β F (X r.toNNReal ω)
        = itoIntegral P ℱ W' (fun r ω =>
          Set.indicator (Set.Ioc u t) (fun _ => fun k => fkeRef D H (fun _ => F) X r ω k) r) v ω := by
      rw [hIv, hMv, hMu, hsplit]
      ring
    rw [hdiff, ← dyn417_enorm_sq_real]
    exact pow_le_pow_left₀ (by positivity)
      (le_iSup₂ (f := fun τ (_ : τ ∈ Set.Icc (0 : ℝ) t) => ‖itoIntegral P ℱ W' (fun r ω =>
          Set.indicator (Set.Ioc u t) (fun _ => fun k => fkeRef D H (fun _ => F) X r ω k) r) τ ω‖ₑ)
        v ⟨hv0, hvI.2⟩) 2
  have e4 : ENNReal.ofReal (8 * β⁻¹ * (t - u))
      = 4 * (ENNReal.ofReal (2 * β⁻¹) * ENNReal.ofReal (t - u)) := by
    rw [show (8 : ℝ) * β⁻¹ * (t - u) = 4 * ((2 * β⁻¹) * (t - u)) by ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity)]
    norm_num
  calc _ ≤ ∫⁻ ω, (⨆ τ ∈ Set.Icc (0 : ℝ) t, ‖itoIntegral P ℱ W' (fun r ω =>
          Set.indicator (Set.Ioc u t) (fun _ => fun k => fkeRef D H (fun _ => F) X r ω k) r) τ ω‖ₑ) ^ 2 ∂P :=
        lintegral_mono_ae (hgood.mono fun ω hω => iSup₂_le fun v hv => hω v hv)
    _ ≤ 4 * sqIntegralOn P (fun r ω => Set.indicator (Set.Ioc u t)
          (fun _ => fun k => fkeRef D H (fun _ => F) X r ω k) r) t := hDoob
    _ = _ := by rw [hiso, e4]; ring

theorem dyn417_isCk2 {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) : Torus.IsCk 2 h :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm) (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))

set_option maxHeartbeats 1000000 in
/-- Integrability of the Dynkin integrand along a single path: the drift is bounded uniformly in the
configuration (`fkeIto_bound` at horizon `0`, which is harmless since `particleGen` is time-free) and
measurable in time (`measurable_fkeIto_sample`), so it is interval integrable for every `ω`. -/
theorem dyn417_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {N : ℕ} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hfilt : IsFilteredSolution P ℱ W' W X) {s : ℝ} (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β)
    (D : DynData d) (hDs : D.s = s) (hDV : D.V = V) (hDM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hDi : D.invβ = β⁻¹) (hV2 : Torus.IsCk 2 D.V) (hN : 0 < N)
    (F : Config d N → ℝ)
    (hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0))
    {K : Set (Config d N)} (hK : IsCompact K) (hdisj : Disjoint K (collisionSet d N))
    (hsupp : ∀ Y, Y ∉ K → F Y = 0) (H : ℝ) (ω : Ω) :
    IntervalIntegrable (fun r : ℝ => particleGen d s V β F (X r.toNNReal ω)) volume 0 H := by
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  have hΦ := dyn417_isC12 F 0 hFc
  have hsupp' : ∀ (r : ℝ) (Y : Config d N), Y ∉ K → (fun _ => F) r Y = 0 :=
    fun r Y hY => hsupp Y hY
  obtain ⟨C, hC⟩ := fkeIto_bound (le_refl (0 : ℝ)) D hN hV2 (fun _ => F) hΦ hK hdisj hsupp'
  have hfeq := dyn417_fkeIto_eq V β hβ D hDs hDV hDM hDi F hFc
  have hbd : ∀ Z : Config d N, ‖particleGen d s V β F Z‖ ≤ C := by
    intro Z
    have h := hC 0 ⟨le_refl _, le_refl _⟩ (repC Z)
    rw [hfeq 0 0 (repC Z), mk_repC] at h
    exact h
  have hm : Measurable (fun p : ℝ × Ω => particleGen d s V β F (X (Real.toNNReal p.1) p.2)) := by
    have h := measurable_fkeIto_sample hfilt.progressive (le_refl (0 : ℝ)) D hV2 (fun _ => F) hΦ
    have heq : (fun p : ℝ × Ω => particleGen d s V β F (X (Real.toNNReal p.1) p.2)) =
        (fun p : ℝ × Ω => fkeIto D 0 (fun _ => F) (clampTI 0 p.1) (repC (X (Real.toNNReal p.1) p.2))) := by
      funext p
      rw [hfeq, mk_repC]
    rw [heq]
    exact h
  have hpair : Measurable (fun r : ℝ => ((r, ω) : ℝ × Ω)) :=
    Measurable.prodMk measurable_id measurable_const
  have hmr : Measurable (fun r : ℝ => particleGen d s V β F (X r.toNNReal ω)) :=
    Measurable.comp (g := fun p : ℝ × Ω => particleGen d s V β F (X (Real.toNNReal p.1) p.2))
      (f := fun r : ℝ => ((r, ω) : ℝ × Ω)) hm hpair
  exact (intervalIntegrable_const (c := C)).mono_fun hmr.aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall fun r => (hbd _).trans ((le_abs_self C).trans (Real.norm_eq_abs C).symm.le))

theorem dynkin_smooth_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X)
    (F : Config d N → ℝ) (hFm : Measurable F)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0))
    (hK : ∃ K : Set (Config d N), IsCompact K ∧ Disjoint K (collisionSet d N) ∧ ∀ Y, Y ∉ K → F Y = 0) :
    (∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => particleGen d s V β F (X r.toNNReal ω)) volume 0 H) ∧
    (∀ᵐ ω ∂P, ContinuousOn (fun t : ℝ => F (X t.toNNReal ω) - F (X 0 ω) -
        ∫ r in (0 : ℝ)..t, particleGen d s V β F (X r.toNNReal ω)) (Set.Icc 0 H)) ∧
    (∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
          ((F (X v.toNNReal ω) - F (X u.toNNReal ω) -
            ∫ r in u..v, particleGen d s V β F (X r.toNNReal ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (8 * β⁻¹ * (t - u)) *
          ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂(canonicalGibbs (periodicRiesz d s) V N β)) := by
  obtain ⟨K, hKc, hKd, hKs⟩ := hK
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  have hstr : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) H X₀ W X := by
    rcases hflow.flow.flow with h | ⟨h1, -⟩
    · exact h.1
    · exfalso
      omega
  obtain ⟨ℱ, W', hfilt⟩ := hflow.filtered
  have hC := hstr.toContact
  have hV2 : Torus.IsCk 2 (PDE.mfData d s hs0 hsd V β hβ).V := dyn417_isCk2 hV
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ H hN P X₀ W X hflow
  have hXm : ∀ r : ℝ≥0, Measurable (X r) := hstr.adapted
  have hXj : Measurable (fun p : ℝ × Ω => ofNNRealTime X p.1 p.2) :=
    measurable_of_progressive hfilt.progressive
  have hDM : (PDE.mfData d s hs0 hsd V β hβ).M = -(1 : Matrix (Fin d) (Fin d) ℝ) := rfl
  have hint : ∀ ω : Ω, IntervalIntegrable
      (fun r : ℝ => particleGen d s V β F (X r.toNNReal ω)) volume 0 H := fun ω =>
    dyn417_integrable (s := s) hfilt V β hβ (PDE.mfData d s hs0 hsd V β hβ) rfl rfl hDM rfl hV2
      (by omega) F hF hKc hKd hKs H ω
  have hint' : ∀ᵐ ω ∂P, IntervalIntegrable
      (fun r : ℝ => particleGen d s V β F (X r.toNNReal ω)) volume 0 H :=
    Filter.Eventually.of_forall hint
  refine ⟨hint', ?_, ?_⟩
  · rcases le_or_gt 0 H with hH | hH
    · have hM := dyn417_ito (s := s) V β hβ (PDE.mfData d s hs0 hsd V β hβ) rfl rfl hDM rfl hV2
        hH hC hfilt F hF
      filter_upwards [hM] with ω hω
      refine ((continuous_itoIntegral P ℱ W'
        (fun r ω k => fkeRef (PDE.mfData d s hs0 hsd V β hβ) H (fun _ => F) X r ω k) ω).continuousOn).congr ?_
      intro t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have htH : t ≤ H := ht.2
      have h := hω t.toNNReal (by rw [Real.coe_toNNReal _ ht0]; exact htH)
      rw [Real.coe_toNNReal _ ht0, dyn417_setInt_interval _ ht0] at h
      show F (X t.toNNReal ω) - F (X 0 ω) -
          ∫ r in (0 : ℝ)..t, particleGen d s V β F (X r.toNNReal ω) =
        itoIntegral P ℱ W' (fun r ω k => fkeRef (PDE.mfData d s hs0 hsd V β hβ) H (fun _ => F) X r ω k)
          t ω
      rw [h]
      ring
    · exact Filter.Eventually.of_forall fun ω => by
        rw [Set.Icc_eq_empty (not_le.2 hH)]
        exact continuousOn_empty _
  · intro u t hu hut htH
    rcases le_or_gt 0 H with hH | hH
    · have hM := dyn417_ito (s := s) V β hβ (PDE.mfData d s hs0 hsd V β hβ) rfl rfl hDM rfl hV2
        hH hC hfilt F hF
      have hΨ0 := dyn417_fkeRef_progL2 (PDE.mfData d s hs0 hsd V β hβ) hfilt hH (fun _ => F)
        (dyn417_isC12 F H hF)
      exact dyn417_bound (s := s) V β hβ (PDE.mfData d s hs0 hsd V β hβ) rfl hfilt.brownian F hF
        hXm hXj _ hstat hΨ0 hM hint' hu hut htH
    · exfalso
      linarith

end HRS.ME

end
