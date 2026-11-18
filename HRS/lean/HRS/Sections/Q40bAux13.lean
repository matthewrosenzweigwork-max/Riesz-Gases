import HRS.Sections.Q40bAux10

/-!
# Packet Q40b, part 13: the comparison inequality against `law X * N(0, Σ)` (no Gaussian on `Ω`)

`q40b_master_gamma` is `q40b_master` with the Gaussian `G` on `Ω` replaced by the product measure
`(law ζ_0(Uφ)) ⊗ N(0, Σ)` (the law of `ζ_0(Uφ) + G` for `G` independent of `X_0`), which exists without
enlarging the particle system (used for `criterion_stationary`, where no Gaussian is given).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

section Interp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {p : ℕ}

/-- Conditional Gaussian interpolation for a Gaussian `G` that is only independent of the
`ℱ_0`-measurable shift `X` (not of the whole filtration): enlarge the space to `Ω × ℝ^p`. -/
theorem q40b_interp_gamma [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) {T : ℝ} (hT : 0 ≤ T)
    {M : ℝ → Ω → (ℝ^p)} {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ}
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsb : IsDetCovMatrix T sb)
    {X : Ω → (ℝ^p)} (hX : Measurable[ℱ 0] X) {γ : Measure (ℝ^p)} [IsProbabilityMeasure γ]
    (hG : γ = multivariateGaussian 0 (integratedCov T sb))
    {h : (ℝ^p) → ℝ} (hh : MemCb 2 h) :
    |(∫ ω, h (X ω + M T ω) ∂P) - ∫ z, h z ∂(((P.map X).prod γ).map fun r => r.1 + r.2)| ≤
      (1 / 2) * hessSup h * covDiscrepancyMatrix P T Sg sb := by
  classical
  set P' : Measure (Ω × (ℝ^p)) := P.prod γ with hP'
  have hπ : MeasurePreserving (Prod.fst : Ω × (ℝ^p) → Ω) P' P := measurePreserving_fst
  have hπ2 : MeasurePreserving (Prod.snd : Ω × (ℝ^p) → ℝ^p) P' γ := measurePreserving_snd
  set ℱ' := comapFil ℱ hπ.measurable with hℱ'
  have hM' := isVecMart_comapFil hπ hM
  have hX' : Measurable[ℱ' 0] (fun q : Ω × (ℝ^p) => X q.1) :=
    @Measurable.comp (Ω × (ℝ^p)) Ω (ℝ^p) ((ℱ 0).comap Prod.fst) (ℱ 0) _ X Prod.fst hX
      (comap_measurable Prod.fst)
  have hG' : law P' (Prod.snd : Ω × (ℝ^p) → ℝ^p) = multivariateGaussian 0 (integratedCov T sb) := by
    exact hπ2.map_eq.trans hG
  have hGind' : Indep (MeasurableSpace.comap (Prod.snd : Ω × (ℝ^p) → ℝ^p) inferInstance) (ℱ' T) P' := by
    have h1 : IndepFun (Prod.fst : Ω × (ℝ^p) → Ω) (Prod.snd : Ω × (ℝ^p) → ℝ^p) P' :=
      indepFun_prod (μ := P) (ν := γ) (X := id) (Y := id) measurable_id measurable_id
    have h2 : Indep (MeasurableSpace.comap (Prod.fst : Ω × (ℝ^p) → Ω) inferInstance)
        (MeasurableSpace.comap (Prod.snd : Ω × (ℝ^p) → ℝ^p) inferInstance) P' := h1
    exact indep_of_indep_of_le_right h2.symm (MeasurableSpace.comap_mono (ℱ.le T))
  have hcond := conditional_gaussian_interpolation P' ℱ' T hT _ _ hM' sb hsb (fun q => X q.1) hX'
    Prod.snd measurable_snd.aemeasurable hG' hGind' h hh
  -- integrate the conditional bound on the enlarged space
  have hm : ℱ' 0 ≤ (inferInstance : MeasurableSpace (Ω × (ℝ^p))) := ℱ'.le 0
  have hXm : Measurable (fun q : Ω × (ℝ^p) => X q.1) :=
    (hX.mono (ℱ.le 0) le_rfl).comp measurable_fst
  have hMt : AEMeasurable (fun q : Ω × (ℝ^p) => M T q.1) P' :=
    (((hM.sq_int T ⟨hT, le_rfl⟩).comp_measurePreserving hπ).aestronglyMeasurable).aemeasurable
  set g : Ω → ℝ := fun ω => ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ) with hg
  have hintg : Integrable g P :=
    LindebergAux.Iblk_integrable P ℱ hM hsb.meas hsb.int le_rfl le_rfl
  have hintg' : Integrable (fun q : Ω × (ℝ^p) => g q.1) P' := hπ.integrable_comp_of_integrable hintg
  have hU1 : Integrable (fun q : Ω × (ℝ^p) => h (X q.1 + M T q.1)) P' :=
    integrable_memCb_comp P' hh (hXm.aemeasurable.add hMt)
  have hU2 : Integrable (fun q : Ω × (ℝ^p) => h (X q.1 + q.2)) P' :=
    integrable_memCb_comp P' hh (hXm.aemeasurable.add measurable_snd.aemeasurable)
  have hUi : Integrable (P'[fun q : Ω × (ℝ^p) => h (X q.1 + M T q.1) | ℱ' 0]) P' := integrable_condExp
  have hVi : Integrable (P'[fun q : Ω × (ℝ^p) => h (X q.1 + q.2) | ℱ' 0]) P' := integrable_condExp
  have hWi : Integrable (P'[fun q : Ω × (ℝ^p) => g q.1 | ℱ' 0]) P' := integrable_condExp
  have s2 : |(∫ q, h (X q.1 + M T q.1) ∂P') - ∫ q, h (X q.1 + q.2) ∂P'| ≤
      (1 / 2) * hessSup h * ∫ q, g q.1 ∂P' := by
    rw [← integral_condExp hm (f := fun q : Ω × (ℝ^p) => h (X q.1 + M T q.1)),
      ← integral_condExp hm (f := fun q : Ω × (ℝ^p) => h (X q.1 + q.2)), ← integral_sub hUi hVi,
      ← Real.norm_eq_abs]
    have hb : ∀ᵐ q ∂P', ‖(P'[fun q : Ω × (ℝ^p) => h (X q.1 + M T q.1) | ℱ' 0]) q -
        (P'[fun q : Ω × (ℝ^p) => h (X q.1 + q.2) | ℱ' 0]) q‖ ≤
        (1 / 2) * hessSup h * (P'[fun q : Ω × (ℝ^p) => g q.1 | ℱ' 0]) q := by
      filter_upwards [hcond] with q hq
      simpa [Real.norm_eq_abs] using hq
    refine (norm_integral_le_of_norm_le (hWi.const_mul ((1 / 2) * hessSup h)) hb).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_condExp hm]
  -- transfer back to `Ω`
  have hmap := hπ.map_eq
  have e1 : ∫ q, h (X q.1 + M T q.1) ∂P' = ∫ ω, h (X ω + M T ω) ∂P := by
    have hmeas : AEStronglyMeasurable (fun ω => h (X ω + M T ω)) (P'.map Prod.fst) := by
      rw [hmap]
      exact (hh.1.continuous.measurable.comp_aemeasurable
        ((hX.mono (ℱ.le 0) le_rfl).aemeasurable.add
          ((hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable))).aestronglyMeasurable
    have := integral_map (μ := P') (φ := Prod.fst) hπ.aemeasurable hmeas
    rw [hmap] at this
    exact this.symm
  have e3 : ∫ q, g q.1 ∂P' = ∫ ω, g ω ∂P := by
    have := integral_map (μ := P') (φ := Prod.fst) hπ.aemeasurable
      (by rw [hmap]; exact hintg.aestronglyMeasurable : AEStronglyMeasurable g (P'.map Prod.fst))
    rw [hmap] at this
    exact this.symm
  have e2 : ∫ q, h (X q.1 + q.2) ∂P' = ∫ z, h z ∂(((P.map X).prod γ).map fun r => r.1 + r.2) := by
    have hXm0 : Measurable X := hX.mono (ℱ.le 0) le_rfl
    have hadd : Measurable (fun r : (ℝ^p) × (ℝ^p) => r.1 + r.2) := measurable_fst.add measurable_snd
    have hR : P'.map (fun q : Ω × (ℝ^p) => X q.1 + q.2) = ((P.map X).prod γ).map (fun r => r.1 + r.2) := by
      have hpm : (P.map X).prod (γ.map id) = (P.prod γ).map (Prod.map X id) :=
        Measure.map_prod_map P γ hXm0 measurable_id
      rw [Measure.map_id] at hpm
      rw [hpm, Measure.map_map hadd (hXm0.prodMap measurable_id)]
      rfl
    have hmeas : AEStronglyMeasurable h (P'.map (fun q : Ω × (ℝ^p) => X q.1 + q.2)) :=
      hh.1.continuous.aestronglyMeasurable
    calc ∫ q : Ω × (ℝ^p), h (X q.1 + q.2) ∂P'
        = ∫ y, h y ∂(P'.map (fun q : Ω × (ℝ^p) => X q.1 + q.2)) :=
          (integral_map (φ := fun q : Ω × (ℝ^p) => X q.1 + q.2) (hXm.add measurable_snd).aemeasurable
            hmeas).symm
      _ = _ := by rw [hR]
  rw [e1, e2, e3] at s2
  exact s2


/-- The `C²`-smooth distance version. -/
theorem q40b_smoothDist_interp_gamma [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) {T : ℝ} (hT : 0 ≤ T)
    {M : ℝ → Ω → (ℝ^p)} {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ}
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsb : IsDetCovMatrix T sb)
    {X : Ω → (ℝ^p)} (hX : Measurable[ℱ 0] X) {γ : Measure (ℝ^p)} [IsProbabilityMeasure γ]
    (hG : γ = multivariateGaussian 0 (integratedCov T sb)) :
    smoothDist 2 (law P fun ω => X ω + M T ω)
      (((P.map X).prod γ).map fun r => r.1 + r.2) ≤
      (1 / 2) * covDiscrepancyMatrix P T Sg sb := by
  have hXm0 : Measurable X := hX.mono (ℱ.le 0) le_rfl
  have hMt : AEMeasurable (M T) P :=
    (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hcd : 0 ≤ covDiscrepancyMatrix P T Sg sb :=
    integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  obtain ⟨hΦ, hb, hc⟩ := Φ.2
  have hMem : MemCb 2 Φ.1 := ⟨hΦ, hb⟩
  have hhs : hessSup Φ.1 ≤ 1 := by
    have : (⨆ x, ‖iteratedFDeriv ℝ 2 Φ.1 x‖) ≤ 1 := by
      refine le_trans ?_ hc
      unfold cbNorm
      exact Finset.single_le_sum (f := fun j => ⨆ z : EuclideanSpace ℝ (Fin p),
        ‖iteratedFDeriv ℝ j Φ.1 z‖) (fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _)
        (by simp : 2 ∈ Finset.range (2 + 1))
    exact this
  have e1 : ∫ z, Φ.1 z ∂(law P fun ω => X ω + M T ω) = ∫ ω, Φ.1 (X ω + M T ω) ∂P :=
    integral_map (hXm0.aemeasurable.add hMt) hΦ.continuous.aestronglyMeasurable
  rw [e1]
  have := q40b_interp_gamma ℱ hT hM hsb hX hG hMem
  have h0 : 0 ≤ hessSup Φ.1 := Real.iSup_nonneg fun _ => norm_nonneg _
  calc _ ≤ (1 / 2) * hessSup Φ.1 * covDiscrepancyMatrix P T Sg sb := this
    _ ≤ (1 / 2) * covDiscrepancyMatrix P T Sg sb := by
      have := mul_le_mul_of_nonneg_right hhs hcd
      nlinarith


end Interp

section Master

variable {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {p : ℕ}

theorem q40b_master_gamma (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (hN : 2 ≤ N) [NeZero N] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hsol : ∀ T : ℝ, 0 ≤ T → IsStrongSolution P htr.dyn T X₀ W X)
    (hfilt : IsFilteredSolution P ℱ W' W X) {H₁ : ℝ} (hH₁ : 0 ≤ H₁)
    (hentQ : ∀ r : ℝ, 0 ≤ r → relEntropy (P.map (X r.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r))) ≤ ENNReal.ofReal H₁)
    (hentP : ∀ r : ℝ, 0 ≤ r → relEntropy (P.map (X r.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≤ ENNReal.ofReal H₁)
    (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) (Ca : Fin p → ℝ) (m : ℝ) (hC0 : ∀ a, 0 ≤ Ca a) (hm : 0 < m)
    (hclass : ∀ a, ∀ τ : ℝ, 0 ≤ τ → ∃ F : ℝ → Torus d → ℝ,
      IsClassicalAdjointSolution htr.dyn ρ τ (φ a) F ∧
        ∀ r ∈ Set.Icc 0 τ, propagator htr.dyn ρ r τ (φ a) = F r)
    (hgrad : ∀ a, ∀ τ : ℝ, 0 ≤ τ → ∀ r ∈ Set.Icc 0 τ, ∀ x,
      ‖Torus.grad (propagator htr.dyn ρ r τ (φ a)) x‖ ≤ Ca a * Real.exp (-m * (τ - r)))
    (γ : Measure (ℝ^p)) [IsProbabilityMeasure γ]
    (hG : γ = multivariateGaussian 0 (noiseCovMatrix htr.dyn ρ β⁻¹ t φ)) :
    ENNReal.ofReal (smoothDist 2
        (law P fun ω => (WithLp.toLp 2 fun a => zetaStat P X (t a) (φ a) ω : ℝ^p))
        (((P.map fun ω => (WithLp.toLp 2 fun a =>
          zetaStat P X 0 (propagator htr.dyn ρ 0 (t a) (φ a)) ω : ℝ^p)).prod γ).map
            fun r => r.1 + r.2)) ≤
      ∑ a, ∫⁻ ω, ENNReal.ofReal |integratedRemainder htr.dyn ρ P X (t a) (φ a) ω| ∂P +
        ENNReal.ofReal ((1 / 2) * (∑ a, ∑ b, 2 * β⁻¹ * Ca a * Ca b / (2 * m)) *
          Real.sqrt (2 * (H₁ + Real.log 2) / N)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  choose F hFcl hFp using fun a => hclass a (t a) (ht a)
  set T0 : ℝ := ∑ a, t a with hT0
  have hT0nn : 0 ≤ T0 := Finset.sum_nonneg fun a _ => ht a
  have htT : ∀ a, t a ≤ T0 := fun a =>
    Finset.single_le_sum (f := t) (fun a _ => ht a) (Finset.mem_univ a)
  set D := htr.dyn with hDdef
  have hXm : ∀ r : ℝ≥0, Measurable (X r) := fun r => (hfilt.adapted r).mono (ℱ.le _) le_rfl
  -- progressive integrands
  have hΨ : ∀ a, IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D (t a) (F a) X) := fun a =>
    isProgressiveL2_empiricalNoiseIntegrand hfilt.progressive (ht a) (hFcl a).isC12Test
  have hΦ : ∀ a, IsProgressiveL2 P ℱ (qPhi D t F X a) := fun a => (hΨ a).smul (Real.sqrt N)
  have hvec := vectorItoIntegral_isVectorMartingaleWithCovariation hfilt.brownian (qPhi D t F X) hΦ T0
  -- the bracket data
  obtain ⟨c₀, hc₀, Λ, hΛ⟩ := q40b_rho_bounds hd1 htr
  have hBr : Br D ρ t F (fun a r x => -(backwardGenerator D (ρ r) (F a r) x)) Ca m :=
    { t0 := ht
      hF := fun a => (hFcl a).isC12Test
      hC0 := hC0
      hm := hm
      grad := fun a σ hσ x => by
        rw [← hFp a σ hσ]; exact hgrad a (t a) (ht a) σ hσ x
      rhoJ := fun T => q40b_jointCont hd1 htr T
      rhoP := fun σ hσ => (hΛ σ hσ).1
      rhoC := fun σ hσ => PDE.MFLinear.continuous_of_isSmooth (hΛ σ hσ).2.1 }
  have hsb := q40b_isDet hBr T0
  have hGlaw : γ = multivariateGaussian 0 (integratedCov T0 (qsb D ρ t F)) := by
    rw [hG, q40b_integratedCov D ρ t F htT hFp]
    rfl
  -- the initial statistic `ζ_N^∘` as a function of `X 0`
  set ψ : Fin p → Torus d → ℝ := fun a => propagator D ρ 0 (t a) (φ a) with hψdef
  have hψc : ∀ a, Continuous (ψ a) := by
    intro a
    have h1 : ψ a = F a 0 := hFp a 0 ⟨le_rfl, ht a⟩
    rw [h1]
    exact PDE.MFAux.continuous_of_isCk (PDE.ClassicalAux.isCk_of_le (by norm_num)
      ((hFcl a).c2 0 ⟨le_rfl, ht a⟩))
  set Zf : Config d N → (ℝ^p) := fun x => WithLp.toLp 2 fun a => Real.sqrt N *
    ((1 / (N : ℝ)) * ∑ i, ψ a (x i) - pair (meanEmpirical (P.map (X 0))) (ψ a)) with hZf
  have hZfm : Measurable Zf := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
    refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
    exact Finset.measurable_sum _ fun i _ => (hψc a).measurable.comp (measurable_pi_apply i)
  have hZeq : (fun ω => (WithLp.toLp 2 fun a => zetaStat P X 0 (ψ a) ω : ℝ^p)) = fun ω => Zf (X 0 ω) := by
    funext ω
    simp only [hZf, zetaStat, Real.toNNReal_zero]
  have hZmeas : Measurable[ℱ 0] (fun ω => Zf (X 0 ω)) :=
    @Measurable.comp Ω (Config d N) (ℝ^p) (ℱ 0) _ _ Zf (X 0) hZfm (hfilt.adapted 0)
  -- the a.s. identity, componentwise
  set Mv := vectorItoIntegral P ℱ W' (qPhi D t F X) with hMv
  set R : Fin p → Ω → ℝ := fun a ω => integratedRemainder D ρ P X (t a) (φ a) ω with hR
  have hid : ∀ a, ∀ᵐ ω ∂P, zetaStat P X (t a) (φ a) ω = zetaStat P X 0 (ψ a) ω +
      Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω - R a ω :=
    fun a => q40b_ae_identity hd htr hN hsol hfilt (ht a) (hφ a) (hFcl a) (hFp a)
      (fun r hr => hentQ r hr.1)
  have hstop : ∀ a, ∀ᵐ ω ∂P, itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) T0 ω =
      itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω := by
    intro a
    refine q40b_ito_stop hfilt.brownian (hΨ a) (ht a) (htT a) fun s' ω k hs => ?_
    unfold empiricalNoiseIntegrand
    have : s' ∉ Set.Icc 0 (t a) := fun h => absurd h.2 (not_le.2 hs)
    simp [this]
  have hsm : ∀ a, ∀ᵐ ω ∂P, ∀ τ : ℝ, itoIntegral P ℱ W' (qPhi D t F X a) τ ω =
      Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) τ ω :=
    fun a => itoIntegral_smul hfilt.brownian (hΨ a) (Real.sqrt N)
  have hAE : ∀ᵐ ω ∂P, ∀ a, zetaStat P X (t a) (φ a) ω = zetaStat P X 0 (ψ a) ω + Mv T0 ω a - R a ω := by
    have h1 := ae_all_iff.2 hid
    have h2 := ae_all_iff.2 hstop
    have h3 := ae_all_iff.2 hsm
    filter_upwards [h1, h2, h3] with ω a1 a2 a3 a
    rw [a1 a]
    have : Mv T0 ω a = Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω := by
      show itoIntegral P ℱ W' (qPhi D t F X a) T0 ω = _
      rw [a3 a T0, a2 a]
    rw [this]
  -- measurability of the statistics
  have hζm : ∀ (τ : ℝ) (ψ' : Torus d → ℝ), Continuous ψ' →
      Measurable (fun ω => zetaStat P X τ ψ' ω) := by
    intro τ ψ' hψ'
    unfold zetaStat
    refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
    exact Finset.measurable_sum _ fun i _ => hψ'.measurable.comp ((measurable_pi_apply i).comp (hXm _))
  have hφc : ∀ a, Continuous (φ a) := fun a => PDE.MFLinear.continuous_of_isSmooth (hφ a)
  have hMvm : AEMeasurable (Mv T0) P :=
    (hvec.sq_int T0 ⟨hT0nn, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hAm : Measurable (fun ω => (WithLp.toLp 2 fun a => zetaStat P X (t a) (φ a) ω : ℝ^p)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => hζm (t a) (φ a) (hφc a))
  have hZvm : Measurable (fun ω => Zf (X 0 ω)) := hZfm.comp (hXm 0)
  have hBm : AEMeasurable (fun ω => Zf (X 0 ω) + Mv T0 ω) P := hZvm.aemeasurable.add hMvm
  rw [hZeq]
  -- the remainder is a.e. a measurable function
  have hRm : ∀ a, AEMeasurable (fun ω => ENNReal.ofReal |R a ω|) P := by
    intro a
    have hIm : Measurable (fun ω => itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω) :=
      (adapted_itoIntegral P ℱ W' _ (t a)).mono (ℱ.le _) le_rfl
    have hGm' : Measurable (fun ω => zetaStat P X 0 (ψ a) ω +
        Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω -
        zetaStat P X (t a) (φ a) ω) :=
      ((hζm 0 (ψ a) (hψc a)).add (measurable_const.mul hIm)).sub (hζm (t a) (φ a) (hφc a))
    have hmeasR : AEMeasurable (R a) P :=
      hGm'.aemeasurable.congr ((hid a).mono fun ω h => by beta_reduce; linarith [h])
    exact ENNReal.measurable_ofReal.comp_aemeasurable hmeasR.abs
  -- the two steps of the comparison
  set Avec : Ω → (ℝ^p) := fun ω => (WithLp.toLp 2 fun a => zetaStat P X (t a) (φ a) ω : ℝ^p) with hAvec
  set Bvec : Ω → (ℝ^p) := fun ω => Zf (X 0 ω) + Mv T0 ω with hBvec
  set Cm : Measure (ℝ^p) := ((P.map fun ω => Zf (X 0 ω)).prod γ).map fun r => r.1 + r.2 with hCm
  haveI : IsProbabilityMeasure (P.map fun ω => Zf (X 0 ω)) := inferInstance
  haveI : IsProbabilityMeasure Cm := inferInstance
  have hstep1 : ENNReal.ofReal (smoothDist 2 (law P Avec) (law P Bvec)) ≤
      ∑ a, ∫⁻ ω, ENNReal.ofReal |R a ω| ∂P := by
    refine (q40b_smoothDist_perturb hAm.aemeasurable hBm).trans ?_
    calc ∫⁻ ω, ‖Avec ω - Bvec ω‖ₑ ∂P ≤ ∫⁻ ω, ∑ a, ENNReal.ofReal |R a ω| ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hAE] with ω hω
          have hcomp : ∀ a, (Avec ω - Bvec ω) a = -(R a ω) := by
            intro a
            simp only [hAvec, hBvec, PiLp.sub_apply, PiLp.add_apply]
            have := hω a
            have hZ := congrFun hZeq ω
            have hZa := congrArg (fun v : ℝ^p => v a) hZ
            simp only [hψdef] at hZa
            rw [this, ← hZa]
            ring
          rw [← ofReal_norm_eq_enorm]
          have hn : ‖Avec ω - Bvec ω‖ ≤ ∑ a, |R a ω| := by
            refine (PDE.MFLinear.norm_euclid_le_sum _).trans (le_of_eq ?_)
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hcomp a, abs_neg]
          calc ENNReal.ofReal ‖Avec ω - Bvec ω‖ ≤ ENNReal.ofReal (∑ a, |R a ω|) :=
                ENNReal.ofReal_le_ofReal hn
            _ = ∑ a, ENNReal.ofReal |R a ω| :=
                ENNReal.ofReal_sum_of_nonneg fun a _ => abs_nonneg _
      _ = ∑ a, ∫⁻ ω, ENNReal.ofReal |R a ω| ∂P := lintegral_finset_sum' _ fun a _ => hRm a
  have hstep2 : smoothDist 2 (law P Bvec) Cm ≤
      (1 / 2) * (∑ a, ∑ b, 2 * β⁻¹ * Ca a * Ca b / (2 * m)) *
        Real.sqrt (2 * (H₁ + Real.log 2) / N) := by
    have h1 := q40b_smoothDist_interp_gamma ℱ hT0nn hvec hsb hZmeas hGlaw
    have h2 := q40b_cov_bound hBr hN0 hXm hvec.sigma_meas hH₁ hentP hT0nn htT
    calc smoothDist 2 (law P Bvec) Cm ≤ (1 / 2) * covDiscrepancyMatrix P T0
          (covMatrixProcess (qPhi D t F X)) (qsb D ρ t F) := h1
      _ ≤ (1 / 2) * ((∑ a, ∑ b, 2 * D.invβ * Ca a * Ca b / (2 * m)) *
          Real.sqrt (2 * (H₁ + Real.log 2) / N)) := by gcongr
      _ = _ := by rw [← mul_assoc]; rfl
  have htri := smoothDist_triangle 2 (law P Avec) (law P Bvec) Cm
  calc ENNReal.ofReal (smoothDist 2 (law P Avec) Cm)
      ≤ ENNReal.ofReal (smoothDist 2 (law P Avec) (law P Bvec) + smoothDist 2 (law P Bvec) Cm) :=
        ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal (smoothDist 2 (law P Avec) (law P Bvec)) +
        ENNReal.ofReal (smoothDist 2 (law P Bvec) Cm) :=
        ENNReal.ofReal_add (smoothDist_nonneg _ _ _) (smoothDist_nonneg _ _ _)
    _ ≤ _ := add_le_add hstep1 (ENNReal.ofReal_le_ofReal hstep2)

end Master

end HRS.Q40b
