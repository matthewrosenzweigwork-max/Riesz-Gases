import HRS.Prob.HilbertMartingale
import HRS.Stochastic.QuadraticVariation

/-!
# Packet Q40b, part 4: conditional Gaussian interpolation with a Gaussian independent of `X` only

`q40b_smoothDist_interp`: `𝖽_{C²}(law(X + M_T), law(X + G)) ≤ ½ E ∫_0^T ‖Σ_r - Σ̄_r‖_{S₁} dr` for an
`ℱ_0`-measurable `X` and a Gaussian `G` that is merely independent of `X` (Lemma A.27 needs
independence of `ℱ_T`; we enlarge the probability space to `Ω × ℝ^p`, with the pulled-back
filtration, `comapFil`, and use that only the joint law of `(X, G)` enters).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

section Transfer

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}

/-- The pull-back filtration `(ℱ_t).comap π`. -/
def comapFil (ℱ : Filtration ℝ mΩ) {π : Ω' → Ω} (hπ : Measurable π) : Filtration ℝ mΩ' where
  seq t := (ℱ t).comap π
  mono' := fun s t hst => MeasurableSpace.comap_mono (ℱ.mono hst)
  le' := fun t => (MeasurableSpace.comap_mono (ℱ.le t)).trans hπ.comap_le

theorem martingale_comapFil {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω}
    (hπ : MeasurePreserving π P' P) {ℱ : Filtration ℝ mΩ} {f : ℝ → Ω → ℝ}
    (hf : Martingale f ℱ P) [IsFiniteMeasure P] [IsFiniteMeasure P'] :
    Martingale (fun τ ω' => f τ (π ω')) (comapFil ℱ hπ.measurable) P' := by
  have hmap := hπ.map_eq
  have hsm : ∀ (g : Ω → ℝ) (B : Set Ω), MeasurableSet B → AEStronglyMeasurable g P →
      ∫ ω' in π ⁻¹' B, g (π ω') ∂P' = ∫ ω in B, g ω ∂P := by
    intro g B hB hg
    have := setIntegral_map (μ := P') (g := π) (f := g) hB (by rw [hmap]; exact hg) hπ.aemeasurable
    rw [hmap] at this
    exact this.symm
  refine ⟨fun t => ?_, fun i j hij => ?_⟩
  · exact (hf.1 t).comp_measurable (comap_measurable π)
  · symm
    refine ae_eq_condExp_of_forall_setIntegral_eq ((comapFil ℱ hπ.measurable).le i) ?_ ?_ ?_ ?_
    · exact hπ.integrable_comp_of_integrable (hf.integrable j)
    · intro A _ _
      exact (hπ.integrable_comp_of_integrable (hf.integrable i)).integrableOn
    · intro A hA _
      obtain ⟨B, hB, rfl⟩ := hA
      have hBm : MeasurableSet B := ℱ.le i _ hB
      rw [hsm (f j) B hBm (hf.integrable j).aestronglyMeasurable,
        hsm (f i) B hBm (hf.integrable i).aestronglyMeasurable]
      exact hf.setIntegral_eq hij hB
    · exact ((hf.1 i).comp_measurable (comap_measurable π)).aestronglyMeasurable


variable {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω} {p : ℕ}

theorem isVecMart_comapFil [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hπ : MeasurePreserving π P' P) {ℱ : Filtration ℝ mΩ} {T : ℝ} {M : ℝ → Ω → (ℝ^p)}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg) :
    IsVectorMartingaleWithCovariation P' (comapFil ℱ hπ.measurable) T (fun τ ω' => M τ (π ω'))
      (fun σ ω' => Sg σ (π ω')) where
  martingale a := martingale_comapFil hπ (hM.martingale a)
  zero := hπ.quasiMeasurePreserving.ae hM.zero
  cont := hπ.quasiMeasurePreserving.ae hM.cont
  sq_int τ hτ := (hM.sq_int τ hτ).comp_measurePreserving hπ
  sigma_meas := hM.sigma_meas.comp (measurable_fst.prodMk (hπ.measurable.comp measurable_snd))
  sigma_adapted σ := @Measurable.comp Ω' Ω (Matrix (Fin p) (Fin p) ℝ) ((ℱ σ).comap π) (ℱ σ) _ (Sg σ) π (hM.sigma_adapted σ) (comap_measurable π)
  sigma_psd := hπ.quasiMeasurePreserving.ae hM.sigma_psd
  sigma_int := hπ.integrable_comp_of_integrable hM.sigma_int
  sigma_pathint := hπ.quasiMeasurePreserving.ae hM.sigma_pathint
  sigma_entry_int := hπ.quasiMeasurePreserving.ae hM.sigma_entry_int
  covariation a b := by
    have := martingale_comapFil hπ (hM.covariation a b)
    exact this

end Transfer


section Interp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {p : ℕ}

/-- Conditional Gaussian interpolation for a Gaussian `G` that is only independent of the
`ℱ_0`-measurable shift `X` (not of the whole filtration): enlarge the space to `Ω × ℝ^p`. -/
theorem q40b_interp [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) {T : ℝ} (hT : 0 ≤ T)
    {M : ℝ → Ω → (ℝ^p)} {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ}
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsb : IsDetCovMatrix T sb)
    {X : Ω → (ℝ^p)} (hX : Measurable[ℱ 0] X) {G : Ω → (ℝ^p)} (hGm : Measurable G)
    (hG : law P G = multivariateGaussian 0 (integratedCov T sb))
    (hind : IndepFun X G P) {h : (ℝ^p) → ℝ} (hh : MemCb 2 h) :
    |(∫ ω, h (X ω + M T ω) ∂P) - ∫ ω, h (X ω + G ω) ∂P| ≤
      (1 / 2) * hessSup h * covDiscrepancyMatrix P T Sg sb := by
  classical
  set γ : Measure (ℝ^p) := law P G with hγ
  haveI : IsProbabilityMeasure γ := show IsProbabilityMeasure (P.map G) from inferInstance
  set P' : Measure (Ω × (ℝ^p)) := P.prod γ with hP'
  have hπ : MeasurePreserving (Prod.fst : Ω × (ℝ^p) → Ω) P' P := measurePreserving_fst
  have hπ2 : MeasurePreserving (Prod.snd : Ω × (ℝ^p) → ℝ^p) P' γ := measurePreserving_snd
  set ℱ' := comapFil ℱ hπ.measurable with hℱ'
  have hM' := isVecMart_comapFil hπ hM
  have hX' : Measurable[ℱ' 0] (fun q : Ω × (ℝ^p) => X q.1) :=
    @Measurable.comp (Ω × (ℝ^p)) Ω (ℝ^p) ((ℱ 0).comap Prod.fst) (ℱ 0) _ X Prod.fst hX
      (comap_measurable Prod.fst)
  have hG' : law P' (Prod.snd : Ω × (ℝ^p) → ℝ^p) = multivariateGaussian 0 (integratedCov T sb) := by
    rw [← hG]; exact hπ2.map_eq
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
  have e2 : ∫ q, h (X q.1 + q.2) ∂P' = ∫ ω, h (X ω + G ω) ∂P := by
    have hXm0 : Measurable X := hX.mono (ℱ.le 0) le_rfl
    have hadd : Measurable (fun r : (ℝ^p) × (ℝ^p) => r.1 + r.2) := measurable_fst.add measurable_snd
    have hjoint : P.map (fun ω => (X ω, G ω)) = (P.map X).prod γ :=
      (indepFun_iff_map_prod_eq_prod_map_map hXm0.aemeasurable hGm.aemeasurable).1 hind
    have hL : P.map (fun ω => X ω + G ω) = ((P.map X).prod γ).map (fun r => r.1 + r.2) := by
      rw [← hjoint, Measure.map_map hadd (hXm0.prodMk hGm)]
      rfl
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
      _ = ∫ y, h y ∂(P.map (fun ω => X ω + G ω)) := by rw [hR, hL]
      _ = ∫ ω, h (X ω + G ω) ∂P :=
          integral_map (φ := fun ω => X ω + G ω) (hXm0.add hGm).aemeasurable
            hh.1.continuous.aestronglyMeasurable
  rw [e1, e2, e3] at s2
  exact s2


/-- The `C²`-smooth distance version. -/
theorem q40b_smoothDist_interp [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) {T : ℝ} (hT : 0 ≤ T)
    {M : ℝ → Ω → (ℝ^p)} {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ}
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsb : IsDetCovMatrix T sb)
    {X : Ω → (ℝ^p)} (hX : Measurable[ℱ 0] X) {G : Ω → (ℝ^p)} (hGm : Measurable G)
    (hG : law P G = multivariateGaussian 0 (integratedCov T sb))
    (hind : IndepFun X G P) :
    smoothDist 2 (law P fun ω => X ω + M T ω) (law P fun ω => X ω + G ω) ≤
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
  have e2 : ∫ z, Φ.1 z ∂(law P fun ω => X ω + G ω) = ∫ ω, Φ.1 (X ω + G ω) ∂P :=
    integral_map (hXm0.add hGm).aemeasurable hΦ.continuous.aestronglyMeasurable
  rw [e1, e2]
  have := q40b_interp ℱ hT hM hsb hX hGm hG hind hMem
  have h0 : 0 ≤ hessSup Φ.1 := Real.iSup_nonneg fun _ => norm_nonneg _
  calc _ ≤ (1 / 2) * hessSup Φ.1 * covDiscrepancyMatrix P T Sg sb := this
    _ ≤ (1 / 2) * covDiscrepancyMatrix P T Sg sb := by
      have := mul_le_mul_of_nonneg_right hhs hcd
      nlinarith

end Interp

end HRS.Q40b
