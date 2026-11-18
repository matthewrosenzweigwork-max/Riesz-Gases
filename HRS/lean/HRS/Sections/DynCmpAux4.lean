import HRS.Prob.HilbertMartingale

/-!
# DYNCMP: Theorem 5.4 `dynamic_comparison`, step (4a): the enlargement and the Gaussian comparison with remainder

The statement of `dynamic_comparison` gives the Gaussian vector `G` only independent of the initial configuration, while
`conditional_gaussian_interpolation` needs `G` independent of `ℱ_T`.  Since only laws enter, we pass to the enlargement
`Ω × ℝ^p`, `P' = P ⊗ Law G`, with the pulled-back filtration `dyncmp_fil` (`ℱ'_t = π⁻¹ ℱ_t`), `G'(ω,y) = y`:

* `dyncmp_martingale_comp_fst`, `dyncmp_vec_comp_fst`: martingales and `IsVectorMartingaleWithCovariation` pull back;
* `dyncmp_indep_snd_fil`: `σ(G') ⟂ ℱ'_T`;  `dyncmp_law_add`: `Law_{P'}(A∘π + G') = Law_P(A + G)` when `A ⟂ G`;
* `dyncmp_gaussian_comparison`: `d_{C²}(Law(A + M_T + R), Law(A + G)) ≤ E‖R‖ + ½ E∫‖Σ_r - Σ̄_r‖_{S_1} dr`
  (`N:eq:conditional-gaussian` and the removal of the remainder by the gradient bound).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS


section Enlarge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {E : Type*} {mE : MeasurableSpace E}

/-- The pulled-back filtration on the enlargement `Ω × E`. -/
def dyncmp_fil (ℱ : Filtration ℝ mΩ) : Filtration ℝ (mΩ.prod mE) where
  seq t := (ℱ t).comap Prod.fst
  mono' := fun s t h => MeasurableSpace.comap_mono (ℱ.mono h)
  le' := fun t => by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := hA
    exact measurable_fst (ℱ.le t B hB)

lemma dyncmp_measurable_fst_fil (ℱ : Filtration ℝ mΩ) (t : ℝ) :
    Measurable[(dyncmp_fil (mE := mE) ℱ) t, ℱ t] (Prod.fst : Ω × E → Ω) :=
  comap_measurable Prod.fst


section Transport

variable (P : Measure Ω) [IsProbabilityMeasure P] (γ : Measure E) [IsProbabilityMeasure γ]

lemma dyncmp_setIntegral_comp_fst {B : Set Ω} (hB : MeasurableSet B) {F : Ω → ℝ}
    (hF : AEStronglyMeasurable F P) :
    ∫ w in Prod.fst ⁻¹' B, F w.1 ∂(P.prod γ) = ∫ ω in B, F ω ∂P := by
  have hπ : MeasurePreserving (Prod.fst : Ω × E → Ω) (P.prod γ) P := measurePreserving_fst
  have h : ∫ y in B, F y ∂(Measure.map Prod.fst (P.prod γ)) = ∫ x in Prod.fst ⁻¹' B, F x.1 ∂(P.prod γ) :=
    setIntegral_map hB (by rw [hπ.map_eq]; exact hF) measurable_fst.aemeasurable
  rw [hπ.map_eq] at h
  exact h.symm

lemma dyncmp_integral_comp_fst {F : Ω → ℝ} (hF : AEStronglyMeasurable F P) :
    ∫ w, F w.1 ∂(P.prod γ) = ∫ ω, F ω ∂P := by
  have hπ : MeasurePreserving (Prod.fst : Ω × E → Ω) (P.prod γ) P := measurePreserving_fst
  have h : ∫ y, F y ∂(Measure.map Prod.fst (P.prod γ)) = ∫ x, F x.1 ∂(P.prod γ) :=
    integral_map measurable_fst.aemeasurable (by rw [hπ.map_eq]; exact hF)
  rw [hπ.map_eq] at h
  exact h.symm

lemma dyncmp_condExp_comp_fst (ℱ : Filtration ℝ mΩ) (s : ℝ) {f : Ω → ℝ} (hf : Integrable f P) :
    (P.prod γ)[fun w : Ω × E => f w.1 | (dyncmp_fil (mE := mE) ℱ) s] =ᵐ[P.prod γ]
      fun w => (P[f | ℱ s]) w.1 := by
  have hπ : MeasurePreserving (Prod.fst : Ω × E → Ω) (P.prod γ) P := measurePreserving_fst
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq ((dyncmp_fil ℱ).le s) (hπ.integrable_comp_of_integrable hf) ?_ ?_ ?_
  · intro A _ _
    exact (hπ.integrable_comp_of_integrable integrable_condExp).integrableOn
  · intro A hA _
    obtain ⟨B, hB, rfl⟩ := hA
    have hB' : MeasurableSet B := ℱ.le s B hB
    have h1 := dyncmp_setIntegral_comp_fst P γ hB' (F := P[f | ℱ s]) (stronglyMeasurable_condExp.mono (ℱ.le s)).aestronglyMeasurable
    have h2 := dyncmp_setIntegral_comp_fst P γ hB' (F := f) hf.aestronglyMeasurable
    rw [h1, h2]
    exact setIntegral_condExp (ℱ.le s) hf hB
  · exact (stronglyMeasurable_condExp.comp_measurable (dyncmp_measurable_fst_fil ℱ s)).aestronglyMeasurable


lemma dyncmp_martingale_comp_fst {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → ℝ} (hM : Martingale M ℱ P) :
    Martingale (fun τ (w : Ω × E) => M τ w.1) (dyncmp_fil (mE := mE) ℱ) (P.prod γ) := by
  have hπ : MeasurePreserving (Prod.fst : Ω × E → Ω) (P.prod γ) P := measurePreserving_fst
  refine ⟨fun τ => (hM.1 τ).comp_measurable (dyncmp_measurable_fst_fil ℱ τ), fun i j hij => ?_⟩
  exact (dyncmp_condExp_comp_fst P γ ℱ i (hM.integrable j)).trans
    (hπ.quasiMeasurePreserving.ae_eq_comp (hM.2 i j hij))

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

lemma dyncmp_vec_comp_fst {p : ℕ} {ℱ : Filtration ℝ mΩ} {T : ℝ} {M : ℝ → Ω → ℝ^p}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg) :
    IsVectorMartingaleWithCovariation (P.prod γ) (dyncmp_fil (mE := mE) ℱ) T
      (fun τ w => M τ w.1) (fun σ w => Sg σ w.1) := by
  have hπ : MeasurePreserving (Prod.fst : Ω × E → Ω) (P.prod γ) P := measurePreserving_fst
  have hq := hπ.quasiMeasurePreserving
  refine ⟨fun a => dyncmp_martingale_comp_fst P γ (hM.martingale a), hq.ae hM.zero, hq.ae hM.cont,
    fun τ hτ => (hM.sq_int τ hτ).comp_measurePreserving hπ, ?_, fun σ => ?_, hq.ae hM.sigma_psd,
    hπ.integrable_comp_of_integrable hM.sigma_int, hq.ae hM.sigma_pathint, hq.ae hM.sigma_entry_int,
    fun a b => dyncmp_martingale_comp_fst P γ (hM.covariation a b)⟩
  · exact hM.sigma_meas.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  · exact (hM.sigma_adapted σ).comp (dyncmp_measurable_fst_fil ℱ σ)

end Transport


lemma dyncmp_indep_snd_fil (P : Measure Ω) [IsProbabilityMeasure P] (γ : Measure E) [IsProbabilityMeasure γ]
    {F : Type*} [MeasurableSpace F] {g : E → F} (hg : Measurable g)
    (ℱ : Filtration ℝ mΩ) (T : ℝ) :
    Indep (MeasurableSpace.comap (fun w : Ω × E => g w.2) inferInstance) ((dyncmp_fil (mE := mE) ℱ) T)
      (P.prod γ) := by
  rw [Indep_iff]
  intro t1 t2 h1 h2
  obtain ⟨B, hB, rfl⟩ := h1
  obtain ⟨A, hA, rfl⟩ := h2
  have hA' : MeasurableSet A := ℱ.le T A hA
  have hB' : MeasurableSet ((fun x : E => g x) ⁻¹' B) := hg hB
  have e1 : (fun w : Ω × E => g w.2) ⁻¹' B = Set.univ ×ˢ ((fun x : E => g x) ⁻¹' B) := by
    ext w; simp
  have e2 : (Prod.fst : Ω × E → Ω) ⁻¹' A = A ×ˢ Set.univ := by ext w; simp
  have e3 : (Set.univ ×ˢ ((fun x : E => g x) ⁻¹' B)) ∩ (A ×ˢ Set.univ) =
      A ×ˢ ((fun x : E => g x) ⁻¹' B) := by ext w; simp [and_comm]
  rw [e1, e2, e3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  simp [mul_comm]

lemma dyncmp_law_add {p : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] {A G : Ω → EuclideanSpace ℝ (Fin p)}
    (hA : Measurable A) (hG : AEMeasurable G P) (hind : IndepFun A G P) :
    (P.prod (P.map G)).map (fun w : Ω × EuclideanSpace ℝ (Fin p) => A w.1 + w.2) =
      P.map (fun ω => A ω + G ω) := by
  have hadd : Measurable (fun q : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) => q.1 + q.2) :=
    measurable_fst.add measurable_snd
  have h1 : P.map (fun ω => A ω + G ω) = (P.map (fun ω => (A ω, G ω))).map (fun q => q.1 + q.2) := by
    rw [AEMeasurable.map_map_of_aemeasurable hadd.aemeasurable (hA.aemeasurable.prodMk hG)]; rfl
  have h2 : (P.prod (P.map G)).map (fun w : Ω × EuclideanSpace ℝ (Fin p) => A w.1 + w.2) =
      ((P.map A).prod (P.map G)).map (fun q => q.1 + q.2) := by
    have := Measure.map_prod_map (μa := P) (μc := P.map G) (f := A) (g := id) hA measurable_id
    rw [Measure.map_id] at this
    rw [this, Measure.map_map hadd (hA.prodMap measurable_id)]
    rfl
  rw [h1, h2, hind.map_prod_eq_prod_map_map hA.aemeasurable hG]


section Compare

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

lemma dyncmp_cbUnit_facts {p : ℕ} {h : (ℝ^p) → ℝ} (hh : h ∈ CbUnitBall (ℝ^p) 2) :
    MemCb 2 h ∧ hessSup h ≤ 1 ∧ ∀ x y : ℝ^p, |h y - h x| ≤ ‖y - x‖ := by
  obtain ⟨hC, hb, hn⟩ := hh
  have hnn : ∀ j : ℕ, 0 ≤ ⨆ z : ℝ^p, ‖iteratedFDeriv ℝ j h z‖ := fun j =>
    Real.iSup_nonneg fun z => norm_nonneg _
  have hsum : cbNorm 2 h = (⨆ z : ℝ^p, ‖iteratedFDeriv ℝ 0 h z‖) + (⨆ z : ℝ^p, ‖iteratedFDeriv ℝ 1 h z‖) +
      (⨆ z : ℝ^p, ‖iteratedFDeriv ℝ 2 h z‖) := by
    unfold cbNorm
    simp [Finset.sum_range_succ]
  have h1 : (⨆ z : ℝ^p, ‖iteratedFDeriv ℝ 1 h z‖) ≤ 1 := by
    have := hnn 0; have := hnn 2; linarith
  have h2 : hessSup h ≤ 1 := by
    have := hnn 0; have := hnn 1
    show (⨆ z : ℝ^p, ‖iteratedFDeriv ℝ 2 h z‖) ≤ 1
    linarith
  refine ⟨⟨hC, hb⟩, h2, fun x y => ?_⟩
  have hd : Differentiable ℝ h := hC.differentiable (by norm_num)
  have hf1 : ∀ z, ‖fderiv ℝ h z‖ ≤ 1 := fun z => by
    rw [← norm_iteratedFDeriv_one]
    exact (le_ciSup (hb 1 (by norm_num)) z).trans h1
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := h) (s := Set.univ)
    (fun z _ => hd z) (fun z _ => hf1 z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa using this


/-- **The Gaussian comparison with remainder** (the conclusion of `N:eq:conditional-gaussian` + removal of the
remainder `R`): in `smoothDist 2`, `Law(A + M_T + R)` and `Law(A + G)` are within
`E‖R‖ + ½ E∫‖Σ_r - Σ̄_r‖_{S_1} dr`.  `G` is only assumed independent of `A` (not of `ℱ_T`): the
proof runs on the enlargement `Ω × ℝ^p` with the pulled-back filtration. -/
theorem dyncmp_gaussian_comparison {Ω : Type*} {mΩ : MeasurableSpace Ω} {p : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) {T : ℝ} (hT : 0 ≤ T)
    {M : ℝ → Ω → ℝ^p} {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ}
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsb : IsDetCovMatrix T sb)
    {A : Ω → ℝ^p} (hA : Measurable[ℱ 0] A) {G : Ω → ℝ^p} (hGm : AEMeasurable G P)
    (hG : law P G = multivariateGaussian 0 (integratedCov T sb)) (hind : IndepFun A G P)
    {ℓ R : Ω → ℝ^p} (hR : Integrable R P) (hℓ : ℓ =ᵐ[P] fun ω => A ω + M T ω + R ω) :
    smoothDist 2 (law P ℓ) (law P fun ω => A ω + G ω) ≤
      ∫ ω, ‖R ω‖ ∂P + (1 / 2) * covDiscrepancyMatrix P T Sg sb := by
  have hAm : Measurable A := hA.mono (ℱ.le 0) le_rfl
  have hMt : AEMeasurable (M T) P := (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hRm : AEMeasurable R P := hR.aestronglyMeasurable.aemeasurable
  have hℓm : AEMeasurable ℓ P := ((hAm.aemeasurable.add hMt).add hRm).congr hℓ.symm
  set g : Ω → ℝ := fun ω => ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ) with hg
  have hintg : Integrable g P := LindebergAux.Iblk_integrable P ℱ hM hsb.meas hsb.int le_rfl le_rfl
  have hg0 : 0 ≤ ∫ ω, g ω ∂P :=
    integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
  have hRn : 0 ≤ ∫ ω, ‖R ω‖ ∂P := integral_nonneg fun ω => norm_nonneg _
  -- the enlargement
  set γ : Measure (ℝ^p) := P.map G with hγ
  haveI : IsProbabilityMeasure γ := (Measure.isProbabilityMeasure_map_iff hGm).2 inferInstance
  have hπ : MeasurePreserving (Prod.fst : Ω × (ℝ^p) → Ω) (P.prod γ) P := measurePreserving_fst
  have hM' := dyncmp_vec_comp_fst P γ hM
  have hX' : Measurable[(dyncmp_fil (mE := (inferInstance : MeasurableSpace (ℝ^p))) ℱ) 0]
      (fun w : Ω × (ℝ^p) => A w.1) := hA.comp (dyncmp_measurable_fst_fil ℱ 0)
  have hG' : law (P.prod γ) (fun w : Ω × (ℝ^p) => w.2) = multivariateGaussian 0 (integratedCov T sb) := by
    show (P.prod γ).map Prod.snd = _
    rw [Measure.map_snd_prod]; simp [← hG, hγ]
  have hGind' := dyncmp_indep_snd_fil (mE := (inferInstance : MeasurableSpace (ℝ^p))) P γ
    (g := fun x : ℝ^p => x) measurable_id ℱ T
  refine Real.iSup_le (fun ⟨h, hh⟩ => ?_) (add_nonneg hRn (by positivity))
  obtain ⟨hh2, hhess, hlip⟩ := dyncmp_cbUnit_facts hh
  have hcont : Continuous h := hh2.1.continuous
  -- integrals over the laws
  have e1 : ∫ x, h x ∂(law P ℓ) = ∫ ω, h (A ω + M T ω + R ω) ∂P := by
    rw [integral_map hℓm hcont.aestronglyMeasurable]
    exact integral_congr_ae (hℓ.mono fun ω hω => by simp [hω])
  have hlaw := dyncmp_law_add (p := p) P hAm hGm hind
  have e2 : ∫ x, h x ∂(law P fun ω => A ω + G ω) =
      ∫ w, h (A w.1 + w.2) ∂(P.prod γ) := by
    show ∫ x, h x ∂(P.map fun ω => A ω + G ω) = _
    rw [← hlaw]
    exact integral_map ((hAm.comp measurable_fst).add measurable_snd).aemeasurable hcont.aestronglyMeasurable
  have hi1 : Integrable (fun ω => h (A ω + M T ω + R ω)) P :=
    integrable_memCb_comp P hh2 ((hAm.aemeasurable.add hMt).add hRm)
  have hi0 : Integrable (fun ω => h (A ω + M T ω)) P := integrable_memCb_comp P hh2 (hAm.aemeasurable.add hMt)
  show |∫ x, h x ∂(law P ℓ) - ∫ x, h x ∂(law P fun ω => A ω + G ω)| ≤ _
  rw [e1, e2]
  -- step 1: removing `R`
  have s1 : |(∫ ω, h (A ω + M T ω + R ω) ∂P) - ∫ ω, h (A ω + M T ω) ∂P| ≤ ∫ ω, ‖R ω‖ ∂P := by
    rw [← integral_sub hi1 hi0, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hR.norm (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    simpa using hlip (A ω + M T ω) (A ω + M T ω + R ω)
  -- step 2: the conditional interpolation on the enlargement
  have hcond := conditional_gaussian_interpolation (P.prod γ) (dyncmp_fil ℱ) T hT (fun τ w => M τ w.1)
    (fun σ w => Sg σ w.1) hM' sb hsb (fun w => A w.1) hX' (fun w => w.2) measurable_snd.aemeasurable hG'
    hGind' h hh2
  have hm' : (dyncmp_fil (mE := (inferInstance : MeasurableSpace (ℝ^p))) ℱ) 0 ≤ mΩ.prod inferInstance :=
    (dyncmp_fil ℱ).le 0
  set P' : Measure (Ω × (ℝ^p)) := P.prod γ with hP'
  have hG'am : AEMeasurable (fun w : Ω × (ℝ^p) => A w.1 + w.2) P' :=
    ((hAm.comp measurable_fst).add measurable_snd).aemeasurable
  have hf1 : Integrable (fun w : Ω × (ℝ^p) => h (A w.1 + M T w.1)) P' :=
    hπ.integrable_comp_of_integrable (g := fun ω => h (A ω + M T ω)) hi0
  have hf2 : Integrable (fun w : Ω × (ℝ^p) => h (A w.1 + w.2)) P' := integrable_memCb_comp P' hh2 hG'am
  have hg' : Integrable (fun w : Ω × (ℝ^p) => g w.1) P' := hπ.integrable_comp_of_integrable (g := g) hintg
  have hUi := (integrable_condExp (μ := P') (m := (dyncmp_fil (mE := (inferInstance : MeasurableSpace (ℝ^p))) ℱ) 0)
    (f := fun w : Ω × (ℝ^p) => h (A w.1 + M T w.1)))
  have hVi := (integrable_condExp (μ := P') (m := (dyncmp_fil (mE := (inferInstance : MeasurableSpace (ℝ^p))) ℱ) 0)
    (f := fun w : Ω × (ℝ^p) => h (A w.1 + w.2)))
  have hWi := (integrable_condExp (μ := P') (m := (dyncmp_fil (mE := (inferInstance : MeasurableSpace (ℝ^p))) ℱ) 0)
    (f := fun w : Ω × (ℝ^p) => g w.1))
  have hE1 : ∫ w, h (A w.1 + M T w.1) ∂P' = ∫ ω, h (A ω + M T ω) ∂P :=
    dyncmp_integral_comp_fst P γ (F := fun ω => h (A ω + M T ω)) hi0.aestronglyMeasurable
  have hEg : ∫ w, g w.1 ∂P' = ∫ ω, g ω ∂P := dyncmp_integral_comp_fst P γ (F := g) hintg.aestronglyMeasurable
  -- the integrated conditional bound
  have hb : ∀ᵐ w ∂P', ‖(P'[fun w : Ω × (ℝ^p) => h (A w.1 + M T w.1) |
        (dyncmp_fil (mE := (inferInstance : MeasurableSpace (ℝ^p))) ℱ) 0]) w -
      (P'[fun w : Ω × (ℝ^p) => h (A w.1 + w.2) | (dyncmp_fil (mE := (inferInstance : MeasurableSpace (ℝ^p))) ℱ) 0]) w‖ ≤
      (1 / 2) * hessSup h * (P'[fun w : Ω × (ℝ^p) => g w.1 |
        (dyncmp_fil (mE := (inferInstance : MeasurableSpace (ℝ^p))) ℱ) 0]) w := by
    filter_upwards [hcond] with w hw
    simpa [Real.norm_eq_abs] using hw
  have s2' : |(∫ w, h (A w.1 + M T w.1) ∂P') - ∫ w, h (A w.1 + w.2) ∂P'| ≤ (1 / 2) * ∫ ω, g ω ∂P := by
    rw [← integral_condExp hm' (f := fun w : Ω × (ℝ^p) => h (A w.1 + M T w.1)),
      ← integral_condExp hm' (f := fun w : Ω × (ℝ^p) => h (A w.1 + w.2)), ← integral_sub hUi hVi,
      ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hWi.const_mul ((1 / 2) * hessSup h)) hb).trans ?_
    rw [integral_const_mul, integral_condExp hm', hEg]
    nlinarith
  have s2 : |(∫ ω, h (A ω + M T ω) ∂P) - ∫ w, h (A w.1 + w.2) ∂P'| ≤ (1 / 2) * ∫ ω, g ω ∂P := by
    rw [← hE1]; exact s2'
  have key : (∫ ω, h (A ω + M T ω + R ω) ∂P) - ∫ w, h (A w.1 + w.2) ∂P' =
      ((∫ ω, h (A ω + M T ω + R ω) ∂P) - ∫ ω, h (A ω + M T ω) ∂P) +
        ((∫ ω, h (A ω + M T ω) ∂P) - ∫ w, h (A w.1 + w.2) ∂P') := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  show _ ≤ ∫ ω, ‖R ω‖ ∂P + (1 / 2) * ∫ ω, g ω ∂P
  linarith

end Compare

end Enlarge
end HRS
end
