import HRS.Uniform.Q07cAux5
import HRS.Prob.MartingaleRep

/-!
# Q07c, part 6: transfer lemmas for `IsHilbertMartingaleWithCovariation`

Horizon monotonicity with a modified density, stopping with a modified density, replacement of
the process by an a.e. equal one (complete filtration), and lifting to the product enlargement.
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q07c

section HMt

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {N : ℝ → Ω → H} {Sg Sg' : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {t S : ℝ}

omit [BorelSpace H] [IsProbabilityMeasure P] in
lemma tn_meas_uncurry (hm : ∀ x y : H, Measurable (Function.uncurry fun σ ω => Sg' σ ω x y)) :
    Measurable (Function.uncurry fun σ ω => traceNormForm (Sg' σ ω)) :=
  measurable_traceNormForm (H := H) (α := ℝ × Ω) (fun a => Sg' a.1 a.2) hm

theorem sigma_fields_of_ae (hSt : S ≤ t)
    (hm' : ∀ x y : H, Measurable (Function.uncurry fun σ ω => Sg' σ ω x y))
    (hI : Integrable (fun ω => ∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω)) P)
    (hpath : ∀ᵐ ω ∂P, IntegrableOn (fun σ => traceNormForm (Sg σ ω)) (Set.Icc 0 t))
    (hent : ∀ᵐ ω ∂P, ∀ x y : H, IntegrableOn (fun σ => Sg σ ω x y) (Set.Icc 0 t))
    (hae : ∀ᵐ ω ∂P, ∀ᵐ σ ∂(volume.restrict (Set.Icc 0 S)), Sg' σ ω = Sg σ ω) :
    Integrable (fun ω => ∫ σ in Set.Icc 0 S, traceNormForm (Sg' σ ω)) P ∧
    (∀ᵐ ω ∂P, IntegrableOn (fun σ => traceNormForm (Sg' σ ω)) (Set.Icc 0 S)) ∧
    (∀ᵐ ω ∂P, ∀ x y : H, IntegrableOn (fun σ => Sg' σ ω x y) (Set.Icc 0 S)) := by
  have hsub : Set.Icc (0 : ℝ) S ⊆ Set.Icc 0 t := Set.Icc_subset_Icc_right hSt
  have hpath' : ∀ᵐ ω ∂P, IntegrableOn (fun σ => traceNormForm (Sg' σ ω)) (Set.Icc 0 S) := by
    filter_upwards [hpath, hae] with ω hω hae'
    refine (hω.mono_set hsub).congr ?_
    filter_upwards [hae'] with σ h
    rw [h]
  refine ⟨?_, hpath', ?_⟩
  · have hmeas := tn_meas_uncurry (Sg' := Sg') hm'
    have hsm : StronglyMeasurable fun ω => ∫ σ in Set.Icc 0 S, traceNormForm (Sg' σ ω) := by
      have := (hmeas.comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable
      exact this.integral_prod_right' (ν := volume.restrict (Set.Icc 0 S))
    refine Integrable.mono' hI hsm.aestronglyMeasurable ?_
    filter_upwards [hpath, hae] with ω hω hae'
    rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _)]
    have e1 : ∫ σ in Set.Icc 0 S, traceNormForm (Sg' σ ω) =
        ∫ σ in Set.Icc 0 S, traceNormForm (Sg σ ω) := by
      refine integral_congr_ae ?_
      filter_upwards [hae'] with σ h
      rw [h]
    rw [e1]
    exact setIntegral_mono_set hω (Filter.Eventually.of_forall fun σ => traceNormForm_nonneg _)
      (Filter.Eventually.of_forall hsub)
  · filter_upwards [hent, hae] with ω hω hae' x y
    refine ((hω x y).mono_set hsub).congr ?_
    filter_upwards [hae'] with σ h
    rw [h]

omit [BorelSpace H] [SecondCountableTopology H] in
lemma ae_zero_nonpos_aux (hM : IsHilbertMartingaleWithCovariation P ℱ t N Sg) (x : H) {τ : ℝ}
    (hτ : τ ≤ 0) : (fun ω => inner ℝ (N τ ω) x) =ᵐ[P] 0 := by
  have h := (hM.martingale x).2 τ 0 hτ
  have h0 : (fun ω => inner ℝ (N 0 ω) x) =ᵐ[P] 0 := hM.zero.mono fun ω h => by simp [h]
  calc (fun ω => inner ℝ (N τ ω) x) =ᵐ[P] P[fun ω => inner ℝ (N 0 ω) x | ℱ τ] := h.symm
    _ =ᵐ[P] P[(0 : Ω → ℝ) | ℱ τ] := condExp_congr_ae h0
    _ =ᵐ[P] 0 := by rw [condExp_zero]

omit [BorelSpace H] [SecondCountableTopology H] in
lemma memLp_inner_aux (hM : IsHilbertMartingaleWithCovariation P ℱ t N Sg) (ht : 0 ≤ t) (x : H)
    {τ : ℝ} (hτ : τ ≤ t) : MemLp (fun ω => inner ℝ (N τ ω) x) 2 P := by
  by_cases h : 0 ≤ τ
  · exact (hM.sq_int τ ⟨h, hτ⟩).inner_const (𝕜 := ℝ) x
  · exact MemLp.ae_eq (ae_zero_nonpos_aux hM x (not_le.1 h).le).symm MemLp.zero

theorem _root_.HRS.IsHilbertMartingaleWithCovariation.mono_congr
    (hM : IsHilbertMartingaleWithCovariation P ℱ t N Sg) (hS : 0 ≤ S) (hSt : S ≤ t)
    (hm' : ∀ x y : H, Measurable (Function.uncurry fun σ ω => Sg' σ ω x y))
    (ha' : ∀ σ, ∀ x y : H, Measurable[ℱ σ] (fun ω => Sg' σ ω x y))
    (heq : ∀ r : ℝ, 0 ≤ r → ∀ ω, Sg' r ω = Sg r ω) :
    IsHilbertMartingaleWithCovariation P ℱ S N Sg' := by
  have hsub : Set.Icc (0 : ℝ) S ⊆ Set.Icc 0 t := Set.Icc_subset_Icc_right hSt
  have hae : ∀ᵐ ω ∂P, ∀ᵐ σ ∂(volume.restrict (Set.Icc 0 S)), Sg' σ ω = Sg σ ω :=
    Filter.Eventually.of_forall fun ω =>
      (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => heq σ hσ.1 ω)
  obtain ⟨h1, h2, h3⟩ := sigma_fields_of_ae hSt hm' hM.sigma_int hM.sigma_pathint
    hM.sigma_entry_int hae
  refine ⟨hM.martingale, hM.zero, ?_, fun τ hτ => hM.sq_int τ ⟨hτ.1, hτ.2.trans hSt⟩, hm', ha',
    ?_, h1, h2, h3, fun x y => ?_⟩
  · filter_upwards [hM.cont] with ω h
    exact h.mono hsub
  · filter_upwards [hM.sigma_traceClass] with ω h σ hσ
    rw [heq σ hσ.1 ω]
    exact h σ (hsub hσ)
  · have e : ∀ τ ω, ∫ σ in Set.Icc 0 τ, Sg' σ ω x y = ∫ σ in Set.Icc 0 τ, Sg σ ω x y := fun τ ω =>
      setIntegral_congr_fun measurableSet_Icc fun σ hσ => by rw [heq σ hσ.1 ω]
    have := hM.covariation x y
    simpa only [e] using this

theorem _root_.HRS.IsHilbertMartingaleWithCovariation.stop_congr (hℱ : IsCompleteFiltration P ℱ)
    (hM : IsHilbertMartingaleWithCovariation P ℱ t N Sg) (hS : 0 ≤ S) (hSt : S ≤ t)
    {Sd : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hm : ∀ x y : H, Measurable (Function.uncurry fun σ ω => Sd σ ω x y))
    (ha : ∀ σ, ∀ x y : H, Measurable[ℱ σ] (fun ω => Sd σ ω x y))
    (htc : ∀ σ ω, IsTraceClassCov (Sd σ ω))
    (hae : ∀ᵐ ω ∂P, ∀ᵐ σ ∂(volume.restrict (Set.Icc 0 S)), Sd σ ω = Sg σ ω) :
    IsHilbertMartingaleWithCovariation P ℱ S (fun τ ω => N (min τ S) ω)
      (fun r ω => if r ≤ S then Sd r ω else 0) := by
  have hsub : Set.Icc (0 : ℝ) S ⊆ Set.Icc 0 t := Set.Icc_subset_Icc_right hSt
  have hmite : ∀ x y : H, Measurable (Function.uncurry fun σ ω =>
      (fun r ω => if r ≤ S then Sd r ω else 0) σ ω x y) := by
    intro x y
    have : (Function.uncurry fun σ ω => (fun r ω => if r ≤ S then Sd r ω else 0) σ ω x y) =
        fun p : ℝ × Ω => if p.1 ≤ S then Sd p.1 p.2 x y else 0 := by
      funext p; by_cases h : p.1 ≤ S <;> simp [Function.uncurry, h]
    rw [this]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const) (hm x y) measurable_const
  have hae' : ∀ᵐ ω ∂P, ∀ᵐ σ ∂(volume.restrict (Set.Icc 0 S)),
      (fun r ω => if r ≤ S then Sd r ω else 0) σ ω = Sg σ ω := by
    filter_upwards [hae] with ω h
    filter_upwards [h, ae_restrict_mem measurableSet_Icc] with σ h1 h2
    simp only [h2.2, ite_true]
    exact h1
  obtain ⟨h1, h2, h3⟩ := sigma_fields_of_ae hSt hmite hM.sigma_int hM.sigma_pathint
    hM.sigma_entry_int hae'
  refine ⟨fun x => ?_, ?_, ?_, fun τ hτ => ?_, hmite, fun σ x y => ?_, ?_, h1, h2, h3,
    fun x y => ?_⟩
  · have := HRS.MRep.martingale_stop_time (hM.martingale x) S
    simpa only [min_comm] using this
  · filter_upwards [hM.zero] with ω h
    simpa [min_eq_left hS] using h
  · filter_upwards [hM.cont] with ω h
    refine (h.mono hsub).congr fun τ hτ => ?_
    simp [min_eq_left hτ.2]
  · have h := hM.sq_int τ ⟨hτ.1, hτ.2.trans hSt⟩
    simpa [min_eq_left hτ.2] using h
  · by_cases hσ : σ ≤ S
    · simpa [hσ] using ha σ x y
    · simp [hσ]
  · exact Filter.Eventually.of_forall fun ω σ hσ => by
      simp only [hσ.2, ite_true]; exact htc σ ω
  · -- covariation
    have hX : Martingale (fun τ ω => inner ℝ (N τ ω) x * inner ℝ (N τ ω) y -
        ∫ σ in Set.Icc 0 τ, Sg σ ω x y) ℱ P := hM.covariation x y
    have hUt : Martingale (fun τ ω => inner ℝ (N (min t τ) ω) x) ℱ P :=
      HRS.MRep.martingale_stop_time (F := fun τ ω => inner ℝ (N τ ω) x) (hM.martingale x) t
    have hVt : Martingale (fun τ ω => inner ℝ (N (min t τ) ω) y) ℱ P :=
      HRS.MRep.martingale_stop_time (F := fun τ ω => inner ℝ (N τ ω) y) (hM.martingale y) t
    have hΛ : Martingale (fun τ ω => inner ℝ (N (min t τ) ω) x * inner ℝ (N (min t τ) ω) y -
        ∫ σ in Set.Icc 0 (min t τ), Sg σ ω x y) ℱ P :=
      HRS.MRep.martingale_stop_time (F := fun τ ω => inner ℝ (N τ ω) x * inner ℝ (N τ ω) y -
        ∫ σ in Set.Icc 0 τ, Sg σ ω x y) hX t
    have hst := HRS.MRep.martingale_stopped_mul hUt hVt
      (fun τ => memLp_inner_aux hM (hS.trans hSt) x (min_le_left t τ))
      (fun τ => memLp_inner_aux hM (hS.trans hSt) y (min_le_left t τ)) hΛ S
    have hmeasI : ∀ τ, Measurable fun ω => ∫ σ in Set.Icc 0 τ,
        (fun r ω => if r ≤ S then Sd r ω else 0) σ ω x y := fun τ =>
      (((hmite x y).comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Set.Icc 0 τ))).measurable
    refine HRS.MRep.martingale_congr_complete hℱ hst (fun τ => ?_) (fun τ => ?_)
    · refine Measurable.sub (Measurable.mul ?_ ?_) (hmeasI τ)
      · exact ((hM.martingale x).1 (min τ S)).measurable.mono (ℱ.le _) le_rfl
      · exact ((hM.martingale y).1 (min τ S)).measurable.mono (ℱ.le _) le_rfl
    · have hmin : min t (min S τ) = min S τ := min_eq_right ((min_le_left S τ).trans hSt)
      filter_upwards [hae] with ω hω
      simp only [hmin, min_comm τ S]
      congr 1
      have e1 : ∫ σ in Set.Icc 0 τ, (fun r ω => if r ≤ S then Sd r ω else 0) σ ω x y =
          ∫ σ in Set.Icc 0 τ, (if σ ≤ S then Sd σ ω x y else 0) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
        by_cases h : σ ≤ S <;> simp [h]
      rw [e1, HRS.MRep.integral_ite_Icc S τ (fun r => Sd r ω x y)]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (Set.Icc_subset_Icc_right (min_le_left S τ)) hω] with σ h
      rw [h]

theorem _root_.HRS.IsHilbertMartingaleWithCovariation.congr_process (hℱ : IsCompleteFiltration P ℱ)
    (hM : IsHilbertMartingaleWithCovariation P ℱ t N Sg) {N' : ℝ → Ω → H}
    (hm : ∀ τ, Measurable (N' τ)) (hae : ∀ τ, N' τ =ᵐ[P] N τ)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun τ => N' τ ω) (Set.Icc 0 t)) :
    IsHilbertMartingaleWithCovariation P ℱ t N' Sg := by
  have hinner : ∀ (x : H) τ, (fun ω => inner ℝ (N τ ω) x) =ᵐ[P] fun ω => inner ℝ (N' τ ω) x :=
    fun x τ => (hae τ).mono fun ω h => by simp only [h]
  refine ⟨fun x => ?_, ?_, hc, fun τ hτ => (hM.sq_int τ hτ).ae_eq (hae τ).symm, hM.sigma_meas,
    hM.sigma_adapted, hM.sigma_traceClass, hM.sigma_int, hM.sigma_pathint, hM.sigma_entry_int,
    fun x y => ?_⟩
  · exact HRS.MRep.martingale_congr_complete hℱ (hM.martingale x)
      (fun τ => (hm τ).inner measurable_const) (hinner x)
  · filter_upwards [hM.zero, hae 0] with ω h1 h2
    rw [h2, h1]
  · have hmeasI : ∀ τ, Measurable fun ω => ∫ σ in Set.Icc 0 τ, Sg σ ω x y := fun τ =>
      (((hM.sigma_meas x y).comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Set.Icc 0 τ))).measurable
    refine HRS.MRep.martingale_congr_complete hℱ (hM.covariation x y) (fun τ => ?_) (fun τ => ?_)
    · exact (((hm τ).inner measurable_const).mul ((hm τ).inner measurable_const)).sub (hmeasI τ)
    · filter_upwards [hae τ] with ω h
      simp only [h]

end HMt

section Prod

universe u

variable {Ω' : Type u} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ℱ' : Filtration ℝ mΩ'} {ι : Type u} [Countable ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {N : ℝ → Ω' → H} {Sg : ℝ → Ω' → (H →L[ℝ] H →L[ℝ] ℝ)} {t : ℝ}

theorem _root_.HRS.IsHilbertMartingaleWithCovariation.comp_fst
    (hM : IsHilbertMartingaleWithCovariation P' ℱ' t N Sg) :
    IsHilbertMartingaleWithCovariation (P'.prod (wMeasure ι))
      (prodFiltration P' (wMeasure ι) ℱ' (wFiltration ι)) t (fun τ p => N τ p.1)
      (fun r p => Sg r p.1) := by
  have hπp : MeasurePreserving (Prod.fst : Ω' × (ι → WienerSeq) → Ω') (P'.prod (wMeasure ι)) P' :=
    measurePreserving_fst
  have hπm : ∀ s, Measurable[prodFiltration P' (wMeasure ι) ℱ' (wFiltration ι) s, ℱ' s]
      (Prod.fst : Ω' × (ι → WienerSeq) → Ω') := fun s =>
    Measurable.of_comap_le (le_sup_of_le_left le_sup_left)
  refine ⟨fun x => HRS.MRep.martingale_fst (F := fun τ ω => inner ℝ (N τ ω) x) (hM.martingale x),
    hπp.quasiMeasurePreserving.ae hM.zero, hπp.quasiMeasurePreserving.ae hM.cont,
    fun τ hτ => (hM.sq_int τ hτ).comp_measurePreserving hπp, fun x y => ?_, fun σ x y => ?_,
    hπp.quasiMeasurePreserving.ae hM.sigma_traceClass, ?_,
    hπp.quasiMeasurePreserving.ae hM.sigma_pathint,
    hπp.quasiMeasurePreserving.ae hM.sigma_entry_int, fun x y => ?_⟩
  · exact (hM.sigma_meas x y).comp (measurable_fst.prodMk (measurable_snd.fst))
  · exact (hM.sigma_adapted σ x y).comp (hπm σ)
  · exact hπp.integrable_comp_of_integrable (g := fun ω => ∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω))
      hM.sigma_int
  · exact HRS.MRep.martingale_fst
      (F := fun τ ω => inner ℝ (N τ ω) x * inner ℝ (N τ ω) y - ∫ σ in Set.Icc 0 τ, Sg σ ω x y)
      (hM.covariation x y)

end Prod

end HRS.Uniform.Q07c
