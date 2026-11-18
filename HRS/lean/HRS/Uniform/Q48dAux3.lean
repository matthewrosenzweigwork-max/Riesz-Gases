import HRS.Uniform.Q48dAux2

/-!
# Q48d, part 3: stopped covariation martingales on longer horizons, suprema over windows, window integrals
(infrastructure for Lemma 3.31)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Uniform.Q48d

lemma integrableOn_extend {f : ℝ → ℝ} {S S' : ℝ} (hS0 : 0 ≤ S) (hSS : S ≤ S')
    (hf : IntegrableOn f (Icc 0 S)) (hz : ∀ σ, S < σ → f σ = 0) : IntegrableOn f (Icc 0 S') := by
  rw [← Icc_union_Ioc_eq_Icc hS0 hSS]
  refine hf.union ?_
  exact (integrableOn_zero (μ := volume) (s := Ioc S S')).congr_fun
    (fun σ hσ => (hz σ hσ.1).symm) measurableSet_Ioc

section HMC

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}

/-- A process stopped at `S` with covariation density cut at `S` is a Hilbert martingale on every longer horizon. -/
lemma isHMC_extend {D : ℝ → Ω → E} {Sd : ℝ → Ω → (E →L[ℝ] E →L[ℝ] ℝ)} {S S' : ℝ} (hS0 : 0 ≤ S)
    (hSS : S ≤ S')
    (h : IsHilbertMartingaleWithCovariation P ℱ S (fun τ ω => D (min τ S) ω)
      (fun r ω => if r ≤ S then Sd r ω else 0)) :
    IsHilbertMartingaleWithCovariation P ℱ S' (fun τ ω => D (min τ S) ω)
      (fun r ω => if r ≤ S then Sd r ω else 0) := by
  have hidem : ∀ τ : ℝ, min (min τ S) S = min τ S := fun τ => min_eq_left (min_le_right _ _)
  have hz : ∀ (σ : ℝ), S < σ → ∀ ω, (if σ ≤ S then Sd σ ω else 0) = 0 := by
    intro σ hσ ω
    rw [if_neg (not_le.2 hσ)]
  refine ⟨h.martingale, h.zero, ?_, ?_, h.sigma_meas, h.sigma_adapted, ?_, ?_, ?_, ?_, h.covariation⟩
  · filter_upwards [h.cont] with ω hω
    have hmaps : MapsTo (fun τ : ℝ => min τ S) (Icc 0 S') (Icc 0 S) :=
      fun τ hτ => ⟨le_min hτ.1 hS0, min_le_right _ _⟩
    have := hω.comp (continuous_id.min continuous_const).continuousOn hmaps
    refine this.congr fun τ _ => ?_
    simp [hidem]
  · intro τ hτ
    have := h.sq_int (min τ S) ⟨le_min hτ.1 hS0, min_le_right _ _⟩
    simpa [hidem] using this
  · filter_upwards [h.sigma_traceClass] with ω hω σ hσ
    by_cases hs : σ ≤ S
    · simpa [hs] using hω σ ⟨hσ.1, hs⟩
    · simpa [hs] using Kot.isTraceClassCov_zero (K' := E)
  · have e : ∀ ω, ∫ σ in Icc 0 S', traceNormForm (if σ ≤ S then Sd σ ω else 0) =
        ∫ σ in Icc 0 S, traceNormForm (if σ ≤ S then Sd σ ω else 0) := by
      intro ω
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
        (Icc_subset_Icc_right hSS) fun σ hσ => ?_
      have : S < σ := by
        by_contra hc
        exact hσ.2 ⟨hσ.1.1, not_lt.1 hc⟩
      simp [not_le.2 this, Kot.traceNormForm_zero]
    simpa [e] using h.sigma_int
  · filter_upwards [h.sigma_pathint] with ω hω
    refine integrableOn_extend hS0 hSS hω fun σ hσ => ?_
    simp [not_le.2 hσ, Kot.traceNormForm_zero]
  · filter_upwards [h.sigma_entry_int] with ω hω x y
    refine integrableOn_extend hS0 hSS (hω x y) fun σ hσ => ?_
    simp [not_le.2 hσ]

end HMC

section Sup

variable {E : Type*} [NormedAddCommGroup E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Countable dense subset of `[a,b]`. -/
def ratIcc (a b : ℝ) : Set ℝ := (Icc a b ∩ range ((↑) : ℚ → ℝ)) ∪ {a, b}

lemma countable_ratIcc (a b : ℝ) : (ratIcc a b).Countable :=
  (((countable_range _).mono inter_subset_right)).union (Set.toFinite {a, b}).countable

lemma ratIcc_subset {a b : ℝ} (hab : a ≤ b) : ratIcc a b ⊆ Icc a b := by
  rintro x (hx | hx | hx)
  · exact hx.1
  · rw [hx]; exact ⟨le_rfl, hab⟩
  · rw [Set.mem_singleton_iff.1 hx]; exact ⟨hab, le_rfl⟩

lemma Icc_subset_closure_ratIcc {a b : ℝ} (hab : a ≤ b) : Icc a b ⊆ closure (ratIcc a b) := by
  intro t ht
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases eq_or_lt_of_le ht.2 with h | h
  · exact ⟨b, Or.inr (Or.inr rfl), by rw [Real.dist_eq, h]; simpa using hε⟩
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < min b (t + ε) from lt_min h (by linarith))
    refine ⟨q, Or.inl ⟨⟨ht.1.trans hq1.le, (hq2.trans_le (min_le_left _ _)).le⟩, q, rfl⟩, ?_⟩
    have := hq2.trans_le (min_le_right _ _)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

lemma iSup_Icc_le_iSup_ratIcc {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (⨆ t ∈ Icc a b, ‖f t‖ₑ) ≤ ⨆ q ∈ ratIcc a b, ‖f q‖ₑ := by
  set c := ⨆ q ∈ ratIcc a b, ‖f q‖ₑ with hc
  have hclosed : IsClosed (Icc a b ∩ f ⁻¹' {y | ‖y‖ₑ ≤ c}) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_le continuous_enorm continuous_const)
  have hsub : ratIcc a b ⊆ Icc a b ∩ f ⁻¹' {y | ‖y‖ₑ ≤ c} := fun q hq =>
    ⟨ratIcc_subset hab hq, le_iSup₂ (f := fun q (_ : q ∈ ratIcc a b) => ‖f q‖ₑ) q hq⟩
  refine iSup₂_le fun t ht => ?_
  exact (closure_minimal hsub hclosed (Icc_subset_closure_ratIcc hab ht)).2

lemma iSup_Icc_eq_iSup_ratIcc {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (⨆ t ∈ Icc a b, ‖f t‖ₑ) = ⨆ q ∈ ratIcc a b, ‖f q‖ₑ :=
  le_antisymm (iSup_Icc_le_iSup_ratIcc hab hf)
    (iSup₂_le fun q hq => le_iSup₂ (f := fun t (_ : t ∈ Icc a b) => ‖f t‖ₑ) q (ratIcc_subset hab hq))

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma aemeasurable_supIcc {f : ℝ → Ω → E} {a b : ℝ} (hab : a ≤ b)
    (hm : ∀ t ∈ Icc a b, AEStronglyMeasurable (f t) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => f t ω) (Icc a b)) :
    AEMeasurable (fun ω => ⨆ t ∈ Icc a b, ‖f t ω‖ₑ) P := by
  have h1 : AEMeasurable (fun ω => ⨆ q ∈ ratIcc a b, ‖f q ω‖ₑ) P :=
    AEMeasurable.biSup (ratIcc a b) (countable_ratIcc a b) fun q hq =>
      (hm q (ratIcc_subset hab hq)).enorm
  refine h1.congr ?_
  filter_upwards [hc] with ω hω
  exact (iSup_Icc_eq_iSup_ratIcc hab hω).symm

end Sup

section Window

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}

/-- The window integral of the cut covariation density. -/
lemma window_rhs_le {D : ℝ → Ω → E} {Sd : ℝ → Ω → (E →L[ℝ] E →L[ℝ] ℝ)} {S S' : ℝ}
    (h : IsHilbertMartingaleWithCovariation P ℱ S' (fun τ ω => D (min τ S) ω)
      (fun r ω => if r ≤ S then Sd r ω else 0)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ r : ℝ, 0 ≤ r → ∫⁻ ω, ENNReal.ofReal (traceNormForm (Sd r ω)) ∂P ≤ ENNReal.ofReal K)
    {u L : ℝ} (hu : 0 ≤ u) (hL : 0 ≤ L) :
    ∫⁻ ω, (∫⁻ r in Icc u (u + L),
        ENNReal.ofReal (traceNormForm (if r ≤ S then Sd r ω else 0))) ∂P ≤ ENNReal.ofReal (K * L) := by
  have hmeas : Measurable fun p : ℝ × Ω =>
      traceNormForm (if p.1 ≤ S then Sd p.1 p.2 else 0) :=
    measurable_traceNormForm (α := ℝ × Ω) (fun p => if p.1 ≤ S then Sd p.1 p.2 else 0)
      (fun x y => h.sigma_meas x y)
  have hmeas' : Measurable (Function.uncurry fun (ω : Ω) (r : ℝ) =>
      ENNReal.ofReal (traceNormForm (if r ≤ S then Sd r ω else 0))) := by
    have := (ENNReal.measurable_ofReal.comp hmeas).comp (measurable_swap (α := Ω) (β := ℝ))
    exact this
  rw [lintegral_lintegral_swap hmeas'.aemeasurable]
  calc ∫⁻ r in Icc u (u + L), (∫⁻ ω, ENNReal.ofReal (traceNormForm (if r ≤ S then Sd r ω else 0)) ∂P)
      ≤ ∫⁻ r in Icc u (u + L), ENNReal.ofReal K := by
        refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
        by_cases hrS : r ≤ S
        · simpa [hrS] using hK r (hu.trans hr.1)
        · simp [hrS, Kot.traceNormForm_zero]
    _ = ENNReal.ofReal (K * L) := by
        rw [setLIntegral_const, Real.volume_Icc, add_sub_cancel_left,
          ← ENNReal.ofReal_mul hK0]

end Window

end HRS.Uniform.Q48d
