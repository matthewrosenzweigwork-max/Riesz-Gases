import HRS.MD.EQInterpHolder

/-!
# EQ-INTERP packet, part 3: the `W_2` clause (lifting of couplings along `E_m ↪ E_{m₁}` and Hölder in probability)

* `coupling_comap`: a coupling of the images `e_*μ, e_*ν` under a measurable embedding is the image of a coupling of `μ, ν`;
* `wass_interp`: for laws `μ, ν` on `𝒳_{m,T}` with `∫ qSq q ≤ A`, `W_2^{𝒳_m}(μ,ν) ≤ (4A)^{(1-α)/2} (b)^α` whenever `W_2^{𝒳_{m₁}}(e_*μ, e_*ν) < b`
  (TeX L4142-4147).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInterp

variable {d : ℕ}

theorem map_eq_of_map_embedding {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {e : X → Y}
    (he : MeasurableEmbedding e) {ρ₁ ρ₂ : Measure X} (h : ρ₁.map e = ρ₂.map e) : ρ₁ = ρ₂ := by
  ext s hs
  have h1 := congrArg (fun r : Measure Y => r (e '' s)) h
  simp only [he.map_apply, Set.preimage_image_eq _ he.injective] at h1
  exact h1

theorem coupling_comap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {e : X → Y}
    (he : MeasurableEmbedding e) {μ ν : Measure X} {π : Measure (Y × Y)}
    (h1 : π.map Prod.fst = μ.map e) (h2 : π.map Prod.snd = ν.map e) :
    ∃ π' : Measure (X × X), π'.map Prod.fst = μ ∧ π'.map Prod.snd = ν ∧
      π'.map (Prod.map e e) = π := by
  have hee : MeasurableEmbedding (Prod.map e e) := he.prodMap he
  have hr : MeasurableSet (Set.range e) := he.measurableSet_range
  have hfst : π (Prod.fst ⁻¹' (Set.range e)ᶜ) = 0 := by
    rw [← Measure.map_apply measurable_fst hr.compl, h1, he.map_apply]
    simp
  have hsnd : π (Prod.snd ⁻¹' (Set.range e)ᶜ) = 0 := by
    rw [← Measure.map_apply measurable_snd hr.compl, h2, he.map_apply]
    simp
  have hae : ∀ᵐ w ∂π, w ∈ Set.range (Prod.map e e) := by
    rw [ae_iff]
    refine measure_mono_null ?_ (measure_union_null hfst hsnd)
    intro w hw
    by_contra hcon
    apply hw
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, not_or, not_not] at hcon
    exact ⟨(hcon.1.choose, hcon.2.choose), by simp [hcon.1.choose_spec, hcon.2.choose_spec]⟩
  have hmap : (π.comap (Prod.map e e)).map (Prod.map e e) = π := by
    rw [hee.map_comap, Measure.restrict_eq_self_of_ae_mem hae]
  refine ⟨π.comap (Prod.map e e), ?_, ?_, hmap⟩
  · refine map_eq_of_map_embedding he ?_
    rw [Measure.map_map he.measurable measurable_fst]
    have : e ∘ Prod.fst = Prod.fst ∘ Prod.map e e := rfl
    rw [this, ← Measure.map_map measurable_fst hee.measurable, hmap, h1]
  · refine map_eq_of_map_embedding he ?_
    rw [Measure.map_map he.measurable measurable_snd]
    have : e ∘ Prod.snd = Prod.snd ∘ Prod.map e e := rfl
    rw [this, ← Measure.map_map measurable_snd hee.measurable, hmap, h2]

/-- The squared transport cost of a plan. -/
def wCost {B : Type*} [NormedAddCommGroup B] [MeasurableSpace B] (π : Measure (B × B)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π

theorem wassersteinE_two {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    (P Q : Measure B) :
    wassersteinE 2 P Q = ⨅ π : couplings P Q, (wCost π.1) ^ ((1 : ℝ) / 2) := rfl

theorem exists_coupling_of_lt {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    {P Q : Measure B} {b : ℝ≥0∞} (h : wassersteinE 2 P Q < b) :
    ∃ π : Measure (B × B), IsCoupling π P Q ∧ (wCost π) ^ ((1 : ℝ) / 2) < b := by
  rw [wassersteinE_two, iInf_lt_iff] at h
  obtain ⟨π, hπ⟩ := h
  exact ⟨π.1, π.2, hπ⟩

theorem wassersteinE_le_of_coupling {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] {P Q : Measure B} {π : Measure (B × B)} (h : IsCoupling π P Q) :
    wassersteinE 2 P Q ≤ (wCost π) ^ ((1 : ℝ) / 2) := by
  rw [wassersteinE_two]
  exact iInf_le (fun π : couplings P Q => (wCost π.1) ^ ((1 : ℝ) / 2)) ⟨π, h⟩

/-- Hölder in probability on a lifted coupling. -/
theorem wCost_comap_le {m m₁ T q α : ℝ} (hmm : m ≤ m₁) (hT : 0 ≤ T) (hα0 : 0 < α) (hα1 : α < 1)
    (hα : α * (m₁ - q) = m - q) (π' : Measure (PathSpace d m T × PathSpace d m T)) (A : ℝ≥0∞)
    (h1 : ∫⁻ w, qSq q w ∂(π'.map Prod.fst) ≤ A) (h2 : ∫⁻ w, qSq q w ∂(π'.map Prod.snd) ≤ A) :
    wCost π' ≤ (4 * A) ^ (1 - α) * (wCost (π'.map (Prod.map (epath hmm T) (epath hmm T)))) ^ α := by
  set e := (epath hmm T : PathSpace d m T → PathSpace d m₁ T) with he
  have hem : Measurable e := (epath hmm T).continuous.measurable
  have hpq : (1 / (1 - α)).HolderConjugate (1 / α) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · field_simp; ring
  set f : PathSpace d m T × PathSpace d m T → ℝ≥0∞ := fun z => qSq q (z.1 - z.2) with hf
  set G : PathSpace d m T × PathSpace d m T → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (‖e z.1 - e z.2‖ ^ 2) with hG
  have hfm : Measurable f := (qSq_measurable q m T).comp (measurable_fst.sub measurable_snd)
  have hGm : Measurable G := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (((epath hmm T).continuous.comp continuous_fst).sub
      ((epath hmm T).continuous.comp continuous_snd)).norm.pow 2 |>.measurable
  have hpt : ∀ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ≤ f z ^ (1 - α) * G z ^ α := by
    intro z
    have := sq_norm_le_holder hmm hT q α hα0 hα1 hα (z.1 - z.2)
    rw [Real.rpow_two]
    simpa [hf, hG, he, map_sub] using this
  -- the integral of `f`
  have hint1 : ∫⁻ z, f z ∂π' ≤ 4 * A := by
    calc ∫⁻ z, f z ∂π' ≤ ∫⁻ z, (2 * qSq q z.1 + 2 * qSq q z.2) ∂π' :=
          lintegral_mono fun z => qSq_sub_le q z.1 z.2
      _ = 2 * ∫⁻ z, qSq q z.1 ∂π' + 2 * ∫⁻ z, qSq q z.2 ∂π' := by
          have hm1 : Measurable fun z : PathSpace d m T × PathSpace d m T => 2 * qSq q z.1 :=
            ((qSq_measurable q m T).comp measurable_fst).const_mul 2
          rw [lintegral_add_left hm1, lintegral_const_mul' _ _ (by simp),
            lintegral_const_mul' _ _ (by simp)]
      _ = 2 * ∫⁻ w, qSq q w ∂(π'.map Prod.fst) + 2 * ∫⁻ w, qSq q w ∂(π'.map Prod.snd) := by
          rw [lintegral_map (qSq_measurable q m T) measurable_fst,
            lintegral_map (qSq_measurable q m T) measurable_snd]
      _ ≤ 2 * A + 2 * A := by gcongr
      _ = 4 * A := by rw [← two_mul, ← mul_assoc]; norm_num
  have hintG : ∫⁻ z, G z ∂π' = wCost (π'.map (Prod.map e e)) := by
    unfold wCost
    rw [lintegral_map (by
      refine ENNReal.measurable_ofReal.comp ?_
      exact (continuous_fst.sub continuous_snd).norm.rpow_const (fun _ => Or.inr (by norm_num)) |>.measurable)
      (Measurable.prodMap hem hem)]
    refine lintegral_congr fun z => ?_
    simp only [hG, Prod.map, Real.rpow_two]
  calc wCost π' ≤ ∫⁻ z, f z ^ (1 - α) * G z ^ α ∂π' := lintegral_mono hpt
    _ ≤ (∫⁻ z, (f z ^ (1 - α)) ^ (1 / (1 - α)) ∂π') ^ (1 / (1 / (1 - α))) *
        (∫⁻ z, (G z ^ α) ^ (1 / α) ∂π') ^ (1 / (1 / α)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq π' hpq (hfm.pow_const _).aemeasurable (hGm.pow_const _).aemeasurable
    _ = (∫⁻ z, f z ∂π') ^ (1 - α) * (∫⁻ z, G z ∂π') ^ α := by
        have e1 : ∀ z, (f z ^ (1 - α)) ^ (1 / (1 - α)) = f z := fun z => by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel (by linarith), ENNReal.rpow_one]
        have e2 : ∀ z, (G z ^ α) ^ (1 / α) = G z := fun z => by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hα0.ne', ENNReal.rpow_one]
        have h1' : 1 / (1 / (1 - α)) = 1 - α := by field_simp
        have h2' : 1 / (1 / α) = α := by field_simp
        simp_rw [e1, e2]; rw [h1', h2']
    _ ≤ (4 * A) ^ (1 - α) * (wCost (π'.map (Prod.map e e))) ^ α := by
        rw [hintG]; gcongr

/-- `W_2` interpolation (TeX L4142-4147): lifting an almost optimal coupling from `𝒳_{m₁,T}` back to `𝒳_{m,T}`. -/
theorem wass_interp {m m₁ T q α : ℝ} (hmm : m ≤ m₁) (hT : 0 ≤ T) (hα0 : 0 < α) (hα1 : α < 1)
    (hα : α * (m₁ - q) = m - q) (μ ν : Measure (PathSpace d m T)) (A : ℝ≥0∞)
    (hμ : ∫⁻ w, qSq q w ∂μ ≤ A) (hν : ∫⁻ w, qSq q w ∂ν ≤ A) (b : ℝ≥0∞)
    (hb : wassersteinE 2 (μ.map (epath hmm T)) (ν.map (epath hmm T)) < b) :
    wassersteinE 2 μ ν ≤ (4 * A) ^ ((1 - α) / 2) * b ^ α := by
  obtain ⟨π, hπ, hlt⟩ := exists_coupling_of_lt hb
  obtain ⟨π', hp1, hp2, hpm⟩ := coupling_comap (epath_measurableEmbedding hmm T) hπ.1 hπ.2
  have hcost := wCost_comap_le hmm hT hα0 hα1 hα π' A (by rw [hp1]; exact hμ) (by rw [hp2]; exact hν)
  rw [hpm] at hcost
  calc wassersteinE 2 μ ν ≤ (wCost π') ^ ((1 : ℝ) / 2) :=
        wassersteinE_le_of_coupling ⟨hp1, hp2⟩
    _ ≤ ((4 * A) ^ (1 - α) * (wCost π) ^ α) ^ ((1 : ℝ) / 2) := by gcongr
    _ = (4 * A) ^ ((1 - α) / 2) * ((wCost π) ^ ((1 : ℝ) / 2)) ^ α := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        congr 2 <;> ring
    _ ≤ (4 * A) ^ ((1 - α) / 2) * b ^ α := by gcongr

end HRS.MD.EQInterp
