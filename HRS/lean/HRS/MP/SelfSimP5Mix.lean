import HRS.MP.SelfSimP5Spec
import HRS.MP.SelfSimP5MixB
import HRS.MP.SelfSimP1CepaUniq

/-!
# MPP5C (1): the mixture over the order classes, `ss5_mixture`

`HRS.MP.SelfSimP5Impl.ss5_mixture_proof` has the statement of `HRS.MP.SelfSimP5.ss5_mixture`.
Route (port of `HRS/MC/CepH5FinProof.lean`): the cones `ss5_cone σ` are disjoint open sets covering the collision-free
space, `P = ∑ P(A_σ) cond P A_σ` with `A_σ = Y₀⁻¹(cone σ)`; the entropy/Fisher additivity (`SelfSimP5MixA`) turns the
inequality for the mixture into the recombination of the component inequalities (`EReal` bookkeeping, copied from
`CepH5FinProof`); the component laws live on `cone σ` at every time `τ ≤ S` because their entropy is finite
(`≪ Ḡ dξ`, so no mass on the collision set) and the ordering permutation is forced to be `σ`; the measurability in time
of the Fisher informations is `SelfSimP5MixB`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS.MP.SelfSimP5
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MP.SelfSimP5Impl

/-! ### Bookkeeping in `EReal` / `ℝ≥0∞` (finite mixtures); copied from `CepH5FinProof` -/

section Bookkeeping

/-- A finite sum of real coercions is the coercion of the real sum (glue; proved). -/
theorem ss5m_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]


/-- A finite sum of terms `≠ ⊥` is `≠ ⊥` (glue; proved). -/
theorem ss5m_sum_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal) (h : ∀ i, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact fun hh => (EReal.add_eq_bot_iff.1 hh).elim (h a) ih

/-- **B1** (finiteness of the components).  In a mixture `∑ p_i a_i + c` of `EReal` numbers `a_i ≠ ⊥` with weights
`p_i ≥ 0` and a real `c`, finiteness of the total forces `a_i < ⊤` for every `i` with `p_i ≠ 0` (a term `p_i * ⊤ = ⊤`
absorbs the finitely many other terms, none of which is `⊥`). -/
theorem ss5m_components_lt_top {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (a : ι → EReal)
    (ha : ∀ i, a i ≠ ⊥) (c : EReal) (hc1 : c ≠ ⊥) (hc2 : c ≠ ⊤)
    (h : ∑ i, ((p i : ℝ) : EReal) * a i + c < ⊤) : ∀ i, p i ≠ 0 → a i < ⊤ := by
  classical
  intro i0 hi0
  by_contra hcon
  have hat : a i0 = ⊤ := by
    rcases (not_lt.1 hcon).eq_or_lt with h' | h'
    · exact (top_le_iff.1 (not_lt.1 hcon))
    · exact absurd h' (not_lt.2 le_top)
  have hpos : 0 < p i0 := lt_of_le_of_ne (hp i0) (Ne.symm hi0)
  have hterm : ((p i0 : ℝ) : EReal) * a i0 = ⊤ := by
    rw [hat]; exact EReal.coe_mul_top_of_pos hpos
  have hne : ∀ i, ((p i : ℝ) : EReal) * a i ≠ ⊥ := by
    intro i
    by_cases hz : p i = 0
    · simp [hz]
    · exact (EReal.mul_ne_bot _ _).2 ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (ha i),
        Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_nonneg.2 (hp i))⟩
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0), hterm,
    EReal.top_add_of_ne_bot (ss5m_sum_ne_bot _ _ hne), EReal.top_add_of_ne_bot hc1] at h
  exact lt_irrefl _ h


/-- **B2** (recombination of the entropy inequalities).  If for the weights `p_i ≥ 0` and each `i` with `p_i ≠ 0`
`Ht_i + F_i ≤ H0_i < ⊤` with `Ht_i, H0_i ≠ ⊥`, then for any real `c`
`∑ p_i Ht_i + c + ↑(∑ ofReal p_i * F_i) ≤ ∑ p_i H0_i + c`.  Proof: for `p_i ≠ 0` the three numbers `Ht_i, F_i, H0_i`
are finite (`Ht_i ≠ ⊥`, `Ht_i + F_i ≤ H0_i < ⊤`), so everything is real arithmetic; terms with `p_i = 0` vanish. -/
theorem ss5m_recombine {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (Ht H0 : ι → EReal)
    (F : ι → ℝ≥0∞) (hHt : ∀ i, Ht i ≠ ⊥) (hH0 : ∀ i, H0 i ≠ ⊥)
    (h : ∀ i, p i ≠ 0 → H0 i < ⊤ ∧ Ht i + (F i : EReal) ≤ H0 i) (c : EReal) (hc1 : c ≠ ⊥) (hc2 : c ≠ ⊤) :
    ∑ i, ((p i : ℝ) : EReal) * Ht i + c + ((∑ i, ENNReal.ofReal (p i) * F i : ℝ≥0∞) : EReal)
      ≤ ∑ i, ((p i : ℝ) : EReal) * H0 i + c := by
  classical
  obtain ⟨c', rfl⟩ : ∃ c' : ℝ, c = (c' : EReal) := ⟨c.toReal, (EReal.coe_toReal hc2 hc1).symm⟩
  -- real shadows
  have key : ∀ i, ((p i : ℝ) : EReal) * Ht i = (((p i * (Ht i).toReal : ℝ)) : EReal) := by
    intro i
    by_cases hz : p i = 0
    · simp [hz]
    · obtain ⟨h1, h2⟩ := h i hz
      have hHtt : Ht i ≠ ⊤ := by
        intro ht
        rw [ht] at h2
        have : (⊤ : EReal) + (F i : EReal) = ⊤ := EReal.top_add_of_ne_bot (by simp)
        rw [this] at h2
        exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
      rw [EReal.coe_mul, EReal.coe_toReal hHtt (hHt i)]
  have key0 : ∀ i, ((p i : ℝ) : EReal) * H0 i = (((p i * (H0 i).toReal : ℝ)) : EReal) := by
    intro i
    by_cases hz : p i = 0
    · simp [hz]
    · obtain ⟨h1, h2⟩ := h i hz
      rw [EReal.coe_mul, EReal.coe_toReal h1.ne (hH0 i)]
  have keyF : ∀ i, ENNReal.ofReal (p i) * F i = ENNReal.ofReal (p i * (F i).toReal) := by
    intro i
    by_cases hz : p i = 0
    · simp [hz]
    · obtain ⟨h1, h2⟩ := h i hz
      have hFt : F i ≠ ⊤ := by
        intro ft
        have hh : Ht i + (F i : EReal) = ⊤ := by
          rw [ft]; simp; exact EReal.add_top_of_ne_bot (hHt i)
        rw [hh] at h2
        exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
      rw [ENNReal.ofReal_mul (hp i), ENNReal.ofReal_toReal hFt]
  have hineq : ∑ i, p i * (Ht i).toReal + c' + ∑ i, p i * (F i).toReal ≤ ∑ i, p i * (H0 i).toReal + c' := by
    have : ∑ i, p i * (Ht i).toReal + ∑ i, p i * (F i).toReal ≤ ∑ i, p i * (H0 i).toReal := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hz : p i = 0
      · simp [hz]
      · obtain ⟨h1, h2⟩ := h i hz
        have hHtt : Ht i ≠ ⊤ := by
          intro ht
          rw [ht] at h2
          have : (⊤ : EReal) + (F i : EReal) = ⊤ := EReal.top_add_of_ne_bot (by simp)
          rw [this] at h2
          exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
        have hFt : F i ≠ ⊤ := by
          intro ft
          have hh : Ht i + (F i : EReal) = ⊤ := by
            rw [ft]; simp; exact EReal.add_top_of_ne_bot (hHt i)
          rw [hh] at h2
          exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (hp i)
        have e1 : (Ht i) = ((Ht i).toReal : EReal) := (EReal.coe_toReal hHtt (hHt i)).symm
        have e2 : (F i : EReal) = (((F i).toReal : ℝ) : EReal) := by
          rw [← EReal.coe_ennreal_toReal hFt]
        have e0 : (H0 i) = ((H0 i).toReal : EReal) := (EReal.coe_toReal h1.ne (hH0 i)).symm
        rw [e1, e2, e0, ← EReal.coe_add] at h2
        exact EReal.coe_le_coe_iff.1 h2
    linarith
  simp only [key, key0, keyF]
  rw [ss5m_coe_sum, ss5m_coe_sum, ← ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (hp i) ENNReal.toReal_nonneg), EReal.coe_ennreal_ofReal,
    ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
  refine EReal.coe_le_coe_iff.2 ?_
  have := le_max_left (∑ i, p i * (F i).toReal) 0
  rw [max_eq_left (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) ENNReal.toReal_nonneg)]
  exact hineq

end Bookkeeping

/-- `gibbsEntropyW` is never `⊥`. -/
theorem ss5m_gibbsEntropyW_ne_bot {d N : ℕ} (G : EucConfig d N → ℝ) (μ : Measure (EucConfig d N)) :
    gibbsEntropyW G μ ≠ ⊥ := by
  unfold gibbsEntropyW
  generalize relEntropy μ (gibbsRefW G) = x
  generalize Real.log (gibbsPartitionW G).toReal = r
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  · have : ((x : ℝ≥0∞) : EReal) = ((x.toReal : ℝ) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hx]
    rw [this, ← EReal.coe_sub]
    exact EReal.coe_ne_bot _

/-! ### The cones -/

section Cones

variable {N : ℕ}

theorem ss5m_cone_open (σ : Equiv.Perm (Fin N)) : IsOpen (ss5_cone σ) := by
  have : ss5_cone σ = ⋂ k : Fin N, ⋂ l : Fin N, ⋂ (_ : k < l),
      {ξ : EucConfig 1 N | ξ (σ k) 0 < ξ (σ l) 0} := by
    ext ξ; simp [ss5_cone]
  rw [this]
  refine isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l =>
    isOpen_iInter_of_finite fun _ => ?_
  exact isOpen_lt ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_apply (σ k)))
    ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_apply (σ l)))

theorem ss5m_cone_not_coll {σ : Equiv.Perm (Fin N)} {ξ : EucConfig 1 N} (h : ξ ∈ ss5_cone σ) :
    ξ ∉ eucCollisionSet 1 N := by
  rintro ⟨i, j, hij, hEq⟩
  obtain ⟨k, rfl⟩ := σ.surjective i
  obtain ⟨l, rfl⟩ := σ.surjective j
  have hkl : k ≠ l := fun h' => hij (by rw [h'])
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · have := h k l hlt; rw [hEq] at this; exact lt_irrefl _ this
  · have := h l k hlt; rw [hEq] at this; exact lt_irrefl _ this

theorem ss5m_cone_ord {σ : Equiv.Perm (Fin N)} {ξ : EucConfig 1 N} (h : ξ ∈ ss5_cone σ) :
    ∀ k k' : Fin N, k ≤ k' → ξ (σ k) 0 ≤ ξ (σ k') 0 := by
  intro k k' hk
  rcases hk.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (h k k' hlt).le

theorem ss5m_cone_disjoint {σ σ' : Equiv.Perm (Fin N)} (h : σ ≠ σ') :
    Disjoint (ss5_cone σ) (ss5_cone σ') := by
  rw [Set.disjoint_left]
  intro ξ h1 h2
  exact h (HRS.MP.SelfSimP1.ssp1c_perm_unique (ss5m_cone_not_coll h1) (ss5m_cone_ord h1)
    (ss5m_cone_ord h2))

theorem ss5m_cone_iUnion : (⋃ σ : Equiv.Perm (Fin N), ss5_cone σ) = (eucCollisionSet 1 N)ᶜ := by
  ext ξ
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 h
    exact ss5m_cone_not_coll hσ
  · intro hx
    have hinj := HRS.MP.SelfSimP1.ssp1c_coord_injective hx
    refine Set.mem_iUnion.2 ⟨Tuple.sort (fun i => ξ i 0), ?_⟩
    intro k l hkl
    have hm := Tuple.monotone_sort (fun i => ξ i 0)
    exact lt_of_le_of_ne (hm hkl.le) fun h => hkl.ne ((Tuple.sort _).injective (hinj h))

/-- A point of `cone σ` (used as a dummy law for the classes of probability zero). -/
def ss5m_wit (σ : Equiv.Perm (Fin N)) : EucConfig 1 N :=
  fun i => WithLp.toLp 2 fun _ => ((σ.symm i : Fin N) : ℝ)

theorem ss5m_wit_mem (σ : Equiv.Perm (Fin N)) : ss5m_wit σ ∈ ss5_cone σ := by
  intro k l hkl
  simp only [ss5m_wit, Equiv.symm_apply_apply]
  exact_mod_cast hkl

theorem ss5m_weight_const (N : ℕ) (invβ τ : ℝ) :
    selfSimWeight 1 0 invβ N τ = selfSimWeight 1 0 invβ N 0 := by
  funext Ξ
  simp [selfSimWeight, selfSimPotential, aSelfSim]

theorem ss5m_fin_null (G : EucConfig 1 N → ℝ) (hG0 : ∀ ξ ∈ eucCollisionSet 1 N, G ξ = 0)
    (μ : Measure (EucConfig 1 N)) [IsFiniteMeasure μ] (h : gibbsEntropyW G μ < ⊤) :
    μ (eucCollisionSet 1 N) = 0 := by
  have hcm : MeasurableSet (eucCollisionSet 1 N) := ss5m_collision_closed.measurableSet
  unfold gibbsEntropyW at h
  have hk : relEntropy μ (gibbsRefW G) ≠ ⊤ := by
    intro htop
    rw [htop] at h
    simp at h
  have hac : μ ≪ gibbsRefW G := (klDiv_ne_top_iff.1 hk).1
  refine hac ?_
  unfold gibbsRefW
  rw [Measure.smul_apply, withDensity_apply _ hcm]
  have : ∫⁻ x in eucCollisionSet 1 N, ENNReal.ofReal (G x) = 0 := by
    rw [setLIntegral_congr_fun hcm (g := fun _ => 0) (fun x hx => by simp [hG0 x hx])]
    simp
  rw [this]; simp

end Cones

/-! ### The conditional laws -/

section Cond

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

open Classical in
/-- The conditional law of `X` on the class `A_σ = Z⁻¹(cone σ)` (a dummy Dirac law if `P A_σ = 0`). -/
def ss5mNu (P : Measure Ω) (Z X : Ω → EucConfig 1 N) (σ : Equiv.Perm (Fin N)) : Measure (EucConfig 1 N) :=
  if P (Z ⁻¹' ss5_cone σ) = 0 then Measure.dirac (ss5m_wit σ)
  else (ProbabilityTheory.cond P (Z ⁻¹' ss5_cone σ)).map X

theorem ss5mNu_of_ne {P : Measure Ω} {Z X : Ω → EucConfig 1 N} {σ : Equiv.Perm (Fin N)}
    (h : P (Z ⁻¹' ss5_cone σ) ≠ 0) :
    ss5mNu P Z X σ = (ProbabilityTheory.cond P (Z ⁻¹' ss5_cone σ)).map X := by
  unfold ss5mNu; rw [if_neg h]

theorem ss5mNu_of_eq {P : Measure Ω} {Z X : Ω → EucConfig 1 N} {σ : Equiv.Perm (Fin N)}
    (h : P (Z ⁻¹' ss5_cone σ) = 0) :
    ss5mNu P Z X σ = Measure.dirac (ss5m_wit σ) := by
  unfold ss5mNu; rw [if_pos h]

theorem ss5mNu_prob (P : Measure Ω) [IsProbabilityMeasure P] {Z X : Ω → EucConfig 1 N}
    (hX : Measurable X) (σ : Equiv.Perm (Fin N)) : IsProbabilityMeasure (ss5mNu P Z X σ) := by
  by_cases h : P (Z ⁻¹' ss5_cone σ) = 0
  · rw [ss5mNu_of_eq h]; infer_instance
  · rw [ss5mNu_of_ne h]
    haveI : IsProbabilityMeasure (ProbabilityTheory.cond P (Z ⁻¹' ss5_cone σ)) :=
      cond_isProbabilityMeasure_of_finite h (measure_ne_top _ _)
    exact (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance

theorem ss5mNu_supp0 (P : Measure Ω) [IsProbabilityMeasure P] {Z X : Ω → EucConfig 1 N}
    (hZ : Measurable Z) (hX : Measurable X) (σ : Equiv.Perm (Fin N))
    (hXZ : ∀ᵐ ζ ∂(ProbabilityTheory.cond P (Z ⁻¹' ss5_cone σ)), X ζ ∈ ss5_cone σ) :
    ss5mNu P Z X σ (ss5_cone σ)ᶜ = 0 := by
  have hcm : MeasurableSet (ss5_cone σ)ᶜ := (ss5m_cone_open σ).measurableSet.compl
  by_cases h : P (Z ⁻¹' ss5_cone σ) = 0
  · rw [ss5mNu_of_eq h, Measure.dirac_apply' _ hcm]
    simp [Set.indicator, ss5m_wit_mem σ]
  · rw [ss5mNu_of_ne h, Measure.map_apply hX hcm]
    exact ae_iff.mp hXZ

theorem ss5m_mix_law (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → EucConfig 1 N}
    (hZ : Measurable Z) (hdist : ∀ᵐ ζ ∂P, Z ζ ∉ eucCollisionSet 1 N) :
    (∑ σ : Equiv.Perm (Fin N), (P (Z ⁻¹' ss5_cone σ)).toReal = 1) ∧
      ∀ X : Ω → EucConfig 1 N, Measurable X →
        P.map X = ∑ σ : Equiv.Perm (Fin N), ENNReal.ofReal ((P (Z ⁻¹' ss5_cone σ)).toReal) •
          ss5mNu P Z X σ := by
  classical
  have hAm : ∀ σ : Equiv.Perm (Fin N), MeasurableSet (Z ⁻¹' ss5_cone σ) :=
    fun σ => hZ (ss5m_cone_open σ).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint fun σ : Equiv.Perm (Fin N) => Z ⁻¹' ss5_cone σ) :=
    fun σ σ' h => (ss5m_cone_disjoint h).preimage Z
  have hconull : P (⋃ σ : Equiv.Perm (Fin N), Z ⁻¹' ss5_cone σ)ᶜ = 0 := by
    have : (⋃ σ : Equiv.Perm (Fin N), Z ⁻¹' ss5_cone σ) = Z ⁻¹' (eucCollisionSet 1 N)ᶜ := by
      rw [← ss5m_cone_iUnion, Set.preimage_iUnion]
    rw [this, Set.preimage_compl, compl_compl]
    exact measure_eq_zero_iff_ae_notMem.2 hdist
  have hpart : ∀ E : Set Ω, MeasurableSet E →
      P E = ∑ σ : Equiv.Perm (Fin N), P (Z ⁻¹' ss5_cone σ ∩ E) := by
    intro E hE
    have h1 : P (E ∩ ⋃ σ : Equiv.Perm (Fin N), Z ⁻¹' ss5_cone σ) = P E := measure_inter_conull hconull
    have h2 : E ∩ (⋃ σ : Equiv.Perm (Fin N), Z ⁻¹' ss5_cone σ) =
        ⋃ σ : Equiv.Perm (Fin N), (Z ⁻¹' ss5_cone σ ∩ E) := by
      ext x; simp [and_comm]
    rw [← h1, h2, measure_iUnion (fun σ σ' h => (hdisj h).mono Set.inter_subset_left Set.inter_subset_left)
      (fun σ => (hAm σ).inter hE), tsum_fintype]
  refine ⟨?_, ?_⟩
  · have h := hpart Set.univ MeasurableSet.univ
    simp only [Set.inter_univ, measure_univ] at h
    have h3 := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_sum (fun σ _ => measure_ne_top P _)] at h3
    simpa using h3.symm
  · intro X hX
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply hX hS, hpart _ (hX hS), Measure.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    by_cases h : P (Z ⁻¹' ss5_cone σ) = 0
    · have h0 : P (Z ⁻¹' ss5_cone σ ∩ X ⁻¹' S) = 0 := measure_mono_null Set.inter_subset_left h
      rw [h0, h]; simp
    · rw [ss5mNu_of_ne h, Measure.map_apply hX hS, ProbabilityTheory.cond_apply (hAm σ),
        ENNReal.ofReal_toReal (measure_ne_top _ _), ← mul_assoc,
        ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_mul]

/-- On the class `σ`, the ordering permutation is `σ`, and a time-`t` law without mass on the collision set is
carried by the cone. -/
theorem ss5m_comp_support (P : Measure Ω) [IsProbabilityMeasure P] {S : ℝ} (hS0 : 0 ≤ S)
    {Y : ℝ≥0 → Ω → EucConfig 1 N} (hYm : ∀ t, Measurable (Y t)) (hord : SSOrdered P S Y)
    (hdist : ∀ᵐ ζ ∂P, Y 0 ζ ∉ eucCollisionSet 1 N) (σ : Equiv.Perm (Fin N)) (t : ℝ≥0)
    (ht : (t : ℝ) ≤ S)
    (hcoll : (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)).map (Y t) (eucCollisionSet 1 N) = 0) :
    (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)).map (Y t) (ss5_cone σ)ᶜ = 0 := by
  obtain ⟨π, hπm, hπ⟩ := hord
  set Q := ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ) with hQdef
  have hQ : Q ≪ P := ProbabilityTheory.cond_absolutelyContinuous
  have hcm : MeasurableSet (eucCollisionSet 1 N) := ss5m_collision_closed.measurableSet
  rw [Measure.map_apply (hYm t) (ss5m_cone_open σ).measurableSet.compl]
  have hc : Q (Y t ⁻¹' eucCollisionSet 1 N) = 0 := by rwa [Measure.map_apply (hYm t) hcm] at hcoll
  have h1 := measure_eq_zero_iff_ae_notMem.1 hc
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [h1, hQ.ae_le hπ, hQ.ae_le hdist,
    ProbabilityTheory.ae_cond_mem (μ := P) (hYm 0 (ss5m_cone_open σ).measurableSet)] with ζ h1 h2 h3 h4
  have hπσ : π ζ = σ :=
    HRS.MP.SelfSimP1.ssp1c_perm_unique h3
      (fun k k' hk => h2 0 (by simpa using hS0) 0 k k' hk) (ss5m_cone_ord h4)
  show ¬ (Y t ζ ∈ (ss5_cone σ)ᶜ)
  rw [Set.mem_compl_iff, not_not]
  intro k l hkl
  have hh := h2 t ht 0 k l hkl.le
  rw [hπσ] at hh
  refine lt_of_le_of_ne hh fun h => h1 ⟨σ k, σ l, σ.injective.ne hkl.ne, ?_⟩
  ext i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  exact h

end Cond

/-! ### The theorem -/

/-- **1 (mixture over the order classes).**  Statement of `HRS.MP.SelfSimP5.ss5_mixture`. -/
theorem ss5_mixture_proof (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : ℝ≥0 → Ω → EucConfig 1 N} (hYm : ∀ t, Measurable (Y t)) (hYc : ∀ ζ, Continuous fun t => Y t ζ)
    (hord : SSOrdered P S Y) (hdist : ∀ᵐ ζ ∂P, Y 0 ζ ∉ eucCollisionSet 1 N)
    (hH0 : gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law P (Y 0)) < ⊤)
    (hcomp : ∀ σ : Equiv.Perm (Fin N), P (Y 0 ⁻¹' ss5_cone σ) ≠ 0 →
      gibbsEntropyW (selfSimWeight 1 0 invβ N 0)
        (law (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) (Y 0)) < ⊤ →
      SSEntropyIneq 1 0 invβ N S (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) Y) :
    SSEntropyIneq 1 0 invβ N S P Y := by
  classical
  obtain ⟨G, hGdef⟩ : ∃ G : EucConfig 1 N → ℝ, G = selfSimWeight 1 0 invβ N 0 := ⟨_, rfl⟩
  have hGτ : ∀ τ, selfSimWeight 1 0 invβ N τ = G := fun τ => by
    rw [hGdef]; exact ss5m_weight_const N invβ τ
  have hG0 : ∀ ξ ∈ eucCollisionSet 1 N, G ξ = 0 := fun ξ hξ => by
    rw [hGdef]; simp [selfSimWeight, hξ]
  simp only [hGτ] at hH0
  simp only [SSEntropyIneq, hGτ] at hcomp ⊢
  have hAm : ∀ σ : Equiv.Perm (Fin N), MeasurableSet (Y 0 ⁻¹' ss5_cone σ) :=
    fun σ => hYm 0 (ss5m_cone_open σ).measurableSet
  obtain ⟨hsum1', hmix'⟩ := ss5m_mix_law P (hYm 0) hdist
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ≥0 → Equiv.Perm (Fin N) → Measure (EucConfig 1 N),
      ∀ t σ, ν t σ = ss5mNu P (Y 0) (Y t) σ := ⟨fun t σ => ss5mNu P (Y 0) (Y t) σ, fun _ _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Equiv.Perm (Fin N) → ℝ, ∀ σ, p σ = (P (Y 0 ⁻¹' ss5_cone σ)).toReal :=
    ⟨fun σ => (P (Y 0 ⁻¹' ss5_cone σ)).toReal, fun _ => rfl⟩
  have hsum1 : ∑ σ, p σ = 1 := by simp only [hp]; exact hsum1'
  have hp0 : ∀ σ, 0 ≤ p σ := fun σ => by rw [hp]; exact ENNReal.toReal_nonneg
  have hpne : ∀ σ, p σ ≠ 0 ↔ P (Y 0 ⁻¹' ss5_cone σ) ≠ 0 := by
    intro σ
    simp only [hp, ne_eq, ENNReal.toReal_eq_zero_iff, measure_ne_top P _, or_false]
  have hνprob : ∀ t σ, IsProbabilityMeasure (ν t σ) := fun t σ => by
    rw [hν]; exact ss5mNu_prob P (hYm t) σ
  have hmix : ∀ t, law P (Y t) = ∑ σ, ENNReal.ofReal (p σ) • ν t σ := fun t => by
    simp only [hp, hν]; exact hmix' (Y t) (hYm t)
  have hνA : ∀ σ, P (Y 0 ⁻¹' ss5_cone σ) ≠ 0 → ∀ t,
      ν t σ = law (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) (Y t) := fun σ h t => by
    rw [hν]; exact ss5mNu_of_ne h
  -- additivity (H0) at a time `t` where all components live on their cones
  have hH0t : ∀ t : ℝ≥0, (∀ σ, ν t σ (ss5_cone σ)ᶜ = 0) →
      fisherInfoW G (law P (Y t)) = ∑ σ, ENNReal.ofReal (p σ) * fisherInfoW G (ν t σ) ∧
      gibbsEntropyW G (law P (Y t)) = ∑ σ, ((p σ : ℝ) : EReal) * gibbsEntropyW G (ν t σ)
        + ∑ σ, (((p σ * Real.log (p σ)) : ℝ) : EReal) := by
    intro t hsupp
    haveI : ∀ σ, IsProbabilityMeasure (ν t σ) := hνprob t
    rw [hmix t]
    exact ss5m_component_additivity G ss5_cone ss5m_cone_open (fun σ σ' h => ss5m_cone_disjoint h)
      ss5m_cone_iUnion (fun σ => ν t σ) hsupp p hp0 hsum1
  have hc : ∑ σ, (((p σ * Real.log (p σ)) : ℝ) : EReal) = ((∑ σ, p σ * Real.log (p σ) : ℝ) : EReal) :=
    (ss5m_coe_sum _ _)
  -- support at time 0
  have hsupp0 : ∀ σ, ν 0 σ (ss5_cone σ)ᶜ = 0 := fun σ => by
    rw [hν]
    refine ss5mNu_supp0 P (hYm 0) (hYm 0) σ ?_
    exact ProbabilityTheory.ae_cond_mem (μ := P) (hAm σ)
  -- finite conditional entropies at time 0
  have hfin0 : ∀ σ, P (Y 0 ⁻¹' ss5_cone σ) ≠ 0 → gibbsEntropyW G (ν 0 σ) < ⊤ := by
    intro σ hσ
    have h := (hH0t 0 hsupp0).2
    rw [h, hc] at hH0
    exact ss5m_components_lt_top p hp0 (fun σ => gibbsEntropyW G (ν 0 σ))
      (fun σ => ss5m_gibbsEntropyW_ne_bot G _) _ (EReal.coe_ne_bot _) (EReal.coe_ne_top _) hH0 σ
      ((hpne σ).2 hσ)
  -- the component inequalities
  have hineq : ∀ σ, P (Y 0 ⁻¹' ss5_cone σ) ≠ 0 → ∀ τ ∈ Icc (0 : ℝ) S,
      gibbsEntropyW G (ν (Real.toNNReal τ) σ) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Icc (0 : ℝ) τ, fisherInfoW G (ν (Real.toNNReal r) σ) : ℝ≥0∞) : EReal)
        ≤ gibbsEntropyW G (ν 0 σ) := by
    intro σ hσ τ hτ
    have h := hcomp σ hσ (by rw [← hνA σ hσ 0]; exact hfin0 σ hσ) τ hτ
    simpa only [hνA σ hσ] using h
  -- support at times in `[0,S]`
  have hsuppT : ∀ σ, ∀ τ ∈ Icc (0 : ℝ) S, ν (Real.toNNReal τ) σ (ss5_cone σ)ᶜ = 0 := by
    intro σ τ hτ
    by_cases h : P (Y 0 ⁻¹' ss5_cone σ) = 0
    · rw [hν, ss5mNu_of_eq h, Measure.dirac_apply' _ (ss5m_cone_open σ).measurableSet.compl]
      simp [Set.indicator, ss5m_wit_mem σ]
    · have hσ : P (Y 0 ⁻¹' ss5_cone σ) ≠ 0 := h
      haveI : IsProbabilityMeasure (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) :=
        cond_isProbabilityMeasure_of_finite hσ (measure_ne_top _ _)
      have hH := hineq σ hσ τ hτ
      have hlt : gibbsEntropyW G (ν (Real.toNNReal τ) σ) < ⊤ := by
        by_contra hcon
        have htop : gibbsEntropyW G (ν (Real.toNNReal τ) σ) = ⊤ := top_le_iff.1 (not_lt.1 hcon)
        rw [htop, EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _)] at hH
        exact absurd (lt_of_le_of_lt hH (hfin0 σ hσ)) (lt_irrefl _)
      have hνa := hνA σ hσ (Real.toNNReal τ)
      rw [hνa] at hlt ⊢
      haveI : IsProbabilityMeasure (law (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) (Y (Real.toNNReal τ))) :=
        inferInstanceAs (IsProbabilityMeasure ((ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)).map _))
      have hcoll := ss5m_fin_null G hG0 _ hlt
      exact ss5m_comp_support P hS.le hYm hord hdist σ (Real.toNNReal τ)
        (by rw [Real.coe_toNNReal τ hτ.1]; exact hτ.2) hcoll
  -- measurability in time of the component Fisher informations
  have hfm : ∀ σ, Measurable fun r : ℝ => fisherInfoW G (ν (Real.toNNReal r) σ) := by
    intro σ
    by_cases h : P (Y 0 ⁻¹' ss5_cone σ) = 0
    · have : (fun r : ℝ => fisherInfoW G (ν (Real.toNNReal r) σ)) =
          fun _ => fisherInfoW G (Measure.dirac (ss5m_wit σ)) := by
        funext r; rw [hν, ss5mNu_of_eq h]
      rw [this]; exact measurable_const
    · haveI : IsProbabilityMeasure (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) :=
        cond_isProbabilityMeasure_of_finite h (measure_ne_top _ _)
      have e : (fun r : ℝ => fisherInfoW G (ν (Real.toNNReal r) σ)) =
          fun r : ℝ => fisherInfoW G
            (law (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) (Y (Real.toNNReal r))) :=
        funext fun r => by rw [hνA σ h]
      rw [e, hGdef]
      exact ss5m_fisher_meas (d := 1) (N := N) invβ 0 _ hYm hYc
  intro τ hτ
  have hIcc : ∀ r ∈ Icc (0 : ℝ) τ, r ∈ Icc (0 : ℝ) S := fun r hr => ⟨hr.1, hr.2.trans hτ.2⟩
  have hfisher : (∫⁻ r in Icc (0 : ℝ) τ, fisherInfoW G (law P (Y (Real.toNNReal r)))) =
      ∑ σ, ENNReal.ofReal (p σ) * ∫⁻ r in Icc (0 : ℝ) τ, fisherInfoW G (ν (Real.toNNReal r) σ) := by
    rw [setLIntegral_congr_fun measurableSet_Icc
      (g := fun r => ∑ σ, ENNReal.ofReal (p σ) * fisherInfoW G (ν (Real.toNNReal r) σ))
      (fun r hr => (hH0t _ (fun σ => hsuppT σ r (hIcc r hr))).1)]
    rw [lintegral_finset_sum']
    · exact Finset.sum_congr rfl fun σ _ => lintegral_const_mul'' _ (hfm σ).aemeasurable
    · intro σ _
      exact ((hfm σ).const_mul _).aemeasurable
  have hF' : ENNReal.ofReal invβ * ∫⁻ r in Icc (0 : ℝ) τ, fisherInfoW G (law P (Y (Real.toNNReal r))) =
      ∑ σ, ENNReal.ofReal (p σ) *
        (ENNReal.ofReal invβ * ∫⁻ r in Icc (0 : ℝ) τ, fisherInfoW G (ν (Real.toNNReal r) σ)) := by
    rw [hfisher, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => mul_left_comm _ _ _
  rw [hF', (hH0t (Real.toNNReal τ) (fun σ => hsuppT σ τ hτ)).2, (hH0t 0 hsupp0).2, hc]
  refine ss5m_recombine p hp0 (fun σ => gibbsEntropyW G (ν (Real.toNNReal τ) σ))
    (fun σ => gibbsEntropyW G (ν 0 σ))
    (fun σ => ENNReal.ofReal invβ * ∫⁻ r in Icc (0 : ℝ) τ, fisherInfoW G (ν (Real.toNNReal r) σ))
    (fun σ => ss5m_gibbsEntropyW_ne_bot G _) (fun σ => ss5m_gibbsEntropyW_ne_bot G _) ?_ _
    (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
  intro σ hσ
  have hg : P (Y 0 ⁻¹' ss5_cone σ) ≠ 0 := (hpne σ).1 hσ
  exact ⟨hfin0 σ hg, hineq σ hg τ hτ⟩

example := (@ss5_mixture_proof : type_of% @HRS.MP.SelfSimP5.ss5_mixture)

end HRS.MP.SelfSimP5Impl
