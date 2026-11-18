import HRS.MC.CepH0Aux4
import HRS.MC.CepH0Aux5
import HRS.Whole.AppendixALemmas2

/-!
# MPP5C (1a): additivity of the Gibbs entropy and of the Fisher information over disjoint open components, on `ℝ^{dN}`

Port of `HRS/MC/CepH0Aux6-8.lean` (`cep_H0_component_additivity`) from the torus configuration space to
`EucConfig d N` with an arbitrary weight `G`.  The abstract Kullback-Leibler mixture lemmas
(`CepH0Aux1-5`) are imported as they are.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MC.CepH0
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MP.SelfSimP5Impl

variable {d N : ℕ}

/-! ### Gibbs entropy -/

theorem ss5m_ref_cases (G : EucConfig d N → ℝ) :
    IsProbabilityMeasure (gibbsRefW G) ∨ gibbsRefW G = 0 := by
  by_cases hZ : gibbsPartitionW G = 0 ∨ gibbsPartitionW G = ⊤
  · right
    rcases hZ with hZ | hZ
    · unfold gibbsRefW
      have : (volume : Measure (EucConfig d N)).withDensity (fun X => ENNReal.ofReal (G X)) = 0 := by
        refine Measure.ext fun s _ => ?_
        rw [withDensity_apply']
        refine le_antisymm ?_ bot_le
        calc ∫⁻ a in s, ENNReal.ofReal (G a) ≤ ∫⁻ a, ENNReal.ofReal (G a) :=
              setLIntegral_le_lintegral _ _
          _ = 0 := hZ
      rw [this, smul_zero]
    · unfold gibbsRefW; rw [hZ]; simp
  · left
    push_neg at hZ
    refine ⟨?_⟩
    unfold gibbsRefW
    rw [Measure.smul_apply, withDensity_apply' _ Set.univ, Measure.restrict_univ]
    change (gibbsPartitionW G)⁻¹ * gibbsPartitionW G = 1
    exact ENNReal.inv_mul_cancel hZ.1 hZ.2

theorem ss5m_gibbsEntropy_mix (G : EucConfig d N → ℝ) {ι : Type*} [Fintype ι] (C : ι → Set (EucConfig d N))
    (hCo : ∀ c, IsOpen (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (ν : ι → Measure (EucConfig d N)) [∀ c, IsProbabilityMeasure (ν c)]
    (hν : ∀ c, ν c (C c)ᶜ = 0) (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    gibbsEntropyW G (∑ c, ENNReal.ofReal (p c) • ν c) =
      ∑ c, ((p c : ℝ) : EReal) * gibbsEntropyW G (ν c) + ∑ c, (((p c * Real.log (p c)) : ℝ) : EReal) := by
  classical
  haveI := h0mix_prob p hp0 hp1 ν
  change gibbsEntropyW G (h0mix p ν) = _
  unfold gibbsEntropyW
  have hCm : ∀ c, MeasurableSet (C c) := fun c => (hCo c).measurableSet
  have hex : ∃ c, 0 < p c := by
    by_contra hcon
    push_neg at hcon
    have : ∑ c, p c = 0 := Finset.sum_eq_zero fun c _ => le_antisymm (hcon c) (hp0 c)
    rw [this] at hp1
    exact zero_ne_one hp1
  refine h0_ereal_mix (fun c => relEntropy (ν c) (gibbsRefW G)) (relEntropy (h0mix p ν) (gibbsRefW G))
    (Real.log (gibbsPartitionW G).toReal) p hp0 hp1 ?_ ?_
  · rintro ⟨c, hc, hk⟩
    rcases ss5m_ref_cases (d := d) (N := N) G with h | h
    · exact h0_klDiv_mix_top (gibbsRefW G) C hCm hCd ν hν p hp0 hp1 ⟨c, hc, hk⟩
    · unfold relEntropy; rw [h]; exact klDiv_zero_right
  · intro hfin
    rcases ss5m_ref_cases (d := d) (N := N) G with h | h
    · exact h0_klDiv_mix_finite (gibbsRefW G) C hCm hCd ν hν p hp0 hp1 hfin
    · exfalso
      obtain ⟨c, hc⟩ := hex
      refine hfin c hc ?_
      unfold relEntropy; rw [h]; exact klDiv_zero_right

/-! ### Fisher information -/

/-- The integrand of the variational formula of `fisherInfoW`. -/
def ss5mF (G : EucConfig d N → ℝ) (ζ : EucConfig d N → EucConfig d N) (X : EucConfig d N) : ℝ :=
  -2 * configDivW ζ X - 2 * fderiv ℝ (fun Z : EucConfig d N => Real.log (G Z)) X (ζ X) -
        ∑ i, ‖ζ X i‖ ^ 2

theorem ss5m_fisher_eq (G : EucConfig d N → ℝ) (P : Measure (EucConfig d N)) :
    fisherInfoW G P = ⨆ (ζ : EucConfig d N → EucConfig d N) (_ : IsFisherTestFieldW ζ),
      ENNReal.ofReal (∫ X, ss5mF G ζ X ∂P) := rfl

theorem ss5mF_congr_of_eq_on (G : EucConfig d N → ℝ) {ζ ζ' : EucConfig d N → EucConfig d N}
    {U : Set (EucConfig d N)} (hU : IsOpen U) (h : ∀ X ∈ U, ζ X = ζ' X) {X : EucConfig d N}
    (hX : X ∈ U) : ss5mF G ζ X = ss5mF G ζ' X := by
  have hζ : ζ X = ζ' X := h X hX
  have hdiv : configDivW ζ X = configDivW ζ' X := by
    unfold configDivW
    refine Finset.sum_congr rfl fun k _ => ?_
    have hev : (fun Z : EucConfig d N => ζ Z k.1 k.2) =ᶠ[𝓝 X] (fun Z : EucConfig d N => ζ' Z k.1 k.2) := by
      filter_upwards [hU.mem_nhds hX] with Z hZ
      rw [h _ hZ]
    rw [hev.fderiv_eq]
  unfold ss5mF
  rw [hdiv, hζ]

theorem ss5m_piece_smooth {n : WithTop ℕ∞} (S : Set (EucConfig d N)) (hSo : IsOpen S)
    (K : Set (EucConfig d N)) (hK : IsClosed K) (ζc : EucConfig d N → EucConfig d N)
    (hsm : ContDiff ℝ n ζc) (hsupp : ∀ X, X ∉ K → ζc X = 0)
    (hKS : ∀ X ∈ K, X ∉ S → ∃ S' : Set (EucConfig d N), IsOpen S' ∧ X ∈ S' ∧ Disjoint S' S) :
    ContDiff ℝ n (S.indicator ζc) := by
  rw [contDiff_iff_contDiffAt]
  intro Y
  by_cases hY : Y ∈ S
  · refine (hsm.contDiffAt (x := Y)).congr_of_eventuallyEq ?_
    filter_upwards [hSo.mem_nhds hY] with Z hZ
    exact Set.indicator_of_mem (s := S) hZ ζc
  · have hz : S.indicator ζc =ᶠ[𝓝 Y] fun _ => (0 : EucConfig d N) := by
      by_cases hYK : Y ∈ K
      · obtain ⟨S', hS'o, hYS', hS'd⟩ := hKS _ hYK hY
        filter_upwards [hS'o.mem_nhds hYS'] with Z hZ
        exact Set.indicator_of_notMem (fun hm => Set.disjoint_left.mp hS'd hZ hm) _
      · filter_upwards [hK.isOpen_compl.mem_nhds hYK] with Z hZ
        by_cases hm : Z ∈ S
        · rw [Set.indicator_of_mem hm]; exact hsupp _ hZ
        · exact Set.indicator_of_notMem hm _
    exact (contDiffAt_const : ContDiffAt ℝ n (fun _ : EucConfig d N => (0 : EucConfig d N)) Y).congr_of_eventuallyEq hz

theorem ss5m_glue {ι : Type*} [Fintype ι] (C : ι → Set (EucConfig d N)) (hCo : ∀ c, IsOpen (C c))
    (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (hCc : (⋃ c, C c) = (eucCollisionSet d N)ᶜ)
    (ζs : ι → EucConfig d N → EucConfig d N) (hζ : ∀ c, IsFisherTestFieldW (ζs c)) :
    IsFisherTestFieldW (fun X => ∑ c, (C c).indicator (ζs c) X) ∧
      ∀ c, ∀ X ∈ C c, (∑ c', (C c').indicator (ζs c') X) = ζs c X := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine ContDiff.sum fun c _ => ?_
    obtain ⟨K, hKc, hKd, hKs⟩ := (hζ c).support
    refine ss5m_piece_smooth (C c) (hCo c) K hKc.isClosed (ζs c) (hζ c).smooth hKs ?_
    intro X hXK hXC
    have hXn : X ∉ eucCollisionSet d N := fun h => Set.disjoint_left.mp hKd hXK h
    have : X ∈ ⋃ c, C c := by rw [hCc]; exact hXn
    obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp this
    have hne : c' ≠ c := fun h => hXC (h ▸ hc')
    exact ⟨C c', hCo c', hc', hCd hne⟩
  · choose K hKc hKd hKs using fun c => (hζ c).support
    refine ⟨⋃ c, K c, isCompact_iUnion hKc, ?_, ?_⟩
    · rw [Set.disjoint_iUnion_left]; exact hKd
    · intro X hX
      refine Finset.sum_eq_zero fun c _ => ?_
      have : X ∉ K c := fun h => hX (Set.mem_iUnion.mpr ⟨c, h⟩)
      by_cases hm : X ∈ C c
      · rw [Set.indicator_of_mem hm]; exact hKs c X this
      · exact Set.indicator_of_notMem hm _
  · intro c X hX
    rw [Finset.sum_eq_single c]
    · exact Set.indicator_of_mem hX _
    · intro c' _ hc'
      exact Set.indicator_of_notMem (fun h => Set.disjoint_left.mp (hCd hc') h hX) _
    · simp

theorem ss5m_ofReal_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ENNReal.ofReal (∑ c ∈ s, x c) ≤ ∑ c ∈ s, ENNReal.ofReal (x c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.ofReal_add_le).trans (add_le_add_right ih _)

theorem ss5m_testField_zero : IsFisherTestFieldW (d := d) (N := N) (fun _ => (0 : EucConfig d N)) :=
  ⟨contDiff_const, ∅, isCompact_empty, Set.empty_disjoint _, fun _ _ => rfl⟩

theorem ss5mF_zero (G : EucConfig d N → ℝ) : ss5mF G (fun _ => (0 : EucConfig d N)) = fun _ => 0 := by
  funext X
  simp [ss5mF, configDivW]

abbrev Ss5mA (d N : ℕ) := {ζ : EucConfig d N → EucConfig d N // IsFisherTestFieldW ζ}

theorem ss5m_pick (G : EucConfig d N → ℝ) (ν : Measure (EucConfig d N)) [IsFiniteMeasure ν]
    (a : Ss5mA d N) :
    ∃ b : Ss5mA d N,
      Integrable (ss5mF G b.1) ν ∧ 0 ≤ ∫ X, ss5mF G b.1 X ∂ν ∧
        ENNReal.ofReal (∫ X, ss5mF G a.1 X ∂ν) = ENNReal.ofReal (∫ X, ss5mF G b.1 X ∂ν) := by
  by_cases h : Integrable (ss5mF G a.1) ν ∧ 0 ≤ ∫ X, ss5mF G a.1 X ∂ν
  · exact ⟨a, h.1, h.2, rfl⟩
  · refine ⟨⟨_, ss5m_testField_zero⟩, ?_, ?_, ?_⟩
    · simp only [ss5mF_zero]; exact integrable_zero _ _ _
    · simp [ss5mF_zero]
    · simp only [ss5mF_zero, integral_zero]
      by_cases hi : Integrable (ss5mF G a.1) ν
      · have : ∫ X, ss5mF G a.1 X ∂ν < 0 := by
          by_contra hn
          exact h ⟨hi, not_lt.mp hn⟩
        simp [ENNReal.ofReal_of_nonpos this.le]
      · simp [integral_undef hi]

theorem ss5m_fisher_mix_le {ι : Type*} [Fintype ι] (G : EucConfig d N → ℝ)
    (ν : ι → Measure (EucConfig d N)) [∀ c, IsProbabilityMeasure (ν c)] (p : ι → ℝ)
    (hp0 : ∀ c, 0 ≤ p c) :
    fisherInfoW G (h0mix p ν) ≤ ∑ c, ENNReal.ofReal (p c) * fisherInfoW G (ν c) := by
  rw [ss5m_fisher_eq]
  refine iSup₂_le fun ζ hζ => ?_
  by_cases hI : Integrable (ss5mF G ζ) (h0mix p ν)
  · have hpiece : ∀ c, Integrable (ss5mF G ζ) (ENNReal.ofReal (p c) • ν c) :=
      fun c => hI.mono_measure (h0_smul_le_mix p ν c)
    have e : ∫ X, ss5mF G ζ X ∂(h0mix p ν) =
        ∑ c, ∫ X, ss5mF G ζ X ∂(ENNReal.ofReal (p c) • ν c) :=
      integral_finset_sum_measure (fun c _ => hpiece c)
    simp_rw [integral_smul_measure, ENNReal.toReal_ofReal (hp0 _), smul_eq_mul] at e
    rw [e]
    refine (ss5m_ofReal_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [ENNReal.ofReal_mul (hp0 c)]
    refine mul_le_mul_right ?_ _
    rw [ss5m_fisher_eq]
    exact le_iSup₂ (f := fun (ζ : EucConfig d N → EucConfig d N) (_ : IsFisherTestFieldW ζ) =>
      ENNReal.ofReal (∫ X, ss5mF G ζ X ∂(ν c))) ζ hζ
  · rw [integral_undef hI]; simp

theorem ss5m_fisher_mix_ge {ι : Type*} [Fintype ι] (G : EucConfig d N → ℝ) (C : ι → Set (EucConfig d N))
    (hCo : ∀ c, IsOpen (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (hCc : (⋃ c, C c) = (eucCollisionSet d N)ᶜ)
    (ν : ι → Measure (EucConfig d N)) [∀ c, IsProbabilityMeasure (ν c)]
    (hν : ∀ c, ν c (C c)ᶜ = 0) (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    ∑ c, ENNReal.ofReal (p c) * fisherInfoW G (ν c) ≤ fisherInfoW G (h0mix p ν) := by
  classical
  haveI : Nonempty (Ss5mA d N) := ⟨⟨_, ss5m_testField_zero⟩⟩
  have hfc : ∀ c, fisherInfoW G (ν c) =
      ⨆ ζ : Ss5mA d N, ENNReal.ofReal (∫ X, ss5mF G ζ.1 X ∂(ν c)) := by
    intro c
    rw [ss5m_fisher_eq, iSup_subtype']
  calc ∑ c, ENNReal.ofReal (p c) * fisherInfoW G (ν c)
      = ∑ c, ⨆ ζ : Ss5mA d N, ENNReal.ofReal (p c) * ENNReal.ofReal (∫ X, ss5mF G ζ.1 X ∂(ν c)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hfc c, ENNReal.mul_iSup]
    _ ≤ ⨆ a : ι → Ss5mA d N, ∑ c, ENNReal.ofReal (p c) * ENNReal.ofReal (∫ X, ss5mF G (a c).1 X ∂(ν c)) :=
        h0_sum_iSup_le (A := fun _ : ι => Ss5mA d N) Finset.univ (fun c (ζ : Ss5mA d N) =>
          ENNReal.ofReal (p c) * ENNReal.ofReal (∫ X, ss5mF G ζ.1 X ∂(ν c)))
    _ ≤ fisherInfoW G (h0mix p ν) := by
        refine iSup_le fun a => ?_
        choose b hbint hbnn hbeq using fun c => ss5m_pick G (ν c) (a c)
        obtain ⟨hgl, hgeq⟩ := ss5m_glue C hCo hCd hCc (fun c => (b c).1) (fun c => (b c).2)
        set ζ : EucConfig d N → EucConfig d N := fun X => ∑ c, (C c).indicator (b c).1 X with hζdef
        have hae : ∀ c, ∀ᵐ X ∂(ν c), ss5mF G ζ X = ss5mF G (b c).1 X := by
          intro c
          have : ∀ᵐ X ∂(ν c), X ∈ C c := by
            rw [ae_iff]; exact hν c
          filter_upwards [this] with X hX
          exact ss5mF_congr_of_eq_on G (hCo c) (fun Y hY => hgeq c Y hY) hX
        have hint : ∀ c, Integrable (ss5mF G ζ) (ν c) :=
          fun c => (hbint c).congr (Filter.EventuallyEq.symm (hae c))
        have hpiece : ∀ c, Integrable (ss5mF G ζ) (ENNReal.ofReal (p c) • ν c) :=
          fun c => (hint c).smul_measure ENNReal.ofReal_ne_top
        have e : ∫ X, ss5mF G ζ X ∂(h0mix p ν) =
            ∑ c, ∫ X, ss5mF G ζ X ∂(ENNReal.ofReal (p c) • ν c) :=
          integral_finset_sum_measure (fun c _ => hpiece c)
        simp_rw [integral_smul_measure, ENNReal.toReal_ofReal (hp0 _), smul_eq_mul] at e
        have e2 : ∀ c, ∫ X, ss5mF G ζ X ∂(ν c) = ∫ X, ss5mF G (b c).1 X ∂(ν c) :=
          fun c => integral_congr_ae (hae c)
        simp_rw [e2] at e
        calc ∑ c, ENNReal.ofReal (p c) * ENNReal.ofReal (∫ X, ss5mF G (a c).1 X ∂(ν c))
            = ∑ c, ENNReal.ofReal (p c * ∫ X, ss5mF G (b c).1 X ∂(ν c)) := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [hbeq c, ENNReal.ofReal_mul (hp0 c)]
          _ = ENNReal.ofReal (∫ X, ss5mF G ζ X ∂(h0mix p ν)) := by
              rw [e, ENNReal.ofReal_sum_of_nonneg (fun c _ => mul_nonneg (hp0 c) (hbnn c))]
          _ ≤ _ := by
              rw [ss5m_fisher_eq]
              exact le_iSup₂ (f := fun (ζ : EucConfig d N → EucConfig d N)
                (_ : IsFisherTestFieldW ζ) =>
                ENNReal.ofReal (∫ X, ss5mF G ζ X ∂(h0mix p ν))) ζ hgl

theorem ss5m_fisher_mix {ι : Type*} [Fintype ι] (G : EucConfig d N → ℝ) (C : ι → Set (EucConfig d N))
    (hCo : ∀ c, IsOpen (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (hCc : (⋃ c, C c) = (eucCollisionSet d N)ᶜ)
    (ν : ι → Measure (EucConfig d N)) [∀ c, IsProbabilityMeasure (ν c)]
    (hν : ∀ c, ν c (C c)ᶜ = 0) (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    fisherInfoW G (∑ c, ENNReal.ofReal (p c) • ν c) = ∑ c, ENNReal.ofReal (p c) * fisherInfoW G (ν c) :=
  le_antisymm (ss5m_fisher_mix_le G ν p hp0) (ss5m_fisher_mix_ge G C hCo hCd hCc ν hν p hp0 hp1)

/-- **(1a)** Additivity over disjoint open components covering the collision-free space. -/
theorem ss5m_component_additivity {ι : Type*} [Fintype ι] (G : EucConfig d N → ℝ)
    (C : ι → Set (EucConfig d N))
    (hCo : ∀ c, IsOpen (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (hCc : (⋃ c, C c) = (eucCollisionSet d N)ᶜ)
    (ν : ι → Measure (EucConfig d N)) [∀ c, IsProbabilityMeasure (ν c)]
    (hν : ∀ c, ν c (C c)ᶜ = 0) (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    fisherInfoW G (∑ c, ENNReal.ofReal (p c) • ν c) =
        ∑ c, ENNReal.ofReal (p c) * fisherInfoW G (ν c) ∧
    gibbsEntropyW G (∑ c, ENNReal.ofReal (p c) • ν c) =
      ∑ c, ((p c : ℝ) : EReal) * gibbsEntropyW G (ν c) + ∑ c, (((p c * Real.log (p c)) : ℝ) : EReal) :=
  ⟨ss5m_fisher_mix G C hCo hCd hCc ν hν p hp0 hp1, ss5m_gibbsEntropy_mix G C hCo hCd ν hν p hp0 hp1⟩

end HRS.MP.SelfSimP5Impl
