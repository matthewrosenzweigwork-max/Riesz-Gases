import HRS.MS.CritWholeW2Shift
import HRS.MS.GenPathAux41
import HRS.Main.GFB3Aux5
import HRS.Main.T25PAux21

/-!
# S8.1 (worker S81S): transport lemmas along a measure-preserving extension

Namespace `HRS.Whole.S81S`, prefix `s81s_`.

* `s81s_indep_comp`: independence of two sub-σ-algebras is preserved by pulling back along a measure-preserving map.
* `s81s_iIndep3`: three processes `G 0, G 1, G 2` are jointly independent if `G 0, G 1` are `𝒢`-measurable and independent,
  and `G 2` is independent of `𝒢`.
* `s81s_zeta_comp`: the exactly centered particle window of `X ∘ π` under `Q` is the window of `X` under `P` composed with `π`.
* `s81s_canonical_comp`: a canonical realization pulled back along a measure-preserving `π`, carrying a filtered form for an
  enlarged filtration, is a canonical realization (Pro R26-T2.K01).
* `s81s_cyl_shift`: the shifted cylindrical Brownian motion of the shifted filtration.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81S

section Indep

theorem s81s_indep_comp {Ω Ω' : Type*} (𝒜 ℬ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω']
    [mΩ₀ : MeasurableSpace Ω]
    {P : Measure Ω} {Q : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π Q P)
    (h𝒜 : 𝒜 ≤ mΩ₀) (hℬ : ℬ ≤ mΩ₀) (h : Indep 𝒜 ℬ P) :
    Indep (𝒜.comap π) (ℬ.comap π) Q := by
  rw [Indep_iff] at h ⊢
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  have hA' : MeasurableSet A := h𝒜 _ hA
  have hB' : MeasurableSet B := hℬ _ hB
  rw [← Set.preimage_inter, hπ.measure_preimage (hA'.inter hB').nullMeasurableSet,
    hπ.measure_preimage hA'.nullMeasurableSet, hπ.measure_preimage hB'.nullMeasurableSet]
  exact h A B hA hB

/-- Three processes: `G 0`, `G 1` measurable for `𝒢` and independent, `G 2` independent of `𝒢`. -/
theorem s81s_iIndep3 {Ω E : Type*} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E] {Q : Measure Ω}
    [IsProbabilityMeasure Q] (G : Fin 3 → Ω → E) (h𝒢 : 𝒢 ≤ mΩ)
    (h0 : @Measurable Ω E 𝒢 _ (G 0)) (h1 : @Measurable Ω E 𝒢 _ (G 1))
    (h2 : Measurable (G 2)) (h01 : IndepFun (G 0) (G 1) Q)
    (hind : Indep 𝒢 (MeasurableSpace.comap (G 2) inferInstance) Q) : iIndepFun G Q := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  classical
  set s' : Fin 3 → Set E := fun i => if i ∈ S then sets i else Set.univ with hs'
  have hs'm : ∀ i, MeasurableSet (s' i) := fun i => by
    by_cases hi : i ∈ S
    · simp only [hs', hi, ite_true]; exact hsets i hi
    · simp only [hs', hi, ite_false]; exact MeasurableSet.univ
  have e1 : ⋂ i ∈ S, G i ⁻¹' sets i = G 0 ⁻¹' s' 0 ∩ G 1 ⁻¹' s' 1 ∩ G 2 ⁻¹' s' 2 := by
    ext z
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff, hs']
    constructor
    · intro hz
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> (split_ifs with hi; exact hz _ hi; trivial)
    · rintro ⟨⟨a, b⟩, c⟩ i hi
      fin_cases i
      · exact (by simpa using a : 0 ∈ S → G 0 z ∈ sets 0) hi
      · exact (by simpa using b : 1 ∈ S → G 1 z ∈ sets 1) hi
      · exact (by simpa using c : 2 ∈ S → G 2 z ∈ sets 2) hi
  have e2 : ∏ i ∈ S, Q (G i ⁻¹' sets i) = Q (G 0 ⁻¹' s' 0) * Q (G 1 ⁻¹' s' 1) * Q (G 2 ⁻¹' s' 2) := by
    have : ∏ i ∈ S, Q (G i ⁻¹' sets i) = ∏ i : Fin 3, Q (G i ⁻¹' s' i) := by
      rw [← Finset.prod_subset (Finset.subset_univ S)]
      · exact Finset.prod_congr rfl fun i hi => by simp [hs', hi]
      · intro i _ hi
        simp [hs', hi]
    rw [this, Fin.prod_univ_three]
  rw [e1, e2]
  have hA0 : MeasurableSet[𝒢] (G 0 ⁻¹' s' 0) := h0 (hs'm 0)
  have hA1 : MeasurableSet[𝒢] (G 1 ⁻¹' s' 1) := h1 (hs'm 1)
  have hB : MeasurableSet[MeasurableSpace.comap (G 2) inferInstance] (G 2 ⁻¹' s' 2) := ⟨_, hs'm 2, rfl⟩
  have hAB : MeasurableSet[𝒢] (G 0 ⁻¹' s' 0 ∩ G 1 ⁻¹' s' 1) := hA0.inter hA1
  rw [(Indep_iff _ _ _).1 hind _ _ hAB hB]
  congr 1
  exact h01.measure_inter_preimage_eq_mul _ _ (hs'm 0) (hs'm 1)

end Indep

section Zeta

variable {d N : ℕ}

theorem s81s_map_comp {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    {P : Measure Ω} {Q : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π Q P)
    {f : Ω → E} (hf : Measurable f) : Q.map (fun z => f (π z)) = P.map f := by
  have : (fun z => f (π z)) = f ∘ π := rfl
  rw [this, ← Measure.map_map hf hπ.measurable, hπ.map_eq]

theorem s81s_zeta_comp {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    (Q : Measure Ω') (π : Ω' → Ω) (hπ : MeasurePreserving π Q P) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : ∀ t, Measurable (X t)) (m T u : ℝ) :
    zetaPathW m T u Q (fun t z => X t (π z)) = fun z => zetaPathW m T u P X (π z) := by
  funext z
  unfold zetaPathW
  have h : ∀ s : ℝ≥0, Q.map (fun z => X s (π z)) = P.map (X s) := fun s => s81s_map_comp hπ (hX s)
  simp only [h]

end Zeta

section Canonical

variable {d N : ℕ} {s a β : ℝ}

theorem s81s_canonical_comp {Ω Ω' : Type} [MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {π : Ω' → Ω} (hπ : MeasurePreserving π Q P)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hR : IsCanonicalRealization d s a β N P X₀ W X)
    (ℱ' : Filtration ℝ mΩ') (W'' : ℝ≥0 → Ω' → (Fin N × Fin d) → ℝ)
    (hF : IsWholeFilteredSolution Q ℱ' W'' (fun t z => W t (π z)) (fun t z => X t (π z))) :
    IsCanonicalRealization d s a β N Q (fun z => X₀ (π z)) (fun t z => W t (π z))
      (fun t z => X t (π z)) where
  brownian := by
    have hWc : ∀ i j, AEMeasurable (fun ω => (fun t : ℝ≥0 => W t ω i j)) P := fun i j =>
      HRS.T25P.t25p_aemeasurable_path
        (fun t => (hR.brownian.1 i j).toIsPreBrownianReal.aemeasurable t) (hR.brownian.1 i j).cont
    refine ⟨fun i j => ?_, ?_⟩
    · have h := hR.brownian.1 i j
      refine ⟨⟨fun I => ?_⟩, hπ.quasiMeasurePreserving.ae h.cont⟩
      exact (h.toIsPreBrownianReal.hasLaw I).comp hπ.hasLaw
    · exact HRS.T25P.t25p_iIndepFun_comp hπ (fun ij : Fin N × Fin d => hWc ij.1 ij.2) hR.brownian.2
  indep := by
    have hX₀ : AEMeasurable X₀ P := ((hR.solution 0).adapted 0).aemeasurable.congr (hR.solution 0).init
    have hWp : AEMeasurable (fun ω => fun t : ℝ≥0 => W t ω) P :=
      HRS.T25P.t25p_aemeasurable_path (fun t => HRS.T25P.t25p_vecBrownian_aemeas hR.brownian t)
        (HRS.T25P.t25p_vecBrownian_cont hR.brownian)
    have hpair : AEMeasurable (fun ω => (X₀ ω, fun t : ℝ≥0 => W t ω)) P := hX₀.prodMk hWp
    have h1 := (indepFun_iff_map_prod_eq_prod_map_map hX₀ hWp).1 hR.indep
    have hf1 : AEMeasurable (fun ω' => X₀ (π ω')) Q := by
      have : AEMeasurable X₀ (Q.map π) := by rw [hπ.map_eq]; exact hX₀
      exact this.comp_aemeasurable hπ.aemeasurable
    have hf2 : AEMeasurable (fun ω' => fun t : ℝ≥0 => W t (π ω')) Q := by
      have : AEMeasurable (fun ω => fun t : ℝ≥0 => W t ω) (Q.map π) := by rw [hπ.map_eq]; exact hWp
      exact this.comp_aemeasurable hπ.aemeasurable
    refine (indepFun_iff_map_prod_eq_prod_map_map hf1 hf2).2 ?_
    have e1 : Q.map (fun ω' => (X₀ (π ω'), fun t : ℝ≥0 => W t (π ω'))) =
        P.map (fun ω => (X₀ ω, fun t : ℝ≥0 => W t ω)) := by
      have : AEMeasurable (fun ω => (X₀ ω, fun t : ℝ≥0 => W t ω)) (Q.map π) := by
        rw [hπ.map_eq]; exact hpair
      rw [← hπ.map_eq]
      exact (AEMeasurable.map_map_of_aemeasurable this hπ.aemeasurable).symm
    have e2 : Q.map (fun ω' => X₀ (π ω')) = P.map X₀ := by
      have : AEMeasurable X₀ (Q.map π) := by rw [hπ.map_eq]; exact hX₀
      rw [← hπ.map_eq]
      exact (AEMeasurable.map_map_of_aemeasurable this hπ.aemeasurable).symm
    have e3 : Q.map (fun ω' => fun t : ℝ≥0 => W t (π ω')) = P.map (fun ω => fun t : ℝ≥0 => W t ω) := by
      have : AEMeasurable (fun ω => fun t : ℝ≥0 => W t ω) (Q.map π) := by rw [hπ.map_eq]; exact hWp
      rw [← hπ.map_eq]
      exact (AEMeasurable.map_map_of_aemeasurable this hπ.aemeasurable).symm
    rw [e1, e2, e3]
    exact h1
  init := by
    have hX₀ : AEMeasurable X₀ P := ((hR.solution 0).adapted 0).aemeasurable.congr (hR.solution 0).init
    have : AEMeasurable X₀ (Q.map π) := by rw [hπ.map_eq]; exact hX₀
    rw [← hR.init]
    show Q.map (X₀ ∘ π) = P.map X₀
    rw [← hπ.map_eq]
    exact (AEMeasurable.map_map_of_aemeasurable this hπ.aemeasurable).symm
  solution := fun T' => HRS.MS.GenPath.s56_strong_comp hπ (hR.solution T')
  filtered := ⟨ℱ', W'', hF⟩
  invariant := hR.invariant

end Canonical

section Shift

variable {d N : ℕ}

theorem s81s_cyl_shift {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {ℱ : Filtration ℝ mΩ} {κ : Type*} [Countable κ] {B : ℝ≥0 → Ω → κ → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) (u : ℝ≥0) :
    IsCylindricalBrownian P (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ u)
      (HRS.MD.EQLawPath.shiftProc B u) := by
  intro s
  exact HRS.Whole.BreakdownS81.s81b_isBrownianFiltration_shift (hB s) u

theorem s81s_cyl_shift_vec {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    (hW : IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2)) (u : ℝ≥0) :
    IsCylindricalBrownian P (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ u)
      (fun t z (ia : Fin N × Fin d) => HRS.Whole.S79.s79p_shiftW u W t z ia.1 ia.2) := by
  have h := s81s_cyl_shift hW u
  have e : (fun t z (ia : Fin N × Fin d) => HRS.Whole.S79.s79p_shiftW u W t z ia.1 ia.2) =
      HRS.MD.EQLawPath.shiftProc (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) u := by
    funext t z ia
    simp [HRS.Whole.S79.s79p_shiftW, HRS.MD.EQLawPath.shiftProc]
  rw [e]
  exact h

theorem s81s_prog_coord {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
    {X : ℝ≥0 → Ω → EucConfig d N} (h : IsProgressive ℱ (ofNNRealTime X)) (i : Fin N) :
    IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i) :=
  fun t => (measurable_pi_apply i).comp (h t)

end Shift

end HRS.Whole.S81S
