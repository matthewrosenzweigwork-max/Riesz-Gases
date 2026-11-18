import HRS.Appendix.B15EAux8

/-!
# Packet B15E: Proposition B.15, strong branch -- the relocated proof `b15_sde_entropy_law_free_proof`

Relocated proof of `HRS.b15_sde_entropy_law_free` (`HRS/Appendix/B15Aux1.lean`, statement unchanged and
frozen there with its `sorry`); the statement below is a verbatim copy, tied to the original by
`example := (@b15_sde_entropy_law_free_proof : type_of% @b15_sde_entropy_law_free)`.

Assembly (plan in `B15EAux1.lean`): shifted filtration `ℱ' t = ℱ (max t 0)`, level-`M_n = n` regularised
solutions started at `rep ∘ X 0`; `X^{M_n} = X` eventually (`b15c_regularised_eq_strong_proof`);
the level-`M` entropy inequality for `V ∈ C²` (`b15e_regularised_entropy`: smooth approximation, D2 + D3,
Gronwall, lower semicontinuity); the limit `n → ∞` (`b15e_step4_limit`); densities from finiteness of the
entropy; the FKE conjunct from `selected_law_fke`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem b15_sde_entropy_law_free_proof
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hβ : 0 < D.invβ)
    (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet d N)
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config d N}
    (hS : IsStrongSolution P D T X₀ W X) (hU : PathwiseUnique P D T X₀ W)
    (hF : IsFilteredSolution P ℱ W' W X)
    (hdens0 : HasSelectedDensity P X 0)
    (hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤) :
    b15_EntropyLawConcl P D T X := by
  have hX : SelectedFlow P D T X₀ W X := ⟨hX₀, hdist, hW, hind, Or.inl ⟨hS, hU⟩⟩
  have hd := b15_one_le_d D
  have hNd : 1 ≤ N * d := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (by omega))
  have hW'' : IsBrownianFiltration P (b15e_shiftFil ℱ) W' := b15e_shiftFil_brownian hF.brownian
  have hY₀ : ∀ t : ℝ, Measurable[b15e_shiftFil ℱ t] (b15e_initLift X) :=
    b15e_initLift_measurable (hF.adapted 0)
  have hY₀ae : ∀ᵐ ω ∂P, (fun i => Torus.mk (b15e_initLift X ω i)) = X₀ ω := by
    filter_upwards [hS.init] with ω h
    rw [b15e_mk_initLift, h]
  set M : ℕ → ℝ := fun n => (n : ℝ) with hMdef
  have hMt : Tendsto M atTop atTop := tendsto_natCast_atTop_atTop
  have hM0 : ∀ n, 0 ≤ M n := fun n => Nat.cast_nonneg n
  choose Y hY using fun n => b15e_exists_regularised hW'' D hV (M n) (b15e_initLift X) hY₀
  have hev := b15c_regularised_eq_strong_proof D hV hW hS hF.coords hY₀ae hMt hY
  have hprobX : ∀ r : ℝ, IsProbabilityMeasure (selectedLaw P X r) := fun r =>
    b15b_selectedLaw_isProb hS.adapted r
  have := hprobX 0
  have hreg : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D (M n)) (selectedLaw P (b15c_regProcess (Y n)) t)
      + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ
          (b15c_potentialReg D (M n)) (selectedLaw P (b15c_regProcess (Y n)) r) : ℝ≥0∞) : EReal)
      ≤ gibbsEntropy D (selectedLaw P X 0) := by
    intro n t ht
    have hfin_n : b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D (M n))
        (selectedLaw P (b15c_regProcess (Y n)) 0) < ⊤ := by
      rw [b15e_selectedLaw_zero (hY n)]
      exact lt_of_le_of_lt (b15c_gibbsEntropyGen_le_proof D hβ hV (hM0 n) _) hH0
    have h := b15e_regularised_entropy hNd D hβ hM hV (M n) hW'' hY₀ (hY n) hT hfin_n t ht
    refine h.trans ?_
    rw [b15e_selectedLaw_zero (hY n)]
    exact b15c_gibbsEntropyGen_le_proof D hβ hV (hM0 n) _
  have hmain : ∀ t ∈ Set.Icc (0 : ℝ) T, gibbsEntropy D (selectedLaw P X t)
      + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
      ≤ gibbsEntropy D (selectedLaw P X 0) := fun t ht =>
    b15e_step4_limit hβ hV hS hMt hM0 hY hev ht.1 ht.2 (fun n => hreg n t ht)
  have hdens : ∀ t ∈ Set.Icc (0 : ℝ) T, HasSelectedDensity P X t := by
    intro t ht
    have h1 := hmain t ht
    have hJ : (0 : EReal) ≤ ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t,
        fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal) := EReal.coe_ennreal_nonneg _
    have hHt : gibbsEntropy D (selectedLaw P X t) < ⊤ :=
      lt_of_le_of_lt ((le_add_of_nonneg_right hJ).trans h1) hH0
    have hrel : InformationTheory.klDiv (selectedLaw P X t) (gibbsRef D N) ≠ ⊤ := by
      intro h
      unfold gibbsEntropy relEntropy at hHt
      rw [h] at hHt
      simp at hHt
    have hac : selectedLaw P X t ≪ gibbsRef D N := (InformationTheory.klDiv_ne_top_iff.mp hrel).1
    have hgv : gibbsRef D N ≪ (volume : Measure (Config d N)) :=
      (withDensity_absolutelyContinuous _ _).smul_left _
    exact hac.trans hgv
  exact ⟨fun t ht => ⟨hdens t ht, hmain t ht⟩, b15_solvesSelectedFKE hN hV hT hX hF⟩

example := (@b15_sde_entropy_law_free_proof : type_of% @b15_sde_entropy_law_free)

/-- The dispatcher `b15_sde_entropy_law_of_free` with the free lemma replaced by its proof
`b15_sde_entropy_law_free_proof` (strong branch); the Cépa-Lépingle branch is still
`cepa_entropy_confined` (not part of this packet). -/
theorem b15_sde_entropy_law_of_free_proof
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hβ : 0 < D.invβ)
    (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hdens0 : HasSelectedDensity P X 0)
    (hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤) :
    (∀ t ∈ Set.Icc 0 T, HasSelectedDensity P X t ∧
      gibbsEntropy D (selectedLaw P X t)
        + ((ENNReal.ofReal D.invβ *
            ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
        ≤ gibbsEntropy D (selectedLaw P X 0)) ∧
    SolvesSelectedFKE D T (selectedLaw P X) := by
  rcases hX with ⟨hX₀, hdist, hW, hind, hflow⟩
  rcases hflow with ⟨hS, hU⟩ | ⟨hd1, hs0, _, _, hCL⟩
  · exact b15_sde_entropy_law_free_proof hN hM hβ hV hT hX₀ hdist hW hind hS hU hF hdens0 hH0
  · subst hd1
    exact cepa_entropy_confined hN hs0 hβ hM hV hT hX₀ hdist hW hind hCL hF hdens0 hH0

example := (@b15_sde_entropy_law_of_free_proof : type_of% @b15_sde_entropy_law_of_free)

end HRS
