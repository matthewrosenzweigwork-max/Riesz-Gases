import HRS.MP.SelfSimSpec
import HRS.MP.SelfSimP1
import HRS.MP.SelfSimP2
import HRS.MP.SelfSimP3
import HRS.MP.SelfSimP4Final
import HRS.MP.SelfSimP5Final

/-!
# S.A.28 (`selected_law_selfsimilar`), assembled from the proved packets

`selected_law_selfsimilar_final` has the statement of the frozen `HRS.Whole.AppendixALemmas.selected_law_selfsimilar`; the
assembly of `HRS.MP.SelfSim.selected_law_selfsimilar_proof` with the packets P1-P5, P7 replaced by their proofs (P6 is proved in
`SelfSimSpec`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimFinal

variable {d : ℕ}

/-- Corollary S.A.28, assembled from the proved packets P1-P7 (statement verbatim from
`HRS.Whole.AppendixALemmas.selected_law_selfsimilar`). -/
theorem selected_law_selfsimilar_final (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
    (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (T : ℝ) (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : SelectedFlowRd P (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) T X₀ W X)
    (hdens0 : law P (X₀) ≪ (volume : Measure (EucConfig d N)))
    (hH0 : gibbsEntropyW (selfSimWeight d s invβ N 0) (law P X₀) < ⊤) :
    (∀ τ ∈ Set.Icc (0 : ℝ) (Real.log (1 + T)),
      law P (selfSimProcess X τ) ≪ (volume : Measure (EucConfig d N))) ∧
    SolvesFKEW invβ (fun τ Ξ i => -((aSelfSim s τ / N) • ∑ j ∈ Finset.univ.erase i,
        rieszKernelGrad d s (Ξ i - Ξ j) + (1 / 2 : ℝ) • Ξ i)) (Real.log (1 + T))
      (fun τ => law P (selfSimProcess X τ)) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) (Real.log (1 + T)),
      gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (selfSimProcess X τ)) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) τ,
          fisherInfoW (selfSimWeight d s invβ N r) (law P (selfSimProcess X r)) : ℝ≥0∞) : EReal) ≤
      gibbsEntropyW (selfSimWeight d s invβ N 0) (law P X₀)) ∧
    SolvesFKEW invβ (fun _ Ξ i => particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) Ξ i) T
      (fun t => law P (X (Real.toNNReal t))) := by
  obtain ⟨X', ℱ, W', hXX', hX'0, hY, hbr⟩ :=
    HRS.MP.SelfSimP1.ss_P1_filtered_version_proof hd s hs0 hsd N hN invβ hβ T hT P X₀ W X hX
  obtain ⟨ℱb, Wb', Wb, hYb, hnc, hord⟩ := HRS.MP.SelfSimP2.ss_P2_time_change_proof hd s hs0 hsd N hN invβ hβ T hT P hY
  have hlog : 0 < Real.log (1 + T) := Real.log_pos (by linarith)
  -- laws: the modification and the re-indexing do not change the laws
  have hss : ∀ τ : ℝ, 0 ≤ τ → τ ≤ Real.log (1 + T) →
      law P (selfSimProcess X τ) = law P (ssPath X' (Real.toNNReal τ)) := by
    intro τ hτ hτT
    have hle : ((Real.toNNReal (Real.exp τ - 1) : ℝ≥0) : ℝ) ≤ T := by
      rw [Real.coe_toNNReal _ (by linarith [Real.add_one_le_exp τ])]
      have := (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < 1 + T)).1 hτT
      linarith
    refine Measure.map_congr ?_
    filter_upwards [hXX' (Real.toNNReal (Real.exp τ - 1)) hle] with ζ hζ
    funext i
    simp only [ssPath, selfSimProcess, Real.coe_toNNReal _ hτ, hζ]
  have h0 : law P X₀ = law P (ssPath X' 0) := by
    refine Measure.map_congr ?_
    filter_upwards [hX'0] with ζ hζ
    funext i
    simp [ssPath, selfSimProcess, hζ]
  have hXlaw : ∀ t ∈ Set.Icc (0 : ℝ) T,
      law P (X (Real.toNNReal t)) = law P (X' (Real.toNNReal t)) := fun t ht =>
    Measure.map_congr (hXX' _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)).symm
  have hH0' : gibbsEntropyW (selfSimWeight d s invβ N 0) (law P (ssPath X' 0)) < ⊤ := h0 ▸ hH0
  -- the entropy inequality for the self-similar version, by branch
  have hent : SSEntropyIneq d s invβ N (Real.log (1 + T)) P (ssPath X') := by
    rcases hbr with hnc0 | ⟨rfl, rfl, hord0⟩
    · exact HRS.MP.SelfSimP4Final.ss_P4_entropy_free_final hd s hs0 hsd N hN invβ hβ _ hlog P hYb (hnc hnc0) hH0'
    · exact HRS.MP.SelfSimP5Final.ss_P5_entropy_cepa_final N hN invβ hβ _ hlog P hYb (hord hord0) hH0'
  have hent' : ∀ τ ∈ Set.Icc (0 : ℝ) (Real.log (1 + T)),
      gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (selfSimProcess X τ)) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) τ,
          fisherInfoW (selfSimWeight d s invβ N r) (law P (selfSimProcess X r)) : ℝ≥0∞) : EReal) ≤
      gibbsEntropyW (selfSimWeight d s invβ N 0) (law P X₀) := by
    intro τ hτ
    have hI : (∫⁻ r in Set.Icc (0 : ℝ) τ,
        fisherInfoW (selfSimWeight d s invβ N r) (law P (selfSimProcess X r))) =
        ∫⁻ r in Set.Icc (0 : ℝ) τ,
          fisherInfoW (selfSimWeight d s invβ N r) (law P (ssPath X' (Real.toNNReal r))) :=
      setLIntegral_congr_fun measurableSet_Icc (fun r hr => by rw [hss r hr.1 (hr.2.trans hτ.2)])
    rw [hI, hss τ hτ.1 hτ.2, h0]
    exact hent τ hτ
  obtain ⟨⟨hm1, hc1⟩, ⟨hm2, hc2⟩⟩ := HRS.MP.SelfSimP3.ss_P7_drift_regular_proof hd s hs0 hsd N invβ
  refine ⟨fun τ hτ => ?_, ?_, hent', ?_⟩
  · -- clause 1: densities from finiteness of the entropy
    apply ss_P6_absCont_of_entropy (G := selfSimWeight d s invβ N τ)
    have h1 := hent' τ hτ
    have h2 : gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (selfSimProcess X τ)) ≤
        gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (selfSimProcess X τ)) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) τ,
          fisherInfoW (selfSimWeight d s invβ N r) (law P (selfSimProcess X r)) : ℝ≥0∞) : EReal) :=
      le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _)
    exact lt_of_le_of_lt (h2.trans h1) hH0
  · -- clause 2: the self-similar forward equation (P3 in self-similar variables)
    have hfke := HRS.MP.SelfSimP3.ss_P3_fke_proof P hβ.le hlog hm1 (hc1 _) hYb
    exact ss_solvesFKEW_congr hlog.le (fun r hr => hss r hr.1 hr.2) hfke
  · -- clause 4: the unconfined forward equation (P3 in the original variables)
    have hfke := HRS.MP.SelfSimP3.ss_P3_fke_proof P hβ.le hT hm2 (hc2 _) hY
    exact ss_solvesFKEW_congr hT.le (fun r hr => hXlaw r hr) hfke

example := (@selected_law_selfsimilar_final : type_of% @selected_law_selfsimilar)

end HRS.MP.SelfSimFinal
