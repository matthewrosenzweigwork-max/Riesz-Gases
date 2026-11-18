import HRS.MS.MainRdPathAux1

/-!
# S.A.9, packet P1b: the path representative and uniqueness of representatives

* `sa9_pathRepr`: a process with measurable evaluations and a.s. continuous paths on `[0,T]` has a measurable
  `C([0,T]; E)`-valued modification (zero off a measurable null set), whose evaluations agree a.s. with the process;
* `sa9_path_ae_eq`: two `HNegPath`-valued random variables with a.s. equal evaluations (pairings against the Parseval
  system) at each time are a.s. equal, so their laws coincide.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MS.MainRdField

variable {d : ℕ}

section PathRepr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Measurability of a `C([0,T]; E)`-valued map from the measurability of its evaluations. -/
theorem sa9_measurable_path {T : ℝ} (Ξ : Ω → C(Set.Icc (0 : ℝ) T, E))
    (h : ∀ t : Set.Icc (0 : ℝ) T, Measurable fun ζ => Ξ ζ t) : Measurable Ξ := by
  rw [measurable_iff_comap_le, ContinuousMap.measurableSpace_eq_iSup_comap_eval,
    MeasurableSpace.comap_iSup]
  refine iSup_le fun t => ?_
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 (h t)

theorem sa9_pathRepr {T : ℝ} (P : Measure Ω) (Z : ℝ → Ω → E) (hmeas : ∀ t, Measurable (Z t))
    (hcont : ∀ᵐ ζ ∂P, Continuous fun t : Set.Icc (0 : ℝ) T => Z t.1 ζ) :
    ∃ Ξ : Ω → C(Set.Icc (0 : ℝ) T, E), Measurable Ξ ∧
      (∀ t : Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂P, Ξ ζ t = Z t.1 ζ) ∧
      ∀ᵐ ζ ∂P, Ξ ζ = contPathOf T (fun t => Z t ζ) := by
  classical
  obtain ⟨s, hsub, hsm, hs0⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  let Zh : ℝ → Ω → E := fun t ζ => if ζ ∈ s then 0 else Z t ζ
  have hZh : ∀ ζ, Continuous fun t : Set.Icc (0 : ℝ) T => Zh t.1 ζ := by
    intro ζ
    by_cases hζ : ζ ∈ s
    · simp only [Zh, hζ, if_true]; exact continuous_const
    · simp only [Zh, hζ, if_false]
      by_contra hc
      exact hζ (hsub hc)
  let Ξ : Ω → C(Set.Icc (0 : ℝ) T, E) := fun ζ => ⟨fun t => Zh t.1 ζ, hZh ζ⟩
  refine ⟨Ξ, sa9_measurable_path Ξ fun t => ?_, fun t => ?_, ?_⟩
  · exact Measurable.ite hsm measurable_const (hmeas t.1)
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hs0] with ζ hζ
    simp [Ξ, Zh, hζ]
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hs0, hcont] with ζ hζ hc
    unfold contPathOf
    rw [dif_pos hc]
    ext t
    simp [Ξ, Zh, hζ]

end PathRepr

section Unique

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {q : ℕ} {T : ℝ}

/-- Two random paths in `H^{-q}` with a.s. equal evaluations at every time are a.s. equal. -/
theorem sa9_path_ae_eq (P : Measure Ω) (Ξ₁ Ξ₂ : Ω → C(Set.Icc (0 : ℝ) T, HNeg d (q : ℝ)))
    (h : ∀ t : Set.Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ → ∀ᵐ ζ ∂P,
      HNeg.pairing φ (Ξ₁ ζ t) = HNeg.pairing φ (Ξ₂ ζ t)) : ∀ᵐ ζ ∂P, Ξ₁ ζ = Ξ₂ ζ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) T)
  have hD : ∀ t ∈ D, ∀ᵐ ζ ∂P, Ξ₁ ζ t = Ξ₂ ζ t := by
    intro t _
    have := mrm_ae_eq_of_pairings (μ := P) (F := fun ζ => Ξ₁ ζ t) (G := fun ζ => Ξ₂ ζ t)
      (fun _ => True) (fun ℓ => by
        filter_upwards [h t _ (mrm_e_test (q : ℝ) ℓ)] with ζ hζ _ using hζ)
    filter_upwards [this] with ζ hζ using hζ trivial
  filter_upwards [(ae_ball_iff hDc).2 hD] with ζ hζ
  exact ContinuousMap.ext fun t => by
    have := (Ξ₁ ζ).continuous.ext_on hDd (Ξ₂ ζ).continuous (fun t ht => hζ t ht)
    exact congrFun this t

theorem sa9_law_eq_of_ae_eq {β : Type*} [MeasurableSpace β] (P : Measure Ω) {F G : Ω → β}
    (h : ∀ᵐ ζ ∂P, F ζ = G ζ) : P.map F = P.map G :=
  Measure.map_congr h

end Unique

end HRS.MS.MainRdPath
