import HRS.MS.MfeConfAux106

/-!
# S.B.1, packet F9 (part 10): the abstract passage `M → ∞` in the entropy inequality

`sb1_AL`: if the level-`M` inequalities hold, the final entropy is lower semicontinuous along `M`, the initial entropies converge
and the time integrals of the sources converge, then the limit inequality holds (and the limit entropy is finite).
-/

noncomputable section

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MfeConf

theorem sb1_AL {α : Type*} [MeasurableSpace α] {T : ℝ} {mM QM : ℕ → ℝ → Measure α} {m Q : ℝ → Measure α}
    {ν₀ : Measure α} {aM : ℕ → ℝ → ℝ} {a : ℝ → ℝ}
    (hM : ∀ M, ∀ t ∈ Set.Icc (0 : ℝ) T, relEntropy (mM M t) (QM M t) ≠ ⊤ ∧
      (relEntropy (mM M t) (QM M t)).toReal ≤ (relEntropy ν₀ (QM M 0)).toReal + ∫ s in Set.Icc (0 : ℝ) t, aM M s)
    (hlsc : ∀ t ∈ Set.Icc (0 : ℝ) T, relEntropy (m t) (Q t) ≤ liminf (fun M => relEntropy (mM M t) (QM M t)) atTop)
    (hinit : Tendsto (fun M => (relEntropy ν₀ (QM M 0)).toReal) atTop (𝓝 (relEntropy ν₀ (Q 0)).toReal))
    (hsrc : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun M => ∫ s in Set.Icc (0 : ℝ) t, aM M s) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) t, a s)))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    relEntropy (m t) (Q t) ≠ ⊤ ∧
      (relEntropy (m t) (Q t)).toReal ≤ (relEntropy ν₀ (Q 0)).toReal + ∫ s in Set.Icc (0 : ℝ) t, a s := by
  set R : ℝ := (relEntropy ν₀ (Q 0)).toReal + ∫ s in Set.Icc (0 : ℝ) t, a s with hR
  have hRlim : Tendsto (fun M => (relEntropy ν₀ (QM M 0)).toReal + ∫ s in Set.Icc (0 : ℝ) t, aM M s) atTop (𝓝 R) :=
    hinit.add (hsrc t ht)
  have hRnn : 0 ≤ R :=
    ge_of_tendsto hRlim (Eventually.of_forall fun M => (ENNReal.toReal_nonneg).trans (hM M t ht).2)
  have hle : relEntropy (m t) (Q t) ≤ ENNReal.ofReal R := by
    refine (hlsc t ht).trans ?_
    have h3 := (ENNReal.tendsto_ofReal hRlim).liminf_eq
    rw [← h3]
    refine liminf_le_liminf (Eventually.of_forall fun M => ?_)
    rw [← ENNReal.ofReal_toReal (hM M t ht).1]
    exact ENNReal.ofReal_le_ofReal (hM M t ht).2
  exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle, ENNReal.toReal_le_of_le_ofReal hRnn hle⟩

end HRS.MS.MfeConf
