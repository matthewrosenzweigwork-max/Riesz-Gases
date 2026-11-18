import HRS.Sections.AdjKBAux1

/-!
# ADJKB Aux2: Arzelà-Ascoli for `adjkCompactSet`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

variable {d : ℕ}

/-- the defining condition of `adjkCompactSet`, for a function on `[0,T]` -/
def adjkbCond (d : ℕ) (m T m₁ R : ℝ) (δ : ℕ → ℝ) (f : Set.Icc (0 : ℝ) T → NegSobolev d m) : Prop :=
  (∀ t, adjkEnergy m₁ m (f t) ≤ ENNReal.ofReal (R ^ 2)) ∧
    ∀ (j : ℕ) (s t : Set.Icc (0 : ℝ) T), |(s : ℝ) - t| ≤ δ j → ‖f s - f t‖ ≤ 1 / ((j : ℝ) + 1)

lemma adjkb_cond_closed (m T m₁ R : ℝ) (δ : ℕ → ℝ) :
    IsClosed {f : Set.Icc (0 : ℝ) T → NegSobolev d m | adjkbCond d m T m₁ R δ f} := by
  have h1 : IsClosed {F : NegSobolev d m | adjkEnergy m₁ m F ≤ ENNReal.ofReal (R ^ 2)} :=
    (adjkEnergy_lsc (d := d) m₁ m).isClosed_preimage (ENNReal.ofReal (R ^ 2))
  have : {f : Set.Icc (0 : ℝ) T → NegSobolev d m | adjkbCond d m T m₁ R δ f} =
      (⋂ t, (fun f : Set.Icc (0 : ℝ) T → NegSobolev d m => f t) ⁻¹'
        {F : NegSobolev d m | adjkEnergy m₁ m F ≤ ENNReal.ofReal (R ^ 2)}) ∩
      ⋂ (j : ℕ) (s : Set.Icc (0 : ℝ) T) (t : Set.Icc (0 : ℝ) T),
        {f : Set.Icc (0 : ℝ) T → NegSobolev d m |
          |(s : ℝ) - t| ≤ δ j → ‖f s - f t‖ ≤ 1 / ((j : ℝ) + 1)} := by
    ext f
    constructor
    · intro h
      exact ⟨mem_iInter.2 fun t => h.1 t, mem_iInter.2 fun j => mem_iInter.2 fun s =>
        mem_iInter.2 fun t => h.2 j s t⟩
    · intro h
      exact ⟨fun t => mem_iInter.1 h.1 t, fun j s t =>
        mem_iInter.1 (mem_iInter.1 (mem_iInter.1 h.2 j) s) t⟩
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun t => h1.preimage (continuous_apply t)) ?_
  refine isClosed_iInter fun j => isClosed_iInter fun s => isClosed_iInter fun t => ?_
  by_cases h : |(s : ℝ) - t| ≤ δ j
  · simp only [h, true_imp_iff]
    exact isClosed_le (((continuous_apply s).sub (continuous_apply t)).norm) continuous_const
  · simp only [h, false_imp_iff, setOf_true]
    exact isClosed_univ

lemma adjkb_cond_continuous (m T m₁ R : ℝ) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (f : Set.Icc (0 : ℝ) T → NegSobolev d m) (hf : adjkbCond d m T m₁ R δ f) : Continuous f := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  refine ⟨δ j, hδ j, fun a ha => ?_⟩
  have h1 : |(a : ℝ) - b| ≤ δ j := by
    have : dist a b = |(a : ℝ) - b| := by rw [Subtype.dist_eq, Real.dist_eq]
    rw [← this]; exact ha.le
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hf.2 j a b h1) hj

theorem adjkb_compactSet_isCompact (d : ℕ) (m T m₁ R : ℝ) (hm₁ : m₁ < m) (δ : ℕ → ℝ)
    (hδ : ∀ j, 0 < δ j) : IsCompact (adjkCompactSet d m T m₁ R δ) := by
  set K' : Set C(Set.Icc (0 : ℝ) T, NegSobolev d m) :=
    {w | adjkbCond d m T m₁ R δ w} with hK'
  have hK : adjkCompactSet d m T m₁ R δ = K' := rfl
  show IsCompact K'
  refine ArzelaAscoli.isCompact_of_equicontinuous K' ?_ ?_
  · have himg : ContinuousMap.toFun '' K' =
        {f : Set.Icc (0 : ℝ) T → NegSobolev d m | adjkbCond d m T m₁ R δ f} := by
      ext f
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hf
        exact ⟨⟨f, adjkb_cond_continuous m T m₁ R δ hδ f hf⟩, hf, rfl⟩
    rw [himg]
    refine IsCompact.of_isClosed_subset
      (isCompact_univ_pi (s := fun _ : Set.Icc (0 : ℝ) T =>
        {F : NegSobolev d m | adjkEnergy m₁ m F ≤ ENNReal.ofReal (R ^ 2)})
        fun _ => adjkb_ball_isCompact m m₁ R hm₁)
      (adjkb_cond_closed m T m₁ R δ) ?_
    intro f hf t _
    exact hf.1 t
  · intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    refine ⟨δ j, hδ j, fun x hx w => ?_⟩
    have h1 : |(x₀ : ℝ) - x| ≤ δ j := by
      have : dist x x₀ = |(x₀ : ℝ) - x| := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
      rw [← this]; exact hx.le
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (w.2.2 j x₀ x h1) hj

end HRS.AdjK
