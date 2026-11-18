import HRS.Uniform.Q45Core4

/-!
# Q45: assembly of Proposition 3.21, pointwise facts about the path processes
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

lemma continuousOn_VE_zero {T : ℝ} (S : EvolData H E) (hev : S.IsEvolution T) (x : H) :
    ContinuousOn (fun t : ℝ => S.VE t 0 (S.j x)) (Set.Icc 0 T) := by
  have hc := hev.cont_E (S.j x)
  exact hc.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨le_rfl, ht.1, ht.2⟩)

lemma windowPath_eq_mk {T : ℝ} (Y : ℝ → Ω → E) {ω : Ω}
    (h : Continuous fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω) :
    windowPath 0 T Y ω = (⟨fun t => Y (0 + (t : ℝ)) ω, h⟩ : C(Set.Icc (0 : ℝ) T, E)) := by
  unfold windowPath
  exact dif_pos h

lemma windowPath_eq_zero {T : ℝ} (Y : ℝ → Ω → E) {ω : Ω}
    (h : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω) :
    windowPath 0 T Y ω = 0 := by
  unfold windowPath
  exact dif_neg h

lemma windowPath_congr {T : ℝ} {Y Y' : ℝ → Ω → E} {ω : Ω}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ω = Y' t ω) : windowPath 0 T Y ω = windowPath 0 T Y' ω := by
  have e : (fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω) =
      fun t : Set.Icc (0 : ℝ) T => Y' (0 + (t : ℝ)) ω := by
    funext t
    have := h (t : ℝ) t.2
    simpa using this
  by_cases hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω
  · have hc' : Continuous fun t : Set.Icc (0 : ℝ) T => Y' (0 + (t : ℝ)) ω := e ▸ hc
    rw [windowPath_eq_mk Y hc, windowPath_eq_mk Y' hc']
    exact ContinuousMap.ext fun t => congrFun e t
  · have hc' : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => Y' (0 + (t : ℝ)) ω := e ▸ hc
    rw [windowPath_eq_zero Y hc, windowPath_eq_zero Y' hc']

/-- Where the processes are continuous, the window path of a sum of processes is the sum of window paths. -/
lemma windowPath_add_of_cont {T : ℝ} {Y₁ Y₂ Y : ℝ → Ω → E} {ω : Ω}
    (h₁ : ContinuousOn (fun t => Y₁ t ω) (Set.Icc 0 T))
    (h₂ : ContinuousOn (fun t => Y₂ t ω) (Set.Icc 0 T))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ω = Y₁ t ω + Y₂ t ω) :
    windowPath 0 T Y ω = windowPath 0 T Y₁ ω + windowPath 0 T Y₂ ω := by
  have hc : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T) :=
    (h₁.add h₂).congr fun t ht => h t ht
  refine pcm_ext fun t => ?_
  rw [pcm_add, pcm_windowPath Y hc, pcm_windowPath Y₁ h₁, pcm_windowPath Y₂ h₂]
  exact h t t.2

end HRS.Uniform.Q45
