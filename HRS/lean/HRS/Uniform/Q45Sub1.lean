import HRS.Uniform.Q45Trans2

/-!
# Q45 (Lemma 3.20): the closed span of the range of `j` is invariant under the evolution
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Classical

namespace HRS.Uniform.Q45

section Sub

variable {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closure of the range of `j`. -/
def E0 (S : EvolData H E) : Submodule ℝ E := (LinearMap.range (S.j : H →ₗ[ℝ] E)).topologicalClosure

lemma E0_closed (S : EvolData H E) : IsClosed (E0 S : Set E) :=
  Submodule.isClosed_topologicalClosure _

lemma j_mem_E0 (S : EvolData H E) (x : H) : S.j x ∈ E0 S :=
  Submodule.le_topologicalClosure _ ⟨x, rfl⟩

lemma VE_invariant {T : ℝ} {S : EvolData H E} (hev : S.IsEvolution T) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    (htT : t ≤ T) (y : E) (hy : y ∈ E0 S) : S.VE t r y ∈ E0 S := by
  set K' : Submodule ℝ E := (E0 S).comap (S.VE t r : E →ₗ[ℝ] E) with hK'
  have hcl : IsClosed (K' : Set E) := (E0_closed S).preimage (S.VE t r).continuous
  have hle : LinearMap.range (S.j : H →ₗ[ℝ] E) ≤ K' := by
    rintro _ ⟨x, rfl⟩
    show S.VE t r (S.j x) ∈ E0 S
    have := congrArg (fun F : H →L[ℝ] E => F x) (hev.intertwine r t hr hrt htT)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]
    exact j_mem_E0 S _
  exact Submodule.topologicalClosure_minimal _ hle hcl hy

/-- A derivative of a function with values in a closed subspace lies in it. -/
lemma deriv_mem_of_closed {F : Submodule ℝ E} (hF : IsClosed (F : Set E)) {f : ℝ → E} {f' : E}
    {s : Set ℝ} {x : ℝ} (hd : HasDerivWithinAt f f' s x) (hx : x ∈ s) (hfs : ∀ y ∈ s, f y ∈ F)
    (hne : (𝓝[s \ {x}] x).NeBot) : f' ∈ F := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hd
  refine hF.mem_of_tendsto hd ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [slope_def_module]
  exact F.smul_mem _ (F.sub_mem (hfs y hy.1) (hfs x hx))

lemma neBot_Icc {t r : ℝ} (ht : 0 < t) (hr : r ∈ Set.Icc (0 : ℝ) t) :
    (𝓝[Set.Icc (0 : ℝ) t \ {r}] r).NeBot := by
  have := (uniqueDiffOn_Icc ht r hr).accPt
  rw [accPt_iff_nhds] at this
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
  intro U hU
  obtain ⟨y, ⟨hyU, hyI⟩, hyne⟩ := this U hU
  exact ⟨y, hyU, hyI, hyne⟩

end Sub

end HRS.Uniform.Q45
