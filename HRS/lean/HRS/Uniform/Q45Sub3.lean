import HRS.Uniform.Q45Sub2

/-!
# Q45 (Lemma 3.20): the restricted evolution on the closed span of the range of `j`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Classical

namespace HRS.Uniform.Q45

section Sub

variable {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The restriction of `j`. -/
def j0 (S : EvolData H E) : H →L[ℝ] E0 S := S.j.codRestrict (E0 S) (j_mem_E0 S)

/-- The restriction of the evolution (zero where it is not invariant). -/
def VE0 (S : EvolData H E) (t r : ℝ) : E0 S →L[ℝ] E0 S :=
  if h : ∀ y ∈ E0 S, S.VE t r y ∈ E0 S then
    ((S.VE t r).comp (E0 S).subtypeL).codRestrict (E0 S) (fun y => h y y.2)
  else 0

/-- The restriction of the generator (zero where it does not map into `E0`). -/
def A0 (S : EvolData H E) (r : ℝ) : S.D →ₗ[ℝ] E0 S :=
  if h : ∀ x : S.D, S.A r x ∈ E0 S then (S.A r).codRestrict (E0 S) h else 0

/-- The evolution data on `E0`. -/
@[reducible] def subData (S : EvolData H E) : EvolData H (E0 S) where
  j := j0 S
  VH := S.VH
  VE := VE0 S
  D := S.D
  A := A0 S

lemma j0_coe (S : EvolData H E) (x : H) : ((j0 S x : E0 S) : E) = S.j x := rfl

variable {T : ℝ} {S : EvolData H E}

lemma VE0_coe (hev : S.IsEvolution T) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) (y : E0 S) :
    ((VE0 S t r y : E0 S) : E) = S.VE t r y := by
  unfold VE0
  rw [dif_pos (fun y hy => VE_invariant hev hr hrt htT y hy)]
  rfl

lemma A0_coe (hT : 0 < T) (hev : S.IsEvolution T) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : S.D) :
    ((A0 S r x : E0 S) : E) = S.A r x := by
  unfold A0
  rw [dif_pos (fun x => A_mem hT hev hr x)]
  rfl

lemma hasDerivWithinAt_of_coe {F : Submodule ℝ E} {f : ℝ → F} {f' : F} {s : Set ℝ} {x : ℝ}
    (h : HasDerivWithinAt (fun y => (f y : E)) (f' : E) s x) : HasDerivWithinAt f f' s x := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at h ⊢
  rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
  refine h.congr fun y => ?_
  simp only [Function.comp_apply, slope_def_module]
  rfl

end Sub

end HRS.Uniform.Q45
