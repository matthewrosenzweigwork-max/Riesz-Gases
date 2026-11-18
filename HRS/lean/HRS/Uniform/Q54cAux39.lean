import HRS.Uniform.Q54cAux38

/-!
# Q54c, part 39: measurability and sup-norm bounds for `toPath`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Uniform.Q54c

open HRS

variable {d : ℕ}

theorem aemeasurable_toPath {m T : ℝ} (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℝ → Ω → NegSobolev d m) (hm : ∀ t, Measurable (Y t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    AEMeasurable (toPath m T Y) P := by
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hsdef
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hemb := measurableEmbedding_pathCoords (d := d) m T s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id
    (fun _ => ⟨0⟩)
  set Ψ₀ : Ω → (ℕ × NonzeroLattice d → ℝ) := fun ω i => NegSobolev.coord (Y (s i.1) ω) i.2 with hΨ₀
  have hcoordm : ∀ (k : NonzeroLattice d), Measurable fun F : NegSobolev d m => NegSobolev.coord F k :=
    fun k => (continuous_coord m k).measurable
  have hΨm : Measurable Ψ₀ := measurable_pi_iff.2 fun i => (hcoordm i.2).comp (hm _)
  have hae : toPath m T Y =ᵐ[P] fun ω => g (Ψ₀ ω) := by
    filter_upwards [hc] with ω h
    have := pathCoords_toPath (d := d) s Y h
    have h2 := congrFun hg (toPath m T Y ω)
    simp only [Function.comp, id] at h2
    rw [← h2, this]
  exact (hgm.comp hΨm).aemeasurable.congr hae.symm

open Classical in
theorem norm_toPath_sub_le {m T : ℝ} {Ω : Type*} (Y Y' : ℝ → Ω → NegSobolev d m) {ω : Ω}
    (h : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) (h' : ContinuousOn (fun t => Y' t ω) (Set.Icc 0 T))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t ∈ Set.Icc 0 T, ‖Y t ω - Y' t ω‖ ≤ B) :
    ‖toPath m T Y ω - toPath m T Y' ω‖ ≤ B := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω := h.comp_continuous continuous_subtype_val
    fun t => t.2
  have hc' : Continuous fun t : Set.Icc (0 : ℝ) T => Y' t ω := h'.comp_continuous continuous_subtype_val
    fun t => t.2
  have e1 : toPath m T Y ω = (⟨fun t : Set.Icc (0 : ℝ) T => Y t ω, hc⟩ :
      C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold toPath; exact dif_pos hc
  have e2 : toPath m T Y' ω = (⟨fun t : Set.Icc (0 : ℝ) T => Y' t ω, hc'⟩ :
      C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold toPath; exact dif_pos hc'
  rw [e1, e2]
  show ‖(⟨fun t : Set.Icc (0 : ℝ) T => Y t ω, hc⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) -
    ⟨fun t : Set.Icc (0 : ℝ) T => Y' t ω, hc'⟩‖ ≤ B
  rw [ContinuousMap.norm_le _ hB]
  intro t
  simpa using hb t t.2

end HRS.Uniform.Q54c
