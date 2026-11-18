import HRS.ME.UIPath
import HRS.ME.RetPathLaw
import HRS.ME.RetGlueB
import HRS.MD.EQFrozen29Rest
import HRS.MD.EQLawPath
import HRS.Sections.AdjKGlue

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathTight

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

/-- Evaluation of a path on a subset `D` of the time interval. -/
def p_up4_rEval (m T : ℝ) (D : Set (Set.Icc (0 : ℝ) T)) :
    PathSpace d m T → (D → NegSobolev d m) := fun w q => w.at' q.1

theorem p_up4_rEval_continuous (m T : ℝ) (D : Set (Set.Icc (0 : ℝ) T)) :
    Continuous (p_up4_rEval (d := d) m T D) := by
  refine continuous_pi fun q => ?_
  exact (continuous_eval_const (F := C(Set.Icc (0 : ℝ) T, NegSobolev d m)) q.1 :)

theorem p_up4_rEval_injective (m T : ℝ) (D : Set (Set.Icc (0 : ℝ) T)) (hD : Dense D) :
    Function.Injective (p_up4_rEval (d := d) m T D) := by
  intro w w' h
  have key : (fun t => w.at' t) = fun t => w'.at' t :=
    Continuous.ext_on hD (f := fun t => w.at' t) (g := fun t => w'.at' t)
      (w : C(Set.Icc (0 : ℝ) T, NegSobolev d m)).continuous
      (w' : C(Set.Icc (0 : ℝ) T, NegSobolev d m)).continuous
      (fun q hq => congrFun h ⟨q, hq⟩)
  exact ContinuousMap.ext (congrFun key)

theorem p_up4_embedding (m T : ℝ) (D : Set (Set.Icc (0 : ℝ) T)) [Countable D] (hD : Dense D) :
    MeasurableEmbedding (p_up4_rEval (d := d) m T D) := by
  have : PolishSpace (PathSpace d m T) :=
    inferInstanceAs (PolishSpace C(Set.Icc (0 : ℝ) T, NegSobolev d m))
  exact (p_up4_rEval_continuous m T D).measurableEmbedding (p_up4_rEval_injective m T D hD)

/-- The time index `u + q` as an element of the horizon set. -/
def p_up4_idx (T u : ℝ) (hu : 0 ≤ u) (q : Set.Icc (0 : ℝ) T) :
    {t : ℝ≥0 // (t : ℝ) ≤ u + T} :=
  ⟨Real.toNNReal (u + q.1), by
    rw [Real.coe_toNNReal _ (by linarith [q.2.1])]; linarith [q.2.2]⟩

theorem ret_window_event {N : ℕ} (hN : 1 ≤ N) {m : ℝ} (hm : (d : ℝ) < 2 * m) (T u : ℝ) (hu : 0 ≤ u)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (A : Set (PathSpace d m T)) (hA : MeasurableSet A) :
    ∃ B : Set (Config d N × ({t : ℝ≥0 // (t : ℝ) ≤ u + T} → Config d N)), MeasurableSet B ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (X₀ : Ω → Config d N) (X : ℝ≥0 → Ω → Config d N),
        (∀ t, Measurable (X t)) → (∀ᵐ ω ∂P, ∀ i, Continuous fun t => X t ω i) →
        (windowGibbs m T u μ X ⁻¹' A) =ᵐ[P]
          ((fun ω => (X₀ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ u + T} => X t.1 ω)) ⁻¹' B) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) T)
  haveI : Countable D := hDc.to_subtype
  have hemb := p_up4_embedding (d := d) m T D hDd
  let g : Config d N × ({t : ℝ≥0 // (t : ℝ) ≤ u + T} → Config d N) → (D → NegSobolev d m) :=
    fun z q => etaE m (z.2 (p_up4_idx T u hu q.1)) μ
  have hg : Measurable g := by
    refine measurable_pi_iff.2 fun q => ?_
    have hc : Continuous fun x : Config d N => etaE m x μ :=
      (HRS.MD.EQLawPath.eqlaw_continuous_ofMeasureDiff_empirical hm μ hN).const_smul (Real.sqrt N)
    exact hc.measurable.comp ((measurable_pi_apply _).comp measurable_snd)
  refine ⟨g ⁻¹' (p_up4_rEval m T D '' A), hg (hemb.measurableSet_image.2 hA), ?_⟩
  intro Ω _ P X₀ X _ hcont
  have hc : Continuous fun x : Config d N => etaE m x μ :=
    (HRS.MD.EQLawPath.eqlaw_continuous_ofMeasureDiff_empirical hm μ hN).const_smul (Real.sqrt N)
  filter_upwards [hcont] with ω hω
  have hf : Continuous fun t : Set.Icc (0 : ℝ) T => etaE m (X (Real.toNNReal (u + t)) ω) μ := by
    refine hc.comp ?_
    refine continuous_pi fun i => ?_
    exact (hω i).comp (continuous_real_toNNReal.comp (continuous_const.add continuous_subtype_val))
  have hw : windowGibbs m T u μ X ω =
      ⟨fun t : Set.Icc (0 : ℝ) T => etaE m (X (Real.toNNReal (u + t)) ω) μ, hf⟩ := by
    unfold windowGibbs
    exact dif_pos hf
  have hrw : p_up4_rEval m T D (windowGibbs m T u μ X ω) =
      g (X₀ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ u + T} => X t.1 ω) := by
    rw [hw]; rfl
  show (windowGibbs m T u μ X ω ∈ A) = ((X₀ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ u + T} => X t.1 ω) ∈
    g ⁻¹' (p_up4_rEval m T D '' A))
  apply propext
  rw [Set.mem_preimage, ← hrw]
  exact (p_up4_rEval_injective m T D hDd).mem_set_image.symm

end HRS.ME.UIPathTight
