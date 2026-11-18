import HRS.MS.SA16Y5Id2
import HRS.MS.SA16RDuh1

/-!
# S.A.16 (SA16Y5) Jc1: joint strong continuity of the gain operators (B8)

`sa16y5_Gam_joint`: `q ↦ Γ_{a(q)} y(q)` is continuous on `S` for continuous positive `a` and continuous `y`.
`sa16y5_Qh_joint`: `(r, s) ↦ Qh (ν s) (N r) x` is continuous on `{r ∈ [0,T], 0 < s ≤ T}`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Jc1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y5_Gam_joint {α : Type*} [TopologicalSpace α] (k : ℕ) {S : Set α} {a : α → ℝ}
    (ha : ContinuousOn a S) (hpos : ∀ q ∈ S, 0 < a q) {y : α → WmpSpace d k p} (hy : ContinuousOn y S) :
    ContinuousOn (fun q => sa16r_Gam d k p (a q) (y q)) S := by
  intro q0 hq0
  have h0 := hpos q0 hq0
  refine sa16r_clm_apply_strong (F := fun q => sa16r_Gam d k p (a q)) (B := sa16r_cG d (a q0) + 1)
    (fun v => ?_) ?_ (hy q0 hq0)
  · exact (sa16r_Gam_cont (p := p) k h0 v).comp (ha q0 hq0)
  · have hcG : ∀ᶠ b in 𝓝 (a q0), sa16r_cG d b ≤ sa16r_cG d (a q0) + 1 := by
      have := (sa16r_cG_cont (d := d) h0).eventually
        (Iio_mem_nhds (show sa16r_cG d (a q0) < sa16r_cG d (a q0) + 1 by linarith))
      filter_upwards [this] with b hb using hb.le
    have hpos' : ∀ᶠ b in 𝓝 (a q0), 0 < b := lt_mem_nhds h0
    have h1 : ∀ᶠ q in 𝓝[S] q0, sa16r_cG d (a q) ≤ sa16r_cG d (a q0) + 1 ∧ 0 < a q :=
      (ha q0 hq0).eventually (hcG.and hpos')
    filter_upwards [h1] with q hq
    exact (sa16r_Gam_norm hq.2 k).trans hq.1

theorem sa16y5_Qh_joint {ν T : ℝ} (hν : 0 < ν) (m : ℕ)
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hNc : ∀ x, ContinuousOn (fun r => Nf r x) (Icc 0 T)) (x : WmpSpace d (m + 1 + 1) p) :
    ContinuousOn (fun q : ℝ × ℝ => sa16y5_Qh d m p (ν * q.2) (Nf q.1) x)
      {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T} := by
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T} with hS
  have hay : ContinuousOn (fun q : ℝ × ℝ => ν * q.2 / 2) S :=
    (((continuous_const.mul continuous_snd).div_const 2)).continuousOn
  have hpos : ∀ q ∈ S, 0 < ν * q.2 / 2 := fun q hq => by have := hq.2.1; positivity
  have hy0 : ContinuousOn (fun q : ℝ × ℝ => Nf q.1 x) S :=
    (hNc x).comp continuous_fst.continuousOn (fun q hq => hq.1)
  have h1 := sa16y5_Gam_joint (p := p) m hay hpos hy0
  have h2 := sa16y5_Gam_joint (p := p) (m + 1) hay hpos h1
  exact h2

end Jc1

end HRS.Whole.AppendixA.Phase2SA16R
