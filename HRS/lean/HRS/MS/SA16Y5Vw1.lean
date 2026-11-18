import HRS.MS.SA16Y5Vg3
import HRS.MS.SA16RVol6

/-!
# S.A.16 (SA16Y5) Vw1: triangle Fubini integrability with the singularity `σ^{-γ}` (V7', part 1)

`sa16y5g_tri_int`: copy of `sa16r_tri_int` (`SA16RVol6`) with `σ^{-1/2}` replaced by `σ^{-γ}`, `γ < 1`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

lemma sa16y5g_tri_int {H : ℝ → ℝ → ℝ} {γ T c τ : ℝ} (hγ1 : γ < 1) (hτ : τ ≤ T)
    (hc : ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2) {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T})
    (hb : ∀ r ∈ Icc (0 : ℝ) T, ∀ σ ∈ Ioc (0 : ℝ) T, |H r σ| ≤ c * σ ^ (-γ))
    {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ)
    (hmem : ∀ q ∈ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ τ}, φ q ∈ Icc (0 : ℝ) T) :
    IntegrableOn (fun q : ℝ × ℝ => H (φ q) q.2) {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ τ} := by
  set R : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ τ} with hR
  have hRm : MeasurableSet R := sa16r_tri_meas τ
  have hcont : ContinuousOn (fun q : ℝ × ℝ => H (φ q) q.2) R := by
    have hm : ContinuousOn (fun q : ℝ × ℝ => (φ q, q.2)) R :=
      (hφ.prodMk continuous_snd).continuousOn
    refine hc.comp hm (fun q hq => ⟨hmem q hq, hq.1, hq.2.1.trans (hq.2.2.trans hτ)⟩)
  have hbint : Integrable (fun q : ℝ × ℝ =>
      (Ioc (0 : ℝ) τ).indicator (fun _ => (1 : ℝ)) q.1 *
        (Ioc (0 : ℝ) τ).indicator (fun σ : ℝ => c * σ ^ (-γ)) q.2) (volume.prod volume) := by
    refine Integrable.mul_prod (f := fun x : ℝ => (Ioc (0 : ℝ) τ).indicator (fun _ => (1 : ℝ)) x)
      (g := fun σ : ℝ => (Ioc (0 : ℝ) τ).indicator (fun σ : ℝ => c * σ ^ (-γ)) σ) ?_ ?_
    · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
    · have hI : IntegrableOn (fun σ : ℝ => c * σ ^ (-γ)) (Ioc 0 τ) :=
        (sa16y5g_rpow_int hγ1 τ).const_mul c
      exact hI.integrable_indicator measurableSet_Ioc
  rw [← Measure.volume_eq_prod] at hbint
  refine Integrable.mono' hbint.integrableOn (hcont.aestronglyMeasurable hRm) ?_
  rw [ae_restrict_iff' hRm]
  refine Filter.Eventually.of_forall fun q hq => ?_
  have h1 : q.1 ∈ Ioc (0 : ℝ) τ := ⟨hq.1.trans_le hq.2.1, hq.2.2⟩
  have h2 : q.2 ∈ Ioc (0 : ℝ) τ := ⟨hq.1, hq.2.1.trans hq.2.2⟩
  rw [indicator_of_mem h1, indicator_of_mem h2, one_mul, Real.norm_eq_abs]
  exact hb _ (hmem q hq) _ ⟨hq.1, hq.2.1.trans (hq.2.2.trans hτ)⟩

end HRS.Whole.AppendixA.Phase2SA16R
