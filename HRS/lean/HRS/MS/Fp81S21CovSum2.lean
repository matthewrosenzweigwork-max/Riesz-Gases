import HRS.MS.Fp81S21CovSum

/-!
# S2.1(iii), packet 16b: continuity of an integrable source cumulative

The ENNReal primitive is continuous on its finite interval by dominated
convergence. This is the scalar continuity input used with the summed
interval-local covariance domination.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical Filter
open scoped ENNReal NNReal BigOperators Topology

namespace HRS.Fp81.S21

/-- The cumulative integral of a finite AEMeasurable ENNReal density is
continuous on its closed interval. The proof extends the density by zero to
that interval and applies dominated convergence; the endpoint singleton is
null, so the open-left interval convention has the same limit. -/
theorem fp81s21_continuousOn_lintegral_Ioc
    {q T : ℝ} (f : ℝ → ℝ≥0∞)
    (hf : AEMeasurable f volume)
    (hfinite : ∫⁻ t in Icc q T, f t < ∞) :
    ContinuousOn (fun u => ∫⁻ t in Ioc q u, f t) (Icc q T) := by
  intro u hu
  change Tendsto (fun x => ∫⁻ t in Ioc q x, f t)
    (𝓝[Icc q T] u) (𝓝 (∫⁻ t in Ioc q u, f t))
  let g : ℝ → ℝ≥0∞ := (Icc q T).indicator f
  let F : ℝ → ℝ → ℝ≥0∞ := fun x t => (Ioc q x).indicator g t
  have hg : AEMeasurable g volume := hf.indicator measurableSet_Icc
  have hFm : ∀ x, AEMeasurable (F x) volume := by
    intro x
    exact hg.indicator measurableSet_Ioc
  have hfin : (∫⁻ t, g t ∂volume) ≠ ∞ := by
    rw [lintegral_indicator measurableSet_Icc]
    exact ne_of_lt hfinite
  have hbound : ∀ᶠ x in 𝓝 u, ∀ᵐ t ∂volume, F x t ≤ g t := by
    filter_upwards [] with x
    filter_upwards [] with t
    by_cases ht : t ∈ Ioc q x <;> simp [F, ht]
  have hpoint : ∀ t, t ≠ u →
      Tendsto (fun x => F x t) (𝓝 u) (𝓝 (F u t)) := by
    intro t htu
    by_cases hqt : q < t
    · by_cases htu' : t ≤ u
      · have hlt : t < u := lt_of_le_of_ne htu' htu
        have hev : ∀ᶠ x in 𝓝 u, t ≤ x := by
          filter_upwards [Ioi_mem_nhds hlt] with x hx
          exact hx.le
        have heq : (fun x => F x t) =ᶠ[𝓝 u] fun _ => F u t := by
          filter_upwards [hev] with x hx
          simp [F, hqt, htu', hx]
        exact Tendsto.congr' heq.symm tendsto_const_nhds
      · have hut : u < t := lt_of_not_ge htu'
        have hev : ∀ᶠ x in 𝓝 u, x < t :=
          Iio_mem_nhds hut
        have heq : (fun x => F x t) =ᶠ[𝓝 u] fun _ => F u t := by
          filter_upwards [hev] with x hx
          have hxt : ¬ t ≤ x := not_le_of_gt hx
          simp [F, hqt, htu', hxt]
        exact Tendsto.congr' heq.symm tendsto_const_nhds
    · have hq : t ≤ q := le_of_not_gt hqt
      have heq : (fun x => F x t) =ᶠ[𝓝 u] fun _ => F u t := by
        filter_upwards [] with x
        simp [F, hq]
      exact Tendsto.congr' heq.symm tendsto_const_nhds
  have hlim : ∀ᵐ t ∂volume, Tendsto (fun x => F x t) (𝓝 u) (𝓝 (F u t)) := by
    have hnot : ∀ᵐ t ∂volume, t ∉ ({u} : Set ℝ) := by
      rw [ae_iff]
      simpa using (measure_singleton u)
    filter_upwards [hnot] with t ht
    exact hpoint t (by simpa using ht)
  have hDCT : Tendsto (fun x => ∫⁻ t, F x t ∂volume)
      (𝓝 u) (𝓝 (∫⁻ t, F u t ∂volume)) :=
    tendsto_lintegral_filter_of_dominated_convergence' (l := 𝓝 u)
      g (Filter.Eventually.of_forall hFm) hbound hfin hlim
  have heq : ∀ x ∈ Icc q T,
      (∫⁻ t, F x t ∂volume) = ∫⁻ t in Ioc q x, f t := by
    intro x hx
    calc
      (∫⁻ t, F x t ∂volume) =
          ∫⁻ t in Ioc q x, g t := lintegral_indicator measurableSet_Ioc g
      _ = ∫⁻ t in Ioc q x, f t := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        have hmem : t ∈ Icc q T := ⟨le_of_lt ht.1, ht.2.trans hx.2⟩
        simp [g, hmem]
  have hevent : (fun x => ∫⁻ t, F x t ∂volume) =ᶠ[𝓝[Icc q T] u]
      fun x => ∫⁻ t in Ioc q x, f t := by
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    exact heq x hx
  have hDCT' : Tendsto (fun x => ∫⁻ t, F x t ∂volume)
      (𝓝[Icc q T] u) (𝓝 (∫⁻ t, F u t ∂volume)) :=
    hDCT.mono_left inf_le_left
  have huEq := heq u hu
  rw [← huEq]
  exact (tendsto_congr' hevent).1 hDCT'

#print axioms fp81s21_continuousOn_lintegral_Ioc

end HRS.Fp81.S21

end
