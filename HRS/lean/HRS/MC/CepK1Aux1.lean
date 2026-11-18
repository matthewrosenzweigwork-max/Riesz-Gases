import Mathlib

/-!
# Packet K1, auxiliary 1: `u ↦ π cot(π u) - 1/u` is smooth at `0`
-/

noncomputable section

namespace HRS.MC.CepK1

open Real

/-- The function `q u = cos (π u) / sinc (π u) - 1`. -/
def cepk1_q (u : ℝ) : ℝ := Real.cos (π * u) / Real.sinc (π * u) - 1

lemma cepk1_analyticAt_sinc : AnalyticAt ℝ Real.sinc 0 := by
  obtain ⟨p, hp⟩ := (analyticAt_sin (x := (0 : ℝ)))
  rw [Real.sinc_eq_dslope]
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

lemma cepk1_analyticAt_q : AnalyticAt ℝ cepk1_q 0 := by
  have h1 : AnalyticAt ℝ (fun u : ℝ => Real.cos (π * u)) 0 :=
    (analyticAt_cos (x := π * 0)).comp (f := fun u : ℝ => π * u) (by fun_prop)
  have h2 : AnalyticAt ℝ (fun u : ℝ => Real.sinc (π * u)) 0 :=
    (show AnalyticAt ℝ Real.sinc (π * 0) by simpa using cepk1_analyticAt_sinc).comp
      (f := fun u : ℝ => π * u) (by fun_prop)
  have h3 : AnalyticAt ℝ (fun u : ℝ => Real.cos (π * u) / Real.sinc (π * u)) 0 :=
    h1.fun_div h2 (by simp)
  exact h3.sub analyticAt_const

lemma cepk1_q_zero : cepk1_q 0 = 0 := by simp [cepk1_q]

/-- The removable-singularity function `H = dslope q 0`. -/
def cepk1_H : ℝ → ℝ := dslope cepk1_q 0

lemma cepk1_H_analyticAt : AnalyticAt ℝ cepk1_H 0 := by
  obtain ⟨p, hp⟩ := cepk1_analyticAt_q
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

lemma cepk1_H_eq {u : ℝ} (hu : u ≠ 0) :
    cepk1_H u = π * (Real.cos (π * u) / Real.sin (π * u)) - 1 / u := by
  unfold cepk1_H
  rw [dslope_of_ne _ hu, slope_def_field, cepk1_q_zero, cepk1_q, Real.sinc_of_ne_zero (by positivity)]
  by_cases hs : Real.sin (π * u) = 0
  · simp [hs]
    ring
  · have hpi : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

lemma cepk1_H_odd {u : ℝ} (hu : u ≠ 0) : cepk1_H (-u) = -cepk1_H u := by
  rw [cepk1_H_eq hu, cepk1_H_eq (neg_ne_zero.mpr hu)]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, div_neg, one_div, inv_neg]
  ring

lemma cepk1_H_zero : cepk1_H 0 = 0 := by
  have hc : ContinuousAt cepk1_H 0 := cepk1_H_analyticAt.continuousAt
  have h1 : Filter.Tendsto cepk1_H (nhdsWithin 0 {0}ᶜ) (nhds (cepk1_H 0)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hneg : Filter.Tendsto (fun u : ℝ => -u) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simpa using hu
  have h2 : Filter.Tendsto (fun u : ℝ => -cepk1_H (-u)) (nhdsWithin 0 {0}ᶜ) (nhds (-cepk1_H 0)) :=
    (h1.comp hneg).neg
  have h3 : (fun u : ℝ => -cepk1_H (-u)) =ᶠ[nhdsWithin 0 {0}ᶜ] cepk1_H := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [cepk1_H_odd hu]; ring
  have := tendsto_nhds_unique (h2.congr' h3) h1
  linarith

end HRS.MC.CepK1
