import HRS.MS.SA16RHeat12

/-!
# S.A.16 (SA16R) Heat13: continuity of `a ↦ Γ_a y`

`sa16r_tendsto_of_dense`: pointwise convergence of a locally bounded family of operators on a dense set.
`sa16r_Gam_cont`: `a ↦ Γ_a y` is continuous on `(0,∞)` into `WmpSpace d (k+1) p`, for every `y`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution

section Dense
variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma sa16r_tendsto_of_dense {l : Filter ι} (T : ι → E →L[ℝ] F) (T0 : E →L[ℝ] F) {B : ℝ}
    (hB : ∀ᶠ i in l, ‖T i‖ ≤ B) (hB0 : ‖T0‖ ≤ B) {D : Set E} (hD : Dense D)
    (hconv : ∀ z ∈ D, Tendsto (fun i => T i z) l (𝓝 (T0 z))) (y : E) :
    Tendsto (fun i => T i y) l (𝓝 (T0 y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hB' : 0 ≤ B := (norm_nonneg _).trans hB0
  have hδ : 0 < ε / (4 * (B + 1)) := by positivity
  obtain ⟨z, hzD, hz⟩ := hD.exists_dist_lt y hδ
  have hz1 := (Metric.tendsto_nhds.1 (hconv z hzD)) (ε / 2) (by positivity)
  filter_upwards [hz1, hB] with i hi hBi
  have hyz : ‖y - z‖ < ε / (4 * (B + 1)) := by rwa [← dist_eq_norm]
  have e : T i y - T0 y = T i (y - z) + (T i z - T0 z) - T0 (y - z) := by simp [map_sub]
  rw [dist_eq_norm] at hi ⊢
  rw [e]
  have h1 : ‖T i (y - z)‖ ≤ B * ‖y - z‖ := (T i).le_of_opNorm_le hBi _
  have h2 : ‖T0 (y - z)‖ ≤ B * ‖y - z‖ := T0.le_of_opNorm_le hB0 _
  have h3 : B * ‖y - z‖ ≤ ε / 4 := by
    calc B * ‖y - z‖ ≤ (B + 1) * (ε / (4 * (B + 1))) :=
          mul_le_mul (by linarith) hyz.le (norm_nonneg _) (by linarith)
      _ = ε / 4 := by field_simp
  calc ‖T i (y - z) + (T i z - T0 z) - T0 (y - z)‖
      ≤ ‖T i (y - z)‖ + ‖T i z - T0 z‖ + ‖T0 (y - z)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ < ε := by linarith

end Dense

section Heat13
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16r_J_coe (l : ℕ) {f : sa16r_S d l p} (hS : MemLp (sa16j_S d l f.1) (ENNReal.ofReal p) volume) :
    (((sa16r_J d l p f : WmpSpace d l p) : WLp d l p) : Euc d → (WIndex d l → ℝ)) =ᵐ[volume] wJet l f.1 := by
  obtain ⟨G, hG⟩ := sa16j_jet_mem d l p f.2.1 hS
  have hw : wrep d l p G =ᵐ[volume] f.1 := by
    filter_upwards [hG] with x hx
    simp only [wrep]
    rw [hx]
    simp only [wJet, wZero, partialDeriv]
    exact iteratedFDeriv_zero_apply _
  rw [← sa16r_eq_J d l p G f hw]
  exact hG

lemma sa16r_cG_cont {a0 : ℝ} (ha0 : 0 < a0) : ContinuousAt (sa16r_cG d) a0 := by
  unfold sa16r_cG
  refine continuousAt_const.add (continuousAt_const.mul (ContinuousAt.mul ?_ continuousAt_const))
  exact ContinuousAt.rpow_const continuousAt_id (Or.inl ha0.ne')

lemma sa16r_Gam_cc_cont (k : ℕ) {a0 : ℝ} (ha0 : 0 < a0) (φ : ccSub d) :
    Tendsto (fun a : ℝ => sa16r_Gam d k p a (sa16r_Jcc d k p φ)) (𝓝 a0)
      (𝓝 (sa16r_Gam d k p a0 (sa16r_Jcc d k p φ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnear : ∀ᶠ a in 𝓝 a0, 0 < a := lt_mem_nhds ha0
  have hjet := sa16r_jet_diff_tendsto (p := p) φ.2 k ha0
  have hreal := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hjet)
  simp only [ENNReal.toReal_zero] at hreal
  refine hreal.congr' ?_
  filter_upwards [hnear] with a ha
  simp only [Function.comp]
  rw [sa16r_Gam_jet ha, sa16r_Gam_jet ha0]
  have hS1 := sa16r_heat_S_memLp (p := p) ha φ.2 k
  have hS0 := sa16r_heat_S_memLp (p := p) ha0 φ.2 k
  have hc1 := sa16r_J_coe (p := p) (k + 1) (f := sa16r_heatL d p ha k φ) hS1
  have hc0 := sa16r_J_coe (p := p) (k + 1) (f := sa16r_heatL d p ha0 k φ) hS0
  rw [show ‖(sa16r_J d (k + 1) p (sa16r_heatL d p ha k φ)) -
      (sa16r_J d (k + 1) p (sa16r_heatL d p ha0 k φ))‖ = ‖(((sa16r_J d (k + 1) p (sa16r_heatL d p ha k φ) :
        WmpSpace d (k + 1) p) : WLp d (k + 1) p) - ((sa16r_J d (k + 1) p (sa16r_heatL d p ha0 k φ) :
        WmpSpace d (k + 1) p) : WLp d (k + 1) p))‖ from rfl, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (((sa16r_J d (k + 1) p (sa16r_heatL d p ha k φ) : WmpSpace d (k + 1) p) :
      WLp d (k + 1) p)) (((sa16r_J d (k + 1) p (sa16r_heatL d p ha0 k φ) : WmpSpace d (k + 1) p) :
      WLp d (k + 1) p)), hc1, hc0] with x h1 h2 h3
  rw [h1]
  simp only [Pi.sub_apply, h2, h3]
  rfl

theorem sa16r_Gam_cont (k : ℕ) {a0 : ℝ} (ha0 : 0 < a0) (y : WmpSpace d k p) :
    Tendsto (fun a : ℝ => sa16r_Gam d k p a y) (𝓝 a0) (𝓝 (sa16r_Gam d k p a0 y)) := by
  have hnear : ∀ᶠ a in 𝓝 a0, 0 < a := lt_mem_nhds ha0
  have hcG : ∀ᶠ a in 𝓝 a0, sa16r_cG d a ≤ sa16r_cG d a0 + 1 := by
    have := (sa16r_cG_cont (d := d) ha0).eventually (Iio_mem_nhds (show sa16r_cG d a0 < sa16r_cG d a0 + 1 by linarith))
    filter_upwards [this] with a ha using ha.le
  refine sa16r_tendsto_of_dense (fun a => sa16r_Gam d k p a) (sa16r_Gam d k p a0)
    (B := sa16r_cG d a0 + 1) ?_ ?_ (D := Set.range (sa16r_Jcc d k p)) (sa16r_Jcc_dense d k p) ?_ y
  · filter_upwards [hnear, hcG] with a ha h2
    exact (sa16r_Gam_norm ha k).trans h2
  · exact (sa16r_Gam_norm ha0 k).trans (by linarith)
  · rintro z ⟨φ, rfl⟩
    exact sa16r_Gam_cc_cont k ha0 φ

end Heat13

end HRS.Whole.AppendixA.Phase2SA16R
