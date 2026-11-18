import HRS.MS.S11Q3A2
import HRS.MS.S113EndAux16
import HRS.MS.MovForceAux2

/-!
# S11.3 / S11.4 (worker S11Q3), A3: the regular family `ρ_t` and the potential `Γ_t = g * ρ_t`

* `s11q3_rightDeriv`: a function continuous on `[0,∞)`, differentiable on `(0,∞)` with derivative continuous on `[0,∞)` has right derivatives at all `t ≥ 0`.
* `s11q3_Reg`: the hypotheses on the density family used by the producer (Gaussian bounds of the spatial jets uniform in `t ≥ 0`,
  joint continuity of the jets and of `D = ∂_t ρ`, positivity).
* `s11q3_convJoint`: joint continuity in `(t,x)` of `∫ g(z) φ(t,x-z) dz` on `[0,∞) × ℝ^d`.
* `s11q3_Gam_*`: `Γ_t = g * ρ_t` is `C²` with `D_xΓ = g * D_xρ`, `D²_xΓ = g * D²_xρ`; the clamped family is a `s11q3_Jet2`;
  `∂_tΓ = g * D` (two-sided for `t > 0`, right derivative at `0`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.S113BD

theorem s11q3_rightDeriv {f f' : ℝ → ℝ} (hc : ContinuousOn f (Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Ici 0)) : ∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Ici t) t := by
  intro t ht
  rcases ht.lt_or_eq with ht | ht
  · exact (hd t ht).hasDerivWithinAt
  · subst ht
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      ((hc 0 (Set.mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self) self_mem_nhdsWithin ?_
    have h1 : Tendsto f' (𝓝[>] 0) (𝓝 (f' 0)) :=
        (hf' 0 (Set.mem_Ici.2 le_rfl)).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hd x hx).deriv.symm

/-- The regular density family. -/
structure s11q3_Reg (d : ℕ) (ρ D : ℝ → Euc d → ℝ) (c B : ℝ) : Prop where
  hc : 0 < c
  hB : 0 ≤ B
  pos : ∀ t, 0 ≤ t → ∀ x, 0 < ρ t x
  cd : ∀ t, 0 ≤ t → ContDiff ℝ 2 (ρ t)
  g0 : ∀ t, 0 ≤ t → ∀ x, |ρ t x| ≤ B * Real.exp (-c * ‖x‖ ^ 2)
  g1 : ∀ t, 0 ≤ t → ∀ x, ‖fderiv ℝ (ρ t) x‖ ≤ B * Real.exp (-c * ‖x‖ ^ 2)
  g2 : ∀ t, 0 ≤ t → ∀ x, ‖fderiv ℝ (fderiv ℝ (ρ t)) x‖ ≤ B * Real.exp (-c * ‖x‖ ^ 2)
  gD : ∀ t, 0 ≤ t → ∀ x, |D t x| ≤ B * Real.exp (-c * ‖x‖ ^ 2)
  j0 : ContinuousOn (fun p : ℝ × Euc d => ρ p.1 p.2) (Ici 0 ×ˢ univ)
  j1 : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (ρ p.1) p.2) (Ici 0 ×ˢ univ)
  j2 : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ (ρ p.1)) p.2) (Ici 0 ×ˢ univ)
  jD : ContinuousOn (fun p : ℝ × Euc d => D p.1 p.2) (Ici 0 ×ˢ univ)
  dA : ∀ t, 0 < t → ∀ x, HasDerivAt (fun τ => ρ τ x) (D t x) t

variable {d : ℕ} {s : ℝ}

theorem s11q3_convJoint (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    {φ : ℝ → Euc d → ℝ} (hφ : ContinuousOn (fun p : ℝ × Euc d => φ p.1 p.2) (Ici 0 ×ˢ univ))
    (hb : ∀ t, 0 ≤ t → ∀ y, |φ t y| ≤ B * Real.exp (-c * ‖y‖ ^ 2)) :
    ContinuousOn (fun p : ℝ × Euc d => ∫ z, rieszKernel d s z * φ p.1 (p.2 - z)) (Ici 0 ×ˢ univ) := by
  intro p0 hp0
  obtain ⟨hk, hBd, hBint⟩ := mv1_g_data (d := d) (s := s) hd hs0 hsd hc
  set R : ℝ := ‖p0.2‖ + 1 with hR
  have hmap : ∀ z : Euc d, ∀ p : ℝ × Euc d, p ∈ Ici (0 : ℝ) ×ˢ (univ : Set (Euc d)) →
      (p.1, p.2 - z) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (Euc d)) := fun z p hp => ⟨hp.1, mem_univ _⟩
  refine continuousWithinAt_of_dominated (μ := volume)
    (F := fun (p : ℝ × Euc d) (z : Euc d) => rieszKernel d s z * φ p.1 (p.2 - z))
    (bound := fun z => B * Real.exp (c * R ^ 2) *
      ((2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) ?_ ?_ (hBint.const_mul _) ?_
  · refine eventually_nhdsWithin_of_forall fun p hp => ?_
    have hcont : Continuous fun z : Euc d => φ p.1 (p.2 - z) :=
      hφ.comp_continuous (continuous_const.prodMk (continuous_const.sub continuous_id)) (fun z => hmap z p hp)
    exact hk.mul hcont.aestronglyMeasurable
  · have hev : ∀ᶠ p in 𝓝 p0, p.2 ∈ Metric.ball p0.2 1 :=
      continuous_snd.continuousAt.eventually_mem (Metric.ball_mem_nhds p0.2 one_pos)
    have hS : ∀ᶠ p in 𝓝[Ici (0 : ℝ) ×ˢ (univ : Set (Euc d))] p0, p ∈ Ici (0 : ℝ) ×ˢ (univ : Set (Euc d)) :=
      self_mem_nhdsWithin
    filter_upwards [hS, hev.filter_mono nhdsWithin_le_nhds] with p hp hp2
    filter_upwards [hBd] with z hz
    exact mv1_dom_pt0 (k := rieszKernel d s) (B := fun z => 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) hc hB
      (hb p.1 hp.1) (mv1_ball_bound p0.2 hp2) hz
  · refine Filter.Eventually.of_forall fun z => ?_
    have h1 : ContinuousWithinAt (fun p : ℝ × Euc d => (p.1, p.2 - z)) (Ici (0 : ℝ) ×ˢ (univ : Set (Euc d))) p0 :=
      (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousWithinAt
    have h2 := ContinuousWithinAt.comp (f := fun p : ℝ × Euc d => (p.1, p.2 - z))
      (hφ (p0.1, p0.2 - z) (hmap z p0 hp0)) h1 (fun p hp => hmap z p hp)
    exact h2.const_mul _

end HRS.MS.S11Q3

end
