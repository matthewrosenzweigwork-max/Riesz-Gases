import HRS.MS.S111X2Aux31

/-!
# S11.1 X2, packet E07: the generator orbit and the Dirichlet derivative

`s111x2_generator_orbit`: for `f` the classical solution with terminal datum `φ ∈ C_b²` and `h` the classical solution
with terminal datum `Gφ`, put `F t = f (H-t)`, `G_t = h (H-t)`.  Then `F t = φ + ∫_0^t G_r`, `∂_t F = G_t = G F_t`,
`t ↦ D(F_t,F_t)` is absolutely continuous on `[0,H]` with derivative `-2β C_β(G_t,G_t)` on `(0,H)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- **E07.** -/
theorem s111x2_generator_orbit (hd : 2 ≤ d) {s a β H : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hH : 0 < H) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ)
    {φ : Euc d → ℝ} (hφ : MemCb 2 φ) {f h : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H φ f)
    (hh : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H
      (generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 φ) h) :
    (∀ t ∈ Icc (0 : ℝ) H, ∀ x, f (H - t) x = φ x + ∫ r in Icc (0 : ℝ) t, h (H - r) x) ∧
    (∀ t ∈ Ioo (0 : ℝ) H, ∀ x, HasDerivAt (fun r => f (H - r) x) (h (H - t) x) t) ∧
    (∀ t ∈ Icc (0 : ℝ) H, generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (f (H - t)) =
      h (H - t)) ∧
    AbsolutelyContinuousOnInterval (fun t => s111x2_dirichlet (HRS.Whole.withDensityReal ρ)
      (f (H - t)) (f (H - t))) 0 H ∧
    ∀ t ∈ Ioo (0 : ℝ) H, HasDerivAt (fun r => s111x2_dirichlet (HRS.Whole.withDensityReal ρ)
      (f (H - r)) (f (H - r)))
      (-2 * β * HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
        (h (H - t)) (h (H - t))) t := by
  obtain ⟨hfun, hrep, hcomm⟩ := s111x2_orbit_bridge hd hs0 hs ha hβ hH hρ hφ hf hh
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T.prob
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hCdef
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨A0, A1, A2, hA0, hA0', hφC⟩ := s111x2_cb2_bounds hφ
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hfam, hB0'⟩ := s111x2_clamp_fam hH.le hh
  obtain ⟨Bf0, Bf1, Bf2, hBf0, hBf1, hBf2, hfB⟩ := HRS.MS.S111X1.classical_bounds hf
  obtain ⟨Bh0, Bh1, Bh2, hBh0, hBh1, hBh2, hhB⟩ := HRS.MS.S111X1.classical_bounds hh
  have hmemI : ∀ t ∈ Icc (0 : ℝ) H, H - t ∈ Icc (0 : ℝ) H := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hfC : ∀ r ∈ Icc (0 : ℝ) H, CbD (f r) Bf1 Bf2 := fun r hr =>
    ⟨hf.c2 r hr, fun x => (hfB r hr x).2.1, fun x => (hfB r hr x).2.2⟩
  have hhC : ∀ r ∈ Icc (0 : ℝ) H, CbD (h r) Bh1 Bh2 := fun r hr =>
    ⟨hh.c2 r hr, fun x => (hhB r hr x).2.1, fun x => (hhB r hr x).2.2⟩
  have hhb : ∀ r ∈ Icc (0 : ℝ) H, s111x2_clamp H r = r := fun r hr => s111x2_clamp_id hr
  -- (3) the generator commutes with the flow
  have h3 : ∀ t ∈ Icc (0 : ℝ) H, generatorW C 0 (f (H - t)) = h (H - t) := fun t ht =>
    hcomm (H - t) (hmemI t ht)
  -- the Dirichlet energy on the whole line, through the explicit family
  set hb : ℝ → Euc d → ℝ := fun u => h (s111x2_clamp H u) with hbdef
  have hDc : Continuous fun t => s111x2_dirichlet μ (s111x2_Ftil φ hb H (H - t)) (s111x2_Ftil φ hb H (H - t)) :=
    continuous_iff_continuousAt.2 fun t => (s111x2_dirichlet_deriv T hfam hφC H t).continuousAt
  have hder0 : ∀ t ∈ Ioo (0 : ℝ) H, HasDerivAt (fun r => s111x2_dirichlet μ (f (H - r)) (f (H - r)))
      (2 * s111x2_dirichlet μ (f (H - t)) (h (H - t))) t := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) H := ⟨ht.1.le, ht.2.le⟩
    have hD := s111x2_dirichlet_deriv T hfam hφC H t
    have hev : (fun r => s111x2_dirichlet μ (f (H - r)) (f (H - r))) =ᶠ[nhds t]
        fun r => s111x2_dirichlet μ (s111x2_Ftil φ hb H (H - r)) (s111x2_Ftil φ hb H (H - r)) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      rw [hfun (H - r) (hmemI r ⟨hr.1.le, hr.2.le⟩)]
    have := hD.congr_of_eventuallyEq hev
    have e1 : s111x2_Ftil φ hb H (H - t) = f (H - t) := (hfun _ (hmemI t htI)).symm
    have e2 : hb (H - t) = h (H - t) := by
      simp only [hbdef]; rw [s111x2_clamp_id (hmemI t htI)]
    rw [e1, e2] at this
    exact this
  have hder1 : ∀ t ∈ Ioo (0 : ℝ) H, HasDerivAt (fun r => s111x2_dirichlet μ (f (H - r)) (f (H - r)))
      (-2 * β * HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β (h (H - t)) (h (H - t))) t := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) H := ⟨ht.1.le, ht.2.le⟩
    have hmI := hmemI t htI
    have hs1 := s111x2_susc_gen T (hfC (H - t) hmI) ((hhC (H - t) hmI).smooth.of_le (by norm_num))
      (fun x => (hhB (H - t) hmI x).1) (fun x => (hhB (H - t) hmI x).2.1)
    rw [h3 t htI] at hs1
    refine (hder0 t ht).congr_deriv ?_
    rw [s111x2_dirichlet_symm μ (f (H - t)) (h (H - t))]
    have hβ' : β ≠ 0 := hβ.ne'
    rw [hs1]
    field_simp
    rfl
  refine ⟨?_, ?_, h3, ?_, ?_⟩
  · -- (1) integral representation
    intro t ht x
    rw [hrep (H - t) (hmemI t ht) x, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1,
      intervalIntegral.integral_comp_sub_left (fun u => h u x) H, sub_zero]
  · -- (2) time derivative
    intro t ht x
    have htI : t ∈ Icc (0 : ℝ) H := ⟨ht.1.le, ht.2.le⟩
    have hr : H - t ∈ Ioo (0 : ℝ) H := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h1 := hf.time_deriv x (H - t) hr
    rw [s111x2_gen_auto T (hfC (H - t) (hmemI t htI)) (H - t), h3 t htI] at h1
    have h2 : HasDerivAt (fun r : ℝ => H - r) (-1) t := by simpa using (hasDerivAt_id t).const_sub H
    have := h1.comp t h2
    exact this.congr_deriv (by ring)
  · -- (4) absolute continuity
    have hcont : ContinuousOn (fun t => s111x2_dirichlet μ (f (H - t)) (f (H - t))) (Icc 0 H) := by
      refine hDc.continuousOn.congr fun t ht => ?_
      simp only
      rw [hfun (H - t) (hmemI t ht)]
    refine s111x2_ac_of_deriv_bdd (K := 2 * (Bf1 * Bh1)) hH hcont hder0 fun t ht => ?_
    have htI : t ∈ Icc (0 : ℝ) H := ⟨ht.1.le, ht.2.le⟩
    have hmI := hmemI t htI
    have := s111x2_dirichlet_bound T (fun x => (hfB (H - t) hmI x).2.1) (fun x => (hhB (H - t) hmI x).2.1)
    rw [abs_mul, abs_two]
    linarith
  · exact hder1

end HRS.MS.S111X2
