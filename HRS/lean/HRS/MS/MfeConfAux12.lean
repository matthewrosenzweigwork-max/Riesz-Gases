import HRS.MS.MfeConfAux11

/-!
# S.B.1, packet F1 (part 7): the classical time derivative and `IsC12TestRd`

* `sb1_rho_integral`: `ρ_t(x) = ρ_0(x) + ∫_0^t A(ρ_r)(x) dr` for `t ∈ [0,T]`, all `x` (weak interval identity, `sb1_weak_eq_pde`,
  Fubini, and the fundamental lemma of the calculus of variations for the continuous function
  `ρ_t - ρ_0 - ∫_0^t A`);
* `sb1_hasDerivAt`: `∂_t ρ_r(x) = A(ρ_r)(x)` on `(0,T)`;
* `sb1_isC12TestRd`: `ρ` is an `IsC12TestRd` test with time derivative `A(ρ_r)` (the classical regularity needed by the Itô
  calculus of the moving reference, the whole-space `movT_isC12Test_of_weak`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

open HRS.MP.RdGen HRS.MH.DualityRd

variable {d : ℕ} {D : Whole.WholeDyn d} {T C B : ℝ} {ρ : ℝ → Euc d → ℝ}

/-- `A(ρ_r)(x)` with the time clamped to `[0,T]`. -/
def sb1At (D : Whole.WholeDyn d) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (r : ℝ) (x : Euc d) : ℝ :=
  sb1A D (ρ (Set.projIcc (0 : ℝ) T hT r)) x

theorem sb1At_eq {T : ℝ} (hT : 0 ≤ T) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    sb1At D hT ρ r x = sb1A D (ρ r) x := by
  unfold sb1At
  rw [Set.projIcc_of_mem hT hr]

theorem sb1At_cont (H : Sb1Traj D T C B ρ) (hT : 0 ≤ T) :
    Continuous fun p : ℝ × Euc d => sb1At D hT ρ p.1 p.2 := by
  have hc : Continuous fun r : ℝ => (Set.projIcc (0 : ℝ) T hT r) := continuous_projIcc
  exact (sb1_A_joint_cont H).comp ((hc.comp continuous_fst).prodMk continuous_snd)

theorem sb1At_bound (H : Sb1Traj D T C B ρ) (hT : 0 ≤ T) (r : ℝ) (x : Euc d) :
    |sb1At D hT ρ r x| ≤ H.KA :=
  sb1A_bound D H.V H.hd H.hs0 H.hsd (H.slice _ (Set.projIcc (0 : ℝ) T hT r).2) x

set_option maxHeartbeats 1600000 in
theorem sb1_rho_integral (H : Sb1Traj D T C B ρ) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (x : Euc d) : ρ t x = ρ 0 x + ∫ r in (0 : ℝ)..t, sb1At D hT ρ r x := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  set Hf : Euc d → ℝ := fun y => ∫ r in (0 : ℝ)..t, sb1At D hT ρ r y with hHf
  have hHcont : Continuous Hf :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y r => sb1At D hT ρ r y) ((sb1At_cont H hT).comp continuous_swap) 0 t
  set u : Euc d → ℝ := fun y => ρ t y - ρ 0 y - Hf y with hu
  have hucont : Continuous u := ((H.cont ht).sub (H.cont h0)).sub hHcont
  have hz : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∫ y, ψ y • u y = 0 := by
    intro ψ hψ hψc
    have hψ2 : ContDiff ℝ 2 ψ := by exact_mod_cast contDiff_infty.1 hψ 2
    have hint : Integrable ψ := hψ2.continuous.integrable_of_hasCompactSupport hψc
    obtain ⟨-, hw⟩ := sb1_weak_interval H hψ2 hψc
    have hweak := hw 0 t le_rfl ht.1 ht.2
    have hSA : ∀ r ∈ Set.uIcc (0 : ℝ) t, mfGen D ψ (ρ r) = ∫ y, ψ y * sb1At D hT ρ r y := by
      intro r hr
      rw [Set.uIcc_of_le ht.1] at hr
      have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
      rw [sb1_weak_eq_pde D H.V H.hd H.hs0 H.hsd H.hM (H.slice r hrT) (H.reg r hrT) hψ2 hψc]
      simp only [sb1At_eq hT hrT]
    -- Fubini
    have hfub : ∫ y, ψ y * Hf y = ∫ r in (0 : ℝ)..t, ∫ y, ψ y * sb1At D hT ρ r y := by
      have e1 : ∀ y, ψ y * Hf y = ∫ r in Set.Ioc (0 : ℝ) t, ψ y * sb1At D hT ρ r y := fun y => by
        show ψ y * (∫ r in (0 : ℝ)..t, sb1At D hT ρ r y) = _
        rw [intervalIntegral.integral_of_le ht.1, ← integral_const_mul]
      simp_rw [e1]
      rw [intervalIntegral.integral_of_le ht.1]
      refine integral_integral_swap ?_
      have hbd := (hint.norm.mul_prod (integrable_const H.KA) :
        Integrable (fun z : Euc d × ℝ => ‖ψ z.1‖ * H.KA) (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) t))))
      refine hbd.mono' ?_ (Eventually.of_forall fun z => ?_)
      · exact (hψ2.continuous.comp continuous_fst |>.mul
          ((sb1At_cont H hT).comp ((continuous_snd).prodMk continuous_fst))).aestronglyMeasurable
      · rw [Function.uncurry, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (sb1At_bound H hT z.2 z.1) (abs_nonneg _)
    have hp : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) T →
        Whole.pair (Whole.withDensityReal (ρ s)) ψ = ∫ y, ψ y * ρ s y := fun s hs => by
      rw [Whole.Q09A.pair_withDensityReal (H.mf.density s hs)]
      exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    have iρ : ∀ s ∈ Set.Icc (0 : ℝ) T, Integrable fun y => ψ y * ρ s y := fun s hs =>
      (hψ2.continuous.mul (H.cont hs)).integrable_of_hasCompactSupport hψc.mul_right
    have iH : Integrable fun y => ψ y * Hf y :=
      (hψ2.continuous.mul hHcont).integrable_of_hasCompactSupport hψc.mul_right
    have e : (fun y => ψ y • u y) = fun y => (ψ y * ρ t y - ψ y * ρ 0 y) - ψ y * Hf y := by
      funext y; simp only [hu, smul_eq_mul]; ring
    have i1 : Integrable fun y => ψ y * ρ t y - ψ y * ρ 0 y := (iρ t ht).sub (iρ 0 h0)
    rw [e, integral_sub i1 iH, integral_sub (iρ t ht) (iρ 0 h0), hfub,
      ← hp t ht, ← hp 0 h0, hweak]
    rw [sub_eq_zero]
    exact intervalIntegral.integral_congr hSA
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hucont.locallyIntegrable hz
  have hu0 : u = 0 := (Continuous.ae_eq_iff_eq volume hucont continuous_const).1 hae
  have := congrFun hu0 x
  simp only [hu, Pi.zero_apply] at this
  linarith

set_option maxHeartbeats 1600000 in
theorem sb1_hasDerivAt (H : Sb1Traj D T C B ρ) (hT : 0 ≤ T) {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) T)
    (x : Euc d) : HasDerivAt (fun r => ρ r x) (sb1A D (ρ r₀) x) r₀ := by
  have hcont : Continuous fun r : ℝ => sb1At D hT ρ r x := by
    have h1 : Continuous fun r : ℝ => ((r, x) : ℝ × Euc d) := Continuous.prodMk continuous_id continuous_const
    exact (sb1At_cont H hT).comp h1
  have hd : HasDerivAt (fun r => ∫ s in (0 : ℝ)..r, sb1At D hT ρ s x) (sb1At D hT ρ r₀ x) r₀ :=
    (Continuous.integral_hasStrictDerivAt (f := fun r => sb1At D hT ρ r x) hcont 0 r₀).hasDerivAt
  have hev : (fun r => ρ r x) =ᶠ[𝓝 r₀] fun r => ρ 0 x + ∫ s in (0 : ℝ)..r, sb1At D hT ρ s x := by
    filter_upwards [Ioo_mem_nhds hr₀.1 hr₀.2] with r hr
    exact sb1_rho_integral H hT ⟨hr.1.le, hr.2.le⟩ x
  have := (hd.const_add (ρ 0 x)).congr_of_eventuallyEq hev
  rwa [sb1At_eq hT ⟨hr₀.1.le, hr₀.2.le⟩] at this

/-- **F1 (whole-space `movT_isC12Test_of_weak`)**: the mean-field trajectory is a classical `C^{1,2}` test with time
derivative `A(ρ_r)`. -/
theorem sb1_isC12TestRd (H : Sb1Traj D T C B ρ) (hT : 0 ≤ T) :
    IsC12TestRd T ρ (fun r x => sb1A D (ρ r) x) where
  c2 := fun r hr => (H.slice r hr).decay.1.of_le (by norm_num)
  bdd := fun j hj => ⟨C, fun r hr x => by
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]; exact (sb1_slice_facts (H.slice r hr)).2.2.2.2.2 x
    · rw [norm_iteratedFDeriv_one]; exact (sb1_slice_facts (H.slice r hr)).2.2.2.1 x
    · exact (sb1_slice_D23 (H.slice r hr) x).1⟩
  cont_c2 := fun j hj => sb1_jet_cont H j hj
  time_deriv := fun x r hr => sb1_hasDerivAt H hT hr x
  cont_time_deriv := sb1_A_joint_cont H
  lin_growth := ⟨H.KA, fun r hr x => by
    refine (sb1A_bound D H.V H.hd H.hs0 H.hsd (H.slice r hr) x).trans ?_
    have hK := H.KA_nonneg
    have hKA : H.KA = sb1KA d D.invβ C B ‖fderiv ℝ D.V 0‖ (sb1BF d D.s C) := rfl
    rw [← hKA]
    nlinarith [norm_nonneg x]⟩

end HRS.MS.MfeConf
