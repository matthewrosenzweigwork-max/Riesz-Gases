import HRS.MS.MfeConfAux115

/-!
# S.B.1, packet F9 (part 19): the time integral of the Gibbs mean `E_{Q^M} C^M` converges (no domination in time needed)

By the level-`M` normaliser identity `d/dt log K_M = βN E_{Q^M} C^M` (`sb1_Mlevel`, `sb1_log_of_integral_eq`) the integral
`∫_0^t E_{Q^M_r} C^M_r dr` equals `(βN)⁻¹ (log K_M(t) - log K_M(0))`, which converges to the same expression for the singular
kernel, i.e. to `∫_0^t E_{Q_r} C_r dr` (`SbLogK`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_EQ_int_tendsto (hT : 0 ≤ T) (hβ : 0 < D.invβ) (hN : 1 ≤ N) (Kf : ℝ → ℝ)
    (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun M => ∫ r in Set.Icc (0 : ℝ) t, sb1_lv_EQ D (sb1kM d D.s M) N ρ r) atTop
      (𝓝 (∫ r in Set.Icc (0 : ℝ) t, sb1EQ D N ρ r)) := by
  have hs0 := H.tr.hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  set β := D.invβ⁻¹ with hβdef
  have hg := sb1KerU_riesz d D.s hs0
  have hL : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ Kf r ∧
      ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kf r * ‖x - y‖ :=
    fun r hr => sb1_lip_of_hasLip (hLip r hr)
  obtain ⟨A2, hA20, hA2⟩ := sb1kM_hk_bound (d := d) D.s hs0
  have hCs : 0 ≤ sb1Cs d D.s C3 := by
    unfold sb1Cs; have := H.C3nn; have := sb1Isig_nonneg (d := d) D.s; positivity
  set CwR := sb1CwR d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) β N with hCwR
  let Φb : ℝ → ℝ := fun r => CwR * (2 * (A2 * Kf r * sb1Cs d D.s C3))
  have hΦb : IntegrableOn Φb (Set.Icc 0 T) := (hKi.const_mul (A2 * sb1Cs d D.s C3 * 2 * CwR)).congr
    (Eventually.of_forall fun r => by simp only [Φb]; ring)
  -- the level-M identities
  have hM : ∀ M : ℕ, β * N * ∫ r in Set.Icc (0 : ℝ) t, sb1_lv_EQ D (sb1kM d D.s M) N ρ r =
      Real.log (sb1Kpi (sb1kM d D.s M) β N ρ t) - Real.log (sb1Kpi (sb1kM d D.s M) β N ρ 0) := by
    intro M
    have hk4 := sb1kM_isKernel (d := d) D.s hs0 M
    obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 hs0
    have hk := sb1kM_ker (d := d) D.s hs0 M
    have hbd : ∀ r ∈ Set.Icc (0 : ℝ) T, |sb1Phipi (sb1kM d D.s M) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r| ≤ Φb r := by
      intro r hr
      refine (sb1_Phi_abs_le hd hs0 hsd hN hβ0.le hk (H.rho hd hr) (mul_nonneg hA20 (hL r hr).1)
        (fun x y => hA2 M (hL r hr).1 (hL r hr).2 x y)).trans (le_of_eq ?_)
      simp only [Φb, hCwR]
    have hid := sb1_Mlevel H hT hβ0 hN hk hRg hΦb hbd (t := t)
    have hIcc0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hKpos : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 < sb1Kpi (sb1kM d D.s M) β N ρ r := fun r hr => by
      unfold sb1Kpi
      exact sb1_Kpi_pos' hd hs0 hsd hN hβ0.le hk (H.rho hd hr)
    have hint : IntervalIntegrable (fun r => β * N * sb1Phipi (sb1kM d D.s M) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r)
        volume 0 T := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
      have hsub : Set.Ioc (0 : ℝ) T ⊆ Set.Icc 0 T := fun r hr => ⟨hr.1.le, hr.2⟩
      refine Integrable.mono' ((hΦb.mono_set hsub).const_mul (β * N))
        (((sb1_Phipi_aesm H hT hβ0 hN hk hRg).mono_set hsub).const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ β * N)]
      exact mul_le_mul_of_nonneg_left (hbd r (hsub hr)) (by positivity)
    obtain ⟨m, hm, hmK, hlog⟩ := sb1_log_of_integral_eq hT hKpos hint (fun s hs => by
      have := sb1_Mlevel H hT hβ0 hN hk hRg hΦb hbd (t := s) hs
      linarith)
    rw [hlog t ht, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.trans ht.2⟩
    rw [sb1_lv_EQ_eq H hk.meas hrT]
    unfold sb1Phipi
    ring
  have hN0 : 0 < β * N := mul_pos hβ0 (Nat.cast_pos.2 (by omega))
  have hconv : ∀ z : Euc d, z ≠ 0 → Tendsto (fun M => sb1kM d D.s M z) atTop (𝓝 (Whole.rieszKernel d D.s z)) :=
    fun z hz => sb1kM_tend D.s hs0 hz
  have hKlim : ∀ r ∈ Set.Icc (0 : ℝ) T, Tendsto (fun M => sb1Kpi (sb1kM d D.s M) β N ρ r) atTop
      (𝓝 (sb1Kpi (Whole.rieszKernel d D.s) β N ρ r)) := fun r hr =>
    sb1_K_tendsto hd hs0 hsd hN hβ0.le (fun M => sb1kM_ker D.s hs0 M) hg hconv (H.rho hd hr)
  have hKpos : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 < sb1Kpi (Whole.rieszKernel d D.s) β N ρ r := fun r hr =>
    sb1_Kpi_pos' hd hs0 hsd hN hβ0.le hg (H.rho hd hr)
  have hIcc0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hlog : Tendsto (fun M => Real.log (sb1Kpi (sb1kM d D.s M) β N ρ t) - Real.log (sb1Kpi (sb1kM d D.s M) β N ρ 0))
      atTop (𝓝 (Real.log (sb1Kpi (Whole.rieszKernel d D.s) β N ρ t) - Real.log (sb1Kpi (Whole.rieszKernel d D.s) β N ρ 0))) :=
    (((Real.continuousAt_log (hKpos t ht).ne').tendsto.comp (hKlim t ht))).sub
      ((Real.continuousAt_log (hKpos 0 hIcc0).ne').tendsto.comp (hKlim 0 hIcc0))
  have hsing : β * N * ∫ r in Set.Icc (0 : ℝ) t, sb1EQ D N ρ r =
      Real.log (sb1Kpi (Whole.rieszKernel d D.s) β N ρ t) - Real.log (sb1Kpi (Whole.rieszKernel d D.s) β N ρ 0) := by
    have := ((sb1_logK_main H hT hβ hN Kf hKi hLip).2 t ht)
    rw [sb1_gibbs_eq_Kpi H ht, sb1_gibbs_eq_Kpi H hIcc0] at this
    exact this.symm
  have e : ∀ M, ∫ r in Set.Icc (0 : ℝ) t, sb1_lv_EQ D (sb1kM d D.s M) N ρ r =
      (β * N)⁻¹ * (Real.log (sb1Kpi (sb1kM d D.s M) β N ρ t) - Real.log (sb1Kpi (sb1kM d D.s M) β N ρ 0)) := by
    intro M
    rw [← hM M]; field_simp
  have e' : ∫ r in Set.Icc (0 : ℝ) t, sb1EQ D N ρ r = (β * N)⁻¹ *
      (Real.log (sb1Kpi (Whole.rieszKernel d D.s) β N ρ t) - Real.log (sb1Kpi (Whole.rieszKernel d D.s) β N ρ 0)) := by
    rw [← hsing]; field_simp
  simp only [e, e']
  exact hlog.const_mul _

end Main

end HRS.MS.MfeConf
