import HRS.MS.SA16Y5Mi2
import HRS.MS.SA16SHw4

/-!
# S.A.16 (SA16Y5) Mi3: weak heat identity for the Volterra kernel (B8, part 3)

`sa16y5f_HE`: for `r ∈ [0,T]`, `s ∈ (0,T]`, `x ∈ W^{m+2,p}` and a test function `ψ`:
`ℓ_ψ(Q s r x) = ℓ_ψ(B_r x) - ℓ_ψ(N_r x) + ∫_0^s ν ℓ_{Δψ}(Q σ r x) dσ`, from `SA16RHeatWeak` for `Γ` at levels `m` and `m+1` and `ι (Qh a N x) = Γ_a (N x)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Mi3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y5_int_sing {f : ℝ → ℝ} {γ c s : ℝ} (hγ1 : γ < 1) (hs : 0 < s) (hc : ContinuousOn f (Ioc 0 s))
    (hb : ∀ σ ∈ Ioc (0 : ℝ) s, |f σ| ≤ c * σ ^ (-γ)) : IntervalIntegrable f volume 0 s := by
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le).2 ?_
  refine Integrable.mono' ((sa16y5g_rpow_int hγ1 s).const_mul c) (hc.aestronglyMeasurable measurableSet_Ioc) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun σ hσ => by rw [Real.norm_eq_abs]; exact hb σ hσ

set_option maxHeartbeats 1600000 in
theorem sa16y5f_HE {m : ℕ} {ν T BB CN γ : ℝ} (hν : 0 < ν) (hT : 0 < T) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hBb : ∀ r ∈ Icc (0 : ℝ) T, ‖Bf r‖ ≤ BB)
    (hBc : ∀ x, ContinuousOn (fun r => Bf r x) (Icc 0 T))
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hNc : ∀ x, ContinuousOn (fun r => Nf r x) (Icc 0 T))
    (hsharp : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T, ‖sa16y5_Qh d m p (ν * s) (Nf r)‖ ≤ CN * s ^ (-γ))
    (hiota : ∀ r ∈ Icc (0 : ℝ) T, ∀ a : ℝ, 0 < a → ∀ x : WmpSpace d (m + 1 + 1) p,
      sa16r_iota d (m + 1) p (sa16y5_Qh d m p a (Nf r) x) = sa16r_Gam d m p a (Nf r x))
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (x : WmpSpace d (m + 1 + 1) p) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) T) :
    sa16r_ell d (m + 1 + 1) p hψ (sa16y5f_kernel d m p ν Bf Nf s r x) =
      (sa16r_ell d (m + 1) p hψ (Bf r x) - sa16r_ell d m p hψ (Nf r x)) +
        ∫ σ in (0 : ℝ)..s, ν * sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (sa16y5f_kernel d m p ν Bf Nf σ r x) := by
  obtain ⟨C, hC0, hb, hc⟩ := sa16y5f_voltKer hν hT hγ hγ1 Bf hBb hBc Nf hNc hsharp
  set hχ := sa16sw_cc_lap hψ with hχdef
  have hBw := (sa16sw_heatWeak (p := p) hν T (m + 1) hψ).1 (Bf r x) s hs
  have hNw := (sa16sw_heatWeak (p := p) hν T m hψ).1 (Nf r x) s hs
  -- the pieces
  have hker : ∀ σ, sa16y5f_kernel d m p ν Bf Nf σ r x =
      sa16r_GamT d (m + 1) p ν σ (Bf r x) - sa16y5_Qh d m p (ν * σ) (Nf r) x := by
    intro σ; rfl
  have hQ : ∀ σ ∈ Ioc (0 : ℝ) T, sa16r_ell d (m + 1 + 1) p hχ (sa16y5_Qh d m p (ν * σ) (Nf r) x) =
      sa16r_ell d (m + 1) p hχ (sa16r_GamT d m p ν σ (Nf r x)) := by
    intro σ hσ
    rw [← sa16r_ell_iota hχ (m + 1), hiota r hr (ν * σ) (mul_pos hν hσ.1) x]
    rfl
  -- integrability of the full integrand and of the `Γ B` part
  have hint_full : IntervalIntegrable (fun σ => ν * sa16r_ell d (m + 1 + 1) p hχ
      (sa16y5f_kernel d m p ν Bf Nf σ r x)) volume 0 s := by
    refine sa16y5_int_sing (c := ν * ‖sa16r_ell d (m + 1 + 1) p hχ‖ * C * ‖x‖) hγ1 hs.1 ?_ ?_
    · have h1 : ContinuousOn (fun σ : ℝ => sa16y5f_kernel d m p ν Bf Nf σ r x) (Ioc 0 s) := by
        have hmap : ContinuousOn (fun σ : ℝ => (r, σ)) (Ioc 0 s) :=
          (continuous_const.prodMk continuous_id).continuousOn
        have hmem : ∀ σ ∈ Ioc (0 : ℝ) s, (fun σ : ℝ => (r, σ)) σ ∈
            {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T} :=
          fun σ hσ => ⟨hr, hσ.1, hσ.2.trans hs.2⟩
        have h := (hc x).comp hmap hmem
        refine h.congr (fun σ _ => ?_)
        rfl
      exact continuousOn_const.mul ((sa16r_ell d (m + 1 + 1) p hχ).continuous.comp_continuousOn h1)
    · intro σ hσ
      have h1 := hb r hr σ ⟨hσ.1, hσ.2.trans hs.2⟩
      rw [abs_mul, abs_of_pos hν]
      calc ν * |sa16r_ell d (m + 1 + 1) p hχ (sa16y5f_kernel d m p ν Bf Nf σ r x)| ≤
          ν * (‖sa16r_ell d (m + 1 + 1) p hχ‖ * (‖sa16y5f_kernel d m p ν Bf Nf σ r‖ * ‖x‖)) := by
            refine mul_le_mul_of_nonneg_left ?_ hν.le
            rw [← Real.norm_eq_abs]
            exact ((sa16r_ell d (m + 1 + 1) p hχ).le_opNorm _).trans
              (mul_le_mul_of_nonneg_left ((sa16y5f_kernel d m p ν Bf Nf σ r).le_opNorm x) (norm_nonneg _))
        _ ≤ ν * (‖sa16r_ell d (m + 1 + 1) p hχ‖ * ((C * σ ^ (-γ)) * ‖x‖)) := by
            gcongr
        _ = _ := by ring
  have hint_B : IntervalIntegrable (fun σ => ν * sa16r_ell d (m + 1 + 1) p hχ
      (sa16r_GamT d (m + 1) p ν σ (Bf r x))) volume 0 s := by
    refine sa16y5_int_sing (γ := 1 / 2) (c := ν * ‖sa16r_ell d (m + 1 + 1) p hχ‖ * sa16r_Cgam d ν T * ‖Bf r x‖)
      (by norm_num) hs.1 ?_ ?_
    · exact continuousOn_const.mul ((sa16r_ell d (m + 1 + 1) p hχ).continuous.comp_continuousOn
        ((sa16r_GamT_cont hν (m + 1) (Bf r x)).mono (Ioc_subset_Ioc_right hs.2)))
    · intro σ hσ
      have h1 := sa16r_GamT_bound (d := d) (p := p) hν (m + 1) hσ.1 (hσ.2.trans hs.2)
      rw [abs_mul, abs_of_pos hν]
      calc ν * |sa16r_ell d (m + 1 + 1) p hχ (sa16r_GamT d (m + 1) p ν σ (Bf r x))| ≤
          ν * (‖sa16r_ell d (m + 1 + 1) p hχ‖ * (‖sa16r_GamT d (m + 1) p ν σ‖ * ‖Bf r x‖)) := by
            refine mul_le_mul_of_nonneg_left ?_ hν.le
            rw [← Real.norm_eq_abs]
            exact ((sa16r_ell d (m + 1 + 1) p hχ).le_opNorm _).trans
              (mul_le_mul_of_nonneg_left ((sa16r_GamT d (m + 1) p ν σ).le_opNorm _) (norm_nonneg _))
        _ ≤ ν * (‖sa16r_ell d (m + 1 + 1) p hχ‖ * ((sa16r_Cgam d ν T * σ ^ (-(1 / 2 : ℝ))) * ‖Bf r x‖)) := by
            gcongr
        _ = _ := by ring
  have hsplit : ∫ σ in (0 : ℝ)..s, ν * sa16r_ell d (m + 1 + 1) p hχ (sa16y5f_kernel d m p ν Bf Nf σ r x) =
      (∫ σ in (0 : ℝ)..s, ν * sa16r_ell d (m + 1 + 1) p hχ (sa16r_GamT d (m + 1) p ν σ (Bf r x))) -
      ∫ σ in (0 : ℝ)..s, ν * sa16r_ell d (m + 1) p hχ (sa16r_GamT d m p ν σ (Nf r x)) := by
    have hNint : IntervalIntegrable (fun σ => ν * sa16r_ell d (m + 1) p hχ (sa16r_GamT d m p ν σ (Nf r x)))
        volume 0 s := by
      have : (fun σ => ν * sa16r_ell d (m + 1) p hχ (sa16r_GamT d m p ν σ (Nf r x))) =ᵐ[volume.restrict (Ioc 0 s)]
          fun σ => ν * sa16r_ell d (m + 1 + 1) p hχ (sa16r_GamT d (m + 1) p ν σ (Bf r x)) -
            ν * sa16r_ell d (m + 1 + 1) p hχ (sa16y5f_kernel d m p ν Bf Nf σ r x) := by
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
        refine Eventually.of_forall fun σ hσ => ?_
        rw [hker σ, map_sub, hQ σ ⟨hσ.1, hσ.2.trans hs.2⟩]
        ring
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1.le).2 ?_
      exact (((intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1.le).1 hint_B).sub
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1.le).1 hint_full)).congr this.symm
    rw [← intervalIntegral.integral_sub hint_B hNint]
    rw [intervalIntegral.integral_of_le hs.1.le, intervalIntegral.integral_of_le hs.1.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
    beta_reduce
    rw [hker σ, map_sub, hQ σ ⟨hσ.1, hσ.2.trans hs.2⟩]
    ring
  rw [hker s, map_sub, hsplit]
  have hQs : sa16r_ell d (m + 1 + 1) p hψ (sa16y5_Qh d m p (ν * s) (Nf r) x) =
      sa16r_ell d (m + 1) p hψ (sa16r_GamT d m p ν s (Nf r x)) := by
    rw [← sa16r_ell_iota hψ (m + 1), hiota r hr (ν * s) (mul_pos hν hs.1) x]
    rfl
  rw [hQs, hBw, hNw]
  ring

end Mi3

end HRS.Whole.AppendixA.Phase2SA16R
