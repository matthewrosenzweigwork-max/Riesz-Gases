import HRS.MS.SA16Y5Ap3f
import HRS.MS.SA16Y5Li2

/-!
# S.A.16 (SA16Y5) Li2f: pairing bounds, weak integrand and equi-Lipschitz estimate for the fractional-order approximations (B9)

`sa16y5f_B_pair_bound`: `|ℓ_{m+1,ψ}(B_bc y)| ≤ cN V ‖ι² y‖`.
`sa16y5f_weak_integrand`: the weak identity of `sa16y5f_weak` with a continuous integrand `f` bounded by `L Bm` (`L` depends on `ψ, ν, cN, Cn`).
`sa16y5f_lip`: the pairing `τ ↦ ℓ_{m+2,ψ}(u τ)` is Lipschitz with constant `L Bm`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Li2f
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y5f_B_pair_bound {m : ℕ} {B' cN R0 : ℝ} {bc : Fin d → Euc d → ℝ}
    (hbo : SA16BddCoef (m + 1) B' bc) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (hNb : ∀ x, |sa16so_divFun bc ψ x| ≤ cN * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) x)
    (hcN : 0 ≤ cN) (y : WmpSpace d (m + 1 + 1) p) :
    |sa16r_ell d (m + 1) p hψ (sa16so_B d (m + 1) p bc y)| ≤
      cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) * ‖sa16sz_iota2 d m p y‖ := by
  rw [sa16so_ell_B hbo hψ y, abs_neg, ← sa16y3_ell_iota2 (sa16so_cc_div hbo hψ), sa16r_ell_apply]
  exact sa16y3_ell_sup_bound _ (sa16so_cc_div hbo hψ).1.continuous.aestronglyMeasurable hcN hNb

set_option maxHeartbeats 3200000 in
theorem sa16y5f_weak_integrand {m : ℕ} {ν T B' BB BN CN γ Cn cN R0 Bm : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hcN : 0 ≤ cN) (hCn : 0 ≤ Cn)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbo : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hBf : ∀ r, Bf r = sa16so_B d (m + 1) p (bc r))
    (hBb : ∀ r ∈ Icc (0 : ℝ) T, ‖Bf r‖ ≤ BB) (hBc : ∀ x, ContinuousOn (fun r => Bf r x) (Icc 0 T))
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hNb : ∀ r ∈ Icc (0 : ℝ) T, ‖Nf r‖ ≤ BN) (hNc : ∀ x, ContinuousOn (fun r => Nf r x) (Icc 0 T))
    (hsharp : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T, ‖sa16y5_Qh d m p (ν * s) (Nf r)‖ ≤ CN * s ^ (-γ))
    (hiota : ∀ r ∈ Icc (0 : ℝ) T, ∀ a : ℝ, 0 < a → ∀ x : WmpSpace d (m + 1 + 1) p,
      sa16r_iota d (m + 1) p (sa16y5_Qh d m p a (Nf r) x) = sa16r_Gam d m p a (Nf r x))
    (φ : WmpSpace d (m + 1 + 1) p) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (hNn : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, |sa16r_ell d m p hψ (Nf r y)| ≤ Cn * ‖sa16sz_iota2 d m p y‖)
    (hdiv : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, |sa16so_divFun (bc r) ψ x| ≤
      cN * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) x)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (fun τ s => sa16y5f_kernel d m p ν Bf Nf s (τ - s)) u τ)
    (hbd : ∀ r ∈ Icc (0 : ℝ) T, ‖sa16sz_iota2 d m p (u r)‖ ≤ Bm) :
    let f : ℝ → ℝ := fun σ => ν * sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u σ) +
      (sa16r_ell d (m + 1) p hψ (Bf σ (u σ)) - sa16r_ell d m p hψ (Nf σ (u σ)))
    (∀ τ ∈ Icc (0 : ℝ) T, sa16r_ell d (m + 1 + 1) p hψ (u τ) =
        sa16r_ell d (m + 1 + 1) p hψ φ + ∫ σ in (0 : ℝ)..τ, f σ) ∧
      ContinuousOn f (Icc 0 T) ∧
      ∀ σ ∈ Icc (0 : ℝ) T, |f σ| ≤ (ν * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ +
        cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) + Cn) * Bm := by
  intro f
  have hid := sa16y5f_weak hν hT hγ hγ1 Bf hBb hBc Nf hNb hNc hsharp hiota φ hu hsol hψ
  have hcont : ContinuousOn f (Icc 0 T) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.mul ((sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ)).continuous.comp_continuousOn hu)
    · refine ContinuousOn.sub ?_ ?_
      · refine (sa16r_ell d (m + 1) p hψ).continuous.comp_continuousOn ?_
        intro a ha
        exact sa16r_clm_apply_strong (S := Icc 0 T) (B := BB) (fun v => hBc v a ha)
          (eventually_nhdsWithin_of_forall fun q hq => hBb q hq) (hu a ha)
      · refine (sa16r_ell d m p hψ).continuous.comp_continuousOn ?_
        intro a ha
        exact sa16r_clm_apply_strong (S := Icc 0 T) (B := BN) (fun v => hNc v a ha)
          (eventually_nhdsWithin_of_forall fun q hq => hNb q hq) (hu a ha)
  refine ⟨fun τ hτ => hid τ hτ, hcont, fun σ hσ => ?_⟩
  have hBm0 : 0 ≤ Bm := (norm_nonneg _).trans (hbd 0 ⟨le_rfl, hT.le⟩)
  have h1 : |sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u σ)| ≤ ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ * Bm := by
    rw [← sa16y3_ell_iota2 (sa16sw_cc_lap hψ), ← Real.norm_eq_abs]
    exact ((sa16r_ell d m p _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hbd σ hσ) (ContinuousLinearMap.opNorm_nonneg _))
  have h2 : |sa16r_ell d (m + 1) p hψ (Bf σ (u σ))| ≤
      cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) * Bm := by
    rw [hBf σ]
    exact (sa16y5f_B_pair_bound (hbo σ hσ) hψ (hdiv σ hσ) hcN (u σ)).trans
      (mul_le_mul_of_nonneg_left (hbd σ hσ) (mul_nonneg hcN (Real.rpow_nonneg ENNReal.toReal_nonneg _)))
  have h3 : |sa16r_ell d m p hψ (Nf σ (u σ))| ≤ Cn * Bm :=
    (hNn σ hσ _).trans (mul_le_mul_of_nonneg_left (hbd σ hσ) hCn)
  calc |f σ| ≤ |ν * sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u σ)| +
        (|sa16r_ell d (m + 1) p hψ (Bf σ (u σ))| + |sa16r_ell d m p hψ (Nf σ (u σ))|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        exact abs_sub _ _
    _ ≤ ν * (‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ * Bm) + (cN * (volume (closedBall (0 : Euc d) R0)).toReal ^
        (1 / Real.conjExponent p) * Bm + Cn * Bm) := by
        refine add_le_add ?_ (add_le_add h2 h3)
        rw [abs_mul, abs_of_pos hν]
        exact mul_le_mul_of_nonneg_left h1 hν.le
    _ = _ := by ring

theorem sa16y5f_lip {m : ℕ} {ν T B' BB BN CN γ Cn cN R0 Bm : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hcN : 0 ≤ cN) (hCn : 0 ≤ Cn)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbo : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hBf : ∀ r, Bf r = sa16so_B d (m + 1) p (bc r))
    (hBb : ∀ r ∈ Icc (0 : ℝ) T, ‖Bf r‖ ≤ BB) (hBc : ∀ x, ContinuousOn (fun r => Bf r x) (Icc 0 T))
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hNb : ∀ r ∈ Icc (0 : ℝ) T, ‖Nf r‖ ≤ BN) (hNc : ∀ x, ContinuousOn (fun r => Nf r x) (Icc 0 T))
    (hsharp : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T, ‖sa16y5_Qh d m p (ν * s) (Nf r)‖ ≤ CN * s ^ (-γ))
    (hiota : ∀ r ∈ Icc (0 : ℝ) T, ∀ a : ℝ, 0 < a → ∀ x : WmpSpace d (m + 1 + 1) p,
      sa16r_iota d (m + 1) p (sa16y5_Qh d m p a (Nf r) x) = sa16r_Gam d m p a (Nf r x))
    (φ : WmpSpace d (m + 1 + 1) p) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (hNn : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, |sa16r_ell d m p hψ (Nf r y)| ≤ Cn * ‖sa16sz_iota2 d m p y‖)
    (hdiv : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, |sa16so_divFun (bc r) ψ x| ≤
      cN * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) x)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (fun τ s => sa16y5f_kernel d m p ν Bf Nf s (τ - s)) u τ)
    (hbd : ∀ r ∈ Icc (0 : ℝ) T, ‖sa16sz_iota2 d m p (u r)‖ ≤ Bm) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ τ' ∈ Icc (0 : ℝ) T,
      |sa16r_ell d (m + 1 + 1) p hψ (u τ) - sa16r_ell d (m + 1 + 1) p hψ (u τ')| ≤
        (ν * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ + cN * (volume (closedBall (0 : Euc d) R0)).toReal ^
          (1 / Real.conjExponent p) + Cn) * Bm * |τ - τ'| := by
  obtain ⟨hid, hcont, hb⟩ := sa16y5f_weak_integrand hν hT hγ hγ1 hcN hCn bc hbo Bf hBf hBb hBc Nf hNb hNc
    hsharp hiota φ hψ hNn hdiv hu hsol hbd
  intro τ hτ τ' hτ'
  set f : ℝ → ℝ := fun σ => ν * sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u σ) +
      (sa16r_ell d (m + 1) p hψ (Bf σ (u σ)) - sa16r_ell d m p hψ (Nf σ (u σ))) with hf
  have hii : ∀ x ∈ Icc (0 : ℝ) T, IntervalIntegrable f volume 0 x := fun x hx =>
    (hcont.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
  have e : sa16r_ell d (m + 1 + 1) p hψ (u τ) - sa16r_ell d (m + 1 + 1) p hψ (u τ') =
      ∫ σ in τ'..τ, f σ := by
    rw [hid τ hτ, hid τ' hτ', ← intervalIntegral.integral_interval_sub_left (hii τ hτ) (hii τ' hτ')]
    ring
  rw [e]
  have hL : ∀ σ ∈ Set.uIoc τ' τ, ‖f σ‖ ≤ (ν * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ + cN *
      (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) + Cn) * Bm := by
    intro σ hσ
    have hσ' : σ ∈ Icc (0 : ℝ) T := by
      rcases le_total τ' τ with h | h
      · rw [Set.uIoc_of_le h] at hσ; exact ⟨by linarith [hτ'.1, hσ.1], by linarith [hτ.2, hσ.2]⟩
      · rw [Set.uIoc_of_ge h] at hσ; exact ⟨by linarith [hτ.1, hσ.1], by linarith [hτ'.2, hσ.2]⟩
    rw [Real.norm_eq_abs]
    exact hb σ hσ'
  have := intervalIntegral.norm_integral_le_of_norm_le_const hL
  simpa [Real.norm_eq_abs] using this

end Li2f

end HRS.Whole.AppendixA.Phase2SA16R
