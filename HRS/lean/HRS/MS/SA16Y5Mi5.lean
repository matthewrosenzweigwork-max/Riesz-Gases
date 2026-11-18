import HRS.MS.SA16Y5Mi4

/-!
# S.A.16 (SA16Y5) Mi5: strong form of the fractional-order mild solution (B8, part 5)

`sa16y5f_f_cont`, `sa16y5f_strong`: `ι² (u τ) = ι² φ + ∫_0^τ f`, `f r = ν Δ u r + ι (B_r u r) - N_r u r ∈ W^{m,p}`;
`sa16y5f_hasDerivAt`: `HasDerivAt (r ↦ ι² (u r)) (f τ) τ` for `τ ∈ (0,T)` (copy of `sa16sx_strong`, `sa16sx_hasDerivAt`, `SA16SSt1`, with `N` in `W^m`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Mi5
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y5f_f_cont {m : ℕ} {ν T BB BN : ℝ}
    {Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p} (hBb : ∀ r ∈ Icc (0 : ℝ) T, ‖Bf r‖ ≤ BB)
    (hBc : ∀ x, ContinuousOn (fun r => Bf r x) (Icc 0 T))
    {Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p} (hNb : ∀ r ∈ Icc (0 : ℝ) T, ‖Nf r‖ ≤ BN)
    (hNc : ∀ x, ContinuousOn (fun r => Nf r x) (Icc 0 T))
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T)) :
    ContinuousOn (sa16y5f_f m ν Bf Nf u) (Icc 0 T) := by
  unfold sa16y5f_f
  refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
  · exact ((sa16so_Lap d m p).continuous.comp_continuousOn hu).const_smul ν
  · refine (sa16r_iota d m p).continuous.comp_continuousOn ?_
    intro a ha
    exact sa16r_clm_apply_strong (S := Icc 0 T) (B := BB) (fun v => hBc v a ha)
      (eventually_nhdsWithin_of_forall fun q hq => hBb q hq) (hu a ha)
  · intro a ha
    exact sa16r_clm_apply_strong (S := Icc 0 T) (B := BN) (fun v => hNc v a ha)
      (eventually_nhdsWithin_of_forall fun q hq => hNb q hq) (hu a ha)

set_option maxHeartbeats 3200000 in
theorem sa16y5f_strong {m : ℕ} {ν T BB BN CN γ : ℝ} (hν : 0 < ν) (hT : 0 < T) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hBb : ∀ r ∈ Icc (0 : ℝ) T, ‖Bf r‖ ≤ BB)
    (hBc : ∀ x, ContinuousOn (fun r => Bf r x) (Icc 0 T))
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hNb : ∀ r ∈ Icc (0 : ℝ) T, ‖Nf r‖ ≤ BN)
    (hNc : ∀ x, ContinuousOn (fun r => Nf r x) (Icc 0 T))
    (hsharp : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T, ‖sa16y5_Qh d m p (ν * s) (Nf r)‖ ≤ CN * s ^ (-γ))
    (hiota : ∀ r ∈ Icc (0 : ℝ) T, ∀ a : ℝ, 0 < a → ∀ x : WmpSpace d (m + 1 + 1) p,
      sa16r_iota d (m + 1) p (sa16y5_Qh d m p a (Nf r) x) = sa16r_Gam d m p a (Nf r x))
    (φ : WmpSpace d (m + 1 + 1) p) {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (fun τ s => sa16y5f_kernel d m p ν Bf Nf s (τ - s)) u τ) :
    ∀ τ ∈ Icc (0 : ℝ) T, sa16r_iota d m p (sa16r_iota d (m + 1) p (u τ)) =
      sa16r_iota d m p (sa16r_iota d (m + 1) p φ) + ∫ r in (0 : ℝ)..τ, sa16y5f_f m ν Bf Nf u r := by
  intro τ hτ
  have hfc := sa16y5f_f_cont (ν := ν) hBb hBc hNb hNc hu
  have hii : IntervalIntegrable (sa16y5f_f m ν Bf Nf u) volume 0 τ :=
    (hfc.mono (Icc_subset_Icc le_rfl hτ.2)).intervalIntegrable_of_Icc hτ.1
  refine sa16sx_eq_of_ell m _ _ (fun {ψ} hψ => ?_)
  have hW := sa16y5f_weak hν hT hγ hγ1 Bf hBb hBc Nf hNb hNc hsharp hiota φ hu hsol hψ τ hτ
  rw [map_add, sa16r_ell_iota, sa16r_ell_iota, sa16r_ell_iota, sa16r_ell_iota, hW]
  congr 1
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hii]
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  simp only [sa16y5f_f, map_add, map_sub, map_smul, smul_eq_mul]
  rw [sa16so_ell_Lap m hψ, sa16r_ell_iota]
  ring

theorem sa16y5f_hasDerivAt {m : ℕ} {ν T BB BN CN γ : ℝ} (hν : 0 < ν) (hT : 0 < T) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hBb : ∀ r ∈ Icc (0 : ℝ) T, ‖Bf r‖ ≤ BB)
    (hBc : ∀ x, ContinuousOn (fun r => Bf r x) (Icc 0 T))
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hNb : ∀ r ∈ Icc (0 : ℝ) T, ‖Nf r‖ ≤ BN)
    (hNc : ∀ x, ContinuousOn (fun r => Nf r x) (Icc 0 T))
    (hsharp : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T, ‖sa16y5_Qh d m p (ν * s) (Nf r)‖ ≤ CN * s ^ (-γ))
    (hiota : ∀ r ∈ Icc (0 : ℝ) T, ∀ a : ℝ, 0 < a → ∀ x : WmpSpace d (m + 1 + 1) p,
      sa16r_iota d (m + 1) p (sa16y5_Qh d m p a (Nf r) x) = sa16r_Gam d m p a (Nf r x))
    (φ : WmpSpace d (m + 1 + 1) p) {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (fun τ s => sa16y5f_kernel d m p ν Bf Nf s (τ - s)) u τ) {τ : ℝ} (hτ : τ ∈ Ioo 0 T) :
    HasDerivAt (fun r => sa16r_iota d m p (sa16r_iota d (m + 1) p (u r))) (sa16y5f_f m ν Bf Nf u τ) τ := by
  have hstrong := sa16y5f_strong hν hT hγ hγ1 Bf hBb hBc Nf hNb hNc hsharp hiota φ hu hsol
  have hfc := sa16y5f_f_cont (ν := ν) hBb hBc hNb hNc hu
  have hint : IntervalIntegrable (sa16y5f_f m ν Bf Nf u) volume 0 τ :=
    (hfc.mono (Icc_subset_Icc le_rfl hτ.2.le)).intervalIntegrable_of_Icc hτ.1.le
  have hcont : ContinuousAt (sa16y5f_f m ν Bf Nf u) τ := hfc.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
  have hmeas : StronglyMeasurableAtFilter (sa16y5f_f m ν Bf Nf u) (𝓝 τ) volume :=
    (hfc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo τ hτ
  have h1 := intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  have h2 := h1.const_add (sa16r_iota d m p (sa16r_iota d (m + 1) p φ))
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hτ.1 hτ.2] with r hr
  exact hstrong r hr

end Mi5

end HRS.Whole.AppendixA.Phase2SA16R
