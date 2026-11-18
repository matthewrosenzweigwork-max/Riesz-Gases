import HRS.MS.SA16Y5Mi3

/-!
# S.A.16 (SA16Y5) Mi4: weak and strong form of the fractional-order mild solution (B8, part 4)

`sa16y5f_weak`: for `ψ ∈ C_c^∞`, `ℓ_ψ(u τ) = ℓ_ψ φ + ∫_0^τ (ν ℓ_{Δψ}(u r) + ℓ_ψ(B_r u r) - ℓ_ψ(N_r u r)) dr` (`ℓ` at the levels `m+2, m+2, m+1, m`).
`sa16y5f_strong`: `ι² (u τ) = ι² φ + ∫_0^τ f`, `f r = ν Δ u r + ι (B_r u r) - N_r u r ∈ W^{m,p}`; `sa16y5f_hasDerivAt`: `ι² u` has derivative `f τ` on `(0,T)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Mi4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the integrand of the strong form -/
def sa16y5f_f (m : ℕ) (ν : ℝ) (Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p) (u : ℝ → WmpSpace d (m + 1 + 1) p) (r : ℝ) :
    WmpSpace d m p :=
  ν • sa16so_Lap d m p (u r) + sa16r_iota d m p (Bf r (u r)) - Nf r (u r)

set_option maxHeartbeats 3200000 in
theorem sa16y5f_weak {m : ℕ} {ν T BB BN CN γ : ℝ} (hν : 0 < ν) (hT : 0 < T) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1)
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
      voltOp (fun τ s => sa16y5f_kernel d m p ν Bf Nf s (τ - s)) u τ)
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    ∀ τ ∈ Icc (0 : ℝ) T, sa16r_ell d (m + 1 + 1) p hψ (u τ) =
      sa16r_ell d (m + 1 + 1) p hψ φ + ∫ r in (0 : ℝ)..τ,
        (ν * sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u r) +
          (sa16r_ell d (m + 1) p hψ (Bf r (u r)) - sa16r_ell d m p hψ (Nf r (u r)))) := by
  obtain ⟨C, hC0, hb, hc⟩ := sa16y5f_voltKer hν hT hγ hγ1 Bf hBb hBc Nf hNc hsharp
  have hBN0 : 0 ≤ BN := (ContinuousLinearMap.opNorm_nonneg _).trans (hNb 0 ⟨le_rfl, hT.le⟩)
  have hBB0 : 0 ≤ BB := (ContinuousLinearMap.opNorm_nonneg _).trans (hBb 0 ⟨le_rfl, hT.le⟩)
  set hχ := sa16sw_cc_lap hψ with hχdef
  have hHW := sa16sw_heatWeak (p := p) hν T (m + 1) hψ
  have hw := sa16y5g_volt_weak (γ := γ) (T := T) (C := C) (by linarith) hγ1 hT hC0
    (fun s r => sa16y5f_kernel d m p ν Bf Nf s r) hb hc
    (f0 := sa16r_f0 d (m + 1) p ν φ) (u := u) (sa16r_f0_cont hν (m + 1) φ) hu hsol
    (sa16r_ell d (m + 1 + 1) p hψ) (ν • sa16r_ell d (m + 1 + 1) p hχ)
    (fun r => (sa16r_ell d (m + 1) p hψ).comp (Bf r) - (sa16r_ell d m p hψ).comp (Nf r))
    (sa16r_ell d (m + 1 + 1) p hψ φ)
    (BY := ‖sa16r_ell d (m + 1) p hψ‖ * BB + ‖sa16r_ell d m p hψ‖ * BN)
    (fun r hr => by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (hBb r hr) (ContinuousLinearMap.opNorm_nonneg _))
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (hNb r hr) (ContinuousLinearMap.opNorm_nonneg _)))
    (fun x => ((sa16r_ell d (m + 1) p hψ).continuous.comp_continuousOn (hBc x)).sub
      ((sa16r_ell d m p hψ).continuous.comp_continuousOn (hNc x)))
    (fun x r hr s hs => by
      have := sa16y5f_HE hν hT hγ hγ1 Bf hBb hBc Nf hNc hsharp hiota hψ x hr hs
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      exact this)
    (fun τ hτ => by
      have := hHW.2 φ τ hτ
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      exact this)
  intro τ hτ
  have := hw τ hτ
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply] at this
  exact this

end Mi4

end HRS.Whole.AppendixA.Phase2SA16R
