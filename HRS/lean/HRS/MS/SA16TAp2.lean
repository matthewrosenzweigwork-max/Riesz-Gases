import HRS.MS.SA16TAp1
import HRS.MS.SA16SEn13

/-!
# S.A.16 (SA16T) Ap2: weak form of the strong equation, strong continuity of the transport part

`sa16t_Fterm`: the integrand `ν ∫ w Δψ - ∫ w div(bψ) - ∫ w N_ψ` of the weak identity.
`sa16t_ell_f`: `ℓ_ψ (sa16sx_f m ν K u σ) = sa16t_Fterm ...` for `K σ = B_{bc σ} - T1 σ ι` and `ι T1 = T0 ι` with the weak
identity of `T0`.  `sa16t_B_cont`: strong continuity of `σ ↦ B_{bc σ}` from the `SA16BddCoef`-continuity of `bc`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P Phase2SA16Evolution Phase2SA16Transfer

section Ap2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the integrand of the weak identity -/
def sa16t_Fterm (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (ν : ℝ) (bcs : ℝ → Fin d → Euc d → ℝ) (C : WholeCoeff d) (t : ℝ)
    (w : ℝ → WmpSpace d m p) (ψ : Euc d → ℝ) (σ : ℝ) : ℝ :=
  ν * (∫ x, wrep d m p (w σ) x * Laplacian.laplacian ψ x) -
    (∫ x, wrep d m p (w σ) x * sa16so_divFun (bcs σ) ψ x) -
    ∫ x, wrep d m p (w σ) x * nonlocalTestRd C (t - σ) ψ x

set_option maxHeartbeats 1600000 in
lemma sa16t_ell_f {m : ℕ} {ν Bn : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef (m + 1) Bn bc)
    {T1 : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p} {T0 : WmpSpace d m p →L[ℝ] WmpSpace d m p}
    (hcomp : (sa16r_iota d m p).comp T1 = T0.comp (sa16r_iota d m p))
    {K : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p}
    (hK : K = sa16so_B d (m + 1) p bc - T1.comp (sa16r_iota d (m + 1) p))
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) {N : Euc d → ℝ}
    (hT0 : ∀ Y : WmpSpace d m p, sa16r_ell d m p hψ (T0 Y) = ∫ x, wrep d m p Y x * N x)
    (G : WmpSpace d (m + 1 + 1) p) :
    sa16r_ell d m p hψ (ν • sa16so_Lap d m p G + sa16r_iota d m p (K G)) =
      ν * (∫ x, wrep d m p (sa16sz_iota2 d m p G) x * Laplacian.laplacian ψ x) -
        (∫ x, wrep d m p (sa16sz_iota2 d m p G) x * sa16so_divFun bc ψ x) -
        ∫ x, wrep d m p (sa16sz_iota2 d m p G) x * N x := by
  have hdiv := sa16so_cc_div hb hψ
  have hlap := sa16sw_cc_lap hψ
  rw [map_add, map_smul, smul_eq_mul, sa16so_ell_Lap m hψ, sa16r_ell_iota, hK, ContinuousLinearMap.sub_apply,
    map_sub, sa16so_ell_B hb hψ, ContinuousLinearMap.comp_apply]
  have e1 : sa16r_ell d (m + 1 + 1) p hlap G = ∫ x, wrep d m p (sa16sz_iota2 d m p G) x * Laplacian.laplacian ψ x := by
    have h : sa16r_ell d (m + 1 + 1) p hlap G = sa16r_ell d m p hlap (sa16sz_iota2 d m p G) := by
      unfold sa16sz_iota2
      rw [ContinuousLinearMap.comp_apply, sa16r_ell_iota, sa16r_ell_iota]
    rw [h, sa16r_ell_apply, sa16sw_lap_eq hψ.1]
  have e2 : sa16r_ell d (m + 1 + 1) p hdiv G = ∫ x, wrep d m p (sa16sz_iota2 d m p G) x * sa16so_divFun bc ψ x := by
    have : sa16r_ell d (m + 1 + 1) p hdiv G = sa16r_ell d m p hdiv (sa16sz_iota2 d m p G) := by
      unfold sa16sz_iota2
      rw [ContinuousLinearMap.comp_apply, sa16r_ell_iota, sa16r_ell_iota]
    rw [this, sa16r_ell_apply]
  have e3 : sa16r_ell d (m + 1) p hψ (T1 (sa16r_iota d (m + 1) p G)) =
      ∫ x, wrep d m p (sa16sz_iota2 d m p G) x * N x := by
    rw [← sa16r_ell_iota, ← ContinuousLinearMap.comp_apply (sa16r_iota d m p) T1, hcomp,
      ContinuousLinearMap.comp_apply, hT0]
    rfl
  rw [e1, e2, e3]
  ring

lemma sa16so_cB_lin (d k : ℕ) (B : ℝ) : sa16so_cB d k B = B * sa16so_cB d k 1 := by
  unfold sa16so_cB; ring

theorem sa16t_B_cont {k : ℕ} {Bn : ℝ} {S : Set ℝ} {bcs : ℝ → Fin d → Euc d → ℝ}
    (hbc : ∀ σ ∈ S, SA16BddCoef k Bn (bcs σ))
    (hdiff : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ S, ∀ σ' ∈ S, |σ - σ'| < δ →
      SA16BddCoef k ε (fun i x => bcs σ i x - bcs σ' i x)) (x : WmpSpace d (k + 1) p) :
    ContinuousOn (fun σ => sa16so_B d k p (bcs σ) x) S := by
  intro σ₀ hσ₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hc0 : 0 ≤ sa16so_cB d k 1 := sa16so_cB_nonneg d k zero_le_one
  set c : ℝ := sa16so_cB d k 1 with hc
  obtain ⟨δ, hδ, hδ'⟩ := hdiff (ε / ((c + 1) * (‖x‖ + 1) * 2)) (by positivity)
  refine ⟨δ, hδ, fun σ hσ hlt => ?_⟩
  have hd := hδ' σ hσ σ₀ hσ₀ (by simpa [Real.dist_eq] using hlt)
  have hsub := sa16so_B_sub (p := p) (hbc σ hσ) (hbc σ₀ hσ₀)
  have hn := sa16so_B_norm (p := p) hd
  have hx := congrArg (fun L : WmpSpace d (k + 1) p →L[ℝ] WmpSpace d k p => L x) hsub
  simp only [ContinuousLinearMap.sub_apply] at hx
  rw [dist_eq_norm, ← hx]
  refine lt_of_le_of_lt ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) ?_
  rw [sa16so_cB_lin, ← hc]
  have hx0 := norm_nonneg x
  rw [show ε / ((c + 1) * (‖x‖ + 1) * 2) * c * ‖x‖ = ε / 2 * ((c / (c + 1)) * (‖x‖ / (‖x‖ + 1))) by
    field_simp]
  have h1 : c / (c + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h2 : ‖x‖ / (‖x‖ + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h3 : (c / (c + 1)) * (‖x‖ / (‖x‖ + 1)) ≤ 1 :=
    mul_le_one₀ h1 (by positivity) h2
  nlinarith

end Ap2

end HRS.Whole.AppendixA.Phase2SA16R
