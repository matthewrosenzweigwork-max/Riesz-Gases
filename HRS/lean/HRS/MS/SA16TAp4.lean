import HRS.MS.SA16TAp3b

/-!
# S.A.16 (SA16T) Ap4: the approximating problems of the limit assembly (P8, sub case)

`sa16t_approx`: for `AdjointRdData` in the sub case, `t ∈ (0,T]`, `n ∈ ℕ` and `φ_n ∈ W^{m+2,p}`, the mild solution `u_n` of
`∂_τ u = ν_n Δu + (b_n^τ·∇ - G_n^τ) u`, `u(0) = φ_n` (`ν_n = ν + 1/(n+1)`, `b_n` the smoothed cut-off drift, `G_n` the nonlocal
operator of the mollified density) gives `w = ι²u : [0,t] → W^{m,p}` continuous, with the uniform bound
`‖w τ‖ ≤ Kb e^{cexp τ} ‖ι²φ_n‖` (constants independent of `n, D, μ, t`) and the weak identity tested against `C_c^∞`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section Ap4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 4000000 in
theorem sa16t_approx (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (hsub : s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1)) (MB Λ ΛV G₀ νbar T : ℝ) :
    ∃ Kb cexp : ℝ, 0 < Kb ∧ ∀ (D : WholeDyn d) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ n : ℕ, ∀ φn : WmpSpace d (m + 1 + 1) p,
      ∃ w : ℝ → WmpSpace d m p, ContinuousOn w (Icc 0 t) ∧
        (∀ τ ∈ Icc (0 : ℝ) t, ‖w τ‖ ≤ Kb * Real.exp (cexp * τ) * ‖sa16sz_iota2 d m p φn‖) ∧
        ∀ {ψ : Euc d → ℝ} (_ : IsCcInfty ψ),
          ContinuousOn (sa16t_Fterm d m p (sa16t_nu D n) (sa16t_bcs d n D μ t) (D.coeff (sa16t_mu d n μ)) t w ψ)
            (Icc 0 t) ∧
          ∀ τ ∈ Icc (0 : ℝ) t, ∫ x, wrep d m p (w τ) x * ψ x =
            (∫ x, wrep d m p (sa16sz_iota2 d m p φn) x * ψ x) +
              ∫ σ in (0 : ℝ)..τ, sa16t_Fterm d m p (sa16t_nu D n) (sa16t_bcs d n D μ t)
                (D.coeff (sa16t_mu d n μ)) t w ψ σ := by
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) ≤ d := by linarith [hsub.1]
    exact_mod_cast this
  obtain ⟨CP, hCP, hP6⟩ := sa16so_P6 (p := p) hd s hs0 hsd m hm MB (sa16t_Lam1 d m Λ) ΛV G₀ νbar T hsub
  obtain ⟨Bχ, hBχ, hcoef⟩ := sa16t_coefs hd m
  obtain ⟨CJ, hCJ0, hen⟩ := sa16t_energy_solution (d := d) (p := p) m
  obtain ⟨hN, ⟨Cj, hCj0, hCj⟩, hpow, -⟩ := closed_jet_energy_calculus d m p
  have hp0 : 0 < p := by linarith [(Fact.out : 2 ≤ p)]
  set Bm : ℝ := max (sa16t_Bu Bχ d (m + 1) (sa16t_C0 d m s MB Λ G₀) (sa16t_L d m s MB Λ ΛV)) 0 with hBm
  have hBm0 : 0 ≤ Bm := le_max_right _ _
  set c : ℝ := p * sa16sz_cTr d m p Bm + p * CJ * CP with hc
  refine ⟨Cj, c / p, hCj0, fun D μ hD t ht n φn => ?_⟩
  obtain ⟨hDs, -, -⟩ := hD.hs
  subst hDs
  have hT0t : 0 < t := ht.1
  have htT : t ≤ T := ht.2
  have hDn := sa16t_adjData hd hsub.1 hD n
  set μn : ℝ → Euc d → ℝ := sa16t_mu d n μ with hμn
  have hν : 0 < sa16t_nu D n := sa16t_nu_pos hD.hν.1 n
  obtain ⟨hbc, hbb, habs⟩ := hcoef hD ht n
  set Bn : ℝ := max (sa16t_C0 d m D.s MB Λ G₀ + sa16t_L d m D.s MB Λ ΛV * (2 * sa16t_R n + 1))
    (sa16t_Bu Bχ d (m + 1) (sa16t_C0 d m D.s MB Λ G₀) (sa16t_L d m D.s MB Λ ΛV)) with hBn
  have hrT : ∀ σ ∈ Icc (0 : ℝ) t, t - σ ∈ Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  -- operators
  have hreg1 : ∀ r ∈ Icc (0 : ℝ) T, IsRegularDensityW (m + 1 + 3) (sa16t_LamN d n (m + 1 + 3) (sa16t_A0 d m Λ)) (μn r) :=
    fun r hr => sa16t_reg_hi hd hD.hμ n (m + 1 + 3) hr
  obtain ⟨C1, hC1, hG1⟩ := sa16t_G_subop (p := p) (m + 1) hd D.s MB
    (sa16t_LamN d n (m + 1 + 3) (sa16t_A0 d m Λ)) hs0 hsub.1 hsub.2
  obtain ⟨C0', hC0', hG0⟩ := sa16t_G_subop (p := p) m hd D.s MB (sa16t_Lam1 d m Λ) hs0 hsub.1 hsub.2
  set T1 : ℝ → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p :=
    fun σ => sa16so_G d (m + 1) p D.s D.M (μn (t - σ)) with hT1
  set T0 : ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p :=
    fun σ => sa16so_G d m p D.s D.M (μn (t - σ)) with hT0def
  have hS1 : ∀ σ ∈ Icc (0 : ℝ) t, SA16SubOp d (m + 1) p D.s D.M (sa16t_mu d n (fun σ => μ (t - σ)) σ) (T1 σ) :=
    fun σ hσ => (hG1 D.M hD.hM _ (hreg1 _ (hrT σ hσ))).1
  have hT1n : ∀ σ ∈ Icc (0 : ℝ) t, ‖T1 σ‖ ≤ C1 := fun σ hσ => (hG1 D.M hD.hM _ (hreg1 _ (hrT σ hσ))).2
  have hS0 : ∀ σ ∈ Icc (0 : ℝ) t, SA16SubOp d m p D.s D.M (μn (t - σ)) (T0 σ) := fun σ hσ =>
    (hG0 D.M hD.hM _ (sa16so_regDensity_of_MF hDn.hμ.regular (hrT σ hσ))).1
  have hT0n : ∀ σ ∈ Icc (0 : ℝ) t, ‖T0 σ‖ ≤ CP := fun σ hσ => (hP6 D μn hDn _ (hrT σ hσ)).1
  have hcomp : ∀ σ ∈ Icc (0 : ℝ) t, (sa16r_iota d m p).comp (T1 σ) = (T0 σ).comp (sa16r_iota d m p) :=
    fun σ hσ => sa16sz_nl_compat m (hS1 σ hσ) (hS0 σ hσ)
  -- the operator K
  set bcs : ℝ → Fin d → Euc d → ℝ := sa16t_bcs d n D μ t with hbcs
  set K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p :=
    fun σ => sa16so_B d (m + 1) p (bcs σ) - (T1 σ).comp (sa16r_iota d (m + 1) p) with hKdef
  have hBn0 : 0 ≤ Bn := le_max_of_le_right (by
    have := (hbb 0 ⟨le_rfl, hT0t.le⟩ ⟨0, by omega⟩ 1 le_rfl (by omega) 0)
    have h2 := (norm_nonneg _).trans this
    exact h2)
  set Bk : ℝ := sa16so_cB d (m + 1) Bn + C1 * ‖sa16r_iota d (m + 1) p‖ with hBk
  have hBk0 : 0 ≤ Bk := by
    have := sa16so_cB_nonneg d (m + 1) hBn0
    have hc1 : 0 ≤ C1 := le_trans (norm_nonneg (T1 0)) (hT1n 0 ⟨le_rfl, hT0t.le⟩)
    rw [hBk]; positivity
  have hKb : ∀ σ ∈ Icc (0 : ℝ) t, ‖K σ‖ ≤ Bk := by
    intro σ hσ
    have h1 := norm_sub_le (sa16so_B d (m + 1) p (bcs σ)) ((T1 σ).comp (sa16r_iota d (m + 1) p))
    have h2 := sa16so_B_norm (p := p) (hbc σ hσ)
    have h3 : ‖(T1 σ).comp (sa16r_iota d (m + 1) p)‖ ≤ C1 * ‖sa16r_iota d (m + 1) p‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hT1n σ hσ) (norm_nonneg _))
    have h4 : K σ = sa16so_B d (m + 1) p (bcs σ) - (T1 σ).comp (sa16r_iota d (m + 1) p) := rfl
    rw [h4, hBk]
    linarith
  have hbbm : ∀ r ∈ Icc (0 : ℝ) t, ∀ l : Fin d, ∀ i, 1 ≤ i → i ≤ m + 1 → ∀ x,
      ‖iteratedFDeriv ℝ i (bcs r l) x‖ ≤ Bm := fun r hr l i h1 h2 x => (hbb r hr l i h1 h2 x).trans (le_max_left _ _)
  have hTnn : 0 ≤ T := hT0t.le.trans htT
  have hdr := sa16t_b_cont hd hD ht
  have hbcs_cont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Icc (0 : ℝ) t, ∀ σ' ∈ Icc (0 : ℝ) t, |σ - σ'| < δ →
      SA16BddCoef (m + 1) ε (fun i x => bcs σ i x - bcs σ' i x) := fun ε hε =>
    sa16t_bcv_cont (m + 1) n isCompact_Icc hdr hε
  have hμc' := sa16t_mu_cont_rev hd hD.hμ ht
  have hKc : ∀ x, ContinuousOn (fun σ => K σ x) (Icc 0 t) := by
    intro x
    have h1 := sa16t_B_cont (p := p) (k := m + 1) hbc hbcs_cont x
    have h2 := sa16t_G_strong (p := p) (m + 1) n hd D.s MB hs0 hsub.1 hsub.2 D.M hD.hM isCompact_Icc hμc'
      (Aμ := Λ) (fun σ hσ y => sa16t_mu_bdd hD.hμ (hrT σ hσ) y) hS1 hT1n (sa16r_iota d (m + 1) p x)
    refine (h1.sub h2).congr (fun σ hσ => ?_)
    simp only [hKdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, Pi.sub_apply]
  obtain ⟨u, hu, hsol, -⟩ := sa16r_fixedn_mild hν hT0t hBk0 (m + 1) K hKb hKc φn
  have hE := hen hν hT0t bcs hbc hBm0 hbbm T1 T0 hcomp hT0n K (fun r => rfl) hKb hBk0 hKc φn hu hsol
  have hEnn : ∀ G : WmpSpace d m p, 0 ≤ jetEnergy d m p G := fun G => by
    rw [← hpow G]; exact Real.rpow_nonneg (hN.nonneg G) _
  refine ⟨fun τ => sa16sz_iota2 d m p (u τ), (sa16sz_iota2 d m p).continuous.comp_continuousOn hu,
    fun τ hτ => ?_, fun {ψ} hψ => ?_⟩
  · exact sa16t_bound_from_energy (p := p) hp0 (hEnn _) (hEnn _) (hE τ hτ) (hCj _).1 (hCj _).2 hCj0.le
  · have hsx := sa16sx_strong hν hT0t K hKb hBk0 hKc φn hu hsol
    have hfc := sa16sx_f_cont (ν := sa16t_nu D n) hKb hKc hu
    have hpt : ∀ σ ∈ Icc (0 : ℝ) t, sa16r_ell d m p hψ (sa16sx_f m (sa16t_nu D n) K u σ) =
        sa16t_Fterm d m p (sa16t_nu D n) bcs (D.coeff μn) t (fun τ => sa16sz_iota2 d m p (u τ)) ψ σ := by
      intro σ hσ
      exact sa16t_ell_f (hbc σ hσ) (hcomp σ hσ) (K := K σ) rfl hψ
        (N := nonlocalTestRd (D.coeff μn) (t - σ) ψ)
        (fun Y => (hP6 D μn hDn (t - σ) (hrT σ hσ)).2 hψ Y) (u σ)
    refine ⟨((sa16r_ell d m p hψ).continuous.comp_continuousOn hfc).congr (fun σ hσ => (hpt σ hσ).symm),
      fun τ hτ => ?_⟩
    have hii : IntervalIntegrable (sa16sx_f m (sa16t_nu D n) K u) volume 0 τ :=
      (hfc.mono (Icc_subset_Icc le_rfl hτ.2)).intervalIntegrable_of_Icc hτ.1
    have h2 := congrArg (sa16r_ell d m p hψ) (hsx τ hτ)
    rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hii] at h2
    have e : ∫ σ in (0 : ℝ)..τ, sa16t_Fterm d m p (sa16t_nu D n) bcs (D.coeff μn) t
        (fun τ => sa16sz_iota2 d m p (u τ)) ψ σ = ∫ σ in (0 : ℝ)..τ, sa16r_ell d m p hψ (sa16sx_f m (sa16t_nu D n) K u σ) := by
      refine intervalIntegral.integral_congr (fun σ hσ => ?_)
      rw [Set.uIcc_of_le hτ.1] at hσ
      exact (hpt σ ⟨hσ.1, hσ.2.trans hτ.2⟩).symm
    rw [← sa16r_ell_apply hψ, ← sa16r_ell_apply hψ, e]
    exact h2

end Ap4

end HRS.Whole.AppendixA.Phase2SA16R
