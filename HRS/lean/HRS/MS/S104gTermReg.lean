import HRS.MS.S104gCore
import HRS.MS.S104bOrb1
import HRS.MS.S103dLip2

/-!
# S10.4 packet S104G, part 8: `S104bTermRegGen` for a small `ε_*` from the adjoint existence

Prefix `s104g_`, namespace `HRS.MS.R2WinOrbNL`.

`s104g_termRegGen_small`: for `c₁, C₁` there is `ε₁ > 0` such that for all `0 < ε_* ≤ ε₁`, `S104bTermRegGen d s a β ρβ ε_* c₁ C₁` follows from `S103cRhoPrimeUC` at `ε_*`
and the explicit adjoint-existence hypothesis `hex` (classical adjoint solutions with terminal datum `φ_α` for every trajectory of the class and all terminal times `t ≥ 0`,
exactly the hypothesis of `s103d_core`/`S103nTermReg`; the existence for the data `L_tφ_α`, `L_t²φ_α + ∂_tL_tφ_α` is constructed, not assumed).
`s104g_termRegGen_of_ex`: the same with `S103cRhoPrimeUC` discharged by `s103d_rhoPrimeUCsmall`; only `hex` remains.
The proof is the proof of `s103d_termReg_small` with `s103d_core` replaced by the general-initial-time `s104g_core`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrb
  HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.MovAdj HRS.MS.R2WinErr

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem s104g_termRegGen_small {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (c₁ C₁ : ℝ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ εstar : ℝ, 0 < εstar → εstar ≤ ε₁ →
      S103cRhoPrimeUC d s a β ρβ εstar c₁ C₁ (8 * d + 80 + 1) (s103dL d s) →
      (∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ), IsAdmissiblePerturbation ρβ εstar ε ψ →
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
          ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) f) →
      S104bTermRegGen d s a β ρβ εstar c₁ C₁ := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  by_cases hc₁ : 0 < c₁
  swap
  · exact ⟨1, one_pos, fun εstar _ _ _ _ ε ψ ρ _ hres => absurd hres.cpos hc₁⟩
  set Lnat : ℕ := s103dL d s with hLnatdef
  have hLnat := s103dL_spec d H.hs0
  obtain ⟨Rw, hRw, hZ⟩ := s103n_zeroth H
  obtain ⟨Rstar, Cg', cg', hRstar, hCg'1, hcg', hRad⟩ := s103c_radius H (8 * d + 83) (by omega)
  have hK : ((9 * d + 92 : ℕ) : ℝ) + d / 2 + 4 < ((102 * d + 1020 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨εs, r, hεs, hr, hr1, hrRs, hCε, ⟨Cg, cg, hCg, hcg, hGrad⟩, hSch⟩ :=
    s103n_setup2 H (min Rw Rstar) (lt_min hRw hRstar) (9 * d + 92) hK c₁ C₁ hc₁
  have hrRw : r ≤ Rw := hrRs.trans (min_le_left _ _)
  have hrRstar : r ≤ Rstar := hrRs.trans (min_le_right _ _)
  obtain ⟨Cz, hCz0, hZr⟩ := hZ r c₁ Cg cg hr.le hrRw hr1 hc₁.le hcg (by linarith)
  obtain ⟨C5, hC50, hC5⟩ := s103n_orbitSup_of_bd H (by linarith : 0 ≤ Cg) hcg hCz0
  obtain ⟨CKL, hCKL⟩ := hSch Lnat
  obtain ⟨Aβ, hAβ0, hAβ⟩ := s103n_rho_u2dec H (9 * d + 92) Lnat
  set Ad : ℝ := 2 ^ Lnat * |CKL| with hAd
  set Aρ : ℝ := Aβ + Ad with hAρ
  have hAd0 : 0 ≤ Ad := by positivity
  have hAρ0 : 0 ≤ Aρ := by positivity
  refine ⟨εs, hεs, fun εstar hεpos hεle hUC hexAll ε ψ ρ hψ hres α T0 hT0 => ?_⟩
  have hex := hexAll ε ψ ρ hψ hres α
  have hψ' := s103c_adm_mono hψ hεle
  have hres' := s103c_res_mono hres hεpos hεle
  have hsm := s103n_small_class hres' hCε
  have hG : S103nGrad d s a β ρβ ρ Cg cg := hGrad _ ρ hsm
  have hZ' : S103nZero d s a β ρβ ρ Cz := fun T φ f Bφ hT hf hφ1 hosc hfin hφB r' hr' x =>
    hZr _ ρ hsm hG T φ f Bφ hT hf hφ1 hosc hfin hφB r' hr' x
  have hGc : S103cGrad d s a β ρβ ρ (8 * d + 83) (8 * d + 83 + d + 6) Cg' cg' :=
    hRad r c₁ hr.le hrRstar hc₁.le _ ρ hsm
  obtain ⟨ρ', hder, hcls⟩ := hCKL ε ψ ρ hψ' hres'
  have hclass : ∀ τ : ℝ, 0 ≤ τ → U2Dec (9 * d + 92) (Lnat : ℝ) Aρ (ρ τ) ∧
      U2Dec (9 * d + 92) (Lnat : ℝ) Ad (ρ' τ) := by
    intro τ hτ
    obtain ⟨h1, h2, h3⟩ := hcls τ hτ
    exact hAβ |CKL| ρ ρ' τ hτ h1 h2 (fun k hk x => (h3 k hk x).trans (le_abs_self _))
  have hmcls : (d : ℝ) / 2 + 2 < ((102 * d + 1020 : ℕ) : ℝ) := by push_cast; linarith
  have hcont : ∀ y, ContinuousOn (fun τ => ρ τ y) (Set.Ici 0) := fun y => s103n_cont_time H hmcls hsm y
  have hUC' := hUC ε ψ ρ ρ' hψ hres hder ⟨Ad, fun t ht =>
    ult_U2Dec_mono (hclass t ht).2 (by omega : 8 * d + 80 + 1 ≤ 9 * d + 92)⟩
  obtain ⟨Kφ, hKφ0, hKφ⟩ := s103c_phi_syn3 (d := d) (9 * d + 93) (by omega)
  exact s104g_core H Lnat hLnat ρ ρ' Aρ Ad hAρ0 hAd0 (fun τ hτ => (hclass τ hτ).1)
    (fun τ hτ => (hclass τ hτ).2) hder hcont hUC' (by linarith : 0 ≤ Cg') hcg' hGc hC50
    (fun g A' hg t ht => hC5 ρ hG hZ' g A' hg t ht) (hKφ α) hex T0 hT0

/-- `S104bTermRegGen` for a small `ε_*` from the adjoint-existence hypothesis alone (the identification and time continuity of `ρ'` are proved). -/
theorem s104g_termRegGen_of_ex (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) (c₁ C₁ : ℝ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ εstar : ℝ, 0 < εstar → εstar ≤ ε₁ →
      (∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ), IsAdmissiblePerturbation ρβ εstar ε ψ →
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
          ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) f) →
      S104bTermRegGen d s a β ρβ εstar c₁ C₁ := by
  have H : Mov2dTh d s β a ρβ := ⟨hd, hs0, hs, hβ, ha, hρβ⟩
  obtain ⟨ε₁, hε₁, hTR⟩ := s104g_termRegGen_small H c₁ C₁
  obtain ⟨ε₀, hε₀, hUC⟩ := s103d_rhoPrimeUCsmall hd hs0 hs ha hβ ρβ hρβ c₁ C₁
  refine ⟨min ε₁ ε₀, lt_min hε₁ hε₀, fun εstar hpos hle hex => ?_⟩
  exact hTR εstar hpos (hle.trans (min_le_left _ _)) (hUC εstar hpos (hle.trans (min_le_right _ _))) hex

end HRS.MS.R2WinOrbNL

end
