import HRS.MS.WsStatAux15
import HRS.MS.FldRemTie

/-!
# S21 packet F3c: the centred mild identity (coordinates of the centred remainder)

Setting: the stationary setup `S` of packet D (`S.rho N t = rho`, `S.invbeta N = beta^{-1}`), a filtered strong solution `X` with
`law (X t) = nu` (`nu = P_{N,beta}`) for `t <= T`, the particle martingale `M` of `s56_particle_martingale`.

`s21Rt` is the centred remainder
`R~_t = sigma (mu_N^t - m_N) - A(k_0 - kappa)(t) - T M (t)`, `m_N = meanEmpirical nu`, `kappa = s56k0 .. m_N ..`
(the deterministic centring of the initial `K`-state: no Bochner expectation).

`s21_centered_coord`: for every `t in [0,T]` and `alpha`, a.s.
`coord R~_t alpha = -(sigma/2) int_0^t (c_alpha(r,.) - E c_alpha(r,.)) dr`, `c_alpha = commForcing`, i.e. exactly the object that
`field_remainder_centered` (S5.3) bounds in `L^2(C_t l^2)` (scaled by `sigma/sqrt N`).

Proof: the mild identity `s56_mild_coord`, the coordinate formulas of the centred field and of `A(k_0 - kappa)`
(`s56_k0_eval`, `s21_k0_eval_gen`), and the expectation of the mild identity (`s21_E_pair_emp`, `s21_E_recon`, Fubini
`s21_fubini_comm`) which identifies the deterministic constant `sigma (m_N - rho)(phi_alpha - U^{0,t} phi_alpha)` with
`sigma int_0^t E F_alpha dr`, `F_alpha = -(1/2) c_alpha` (`s56_fluc_eq_comm` for `M = -1`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.MS.S53 HRS.MS.S52B HRS.MS.Ul
open HRS (Euc)

variable {d : ℕ}

/-- The orbit input of S5.3 for the stationary quadratic coefficient. -/
theorem s21_orbit_data (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {T : ℝ} (hT : 0 ≤ T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ (b : MultiIndex d → ℝ) (K : ℝ) (G0 G1 G2 : MultiIndex d → ℝ → Euc d → ℝ),
      S53Orbit ((⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T K b G0 G1 G2 := by
  have hρS : IsSchwartzDensity ρ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]; exact s21_schwartz_thermal hd hs0 hsd ha hβ
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  have hO : UlOrb d s β⁻¹ ρ (fun _ => (0 : Euc d)) (fun x => (fun _ : Euc d => (0 : Euc d)) x -
      convGradConvW (rieszKernelGrad d s) ρ x) θ :=
    ⟨hd, hs0, hsd, hν, hρS.2.elim fun ψ hψ => ⟨ψ, hψ⟩, fun i => ⟨0, by ext x; simp⟩, rfl, hθ⟩
  have huniq := s53_uniq hd hs0 hsd hν (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hρS T
  rw [s53_coeff_eq] at huniq
  have hk : (d : ℝ) / 2 + 6 < ((d + 9 : ℕ) : ℝ) := by
    push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hm : ((2 * (d + 9) + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨b, K, G0, G1, G2, Orb⟩ := s53_orbit_of_uniq hO (Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ)))
    ((wholeSpaceIndex d : ℕ) : ℝ) hT huniq (s53_index_bound s hs0 hsd (d + 9) hk _ hm)
  rw [← s53_coeff_eq] at Orb
  exact ⟨b, K, G0, G1, G2, Orb⟩

end HRS.MS.S21
