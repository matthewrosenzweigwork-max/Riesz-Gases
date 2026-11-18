import HRS.MC.S7S7dAux24

/-!
# Packet `s7_S7d_uniform_limits` (relocation of `HRS.MC.Sec7.s7_S7d_uniform_limits`)

The two limits (R2), (R3) of Proposition 7.7, uniformly over `Φ` in the `C_b^5` unit ball and over `N ≥ N₀`
(the second, a statement about the `B`-term, only for `0 < γ`).

Plan (the files `S7S7dAux1 … S7S7dAux24`):
* Stein class `s7d_Cl f` (`C⁴`, `‖D^j f‖ ≤ 1` for `1 ≤ j ≤ 4`) contains `steinSolG G Φ` for all `Φ` in the ball (`s7d_stein_cl`);
  all estimates below are uniform over this class and over `‖u‖ ≤ 1`, so the uniformity in `Φ` is free.
* Finite-dimensional core (`s7d_core_R2`, `s7d_core_R3`): for the truncation `κ : Fin K.card → modes` the vector
  `(centeredStat, sed_Y …)` has a joint limit (B10b CLT, B13b for (R2), B9a/B9 window for (R3)); a Lipschitz transfer
  (`s7d_uniform_weak`, Lemma U from `WQ` via `s7d_uniform_ident`) makes the convergence uniform over bounded Lipschitz tests.
* Truncation errors: `W_N ↦ truncE K W_N` is uniform in `N` by coordinate `L¹` bounds (`s7d_W_tail`, `s7d_W_trunc_err`),
  `G ↦ truncE K G` by dominated convergence (`s7d_gauss_trunc_tendsto`); the finite-dimensional marginal of `G` is the Gaussian
  of covariance `sed_Cmat` (`s7d_law_G`, `s7d_gauss_to_G`) and `responseInverse φ_k = a_k` a.e. (`s7d_respInv_ae`).
* Single pair / single mode: `s7d_pair_R2` (observable `w = v_k·∇φ_l`) and `s7d_pair_R3` (statistic `B_k`).
* Sum over modes: S7b gives `b_k = ⟨k⟩^{-d-3}` weights for `w`, `B_k`, the tensor `Q_{k;lj}` (`s7d_Qt_bound`) and the drift
  integrals (`s7d_mode_bounds`), so the double (resp. single) series split into a finite block and a tail
  (`s7d_tsum2_tail`, `s7d_tsum1_tail`): `s7d_main_R2`, `s7d_main_R3`.
* Conclusion by `max` of the two thresholds.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ}

theorem s7_S7d_uniform_limits_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (r : ℝ)
    (hr : r = 2 * (d : ℝ) + 6) {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (NegSobolev d r) 5,
      |∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d,
          ∫ X, Real.sqrt N * (sed_A (v k) (s7_phi r l) X -
              ∫ Y, sed_A (v k) (s7_phi r l) Y ∂(sed_Q d s N γ ρ)) *
            iteratedFDeriv ℝ 2 (steinSolG G Φ) (zetaE r (sed_Q d s N γ ρ) X)
              ![s7_eps r k, s7_eps r l] ∂(sed_Q d s N γ ρ) -
        ∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d, ∑' j : NonzeroLattice d,
          (∫ x, a j x * sed_drift (v k) (s7_phi r l) x ∂(withDensityReal ρ)) *
            ∫ F, iteratedFDeriv ℝ 3 (steinSolG G Φ) F ![s7_eps r k, s7_eps r l, s7_eps r j] ∂G| ≤ ε ∧
      (0 < γ → |∑' k : NonzeroLattice d, ∫ X, sed_B d s ρ γ (v k) X *
            fderiv ℝ (steinSolG G Φ) (zetaE r (sed_Q d s N γ ρ) X) (s7_eps r k)
            ∂(sed_Q d s N γ ρ) -
        (1 / 2) * ∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d, ∑' j : NonzeroLattice d,
          sed_Qt d s ρ (v k) (a l) (a j) *
            ∫ F, iteratedFDeriv ℝ 3 (steinSolG G Φ) F ![s7_eps r l, s7_eps r j, s7_eps r k] ∂G| ≤ ε) := by
  intro ε hε
  obtain ⟨N₁, h1⟩ := s7d_main_R2 hd hs0 hs hr hγ hρ hmode G hG hε
  by_cases hγpos : 0 < γ
  · obtain ⟨N₂, h2⟩ := s7d_main_R3 hd hs0 hs hr hγpos hρ hmode G hG hε
    exact ⟨max N₁ N₂, fun N hN hN1 Φ hΦ =>
      ⟨h1 N (le_trans (le_max_left _ _) hN) hN1 Φ hΦ,
       fun _ => h2 N (le_trans (le_max_right _ _) hN) hN1 Φ hΦ⟩⟩
  · exact ⟨N₁, fun N hN hN1 Φ hΦ => ⟨h1 N hN hN1 Φ hΦ, fun h => absurd h hγpos⟩⟩

end HRS.MC.Sec7.S7d

end
