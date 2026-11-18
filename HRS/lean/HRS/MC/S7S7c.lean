import HRS.MC.S7S7cAux10

/-!
# Packet `s7_S7c_hilbert_stein` (relocation of `HRS.MC.Sec7.s7_S7c_hilbert_stein`)

The Hilbert-space Stein identity `F:eq:static-Stein` summed over `k` (TeX L8315-8323).  Proof: for the first
`n` modes (a finite set `K`, enumerated by `Fin K.card`), `sed_B5b_stein_centred` with `w = phi_k` and
`psi = d_k (F o iota)` (`MemCb 1`: `F` has bounded first and second derivatives) is summed over `k in K`
(`s7c_finite_identity`); `K -> infinity` along the Finset filter by dominated convergence (`Pi_K W_N -> W_N`
in `E_r`, `||Pi_K W|| <= ||W||`, `E ||W_N|| < infinity` from `sed_B7_lln`) and Tannery
(`|A_{N,kl}| <= C b_k b_l` deterministically, `E|B_{N,k}| <= C b_k` from the `L^2` energy bound and the Holder
transfer, `sum b_k < infinity`).  The `L^2` bound for `B` carries the Lipschitz constants of `v_k` explicitly
(`s7c_env`, `s7c_L2_bound`, `s7c_B_L1`).  `s7_C2b` is a local copy (defeq) of the spec definition.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

theorem s7_S7c_hilbert_stein_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (r : ℝ)
    (hr : r = 2 * (d : ℝ) + 6) {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀) {N : ℕ} (hN : 1 ≤ N) {F : NegSobolev d r → ℝ}
    (hF : s7_C2b F) :
    ∫ X, fderiv ℝ F (zetaE r (sed_Q d s N γ ρ) X) (zetaE r (sed_Q d s N γ ρ) X) ∂(sed_Q d s N γ ρ) =
      ∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d,
          ∫ X, sed_A (v k) (s7_phi r l) X *
            iteratedFDeriv ℝ 2 F (zetaE r (sed_Q d s N γ ρ) X) ![s7_eps r k, s7_eps r l]
            ∂(sed_Q d s N γ ρ) -
        γ / Real.sqrt N * ∑' k : NonzeroLattice d,
          ∫ X, sed_B d s ρ γ (v k) X * fderiv ℝ F (zetaE r (sed_Q d s N γ ρ) X) (s7_eps r k)
            ∂(sed_Q d s N γ ρ) :=
  s7c_main hd hs0 hs hr hγ hρ hmode hN hF

end HRS.MC.Sec7.S7c

end
