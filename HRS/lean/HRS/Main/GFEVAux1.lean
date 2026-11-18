import HRS.Main.GFSpec1
import HRS.Uniform.Q54Aux23

/-!
# Packet GFEV, part 1: chain plan for `gf_ev_mat` and `gf_ev_grad` (GFSpec1)

Relocation pattern: `GFSpec*.lean` are not edited; the proofs live in `HRS/Main/GFEVAux*.lean` (namespace `HRS.GF`, helpers
`gfev_*`) as `gf_ev_mat_proof`, `gf_ev_grad_proof` (statements verbatim), each followed by
`example := (@<name>_proof : type_of% @HRS.GF.<name>)`.

## 0. Status of the two statements (analysis done before any Lean)

### `gf_ev_mat` : NOT PROVABLE from `AdjointInput + MFHypM` (statement-level obstruction; left open)

`GFEvo.maxHyp` contains `IsEvolution.cont_H` (strong continuity of `V` on `E_γ` on the triangle) and `cont_E`.
`VE` is forced by `GFEvo.dual` (pairing identity on smooth tests), and `VH = VE ∘ j` is forced by `intertwine` and injectivity of `j`.
What the hypotheses give (all verified on paper):
* bounds of `U^{r,t}` on `H^γ`, `H^{γ+2}` and of `𝓛_r : H^{γ+2} → H^γ` (the three terms of `AdjointInput`);
* from these, by duality and the classical equation: `‖(V(t,r') - V(t,r))x‖_{E_{γ+2}} ≤ C|r'-r| ‖x‖_{E_γ}` and the same in `t`
  (so `cont_E` on `E_{γ+2}` holds, via density of `E_γ` in `E_{γ+2}`), and `V(t,r')e_k - V(t,r)e_k` is Lipschitz in `r` in the
  `E_γ`-NORM for plane waves `e_k` (finite Fourier coefficients of `𝓛_σ f` are controlled by `‖f‖_{H^γ}`, `genEntry_bound`);
  hence right-continuity in `t` (`(V(t',t) - 1)y → 0` for `t' ↓ t`, density of plane waves, uniform bound).
* LEFT continuity of `t ↦ V(t,r)x` in the `E_γ`-norm, i.e. `cont_H`, needs relative compactness of `{V(s,r)e_k}_s` in `E_γ`,
  i.e. a bound of `U^{r,t}` on some `H^{γ-ε}` (or an equivalent smoothing/regularity statement for the forward equation).
  `AdjointInput` bounds `U` only on `H^γ` and `H^{γ+2}` (both ≥ γ), so this is NOT implied: abstractly, a uniformly bounded
  cocycle `V(t,r) = B(t)^{-*} B(r)^*`, `B(t) = I + ⟨·,a(t)⟩e` with `a` weakly but not norm continuous satisfies all two-level
  bounds, the Lipschitz estimates in `E_{γ+2}` and the derivative identity, but not `cont_H`.
* In the Prop 3.9 regimes (R1, R2a, R2b, R2c, R3 with `invβ_N > 0`) the lower-level bounds exist (`adjoint_torus_classical` at
  every integer level `m' ≤ γ`), so there the packet is provable by the route of `gf_ev_grad` below (Q54 machinery `ContData`).
  The obstruction is exactly the corner of ISSUES "ADJIN": `invβ_N = 0`, `d-1 < s < d`, `Sym M ≠ 0`, `ρ_N` with zeros, where
  the paper itself has no well-posedness theory and the hypotheses carry only the two levels.
* Minimal repair: add to `AdjointInput` a bound `‖U^{r,t}‖_{H^{γ-1}→H^{γ-1}} ≤ K` (any level `< γ`), or weaken `cont_H` in
  `IsEvolution` to weak continuity on `E_γ` (then `Q45` etc. must be rechecked).  Nothing is changed here.

### `gf_ev_grad` : provable (regimes R1 (`s ≤ d-2`) and R2b (`ρ ≥ c`) cover the gradient case; NO regime-corner issue)

Route (all steps sized in lines of Lean; `S`-free constants are the `Cs m'` of `adjoint_torus_classical`):

(G1) [M]  `μ'` := constant continuation of `ρ_N` after `T`; `AdjointData` for every window, level `γ`, regime `R1` or `R2b b.c`
          chosen by `b.s ≤ d-2`; `propagator D μ' = propagator D ρ_N` for `u ≤ t ≤ T`.  (~250)
(G2) [M]  levels: `QuasiAt` for `a ∈ {γ, γ-2, γ-4}` from `adjoint_torus_classical` (integer levels), `Dom γ` class, `EvoCore`
          (windowless thanks to `μ'`: reuse `evoCore_upF`), `HoldAt` at `γ-2` by Duhamel (`gen_hs_bound`, `GenHyp` from the
          uniform `C^{γ+2d+12}` bounds).  (~450)
(G3) [M]  `exists_evol` at levels `γ`, `γ-2`, `γ-4` (`Q54Aux16`), consistency `V_γ ∘ embed = embed ∘ V_{γ-2}`, `ContData`,
          `strong_cont` (Q54Aux18): `IsEvolution` fields `inj dense self comp intertwine cont_H cont_E`.  (~300)
(G4) [L]  mixed-level dual operator `A_σ : E_{γ-2} → E_γ` (dual of `𝓛_σ : H^γ → H^{γ-2}`, copy of `exists_dual_op` with two
          levels), pairing identity on the class `{C² ∩ H^γ}`, `‖A_σ‖ ≤ C`, `σ ↦ A_σ z` norm-continuous for finitely supported
          `z`.  (~700)
(G5) [L]  mild formula `V(t,r')z - V(t,r)z = -∫_r^{r'} V(t,σ) A_σ z dσ` for `z ∈ E_{γ-2}` (finite `z` by the classical FTC for
          `r ↦ ⟨z, f(r)⟩`, then density).  Consequences: `IsEvolution.deriv` (derivative in `r`), the forward equation
          `∂_t V(t,r)z = A_t V(t,r)z` (at the diagonal), quasi-dissipativity `2⟨z, A_r z⟩ ≤ K‖z‖²` from `‖V‖ ≤ e^{C(t-r)}`
          (no `gradient_energy` needed).  (~700)
(G6) [XL] Galerkin conjunct: `P_n` = coordinate projection onto `|k|_∞ ≤ n` in the real lp coordinates, Galerkin ODE via
          `linear_ode_exists`, strong convergence by energy/Grönwall on dense `x ∈ E_{γ-4}` plus uniform bound.  (~900)
(G7) [M]  `GFEvo.adjoint` (classical existence for `C² ∩ H^γ` data incl. `t = 0`, `MemSobolev`, norm bound with `K`), `GFEvo.dual`,
          assembly of `EvolData`, constants `K`, relocation theorem and `type_of%` tie.  (~400)

## 1. Progress log (final)

`gf_ev_grad` is PROVED as `gf_ev_grad_proof` (GFEVAux26, tied by `example := (@gf_ev_grad_proof : type_of% @HRS.GF.gf_ev_grad)`).
The route actually used differs from G1-G7 above (simplifications found while coding):

* the data level is `J = γ + 2` (so that `a + 2 < J` for the Hölder estimate at `a = γ - 2`), the core is `D = E_{γ-4} ⊂ E_γ`, and
  `A_t : E_{γ-2} → E_γ` is the dual of `𝓛_t : H^γ → H^{γ-2}`; no `E_{γ-4}`-level strong continuity is needed;
* GFEVAux2-3: abstract Hilbert-space layer (`GFAbs`): from the mild identities `V(t,u)x - V(t,u')x = ∫ V(t,s)A_s x ds` and
  `V(t',r)x - V(t,r)x = ∫_t^{t'} V(t',s)A_s V(t,r)x ds`, strong continuity and norm continuity of `s ↦ A_s` it derives
  `∂_r V = -V A`, the forward equation, quasi-dissipativity, and the Galerkin conjunct (ODE in `H →L H`, Gronwall);
* GFEVAux4-6: `forward_hold`/`prop_hold` without a viscosity lower bound (energy argument without `gen_form`), `AdjointData` on
  every window for the constant continuation `μ'` of `ρ_N`, `GenHyp`, `EvoCore`, `QuasiAt` at integer levels (uniform constants);
* GFEVAux7-8: embeddings algebra, the evolution `V` on `E_γ` (Q54 `exists_evol`/`strong_cont`) and `W` on `E_{γ-4}`;
* GFEVAux9-13: two-level dual operator, `A_t`, operator-norm continuity of `t ↦ A_t` (via `forwardGen_diff_bound` and the
  `C^γ`-continuity of the density path from weak continuity);
* GFEVAux14-16: Duhamel pairing formula; GFEVAux17-20: `GFAbs` for the concrete data; GFEVAux21-23: Galerkin projections;
* GFEVAux24: `EvolData` (IsEvolution, Dissipative); GFEVAux25-26: gluing and `gf_ev_grad_proof`.
  NOTE for SPEC-GF2: the field `cont_H` of `IsEvolution` is filled in GFEVAux24 by the same one-line term as `cont_E`.
-/

noncomputable section

namespace HRS.GF

end HRS.GF
