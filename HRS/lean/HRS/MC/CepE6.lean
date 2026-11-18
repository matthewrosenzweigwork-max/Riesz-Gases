import HRS.MC.CepE6Aux1

/-!
# Packet CEPE6 (`cep_E6_limit_solution`): PLAN AND STATUS (no `_proof` theorem yet; conjunct (e) is BLOCKED)

Conjuncts of the conclusion, argument, inputs (`Z^n`, `w_n = J_n Z^n`, `G_n(Z^n) = ∇Φ(w_n)`, `Z^n - w_n = G_n(Z^n)/n`):
(a) Zl exists, continuous, adapted, `sup_{[0,T]}|Z^n - Zl| → 0` in probability.  E5c (Cauchy in probability on every
    `[0,T]`) + completeness of uniform convergence in probability: choose a diagonal subsequence `n_j` with
    `P(sup_{[0,j]}|Z^{n_{j+1}} - Z^{n_j}| > 2^{-j}) < 2^{-j}`, Borel–Cantelli, a.s. locally uniform limit, define Zl = 0 off the null set;
    `Zl_t` is `ℱ_t`-measurable because `ℱ` is complete (`IsBrownianFiltration`) and each `Z^n_t` is; then the full sequence
    converges in probability by E5c's Cauchy property.
(b) Zl ∈ closure(alcove).  `dist(Z^n_s, alcove) ≤ |Z^n_s - w_n(s)| = |G_n|/n`, and `E∫_0^T |G_n|/n ≤ C/n` (E4); a.s. along a
    subsequence `∫_0^T dist(Z^n,alcove) ds → 0`, so by continuity of Zl, `Zl_s ∈ closure` for all `s` (open complement).
(c) contact set null, (d) local integrability.  `cep_pair_cot_le` (CepE6Aux1) gives `‖∇Φ(z)‖₁ ≥ Σ_p|π cot πd_p|/C - 1`, so
    `‖∇Φ(w_n)‖₁ → ∞` when `w_n → ∂alcove`; with `‖∇Φ‖₁ := +∞` off the open alcove this is lsc, and Fatou on `dt × P` with E4
    gives `E∫_0^T ‖∇Φ(Zl)‖₁ ds ≤ liminf E∫‖G_n(Z^n)‖₁ ≤ C`: (d), and (c) since `‖∇Φ‖₁ = ∞` on the boundary.
(e) integral equation.  `Zl = z₀ + ∫F(Zl) - A + σ'·noise` with `A = lim ∫_0^t G_n(Z^n) ds` (uniform in probability, pathwise
    along a subsequence); `A` has bounded variation (Fatou on total variation, E4).  On open-alcove compacts
    `G_n(Z^n) = ∇Φ(w_n) → ∇Φ(Zl)` uniformly, so `dA = ∇Φ(Zl) ds` there; the remainder `μ_s` of `dA` lives on the Lebesgue-null
    boundary time set `S = {s : Zl_s ∈ ∂alcove}`.  EQUATION (e) ⟺ `μ_s = 0` (no local-time/Skorokhod term).

STATUS OF (e): NOT derivable from E4, E5a, E5b, E5c (nor from the Minty/Yosida monotonicity argument).
  * Minty with the Yosida inequality (E5a) only proves the inclusion `dA ∈ ∂Φ(Zl) + N_{closure}(Zl)` (measure-valued
    subdifferential): singular parts normal to the boundary are admitted.  Reflected Brownian motion (indicator potential, whose
    Yosida approximations satisfy the same abstract E4/E5a/E5b/E5c bounds: `E∫G_n ≤ C`, `E∫|G_n|²/n = O(n^{-1/2})`, Cauchy) is the
    counter-model; E4/E5b are numbers, they are also compatible with `G_n = √n 1_{set of measure n^{-1/2}}`.
  * What separates the log barrier from reflection is the noise (Bessel dimension `δ = 1 + 2a/(Nσ'²) > 1`).  MINIMAL EXTRA
    INPUT: uniform integrability of `G_n(Z^n)` in `L¹(dt × P)`, e.g. `sup_n E∫_0^T ‖G_n(Z^n_s)‖₁^{1+θ} ds < ∞` (some `θ > 0`), equivalently
    the improved occupation bound `E∫_0^T 1_{dist_p(J_nZ^n_s) < r} ds ≤ C r^{1+θ}` for pairs AND clusters of ≥ 3 particles.
    With it: Vitali gives `G_n(Z^n) → ∇Φ(Zl)` weakly in `L¹` (identification on open-alcove compacts), hence `μ_s = 0`.
  * Itô on `f_n = exp(-κ Φ_n)` (`∇Φ_n = G_n`, `ΔΦ_n ≤ ΔΦ(w_n)`, exact identity `|∇Φ|² = (aπ/N)²(2Σ_p cot²πd_p - 2C(N,3))` from
    `cot A cot B + cot B cot C + cot C cot A = 1`, `A+B+C ≡ 0 mod π`) gives, for `κ = qN/a`, `q ∈ (1 - 2a/(Nσ'²), 1)`,
    `E∫ f_n(Z^n) (Σ_p csc² π d_p(w_n)) e^{-κ|G_n|²/2n} ds ≤ C` uniformly in `n`: a UI estimate for `N = 2` (and for pairs isolated
    from the others) but with product weight `∏_p d_p^q`, which for a cluster of 3 particles is `ε^{3q-2}` and is too small
    (needs exponent `< -1`).  A cluster-adapted (radial) Lyapunov function with cutoffs is the missing estimate for `N ≥ 3`.

Delivered here: `HRS/MC/CepE6Aux1.lean`, `HRS.MC.CepE6.cep_pair_cot_le` (each pair force, and their sum,
`≤ C(N,a)(‖∇Φ‖₁ + 1)` on the alcove; required by E7).
-/
