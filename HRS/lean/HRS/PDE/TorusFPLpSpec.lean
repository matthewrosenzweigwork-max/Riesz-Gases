import HRS.PDE.TorusFPEntropySpec

/-!
# Packet D3PHI (specification): the `L^p` (`Φ(h) = h^{p(t)}`) analogue of the D3 layer on the torus

Why.  `movT_lp_reg_bound` (`HRS/PDE/MovSpec2.lean`; TeX M L6674-6695, L8415-8420) is the variable-exponent bound for
the regularised particle system.  ISSUES "MOVSPEC, round 2": it "needs the Φ-version of D3".  D3
(`HRS/PDE/TorusFPEntropySpec.lean`, proved by D3A/D3B) is the case `Φ = h log h`, fixed exponent `1`; this file is the case
`Φ(t,h) = h^{p(t)}` with a time-dependent exponent, for the *same* data: fixed drift `-∇U` (`L = d1_gen κ (d1_gradDrift U)`),
`P = d1_gibbsMeasure κ U`, time-dependent tilt `ψ^t ∈ IsC12Test`, moving reference
`q^t = d3phi_q = d1_gibbsMeasure κ (d3_tiltPot κ U (ψ^t)) = P e^{ψ^t}/Z̃_t` (`d3b_tilt_eq`).

Mathematics (checked here, with the repository conventions).  For a positive classical solution `w` of `∂_t w = L w`
(`D3Classical`), `μ_t = P·w_t`, put `h_t = dμ_t/dq^t = w_t Z̃_t e^{-ψ_t}` (`d3phi_h`), `Z̃_t = ∫ e^{ψ_t} dP`
(`d3phi_Z`).  With the exact moving-reference source `S^t = (L*q^t - ∂_t q^t)/q^t = d3_source + E_{q^t}∂_tψ`
(`d3phi_src`; this is `d3_entropy_moving`'s integrand, cf. TeX `P:eq:source` L6662-6665) one has
`∂_t h = L_q h + S h`, `L_q h = κΔh + (2κ∇log q + ∇U)·∇h`, and for `Y(t) = ∫ h^{p(t)} dq^t`
```
Y' = -κ p(p-1) ∫ h^{p-2}|∇h|² dq + (p-1) ∫ S h^p dq + p' ∫ h^p log h dq
   = -(4(p-1)/(pβ)) ∫ |∇h^{p/2}|² dq + (p-1) ∫ S h^p dq + p' ∫ h^p log h dq ,      β = 1/κ
```
(TeX `P:eq:variable-p` L6678-6679 = `U:eq:variable-exponent` L8417-8420; derivation: `p ∫ h^{p-1} q L_q h = -Dir - ∫ h^p L*q` by one
integration by parts and `∫ ∇(h^p)·(κ∇q + q∇U) = -∫ h^p L*q`, and `∫ h^p ∂_t q = ∫ h^p (L*q - S q)`).  The identity needs no
normalisation of `w` (`D3Classical` is all that is used).  Entropy argument (TeX L6681-6684): with `ν = h^p q/Y`,
`H_p = H(ν|q) = p E_ν[log h] - log Y` and the Donsker-Varadhan inequality `E_ν[S] ≤ (L/c)(H_p + log E_q e^{cS/L})`,
the exponential bound `E_q e^{c|S|/L} ≤ e^{Cs}` (hypothesis `hexp`, the TeX `P:eq:source-exp`) gives
`(p-1)∫ S h^p dq ≤ (p-1) Y (L/c)(H_p + Cs)`; for `p' = -(L/c) p (p-1)` (`P:eq:p-ode` L6685-6688) the coefficient of `H_p` in
`(log Y / p)'` cancels exactly, the Dirichlet form is dropped, and `(log ‖h‖_{p})' ≤ (Cs/c) L (p-1)/p` (`P:eq:lognorm-derivative`
L6692-6695).

## Exponent paths with `L` merely integrable (design decision, doubt (1) below)
`L = ‖∇u^t‖_∞` is only assumed `IntegrableOn` in `movT_lp_reg_bound`, so `p = movT_pPath c p₀ L` is absolutely continuous, not `C¹`.
All statements here therefore take an absolutely continuous exponent path (`AbsolutelyContinuousOnInterval p 0 T`) and use
`deriv p` (Lebesgue-a.e. defined and integrable; `D3phiPath.ode` says `p' = -(1/c) L p (p-1)` a.e.).  Approximating `L` by
continuous functions from above (the monotonicity `L ≤ L' ⇒ E e^{c|S|/L'} ≤ E e^{c|S|/L}` that would allow it) is impossible
in general (e.g. `L = 1 + 1_U`, `U` open dense of small measure).

## Chain plan (files: this one, `TorusFPLpGlue1`-`Glue5`; all compile, `type_of%` ties checked)
SORRIED packets (this file; specifications awaiting review), with TeX lines and sizes (S < M < L < XL):
* **A** `d3phi_identity_classical` (L, ~700-900 lines): the exact integrated identity for the classical positive solution and an
  AC exponent, with the integrability conclusions.  TeX `P:eq:variable-p` L6678-6680, `U:eq:variable-exponent` L8417-8420.
  Route: as `d3_tilted_identity_classical` (`TorusFPEntropyClassicalAux1-5`: weighted Green identity `d3a_*`, differentiation
  under `∫`, `d3a_ftc`), on `[ε,t]`, `ε → 0`; for a `C¹` path a pointwise-in-`r` derivative computation
  (`∂_t h = L_q h + S h`, `∫ h^{p-1} q L_q h = -Dir/p - ∫ h^p L*q /p`), for an AC path approximate `p` in `W^{1,1}` by `C¹`
  paths (both sides are continuous in `(p, p')` for fixed smooth data).
* **C1** `d3phi_approx_Lp` (M, ~200 lines): smooth positive `L^{p}`-approximation of a density with a fixed continuous weight
  (generic measure theory on `𝕋^n`).
PROVED here (no sorry of their own; they depend on A, C1, and the frozen `movT_lp_lsc` of MovSpec2, proved in MovEFinal):
* `TorusFPLpGlue1`: `d3phi_movT_path` (`movT_pPath` is a `D3phiPath`: AC chain rule, Lebesgue differentiation) and
  `d3phi_movT_gain` (`movT_lpGain` is `d3phi_gain` along it); standard axioms only.
* `TorusFPLpGlue4`: `d3phi_Sh_bound` (entropy / Donsker-Varadhan step: Young `a b ≤ a log a - a + e^b` + `hexp`), `d3phi_alg`
  (exact cancellation of the coefficient of `H_p`), `d3phi_lp_classical_bound` (from A: `Φ = (log Y)/p - ∫_0^t (Cs/c) L (p-1)/p`
  is absolutely continuous with `Φ' ≤ 0` a.e.; Dirichlet form dropped).  TeX L6681-6695.
* `TorusFPLpGlue5`: `d3phi_lp_bound_proof` (tied to the frozen `d3phi_lp_bound` by `type_of%`): from A and C1 by
  `d3_classical_exists_proof` + `d3_classical_isWeak_proof` (classical solutions `w^k` from the smooth data of C1),
  `d3phi_lp_classical_bound` at each `k`, `d3b_stability` (narrow convergence of `μ^k_t`), `movT_lp_lsc` (constant reference
  `q^t`).  TeX L6697-6705.  No truncation of the initial density and no comparison principle are needed: smooth positive
  data on the compact torus are bounded above and below, and `L^{p_0}`-approximation replaces "truncation, Markov `L¹`
  contraction + Fatou".
* `TorusFPLpGlue2`: `movT_lp_reg_bound_smooth_of_d3phi`, the `ε`-level bridge for smooth `V` (the SDE law is the
  `D1WeakSolution` of D2 `b15e_law_eq_fp`; `Q^M_r` is the tilted Gibbs measure `movb_gibbs_eq`; `movb_source_eq`; transport by
  `d1_configEquiv`, `d3phi_eLpNorm_rnDeriv_map`), modelled on `movb_reg_ineq_smooth`; uses the FROZEN `d3phi_lp_bound`.
* `TorusFPLpGlue3`: `movT_lp_reg_bound_pos_of_d3phi` (`V ∈ C²`: `V_k → V`, `movb_exists_approx_solutions`, the `C ε_k`
  perturbation of `Cs` from `movb_srcReg_withV_diff`, `movT_lp_lsc` along the constant `Q^M_t`; modelled on `movb_reg_ineq_pos`)
  and **`movT_lp_reg_bound_of_d3phi`**: the statement of `movT_lp_reg_bound` (MovSpec2:176) verbatim (tied by `type_of%`),
  `p = movT_pPath`, `t = 0` trivial, `t > 0` forces `T > 0`.
Total size: A L + C1 M for the packets; ~1.9k lines of proved glue.

## Doubts for the reviewer
(1) AC exponent vs `C¹` exponent (above); `deriv p` is junk on the null set where `p` is not differentiable, harmless.
(2) `d3phi_lp_bound` is stated for a general `L^{p_0}` initial ratio (not only a bounded ratio): the stronger statement, which is
    what `movT_lp_reg_bound` needs (`hfin` is only `eLpNorm < ⊤`); proved from A and C1 in `TorusFPLpGlue5`.
(3) `hexp` is stated for `d3phi_src` (= `d3_source + E_q ψt`), exactly the `d3_entropy_moving` integrand; at the particle level
    `movb_source_eq` identifies it with `movT_srcReg` for smooth `V`; `V ∈ C²` costs a `C ε_k` perturbation of `Cs`.
(4) `T = 0` is excluded from the torus packets (`0 < T`, as D3); `movT_lp_reg_bound` at `T = 0` only has `t = 0`, trivial.
(5) The Dirichlet integrand `‖∇ h^{p/2}‖²` uses `Torus.grad` of `fun y => h y ^ (p/2)` (real power of a positive `C²` function);
    only its nonnegativity is used downstream.
(6) Packet A needs no mass normalisation of `w` and no `hmass`; it is stated with `D3Classical` only (positivity on `[0,T]`).
(7) The consumer `movT_lp_reg_bound` does not need `0 ≤ M` (unused hypothesis), nor `hY₀` beyond the SDE bridge.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS
variable {n : ℕ}

/-! ### Definitions -/

/-- The moving reference `q^r = d1_gibbsMeasure κ (U - κ ψ^r) = P e^{ψ^r}/Z̃_r` (`P = d1_gibbsMeasure κ U`). -/
def d3phi_q (κ : ℝ) (U : Torus n → ℝ) (ψ : ℝ → Torus n → ℝ) (r : ℝ) : Measure (Torus n) :=
  d1_gibbsMeasure κ (d3_tiltPot κ U (ψ r))

/-- The partition function of the tilt, `Z̃_r = ∫ e^{ψ^r} dP`, `P = d1_gibbsMeasure κ U`. -/
def d3phi_Z (κ : ℝ) (U : Torus n → ℝ) (ψ : ℝ → Torus n → ℝ) (r : ℝ) : ℝ :=
  ∫ x, Real.exp (ψ r x) ∂(d1_gibbsMeasure κ U)

/-- The density `h_r = d(P·w_r)/dq^r = w_r Z̃_r e^{-ψ_r}` of `μ_r = P.withDensity w_r` w.r.t. the moving reference `q^r`
(a classical positive function when `w` is a positive classical solution). -/
def d3phi_h (κ : ℝ) (U : Torus n → ℝ) (ψ w : ℝ → Torus n → ℝ) (r : ℝ) (x : Torus n) : ℝ :=
  w r x * d3phi_Z κ U ψ r * Real.exp (-ψ r x)

/-- The exact moving-reference source `S^r = (L*q^r - ∂_r q^r)/q^r = d3_source + E_{q^r}∂_rψ_r`
(TeX `P:eq:source` L6662-6665; the integrand of `d3_entropy_moving`). -/
def d3phi_src (κ : ℝ) (U : Torus n → ℝ) (ψ ψt : ℝ → Torus n → ℝ) (r : ℝ) (x : Torus n) : ℝ :=
  d3_source κ U ψ ψt r x + ∫ y, ψt r y ∂(d3phi_q κ U ψ r)

/-- `Y(r) = ∫ h_r^{p(r)} dq^r` (TeX `Y = ∫ h^{p(t)} dQ_N^t`, L6674). -/
def d3phi_Y (κ : ℝ) (U : Torus n → ℝ) (ψ w : ℝ → Torus n → ℝ) (p : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ x, d3phi_h κ U ψ w r x ^ p r ∂(d3phi_q κ U ψ r)

/-- `∫ h^p log h dq` (the coefficient of `p'` in `P:eq:variable-p`). -/
def d3phi_Ylog (κ : ℝ) (U : Torus n → ℝ) (ψ w : ℝ → Torus n → ℝ) (p : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ x, d3phi_h κ U ψ w r x ^ p r * Real.log (d3phi_h κ U ψ w r x) ∂(d3phi_q κ U ψ r)

/-- `∫ S h^p dq` (the source term of `P:eq:variable-p`). -/
def d3phi_Sh (κ : ℝ) (U : Torus n → ℝ) (ψ ψt w : ℝ → Torus n → ℝ) (p : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ x, d3phi_src κ U ψ ψt r x * d3phi_h κ U ψ w r x ^ p r ∂(d3phi_q κ U ψ r)

/-- The Dirichlet term `(4(p-1)/(pβ)) ∫ |∇h^{p/2}|² dq`, `β = 1/κ` (TeX `P:eq:variable-p` L6678). -/
def d3phi_dir (κ : ℝ) (U : Torus n → ℝ) (ψ w : ℝ → Torus n → ℝ) (p : ℝ → ℝ) (r : ℝ) : ℝ :=
  (4 * (p r - 1) / p r) * κ *
    ∫ x, ‖Torus.grad (fun y => d3phi_h κ U ψ w r y ^ (p r / 2)) x‖ ^ 2 ∂(d3phi_q κ U ψ r)

/-- An admissible exponent path for the constant `c` and the weight `L` on `[0,T]`: absolutely continuous, `> 1`, and solving
`p' = -(1/c) L p (p-1)` almost everywhere (TeX `P:eq:p-ode` L6685-6688 with `C₀ = 1/c`).  `p = movT_pPath c p₀ L` is one
(`d3phi_movT_path`). -/
structure D3phiPath (c : ℝ) (L p : ℝ → ℝ) (T : ℝ) : Prop where
  ac : AbsolutelyContinuousOnInterval p 0 T
  gt_one : ∀ r ∈ Set.Icc 0 T, 1 < p r
  ode : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.Ioo 0 T →
    HasDerivAt p (-(1 / c) * L r * p r * (p r - 1)) r

/-- The accumulated gain `∫_0^t C₁ L(r) (p(r)-1)/p(r) dr`, `C₁ = Cs/c` (TeX `P:eq:lognorm-derivative` L6692-6695, integrated). -/
def d3phi_gain (c Cs : ℝ) (L p : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..t, (Cs / c) * L r * ((p r - 1) / p r)

/-! ### Packet A: the classical variable-exponent identity -/

/-- **SPEC (sorried, L): exact variable-exponent identity for a positive classical solution** (TeX `P:eq:variable-p` L6678-6680,
`U:eq:variable-exponent` L8417-8420, integrated form).  Hypotheses: `D3Classical κ U T w` (the classical positive solution of
`∂_t w = L w`, `D3Classical.c12`, `.pos`), a tilt `ψ ∈ IsC12Test T ψ ψt`, an absolutely continuous exponent `p > 1` on `[0,T]`.
Conclusion, for every `t ∈ [0,T]`: the three integrands are integrable on `[0,t]` (so none of the real integrals is a junk
value) and
`Y(t) + ∫_0^t Dir = Y(0) + ∫_0^t ((p-1) ∫ S h^p dq + p' ∫ h^p log h dq) dr`.
Technical hypotheses: `hn : 1 ≤ n`, `0 < κ`, `U` smooth, `0 < T` (as D3).  No normalisation of `w` is needed.
Route: see the header (A). -/
theorem d3phi_identity_classical (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w)
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) {p : ℝ → ℝ}
    (hpac : AbsolutelyContinuousOnInterval p 0 T) (hp1 : ∀ r ∈ Set.Icc 0 T, 1 < p r) :
    ∀ t ∈ Set.Icc 0 T,
      IntegrableOn (fun r => d3phi_dir κ U ψ w p r) (Set.Icc 0 t) ∧
      IntegrableOn (fun r => (p r - 1) * d3phi_Sh κ U ψ ψt w p r) (Set.Icc 0 t) ∧
      IntegrableOn (fun r => deriv p r * d3phi_Ylog κ U ψ w p r) (Set.Icc 0 t) ∧
      d3phi_Y κ U ψ w p t + ∫ r in Set.Icc 0 t, d3phi_dir κ U ψ w p r
        = d3phi_Y κ U ψ w p 0 + ∫ r in Set.Icc 0 t,
            ((p r - 1) * d3phi_Sh κ U ψ ψt w p r + deriv p r * d3phi_Ylog κ U ψ w p r) := by
  sorry

/-! ### Packet C1: smooth positive approximation in `L^{p}` -/

/-- **SPEC (sorried, M): smooth positive approximation of an `L^{p₀}` density, with a fixed continuous weight.**  `q` a
probability measure on `𝕋^n`, `ν ≪ q` a probability measure with `h₀ = dν/dq ∈ L^{p₀}(q)`, `p₀ > 1`, `ρ` continuous and
positive (in the application `ρ = Z̃_0 e^{-ψ^0}`, so that `P·g = q^0 · (g ρ)`, `ψ^0 ∈ C²` only: the smooth object is `g`, not `gρ`).
There are smooth positive `g_k` with `∫ g_k ρ dq = 1`, `g_k ρ q → ν` narrowly and `‖g_k ρ‖_{L^{p₀}(q)} → ‖h₀‖_{L^{p₀}(q)}`.
Route: `ρ` is bounded above and below, so `h₀/ρ ∈ L^{p₀}(q)`; bounded continuous functions are dense in `L^{p₀}(q)`
(`MemLp.exists_boundedContinuous_eLpNorm_sub_le`, `q` finite Borel on a compact metric space), smooth ones are uniformly dense
in `C(𝕋^n)` (`d1_exists_smooth_approx`), add `1/k` for positivity, divide by `∫ g ρ dq → 1`; narrow convergence from
`|∫ (g ρ - h₀) φ dq| ≤ ‖φ‖_∞ ‖g ρ - h₀‖_{L^1(q)} ≤ ‖φ‖_∞ ‖g ρ - h₀‖_{L^{p₀}(q)}`, and the norm convergence from the triangle inequality. -/
theorem d3phi_approx_Lp (q : Measure (Torus n)) [IsProbabilityMeasure q] {ρ : Torus n → ℝ}
    (hρc : Continuous ρ) (hρ : ∀ x, 0 < ρ x) {ν : Measure (Torus n)} [IsProbabilityMeasure ν]
    (hac : ν ≪ q) {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hfin : eLpNorm (ν.rnDeriv q) (ENNReal.ofReal p₀) q < ⊤) :
    ∃ g : ℕ → Torus n → ℝ, (∀ k, Torus.IsSmooth (g k)) ∧ (∀ k x, 0 < g k x) ∧
      (∀ k, ∫ x, g k x * ρ x ∂q = 1) ∧
      (∀ φ : Torus n → ℝ, Continuous φ →
        Tendsto (fun k => ∫ x, g k x * ρ x * φ x ∂q) atTop (𝓝 (∫ x, φ x ∂ν))) ∧
      Tendsto (fun k => eLpNorm (fun x => ENNReal.ofReal (g k x * ρ x)) (ENNReal.ofReal p₀) q) atTop
        (𝓝 (eLpNorm (ν.rnDeriv q) (ENNReal.ofReal p₀) q)) := by
  sorry

/-! ### Packet C: the measure-level `L^p` inequality -/

/-- **SPEC (sorried, L): the `L^p` analogue of `d3_entropy_moving`** (TeX L6674-6705).  Let `μ` be a `D1WeakSolution` of the
Fokker-Planck equation with drift `-∇U` with probability initial datum, `μ 0 ≪ q^0` and
`‖dμ_0/dq^0‖_{L^{p(0)}(q^0)} < ∞`, `ψ ∈ IsC12Test T ψ ψt` a tilt with moving reference `q^r = d3phi_q`, and suppose the
source satisfies the exponential bound `E_{q^r}[exp(c|S^r|/L(r))] ≤ e^{Cs}` (`S = d3phi_src`; TeX `P:eq:source-exp` L6670) for
`r ∈ [0,T]`, with `L ≥ ℓ > 0` integrable and `p` an admissible exponent path (`D3phiPath c L p T`).  Then for all `t ∈ [0,T]`:
`μ_t ≪ q^t` and
`‖dμ_t/dq^t‖_{L^{p(t)}(q^t)} ≤ ‖dμ_0/dq^0‖_{L^{p(0)}(q^0)} · exp(∫_0^t (Cs/c) L (p-1)/p dr)`.
Technical hypotheses: `hn`, `0 < κ`, `U` smooth, `0 < T`, `[IsProbabilityMeasure (μ 0)]` (as D3); `0 < c`, `0 < ℓ ≤ L`,
`IntegrableOn L` (the TeX convention `L(t) = 0 ⇒ S = 0` is replaced by `L ≥ ℓ > 0`, as in `movT_source_exp_scaled_uniform`).
The absolute continuity conclusion is part of the statement because `eLpNorm (rnDeriv ..)` ignores the singular part.
Route: see the header (C). -/
theorem d3phi_lp_bound (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt)
    {c Cs ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {L : ℝ → ℝ} (hL : ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r)
    (hLi : IntegrableOn L (Set.Icc 0 T))
    (hexp : ∀ r ∈ Set.Icc 0 T, ∫⁻ x, ENNReal.ofReal (Real.exp (c * |d3phi_src κ U ψ ψt r x| / L r))
      ∂(d3phi_q κ U ψ r) ≤ ENNReal.ofReal (Real.exp Cs))
    {p : ℝ → ℝ} (hp : D3phiPath c L p T)
    (hac : μ 0 ≪ d3phi_q κ U ψ 0)
    (hfin : eLpNorm ((μ 0).rnDeriv (d3phi_q κ U ψ 0)) (ENNReal.ofReal (p 0)) (d3phi_q κ U ψ 0) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      μ t ≪ d3phi_q κ U ψ t ∧
      eLpNorm ((μ t).rnDeriv (d3phi_q κ U ψ t)) (ENNReal.ofReal (p t)) (d3phi_q κ U ψ t) ≤
        eLpNorm ((μ 0).rnDeriv (d3phi_q κ U ψ 0)) (ENNReal.ofReal (p 0)) (d3phi_q κ U ψ 0) *
          ENNReal.ofReal (Real.exp (d3phi_gain c Cs L p t)) := by
  sorry

end HRS
