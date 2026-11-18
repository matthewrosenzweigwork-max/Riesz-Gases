import HRS.PDE.MovSpec1

/-!
# MOVSPEC (part 2): `L^p` bounds along the moving reference (Lemma 5.8, Lemma 7.8 item 1)

TeX (M): Lemma `P:lem:moving-moments` proof L6658-6705 (source `P:eq:source`, `P:eq:source-exp` L6670, variable-exponent
identity `P:eq:variable-p` L6678-6680, entropy argument L6681-6684, exponent ODE `P:eq:p-ode` L6685-6688, log-norm
derivative `P:eq:lognorm-derivative` L6692-6695); Lemma `U:lem:alltime-Lp` proof L8408-8420 (`U:eq:variable-exponent`);
the passage from bounded truncations to the singular process L6697-6705, L8569-8580.

Design.  The variable-exponent identity is *not* an integrated inequality one can state without a hypothesis on the
exponent path (the terms `(p-1)∫R h^p dQ` and `p'∫h^p log h dQ` are only finite along the path of `P:eq:p-ode`), so the
statement `mov_lp_ineq` is the *log-norm bound of `P:eq:lognorm-derivative` in integrated, exponentiated form*,
`‖h_t‖_{L^{p(t)}(Q_t)} ≤ ‖h_0‖_{L^{p₀}(Q_0)} exp(C₁∫_0^t L(r)(p(r)-1)/p(r) dr)`, along the closed-form exponent
`1 - 1/p(t) = (1-1/p₀) e^{-C₀∫_0^tL}` (`movT_pPath`), with `C₀ = 1/c`, `C₁ = Cs/c`, where `(c, Cs, L)` is any triple for
which the regularised sources satisfy the scaled exponential bound `P:eq:source-exp` (`MovSrcScaled`): this is exactly
the form in which the entropy inequality `E_ν[S] ≤ (L/c)(H(ν|Q) + Cs)` enters the TeX computation
`E_p[S] ≤ C₀LH_p + C₁L` (L6683).  The hypothesis is on the *regularised* sources because the proof is carried out at
the `ε`-level (L6697-6702: "the scalar bound is uniform in these truncations"); `movT_source_exp_scaled_uniform`
supplies it from the pressure estimates for the actual `L(t) = ‖∇u^t‖_∞`.  `L ≥ ℓ > 0` replaces the TeX convention
"at `L(t) = 0` the source vanishes" (the regularised source has one-body remainders of size `o(1)`); consumers apply it
to `L + η`.

Chain plan (packets of this file; sizes S < M < L < XL):
* `movT_source_exp_scaled_uniform` (SPEC, M-L): scaled `ε`-uniform exponential bound, uniform over the trajectory class
  (same proof as `movT_source_exp_uniform`, MovSpec1 item 9, with the `L(t)`-scaling of M L6321-6322, L6670).
* `movT_lp_reg_bound` (SPEC, XL): the `ε`-level variable-exponent computation for the regularised classical solution
  (M L6674-6695, L8415-8420): the `L^p` analogue of D3 (`d3_entropy_moving`), i.e. `d/dt ∫ w^{p(t)} dq^t` for the classical
  positive solution `w` of the Doob-transformed equation with the moving reference `q^t`, IBP in the physical Dirichlet
  form (the nonpositive Dirichlet form `-(4(p-1)/(pβ))∫|∇h^{p/2}|²` is dropped), the entropy inequality for the
  source, the cancellation `p' = -C₀Lp(p-1)`.  Needs a classical-solution `Φ`-version of D3 (PROOF_QUEUE: "optional").
* `movT_lp_init_limsup` (SPEC, M): initial norms converge, `‖dν/dQ^{M_n}_0‖_{p₀} → ‖dν/dQ_0‖_{p₀}` (dominated convergence:
  `dQ^M/dQ ≥ c > 0` since `g_M ≤ g` and the one-body parts are bounded).
* `movT_lp_lsc` (SPEC, L, generic): joint narrow lower semicontinuity of `(ν,Q) ↦ ‖dν/dQ‖_{L^p(Q)}` on a compact
  metric space (dual representation, as the Donsker-Varadhan formula `b15b_klDiv_eq_iSup`).
* Glue proved here: `movT_pPath_*`, `mov_lp_ineq` (limit passage), `mov_lp_bound` (the consumer statement:
  `pInf`, `C`, `J_N` of Lemma 5.8, and the constants of Lemma 7.8 item 1).
Doubts: (a) the TeX takes `∫_0^∞L < ∞` from "the relaxation input"; `IsSmoothPositiveTrajectory` does not contain it;
(b) Lemma 7.8 item 1 is for the prepared regime `R` (`Regime`) whose trajectory has uniform `C^k` bounds on `[0,∞)`
(`U:eq:background-uniform`, L8395): the bridge `Regime ⇒ MovTraj` on every `[0,T]` with `T`-independent `Λ, c₀` is a
consumer-side packet (like `movT_traj_of_global`, MovSpec3).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### The exponent path -/

/-- The exponent path of `P:eq:p-ode` (M L6685-6688): `p' = -C₀ L(t) p (p-1)`, `p(0) = p₀`, i.e.
`1 - 1/p(t) = (1 - 1/p₀) exp(-C₀ ∫_0^t L)`, with `C₀ = 1/c` (`c` the constant of the exponential source bound). -/
def movT_pPath (c p₀ : ℝ) (L : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / (1 - (1 - 1 / p₀) * Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r))

/-- The accumulated gain `C₁∫_0^t L(r)(p(r)-1)/p(r) dr` of `P:eq:lognorm-derivative` (M L6692-6695), `C₁ = Cs/c`, in closed
form: along `p = movT_pPath c p₀ L` one has `(p-1)/p = (1-1/p₀) e^{-A}`, `A(r) = c⁻¹∫_0^rL`, hence
`∫_0^t L (p-1)/p dr = c (1-1/p₀)(1 - e^{-A(t)})`, so the gain is `Cs (1-1/p₀)(1 - e^{-A(t)})`. -/
def movT_lpGain (c Cs p₀ : ℝ) (L : ℝ → ℝ) (t : ℝ) : ℝ :=
  Cs * (1 - 1 / p₀) * (1 - Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r))

/-- `∫_0^t L ≥ 0` for `L ≥ 0` on `[0,T]`. -/
theorem movT_intL_nonneg {T : ℝ} {L : ℝ → ℝ} (hL : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) : 0 ≤ ∫ r in (0 : ℝ)..t, L r :=
  intervalIntegral.integral_nonneg ht.1 fun r hr => hL r ⟨hr.1, hr.2.trans ht.2⟩

/-- `1 < p(t) ≤ p₀` for `t ∈ [0,T]` (so `p_∞ = inf_t p(t) > 1`, M L6689). -/
theorem movT_pPath_bounds {c p₀ T : ℝ} (hc : 0 < c) (hp₀ : 1 < p₀) {L : ℝ → ℝ}
    (hL : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) : 1 < movT_pPath c p₀ L t ∧ movT_pPath c p₀ L t ≤ p₀ := by
  have hA : 0 ≤ (1 / c) * ∫ r in (0 : ℝ)..t, L r :=
    mul_nonneg (by positivity) (movT_intL_nonneg hL ht)
  set q : ℝ := 1 - 1 / p₀ with hq
  have hp0 : 0 < p₀ := by linarith
  have hq0 : 0 < q := by rw [hq]; have : 1 / p₀ < 1 := (div_lt_one hp0).2 hp₀; linarith
  have hq1 : q < 1 := by
    have h : 0 < 1 / p₀ := by positivity
    rw [hq]; linarith
  set e : ℝ := Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := by
    rw [he]; apply Real.exp_le_one_iff.2; nlinarith
  have hden0 : 0 < 1 - q * e := by nlinarith
  have hden1 : 1 - q * e < 1 := by nlinarith [mul_pos hq0 he0]
  have hdenge : 1 / p₀ ≤ 1 - q * e := by
    have : q * e ≤ q := by nlinarith
    rw [hq] at this ⊢; linarith
  unfold movT_pPath
  refine ⟨?_, ?_⟩
  · rw [← hq, ← he, lt_div_iff₀ hden0]; linarith
  · rw [← hq, ← he, div_le_iff₀ hden0]
    have := (div_le_iff₀ hp0).1 (show 1 / p₀ ≤ 1 - q * e from hdenge)
    nlinarith

/-- Monotone lower bound: `∫_0^T L ≤ Λ₁` gives `p(t) ≥ 1/(1 - (1-1/p₀) e^{-Λ₁/c}) =: p_∞ > 1`. -/
theorem movT_pPath_ge {c p₀ T Λ₁ : ℝ} (hc : 0 < c) (hp₀ : 1 < p₀) {L : ℝ → ℝ}
    (hL : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r) (hLi : IntegrableOn L (Set.Icc 0 T)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) (hΛ : ∫ r in Set.Icc 0 T, L r ≤ Λ₁) :
    1 / (1 - (1 - 1 / p₀) * Real.exp (-(1 / c) * Λ₁)) ≤ movT_pPath c p₀ L t := by
  have hp0 : 0 < p₀ := by linarith
  set q : ℝ := 1 - 1 / p₀ with hq
  have hq0 : 0 < q := by rw [hq]; have : 1 / p₀ < 1 := (div_lt_one hp0).2 hp₀; linarith
  have hq1 : q < 1 := by
    have h : 0 < 1 / p₀ := by positivity
    rw [hq]; linarith
  have hint : ∫ r in (0 : ℝ)..t, L r ≤ Λ₁ := by
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    refine le_trans ?_ hΛ
    exact setIntegral_mono_set hLi (ae_restrict_of_forall_mem measurableSet_Icc hL)
      (Eventually.of_forall (Set.Icc_subset_Icc le_rfl ht.2))
  have hE : Real.exp (-(1 / c) * Λ₁) ≤ Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r) := by
    apply Real.exp_le_exp.2
    have : 0 < 1 / c := by positivity
    nlinarith
  have he0 := Real.exp_pos (-(1 / c) * Λ₁)
  set e₁ := Real.exp (-(1 / c) * Λ₁)
  have hden1 : 0 < 1 - q * e₁ := by
    have : e₁ ≤ Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r) := hE
    have h1 : Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have := movT_intL_nonneg hL ht
      have : 0 < 1 / c := by positivity
      nlinarith
    nlinarith
  have hden2 : 0 < 1 - q * Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r) := by
    have h1 : Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have := movT_intL_nonneg hL ht
      have : 0 < 1 / c := by positivity
      nlinarith
    nlinarith [Real.exp_pos (-(1 / c) * ∫ r in (0 : ℝ)..t, L r)]
  unfold movT_pPath
  rw [← hq]
  apply one_div_le_one_div_of_le hden2
  nlinarith

/-! ### The hypothesis: scaled exponential bound for the regularised sources -/

/-- `P:eq:source-exp` (M L6670) at the regularised level, uniformly in the level: there is `M₀` such that for all
levels `M ≥ M₀` and `r ∈ [0,T]`, `E_{Q^M_r}[exp(c|S^M_r|/L(r))] ≤ e^{Cs}`. -/
def MovSrcScaled (D : DynData d) (N : ℕ) (ρ ρt : ℝ → Torus d → ℝ) (T c Cs : ℝ) (L : ℝ → ℝ) : Prop :=
  ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → ∀ r ∈ Set.Icc 0 T,
    ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (c * |movT_srcReg D N M ρ ρt r X| / L r))
      ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤ ENNReal.ofReal (Real.exp Cs)

/-- **SPEC (sorried, M-L).**  `MovSrcScaled` holds with `c`, `Cs = C N δ_N` independent of the trajectory (data
`s, β ∈ [βm,βp], c₀, Λ_k`), of `T`, of `N ≥ 2`, and of the Lipschitz bound `L` (any `L(r) ≥ ℓ > 0` bounding the
Lipschitz constant of `u^r`).  Proof: as `movT_source_exp_uniform` (MovSpec1 header item 9) combined with the
envelope `|h_{u+e}| ≤ C L(r)(g_M + c_*)` for the pair part (`N:prop:pressure` applied to the kernel divided by
`L(r)`, M L6413-6416, L6321-6322), the one-body remainders being `≤ ℓ·o(1)` for `M ≥ M₀(ℓ)`; the constants are
those of `movT_source_exp` for the pair part.

Repaired 2026-10-17, ISSUES MOVD, MOVE: added `0 < T` (false at `T = 0`: the constants must be uniform in `ρt`, but `ρt 0` is
arbitrary). -/
theorem movT_source_exp_scaled_uniform (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ ∀ {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}, MovTraj D T ρ →
      IsC12Test T ρ ρt → 0 < T → D.s = s → D.invβ⁻¹ ∈ Set.Icc βm βp →
      (∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x) → (∀ r ∈ Set.Icc 0 T, Torus.cbNorm 2 (ρ r) ≤ Λ₂) →
      ∀ {ℓ : ℝ} (L : ℝ → ℝ), 0 < ℓ →
        (∀ r ∈ Set.Icc 0 T, ℓ ≤ L r ∧ IsLipschitzVF (L r) (mfeTransport D (ρ r))) →
        ∀ N : ℕ, 2 ≤ N → MovSrcScaled D N ρ ρt T c (C * N * deltaN d s N) L := by
  sorry

/-! ### Packets of the `L^p` chain -/

/-- **SPEC (sorried, XL): `ε`-level variable-exponent bound** (M L6674-6695, L8415-8420).  For the regularised SDE at
level `M` with initial law `f^M_0 ≪ Q^M_0` and `‖dν_0/dQ^M_0‖_{L^{p₀}} < ∞`, and the scaled exponential bound
`E_{Q^M_r}[e^{c|S^M_r|/L(r)}] ≤ e^{Cs}` (`L ≥ ℓ > 0` on `[0,T]`): for all `t ∈ [0,T]`, `f^M_t ≪ Q^M_t` and
`‖df^M_t/dQ^M_t‖_{L^{p(t)}(Q^M_t)} ≤ ‖df^M_0/dQ^M_0‖_{L^{p₀}(Q^M_0)} exp(movT_lpGain c Cs p₀ L t)`,
`p = movT_pPath c p₀ L`.  The identity `P:eq:variable-p` holds for the classical positive solution (smooth at positive
times, density bounded above and below for smooth initial data; truncate and normalise the initial density, Markov
contraction in `L¹` and Fatou, L6697-6705), the entropy argument and the exact cancellation give
`(log‖h‖_{p(t)})' ≤ C₁L(p-1)/p`.  The Dirichlet form is nonpositive and dropped. -/
theorem movT_lp_reg_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (M : ℝ) (hM : 0 ≤ M) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    {c Cs ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {L : ℝ → ℝ} (hL : ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r)
    (hLi : IntegrableOn L (Set.Icc 0 T))
    (hexp : ∀ r ∈ Set.Icc 0 T, ∫⁻ X : Config d N,
      ENNReal.ofReal (Real.exp (c * |movT_srcReg D N M ρ ρt r X| / L r))
        ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤ ENNReal.ofReal (Real.exp Cs))
    {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hac : selectedLaw P (b15c_regProcess Y) 0 ≪ movT_Q (b15c_gReg d D.s M) D N ρ 0)
    (hfin : eLpNorm ((selectedLaw P (b15c_regProcess Y) 0).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ 0))
      (ENNReal.ofReal p₀) (movT_Q (b15c_gReg d D.s M) D N ρ 0) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      selectedLaw P (b15c_regProcess Y) t ≪ movT_Q (b15c_gReg d D.s M) D N ρ t ∧
      eLpNorm ((selectedLaw P (b15c_regProcess Y) t).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ t))
          (ENNReal.ofReal (movT_pPath c p₀ L t)) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≤
        eLpNorm ((selectedLaw P (b15c_regProcess Y) 0).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ 0))
            (ENNReal.ofReal p₀) (movT_Q (b15c_gReg d D.s M) D N ρ 0) *
          ENNReal.ofReal (Real.exp (movT_lpGain c Cs p₀ L t)) := by
  sorry

/-- **SPEC (sorried, M).**  Convergence of the initial `L^{p₀}` norms: for a probability law `ν ≪ Q_0` with
`‖dν/dQ_0‖_{L^{p₀}(Q_0)} < ∞` (`p₀ > 1`), `ν ≪ Q^{M_n}_0` for all `n` and
`‖dν/dQ^{M_n}_0‖_{L^{p₀}(Q^{M_n}_0)} → ‖dν/dQ_0‖_{L^{p₀}(Q_0)}`.  Proof: `‖h‖_p^p = ∫ (dν/dQ)^{p-1} dν`; the
densities `dQ^M/dQ` are bounded below by `c > 0` uniformly in `M ≥ 0` (`g_M ≤ g` off the collision set, one-body parts
bounded, `K^M ≥ c`), so `(dν/dQ^M)^{p-1} ≤ C (dν/dQ)^{p-1}`; pointwise convergence off collisions; dominated
convergence.  Not in the TeX. -/
theorem movT_lp_init_limsup (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hT : 0 ≤ T) (h : MovTraj D T ρ) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n)
    {ν : Measure (Config d N)} [IsProbabilityMeasure ν] {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hac : ν ≪ movT_Q (periodicRiesz d D.s) D N ρ 0)
    (hfin : eLpNorm (ν.rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
      (movT_Q (periodicRiesz d D.s) D N ρ 0) < ⊤) :
    (∀ n, ν ≪ movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) ∧
      Tendsto (fun n => eLpNorm (ν.rnDeriv (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0))
          (ENNReal.ofReal p₀) (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)) atTop
        (𝓝 (eLpNorm (ν.rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
          (movT_Q (periodicRiesz d D.s) D N ρ 0))) := by
  sorry

/-- **SPEC (sorried, L, generic).**  Joint lower semicontinuity of the `L^p` norm of the density along narrowly
convergent probability measures on a compact metric space: if `ν_n ⇀ ν`, `Q_n ⇀ Q`, `ν_n ≪ Q_n` eventually (Review 1, D1:
without it the statement is false, `eLpNorm (rnDeriv)` ignores the singular part: `ν_n = ν = δ₀`, `Q_n = Q` Haar) and
`liminf ‖dν_n/dQ_n‖_{L^p(Q_n)} < ∞` (`p > 1`), then `ν ≪ Q` and `‖dν/dQ‖_{L^p(Q)} ≤ liminf ‖dν_n/dQ_n‖_{L^p(Q_n)}`.
Proof: `‖dν/dQ‖_p = sup { ∫φ dν : φ ∈ C(α), ∫|φ|^{p'} dQ ≤ 1 }` (equal to `+∞` if `ν ≪̸ Q`), a supremum of jointly
narrowly continuous functionals; same method as `b15b_klDiv_eq_iSup` (density of `C(α)` in `L^{p'}(Q)`, Riesz
representation for the singular case).  M L6703-6705 ("Markov `L¹` contraction and Fatou pass to the original density"),
L8577-8579. -/
theorem movT_lp_lsc {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {ν Q : Measure α} {νn Qn : ℕ → Measure α} [IsProbabilityMeasure ν] [IsProbabilityMeasure Q]
    [∀ n, IsProbabilityMeasure (νn n)] [∀ n, IsProbabilityMeasure (Qn n)]
    (hν : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(νn n)) atTop (𝓝 (∫ x, φ x ∂ν)))
    (hQ : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(Qn n)) atTop (𝓝 (∫ x, φ x ∂Q)))
    (hacn : ∀ᶠ n in atTop, νn n ≪ Qn n) {p : ℝ} (hp : 1 < p)
    (hlim : liminf (fun n => eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n)) atTop < ⊤) :
    ν ≪ Q ∧ eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal p) Q ≤
      liminf (fun n => eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n)) atTop := by
  sorry

/-! ### Glue -/

/-- **`mov_lp_ineq` (variable-exponent `L^p` bound along the moving reference).**  For the particle system `MovHyp`
and any `(c, Cs, ℓ, L)` such that the regularised sources satisfy the scaled exponential bound `MovSrcScaled`
(`P:eq:source-exp`, M L6670), with `‖h_0‖_{L^{p₀}(Q_0)} < ∞`, `h_0 = df_N^0/dQ_N^0`: for all `t ∈ [0,T]`,
`f_N^t ≪ Q_N^t` and `‖h_N^t‖_{L^{p(t)}(Q_N^t)} ≤ ‖h_N^0‖_{L^{p₀}(Q_N^0)} exp(movT_lpGain)`, `movT_lpGain = (Cs/c)∫_0^t L(p-1)/p dr`, with the exponent path
`p = movT_pPath c p₀ L` (`P:eq:p-ode`).  This is `P:eq:lognorm-derivative` (M L6692-6695), integrated and exponentiated,
for the *unregularised* particle system; `f_N^t ≪ Q_N^t` is part of the conclusion so that `h_N^t` is the genuine density.
Proof: `movT_regSeq_exists`, `movT_lp_reg_bound` for each level, `movT_lp_init_limsup`, `movT_lp_lsc` along
`b15c_marginal_tendsto`, `movT_Q_tendsto_weak`. -/
theorem mov_lp_ineq (hN : 2 ≤ N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : MovHyp P D N T ρ X₀ W X) (hρt : IsC12Test T ρ ρt)
    {c Cs ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {L : ℝ → ℝ} (hL : ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r)
    (hLi : IntegrableOn L (Set.Icc 0 T)) (hexp : MovSrcScaled D N ρ ρt T c Cs L)
    {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hac : P.map X₀ ≪ movT_Q (periodicRiesz d D.s) D N ρ 0)
    (hfin : eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
      (movT_Q (periodicRiesz d D.s) D N ρ 0) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      P.map (X t.toNNReal) ≪ movT_Q (periodicRiesz d D.s) D N ρ t ∧
      eLpNorm ((P.map (X t.toNNReal)).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ t))
          (ENNReal.ofReal (movT_pPath c p₀ L t)) (movT_Q (periodicRiesz d D.s) D N ρ t) ≤
        eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
            (movT_Q (periodicRiesz d D.s) D N ρ 0) *
          ENNReal.ofReal (Real.exp (movT_lpGain c Cs p₀ L t)) := by
  intro t ht
  have hS := h.sol
  obtain ⟨ℱ, W', M, Y₀, Y, seq⟩ := movT_regSeq_exists h
  haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
  obtain ⟨hac_n, hlim0⟩ := movT_lp_init_limsup hN (ht.1.trans ht.2) h.traj seq.levels seq.levels_nonneg hp₀ hac hfin
  obtain ⟨M₀, hM₀⟩ := hexp
  have hMev : ∀ᶠ n in atTop, M₀ ≤ M n := seq.levels.eventually_ge_atTop M₀
  have hL0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r := fun r hr => hℓ.le.trans (hL r hr)
  set a := eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
    (movT_Q (periodicRiesz d D.s) D N ρ 0) with ha
  set E := ENNReal.ofReal (Real.exp (movT_lpGain c Cs p₀ L t)) with hE
  have hfinev : ∀ᶠ n in atTop,
      eLpNorm ((P.map X₀).rnDeriv (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)) (ENNReal.ofReal p₀)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) < ⊤ :=
    hlim0.eventually (gt_mem_nhds hfin)
  have hbound : ∀ᶠ n in atTop, selectedLaw P (b15c_regProcess (Y n)) t ≪
      movT_Q (b15c_gReg d D.s (M n)) D N ρ t ∧
      eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) t).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) (ENNReal.ofReal (movT_pPath c p₀ L t))
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ t) ≤
      eLpNorm ((P.map X₀).rnDeriv (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)) (ENNReal.ofReal p₀)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) * E := by
    filter_upwards [hMev, hfinev] with n hn hnf
    have key := movT_lp_reg_bound hN seq.brownian h.traj hρt (M n) (seq.levels_nonneg n)
      seq.init_adapted (seq.sol n) hc hℓ hL hLi (fun r hr => hM₀ (M n) hn r hr) hp₀
      (by rw [movT_reg_init_law seq n]; exact hac_n n)
      (by rw [movT_reg_init_law seq n]; exact hnf) t ht
    rw [movT_reg_init_law seq n] at key
    exact key
  haveI : ∀ n, IsProbabilityMeasure (selectedLaw P (b15c_regProcess (Y n)) t) := fun n =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable (seq.sol n) s) t
  haveI : ∀ n, IsProbabilityMeasure (movT_Q (b15c_gReg d D.s (M n)) D N ρ t) := fun n =>
    movT_QReg_isProb D h.traj (M n) ht
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    inferInstance
  haveI : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ t) := movT_Q_isProb hN h.traj ht
  have hliminf : liminf (fun n => eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) t).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) (ENNReal.ofReal (movT_pPath c p₀ L t))
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) atTop ≤ a * E := by
    calc _ ≤ liminf (fun n => eLpNorm ((P.map X₀).rnDeriv (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0))
              (ENNReal.ofReal p₀) (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) * E) atTop :=
          liminf_le_liminf (hbound.mono fun n hn => hn.2)
      _ = a * E := (ENNReal.Tendsto.mul_const hlim0 (Or.inr ENNReal.ofReal_ne_top)).liminf_eq
  have hlt : liminf (fun n => eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) t).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) (ENNReal.ofReal (movT_pPath c p₀ L t))
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) atTop < ⊤ :=
    lt_of_le_of_lt hliminf (ENNReal.mul_lt_top hfin ENNReal.ofReal_lt_top)
  have hp := (movT_pPath_bounds hc hp₀ hL0 ht).1
  obtain ⟨hacT, hle⟩ := movT_lp_lsc (ν := P.map (X t.toNNReal))
    (hν := fun φ hφ => b15c_marginal_tendsto hS seq.sol seq.eventually_eq ht.1 ht.2 hφ)
    (hQ := fun φ hφ => movT_Q_tendsto_weak hN h.traj seq.levels seq.levels_nonneg ht hφ)
    (hbound.mono fun n hn => hn.1) hp hlt
  exact ⟨hacT, hle.trans hliminf⟩

/-- **`mov_lp_bound`: Lemma 5.8, first assertion `P:eq:log-moment` (M L6642-6646) and Lemma 7.8 item 1 in the
`MovHyp` setting.**  Given the exponent `p₀ > 1`, the data of the pressure estimate (`s`, `β ∈ [βm,βp]`, `inf ρ ≥ c₀`,
`‖ρ^r‖_{C²} ≤ Λ₂`) and a bound `Λ₁` of `∫_0^T L` (`L(t) = ‖∇u^t‖_∞`, M L6660-6661, "the relaxation input gives
`∫_0^∞L < ∞`"), there are `p_∞ > 1` and `C` such that for every `N ≥ 2`, every system and every horizon `T`, if
`h_N^0 = df_N^0/dQ_N^0 ∈ L^{p₀}(Q_N^0)` then for all `t ∈ [0,T]` `f_N^t ≪ Q_N^t` and
`‖h_N^t‖_{L^{p_∞}(Q_N^t)} ≤ exp(C J_N)`, `J_N = 1 + Nδ_N + log‖h_N^0‖_{L^{p₀}(Q_N^0)}` (`logMomentScale`).
`L` is any positive-lower-bounded Lipschitz bound of `u^r` (consumers apply it to `L + η(T)`, `η(T) T ≤ 1`).
Constants independent of `T`, `N`, `L`, the system.  Discharges the "variable-exponent identity" and the
exponential-source steps of `moving_log_moment` (`Sec5.lean:357`) and `alltime_Lp` item 1 (`Sec7Fields.lean:70`). -/
theorem mov_lp_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) (p₀ : ℝ) (hp₀ : 1 < p₀) (Λ₁ : ℝ) (hΛ₁ : 0 ≤ Λ₁) :
    ∃ pInf C : ℝ, 1 < pInf ∧ 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      MovHyp P D N T ρ X₀ W X → IsC12Test T ρ ρt → D.s = s → D.invβ⁻¹ ∈ Set.Icc βm βp →
      (∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x) →
      (∀ r ∈ Set.Icc 0 T, Torus.cbNorm 2 (ρ r) ≤ Λ₂) →
      ∀ L : ℝ → ℝ, (∃ ℓ : ℝ, 0 < ℓ ∧ ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r) → IntegrableOn L (Set.Icc 0 T) →
      (∀ r ∈ Set.Icc 0 T, IsLipschitzVF (L r) (mfeTransport D (ρ r))) →
      ∫ r in Set.Icc 0 T, L r ≤ Λ₁ →
      P.map X₀ ≪ movT_Q (periodicRiesz d s) D N ρ 0 →
      eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d s) D N ρ 0)) (ENNReal.ofReal p₀)
        (movT_Q (periodicRiesz d s) D N ρ 0) < ⊤ →
      ∀ t ∈ Set.Icc 0 T,
        P.map (X t.toNNReal) ≪ movT_Q (periodicRiesz d s) D N ρ t ∧
        eLpNorm ((P.map (X t.toNNReal)).rnDeriv (movT_Q (periodicRiesz d s) D N ρ t))
            (ENNReal.ofReal pInf) (movT_Q (periodicRiesz d s) D N ρ t) ≤
          ENNReal.ofReal (Real.exp (C * (1 + N * deltaN d s N + Real.log
            (eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d s) D N ρ 0)) (ENNReal.ofReal p₀)
              (movT_Q (periodicRiesz d s) D N ρ 0)).toReal))) := by
  obtain ⟨c, C₂, hc, hscal⟩ := movT_source_exp_scaled_uniform hd hs0 hsd βm βp hβm c₀ hc₀ Λ₂
  set Cp : ℝ := max C₂ 0 with hCp
  set q : ℝ := 1 - 1 / p₀ with hq
  have hp0 : 0 < p₀ := by linarith
  have hq0 : 0 < q := by rw [hq]; have : 1 / p₀ < 1 := (div_lt_one hp0).2 hp₀; linarith
  have hq1 : q < 1 := by
    have h : 0 < 1 / p₀ := by positivity
    rw [hq]; linarith
  set e₁ : ℝ := Real.exp (-(1 / c) * Λ₁) with he₁
  have he0 : 0 < e₁ := Real.exp_pos _
  have he1 : e₁ ≤ 1 := by
    rw [he₁]; apply Real.exp_le_one_iff.2
    have : 0 < 1 / c := by positivity
    nlinarith
  set pInf : ℝ := 1 / (1 - q * e₁) with hpInf
  have hden0 : 0 < 1 - q * e₁ := by nlinarith
  have hpInf1 : 1 < pInf := by
    rw [hpInf, lt_div_iff₀ hden0]; nlinarith [mul_pos hq0 he0]
  refine ⟨pInf, max 1 Cp, hpInf1, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro N hN Ω _ P _ D T ρ ρt X₀ W X hH hρt hDs hβ hc0 hΛ L hLℓ hLi hLip hint hac hfin t ht
  obtain ⟨ℓ, hℓ, hLℓ⟩ := hLℓ
  subst hDs
  haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
  haveI : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ 0) :=
    movT_Q_isProb hN hH.traj ⟨le_rfl, ht.1.trans ht.2⟩
  set a := eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
    (movT_Q (periodicRiesz d D.s) D N ρ 0) with ha
  have ha1 : 1 ≤ a := movspec_one_le_eLpNorm_rnDeriv _ _ hac hp₀.le
  have haTop : a ≠ ⊤ := hfin.ne
  have hat1 : 1 ≤ a.toReal := by
    have := ENNReal.toReal_mono haTop ha1
    simpa using this
  have hlog : 0 ≤ Real.log a.toReal := Real.log_nonneg hat1
  have hNδ : 0 ≤ (N : ℝ) * deltaN d D.s N := by
    have : 1 ≤ (N : ℝ) * deltaN d D.s N := one_le_mul_deltaN hs0 N (by omega)
    linarith
  have hapos : 0 < a.toReal := by linarith
  -- the degenerate case `T = 0` (`movT_source_exp_scaled_uniform` needs `0 < T`): `t = 0`, `X 0 = X₀` a.s.
  rcases (ht.1.trans ht.2).eq_or_lt with hT0 | hTpos
  · have ht0 : t = 0 := le_antisymm (by have h2 := ht.2; rwa [← hT0] at h2) ht.1
    subst ht0
    have hXe : P.map (X (0 : ℝ).toNNReal) = P.map X₀ := by
      rw [Real.toNNReal_zero]
      exact Measure.map_congr (by filter_upwards [hH.sol.init] with ω hω; exact hω)
    rw [hXe]
    refine ⟨hac, ?_⟩
    have hpIle : pInf ≤ p₀ := by
      rw [hpInf, div_le_iff₀ hden0]
      have h1 : p₀ * q = p₀ - 1 := by rw [hq]; field_simp
      nlinarith [mul_nonneg (sub_nonneg.2 hp₀.le) (sub_nonneg.2 he1)]
    refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpIle)).trans ?_
    show a ≤ _
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal haTop).symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc a.toReal = Real.exp (Real.log a.toReal) := (Real.exp_log hapos).symm
          _ ≤ _ := by
            refine Real.exp_le_exp.2 ?_
            have hM1 : (1 : ℝ) ≤ max 1 Cp := le_max_left _ _
            nlinarith [mul_le_mul_of_nonneg_right hM1 (by linarith : 0 ≤ 1 + N * deltaN d D.s N + Real.log a.toReal)]
  have hsc := hscal hH.traj hρt hTpos rfl hβ hc0 hΛ L hℓ (fun r hr => ⟨hLℓ r hr, hLip r hr⟩) N hN
  obtain ⟨hacT, hle⟩ := mov_lp_ineq hN P hH hρt hc hℓ hLℓ hLi hsc hp₀ hac hfin t ht
  refine ⟨hacT, ?_⟩
  have hL0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r := fun r hr => hℓ.le.trans (hLℓ r hr)
  haveI : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ t) := movT_Q_isProb hN hH.traj ht
  have hp_ge : pInf ≤ movT_pPath c p₀ L t := movT_pPath_ge hc hp₀ hL0 hLi ht hint
  have hm : AEStronglyMeasurable ((P.map (X t.toNNReal)).rnDeriv
      (movT_Q (periodicRiesz d D.s) D N ρ t)) (movT_Q (periodicRiesz d D.s) D N ρ t) :=
    (Measure.measurable_rnDeriv _ _).aestronglyMeasurable
  have h1 : eLpNorm ((P.map (X t.toNNReal)).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ t))
      (ENNReal.ofReal pInf) (movT_Q (periodicRiesz d D.s) D N ρ t) ≤
      eLpNorm ((P.map (X t.toNNReal)).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ t))
      (ENNReal.ofReal (movT_pPath c p₀ L t)) (movT_Q (periodicRiesz d D.s) D N ρ t) :=
    eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hp_ge)
  refine h1.trans (hle.trans ?_)
  -- the gain
  have hgain : movT_lpGain c (C₂ * N * deltaN d D.s N) p₀ L t ≤ Cp * (N * deltaN d D.s N) := by
    unfold movT_lpGain
    have hA : 0 ≤ (1 / c) * ∫ r in (0 : ℝ)..t, L r :=
      mul_nonneg (by positivity) (movT_intL_nonneg hL0 ht)
    have hE0 : 0 < Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r) := Real.exp_pos _
    have hE1 : Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r) ≤ 1 := by
      apply Real.exp_le_one_iff.2; nlinarith
    set κ : ℝ := (1 - 1 / p₀) * (1 - Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r)) with hκ
    have hκ0 : 0 ≤ κ := mul_nonneg hq0.le (by linarith)
    have hκ1 : κ ≤ 1 := by
      rw [hκ]
      have : (1 - 1 / p₀) ≤ 1 := hq1.le
      nlinarith
    have hCs : C₂ * N * deltaN d D.s N ≤ Cp * (N * deltaN d D.s N) := by
      have : C₂ ≤ Cp := le_max_left _ _
      nlinarith
    have : C₂ * N * deltaN d D.s N * (1 - 1 / p₀) * (1 - Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r)) =
        (C₂ * N * deltaN d D.s N) * κ := by rw [hκ]; ring
    rw [this]
    have hCp0 : 0 ≤ Cp * (N * deltaN d D.s N) := mul_nonneg (le_max_right _ _) hNδ
    rcases le_total 0 (C₂ * N * deltaN d D.s N) with hc2 | hc2
    · calc (C₂ * N * deltaN d D.s N) * κ ≤ (C₂ * N * deltaN d D.s N) * 1 :=
            mul_le_mul_of_nonneg_left hκ1 hc2
        _ ≤ _ := by linarith
    · have : (C₂ * N * deltaN d D.s N) * κ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc2 hκ0
      linarith
  -- assemble: a * exp(gain) ≤ exp(C J)
  have hfinal : a * ENNReal.ofReal (Real.exp (movT_lpGain c (C₂ * N * deltaN d D.s N) p₀ L t)) ≤
      ENNReal.ofReal (Real.exp (max 1 Cp * (1 + N * deltaN d D.s N + Real.log a.toReal))) := by
    rw [← ENNReal.ofReal_toReal haTop, ← ENNReal.ofReal_mul hapos.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx : a.toReal = Real.exp (Real.log a.toReal) := (Real.exp_log hapos).symm
    have hmul : a.toReal * Real.exp (movT_lpGain c (C₂ * N * deltaN d D.s N) p₀ L t) =
        Real.exp (Real.log a.toReal + movT_lpGain c (C₂ * N * deltaN d D.s N) p₀ L t) := by
      rw [Real.exp_add, ← hx]
    rw [hmul]
    refine Real.exp_le_exp.2 ?_
    have h3 : movT_lpGain c (C₂ * N * deltaN d D.s N) p₀ L t ≤ max 1 Cp * (N * deltaN d D.s N) :=
      hgain.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hNδ)
    have h4 : Real.log a.toReal ≤ max 1 Cp * Real.log a.toReal :=
      le_mul_of_one_le_left hlog (le_max_left _ _)
    have hM1 : 0 ≤ max 1 Cp := le_trans zero_le_one (le_max_left _ _)
    have hexpand : max 1 Cp * (1 + N * deltaN d D.s N + Real.log a.toReal) =
        max 1 Cp + max 1 Cp * (N * deltaN d D.s N) + max 1 Cp * Real.log a.toReal := by ring
    rw [ENNReal.toReal_ofReal hapos.le, hexpand]
    linarith
  exact hfinal

end HRS

end
