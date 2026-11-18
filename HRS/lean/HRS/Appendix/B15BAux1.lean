import HRS.Appendix.B15CAux3
import HRS.Appendix.B15BDV

/-!
# Packet B15-B: lower semicontinuity of the relative entropy and of the Fisher information (Step 4 of B.15)

Source: `HRS_periodic_main_20261008T010000Z.tex`, Proposition B.15 (`M:B:prop:sde-entropy-law`,
L12140-12152), proof Step 4 (L12188-12235); plan entry "2026-10-16 plan for the M external cluster"
in `docs/PROOF_QUEUE.md`; ISSUES entries "B15-A0", "B15-C", "D1".

SPEC FILE.  Five statements are `sorry` (marked `SPEC` in their docstrings): `b15b_klDiv_eq_iSup` (DV, L),
`b15b_gibbsRef_tendsto_weak` (S-M), `b15b_gibbsEntropy_liminf_le` (M), `b15b_totalPotential_c1` (S),
`b15b_fisherIntegrand_continuous` (M).  Everything else, including the Fisher liminf, the measurability of
`r ↦ fisherInfo`, the entropy-at-time-`t` corollary and the assembly `b15b_step4_limit`, is proved from them
(these dependent theorems are therefore conditional on the five).

What Step 4 needs from this packet (all along the sequence `ε_n ↔ M_n → ∞` of packet C):

1. **Entropy** (L12195-12204, L12212): `𝓗_G(P^t) ≤ liminf 𝓗_{G_{ε_n}}(P^t_{ε_n})`, from joint lower
   semicontinuity of `H(P|Q)` (Donsker-Varadhan, L12197-12198) and `Q_{ε_n} → Q` in total variation.
   `b15b_klDiv_eq_iSup` (DV) → `b15b_klDiv_liminf_le` → `b15b_gibbsEntropy_liminf_le`.
2. **Fisher information** (L12205-12218): `∫_0^t 𝓘_G(P^r) dr ≤ liminf ∫_0^t 𝓘_{G_{ε_n}}(P^r_{ε_n}) dr`
   (`b15b_fisher_lintegral_liminf`).
3. **Measurability** of `r ↦ 𝓘_G(P^r)` on `[0,T]` (`b15b_measurable_fisherInfo`): the `lintegral` in the
   conclusion of B.15 (`b15_EntropyLawConcl`) is then an honest integral; it is also needed for Fatou.
4. **Assembly** (L12219-12222): `b15b_step4_limit`, which passes to the liminf in the regularised
   entropy inequality `B:eq:selected-regularized-entropy` in the exact form `b15_EntropyLawConcl` needs.

Representation decisions (shared by the whole file).
* Everything is stated along sequences `M : ℕ → ℝ`, `M n → ∞`, `M n ≥ 0` (levels of the truncated kernels
  `g_M` of packet C, `ε ↔ 1/M`), with the regularised processes `Y n` (lifted additive SDE solutions) and
  `b15c_regProcess (Y n)`, hypotheses `hS hY hev` exactly as in `b15c_marginal_tendsto`.
* Weak (narrow) convergence of laws on the compact space `Config d N` is expressed as convergence of
  `∫ φ dP_n` for every continuous `φ` (`C_b = C` on a compact space); this is the conclusion of
  `b15c_marginal_tendsto`, so no `ProbabilityMeasure` topology is needed.
* The TeX derives the Fisher bound from the *space-time* convergence (`b15c_fisher_spacetime_tendsto`,
  L12218).  We do not use it: the variational formula is a supremum of functionals each of which is
  continuous under the pointwise-in-`r` weak convergence `P^r_{ε_n} ⇀ P^r` (`b15c_marginal_tendsto`) and
  the integrand is eventually independent of `n` (`b15c_fisherIntegrand_eventuallyEq`).  Hence
  `𝓘_G(P^r) ≤ liminf 𝓘_{G_{ε_n}}(P^r_{ε_n})` for *every* `r ∈ [0,T]` (`b15b_fisherInfoGen_liminf_le`)
  and Fatou in `r` finishes (`b15b_fisher_lintegral_liminf`).  This needs neither time-dependent test
  fields nor the "countable exhaustion" (the supremum over *all* test fields is used, and measurability
  in `r` is via lower semicontinuity in `r`, `b15b_fisherInfoGen_lowerSemicontinuousOn`).  The
  sorry'd `b15c_fisher_spacetime_tendsto`-route is therefore not needed (it remains correct).
* `EReal` `liminf`s: `EReal.le_liminf_add` (Mathlib) holds without hypotheses, so the "uniform lower
  bound" of the TeX (L12199-12202) is not needed for the bookkeeping in `b15b_step4_limit`
  (it is `≥ -log Z_{ε_n} ≥ -log C`, `b15c_partition_bounds`, and only makes the `EReal` sums honest).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ## Part 1: lower semicontinuity of the relative entropy -/

/-- **Donsker-Varadhan variational formula** (TeX L12197-12198,
`H(P|Q) = sup_{φ ∈ C_b} {∫ φ dP - log ∫ e^φ dQ}`) for probability measures on a compact metric space
(`C_b = C`).  Mathlib's `klDiv` (`ℝ≥0∞`-valued, `+∞` if `P ≪̸ Q` or `llr` not integrable) is the `H` of the
TeX for probability measures.  The supremum is `≥ 0` (`φ = 0`), so `ENNReal.ofReal` loses nothing.
SPEC.  Proof outline: (≤ klDiv) Gibbs inequality `∫ φ dP - log ∫ e^φ dQ ≤ ∫ llr dP` by Jensen applied to
`e^φ/∫e^φ dQ` (when `P ≪ Q`, `llr` integrable; `+∞` otherwise: trivial); (≥) for `P ≪ Q` with `f = dP/dQ`,
approximate `log f ∧ k ∨ -k` by continuous functions in `L¹(P)` and `L¹(Q)` (regularity of Borel
probability measures on compact metric spaces / density of `C(α)` in `L¹`), then monotone convergence in
`k`; for `P ≪̸ Q` use closed `A` with `Q(A) = 0 < P(A)` and `φ_k = k·(1 - j_k·dist(·,A) ∧ 1)` with `j_k` chosen so that `e^k·Q({dist(·,A) < 1/j_k}) ≤ 1` (statement review).
Estimated size: L (200-400 lines). -/
theorem b15b_klDiv_eq_iSup {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    InformationTheory.klDiv P Q =
      ⨆ φ : C(α, ℝ), ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q)) :=
  b15b_klDiv_eq_iSup_proof P Q

/-- **Joint lower semicontinuity of `klDiv` along sequences, narrow topology in both arguments**
(TeX L12197-12199: "joint lower semicontinuity follows from the variational formula").  `P_n ⇀ P`,
`Q_n ⇀ Q` in the sense `∫ φ dP_n → ∫ φ dP`, `∫ φ dQ_n → ∫ φ dQ` for all continuous `φ`.  (Total variation
convergence `Q_{ε_n} → Q`, as in the TeX, implies this, `b15b_gibbsRef_tendsto_weak`.)  Proved from
`b15b_klDiv_eq_iSup`: each term of the supremum is continuous along the sequence. -/
theorem b15b_klDiv_liminf_le {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] {P Q : Measure α} {Pn Qn : ℕ → Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [∀ n, IsProbabilityMeasure (Pn n)] [∀ n, IsProbabilityMeasure (Qn n)]
    (hP : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(Pn n)) atTop (𝓝 (∫ x, φ x ∂P)))
    (hQ : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(Qn n)) atTop (𝓝 (∫ x, φ x ∂Q))) :
    InformationTheory.klDiv P Q ≤ liminf (fun n => InformationTheory.klDiv (Pn n) (Qn n)) atTop := by
  rw [b15b_klDiv_eq_iSup P Q]
  refine iSup_le fun φ => ?_
  have hφc : Continuous φ := φ.continuous
  have hexp : Continuous fun x => Real.exp (φ x) := Real.continuous_exp.comp hφc
  have h1 := hP φ hφc
  have h2 := hQ _ hexp
  have hpos : 0 < ∫ x, Real.exp (φ x) ∂Q := by
    refine integral_exp_pos ?_
    exact hexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h3 := ENNReal.tendsto_ofReal (h1.sub (h2.log hpos.ne'))
  rw [← h3.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  rw [b15b_klDiv_eq_iSup (Pn n) (Qn n)]
  exact le_iSup (fun φ : C(α, ℝ) =>
    ENNReal.ofReal (∫ x, φ x ∂(Pn n) - Real.log (∫ x, Real.exp (φ x) ∂(Qn n)))) φ

/-- `Q_{N,ε_n} ⇀ Q_N` (TeX L12192-12194, `Q_{N,ε} → Q_N` in total variation, here in the weaker narrow
form that `b15b_klDiv_liminf_le` consumes): `Q_{N,ε_n} = b15c_gibbsRefGen D.invβ (U^{ε_n})` and
`Q_N = gibbsRef D N`.  From `b15c_normDensity_tendsto_L1` (`L¹` convergence of the normalised densities,
`b15c_gibbsRefGen_eq_withDensity`, `b15c_gibbsRef_eq_gen`) and `|∫ φ d(Q_n - Q)| ≤ ‖φ‖_∞ ‖f_n - f‖_{L¹}`.
SPEC (cheap, S-M). -/
theorem b15b_gibbsRef_tendsto_weak (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n)
    {φ : Config d N → ℝ} (hφ : Continuous φ) :
    Tendsto (fun n => ∫ x, φ x ∂(b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (M n))))
      atTop (𝓝 (∫ x, φ x ∂(gibbsRef D N))) := by
  sorry

/-- The Gibbs reference measures `Q_{N,ε}` and `Q_N` are probability measures (`0 < Z < ∞`,
`b15c_partition_bounds`), so `b15b_klDiv_liminf_le` applies to them.  Proved. -/
theorem b15b_gibbsRef_isProb (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) :
    IsProbabilityMeasure (gibbsRef D N) := by
  obtain ⟨hpos, hlt⟩ := b15_gibbsPartition_pos_lt_top (N := N) D hV hβ
  refine ⟨?_⟩
  simp only [gibbsRef, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hlt.ne

/-- **Step 4, entropy lower semicontinuity** (TeX L12195-12204, `B:eq:selected-entropy-lsc`, first
inequality, for a general narrowly convergent sequence of probability laws `P_n ⇀ P`):
`𝓗_{G_{N,β_N,V}}(P) ≤ liminf_n 𝓗_{G_{N,ε_n}}(P_n)`, where `𝓗_{G_{ε_n}} = b15c_gibbsEntropyGen _ U^{ε_n}`
(`= H(·|Q_{ε_n}) - log Z_{ε_n}`, L12198 is the definition) and `𝓗_G = gibbsEntropy D`
(`= H(·|Q) - log Z`).  `EReal`-valued, so `+∞` on either side is allowed.  Proof: `b15b_klDiv_liminf_le`
with `b15b_gibbsRef_tendsto_weak`, then `log Z_{ε_n} → log Z` (`b15c_partition_tendsto`, `Z > 0`) and
subtraction of a convergent real sequence from an `EReal` `liminf`.  SPEC (M). -/
theorem b15b_gibbsEntropy_liminf_le (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n)
    {P : Measure (Config d N)} {Pn : ℕ → Measure (Config d N)}
    [IsProbabilityMeasure P] [∀ n, IsProbabilityMeasure (Pn n)]
    (hP : ∀ φ : Config d N → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂(Pn n)) atTop (𝓝 (∫ x, φ x ∂P))) :
    gibbsEntropy D P ≤
      liminf (fun n => b15c_gibbsEntropyGen D.invβ (b15c_potentialReg (N := N) D (M n)) (Pn n)) atTop := by
  sorry

/-- The time marginal `selectedLaw P Z r` of a process measurable at time `r⁺` is a probability measure. -/
theorem b15b_selectedLaw_isProb {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ℝ≥0 → Ω → Config d N} (hZ : ∀ s, Measurable (Z s)) (r : ℝ) :
    IsProbabilityMeasure (selectedLaw P Z r) := by
  unfold selectedLaw
  haveI : Fact (AEMeasurable (Z (Real.toNNReal r)) P) := ⟨(hZ _).aemeasurable⟩
  exact ⟨by
    rw [Measure.map_apply_of_aemeasurable (hZ _).aemeasurable MeasurableSet.univ]; simp⟩

/-! ## Part 2: the Fisher information -/

/-- The lift of a potential to the covering space `(ℝ^d)^N` is `C¹` on the lift of the collision-free
set `Ω_N`: the regularity of `U` used for the Fisher integrands (`U = totalPotential D` or `U^ε`). -/
def B15BUnifC1 (U : Config d N → ℝ) : Prop :=
  ContDiffOn ℝ 1 (fun Y : Fin N → Euc d => U (fun i => Torus.mk (Y i)))
    {Y | (fun i => Torus.mk (Y i)) ∉ collisionSet d N}

/-- `totalPotential D` is `C¹` (in fact `C²`) off collisions for `V ∈ C²`: smoothness of the periodic
Riesz kernel off `0` (`b15c_contDiffAt_lift_periodicRiesz`) and of `V`.  SPEC (S). -/
theorem b15b_totalPotential_c1 (D : DynData d) (hV : Torus.IsCk 2 D.V) :
    B15BUnifC1 (totalPotential (N := N) D) := by
  sorry

/-- The regularised potential `U^ε` is `C¹` everywhere (`b15c_potentialReg_contDiff`).  Proved. -/
theorem b15b_potentialReg_c1 (D : DynData d) (hV : Torus.IsCk 2 D.V) (M : ℝ) :
    B15BUnifC1 (b15c_potentialReg (N := N) D M) := by
  have hV1 : Torus.IsCk 1 D.V := ContDiff.of_le hV (by norm_num)
  exact (b15c_potentialReg_contDiff D (n := 1) (by exact_mod_cast le_top) hV1 M).contDiffOn

/-- **Continuity of the Fisher integrand on the torus** (the `hcont` hypothesis of
`b15c_fisher_spacetime_tendsto`; TeX is silent: the integrand of L12205-12209 is a function on
`(𝕋^d)^N`).  For a test field `ζ ∈ C_c^∞(Ω_N)` (`IsFisherTestField`) and a potential `U` that is `C¹` off
collisions, `X ↦ -2 Div ζ + 2β DU[ζ] - |ζ|²` is continuous on the *torus* configuration space.
The point: `configDiv ζ` and `fderiv (lift U)` are evaluated at the fundamental-domain representative
`rep X`; the lifts are periodic so their `fderiv`s are periodic (`iteratedFDeriv_lift_periodic`), hence
`X ↦ fderiv … (rep X)` is continuous on the torus away from collisions, and `ζ` kills the term near
collisions (the product vanishes on the open complement of `supp ζ`, and `fderiv` of a smooth compactly
supported field vanishes there).  SPEC (M). -/
theorem b15b_fisherIntegrand_continuous (invβ : ℝ) {U : Config d N → ℝ} (hU : B15BUnifC1 U)
    {ζ : Config d N → (Fin N → Euc d)} (hζ : IsFisherTestField ζ) :
    Continuous (b15c_fisherIntegrand invβ U ζ) := by
  sorry

/-- The `hcont` of `b15c_fisher_spacetime_tendsto`, discharged from `hV : Torus.IsCk 2 D.V`. -/
theorem b15b_hcont (D : DynData d) (hV : Torus.IsCk 2 D.V)
    {ζ : Config d N → (Fin N → Euc d)} (hζ : IsFisherTestField ζ) :
    Continuous (b15c_fisherIntegrand D.invβ (totalPotential D) ζ) :=
  b15b_fisherIntegrand_continuous _ (b15b_totalPotential_c1 D hV) hζ

/-- **Lower semicontinuity of the Fisher functional in the pair (potential, law)** (TeX L12205-12216).
If `P_n ⇀ P` narrowly and for every test field `ζ` the integrand for `U_n` is eventually equal to that for
`U` (`b15c_fisherIntegrand_eventuallyEq`: both reduce to the `U`-independent terms outside `supp ζ`, and
`U^{ε_n} = U` near the compact `supp ζ ⊂ Ω_N` for large `n`), then
`𝓘_U(P) ≤ liminf_n 𝓘_{U_n}(P_n)`.  This is "a supremum of continuous functionals is lower
semicontinuous": for each `ζ`, `∫ integrand_U(ζ) dP_n → ∫ integrand_U(ζ) dP` and
`ofReal ∫ integrand_{U_n}(ζ) dP_n ≤ 𝓘_{U_n}(P_n)`.  Proved (no separability or exhaustion needed). -/
theorem b15b_fisherInfoGen_liminf_le (invβ : ℝ) {U : Config d N → ℝ} {Un : ℕ → Config d N → ℝ}
    {P : Measure (Config d N)} {Pn : ℕ → Measure (Config d N)}
    (hcont : ∀ ζ, IsFisherTestField ζ → Continuous (b15c_fisherIntegrand invβ U ζ))
    (hev : ∀ ζ, IsFisherTestField ζ →
      ∀ᶠ n in atTop, b15c_fisherIntegrand invβ (Un n) ζ = b15c_fisherIntegrand invβ U ζ)
    (hP : ∀ φ : Config d N → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂(Pn n)) atTop (𝓝 (∫ x, φ x ∂P))) :
    b15_fisherInfoGen invβ U P ≤ liminf (fun n => b15_fisherInfoGen invβ (Un n) (Pn n)) atTop := by
  simp only [b15c_fisherInfoGen_eq]
  refine iSup₂_le fun ζ hζ => ?_
  have hint := hP _ (hcont ζ hζ)
  have h2 : Tendsto (fun n => ∫ X, b15c_fisherIntegrand invβ (Un n) ζ X ∂(Pn n)) atTop
      (𝓝 (∫ X, b15c_fisherIntegrand invβ U ζ X ∂P)) :=
    hint.congr' ((hev ζ hζ).mono fun n hn => by simp only [hn])
  have h3 := ENNReal.tendsto_ofReal h2
  rw [← h3.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  exact le_iSup₂ (f := fun (ζ : Config d N → (Fin N → Euc d)) (_ : IsFisherTestField ζ) =>
    ENNReal.ofReal (∫ X, b15c_fisherIntegrand invβ (Un n) ζ X ∂(Pn n))) ζ hζ

/-- **`r ↦ 𝓘_U(P^r)` is lower semicontinuous on `[0,T]`** for the time marginals of a process with
(a.s.) continuous paths on `[0,T]`: it is a supremum over test fields `ζ` of the functions
`r ↦ ofReal ∫ integrand(ζ) dP^r = ofReal E[integrand(ζ)(Z_{r⁺})]`, continuous on `[0,T]` by dominated
convergence (continuous integrand on a compact space, `b15c3_integral_contOn`-style).  The basis of the
measurability statement (3) of the plan (TeX: implicit in the `∫_0^t 𝓘 dr` of L12149-12151, L12221).
Proved (given the continuity hypothesis `hcont`, supplied by `b15b_fisherIntegrand_continuous`). -/
theorem b15b_fisherInfoGen_lowerSemicontinuousOn {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (invβ : ℝ) {U : Config d N → ℝ}
    (hcont : ∀ ζ, IsFisherTestField ζ → Continuous (b15c_fisherIntegrand invβ U ζ))
    {Z : ℝ≥0 → Ω → Config d N} (hZ : ∀ s, Measurable (Z s)) {T : ℝ}
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun r : ℝ => Z (Real.toNNReal r) ω) (Set.Icc 0 T)) :
    LowerSemicontinuousOn (fun r : ℝ => b15_fisherInfoGen invβ U (selectedLaw P Z r)) (Set.Icc 0 T) := by
  simp only [b15c_fisherInfoGen_eq]
  refine lowerSemicontinuousOn_iSup fun ζ => lowerSemicontinuousOn_iSup fun hζ => ?_
  have hf := hcont ζ hζ
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Config d N)).exists_bound_of_continuousOn hf.continuousOn
  have hcon : ContinuousOn (fun r : ℝ => ∫ x, b15c_fisherIntegrand invβ U ζ x ∂(selectedLaw P Z r))
      (Set.Icc 0 T) := by
    have h0 : ContinuousOn (fun r : ℝ => ∫ ω, b15c_fisherIntegrand invβ U ζ (Z (Real.toNNReal r) ω) ∂P)
        (Set.Icc 0 T) := by
      refine continuousOn_of_dominated (F := fun r ω => b15c_fisherIntegrand invβ U ζ (Z (Real.toNNReal r) ω))
        (bound := fun _ => C) (fun r _ => ?_) (fun r _ => ?_) (integrable_const C) ?_
      · exact (hf.measurable.comp (hZ _)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun ω => by simpa using hC _ (Set.mem_univ _)
      · filter_upwards [hZc] with ω hω
        exact hf.comp_continuousOn hω
    refine h0.congr fun r _ => ?_
    exact b15c3_selectedLaw_integral P Z hZ (fun _ => b15c_fisherIntegrand invβ U ζ) (fun _ => hf) r
  exact (ENNReal.continuous_ofReal.comp_continuousOn hcon).lowerSemicontinuousOn

/-- **Measurability of `r ↦ 𝓘_U(P^r)` on `[0,T]`** (`AEMeasurable` for `volume.restrict (Icc 0 T)`, which is
the measure of every `∫⁻ r in Icc 0 t` with `t ≤ T`).  Proved from `b15b_fisherInfoGen_lowerSemicontinuousOn`. -/
theorem b15b_fisherInfoGen_aemeasurable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (invβ : ℝ) {U : Config d N → ℝ}
    (hcont : ∀ ζ, IsFisherTestField ζ → Continuous (b15c_fisherIntegrand invβ U ζ))
    {Z : ℝ≥0 → Ω → Config d N} (hZ : ∀ s, Measurable (Z s)) {T : ℝ}
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun r : ℝ => Z (Real.toNNReal r) ω) (Set.Icc 0 T)) :
    AEMeasurable (fun r : ℝ => b15_fisherInfoGen invβ U (selectedLaw P Z r))
      (volume.restrict (Set.Icc 0 T)) := by
  have hl := b15b_fisherInfoGen_lowerSemicontinuousOn invβ hcont hZ hZc
  rw [aemeasurable_restrict_iff_comap_subtype measurableSet_Icc]
  refine Measurable.aemeasurable ?_
  refine LowerSemicontinuous.measurable ?_
  exact lowerSemicontinuous_restrict_iff.mpr hl

/-- **Measurability (3) of the plan**: for a strong solution `X` and `V ∈ C²`,
`r ↦ fisherInfo D N (selectedLaw P X r)` is a.e.-measurable on `[0,T]`, so the `∫⁻ r in Icc 0 t, fisherInfo …`
of `b15_EntropyLawConcl` is the integral of a measurable function.  From
`b15b_fisherInfoGen_aemeasurable`, `b15b_hcont`, `IsStrongSolution.adapted/cont`. -/
theorem b15b_measurable_fisherInfo {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hS : IsStrongSolution P D T X₀ W X) :
    AEMeasurable (fun r : ℝ => fisherInfo D N (selectedLaw P X r)) (volume.restrict (Set.Icc 0 T)) := by
  refine b15b_fisherInfoGen_aemeasurable (P := P) D.invβ (U := totalPotential (N := N) D)
    (fun ζ hζ => b15b_hcont D hV hζ) hS.adapted ?_
  filter_upwards [hS.cont] with ω hω
  have h1 : Continuous fun t : ℝ≥0 => X t ω := continuous_pi hω
  exact (h1.comp continuous_real_toNNReal).continuousOn

/-- The same for the regularised processes `X^{ε_n}` and the potentials `U^{ε_n}` (needed for Fatou in
`b15b_fisher_lintegral_liminf`). -/
theorem b15b_measurable_fisherInfoGen_reg {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsCk 2 D.V) (M : ℝ) {T : ℝ}
    {Y₀ : Ω → Fin N → Euc d} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D)
      Y₀ (fun _ => ⊤) Y) :
    AEMeasurable (fun r : ℝ => b15_fisherInfoGen D.invβ (b15c_potentialReg D M)
      (selectedLaw P (b15c_regProcess Y) r)) (volume.restrict (Set.Icc 0 T)) := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [Set.Icc_eq_empty (not_le.mpr hT), Measure.restrict_empty]
    exact aemeasurable_zero_measure
  refine b15b_fisherInfoGen_aemeasurable (P := P) D.invβ (U := b15c_potentialReg (N := N) D M)
    (fun ζ hζ => b15b_fisherIntegrand_continuous _ (b15b_potentialReg_c1 D hV M) hζ)
    (fun s => b15c_regProcess_measurable hY s) ?_
  exact Filter.Eventually.of_forall fun ω =>
    b15c3_regProcess_contOn Y ω (hY.cont ω T hT (WithTop.coe_lt_top T))

/-- **Step 4, Fisher lower bound** (TeX L12205-12218, `B:eq:selected-fisher-lsc-bound`):
`∫_0^t 𝓘_G(P_N^r) dr ≤ liminf_n ∫_0^t 𝓘_{G_{N,ε_n}}(P^r_{N,ε_n}) dr`, `t ∈ [0,T]`, with
`𝓘_G = fisherInfo D N` and `𝓘_{G_ε} = b15_fisherInfoGen D.invβ U^ε`.  Proof: for each `r ∈ [0,T]`,
`b15b_fisherInfoGen_liminf_le` (weak convergence of the `r`-marginals `b15c_marginal_tendsto`,
`b15c_fisherIntegrand_eventuallyEq`, `b15b_hcont`); then Fatou (`lintegral_liminf_le'`) using
`b15b_measurable_fisherInfoGen_reg`. -/
theorem b15b_fisher_lintegral_liminf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hS : IsStrongSolution P D T X₀ W X)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) {Y₀ : Ω → Fin N → Euc d}
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) ≤
      liminf (fun n => ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ
        (b15c_potentialReg D (M n)) (selectedLaw P (b15c_regProcess (Y n)) r)) atTop := by
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) ≤
      liminf (fun n => b15_fisherInfoGen D.invβ (b15c_potentialReg D (M n))
        (selectedLaw P (b15c_regProcess (Y n)) r)) atTop := by
    intro r hr
    refine b15b_fisherInfoGen_liminf_le D.invβ (U := totalPotential (N := N) D)
      (fun ζ hζ => b15b_hcont D hV hζ) (fun ζ hζ => ?_)
      (fun φ hφ => b15c_marginal_tendsto hS hY hev hr.1 (hr.2.trans htT) hφ)
    obtain ⟨M₀, hM₀⟩ := b15c_fisherIntegrand_eventuallyEq D hζ
    filter_upwards [hM.eventually (eventually_ge_atTop M₀)] with n hn
    exact funext (hM₀ (M n) hn)
  calc ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r)
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, liminf (fun n => b15_fisherInfoGen D.invβ
          (b15c_potentialReg D (M n)) (selectedLaw P (b15c_regProcess (Y n)) r)) atTop :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ ≤ _ := by
        refine lintegral_liminf_le' fun n => ?_
        exact (b15b_measurable_fisherInfoGen_reg hV (M n) (T := T) (hY n)).mono_measure
          (Measure.restrict_mono (Set.Icc_subset_Icc_right htT) le_rfl)

/-! ## Part 3: the passage to the limit in the regularised entropy inequality -/

/-- **Step 4, entropy at time `t`** for the selected law (TeX L12195-12204, `B:eq:selected-entropy-lsc`):
`𝓗_G(P_N^t) ≤ liminf_n 𝓗_{G_{N,ε_n}}(P^t_{N,ε_n})`, `t ∈ [0,T]`.  `b15b_gibbsEntropy_liminf_le` with
`P_n = selectedLaw P (b15c_regProcess (Y n)) t` (`b15b_selectedLaw_isProb`) converging by
`b15c_marginal_tendsto`. -/
theorem b15b_gibbsEntropy_selectedLaw_liminf_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hS : IsStrongSolution P D T X₀ W X)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {Y₀ : Ω → Fin N → Euc d}
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    gibbsEntropy D (selectedLaw P X t) ≤
      liminf (fun n => b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D (M n))
        (selectedLaw P (b15c_regProcess (Y n)) t)) atTop := by
  haveI : IsProbabilityMeasure (selectedLaw P X t) := b15b_selectedLaw_isProb hS.adapted t
  haveI : ∀ n, IsProbabilityMeasure (selectedLaw P (b15c_regProcess (Y n)) t) := fun n =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable (hY n) s) t
  exact b15b_gibbsEntropy_liminf_le D hβ hV hM hM0
    (fun φ hφ => b15c_marginal_tendsto hS hY hev ht0 htT hφ)

/-- **Step 4, assembly** (TeX L12219-12222, "we may pass to the lower limit in
`B:eq:selected-regularized-entropy`; this proves `B:eq:selected-gradient-entropy`"): if for every `n` the
regularised entropy inequality holds at time `t`, with right-hand side `K` independent of `n`
(`K = 𝓗_G(P_N^0)`; in the TeX `𝓗_{G_ε}(f^0) ≤ 𝓗_G(f^0)` is `b15c_gibbsEntropyGen_le`, which packet E/D3
combines with the dissipation identity to produce `hreg`), then the same inequality holds in the limit,
in exactly the form of `b15_EntropyLawConcl`: `gibbsEntropy D (P^t) + invβ · ∫⁻_{[0,t]} fisherInfo D N (P^r) ≤ K`
in `EReal`.  Proof: `b15b_gibbsEntropy_selectedLaw_liminf_le`, `b15b_fisher_lintegral_liminf`, monotonicity
of `ENNReal.ofReal invβ * ·` and of the coercion to `EReal` through `liminf`, `EReal.le_liminf_add`, and
`liminf ≤ limsup ≤ K`.  SPEC (M). -/
theorem b15b_step4_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hS : IsStrongSolution P D T X₀ W X)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {Y₀ : Ω → Fin N → Euc d}
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {K : EReal}
    (hreg : ∀ n, b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D (M n))
        (selectedLaw P (b15c_regProcess (Y n)) t)
      + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ
          (b15c_potentialReg D (M n)) (selectedLaw P (b15c_regProcess (Y n)) r) : ℝ≥0∞) : EReal) ≤ K) :
    gibbsEntropy D (selectedLaw P X t)
      + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
      ≤ K := by
  have hc := b15b_gibbsEntropy_selectedLaw_liminf_le hβ hV hS hM hM0 hY hev ht0 htT
  have hf := b15b_fisher_lintegral_liminf hV hS hM hY hev ht0 htT
  have hmono : Monotone (fun x : ℝ≥0∞ => ((ENNReal.ofReal D.invβ * x : ℝ≥0∞) : EReal)) :=
    fun x y h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (by gcongr)
  have hcont : Continuous (fun x : ℝ≥0∞ => ((ENNReal.ofReal D.invβ * x : ℝ≥0∞) : EReal)) :=
    continuous_coe_ennreal_ereal.comp (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top)
  have hb : ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r)
      : ℝ≥0∞) : EReal) ≤ liminf (fun n => ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t,
        b15_fisherInfoGen D.invβ (b15c_potentialReg D (M n))
          (selectedLaw P (b15c_regProcess (Y n)) r) : ℝ≥0∞) : EReal)) atTop := by
    refine (hmono hf).trans ?_
    exact (hmono.map_liminf_of_continuousAt (F := atTop) (fun n => ∫⁻ r in Set.Icc (0 : ℝ) t,
      b15_fisherInfoGen D.invβ (b15c_potentialReg D (M n))
        (selectedLaw P (b15c_regProcess (Y n)) r)) hcont.continuousAt).le
  refine (add_le_add hc hb).trans ((EReal.le_liminf_add (f := atTop)).trans ?_)
  exact liminf_le_of_frequently_le' (Frequently.of_forall hreg)

end HRS
