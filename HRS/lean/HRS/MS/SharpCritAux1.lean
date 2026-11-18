import HRS.MS.SharpBias
import HRS.MS.WrStatic
import HRS.MS.ThmSpec
import HRS.MS.WrEntAux2

/-!
# HRS.MS.SharpCritAux1 -- S7.8 `sharp_threshold_critical` / `sharp_threshold_supercritical`: scoping report and thermal inputs

Packet S78, namespace `HRS.Whole.S78`, helper prefix `s78_`.  Frozen statements: `HRS/Whole/Bias.lean`
(`sharp_threshold_critical`, `sharp_threshold_supercritical`), TeX S L6011-6065 (`S:cor:sharp-threshold`).

## Scoping report (read first)

Common data.  `ρβ` is any `IsThermalEquilibrium d s a β ρβ`.  It equals `thermalDensity d s a β` *pointwise*
(`s78_eq_thermalDensity`: minimisers are a.e. unique by `thermalDensity_spec_proof`, and the thermal equation, which
depends on `ρ` only through `withDensityReal ρ`, then pins down the values), so every merged result about
`thermalDensity` applies.  `ρβ` is a bounded Lipschitz probability density (`sharp_bias_quadratic_proof`) and strictly
positive (`s78_thermal_pos`).  `canonicalGibbs = modulatedGibbs (thermalMeasure)` (same theorem).

Conjunct `0 < V_ρ` (both theorems; TeX S L5981-5984).  `convolution_susceptibility` (S7.3, proved in `Bias.lean`)
gives `V_ρ ≥ ‖P_μ ρ‖²/(1+βM_g)`; `P_μ ρ ≠ 0` because a strictly positive probability density is not a.e. constant
on `ℝ^d` (infinite volume): `s78_scoreVariance_pos`.  `responseInverse` is a choice function, so the two choices
`responseInverse (P_μρ)` and `responseInverse ρ` are identified through the a.e. uniqueness clause.

Conjunct `IsProbabilityMeasure (canonicalGibbs …)` for `N ≥ 1` (critical): `s71_gwd` (`GibbsWellDefined` for all
`N ≥ 1`) plus `wr9_gibbs_prob`: `s78_isProb`.

Supercritical `L²` bound (TeX S L6048-6055), for `2d/3 < s < d` (so `d/2 < s`, `p = d/s < 3/2`):
`‖N^{p-1}(μ_N(ρ)-μ(ρ)) - 2Aβ^pV‖_{L²} ≤ N^{p-1}√Var μ_N(ρ) + N^{p-1}|m_N(ρ)-μ(ρ)-δ_N b(ρ)|`.
* variance: `euc_static_proof` (S3.3, conjunct 2, `N ≥ 2`, `βm = βp = β`, `M` a density bound);
* bias: `sharp_bias_quadratic_proof` (S7.1) applied to `φ = ρ` (`ρ ∈ L²(μ)` since bounded); the coefficient
  `⟨P_μρ, R P_μρ⟩` is by definition `scoreVariance`; `N^{p-1} δ_N = 1` (`δ_N = N^{1-p}`: the frozen auxiliary
  `deltaN_eq_bias` is itself unproved in `Bias.lean`, re-proved here as `s78_deltaN_eq`; likewise `biasTheta_pos` as
  `s78_biasTheta_pos`);
* `E μ_N(ρ) = ∫ ρ dm_N` by exchangeability (`modulatedGibbs_isExchangeable`, `s78_integral_linStat`);
* `N = 1` (no variance estimate is merged for `N = 1`): the crude bound `|N^{p-1}(μ_N(ρ)-μ(ρ)) - c| ≤ M+|μ(ρ)|+|c|`.
Divergence in probability: Chebyshev from the `L²` bound, `K N^{p-3/2} → 0`.  All of this is fully proved
(`sharp_threshold_supercritical_proof` in `SharpCritTie`).

Critical CLT (`s = 2d/3`, `p = 3/2`, `√N δ_N = 1`).  The scalar limit
`√N(μ_N(ρ)-m_N(ρ)) ⇒ N(0,V_ρ)` is the one-test case of S4.5 `quadratic_static_field` (frozen, NOT proved: the
proof needs the thermal corrector S4.4, the static Stein lemma S3.7, `euc_static_commutator` and Gibbs integration by
parts with collision cutoffs on `(ℝ^d)^N`, est. 3.5-4.5k lines; this is the only missing input).  S3.5
(`r2_log_static`) is irrelevant here: `s = 2d/3 > 0` lies in the Riesz branch `0 < s < d`; the log kernel (`s = 0`)
is never used by S7.8.  Everything else in the critical statement is proved here, conditionally on S4.5, in three
steps (`SharpCritAux2`, `SharpCritTie`):
1. deterministic Slutsky shift by `√N(m_N(ρ)-μ(ρ)) → 2Aβ^{3/2}V` (`s78_bias_est`, `s78_shift`), from the scalar CLT
   `ScalarCLT` (`sharp_threshold_critical_of_clt`);
2. the scalar CLT from S4.5: feature family `φ_0 = ρ_β` (`ρ_β ∈ C_b^J` by `euc_thermal_regularity_proof`), `φ_j = 0`,
   Gaussian `N(0,V_ρ)` on the first axis of `ℓ²` (`s78_gamma`); `featureVec = s78_E ∘ (√N(μ_N(ρ)-m_N(ρ)))`
   (`s78_featureVec_eq`); the `C_b²(ℓ²)` distance bound applied to `cos(t ·)`, `sin(t ·)` (`s78_cbBall`,
   `s78_trig_dist`) gives convergence of the trigonometric moments (`δ_N → 0` since `p > 1`), and Lévy's theorem
   (`s78_weak_of_trig`) gives convergence against bounded continuous test functions
   (`s78_criticalCLT_of_static_field`);
3. `sharp_threshold_critical_of_static_field : type_of% @quadratic_static_field → type_of% @sharp_threshold_critical`.

## Statement audit (frozen statements are true and non-vacuous; no hypothesis is insufficient)
* Junk values checked: `∫` of a bounded continuous function of a measurable statistic against a probability measure
  (no non-integrable `0`); `eLpNorm`/`lintegral` are used only on measurable statistics; `gaussianReal` has variance
  `toNNReal V_ρ` with `V_ρ > 0` (non-degenerate, no Dirac junk); `canonicalGibbs` has normaliser in `(0,∞)` for
  `N ≥ 1` (`ofReal Z⁻¹` is not the junk `⊤`); `responseInverse` is not the junk `0` (a response exists);
  `Real.log` is not used (`s > 0`); `d ≥ 2`, `a, β > 0`; `biasP = d/s = 3/2` exactly at `s = 2d/3`.
* `∀ N, 1 ≤ N` in the probability clause and `∃ C ∀ N ≥ 1` in the `L²` clause hold including the small `N`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Whole.S78

open HRS.MS.Wr

variable {d : ℕ} {s : ℝ}

/-- Any `IsThermalEquilibrium` density is (pointwise) the chosen `thermalDensity`: minimisers are a.e. unique
(`thermalDensity_spec_proof`), and the thermal equation depends on `ρ` only through `withDensityReal ρ`. -/
theorem s78_eq_thermalDensity (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (h : IsThermalEquilibrium d s a β ρ) :
    ρ = thermalDensity d s a β := by
  obtain ⟨-, -, hmin⟩ := HRS.MS.Thm.thermalDensity_spec_proof hd hs0 hsd a β ha hβ
  have hae := hmin ρ h.1
  have hth := HRS.Whole.S71.s71_thermal_equilibrium hd hs0 hsd a β ha hβ
  have hμ : withDensityReal ρ = withDensityReal (thermalDensity d s a β) := by
    unfold withDensityReal
    exact withDensity_congr_ae (hae.mono fun x hx => by show ENNReal.ofReal (ρ x) = ENNReal.ofReal _; rw [hx])
  funext x
  have e1 := h.2.2 x
  have e2 := hth.2.2 x
  rw [hμ] at e1
  exact e1.trans e2.symm

/-- A thermal density is strictly positive everywhere. -/
theorem s78_thermal_pos {g V : Euc d → ℝ} {β : ℝ} {ρ : Euc d → ℝ} (h : IsThermalDensity g V β ρ)
    (x : Euc d) : 0 < ρ x := by
  have hZ : 0 < ∫ y, Real.exp (-β * (V y + convMeasure g (withDensityReal ρ) y)) := by
    have hnn : 0 ≤ ∫ y, Real.exp (-β * (V y + convMeasure g (withDensityReal ρ) y)) := by
      apply integral_nonneg
      intro y
      exact (Real.exp_pos _).le
    rcases hnn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have h0 : ρ = 0 := by
        funext y
        rw [h.2 y, ← heq]
        simp
      have := h.1.integral_one
      rw [h0] at this
      simp at this
  rw [h.2 x]
  exact div_pos (Real.exp_pos _) hZ

/-- A positive probability density is not a.e. constant. -/
theorem s78_not_ae_const (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) (hpos : ∀ x, 0 < ρ x)
    (c : ℝ) : ¬ ∀ᵐ x ∂(volume : Measure (Euc d)), ρ x = c := by
  intro hae
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hint : Integrable ρ (volume : Measure (Euc d)) :=
    Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  have hc : Integrable (fun _ : Euc d => c) (volume : Measure (Euc d)) :=
    hint.congr (hae.mono fun x hx => hx)
  rcases (integrable_const_iff.1 hc) with h0 | hfin
  · obtain ⟨x, hx⟩ := hae.exists
    have := hpos x
    rw [hx, h0] at this
    exact lt_irrefl _ this
  · have h1 := measure_univ_of_isAddLeftInvariant (volume : Measure (Euc d))
    have h2 := measure_lt_top (volume : Measure (Euc d)) Set.univ
    rw [h1] at h2
    exact absurd h2 (by simp)

/-- `V_ρ > 0` for a strictly positive bounded probability density (`S:eq:strict-nonvanishing`):
`V_ρ ≥ ‖P_μ ρ‖² / (1 + β M_g) > 0`, `P_μ ρ ≠ 0` since `ρ` is not a.e. constant. -/
theorem s78_scoreVariance_pos (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) (hpos : ∀ x, 0 < ρ x) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    0 < scoreVariance d s β ρ := by
  have hd1 : 1 ≤ d := by omega
  have := wr13a_isProb_density hρ
  have hρm : MemLp ρ 2 (withDensityReal ρ) :=
    MemLp.of_bound hρ.measurable.aestronglyMeasurable M
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]; exact hM x)
  have hρi : Integrable ρ (withDensityReal ρ) := hρm.integrable (by norm_num)
  have hf : MemL2Zero (withDensityReal ρ) (projMean (withDensityReal ρ) ρ) := by
    refine ⟨hρm.sub (memLp_const _), ?_⟩
    show ∫ x, (ρ x - pair (withDensityReal ρ) ρ) ∂(withDensityReal ρ) = 0
    rw [integral_sub hρi (integrable_const _), integral_const]
    simp [pair]
  obtain ⟨-, -, -, hmain⟩ := convolution_susceptibility hd hs hsd ρ hρ M hM β hβ
  obtain ⟨hex, huniq, hlow, -, -⟩ := hmain _ hf
  have hpf : projMean (withDensityReal ρ) (projMean (withDensityReal ρ) ρ) =
      projMean (withDensityReal ρ) ρ := by
    funext x
    have h0 : pair (withDensityReal ρ) (projMean (withDensityReal ρ) ρ) = 0 := hf.2
    simp only [projMean] at h0 ⊢
    rw [h0, sub_zero]
  have hresp : ∀ h, IsResponse (rieszKernel d s) (withDensityReal ρ) β (projMean (withDensityReal ρ) ρ) h ↔
      IsResponse (rieszKernel d s) (withDensityReal ρ) β ρ h := by
    intro h
    unfold IsResponse
    rw [hpf]
  have hexρ : ∃ h, IsResponse (rieszKernel d s) (withDensityReal ρ) β ρ h := by
    obtain ⟨h, hh⟩ := hex
    exact ⟨h, (hresp h).1 hh⟩
  have hspecf : IsResponse (rieszKernel d s) (withDensityReal ρ) β (projMean (withDensityReal ρ) ρ)
      (responseInverse (rieszKernel d s) (withDensityReal ρ) β (projMean (withDensityReal ρ) ρ)) := by
    unfold responseInverse
    rw [dif_pos hex]
    exact hex.choose_spec
  have hspecρ : IsResponse (rieszKernel d s) (withDensityReal ρ) β ρ
      (responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ) := by
    unfold responseInverse
    rw [dif_pos hexρ]
    exact hexρ.choose_spec
  have hae := huniq _ _ hspecf ((hresp _).2 hspecρ)
  have hV : scoreVariance d s β ρ = l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) ρ)
      (responseInverse (rieszKernel d s) (withDensityReal ρ) β (projMean (withDensityReal ρ) ρ)) := by
    unfold scoreVariance susceptibilityCov l2Inner
    refine integral_congr_ae (hae.mono fun x hx => ?_)
    simp only [hx]
  rw [hV]
  refine lt_of_lt_of_le ?_ hlow
  have hM0 : 0 < M := (hpos 0).trans_le (hM 0)
  have hpb : 0 < 1 + β * potentialBound d s M := by
    have h1 : 0 ≤ M * sphereArea d / ((d : ℝ) - s) := by
      have := Q34.sphereArea_nonneg hd1
      have : 0 < (d : ℝ) - s := by linarith
      positivity
    unfold potentialBound
    have : 0 < β * (M * sphereArea d / ((d : ℝ) - s) + 1) := by positivity
    linarith
  refine div_pos ?_ hpb
  -- `∫ (P_μ ρ)² dμ > 0`
  have hsqi : Integrable (fun x => (projMean (withDensityReal ρ) ρ x) ^ 2) (withDensityReal ρ) :=
    hf.1.integrable_sq
  have hnn : 0 ≤ ∫ x, (projMean (withDensityReal ρ) ρ x) ^ 2 ∂(withDensityReal ρ) := by
    apply integral_nonneg
    intro x
    exact sq_nonneg _
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have h0 := (integral_eq_zero_iff_of_nonneg (f := fun x => (projMean (withDensityReal ρ) ρ x) ^ 2) (fun x => sq_nonneg _) hsqi).1
      heq.symm
    have hm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ.measurable
    have h1 : ∀ᵐ x ∂(volume : Measure (Euc d)), ENNReal.ofReal (ρ x) ≠ 0 →
        (fun x => (projMean (withDensityReal ρ) ρ x) ^ 2) x = (0 : Euc d → ℝ) x :=
      (ae_withDensity_iff hm).1 h0
    refine s78_not_ae_const hd1 hρ hpos (pair (withDensityReal ρ) ρ) ?_
    refine h1.mono fun x hx => ?_
    have := hx (by simpa using hpos x)
    simp only [projMean, Pi.zero_apply] at this
    have h2 : ρ x - pair (withDensityReal ρ) ρ = 0 := by
      simpa using this
    linarith

end HRS.Whole.S78
