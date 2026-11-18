import HRS.MS.MovSchTie
import HRS.MS.Mov63Tie
import HRS.MS.MovThermAux2
import HRS.MS.WrEnt
import HRS.MS.WrPress
import HRS.MS.PrepBnd
import HRS.MS.PrepStatAux2
import HRS.MS.MfeConfAux4
import HRS.MS.Mov63BAux4

/-!
# S6.6 `mov_entropy` (HRS/Whole/MovingDyn.lean:119): per-row plan and packet P1/P2 (part 1)

Worker S66, 2026-10-24.  Namespace `HRS.MS.MovEnt`, helper prefix `s66_`.  Full plan: `MovEntPlan` below (see
the plan in this file).  TeX: S L4552-4578 (statement), L4580-4737 (proof).

## Verdict on the frozen statement

TRUE as frozen and non-vacuous modulo inhabitation of `MovParticleSetup` and `GibbsEntropyContraction` (Q47, hypotheses of the
statement); nothing frozen is touched.  Junk-value audit: `P.map (X t)` is fine (`adapted`), `P.map X₀` is AE-measurable (`init`);
`relEntropy` = `klDiv` of probability laws (`modulatedGibbs` is a probability law as `K ∈ (0,∞)`: `GibbsWellDefined` from S3.1 for
`ρ_t ≤ M`, `d ≥ 2`, log moment at `s = 0`); clause (1) has right side `ofReal C * (H₀ + ofReal(Nδ_N))`, which is `⊤` when `H₀ = ⊤`
(`C ≥ 1`); the Bochner integrals inside `rieszModulatedEnergy` are the source integrals (`GibbsWellDefined`); expectations are
`lintegral`s of `ofReal` (only upper bounds by measurable majorants are proved; the window supremum is a.s. a supremum over rationals by
path continuity); `C₀ ≥ 1` makes `o_N > 0` and `δ_N ≤ C o_N`; `d ≥ 2`, `N ≥ 2`; `Real.log` only of `ρ_t > 0`; no `tsum`.

## Does S6.6 need the S.B.1 dissipation inequality?  YES; and the S.B.1 CONCLUSION does not replace it.

Clause (1) (arbitrary initial law, moving reference `Q_t`) is not a consequence of the static `GibbsEntropyContraction` (take
`f_t = ℙ_{N,β}`: `H(ℙ|Q_t) ~ N ε²`, not `≤ C N δ_N`), and the S.B.1 conclusion `𝖤_N(t)+o_N ≤ e^{C∫K}(𝖤_N(0)+o_N)` carries
`N o_N ≫ N δ_N`.  What is needed is the integrated dissipation inequality (DISS, `HRS.MS.MfeConf.MfeDiss`), the whole-space
`mov_mfe_ineq` (S.B.1 Layer 1, 18-26k lines, not in the repository): with it `H(f|Q) = βN𝖤_N + log K` (split identity),
`𝖤_N(t) ≤ 𝖤_N(0) - ½∬Comm`, `Comm = 2F^{h_u}` and the pair entropy inequality of S3.1 for `h_u/L` give the TeX differential inequality
`H' ≤ C L(t)(H + Nδ_N)` and Grönwall (`movspec_gronwall_var`).  So the clause (1) (hence the whole row) is conditional on `SuperDiss d s`
(the same hypothesis as `sb1_super_of_diss`; a future proof of (DISS) closes both rows).

## Packets (stop rule 7,000 lines)

P1 clause 0 (completion constant); P2 uniform class data from S6.3/S6.4; P3 split identity and the pressure/pair-entropy consequences
(F-bound, product bound, `E e_N ≤ C o_N`, second moment); P4 clause (2) from `hH : H(f_t|Q_t) ≤ ofReal(C N δ_N)`; P5 clause (3): Itô for
`|X|²/N`, BDG/Doob on the window; P6 clause (1) from `SuperDiss d s` (`WholeMFEHyp`, finite Gibbs entropy, Grönwall); P7 assembly
`mov_entropy_of_diss` (frozen type + the hypothesis `SuperDiss d s`).  Status lines are appended to this docstring as the packets land.

Merged inputs: `HRS.MS.MovSch.mov_schwartz_proof` (S6.4, contains S6.3), `MovNonlinearConclusion.exists_unique`, `mv0_hgauss`,
`mv0_rho_eq`, `mv0_gapref` (thermal data), `euclidean_pressure_proof`, `euclidean_pair_entropy_proof/_self_proof`,
`euclidean_preparations_bounds_proof`, `wr9_dv_abs`, `HRS.dv_lintegral`, `s32_commN_eq`, `s32_comm_isBounded`, `sb1_core` (template),
`completionNonnegRd_exists`, `oNΛ_le_oN`, `ito_formula_additive`, `bdg_two`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

/-! ### P2a: the thermal reference `ρ₀` -/

/-- Facts about the thermal equilibrium `ρ₀`: probability density, strictly positive, Gaussian upper bound. -/
theorem s66_rho0_facts (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρ₀ : Euc d → ℝ} (h : Whole.IsThermalEquilibrium d s q β ρ₀) :
    Whole.IsProbDensity ρ₀ ∧ (∀ x, 0 < ρ₀ x) ∧
      ∃ Cg c : ℝ, 0 < c ∧ ∀ x, ρ₀ x ≤ Cg * Real.exp (-c * ‖x‖ ^ 2) := by
  refine ⟨h.2.1, ?_, ?_⟩
  · obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ h
    exact hR.pos
  · obtain ⟨-, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd hs0 hsd hq hβ h
    obtain ⟨C, c, hc, hC⟩ := hg 0
    refine ⟨C, c, hc, fun x => ?_⟩
    have := hC x
    rw [norm_iteratedFDeriv_zero] at this
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)

/-! ### P2b: uniform data of the S6.3 trajectories -/

/-- The uniform data used by all pressure arguments: along `t ≥ 0` the densities are probability densities bounded by `M`
(`≤ M`, with the log moment `L` at `s = 0`) and have a uniform Gaussian exponential moment `E` at rate `c₁ > 0` (lintegral form). -/
structure S66Fam (d : ℕ) (s : ℝ) (ρ : ℝ → Euc d → ℝ) (M L E c₁ : ℝ) : Prop where
  prob : ∀ t : ℝ, 0 ≤ t → Whole.IsProbDensity (ρ t)
  bound : ∀ t : ℝ, 0 ≤ t → ∀ x, ρ t x ≤ M
  logm : ∀ t : ℝ, 0 ≤ t → s = 0 → HasLogMoment (wd (ρ t)) L
  expm : ∀ t : ℝ, 0 ≤ t →
    ∫⁻ x, ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ∂(wd (ρ t)) ≤ ENNReal.ofReal E

/-- Every solution of the small class is the S6.3 solution: positivity, ratio and decay transfer to it. -/
theorem s66_class_props {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ c C₁ : ℝ}
    (h : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) {f0 : Euc d → ℝ}
    (hf0 : MovInitialClass ρ₀ j m εstar f0) {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) (hc₀ : 0 ≤ c₀) :
    ∀ t : ℝ, 0 ≤ t → Whole.IsProbDensity (ρ t) ∧ (∀ x, 0 < ρ t x) ∧
      (∀ x, C₁⁻¹ * ρ₀ x ≤ ρ t x ∧ ρ t x ≤ C₁ * ρ₀ x) ∧
      MovDecayBounds d s q β ρ₀ j m c C₁ εstar ρ := by
  obtain ⟨ρ', -, hprob, hratio, hdec, -, -, huniq⟩ := h f0 hf0
  have heq : ∀ t : ℝ, 0 ≤ t → ρ t = ρ' t := fun t ht => huniq ρ (hρ.mono_rate hc₀) t ht
  intro t ht
  rw [heq t ht]
  refine ⟨(hprob t ht).1, (hprob t ht).2, hratio t ht, ?_⟩
  intro τ hτ
  have e := heq τ hτ
  have := hdec τ hτ
  unfold movV at this ⊢
  rw [e]
  exact this

/-- `∫ exp(-b ‖x‖²)` is finite in `ℝ`-integrable form. -/
theorem s66_gauss_int (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Euc d => Real.exp (-b * ‖x‖ ^ 2)) :=
  HRS.MS.Mov63.mnb_gauss_int hd hb

/-- Elementary: `log(2+r) ≤ A + e^{c r²}` with `A = 2 + 1/(4c)`. -/
theorem s66_log_le {c : ℝ} (hc : 0 < c) (r : ℝ) (hr : 0 ≤ r) :
    Real.log (2 + r) ≤ (2 + 1 / (4 * c)) + Real.exp (c * r ^ 2) := by
  have h1 : Real.log (2 + r) ≤ 2 + r - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h2 : r ≤ 1 / (4 * c) + c * r ^ 2 := by
    have : 0 ≤ c * (r - 1 / (2 * c)) ^ 2 := by positivity
    have e : c * (r - 1 / (2 * c)) ^ 2 = c * r ^ 2 - r + 1 / (4 * c) := by
      field_simp
      ring
    linarith
  have h3 : c * r ^ 2 + 1 ≤ Real.exp (c * r ^ 2) := Real.add_one_le_exp _
  linarith

theorem s66_fam_exists (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρ₀ : Euc d → ℝ} (hρ₀ : Whole.IsThermalEquilibrium d s q β ρ₀) {j m : ℕ} {εstar r c₀ c C₁ : ℝ}
    (hC₁ : 0 < C₁) (hc₀ : 0 ≤ c₀) (h : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) :
    ∃ M L E c₁ : ℝ, 1 ≤ M ∧ 0 < c₁ ∧ 0 ≤ E ∧ ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
      ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → S66Fam d s ρ M L E c₁ := by
  obtain ⟨hp0, hpos0, Cg, cg, hcg, hgauss⟩ := s66_rho0_facts hd hs0 hsd hq hβ hρ₀
  have hd1 : 1 ≤ d := by omega
  have hCg : 0 < Cg := by
    have h1 := hgauss 0
    have := hpos0 0
    simp at h1
    linarith
  set c₁ : ℝ := cg / 2 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set Ig : ℝ := ∫ x : Euc d, Real.exp (-c₁ * ‖x‖ ^ 2) with hIg
  have hIgi : Integrable (fun x : Euc d => Real.exp (-c₁ * ‖x‖ ^ 2)) := s66_gauss_int hd1 hc₁0
  have hIg0 : 0 ≤ Ig := integral_nonneg fun x => (Real.exp_pos _).le
  set E : ℝ := C₁ * Cg * Ig with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨max 1 (C₁ * Cg), (2 + 1 / (4 * c₁)) + E, E, c₁, le_max_left _ _, hc₁0, hE0, ?_⟩
  intro f0 hf0 ρ hρ
  have hprops := s66_class_props h hf0 hρ hc₀
  -- pointwise Gaussian bound for ρ t
  have hG : ∀ t : ℝ, 0 ≤ t → ∀ x, ρ t x ≤ C₁ * Cg * Real.exp (-cg * ‖x‖ ^ 2) := by
    intro t ht x
    have h1 := (hprops t ht).2.2.1 x
    calc ρ t x ≤ C₁ * ρ₀ x := h1.2
      _ ≤ C₁ * (Cg * Real.exp (-cg * ‖x‖ ^ 2)) := mul_le_mul_of_nonneg_left (hgauss x) hC₁.le
      _ = C₁ * Cg * Real.exp (-cg * ‖x‖ ^ 2) := by ring
  have hexp : ∀ t : ℝ, 0 ≤ t →
      ∫⁻ x, ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ∂(wd (ρ t)) ≤ ENNReal.ofReal E := by
    intro t ht
    have hpd := (hprops t ht).1
    have hmeas : Measurable fun x : Euc d => Real.exp (c₁ * ‖x‖ ^ 2) := by fun_prop
    unfold Whole.withDensityReal
    rw [lintegral_withDensity_eq_lintegral_mul (volume : Measure (Euc d))
      (f := fun x => ENNReal.ofReal (ρ t x)) (g := fun x => ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)))
      (ENNReal.measurable_ofReal.comp hpd.measurable) (ENNReal.measurable_ofReal.comp hmeas)]
    have hpt : ∀ x : Euc d, ENNReal.ofReal (ρ t x) * ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ≤
        ENNReal.ofReal (C₁ * Cg * Real.exp (-c₁ * ‖x‖ ^ 2)) := by
      intro x
      rw [← ENNReal.ofReal_mul (hpd.nonneg x)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hG t ht x
      have h2 : Real.exp (c₁ * ‖x‖ ^ 2) * (C₁ * Cg * Real.exp (-cg * ‖x‖ ^ 2)) =
          C₁ * Cg * Real.exp (-c₁ * ‖x‖ ^ 2) := by
        have : Real.exp (c₁ * ‖x‖ ^ 2) * Real.exp (-cg * ‖x‖ ^ 2) = Real.exp (-c₁ * ‖x‖ ^ 2) := by
          rw [← Real.exp_add]; congr 1; rw [hc₁]; ring
        calc _ = C₁ * Cg * (Real.exp (c₁ * ‖x‖ ^ 2) * Real.exp (-cg * ‖x‖ ^ 2)) := by ring
          _ = _ := by rw [this]
      calc ρ t x * Real.exp (c₁ * ‖x‖ ^ 2) = Real.exp (c₁ * ‖x‖ ^ 2) * ρ t x := mul_comm _ _
        _ ≤ Real.exp (c₁ * ‖x‖ ^ 2) * (C₁ * Cg * Real.exp (-cg * ‖x‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = _ := h2
    refine (lintegral_mono hpt).trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal ((hIgi.const_mul (C₁ * Cg))) (ae_of_all _ fun x => by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [integral_const_mul]
  refine ⟨fun t ht => (hprops t ht).1, fun t ht x => ?_, fun t ht hs => ?_, hexp⟩
  · calc ρ t x ≤ C₁ * Cg * Real.exp (-cg * ‖x‖ ^ 2) := hG t ht x
      _ ≤ C₁ * Cg * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Real.exp_le_one_iff]
          nlinarith [sq_nonneg ‖x‖]
      _ ≤ max 1 (C₁ * Cg) := by rw [mul_one]; exact le_max_right _ _
  · -- the logarithmic moment
    haveI : IsProbabilityMeasure (wd (ρ t)) := HRS.MS.Thm.cb_withDensityReal_isProb (hprops t ht).1
    have hmeas : Measurable fun x : Euc d => Real.exp (c₁ * ‖x‖ ^ 2) := by fun_prop
    have hfin : ∫⁻ x, ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ∂(wd (ρ t)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hexp t ht)
    have hint : Integrable (fun x : Euc d => Real.exp (c₁ * ‖x‖ ^ 2)) (wd (ρ t)) :=
      (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
        (ae_of_all _ fun x => (Real.exp_pos _).le)).1 hfin
    have hI : ∫ x, Real.exp (c₁ * ‖x‖ ^ 2) ∂(wd (ρ t)) ≤ E := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (Real.exp_pos _).le)
        hmeas.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hE0 (hexp t ht)
    have hlogm : Measurable fun x : Euc d => Real.log (2 + ‖x‖) := by fun_prop
    have hdom : ∀ x : Euc d, |Real.log (2 + ‖x‖)| ≤ (2 + 1 / (4 * c₁)) + Real.exp (c₁ * ‖x‖ ^ 2) := by
      intro x
      have h0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
      rw [abs_of_nonneg h0]
      exact s66_log_le hc₁0 ‖x‖ (norm_nonneg x)
    have hli : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (wd (ρ t)) := by
      refine Integrable.mono' ((integrable_const ((2 + 1 / (4 * c₁) : ℝ))).add hint) hlogm.aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs]
      exact hdom x
    refine ⟨hli, ?_⟩
    calc ∫ x, Real.log (2 + ‖x‖) ∂(wd (ρ t)) ≤
          ∫ x, ((2 + 1 / (4 * c₁)) + Real.exp (c₁ * ‖x‖ ^ 2)) ∂(wd (ρ t)) :=
          integral_mono hli ((integrable_const ((2 + 1 / (4 * c₁) : ℝ))).add hint)
            fun x => (le_abs_self _).trans (hdom x)
      _ = (2 + 1 / (4 * c₁)) + ∫ x, Real.exp (c₁ * ‖x‖ ^ 2) ∂(wd (ρ t)) := by
          rw [integral_add (integrable_const ((2 + 1 / (4 * c₁) : ℝ))) hint]
          simp
      _ ≤ (2 + 1 / (4 * c₁)) + E := by linarith

end HRS.MS.MovEnt

end
