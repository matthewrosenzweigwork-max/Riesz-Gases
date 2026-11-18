import HRS.Equilibrium.PairMomentsL2
import HRS.Equilibrium.PairMomentsCrude
import HRS.ME.NfUPU1b
import HRS.ME.NfUPU1bB
import HRS.ME.NfUPU1aB

/-!
# Packet PU9, part A (uniform second-level bounds `l2_integrals`, `level2_bound`, `level2_crude`)

Uniform copies (namespace `HRS.ME.NfU`) of the following lemmas (rule for uniform statements in
`docs/MAIN_E_NF_PLAN.md`, conventions as in `NfUPU8.lean`).  Fixed data: `d, s, βm, βp, c₀, Λ₀` with
`0 < βm`, `βm ≤ βp`, `1 ≤ Λ₀`, and the setting parameters of the original statement (`c`, `Mmax M'max γmax Cq`).
The constant is chosen before `β ∈ Set.Icc βm βp` and before `ρ`; the thermal hypothesis is
`RhoU d βm βp c₀ Λ₀ β ρ`, whose `hup` replaces `exists_density_bound`.

* `l2_integrals_unif` of `HRS.PairMom.l2_integrals` (PairMomentsL2 l.35).  Uses `critical_envelope_integrals_unif`,
  `pole_w_integrals_unif`, `lintegral_wEll_exp_unif`; `lintegral_mu_w`, `lintegral_mu_wEll` are already uniform in `ρ`.
  The prefactors `exp (M'max + β max(γmax,0) + Mmax)` and `exp (… + β Cq)` are bounded by their values at `βp`.
* `level2_bound_unif` of `HRS.PairMom.level2_bound` (PairMomentsL2 l.280).  Uses `l2_integrals_unif`; the
  constant `8 (6 E₂ (2C²+C) + C) + C²` is taken with `E₂` at `βp`; the β-dependent `E₂` of the proof is bounded by it.
  Hypotheses mentioning `β` (`weakKappa V β ≤ 1/2`, the two-pin mean bound) stay after `V`.
* `level2_crude_unif` of `HRS.PairMom.level2_crude` (PairMomentsCrude l.100).  Uses `l2_integrals_unif`; constant
  `3 E₂ (2C²+C)` with `E₂` at `βp`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.External HRS.Quad HRS.External.PoleVar HRS.PairMom HRS.PairCorrAux HRS.PoleCavityAux
  HRS.ME.PmU

variable {d : ℕ}

section L2IntU

set_option maxHeartbeats 1000000 in
/-- Uniform `l2_integrals`: the constant `B1 + C0 + E0 Λ₀ (B + Cl) + Ep Cw + E0 B1²` is chosen after the fixed
data; `E0, Ep` are the pole prefactors at `βp`. Uniform in `β ∈ Icc βm βp` and `ρ` (`RhoU`). -/
theorem l2_integrals_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      (∀ y : Torus d, ∫⁻ z, ENNReal.ofReal (aFun s c (β / N) y z) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C * logEN N)) ∧
      (∫⁻ u, ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N)) ∧
      (∫⁻ u, ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N)) ∧
      (∫⁻ u, ENNReal.ofReal (wEnv s x u ^ 2 * (logEN N + ellEnv x u) ^ 2) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N ^ 3)) ∧
      (∫⁻ u, Jfun s c (β / N) (withDensityReal ρ) x u * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N ^ 2)) := by
  obtain ⟨C1, hC1⟩ := critical_envelope_integrals_unif hd hcrit c hc βm βp c₀ Λ₀ hβm hββ hΛ 1 one_pos
  obtain ⟨C0, hC00, hC0⟩ := pole_w_integrals_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  obtain ⟨Cw, hCw, hCwF⟩ := lintegral_wEll_exp_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc
  obtain ⟨B, hB0, hB⟩ := lintegral_mu_w hd hcrit
  obtain ⟨Cl, hCl0, hCl⟩ := lintegral_mu_wEll hd hcrit
  have hΛ0 : 0 < Λ₀ := by linarith
  set E0 : ℝ := Real.exp (M'max + βp * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set Ep : ℝ := Real.exp (M'max + βp * max γmax 0 + Mmax + βp * Cq) with hEp
  have hEpp : 0 < Ep := Real.exp_pos _
  set B1 : ℝ := max C1 0 with hB1
  have hB10 : 0 ≤ B1 := le_max_right _ _
  set C : ℝ := B1 + C0 + E0 * Λ₀ * (B + Cl) + Ep * Cw + E0 * B1 ^ 2 with hC
  have hC0' : 0 ≤ C := by positivity
  refine ⟨C, hC0', fun β hβI ρ hU V hV N hN x => ?_⟩
  have hβ : 0 < β := hU.hβpos
  have hβle : β ≤ βp := hU.hβle
  have hρ : SmoothPosDensity ρ := hU.rho
  have hΛρ : ∀ x, ρ x ≤ Λ₀ := hU.hup
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLe := logEN_pos' (N := N) (by omega)
  have hL0 : 0 ≤ logEN N := by linarith
  have hlam0 : 0 ≤ β / N := by positivity
  have hlamβ : β / N ≤ β := by
    rw [div_le_iff₀ hNp]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hE0le : Real.exp (M'max + β * max γmax 0 + Mmax) ≤ E0 := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hβle (le_max_right γmax 0)
    linarith
  have hEpLe : Real.exp (M'max + β * max γmax 0 + Mmax + β * Cq) ≤ Ep := by
    apply Real.exp_le_exp.2
    have h1 := mul_le_mul_of_nonneg_right hβle (le_max_right γmax 0)
    have h2 := mul_le_mul_of_nonneg_right hβle hCq
    linarith
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hI : ∀ y : Torus d, ∫⁻ z, ENNReal.ofReal (aFun s c (β / N) y z) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (B1 * logEN N) := by
    intro y
    have h := ((hC1 β hβI ρ hU N hN).1 y).1
    simp only [one_mul] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0))
  have hCL : B1 * logEN N ≤ C * logEN N := by
    refine mul_le_mul_of_nonneg_right ?_ hL0
    have : 0 ≤ C0 + E0 * Λ₀ * (B + Cl) + Ep * Cw + E0 * B1 ^ 2 := by positivity
    linarith
  refine ⟨fun y => (hI y).trans (ENNReal.ofReal_le_ofReal hCL), ?_, ?_, ?_, ?_⟩
  · refine ((hC0 β hβI ρ hU V hV N hN x).1).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_right ?_ hL0
    have : 0 ≤ B1 + E0 * Λ₀ * (B + Cl) + Ep * Cw + E0 * B1 ^ 2 := by positivity
    linarith
  · -- w (L + ℓ) against the pole weight
    have hmw1 : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u) :=
      ENNReal.measurable_ofReal.comp (PairCorrAux.measurable_wEnv s x)
    have e1 : ∀ u : Torus d, ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) =
        ENNReal.ofReal (logEN N) * ENNReal.ofReal (wEnv s x u) + ENNReal.ofReal (wEnv s x u * ellEnv x u) := by
      intro u
      have h1 := PairCorrAux.one_le_wEnv s x u
      have h2 := one_le_ellEnv x u
      rw [← ENNReal.ofReal_mul hL0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    calc _ ≤ ∫⁻ u, ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) * ENNReal.ofReal E0 ∂(withDensityReal ρ) := by
          refine lintegral_mono fun u => mul_le_mul' le_rfl ?_
          exact (poleW_le_const (V := V) hV hβ.le hlam0 (pinsWith (fun e : Empty => e.elim) x) u).trans
            (ENNReal.ofReal_le_ofReal hE0le)
      _ = (ENNReal.ofReal (logEN N) * ∫⁻ u, ENNReal.ofReal (wEnv s x u) ∂(withDensityReal ρ) +
            ∫⁻ u, ENNReal.ofReal (wEnv s x u * ellEnv x u) ∂(withDensityReal ρ)) * ENNReal.ofReal E0 := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          congr 1
          simp_rw [e1]
          rw [lintegral_add_left (hmw1.const_mul _), lintegral_const_mul _ hmw1]
      _ ≤ (ENNReal.ofReal (logEN N) * ENNReal.ofReal (Λ₀ * B) + ENNReal.ofReal (Λ₀ * Cl)) * ENNReal.ofReal E0 := by
          gcongr
          · exact hB hΛρ hΛ0.le x
          · exact hCl hΛρ hΛ0.le x
      _ = ENNReal.ofReal ((logEN N * (Λ₀ * B) + Λ₀ * Cl) * E0) := by
          rw [← ENNReal.ofReal_mul hL0, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (logEN N * (Λ₀ * B) + Λ₀ * Cl) * E0 ≤ (E0 * Λ₀ * (B + Cl)) * logEN N := by
            have : 0 ≤ Λ₀ * Cl * E0 := by positivity
            nlinarith [mul_nonneg (mul_nonneg hE0p.le hΛ0.le) hCl0, mul_nonneg (mul_nonneg hE0p.le hΛ0.le) hB0]
          have h2 : 0 ≤ B1 + C0 + Ep * Cw + E0 * B1 ^ 2 := by positivity
          nlinarith
  · -- w² (L+ℓ)² against the pole weight
    refine (lintegral_pole_le hV hβ.le hlam0 hlamβ hCq (x := x) (hatom) _).trans ?_
    refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hEpLe) le_rfl) ?_
    have h := hCwF β hβI ρ hU N hN x
    calc ENNReal.ofReal Ep * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * (logEN N + ellEnv x y) ^ 2) *
          ENNReal.ofReal (Real.exp (-(β / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal Ep * ENNReal.ofReal (Cw * logEN N ^ 3) := by
          gcongr
          refine le_trans (le_of_eq ?_) h
          refine lintegral_congr fun y => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (Ep * (Cw * logEN N ^ 3)) := (ENNReal.ofReal_mul hEpp.le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h3 : 0 ≤ logEN N ^ 3 := by positivity
          have h2 : 0 ≤ B1 + C0 + E0 * Λ₀ * (B + Cl) + E0 * B1 ^ 2 := by positivity
          nlinarith [mul_nonneg h2 h3]
  · -- the J term
    have hJ := lintegral_Jfun_le (μ := withDensityReal ρ) hd hcrit c (β / N) x (mul_nonneg hB10 hL0) hI
    calc _ ≤ ∫⁻ u, Jfun s c (β / N) (withDensityReal ρ) x u * ENNReal.ofReal E0 ∂(withDensityReal ρ) := by
          refine lintegral_mono fun u => mul_le_mul' le_rfl ?_
          exact (poleW_le_const (V := V) hV hβ.le hlam0 (pinsWith (fun e : Empty => e.elim) x) u).trans
            (ENNReal.ofReal_le_ofReal hE0le)
      _ = (∫⁻ u, Jfun s c (β / N) (withDensityReal ρ) x u ∂(withDensityReal ρ)) * ENNReal.ofReal E0 :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ (ENNReal.ofReal (B1 * logEN N) * ENNReal.ofReal (B1 * logEN N)) * ENNReal.ofReal E0 := by gcongr
      _ = ENNReal.ofReal ((B1 * logEN N) * (B1 * logEN N) * E0) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h3 : 0 ≤ logEN N ^ 2 := by positivity
          have h2 : 0 ≤ B1 + C0 + E0 * Λ₀ * (B + Cl) + Ep * Cw := by positivity
          have : (B1 * logEN N) * (B1 * logEN N) * E0 = (E0 * B1 ^ 2) * logEN N ^ 2 := by ring
          rw [this]
          nlinarith [mul_nonneg h2 h3]

end L2IntU

section L2BoundU

set_option maxHeartbeats 1000000 in
/-- Uniform `level2_bound`: the constant `8 (6 E₂ (2C²+C) + C) + C²`, `E₂` the prefactor at `βp`, is chosen
after the fixed data; uniform in `β ∈ Icc βm βp` and `ρ`. The potential, the pinned mean hypothesis and
`weakKappa V β ≤ 1/2` stay as hypotheses after `V`. -/
theorem level2_bound_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ m : ℕ, 1 ≤ m → weakKappa V β ≤ 1 / 2 →
      ∀ (K A : ℝ), 0 ≤ A → ∀ (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      IsSymmTriple g3 →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) →
      (∀ x u : Torus d, x ≠ u →
        |∑ k : Fin m, ∫ z, g3 x u z ∂((pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) m
          (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤
          A * (wEnv s x u * (logEN (m + 2) + ellEnv x u))) →
      ∀ x : Torus d,
        ∫⁻ Y, ‖pairSumOrdered (g3 x) Y‖ₑ ^ 2
            ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤
          ENNReal.ofReal (C * (K ^ 2 + A ^ 2) * ((m + 2 : ℕ) : ℝ) ^ 2 * logEN (m + 2) ^ 2) := by
  obtain ⟨C, hC0, hCI⟩ := l2_integrals_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  set E2p : ℝ := Real.exp (M'max + βp * max γmax 0 + Mmax + 2 * (βp * Cq)) with hE2p
  have hE2pp : 0 < E2p := Real.exp_pos _
  refine ⟨8 * (6 * E2p * (2 * C ^ 2 + C) + C) + C ^ 2, by positivity,
    fun β hβI ρ hU V hV m hm1 hκ K A hA g3 hgm hsym hg3 hMean x => ?_⟩
  have hβ : 0 < β := hU.hβpos
  have hβle : β ≤ βp := hU.hβle
  have hρ : SmoothPosDensity ρ := hU.rho
  set E2 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax + 2 * (β * Cq)) with hE2
  have hE2p' : 0 < E2 := Real.exp_pos _
  have hE2le : E2 ≤ E2p := by
    apply Real.exp_le_exp.2
    have h1 := mul_le_mul_of_nonneg_right hβle (le_max_right γmax 0)
    have h2 := mul_le_mul_of_nonneg_right hβle hCq
    linarith
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  set N : ℕ := m + 2 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI : NeZero m := ⟨by omega⟩
  have hLe := logEN_pos' (N := N) (by omega)
  have hL0 : 0 ≤ logEN N := by linarith
  have hLN := logEN_le_N (N := N) (by omega)
  have hlam0 : 0 ≤ β / N := by positivity
  have hlamβ : β / N ≤ β := by
    rw [div_le_iff₀ hNp]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  obtain ⟨hI, hw2, hwl, hw2l, hJ⟩ := hCI β hβI ρ hU V hV N hN2 x
  set h : Torus d → Torus d → ℝ := fun y z => g3 x y z with hh
  have hhm : Measurable (Function.uncurry h) :=
    Measurable.comp (g := fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) hgm
      (f := fun p : Torus d × Torus d => (x, p.1, p.2)) (measurable_const.prodMk measurable_id)
  have hhsym : ∀ y z, h y z = h z y := fun y z => (hsym x y z).2
  have hμ' : IsProbabilityMeasure (pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) :=
    isProb_pinnedLaw V hlam0 (m + 1) _
  have hcard : m + 1 + Fintype.card (Option Empty) ≤ N := by simp [hNdef]
  have hcardB : m + 1 + Fintype.card (Option Empty) ≤ N := hcard
  have hpm : Measurable (pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x)) :=
    (isField_pinField V hlam0 _).measurable
  have hPm : Measurable fun u : Torus d => ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.add hpm))
  have hw2m : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u ^ 2) :=
    ENNReal.measurable_ofReal.comp ((PairCorrAux.measurable_wEnv s x).pow_const 2)
  set 𝒱 : Torus d → ℝ≥0∞ := fun u => ENNReal.ofReal (3 * K ^ 2 * E2) *
    (ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (2 * (C * logEN N)) +
      Jfun s c (β / N) (withDensityReal ρ) x u) with h𝒱
  set 𝓜 : Torus d → ℝ := fun u => A * (wEnv s x u * (logEN N + ellEnv x u)) with h𝓜
  have h𝒱m : Measurable 𝒱 :=
    ((hw2m.mul_const _).add (measurable_Jfun hd hcrit c (β / N) x)).const_mul _
  have h𝓜m : Measurable 𝓜 := measurable_const.mul (measurable_wEll x)
  have h𝓜0 : ∀ u, 0 ≤ 𝓜 u := fun u =>
    mul_nonneg hA (mul_nonneg (by linarith [PairCorrAux.one_le_wEnv s x u]) (by linarith [one_le_ellEnv x u]))
  have hae : ∀ᵐ u ∂(withDensityReal ρ), u ≠ x := HRS.External.PoleVar.ae_ne_pt hatom x
  have hrowV : ∀ᵐ u ∂(withDensityReal ρ), ∫⁻ z, ‖h u z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z)) ∂(withDensityReal ρ) ≤ 𝒱 u := by
    filter_upwards [hae] with u hu
    have hxu : x ≠ u := Ne.symm hu
    refine (var2_bound hd hcrit hV hβ.le hlam0 hlamβ hCq hatom hc K hg3 hxu).trans ?_
    refine mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl ?_) le_rfl)
    calc _ ≤ ENNReal.ofReal (C * logEN N) + ENNReal.ofReal (C * logEN N) := add_le_add (hI x) (hI u)
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hrowM : ∀ᵐ u ∂(withDensityReal ρ), |∑ k : Fin m, ∫ z, h u z ∂((pinnedLaw V (β / N) m
      (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤ 𝓜 u := by
    filter_upwards [hae] with u hu
    exact hMean x u (Ne.symm hu)
  have hrow : ∀ i : Fin (m + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)‖ₑ ^ 2
      ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤
      ∫⁻ u, pinWeight V (β / N) (pinsWith (fun e : Empty => e.elim) x) m u *
        (ENNReal.ofReal (2 * m) * 𝒱 u + ENNReal.ofReal ((𝓜 u) ^ 2)) ∂(withDensityReal ρ) :=
    fun i => row_moment_pins_le V hβ.le (by omega) hcard _ hκ hhm i hrowV hrowM
  have hΨm : Measurable fun u => ENNReal.ofReal (2 * m) * 𝒱 u + ENNReal.ofReal ((𝓜 u) ^ 2) :=
    (h𝒱m.const_mul _).add (ENNReal.measurable_ofReal.comp (h𝓜m.pow_const 2))
  set Ξb : ℝ := 6 * m * K ^ 2 * E2 * (2 * C ^ 2 + C) * logEN N ^ 2 + A ^ 2 * C * logEN N ^ 3 with hΞb
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hXi : ∫⁻ u, pinWeight V (β / N) (pinsWith (fun e : Empty => e.elim) x) m u *
        (ENNReal.ofReal (2 * m) * 𝒱 u + ENNReal.ofReal ((𝓜 u) ^ 2)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal Ξb := by
    refine (lintegral_pinWeight_le V hβ.le (by omega) hcard _ hΨm).trans ?_
    set P : Torus d → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) with hP
    have hpt : ∀ u : Torus d, (ENNReal.ofReal (2 * m) * 𝒱 u + ENNReal.ofReal ((𝓜 u) ^ 2)) * P u =
        ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2) * (2 * (C * logEN N))) * (ENNReal.ofReal (wEnv s x u ^ 2) * P u) +
        ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2)) * (Jfun s c (β / N) (withDensityReal ρ) x u * P u) +
        ENNReal.ofReal (A ^ 2) * (ENNReal.ofReal (wEnv s x u ^ 2 * (logEN N + ellEnv x u) ^ 2) * P u) := by
      intro u
      have e1 : ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2) * (2 * (C * logEN N))) =
          ENNReal.ofReal (2 * m) * ENNReal.ofReal (3 * K ^ 2 * E2) * ENNReal.ofReal (2 * (C * logEN N)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      have e2 : ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2)) =
          ENNReal.ofReal (2 * m) * ENNReal.ofReal (3 * K ^ 2 * E2) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      have e3 : ENNReal.ofReal ((𝓜 u) ^ 2) = ENNReal.ofReal (A ^ 2) *
          ENNReal.ofReal (wEnv s x u ^ 2 * (logEN N + ellEnv x u) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1; simp only [h𝓜]; ring
      rw [e1, e2, e3]
      simp only [h𝒱]
      ring
    refine le_trans (le_of_eq (lintegral_congr hpt)) ?_
    have hF1 : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u ^ 2) * P u := hw2m.mul hPm
    have hF2 : Measurable fun u : Torus d => Jfun s c (β / N) (withDensityReal ρ) x u * P u :=
      (measurable_Jfun hd hcrit c (β / N) x).mul hPm
    have hF3 : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u ^ 2 * (logEN N + ellEnv x u) ^ 2) * P u :=
      (ENNReal.measurable_ofReal.comp (((PairCorrAux.measurable_wEnv s x).pow_const 2).mul
        ((measurable_const.add (measurable_ellEnv_right x)).pow_const 2))).mul hPm
    have hF12 : Measurable fun u : Torus d =>
        ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2) * (2 * (C * logEN N))) * (ENNReal.ofReal (wEnv s x u ^ 2) * P u) +
        ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2)) * (Jfun s c (β / N) (withDensityReal ρ) x u * P u) :=
      (hF1.const_mul _).add (hF2.const_mul _)
    rw [lintegral_add_left hF12, lintegral_add_left (hF1.const_mul _),
      lintegral_const_mul _ hF1, lintegral_const_mul _ hF2, lintegral_const_mul _ hF3]
    calc _ ≤ ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2) * (2 * (C * logEN N))) * ENNReal.ofReal (C * logEN N) +
          ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2)) * ENNReal.ofReal (C * logEN N ^ 2) +
          ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (C * logEN N ^ 3) := by
          gcongr
      _ = ENNReal.ofReal Ξb := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          simp only [hΞb]; ring
  have hrowI : ∀ i : Fin (m + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)‖ₑ ^ 2
      ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤ ENNReal.ofReal Ξb :=
    fun i => (hrow i).trans hXi
  have hint : ∀ i : Fin (m + 1), Integrable (fun Y : Fin (m + 1) → Torus d =>
      ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j))
      (pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) := fun i =>
    integrable_of_sq_lt_top (measurable_rowSum hhm i) (lt_of_le_of_lt (hrowI i) ENNReal.ofReal_lt_top)
  set W : ℝ := A * (C * logEN N) with hWdef
  have hW0 : 0 ≤ W := by positivity
  have hmwl : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) :=
    ENNReal.measurable_ofReal.comp (measurable_wEll x)
  have hW : ∫⁻ u, ENNReal.ofReal (𝓜 u) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal W := by
    calc _ = ∫⁻ u, ENNReal.ofReal A * (ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u))) ∂(withDensityReal ρ) := by
          refine lintegral_congr fun u => ?_
          simp only [h𝓜]
          rw [ENNReal.ofReal_mul hA, mul_assoc]
      _ = ENNReal.ofReal A * ∫⁻ u, ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ) :=
          lintegral_const_mul _ (hmwl.mul hPm)
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C * logEN N) := by gcongr
      _ = ENNReal.ofReal W := (ENNReal.ofReal_mul hA).symm
  have hfπ : ∀ᵐ u ∂(withDensityReal ρ), ∀ k : Fin m, Integrable (h u) ((pinnedLaw V (β / N) m
      (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k)) := by
    filter_upwards [hae] with u hu k
    exact g3_marg_integrable hd hcrit hρ hV hβ.le (by omega) (by omega) K hgm hg3 (Ne.symm hu) k
  have hmean : ∀ i : Fin (m + 1), |∫ Y, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)
      ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x))| ≤ W := fun i =>
    abs_integral_row_le V hβ.le (by omega) hcard _ hhm i (hint i) h𝓜m h𝓜0 hfπ hrowM hW0 hW
  have hmeanT : |∫ Y, pairSumOrdered h Y ∂(pinnedLaw V (β / N) (m + 1)
      (pinsWith (fun e : Empty => e.elim) x))| ≤ ((m : ℝ) + 1) * W := by
    have e : ∫ Y, pairSumOrdered h Y ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) =
        ∑ i : Fin (m + 1), ∫ Y, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)
          ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) := by
      unfold pairSumOrdered
      exact integral_finsetSum _ fun i _ => hint i
    rw [e]
    calc _ ≤ ∑ i : Fin (m + 1), |∫ Y, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)
          ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (m + 1), W := Finset.sum_le_sum fun i _ => hmean i
      _ = ((m : ℝ) + 1) * W := by simp
  have hvar := evariance_pairSum_le_pins V hβ.le (N := N) (n := m + 1) (by omega) hcard
    (pinsWith (fun e : Empty => e.elim) x) hκ hhm hhsym 1
  simp only [one_mul] at hvar
  have hsq := lintegral_sq_le_evariance_add (measurable_pairSumOrdered hhm) hmeanT
  have hsum : ∑ i : Fin (m + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)‖ₑ ^ 2
      ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤
      ENNReal.ofReal ((m : ℝ) + 1) * ENNReal.ofReal Ξb := by
    calc _ ≤ ∑ _i : Fin (m + 1), ENNReal.ofReal Ξb := Finset.sum_le_sum fun i _ => hrowI i
      _ = ENNReal.ofReal ((m : ℝ) + 1) * ENNReal.ofReal Ξb := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          congr 1
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  have hL1 : 1 ≤ logEN N := hLe
  have hfin := real_final E2 C K A (logEN N) N m hE2p'.le hC0 hL1 hLN hmR (by simp [hNdef])
  have hmono : 8 * (6 * E2 * (2 * C ^ 2 + C) + C) + C ^ 2 ≤ 8 * (6 * E2p * (2 * C ^ 2 + C) + C) + C ^ 2 := by
    have h2C : 0 ≤ 2 * C ^ 2 + C := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hE2le h2C]
  have hprod := mul_le_mul_of_nonneg_right hmono
    (by positivity : (0 : ℝ) ≤ (K ^ 2 + A ^ 2) * (N : ℝ) ^ 2 * logEN N ^ 2)
  refine hsq.trans ?_
  refine le_trans (add_le_add (hvar.trans (mul_le_mul' le_rfl hsum)) le_rfl) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [hΞb, hWdef] at *
  nlinarith [hfin, hprod]

set_option maxHeartbeats 1000000 in
/-- Uniform `level2_crude`: the constant `3 E₂ (2C²+C)`, `E₂` the prefactor at `βp`, is chosen after the fixed
data; uniform in `β ∈ Icc βm βp` and `ρ`. -/
theorem level2_crude_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ m : ℕ, 1 ≤ m →
      ∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) →
      ∀ x : Torus d,
        ∫⁻ Y, ‖pairSumOrdered (g3 x) Y‖ₑ ^ 2
            ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤
          ENNReal.ofReal (C * K ^ 2 * ((m + 2 : ℕ) : ℝ) ^ 4 * logEN (m + 2) ^ 2) := by
  obtain ⟨C, hC0, hCI⟩ := l2_integrals_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  set E2p : ℝ := Real.exp (M'max + βp * max γmax 0 + Mmax + 2 * (βp * Cq)) with hE2p
  have hE2pp : 0 < E2p := Real.exp_pos _
  refine ⟨3 * E2p * (2 * C ^ 2 + C), by positivity,
    fun β hβI ρ hU V hV m hm1 K g3 hgm hg3 x => ?_⟩
  have hβ : 0 < β := hU.hβpos
  have hβle : β ≤ βp := hU.hβle
  have hρ : SmoothPosDensity ρ := hU.rho
  set E2 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax + 2 * (β * Cq)) with hE2
  have hE2le : E2 ≤ E2p := by
    apply Real.exp_le_exp.2
    have h1 := mul_le_mul_of_nonneg_right hβle (le_max_right γmax 0)
    have h2 := mul_le_mul_of_nonneg_right hβle hCq
    linarith
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  set N : ℕ := m + 2 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLe := logEN_pos' (N := N) (by omega)
  have hL0 : 0 ≤ logEN N := by linarith
  have hlam0 : 0 ≤ β / N := by positivity
  have hlamβ : β / N ≤ β := by
    rw [div_le_iff₀ hNp]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  obtain ⟨hI, hw2, hwl, hw2l, hJ⟩ := hCI β hβI ρ hU V hV N hN2 x
  set h : Torus d → Torus d → ℝ := fun y z => g3 x y z with hh
  have hhm : Measurable (Function.uncurry h) :=
    Measurable.comp (g := fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) hgm
      (f := fun p : Torus d × Torus d => (x, p.1, p.2)) (measurable_const.prodMk measurable_id)
  have hcard : m + 1 + Fintype.card (Option Empty) ≤ N := by simp [hNdef]
  have hpm : Measurable (pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x)) :=
    (isField_pinField V hlam0 _).measurable
  have hPm : Measurable fun u : Torus d => ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.add hpm))
  have hw2m : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u ^ 2) :=
    ENNReal.measurable_ofReal.comp ((PairCorrAux.measurable_wEnv s x).pow_const 2)
  set 𝒱 : Torus d → ℝ≥0∞ := fun u => ENNReal.ofReal (3 * K ^ 2 * E2) *
    (ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (2 * (C * logEN N)) +
      Jfun s c (β / N) (withDensityReal ρ) x u) with h𝒱
  have h𝒱m : Measurable 𝒱 :=
    ((hw2m.mul_const _).add (measurable_Jfun hd hcrit c (β / N) x)).const_mul _
  have hae : ∀ᵐ u ∂(withDensityReal ρ), u ≠ x := HRS.External.PoleVar.ae_ne_pt hatom x
  have hrowV : ∀ᵐ u ∂(withDensityReal ρ), ∫⁻ z, ‖h u z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z)) ∂(withDensityReal ρ) ≤ 𝒱 u := by
    filter_upwards [hae] with u hu
    have hxu : x ≠ u := Ne.symm hu
    refine (var2_bound hd hcrit hV hβ.le hlam0 hlamβ hCq hatom hc K hg3 hxu).trans ?_
    refine mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl ?_) le_rfl)
    calc _ ≤ ENNReal.ofReal (C * logEN N) + ENNReal.ofReal (C * logEN N) := add_le_add (hI x) (hI u)
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  set Ξb : ℝ := 3 * K ^ 2 * E2 * (2 * C ^ 2 + C) * logEN N ^ 2 with hΞb
  have hΞ : ∫⁻ u, 𝒱 u * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal Ξb := by
    set P : Torus d → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) with hP
    have hpt : ∀ u : Torus d, 𝒱 u * P u =
        ENNReal.ofReal (3 * K ^ 2 * E2 * (2 * (C * logEN N))) * (ENNReal.ofReal (wEnv s x u ^ 2) * P u) +
        ENNReal.ofReal (3 * K ^ 2 * E2) * (Jfun s c (β / N) (withDensityReal ρ) x u * P u) := by
      intro u
      have e1 : ENNReal.ofReal (3 * K ^ 2 * E2 * (2 * (C * logEN N))) =
          ENNReal.ofReal (3 * K ^ 2 * E2) * ENNReal.ofReal (2 * (C * logEN N)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      rw [e1]
      simp only [h𝒱]
      ring
    refine le_trans (le_of_eq (lintegral_congr hpt)) ?_
    have hF1 : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u ^ 2) * P u := hw2m.mul hPm
    have hF2 : Measurable fun u : Torus d => Jfun s c (β / N) (withDensityReal ρ) x u * P u :=
      (measurable_Jfun hd hcrit c (β / N) x).mul hPm
    rw [lintegral_add_left (hF1.const_mul _), lintegral_const_mul _ hF1, lintegral_const_mul _ hF2]
    calc _ ≤ ENNReal.ofReal (3 * K ^ 2 * E2 * (2 * (C * logEN N))) * ENNReal.ofReal (C * logEN N) +
          ENNReal.ofReal (3 * K ^ 2 * E2) * ENNReal.ofReal (C * logEN N ^ 2) := by
          gcongr
      _ = ENNReal.ofReal Ξb := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          simp only [hΞb]; ring
  have hmain := lintegral_pairSum_sq_le_pins V hβ.le (N := N) (n := m) (by omega) hcard
    (pinsWith (fun e : Empty => e.elim) x) hhm h𝒱m hrowV hΞ
  refine hmain.trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hm4 : (((m + 1 : ℕ) : ℝ)) ^ 4 ≤ (N : ℝ) ^ 4 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 4
    exact_mod_cast (by omega : m + 1 ≤ N)
  have h0 : 0 ≤ Ξb := by positivity
  have hΞle : Ξb ≤ 3 * K ^ 2 * E2p * (2 * C ^ 2 + C) * logEN N ^ 2 := by
    rw [hΞb]
    have h3 : 0 ≤ 3 * K ^ 2 * (2 * C ^ 2 + C) * logEN N ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hE2le h3]
  calc ((m + 1 : ℕ) : ℝ) ^ 4 * Ξb ≤ (N : ℝ) ^ 4 * (3 * K ^ 2 * E2p * (2 * C ^ 2 + C) * logEN N ^ 2) :=
        mul_le_mul hm4 hΞle h0 (by positivity)
    _ = _ := by ring

end L2BoundU

end HRS.ME.NfU

end
