/-
# HRS.Equilibrium.L48Aux2 — Proposition 4.8, part 2: the pole first marginal against `L²(μ)` tests

For `Φ ∈ L²(μ)`, every coordinate marginal of the pole law `P_n^{x,t}` satisfies
`|E_P Φ(y_j) - μ(Φ)| ≤ C ‖Φ‖_{L²(μ)} δ_N`
(TeX proof of Lemma 4.6: "every pole first marginal differs from `μ` by `O(δ_N)` in relative `L²`";
the formal statement of Lemma 4.6 only records the uniform prefactor, which loses a logarithm).
Route: `pole_dual` (bounded tests, pole versus cavity), extended to `L²` tests by truncation
and dominated convergence (`l48_dual_extend`); cavity versus `μ`: `item2` and
`firstMarginal_density_L2`; Cauchy-Schwarz (`l48_cs`).
-/
import HRS.Equilibrium.CavityMain
import HRS.Equilibrium.L48Aux1

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L48

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

/-- Cauchy-Schwarz for real functions with `∫ f² ≤ a²`, `∫ g² ≤ b²`, `a, b > 0`. -/
theorem l48_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hf2 : ∫⁻ y, ENNReal.ofReal (f y ^ 2) ∂μ ≤ ENNReal.ofReal (a ^ 2))
    (hg2 : ∫⁻ y, ENNReal.ofReal (g y ^ 2) ∂μ ≤ ENNReal.ofReal (b ^ 2)) :
    |∫ y, f y * g y ∂μ| ≤ a * b := by
  have hfi : Integrable (fun y => f y ^ 2) μ := by
    refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hf2 ENNReal.ofReal_lt_top)
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  have hgi : Integrable (fun y => g y ^ 2) μ := by
    refine ⟨(hg.pow_const 2).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hg2 ENNReal.ofReal_lt_top)
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  have hF : ∫ y, f y ^ 2 ∂μ ≤ a ^ 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hf2
    rwa [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun y => sq_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun y => sq_nonneg _),
      ENNReal.toReal_ofReal (by positivity)] at this
  have hG : ∫ y, g y ^ 2 ∂μ ≤ b ^ 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg2
    rwa [← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun y => sq_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun y => sq_nonneg _),
      ENNReal.toReal_ofReal (by positivity)] at this
  have hfg : Integrable (fun y => f y * g y) μ := by
    have hbd : Integrable (fun y => (f y ^ 2 + g y ^ 2) / 2) μ := (hfi.add hgi).div_const 2
    refine Integrable.mono' hbd (hf.mul hg).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    show ‖f y * g y‖ ≤ (f y ^ 2 + g y ^ 2) / 2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (f y - g y), sq_nonneg (f y + g y)]
  -- `±f g ≤ (t f² + g²/t)/2` with `t = b / a`
  have key : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → σ * ∫ y, f y * g y ∂μ ≤ a * b := by
    intro σ hσ
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hpt : ∀ y, σ * (f y * g y) ≤ ((b / a) * f y ^ 2 + (a / b) * g y ^ 2) / 2 := by
      intro y
      have h1 : 0 ≤ (b / a) * (f y - σ * (a / b) * g y) ^ 2 := by positivity
      have h2 : (b / a) * (f y - σ * (a / b) * g y) ^ 2 =
          (b / a) * f y ^ 2 - 2 * σ * f y * g y + (a / b) * g y ^ 2 * σ ^ 2 := by
        field_simp; ring
      rw [hσ2] at h2
      nlinarith
    have hint : Integrable (fun y => ((b / a) * f y ^ 2 + (a / b) * g y ^ 2) / 2) μ :=
      (((hfi.const_mul _).add (hgi.const_mul _)).div_const 2)
    have h3 := integral_mono (hfg.const_mul σ) hint hpt
    rw [integral_const_mul] at h3
    rw [integral_div, integral_add (hfi.const_mul _) (hgi.const_mul _), integral_const_mul,
      integral_const_mul] at h3
    have h4 : (b / a) * ∫ y, f y ^ 2 ∂μ ≤ (b / a) * a ^ 2 :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    have h5 : (a / b) * ∫ y, g y ^ 2 ∂μ ≤ (a / b) * b ^ 2 :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    have h6 : (b / a) * a ^ 2 + (a / b) * b ^ 2 = 2 * (a * b) := by field_simp; ring
    linarith
  rw [abs_le]
  constructor
  · have := key (-1) (Or.inr rfl); linarith
  · have := key 1 (Or.inl rfl); linarith

/-- Extension of a dual (bounded-test) estimate to `L²(μ)` tests by truncation and dominated
convergence, for two measures dominated by a multiple of `μ`. -/
theorem l48_dual_extend {α : Type*} [MeasurableSpace α] {μ ν₁ ν₂ : Measure α} {M₁ M₂ : ℝ}
    (h1 : ν₁ ≤ ENNReal.ofReal M₁ • μ) (h2 : ν₂ ≤ ENNReal.ofReal M₂ • μ) {Bd : ℝ} (hBd : 0 ≤ Bd)
    (hdual : ∀ f : α → ℝ, Measurable f → ∀ K : ℝ, (∀ y, |f y| ≤ K) →
      |∫ y, f y ∂ν₁ - ∫ y, f y ∂ν₂| ≤ Bd * Real.sqrt (∫ y, f y ^ 2 ∂μ))
    {Φ : α → ℝ} (hΦ : Measurable Φ) (hΦ1 : Integrable Φ μ)
    (hΦ2 : Integrable (fun y => Φ y ^ 2) μ) :
    |∫ y, Φ y ∂ν₁ - ∫ y, Φ y ∂ν₂| ≤ Bd * Real.sqrt (∫ y, Φ y ^ 2 ∂μ) := by
  set Φn : ℕ → α → ℝ := fun n y => max (-(n : ℝ)) (min (Φ y) n) with hΦn
  have hΦnm : ∀ n, Measurable (Φn n) := fun n =>
    measurable_const.max (hΦ.min measurable_const)
  have hΦnb : ∀ n y, |Φn n y| ≤ n := fun n y => by
    rw [abs_le]
    simp only [hΦn]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_right _ _)
  have hΦna : ∀ n y, |Φn n y| ≤ |Φ y| := fun n y => by
    simp only [hΦn]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h0 := abs_nonneg (Φ y)
    rw [abs_le]
    constructor
    · exact le_trans (le_min (neg_abs_le _) (by linarith)) (le_max_right _ _)
    · exact max_le (by linarith) ((min_le_left _ _).trans (le_abs_self _))
  have hlim : ∀ y, Tendsto (fun n : ℕ => Φn n y) atTop (𝓝 (Φ y)) := by
    intro y
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈|Φ y|⌉₊) fun n hn => ?_
    have hn' : |Φ y| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have := abs_le.1 hn'
    simp only [hΦn]
    rw [min_eq_left this.2, max_eq_right this.1]
  have hint : ∀ (ν : Measure α) (M : ℝ), ν ≤ ENNReal.ofReal M • μ → Integrable Φ ν := fun ν M hν =>
    (hΦ1.smul_measure ENNReal.ofReal_ne_top).mono_measure hν
  have hconv : ∀ (ν : Measure α) (M : ℝ), ν ≤ ENNReal.ofReal M • μ →
      Tendsto (fun n : ℕ => ∫ y, Φn n y ∂ν) atTop (𝓝 (∫ y, Φ y ∂ν)) := fun ν M hν => by
    refine tendsto_integral_of_dominated_convergence (fun y => |Φ y|)
      (fun n => (hΦnm n).aestronglyMeasurable) (hint ν M hν).abs ?_
      (Eventually.of_forall hlim)
    exact fun n => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hΦna n y
  have hseq : ∀ n : ℕ, |∫ y, Φn n y ∂ν₁ - ∫ y, Φn n y ∂ν₂| ≤
      Bd * Real.sqrt (∫ y, Φ y ^ 2 ∂μ) := by
    intro n
    refine (hdual (Φn n) (hΦnm n) n (hΦnb n)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hBd
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) hΦ2
      (Eventually.of_forall fun y => ?_)
    have := hΦna n y
    nlinarith [abs_nonneg (Φn n y), sq_abs (Φn n y), sq_abs (Φ y), abs_nonneg (Φ y)]
  exact le_of_tendsto (((hconv ν₁ M₁ h1).sub (hconv ν₂ M₂ h2)).abs)
    (Eventually.of_forall hseq)

/-- `eLpNorm f 2 μ = (∫⁻ ofReal (f²))^{1/2}`. -/
theorem l48_eLpNorm_two {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) :
    eLpNorm f 2 μ = (∫⁻ y, ENNReal.ofReal (f y ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun y => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    Real.rpow_two, sq_abs]

theorem l48_eLpNorm_le_iff {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) {b : ℝ} (hb : 0 ≤ b) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal b ↔
      ∫⁻ y, ENNReal.ofReal (f y ^ 2) ∂μ ≤ ENNReal.ofReal (b ^ 2) := by
  rw [l48_eLpNorm_two hf]
  constructor
  · intro h
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    rw [← ENNReal.rpow_mul] at h2
    norm_num at h2
    rw [ENNReal.ofReal_pow hb]
    exact h2
  · intro h
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg b) (by norm_num)] at h2
    refine h2.trans (le_of_eq ?_)
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hb]

section Marg

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem l48_sqrt_log_le {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt (Real.log N) / N ≤ deltaN d s N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNd := N_mul_deltaN_crit (d := d) hcrit (by omega : 1 ≤ N)
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hδ : deltaN d s N = (1 + Real.log N) / N := by
    rw [eq_div_iff hN0.ne', mul_comm]; exact hNd
  rw [hδ]
  refine div_le_div_of_nonneg_right ?_ hN0.le
  nlinarith [Real.sq_sqrt hL, Real.sqrt_nonneg (Real.log N), sq_nonneg (Real.sqrt (Real.log N) - 1 / 2)]

/-- The cavity first marginal is `δ_N`-close to `μ` in `L²(μ)` (relative density). -/
theorem l48_cavity_marg_L2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      firstMarginal (critCavity d s c β ρ N) ≪ withDensityReal ρ ∧
      eLpNorm (fun y => ((firstMarginal (critCavity d s c β ρ N)).rnDeriv
          (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
        ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C2, hC2, h2⟩ := CavResp.item2 hd hcrit hβ hρ (c := c)
  obtain ⟨C1, h1⟩ := firstMarginal_density_L2 hd hs0 hsd β hβ ρ hρ
  have hμ := isProbabilityMeasure_mu hρ
  refine ⟨|C1| + C2, by positivity, fun N hN => ?_⟩
  obtain ⟨hm1, ha1, hb1⟩ := h2 N hN
  obtain ⟨-, hc1⟩ := h1 N hN
  refine ⟨ha1, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδ0 : 0 ≤ deltaN d s N := by
    have := l48_sqrt_log_le hd hcrit hβ hρ hc hN
    exact (div_nonneg (Real.sqrt_nonneg _) hN0.le).trans this
  set pm : Torus d → ℝ := fun y => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
    (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal with hpm
  set pν : Torus d → ℝ := fun y => ((firstMarginal (critCavity d s c β ρ N)).rnDeriv
    (withDensityReal ρ) y).toReal with hpν
  have hpmm : Measurable pm := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpνm : Measurable pν := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have e1 : (fun y => pν y - 1) = (fun y => pν y - pm y) + (fun y => pm y - 1) := by
    funext y; simp
  have e2 : eLpNorm (fun y => pν y - pm y) 2 (withDensityReal ρ) =
      eLpNorm (fun y => pm y - pν y) 2 (withDensityReal ρ) := by
    have := eLpNorm_sub_comm (f := fun y => pm y) (g := fun y => pν y) (p := 2) (μ := withDensityReal ρ)
    exact this.symm ▸ rfl
  have h3 : eLpNorm (fun y => pν y - 1) 2 (withDensityReal ρ) ≤
      eLpNorm (fun y => pν y - pm y) 2 (withDensityReal ρ) +
        eLpNorm (fun y => pm y - 1) 2 (withDensityReal ρ) := by
    rw [e1]
    exact eLpNorm_add_le (by norm_num)
  refine h3.trans ?_
  rw [e2]
  have hb2 : eLpNorm (fun y => pm y - pν y) 2 (withDensityReal ρ) ≤ ENNReal.ofReal (C2 * deltaN d s N) :=
    hb1.trans (ENNReal.ofReal_le_ofReal (by
      have := l48_sqrt_log_le hd hcrit hβ hρ hc hN
      calc C2 * Real.sqrt (Real.log N) / N = C2 * (Real.sqrt (Real.log N) / N) := by ring
        _ ≤ C2 * deltaN d s N := mul_le_mul_of_nonneg_left this hC2))
  have hc2 : eLpNorm (fun y => pm y - 1) 2 (withDensityReal ρ) ≤ ENNReal.ofReal (|C1| * deltaN d s N) :=
    hc1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0))
  calc _ ≤ ENNReal.ofReal (C2 * deltaN d s N) + ENNReal.ofReal (|C1| * deltaN d s N) := add_le_add hb2 hc2
    _ = ENNReal.ofReal ((|C1| + C2) * deltaN d s N) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hC2 hδ0) (mul_nonneg (abs_nonneg _) hδ0)]
        congr 1; ring

/-- Every coordinate marginal of the pole law differs from `μ` by `O(δ_N)` against an `L²(μ)` test
(`|E_P Φ(y_j) - μ(Φ)| ≤ C ‖Φ‖₂ δ_N`). -/
theorem l48_mean_shift :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j : Fin (N - 1),
      ∀ Φ : Torus d → ℝ, Measurable Φ → ∀ K : ℝ, 0 < K →
        ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) ≤ ENNReal.ofReal K →
        |∫ Y, Φ (Y j) ∂(critPole d s c β ρ N x t) - ∫ y, Φ y ∂(withDensityReal ρ)| ≤
          C * Real.sqrt K * deltaN d s N := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cd, hCd0, hCd⟩ := pole_dual hd hs0 hsd hβ hρ
  obtain ⟨M1, hM1, hM⟩ := pole_marg_le hd hs0 hsd hβ hρ
  obtain ⟨Mc, hMc, hMcav⟩ := cavity_marginal_le hd hs0 hsd hβ hρ
  obtain ⟨Cm, hCm0, hCm⟩ := l48_cavity_marg_L2 hd hcrit hβ hρ hc
  refine ⟨Cd + Cm + 1, by positivity, fun N hN x t ht j Φ hΦ K hK hKint => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  have hδinv : (N : ℝ)⁻¹ ≤ deltaN d s N := inv_le_deltaN (d := d) hs0 N (by omega)
  have hδ0 : 0 < deltaN d s N := lt_of_lt_of_le (inv_pos.2 hN0) hδinv
  have hsδ : Real.sqrt (deltaN d s N / (N : ℝ)) ≤ deltaN d s N := by
    rw [Real.sqrt_le_left hδ0.le]
    have : deltaN d s N / (N : ℝ) ≤ deltaN d s N ^ 2 := by
      rw [div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_left hδinv hδ0.le
    exact this
  have hPeq : critPole d s c β ρ N x t =
      poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t :=
    critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t
  haveI hPprob := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  have hexch := MarginalAux.poleLaw_exchangeable hd hs0 hsd β hρ (N - 1) (β / N) hlam x t
  have hνt : (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
      (fun Y : Config d (N - 1) => Y j) =
      firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) := by
    have : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
          (fun Y : Config d (N - 1) => Y ⟨0, hn1⟩) := by
      unfold firstMarginal; rw [dif_pos hn1]
    rw [this]
    exact hexch.marginal_eq j ⟨0, hn1⟩
  have hstep1 : ∫ Y, Φ (Y j) ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
      ∫ y, Φ y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) := by
    rw [← hνt, integral_map (measurable_pi_apply j).aemeasurable hΦ.aestronglyMeasurable]
  rw [hPeq, hstep1]
  have hνt_le : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
      ENNReal.ofReal M1 • withDensityReal ρ := by
    rw [← hνt]; exact ((hM N hN x t ht).2 j)
  have hν0_le : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) ≤
      ENNReal.ofReal Mc • withDensityReal ρ := by
    have : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) =
        (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map
          (fun Y : Config d (N - 1) => Y ⟨0, hn1⟩) := by
      unfold firstMarginal; rw [dif_pos hn1]
    rw [this]
    exact hMcav N hN ⟨0, hn1⟩
  -- integrability of `Φ`, `Φ²`
  have hΦ2i : Integrable (fun y => Φ y ^ 2) (withDensityReal ρ) := by
    refine ⟨(hΦ.pow_const 2).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hKint ENNReal.ofReal_lt_top)
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  have hΦ1i : Integrable Φ (withDensityReal ρ) := by
    have hmem : MemLp Φ 2 (withDensityReal ρ) :=
      (memLp_two_iff_integrable_sq hΦ.aestronglyMeasurable).2 hΦ2i
    exact hmem.integrable (by norm_num)
  have hΦK : ∫ y, Φ y ^ 2 ∂(withDensityReal ρ) ≤ K := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKint
    rwa [← ofReal_integral_eq_lintegral_ofReal hΦ2i (Eventually.of_forall fun y => sq_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun y => sq_nonneg _),
      ENNReal.toReal_ofReal hK.le] at this
  -- Step 2: pole versus cavity
  have hdual : ∀ f : Torus d → ℝ, Measurable f → ∀ K' : ℝ, (∀ y, |f y| ≤ K') →
      |∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
        ∫ y, f y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β))| ≤
        (Cd * Real.sqrt (deltaN d s N / N)) * Real.sqrt (∫ y, f y ^ 2 ∂(withDensityReal ρ)) := by
    intro f hf K' hfb
    have := hCd N hN x t ht f hf K' hfb
    calc _ ≤ Cd * Real.sqrt (∫ y, f y ^ 2 ∂(withDensityReal ρ)) * Real.sqrt (deltaN d s N / N) := this
      _ = _ := by ring
  have h2 := l48_dual_extend hνt_le hν0_le (by positivity) hdual hΦ hΦ1i hΦ2i
  have h2' : |∫ y, Φ y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
      ∫ y, Φ y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β))| ≤
      Cd * deltaN d s N * Real.sqrt K := by
    refine h2.trans ?_
    have h5 : Real.sqrt (∫ y, Φ y ^ 2 ∂(withDensityReal ρ)) ≤ Real.sqrt K := Real.sqrt_le_sqrt hΦK
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsδ hCd0) h5 (Real.sqrt_nonneg _) (by positivity)
  -- Step 3: cavity versus `μ`
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam
  haveI hν0 := isProb_firstMarginal hn1
    (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)
  obtain ⟨hac0, hL2⟩ := hCm N hN
  rw [critCavity_eq hd hs0 hsd c β hρ N] at hac0 hL2
  set q0 : Torus d → ℝ := fun y => ((firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ)
    (N - 1) (β / N) β)).rnDeriv (withDensityReal ρ) y).toReal with hq0
  have hq0m : Measurable q0 := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hΦν0 : Integrable Φ (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) :=
    (hΦ1i.smul_measure ENNReal.ofReal_ne_top).mono_measure hν0_le
  have hq0Φ : Integrable (fun y => q0 y * Φ y) (withDensityReal ρ) :=
    (integrable_rnDeriv_smul_iff hac0).2 hΦν0
  have e1 : ∫ y, Φ y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) =
      ∫ y, q0 y * Φ y ∂(withDensityReal ρ) := by
    have := (integral_rnDeriv_smul (f := Φ) hac0).symm
    simpa [hq0, smul_eq_mul] using this
  have hdiff : ∫ y, Φ y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) -
      ∫ y, Φ y ∂(withDensityReal ρ) = ∫ y, (q0 y - 1) * Φ y ∂(withDensityReal ρ) := by
    rw [e1, ← integral_sub hq0Φ hΦ1i]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [sub_mul, one_mul]
  have hfm : Measurable (fun y => q0 y - 1) := hq0m.sub measurable_const
  have hδd : 0 ≤ Cm * deltaN d s N := mul_nonneg hCm0 hδ0.le
  have hL2' : ∫⁻ y, ENNReal.ofReal ((q0 y - 1) ^ 2) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (((Cm + 1) * deltaN d s N) ^ 2) := by
    refine ((l48_eLpNorm_le_iff hfm hδd).1 hL2).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_nonneg hCm0 hδ0.le, hδ0]
  have hgK : ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Real.sqrt K ^ 2) := by
    rw [Real.sq_sqrt hK.le]; exact hKint
  have hcs := l48_cs hfm hΦ (a := (Cm + 1) * deltaN d s N) (b := Real.sqrt K)
    (by positivity) (Real.sqrt_pos.2 hK) hL2' hgK
  have hsplit : ∫ y, Φ y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
      ∫ y, Φ y ∂(withDensityReal ρ) =
      (∫ y, Φ y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
        ∫ y, Φ y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β))) +
      (∫ y, Φ y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) -
        ∫ y, Φ y ∂(withDensityReal ρ)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [hdiff]
  have hK0 := Real.sqrt_nonneg K
  calc _ ≤ Cd * deltaN d s N * Real.sqrt K + (Cm + 1) * deltaN d s N * Real.sqrt K := add_le_add h2' hcs
    _ = (Cd + Cm + 1) * Real.sqrt K * deltaN d s N := by ring

end Marg

end L48

end HRS

end
