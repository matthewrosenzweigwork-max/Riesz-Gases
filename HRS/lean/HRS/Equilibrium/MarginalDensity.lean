/-
# HRS.Equilibrium.MarginalDensity -- Proposition 4.2 (full-law half) (EQ-02)

Proposition 4.2 `M:A:prop:marginal`, full law: with `π_N` the first marginal of `Q_{N,β}(μ)`,
`‖dπ_N/dμ - 1‖_{L²(μ)} ≤ C δ_N` and `dπ_N/dμ → 1` uniformly.

## Route (source proof, TeX lines 3675-3760)

Write `N = n + 1`, `λ = β/N`, `P₀ = cavityLaw g μ n λ β` and `ν` its marginal.
1. `Q_{N,β}(μ) = cavityLaw g μ N λ β` (`MarginalCavity.modulatedGibbs_eq_cavity`); exact cavity equation
   (`MarginalCavity.firstMarginal_cavity_eq`): `dπ/dμ = exp(β g*μ + log Φ_x - c)`, `Φ_x = E_{P₀} e^{-λ∑g(x-y_j)}`.
2. `log Φ_x = D_N(x) - λ n ∫ g(x-y) dν`, `0 ≤ D_N ≤ C δ_N` (`MarginalPole.insDefect_le`).
3. With `p = dπ/dμ`, `q = dν/dμ`, `z = p - 1`: `log(1+z) + β g*(z μ) = D_N + e_N - c_N`,
   `e_N = β g*((p-q) μ) + λ g*(q μ)`, and `‖p - q‖_{L¹(μ)} ≤ C √(δ_N/N)` (`MarginalPole.cavity_tv`);
   the convolution estimate (`MarginalKernel.conv_L2`) gives `‖e_N‖_{L²(μ)} ≤ C δ_N`.
4. `‖π_N - μ‖_TV → 0` (`MarginalEntropy.tendsto_tvDist_Q`, coarse entropy); hence
   `‖g*((p-q)μ)‖_∞`-type smallness (`MarginalKernel.sup_conv_small`) and `‖z‖_∞ → 0` including the
   normalisation constant.
5. Absorption: test the cavity equation against `z`; `∬ z g z ≥ 0` (Fourier positivity,
   `MarginalKernel.Kt_nonneg`) and `z log(1+z) ≥ z²/(1+‖z‖_∞)` give `‖z‖₂ ≤ (1+ε)‖D_N + e_N‖₂`.
-/
import HRS.Equilibrium.MarginalPole
import HRS.Equilibrium.MarginalEntropy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace MarginalAux

variable {d : ℕ} {s : ℝ}

open HRS.External HRS.PoleCavityAux

/-! ### Uniform bounds -/

section Bounds

theorem convAbs_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) :
    ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ x : Torus d, ∫ y, |periodicRiesz d s (x - y)| ∂(withDensityReal ρ) ≤ Kg := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  refine ⟨Cc + 2 * B, ?_, fun x => ?_⟩
  · have := hK.Cc_nonneg; linarith
  have h1 : ∫ y, |periodicRiesz d s (x - y)| ∂(withDensityReal ρ) ≤
      ∫ y, (periodicRiesz d s (x - y) + 2 * B) ∂(withDensityReal ρ) := by
    refine integral_mono (hK.int x).abs ((hK.int x).add (integrable_const _)) fun y => ?_
    have := hK.lower (x - y)
    rcases le_total 0 (periodicRiesz d s (x - y)) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  rw [integral_add (hK.int x) (integrable_const _)] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  have h2 := hK.conv x
  have h3 : ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ≤ Cc := (le_abs_self _).trans h2
  linarith

theorem uIns_abs_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      |uIns (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x| ≤ Cu := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  obtain ⟨Kg, hKg0, hKg⟩ := convAbs_bound hd hs0 hsd hρ
  obtain ⟨C, hC, hmarg⟩ := cavity_marginal_le hd hs0 hsd hβ hρ
  obtain ⟨Cd, hCd⟩ := insDefect_le hd hs0 hsd hβ hρ
  obtain ⟨B', hB'0, hB'⟩ : ∃ B' : ℝ, 0 ≤ B' ∧ ∀ z : Torus d, -B' ≤ periodicRiesz d s z := rieszB hd hs0 hsd
  have hCc0 := hK.Cc_nonneg
  refine ⟨|β| * Cc + β * B' + β * (C * Kg) + |β| * Cc, by positivity, fun N hN x => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]; linarith
  haveI := cavity_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam
  set lam : ℝ := β / N with hlamdef
  set n : ℕ := N - 1 with hn
  set P0 := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β with hP0
  have hconv := hK.conv x
  have hconv' : |β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x| ≤ |β| * Cc := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hconv (abs_nonneg _)
  -- upper bound of the log
  have hphi := phiIns_pos hd hs0 hsd hρ hlam hln x
  have hup : Real.log (phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) ≤ β * B' := by
    calc _ ≤ Real.log (Real.exp (β * B')) :=
          Real.log_le_log hphi (phiIns_le_of hd hs0 hsd hρ hlam hln hB'0 hB' x)
      _ = β * B' := Real.log_exp _
  -- lower bound of the log: `D ≥ 0` and `|E S| ≤ n C Kg`
  have hD := (hCd N hN x).1
  have hS : |∫ Y, ∑ j, periodicRiesz d s (x - Y j) ∂P0| ≤ n * (C * Kg) := by
    have hint : ∀ j : Fin n, Integrable (fun Y : Config d n => periodicRiesz d s (x - Y j)) P0 :=
      fun j => integrable_coord hd hs0 hsd hβ hρ hN x j
    rw [integral_finsetSum _ fun j _ => hint j]
    calc |∑ j, ∫ Y, periodicRiesz d s (x - Y j) ∂P0| ≤ ∑ j, |∫ Y, periodicRiesz d s (x - Y j) ∂P0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, (C * Kg) := Finset.sum_le_sum fun j _ => by
          have h1 : |∫ Y, periodicRiesz d s (x - Y j) ∂P0| ≤ ∫ Y, |periodicRiesz d s (x - Y j)| ∂P0 :=
            abs_integral_le_integral_abs
          refine h1.trans ?_
          have hmeas : Measurable fun y : Torus d => |periodicRiesz d s (x - y)| :=
            (measurable_periodicRiesz hd hs0 hsd |>.comp (measurable_const.sub measurable_id)).abs
          have h2 : ∫ Y, |periodicRiesz d s (x - Y j)| ∂P0 = ∫ y, |periodicRiesz d s (x - y)| ∂(P0.map fun Y : Config d n => Y j) := by
            rw [integral_map (measurable_pi_apply j).aemeasurable hmeas.aestronglyMeasurable]
          rw [h2]
          have h3 : ∫ y, |periodicRiesz d s (x - y)| ∂(P0.map fun Y : Config d n => Y j) ≤
              ∫ y, |periodicRiesz d s (x - y)| ∂(ENNReal.ofReal C • withDensityReal ρ) :=
            integral_mono_measure (hmarg N hN j) (Filter.Eventually.of_forall fun y => abs_nonneg _)
              (((hK.int x).abs).smul_measure ENNReal.ofReal_ne_top)
          refine h3.trans ?_
          rw [integral_smul_measure, ENNReal.toReal_ofReal hC.le, smul_eq_mul]
          exact mul_le_mul_of_nonneg_left (hKg x) hC.le
      _ = n * (C * Kg) := by simp
  have hlow : -(β * (C * Kg)) ≤ Real.log (phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) := by
    have h1 : 0 ≤ Real.log (phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) +
        lam * ∫ Y, ∑ j, periodicRiesz d s (x - Y j) ∂P0 := hD
    have h2 : lam * ∫ Y, ∑ j, periodicRiesz d s (x - Y j) ∂P0 ≤ lam * (n * (C * Kg)) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans hS) hlam
    have h3 : lam * (n * (C * Kg)) ≤ β * (C * Kg) := by
      have : lam * (n * (C * Kg)) = (lam * n) * (C * Kg) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hln (by positivity)
    linarith
  unfold uIns
  rw [abs_le]
  have h4 := neg_abs_le (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x)
  have h5 := le_abs_self (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x)
  have p1 : 0 ≤ β * B' := by positivity
  have p2 : 0 ≤ β * (C * Kg) := by positivity
  have p3 : 0 ≤ |β| * Cc := by positivity
  constructor <;> linarith [hconv', hup, hlow]

end Bounds


/-! ### The densities `p = dπ_N/dμ` and `q = dν_n/dμ` -/

section Dens

/-- `p(x) = exp(u(x) - c)`, the density of the first marginal of `Q_{N,β}(μ)` (`N = n + 1`). -/
def pDens (g : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam β : ℝ) (x : Torus d) : ℝ :=
  Real.exp (uIns g μ n lam β x - Real.log (∫ y, Real.exp (uIns g μ n lam β y) ∂μ))

/-- `q = dν_n/dμ`, `ν_n` the first marginal of the cavity law. -/
def qDens (g : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam β : ℝ) (x : Torus d) : ℝ :=
  ((firstMarginal (cavityLaw g μ n lam β)).rnDeriv μ x).toReal

theorem pDens_bounds (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ Mp : ℝ, 1 ≤ Mp ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      Real.exp (-Mp) ≤ pDens (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ∧
      pDens (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ≤ Mp := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cu, hCu0, hCu⟩ := uIns_abs_le hd hs0 hsd hβ hρ
  refine ⟨Real.exp (2 * Cu), Real.one_le_exp (by positivity), fun N hN x => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]; linarith
  have hum := measurable_uIns hd hs0 hsd hρ hlam hln
  set u := uIns (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β with hu
  have hint : Integrable (fun y => Real.exp (u y)) (withDensityReal ρ) :=
    Integrable.of_bound (C := Real.exp Cu) (Real.measurable_exp.comp hum).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans (hCu N hN y)))
  have hZ1 : Real.exp (-Cu) ≤ ∫ y, Real.exp (u y) ∂(withDensityReal ρ) := by
    have := integral_mono (integrable_const (Real.exp (-Cu))) hint (fun y =>
      Real.exp_le_exp.2 (neg_le_of_abs_le (hCu N hN y)))
    simpa using this
  have hZ2 : ∫ y, Real.exp (u y) ∂(withDensityReal ρ) ≤ Real.exp Cu := by
    have := integral_mono hint (integrable_const (Real.exp Cu)) (fun y =>
      Real.exp_le_exp.2 ((le_abs_self _).trans (hCu N hN y)))
    simpa using this
  have hZpos : 0 < ∫ y, Real.exp (u y) ∂(withDensityReal ρ) := integral_exp_pos hint
  have hc1 : -Cu ≤ Real.log (∫ y, Real.exp (u y) ∂(withDensityReal ρ)) := by
    calc -Cu = Real.log (Real.exp (-Cu)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) hZ1
  have hc2 : Real.log (∫ y, Real.exp (u y) ∂(withDensityReal ρ)) ≤ Cu := by
    calc _ ≤ Real.log (Real.exp Cu) := Real.log_le_log hZpos hZ2
      _ = Cu := Real.log_exp _
  have hux := abs_le.1 (hCu N hN x)
  unfold pDens
  constructor
  · refine Real.exp_le_exp.2 ?_
    have : 2 * Cu ≤ Real.exp (2 * Cu) := by linarith [Real.add_one_le_exp (2 * Cu)]
    linarith
  · exact Real.exp_le_exp.2 (by linarith)

end Dens


section Dens2

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
  {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (hln : lam * n ≤ β)

include hd hs0 hsd hρ hlam hln

theorem measurable_pDens :
    Measurable (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
  have := measurable_uIns hd hs0 hsd hρ hlam hln
  unfold pDens
  exact Real.measurable_exp.comp (this.sub measurable_const)

theorem pDens_pos (x : Torus d) : 0 < pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x :=
  Real.exp_pos _

theorem integral_pDens :
    ∫ x, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x ∂(withDensityReal ρ) = 1 := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨M, hM0, hM⟩ := exp_uIns_le hd hs0 hsd hρ hlam hln
  have hum := measurable_uIns hd hs0 hsd hρ hlam hln
  have hint : Integrable (fun y => Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y)) (withDensityReal ρ) :=
    Integrable.of_bound (C := M) (Real.measurable_exp.comp hum).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hM y)
  have hZ := integral_exp_pos hint
  unfold pDens
  simp_rw [Real.exp_sub]
  rw [integral_div, Real.exp_log hZ, div_self hZ.ne']

theorem firstMarginal_eq_withDensity :
    firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) =
      (withDensityReal ρ).withDensity (fun x => ENNReal.ofReal
        (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x)) :=
  firstMarginal_cavity_eq hd hs0 hsd hρ hlam hln

theorem rnDeriv_pi_eq :
    ∀ᵐ x ∂(withDensityReal ρ),
      ((firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β)).rnDeriv
        (withDensityReal ρ) x).toReal = pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x := by
  have hμ := isProbabilityMeasure_mu hρ
  have hm : Measurable fun x => ENNReal.ofReal (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x) :=
    ENNReal.measurable_ofReal.comp (measurable_pDens hd hs0 hsd hρ hlam hln)
  rw [firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln]
  filter_upwards [Measure.rnDeriv_withDensity (withDensityReal ρ) hm] with x hx
  rw [hx, ENNReal.toReal_ofReal (pDens_pos hd hs0 hsd hρ hlam hln x).le]

end Dens2

section Dens3

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ)

include hd hs0 hsd hβ hρ

/-- Uniform density bound for the cavity marginal. -/
theorem qDens_bound : ∃ Mq : ℝ, 0 < Mq ∧ ∀ N : ℕ, 2 ≤ N →
    (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) ≪ withDensityReal ρ ∧
    ∀ᵐ x ∂(withDensityReal ρ),
      qDens (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ≤ Mq := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨C, hC, hmarg⟩ := cavity_marginal_le hd hs0 hsd hβ hρ
  refine ⟨C, hC, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  haveI := cavity_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam
  have hn1 : 0 < N - 1 := by omega
  have hfm : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) =
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map
        (fun Y : Config d (N - 1) => Y ⟨0, hn1⟩) := by
    unfold firstMarginal; rw [dif_pos hn1]
  have h1 := hmarg N hN ⟨0, hn1⟩
  haveI : IsProbabilityMeasure (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) := by
    rw [hfm]; infer_instance
  rw [← hfm, ← withDensity_const] at h1
  obtain ⟨hac, hle⟩ := rnDeriv_le_of_le_withDensity (withDensityReal ρ) _ _ h1
  refine ⟨hac, ?_⟩
  filter_upwards [hle] with x hx
  unfold qDens
  exact ENNReal.toReal_le_of_le_ofReal hC.le hx

end Dens3


section Cav

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlamdef : lam = β / ((n + 1 : ℕ) : ℝ))

include hd hs0 hsd hβ hρ hn hlamdef

theorem lam_facts : 0 ≤ lam ∧ lam * (n : ℝ) ≤ β ∧ lam * ((n : ℝ) + 1) = β := by
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  subst hlamdef
  refine ⟨by positivity, ?_, ?_⟩
  · push_cast
    have : β / ((n : ℝ) + 1) * (n : ℝ) = β * ((n : ℝ) / ((n : ℝ) + 1)) := by ring
    rw [this]
    have : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  · push_cast; field_simp

theorem expectation_S (hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ) (x : Torus d) :
    ∫ Y, ∑ j, periodicRiesz d s (x - Y j) ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) =
      (n : ℝ) * ∫ y, periodicRiesz d s (x - y) * qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y
        ∂(withDensityReal ρ) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hgm := measurable_periodicRiesz hd hs0 hsd
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  set P0 := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β with hP0
  set ν := firstMarginal P0 with hν
  haveI hνp : IsProbabilityMeasure ν := by
    rw [hν]; unfold firstMarginal; rw [dif_pos hn]; infer_instance
  have hN : 2 ≤ n + 1 := by omega
  have hint : ∀ j : Fin n, Integrable (fun Y : Config d n => periodicRiesz d s (x - Y j)) P0 := by
    intro j
    subst hlamdef
    exact integrable_coord hd hs0 hsd hβ hρ (N := n + 1) hN x j
  rw [integral_finsetSum _ fun j _ => hint j]
  have hmeas : Measurable fun y : Torus d => periodicRiesz d s (x - y) :=
    hgm.comp (measurable_const.sub measurable_id)
  have hj : ∀ j : Fin n, ∫ Y, periodicRiesz d s (x - Y j) ∂P0 = ∫ y, periodicRiesz d s (x - y) ∂ν := by
    intro j
    have hfm : ν = P0.map (fun Y : Config d n => Y ⟨0, hn⟩) := by
      rw [hν]; unfold firstMarginal; rw [dif_pos hn]
    rw [hfm, ← (cavityLaw_exchangeable hd hs0 hsd β hρ n lam).marginal_eq j ⟨0, hn⟩,
      integral_map (measurable_pi_apply j).aemeasurable hmeas.aestronglyMeasurable]
  simp_rw [hj]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [← integral_rnDeriv_smul hac]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, qDens]
  ring

end Cav


section Cav2

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlamdef : lam = β / ((n + 1 : ℕ) : ℝ))

include hd hs0 hsd hβ hρ hn hlamdef

theorem qDens_measurable :
    Measurable (qDens (periodicRiesz d s) (withDensityReal ρ) n lam β) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- The exact cavity equation, pointwise: `log p = β g*μ - λ n g*(qμ) + D_N - c_N`. -/
theorem cavity_eq (hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ) (x : Torus d) :
    Real.log (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x) =
      β * ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) -
        (lam * n) * ∫ y, periodicRiesz d s (x - y) *
          qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ∂(withDensityReal ρ) +
      insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x -
        Real.log (∫ y, Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y) ∂(withDensityReal ρ)) := by
  unfold pDens
  rw [Real.log_exp]
  have hE := expectation_S hd hs0 hsd hβ hρ hn hlamdef hac x
  unfold uIns insDefect
  rw [hE]
  unfold convMeasure
  ring

/-- The cavity equation in the form `log(1+z) + β g*(zμ) = e_N + D_N - c_N`. -/
theorem cavity_eq_z (hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ) {Mp Mq : ℝ}
    (hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp)
    (hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq)
    (x : Torus d) :
    Real.log (1 + (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1)) +
        β * ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ)
          (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1) x =
      (β * ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ)
          (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y -
            qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y) x +
        lam * ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ)
          (qDens (periodicRiesz d s) (withDensityReal ρ) n lam β) x) +
      insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x -
        Real.log (∫ y, Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y) ∂(withDensityReal ρ)) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  have hgi := hK.int x
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hpint : Integrable (fun y => periodicRiesz d s (x - y) *
      pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y) (withDensityReal ρ) :=
    hgi.mul_bdd hpm.aestronglyMeasurable (c := Mp) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (pDens_pos hd hs0 hsd hρ hlam hln y)]; exact hpb y)
  have hqint : Integrable (fun y => periodicRiesz d s (x - y) *
      qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y) (withDensityReal ρ) :=
    hgi.mul_bdd hqm.aestronglyMeasurable (c := Mq) (hqb.mono fun y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold qDens; exact ENNReal.toReal_nonneg)]; exact hy)
  have hac' := cavity_eq hd hs0 hsd hβ hρ hn hlamdef hac x
  unfold ResponseAux.Kt
  have e1 : ∫ y, periodicRiesz d s (x - y) * (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1)
      ∂(withDensityReal ρ) = ∫ y, periodicRiesz d s (x - y) *
        pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ∂(withDensityReal ρ) -
        ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) := by
    simp_rw [mul_sub, mul_one]
    exact integral_sub hpint hgi
  have e2 : ∫ y, periodicRiesz d s (x - y) * (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y -
        qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y) ∂(withDensityReal ρ) =
      ∫ y, periodicRiesz d s (x - y) * pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y
        ∂(withDensityReal ρ) -
        ∫ y, periodicRiesz d s (x - y) * qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y
        ∂(withDensityReal ρ) := by
    simp_rw [mul_sub]
    exact integral_sub hpint hqint
  rw [e1, e2, add_sub_cancel, hac']
  have : lam * (n : ℝ) = β - lam := by linarith
  rw [this]
  ring

/-- `u = β g*μ - λ n g*(qμ) + D_N`. -/
theorem uIns_eq (hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ) (x : Torus d) :
    uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x =
      β * ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) -
        (lam * n) * ∫ y, periodicRiesz d s (x - y) *
          qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ∂(withDensityReal ρ) +
      insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x := by
  have hE := expectation_S hd hs0 hsd hβ hρ hn hlamdef hac x
  unfold uIns insDefect
  rw [hE]
  unfold convMeasure
  ring

end Cav2


theorem toReal_withDensity_apply {μ : Measure (Torus d)} {f : Torus d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f μ) {A : Set (Torus d)} (hA : MeasurableSet A) :
    ((μ.withDensity fun x => ENNReal.ofReal (f x)) A).toReal = ∫ x in A, f x ∂μ := by
  rw [withDensity_apply _ hA, ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
    (Filter.Eventually.of_forall fun x => hf0 x), ENNReal.toReal_ofReal (integral_nonneg fun x => hf0 x)]

theorem l1_of_sets {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {p q : Torus d → ℝ}
    (hpm : Measurable p) (hqm : Measurable q) (hpi : Integrable p μ) (hqi : Integrable q μ)
    (hp1 : ∫ x, p x ∂μ = 1) (hq1 : ∫ x, q x ∂μ = 1) {ε : ℝ}
    (hTV : ∀ A : Set (Torus d), MeasurableSet A → |(∫ x in A, p x ∂μ) - ∫ x in A, q x ∂μ| ≤ ε) :
    ∫ y, |p y - q y| ∂μ ≤ 2 * ε := by
  set Aset : Set (Torus d) := {x | q x < p x} with hAset
  have hAm : MeasurableSet Aset := measurableSet_lt hqm hpm
  have h1 := hTV Aset hAm
  have hpt : ∀ y, |p y - q y| = 2 * (Aset.indicator (fun y => p y - q y) y) - (p y - q y) := by
    intro y
    by_cases hy : q y < p y
    · have : y ∈ Aset := hy
      rw [Set.indicator_of_mem this, abs_of_pos (sub_pos.2 hy)]; ring
    · have : y ∉ Aset := hy
      rw [Set.indicator_of_notMem this, abs_of_nonpos (by linarith [not_lt.1 hy])]; ring
  have hdi : Integrable (fun y => p y - q y) μ := hpi.sub hqi
  have hind : Integrable (Aset.indicator fun y => p y - q y) μ := hdi.indicator hAm
  simp_rw [hpt]
  rw [integral_sub (hind.const_mul 2) hdi, integral_const_mul, integral_indicator hAm,
    integral_sub hpi hqi, hp1, hq1]
  have h2 : ∫ y in Aset, (p y - q y) ∂μ = (∫ y in Aset, p y ∂μ) - ∫ y in Aset, q y ∂μ :=
    integral_sub hpi.integrableOn hqi.integrableOn
  rw [h2]
  have := (abs_le.1 h1).2
  linarith


section L1

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlamdef : lam = β / ((n + 1 : ℕ) : ℝ))

include hd hs0 hsd hβ hρ hn hlamdef

theorem integral_qDens (hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ) :
    Integrable (qDens (periodicRiesz d s) (withDensityReal ρ) n lam β) (withDensityReal ρ) ∧
    ∫ y, qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ∂(withDensityReal ρ) = 1 := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  haveI hνp : IsProbabilityMeasure (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)) := by
    unfold firstMarginal; rw [dif_pos hn]; infer_instance
  refine ⟨Measure.integrable_toReal_rnDeriv, ?_⟩
  have h := integral_rnDeriv_smul hac (f := fun _ : Torus d => (1 : ℝ))
  simp only [smul_eq_mul, mul_one, integral_const, probReal_univ, one_smul] at h
  exact h

theorem nu_eq_withDensity (hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ) :
    firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) =
      (withDensityReal ρ).withDensity (fun x => ENNReal.ofReal
        (qDens (periodicRiesz d s) (withDensityReal ρ) n lam β x)) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  haveI hνp : IsProbabilityMeasure (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)) := by
    unfold firstMarginal; rw [dif_pos hn]; infer_instance
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hac]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β))
    (withDensityReal ρ)] with x hx
  unfold qDens
  rw [ENNReal.ofReal_toReal hx.ne]

theorem l1_pq (hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ) {ε : ℝ}
    (hTV : ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) A).toReal -
        (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) A).toReal| ≤ ε)
    {Mp : ℝ} (hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp) :
    ∫ y, |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y -
      qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y| ∂(withDensityReal ρ) ≤ 2 * ε := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  obtain ⟨hqi, hq1⟩ := integral_qDens hd hs0 hsd hβ hρ hn hlamdef hac
  have hp1 := integral_pDens hd hs0 hsd hρ hlam hln
  have hpi : Integrable (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β) (withDensityReal ρ) :=
    Integrable.of_bound (C := Mp) hpm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (pDens_pos hd hs0 hsd hρ hlam hln y)]; exact hpb y)
  have hq0 : ∀ y, 0 ≤ qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y := fun y => ENNReal.toReal_nonneg
  have hνeq := nu_eq_withDensity hd hs0 hsd hβ hρ hn hlamdef hac
  have hπeq := firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  set Aset : Set (Torus d) := {x | q x < p x} with hAset
  have hAm : MeasurableSet Aset := measurableSet_lt hqm hpm
  have h1 := hTV Aset hAm
  rw [hπeq, hνeq, toReal_withDensity_apply (fun x => (pDens_pos hd hs0 hsd hρ hlam hln x).le) hpi hAm,
    toReal_withDensity_apply hq0 hqi hAm] at h1
  -- `|p - q| = 2 (p - q)⁺ - (p - q)`
  have hpt : ∀ y, |p y - q y| = 2 * (Aset.indicator (fun y => p y - q y) y) - (p y - q y) := by
    intro y
    by_cases hy : q y < p y
    · have : y ∈ Aset := hy
      rw [Set.indicator_of_mem this, abs_of_pos (sub_pos.2 hy)]; ring
    · have : y ∉ Aset := hy
      rw [Set.indicator_of_notMem this, abs_of_nonpos (by linarith [not_lt.1 hy])]; ring
  have hdi : Integrable (fun y => p y - q y) μ := hpi.sub hqi
  have hind : Integrable (Aset.indicator fun y => p y - q y) μ := hdi.indicator hAm
  simp_rw [hpt]
  rw [integral_sub (hind.const_mul 2) hdi, integral_const_mul, integral_indicator hAm,
    integral_sub hpi hqi, hp1, hq1]
  have h2 : ∫ y in Aset, (p y - q y) ∂μ = (∫ y in Aset, p y ∂μ) - ∫ y in Aset, q y ∂μ :=
    integral_sub hpi.integrableOn hqi.integrableOn
  rw [h2]
  have := (abs_le.1 h1).2
  linarith

end L1


theorem integral_sq_le_of_lintegral {μ : Measure (Torus d)} {h : Torus d → ℝ} (hm : Measurable h)
    {A : ℝ} (hA : 0 ≤ A) (hl : ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂μ ≤ ENNReal.ofReal A) :
    Integrable (fun x => h x ^ 2) μ ∧ ∫ x, h x ^ 2 ∂μ ≤ A := by
  have hint : Integrable (fun x => h x ^ 2) μ := by
    refine ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hl ENNReal.ofReal_lt_top)
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (hm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hA hl


section KtL2

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ)

include hd hs0 hsd hβ hρ

theorem measurable_Kt {h : Torus d → ℝ} (hm : Measurable h) :
    Measurable (ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) h) := by
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_periodicRiesz hd hs0 hsd
  unfold ResponseAux.Kt
  have : StronglyMeasurable (Function.uncurry fun (x y : Torus d) => periodicRiesz d s (x - y) * h y) :=
    ((hgm.comp (measurable_fst.sub measurable_snd)).mul (hm.comp measurable_snd)).stronglyMeasurable
  exact (this.integral_prod_right' (ν := withDensityReal ρ)).measurable

/-- `L²(μ)` bound for `g * ((p - q) μ)`. -/
theorem kt_pq_L2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      ∫⁻ x, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ)
          (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y -
            qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y) x) ^ 2) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (C * deltaN d s (n + 1)) ^ 2 := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  obtain ⟨Ctv, hCtv0, hCtv⟩ := cavity_tv hd hs0 hsd hβ hρ
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  obtain ⟨Cc, hCc0, hCc⟩ := conv_L2 hd hs0 hsd ((Mp + Mq) * Λ) (2 * Ctv) (by positivity) (by positivity)
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine ⟨Real.sqrt Λ * Cc, by positivity, fun n hn lam hlamdef => ?_⟩
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hacq := (hMq (n + 1) hN)
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪ withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hTV : ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) A).toReal -
        (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) A).toReal| ≤
        Ctv * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    intro A hA
    subst hlam'
    exact hCtv (n + 1) hN A hA
  have hl1 := l1_pq hd hs0 hsd hβ hρ hn hlamdef hac hTV hpb
  obtain ⟨hqi, hq1⟩ := integral_qDens hd hs0 hsd hβ hρ hn hlamdef hac
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
  have hqbm : Measurable qb := hqm.min measurable_const
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  have hqbq : q =ᵐ[μ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
  have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
  have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
  set f : Torus d → ℝ := fun y => ρ y * (p y - qb y) with hf
  have hρm : Measurable ρ := hρ.density.measurable
  have hfm : Measurable f := hρm.mul (hpm.sub hqbm)
  have hfb : ∀ y, |f y| ≤ (Mp + Mq) * Λ := by
    intro y
    have h1 : |p y - qb y| ≤ Mp + Mq := by
      have := pDens_pos hd hs0 hsd hρ hlam hln y
      rw [abs_le]; constructor <;> linarith [hpb y, hqb0 y, hqbM y]
    have h2 : |ρ y| ≤ Λ := by rw [abs_of_pos (hρ.pos y)]; exact hΛ y
    rw [abs_mul, mul_comm]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  -- the `L¹` norm of `f`
  have hpi : Integrable p μ := Integrable.of_bound (C := Mp) hpm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (pDens_pos hd hs0 hsd hρ hlam hln y)]; exact hpb y)
  have hl1f : ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal (2 * Ctv * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ))) := by
    have e1 : ∀ y, ‖f y‖ₑ = ENNReal.ofReal (ρ y) * ‖p y - qb y‖ₑ := by
      intro y
      simp only [hf, enorm_mul, Real.enorm_of_nonneg (hρ.density.nonneg y)]
    simp_rw [e1]
    have hmρ : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
    have e2 : ∫⁻ y, ENNReal.ofReal (ρ y) * ‖p y - qb y‖ₑ = ∫⁻ y, ‖p y - qb y‖ₑ ∂μ := by
      show _ = ∫⁻ y, ‖p y - qb y‖ₑ ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x))
      have hgm' : Measurable fun y => ‖p y - qb y‖ₑ := (hpm.sub hqbm).enorm
      rw [lintegral_withDensity_eq_lintegral_mul _ hmρ hgm']
      rfl
    rw [e2]
    have hdiff : Integrable (fun y => p y - qb y) μ :=
      hpi.sub (Integrable.of_bound (C := Mq) hqbm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hqb0 y)]; exact hqbM y))
    have e3 : ∫⁻ y, ‖p y - qb y‖ₑ ∂μ = ENNReal.ofReal (∫ y, |p y - qb y| ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hdiff.abs (Filter.Eventually.of_forall fun y => abs_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs]
    rw [e3]
    refine ENNReal.ofReal_le_ofReal ?_
    have e4 : ∫ y, |p y - qb y| ∂μ = ∫ y, |p y - q y| ∂μ := by
      refine integral_congr_ae (hqbq.mono fun y hy => ?_)
      simp only [← hy]
    rw [e4]; exact hl1.trans (le_of_eq (by ring))
  have hcv := hCc (n + 1) hN f hfm hfb hl1f
  -- pointwise comparison
  have hae : (fun y => p y - q y) =ᵐ[μ] fun y => p y - qb y :=
    hqbq.mono fun y hy => by simp only [← hy]
  have hKt : ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - q y) =
      ResponseAux.cv (periodicRiesz d s) f := by
    rw [ResponseAux.Kt_congr _ hae, ResponseAux.Kt_eq_cv hρ.density]
  have hpt : ∀ x : Torus d, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - q y) x) ^ 2) ≤
      (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 := by
    intro x
    rw [hKt]
    unfold ResponseAux.cv
    have h1 : ENNReal.ofReal ((∫ y, periodicRiesz d s (x - y) * f y) ^ 2) = ‖∫ y, periodicRiesz d s (x - y) * f y‖ₑ ^ 2 := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h1]
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_mul]
  calc ∫⁻ x, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - q y) x) ^ 2) ∂μ
      ≤ ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ∂μ := lintegral_mono hpt
    _ ≤ ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
        lintegral_mono' (KernelAux2.withDensityReal_le ρ Λ hΛ) le_rfl
    _ = ENNReal.ofReal Λ * ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal ((Cc * deltaN d s (n + 1)) ^ 2) := by gcongr
    _ = ENNReal.ofReal (Real.sqrt Λ * Cc * deltaN d s (n + 1)) ^ 2 := by
        rw [← ENNReal.ofReal_mul hΛ0.le, ← ENNReal.ofReal_pow (by
          have : 0 ≤ deltaN d s (n + 1) := by
            have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
            exact (inv_nonneg.2 hN0.le).trans this
          positivity)]
        congr 1
        have : (Real.sqrt Λ) ^ 2 = Λ := Real.sq_sqrt hΛ0.le
        nlinarith [this]


/-- The forcing `e_N = β g*((p-q)μ) + λ g*(qμ)`. -/
def eFun (g : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam β : ℝ) (x : Torus d) : ℝ :=
  β * ResponseAux.Kt g μ (fun y => pDens g μ n lam β y - qDens g μ n lam β y) x +
    lam * ResponseAux.Kt g μ (qDens g μ n lam β) x

/-- `‖D_N + e_N‖_{L²(μ)} ≤ C δ_N`. -/
theorem w_L2 :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      Integrable (fun x => (eFun (periodicRiesz d s) (withDensityReal ρ) n lam β x +
          insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x) ^ 2) (withDensityReal ρ) ∧
      ∫ x, (eFun (periodicRiesz d s) (withDensityReal ρ) n lam β x +
          insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x) ^ 2 ∂(withDensityReal ρ) ≤
        (Cw * deltaN d s (n + 1)) ^ 2 := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Ca, hCa0, hKt⟩ := kt_pq_L2 hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  obtain ⟨Kg, hKg0, hKg⟩ := convAbs_bound hd hs0 hsd hρ
  obtain ⟨Cd, hCd⟩ := insDefect_le hd hs0 hsd hβ hρ
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine ⟨Real.sqrt (3 * β ^ 2 * Ca ^ 2 + 3 * β ^ 2 * (Mq ^ 2 * Kg ^ 2) + 3 * Cd ^ 2), Real.sqrt_nonneg _,
    fun n hn lam hlamdef => ?_⟩
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hacq := (hMq (n + 1) hN)
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪ withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hlamδ : lam ≤ β * deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    rw [hlam', div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left this hβ.le
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  set a : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - q y) with ha
  set bq : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ q with hbq
  set D : Torus d → ℝ := insDefect (periodicRiesz d s) μ n lam β with hD
  have ham : Measurable a := measurable_Kt hd hs0 hsd hβ hρ (hpm.sub hqm)
  have hbm : Measurable bq := measurable_Kt hd hs0 hsd hβ hρ hqm
  have hDm : Measurable D := by
    haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
    have hSm : Measurable fun x : Torus d => ∫ Y, ∑ j, periodicRiesz d s (x - Y j)
        ∂(cavityLaw (periodicRiesz d s) μ n lam β) := by
      have : StronglyMeasurable (Function.uncurry fun (x : Torus d) (Y : Config d n) =>
          ∑ j, periodicRiesz d s (x - Y j)) :=
        (Finset.measurable_sum _ fun j _ =>
          hgm.comp (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))).stronglyMeasurable
      exact (this.integral_prod_right' (ν := cavityLaw (periodicRiesz d s) μ n lam β)).measurable
    rw [hD]; unfold insDefect
    exact (Real.measurable_log.comp (measurable_phiIns hd hs0 hsd hρ hlam hln)).add (hSm.const_mul _)
  have hA : Integrable (fun x => a x ^ 2) μ ∧ ∫ x, a x ^ 2 ∂μ ≤ (Ca * deltaN d s (n + 1)) ^ 2 := by
    refine integral_sq_le_of_lintegral ham (by positivity) ?_
    have := hKt n hn lam hlamdef
    rw [← ENNReal.ofReal_pow (by positivity)] at this
    exact this
  -- bounds on `bq` and `D`
  have hbb : ∀ x, |bq x| ≤ Mq * Kg := by
    intro x
    obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
    have hgi := hK.int x
    have hqint : Integrable (fun y => periodicRiesz d s (x - y) * q y) μ :=
      hgi.mul_bdd hqm.aestronglyMeasurable (c := Mq) (hqb.mono fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hq, qDens]; exact ENNReal.toReal_nonneg)]; exact hy)
    show |∫ y, periodicRiesz d s (x - y) * q y ∂μ| ≤ Mq * Kg
    refine (abs_integral_le_integral_abs).trans ?_
    have hmeas : Measurable fun y : Torus d => |periodicRiesz d s (x - y)| :=
      (hgm.comp (measurable_const.sub measurable_id)).abs
    calc ∫ y, |periodicRiesz d s (x - y) * q y| ∂μ ≤ ∫ y, Mq * |periodicRiesz d s (x - y)| ∂μ := by
          refine integral_mono_ae hqint.abs ((hgi.abs).const_mul _) (hqb.mono fun y hy => ?_)
          show |periodicRiesz d s (x - y) * q y| ≤ Mq * |periodicRiesz d s (x - y)|
          rw [abs_mul, abs_of_nonneg (by simp only [hq, qDens]; exact ENNReal.toReal_nonneg : 0 ≤ q y)]
          nlinarith [abs_nonneg (periodicRiesz d s (x - y))]
      _ = Mq * ∫ y, |periodicRiesz d s (x - y)| ∂μ := integral_const_mul _ _
      _ ≤ Mq * Kg := mul_le_mul_of_nonneg_left (hKg x) hMq0.le
  have hDb : ∀ x, 0 ≤ D x ∧ D x ≤ Cd * deltaN d s (n + 1) := by
    intro x
    have := hCd (n + 1) hN x
    rw [← hlam'] at this
    exact ⟨this.1, this.2.1⟩
  -- pointwise bound
  set K : ℝ := 3 * ((β * deltaN d s (n + 1) * (Mq * Kg)) ^ 2 + (Cd * deltaN d s (n + 1)) ^ 2) with hK
  have hpt : ∀ x, (β * a x + lam * bq x + D x) ^ 2 ≤ 3 * β ^ 2 * a x ^ 2 + K := by
    intro x
    have h1 : (lam * bq x) ^ 2 ≤ (β * deltaN d s (n + 1) * (Mq * Kg)) ^ 2 := by
      have h2 : |lam * bq x| ≤ β * deltaN d s (n + 1) * (Mq * Kg) := by
        rw [abs_mul, abs_of_nonneg hlam]
        exact mul_le_mul hlamδ (hbb x) (abs_nonneg _) (by positivity)
      calc (lam * bq x) ^ 2 = |lam * bq x| ^ 2 := (sq_abs _).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h2 2
    have h3 : D x ^ 2 ≤ (Cd * deltaN d s (n + 1)) ^ 2 :=
      pow_le_pow_left₀ (hDb x).1 (hDb x).2 2
    nlinarith [sq_nonneg (β * a x - lam * bq x), sq_nonneg (β * a x - D x), sq_nonneg (lam * bq x - D x)]
  have hmeasw : Measurable fun x => (β * a x + lam * bq x + D x) ^ 2 :=
    (((ham.const_mul β).add (hbm.const_mul lam)).add hDm).pow_const 2
  have hdom : Integrable (fun x => 3 * β ^ 2 * a x ^ 2 + K) μ :=
    (hA.1.const_mul _).add (integrable_const _)
  have hI : Integrable (fun x => (β * a x + lam * bq x + D x) ^ 2) μ :=
    Integrable.mono' hdom hmeasw.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt x)
  have hI2 : ∫ x, (β * a x + lam * bq x + D x) ^ 2 ∂μ ≤ 3 * β ^ 2 * (Ca * deltaN d s (n + 1)) ^ 2 + K := by
    calc ∫ x, (β * a x + lam * bq x + D x) ^ 2 ∂μ ≤ ∫ x, (3 * β ^ 2 * a x ^ 2 + K) ∂μ :=
          integral_mono hI hdom hpt
      _ = 3 * β ^ 2 * ∫ x, a x ^ 2 ∂μ + K := by
          rw [integral_add (hA.1.const_mul _) (integrable_const _), integral_const_mul]
          simp
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hA.2 (by positivity : 0 ≤ 3 * β ^ 2)
          linarith
  refine ⟨?_, ?_⟩
  · exact hI
  · refine hI2.trans (le_of_eq ?_)
    have hsq : (Real.sqrt (3 * β ^ 2 * Ca ^ 2 + 3 * β ^ 2 * (Mq ^ 2 * Kg ^ 2) + 3 * Cd ^ 2) *
        deltaN d s (n + 1)) ^ 2 = (3 * β ^ 2 * Ca ^ 2 + 3 * β ^ 2 * (Mq ^ 2 * Kg ^ 2) + 3 * Cd ^ 2) *
          deltaN d s (n + 1) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hsq, hK]
    ring

end KtL2
section DeltaLim

theorem tendsto_deltaN (hs0 : 0 ≤ s) (hsd : s < d) (hd : 1 ≤ d) :
    Tendsto (fun N : ℕ => deltaN d s N) atTop (𝓝 0) := by
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  unfold deltaN
  by_cases h1 : s < (d : ℝ) / 2
  · simp only [h1, if_true]
    exact tendsto_inv_atTop_zero.comp hNat
  by_cases h2 : s = (d : ℝ) / 2
  · simp only [h1, if_false]
    simp only [h2, if_true]
    have hsq : Tendsto (fun N : ℕ => 3 * (Real.sqrt N)⁻¹) atTop (𝓝 0) := by
      have : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop := Real.tendsto_sqrt_atTop.comp hNat
      simpa using (tendsto_inv_atTop_zero.comp this).const_mul 3
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => ?_) ?_ hsq
    · rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp
      · have hN : (0 : ℝ) < N := by exact_mod_cast h
        have : 0 ≤ Real.log (Real.exp 1 * N) := by
          rw [Real.log_mul (Real.exp_pos _).ne' hN.ne', Real.log_exp]
          have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast h)
          linarith
        positivity
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hN0 : (0 : ℝ) < N := by linarith
      have hr0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
      have hr1 : 1 ≤ Real.sqrt N := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN1
      have hrr : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
      have hlog : Real.log N ≤ 2 * Real.sqrt N := by
        have h := Real.log_le_sub_one_of_pos hr0
        have h2 : Real.log N = 2 * Real.log (Real.sqrt N) := by
          conv_lhs => rw [← hrr]
          rw [Real.log_mul hr0.ne' hr0.ne']; ring
        rw [h2]; linarith
      rw [Real.log_mul (Real.exp_pos _).ne' hN0.ne', Real.log_exp, inv_mul_eq_div, div_le_iff₀ hN0]
      calc 1 + Real.log N ≤ 3 * Real.sqrt N := by linarith
        _ = 3 * (Real.sqrt N)⁻¹ * N := by
          field_simp
          linarith [hrr]
  · simp only [h1, h2, if_false]
    have hspos : 0 < s := by
      have : (0 : ℝ) < (d : ℝ) / 2 := by
        have : (0 : ℝ) < d := by exact_mod_cast hd
        positivity
      push Not at h1; linarith
    have hp : 0 < (d : ℝ) / s - 1 := by
      have : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hspos]; linarith
      linarith
    have := (tendsto_rpow_neg_atTop hp).comp hNat
    refine this.congr fun N => ?_
    simp only [Function.comp]
    congr 1; ring

end DeltaLim


section Unif

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)

include hd hs0 hsd hρ

/-- Uniform smallness of `g * (h μ)` for bounded `h` with small `L¹(μ)` norm. -/
theorem Kt_sup_small (M : ℝ) (hM : 0 ≤ M) : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ h : Torus d → ℝ, Measurable h → (∀ y, |h y| ≤ M) → ∫ y, |h y| ∂(withDensityReal ρ) ≤ δ →
      ∀ x, |ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) h x| ≤ ε := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := MarginalAux.sup_conv_small hd hs0 hsd (M * Λ) (by positivity) ε hε
  refine ⟨δ, hδ, fun h hm hb hl x => ?_⟩
  have hρm : Measurable ρ := hρ.density.measurable
  set f : Torus d → ℝ := fun y => ρ y * h y with hf
  have hfm : Measurable f := hρm.mul hm
  have hfb : ∀ y, |f y| ≤ M * Λ := by
    intro y
    have h2 : |ρ y| ≤ Λ := by rw [abs_of_pos (hρ.pos y)]; exact hΛ y
    rw [abs_mul, mul_comm]
    exact mul_le_mul (hb y) h2 (abs_nonneg _) hM
  have hhi : Integrable h (withDensityReal ρ) :=
    Integrable.of_bound (C := M) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y)
  have hl1f : ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal δ := by
    have e1 : ∀ y, ‖f y‖ₑ = ENNReal.ofReal (ρ y) * ‖h y‖ₑ := by
      intro y
      simp only [hf, enorm_mul, Real.enorm_of_nonneg (hρ.density.nonneg y)]
    simp_rw [e1]
    have hmρ : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
    have e2 : ∫⁻ y, ENNReal.ofReal (ρ y) * ‖h y‖ₑ = ∫⁻ y, ‖h y‖ₑ ∂(withDensityReal ρ) := by
      show _ = ∫⁻ y, ‖h y‖ₑ ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x))
      rw [lintegral_withDensity_eq_lintegral_mul _ hmρ hm.enorm]
      rfl
    rw [e2]
    have e3 : ∫⁻ y, ‖h y‖ₑ ∂(withDensityReal ρ) = ENNReal.ofReal (∫ y, |h y| ∂(withDensityReal ρ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hhi.abs (Filter.Eventually.of_forall fun y => abs_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs]
    rw [e3]
    exact ENNReal.ofReal_le_ofReal hl
  have h1 := hs f hfm hfb hl1f x
  have hKt : ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) h x =
      ∫ y, periodicRiesz d s (x - y) * f y := by
    rw [ResponseAux.Kt_eq_cv hρ.density]; rfl
  rw [hKt]
  have h2 : ‖∫ y, periodicRiesz d s (x - y) * f y‖ₑ ≤ ENNReal.ofReal ε := by
    refine (enorm_integral_le_lintegral_enorm _).trans ((le_of_eq ?_).trans h1)
    refine lintegral_congr fun y => ?_
    rw [enorm_mul]
  rw [Real.enorm_eq_ofReal_abs] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 h2

end Unif

section Unif2

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ)

include hd hs0 hsd hβ hρ

/-- Total variation smallness of `π_{n+1}` against `μ`. -/
theorem tv_pi_mu : ∀ ε : ℝ, 0 < ε → ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ A : Set (Torus d), MeasurableSet A →
    |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) (β / ((n + 1 : ℕ) : ℝ)) β) A).toReal -
      (withDensityReal ρ A).toReal| ≤ ε := by
  have hμ := isProbabilityMeasure_mu hρ
  intro ε hε
  have h := tendsto_tvDist_Q hd hs0 hsd hβ hρ
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((tendsto_order.1 h).2 ε hε)
  refine ⟨n₁, fun n hn A hA => ?_⟩
  have hG := modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (n + 1) (Nat.succ_pos n)
  haveI : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) := by
    rw [hG]; exact cavity_isProb hd hs0 hsd β hρ (n + 1) _ (by positivity)
  haveI : IsProbabilityMeasure ((modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)).map
      fun X : Config d (n + 1) => X 0) :=
    (Measure.isProbabilityMeasure_map_iff (Measurable.aemeasurable (measurable_pi_apply 0))).2 inferInstance
  have h1 := Entropy.abs_le_tvDist ((modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)).map
      fun X : Config d (n + 1) => X 0) (withDensityReal ρ) hA
  have h2 := hn₁ n hn
  have e : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) (β / ((n + 1 : ℕ) : ℝ)) β) =
      (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)).map
        fun X : Config d (n + 1) => X 0 := by
    rw [← hG]
    unfold firstMarginal
    rw [dif_pos (Nat.succ_pos n)]
    rfl
  rw [e]
  simp only [Measure.real] at h1
  exact (h1.trans h2.le)

end Unif2

section Unif3

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
  {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (hln : lam * n ≤ β)

include hd hs0 hsd hρ hlam hln

/-- If `|u| ≤ η` pointwise then `|p - 1| ≤ e^{2η} - 1`. -/
theorem pDens_dev {η : ℝ} (hη : 0 ≤ η)
    (hu : ∀ y, |uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y| ≤ η) (x : Torus d) :
    |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1| ≤ Real.exp (2 * η) - 1 := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨M, hM0, hM⟩ := exp_uIns_le hd hs0 hsd hρ hlam hln
  have hum := measurable_uIns hd hs0 hsd hρ hlam hln
  have hint : Integrable (fun y => Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y))
      (withDensityReal ρ) :=
    Integrable.of_bound (C := M) (Real.measurable_exp.comp hum).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hM y)
  set Z := ∫ y, Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y) ∂(withDensityReal ρ) with hZ
  have hZ1 : Real.exp (-η) ≤ Z := by
    have := integral_mono (integrable_const (Real.exp (-η))) hint (fun y => Real.exp_le_exp.2 (abs_le.1 (hu y)).1)
    simpa using this
  have hZ2 : Z ≤ Real.exp η := by
    have := integral_mono hint (integrable_const (Real.exp η)) (fun y => Real.exp_le_exp.2 (abs_le.1 (hu y)).2)
    simpa using this
  have hZ0 : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) hZ1
  have hc1 : -η ≤ Real.log Z := by
    have := Real.log_le_log (Real.exp_pos _) hZ1; rwa [Real.log_exp] at this
  have hc2 : Real.log Z ≤ η := by
    have := Real.log_le_log hZ0 hZ2; rwa [Real.log_exp] at this
  have hux := abs_le.1 (hu x)
  have hp : pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x =
      Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x - Real.log Z) := rfl
  rw [hp]
  set v := uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x - Real.log Z with hv
  have hv1 : -(2 * η) ≤ v := by linarith
  have hv2 : v ≤ 2 * η := by linarith
  rw [abs_le]
  constructor
  · have h1 := Real.add_one_le_exp (v)
    have h2 := Real.add_one_le_exp (2 * η)
    linarith
  · have := Real.exp_le_exp.2 hv2
    linarith

end Unif3

section Unif4

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlamdef : lam = β / ((n + 1 : ℕ) : ℝ))

include hd hs0 hsd hβ hρ hn hlamdef

/-- Pointwise bound for `u` in terms of `g * ((1 - q) μ)`. -/
theorem uIns_le_aux (hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ) {Mq Kg : ℝ} (hMq : 0 ≤ Mq)
    (hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq)
    (hKg : ∀ x : Torus d, ∫ y, |periodicRiesz d s (x - y)| ∂(withDensityReal ρ) ≤ Kg) (x : Torus d) :
    |uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x| ≤
      β * |ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ)
          (fun y => 1 - qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y) x| +
        lam * (Kg * Mq) + |insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x| := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  have hgi := hK.int x
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hq0 : ∀ y, 0 ≤ qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y := fun y => ENNReal.toReal_nonneg
  have hqint : Integrable (fun y => periodicRiesz d s (x - y) *
      qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y) (withDensityReal ρ) :=
    hgi.mul_bdd hqm.aestronglyMeasurable (c := Mq) (hqb.mono fun y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 y)]; exact hy)
  have hu := uIns_eq hd hs0 hsd hβ hρ hn hlamdef hac x
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set G : ℝ := ∫ y, periodicRiesz d s (x - y) * q y ∂(withDensityReal ρ) with hG
  have hKt : ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) (fun y => 1 - q y) x =
      convMeasure (periodicRiesz d s) (withDensityReal ρ) x - G := by
    unfold ResponseAux.Kt convMeasure
    simp_rw [mul_sub, mul_one]
    exact integral_sub hgi hqint
  have hGb : |G| ≤ Kg * Mq := by
    have h1 : ‖G‖ ≤ ∫ y, Mq * |periodicRiesz d s (x - y)| ∂(withDensityReal ρ) := by
      refine norm_integral_le_of_norm_le (hgi.abs.const_mul Mq) (hqb.mono fun y hy => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hq0 y), mul_comm]
      exact mul_le_mul_of_nonneg_right hy (abs_nonneg _) |>.trans_eq (by ring)
    rw [integral_const_mul] at h1
    rw [Real.norm_eq_abs] at h1
    nlinarith [hKg x]
  have hu2 : uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x =
      β * (convMeasure (periodicRiesz d s) (withDensityReal ρ) x - G) + lam * G +
        insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x := by
    rw [hu]
    have : lam * (n : ℝ) = β - lam := by linarith
    rw [this]; unfold convMeasure; ring
  rw [hu2, ← hKt]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) le_rfl)
  · rw [abs_mul, abs_of_pos hβ]
  · rw [abs_mul, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left hGb hlam

/-- `‖1 - q‖_{L¹(μ)}` is small if `π_{n+1}` is `TV`-close to `μ` and to `ν_n`. -/
theorem l1_one_q (hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ) {εa εb : ℝ} {Mp : ℝ}
    (hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp)
    (hTV1 : ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) A).toReal -
        (withDensityReal ρ A).toReal| ≤ εa)
    (hTV2 : ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) A).toReal -
        (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) A).toReal| ≤ εb) :
    ∫ y, |1 - qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y| ∂(withDensityReal ρ) ≤
      2 * εa + 2 * εb := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hl2 := l1_pq hd hs0 hsd hβ hρ hn hlamdef hac hTV2 hpb
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  obtain ⟨hqi, hq1⟩ := integral_qDens hd hs0 hsd hβ hρ hn hlamdef hac
  have hp1 := integral_pDens hd hs0 hsd hρ hlam hln
  have hpi : Integrable (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β) (withDensityReal ρ) :=
    Integrable.of_bound (C := Mp) hpm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (pDens_pos hd hs0 hsd hρ hlam hln y)]; exact hpb y)
  have hπeq := firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln
  have hl1 : ∫ y, |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1| ∂(withDensityReal ρ) ≤ 2 * εa := by
    refine l1_of_sets hpm measurable_const hpi (integrable_const _) hp1 (by simp) ?_
    intro A hA
    have h := hTV1 A hA
    rw [hπeq, toReal_withDensity_apply (fun x => (pDens_pos hd hs0 hsd hρ hlam hln x).le) hpi hA] at h
    have e : ∫ x in A, (1 : ℝ) ∂(withDensityReal ρ) = (withDensityReal ρ A).toReal := by
      rw [setIntegral_const]; simp [Measure.real]
    rw [e]; exact h
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  have h1 : Integrable (fun y => |p y - 1|) (withDensityReal ρ) := (hpi.sub (integrable_const _)).abs
  have h2 : Integrable (fun y => |p y - q y|) (withDensityReal ρ) := (hpi.sub hqi).abs
  have h3 : Integrable (fun y => |1 - q y|) (withDensityReal ρ) := ((integrable_const (1 : ℝ)).sub hqi).abs
  have hle : ∫ y, |1 - q y| ∂(withDensityReal ρ) ≤ ∫ y, (|p y - 1| + |p y - q y|) ∂(withDensityReal ρ) := by
    refine integral_mono h3 (h1.add h2) fun y => ?_
    have := abs_add_le (1 - p y) (p y - q y)
    rw [show (1 - p y) + (p y - q y) = 1 - q y by ring, abs_sub_comm 1 (p y)] at this
    exact this
  rw [integral_add h1 h2] at hle
  linarith


end Unif4

section Unif5

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ)

include hd hs0 hsd hβ hρ

/-- **Uniform smallness**: `‖p_n - 1‖_∞ → 0`. -/
theorem sup_dev_small : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n → ∀ lam : ℝ,
    lam = β / ((n + 1 : ℕ) : ℝ) → ∀ x : Torus d,
      |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1| ≤ ε := by
  have hμ := isProbabilityMeasure_mu hρ
  intro ε hε
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  obtain ⟨Ctv, hCtv0, hCtv⟩ := cavity_tv hd hs0 hsd hβ hρ
  obtain ⟨Cd, hCd⟩ := insDefect_le hd hs0 hsd hβ hρ
  obtain ⟨Kg, hKg0, hKg⟩ := convAbs_bound hd hs0 hsd hρ
  set η : ℝ := Real.log (1 + ε) / 2 with hη
  have hη0 : 0 < η := by
    have : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    positivity
  set ε₁ : ℝ := η / (3 * β) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨δ₁, hδ₁, hKt⟩ := Kt_sup_small hd hs0 hsd hρ (1 + Mq) (by positivity) ε₁ hε₁0
  obtain ⟨n₁, hn₁⟩ := tv_pi_mu hd hs0 hsd hβ hρ (δ₁ / 8) (by positivity)
  -- smallness of `δ_{n+1}`
  have hδt : Tendsto (fun n : ℕ => deltaN d s (n + 1)) atTop (𝓝 0) :=
    (tendsto_deltaN hs0 hsd hd1).comp (tendsto_add_atTop_nat 1)
  set K : ℝ := |Cd| + β * Kg * Mq + 1 with hK
  have hK0 : 0 < K := by positivity
  set κ : ℝ := min (η / (3 * K)) ((δ₁ / (8 * (Ctv + 1))) ^ 2) with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 ((tendsto_order.1 hδt).2 κ hκ0)
  refine ⟨max (max n₁ n₂) 1, fun n hnn hn lam hlamdef x => ?_⟩
  have hn₁' : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnn
  have hn₂' : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnn
  have hδκ := hn₂ n hn₂'
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hacq := (hMq (n + 1) hN)
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪ withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hlamδ : lam ≤ β * deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    rw [hlam', div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left this hβ.le
  have hTV1 : ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) A).toReal -
        (withDensityReal ρ A).toReal| ≤ δ₁ / 8 := by
    intro A hA
    subst hlam'
    exact hn₁ n hn₁' A hA
  have hTV2 : ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) A).toReal -
        (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) A).toReal| ≤
        Ctv * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    intro A hA
    subst hlam'
    exact hCtv (n + 1) hN A hA
  have hsqrt : Ctv * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ δ₁ / 8 := by
    have h1 : deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ) ≤ deltaN d s (n + 1) := by
      refine div_le_self hδ0 ?_
      exact_mod_cast (by omega : 1 ≤ n + 1)
    have h2 : Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ δ₁ / (8 * (Ctv + 1)) := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      exact h1.trans (hδκ.le.trans (min_le_right _ _))
    calc Ctv * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ (Ctv + 1) * (δ₁ / (8 * (Ctv + 1))) := by
          gcongr
          linarith
      _ = δ₁ / 8 := by field_simp
  have hl1 := l1_one_q hd hs0 hsd hβ hρ hn hlamdef hac hpb hTV1 (fun A hA => (hTV2 A hA).trans hsqrt)
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hq0 : ∀ y, 0 ≤ qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y := fun y => ENNReal.toReal_nonneg
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
  have hqbm : Measurable qb := hqm.min measurable_const
  have hqbq : q =ᵐ[withDensityReal ρ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
  have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
  have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
  have hhb : ∀ y, |1 - qb y| ≤ 1 + Mq := by
    intro y
    rw [abs_le]; constructor <;> linarith [hqb0 y, hqbM y]
  have hsm : ∫ y, |1 - qb y| ∂(withDensityReal ρ) ≤ δ₁ := by
    have e4 : ∫ y, |1 - qb y| ∂(withDensityReal ρ) = ∫ y, |1 - q y| ∂(withDensityReal ρ) := by
      refine integral_congr_ae (hqbq.mono fun y hy => ?_)
      simp only [← hy]
    rw [e4]
    refine hl1.trans ?_
    have : 2 * (δ₁ / 8) + 2 * (δ₁ / 8) ≤ δ₁ := by linarith
    linarith
  have hae : (fun y => 1 - q y) =ᵐ[withDensityReal ρ] fun y => 1 - qb y :=
    hqbq.mono fun y hy => by simp only [← hy]
  have hκK : K * deltaN d s (n + 1) ≤ η / 3 := by
    have := hδκ.le.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hut : ∀ y, |uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y| ≤ η := by
    intro y
    have hKty := hKt (fun y => 1 - qb y) (measurable_const.sub hqbm) hhb hsm y
    rw [← ResponseAux.Kt_congr _ hae] at hKty
    have hu := uIns_le_aux hd hs0 hsd hβ hρ hn hlamdef hac hMq0.le hqb hKg y
    have hDb := hCd (n + 1) hN y
    rw [Nat.add_sub_cancel] at hDb
    have hDb' : |insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β y| ≤ |Cd| * deltaN d s (n + 1) := by
      subst hlam'
      rw [abs_of_nonneg hDb.1]
      exact hDb.2.1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)
    have h1 : β * |ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) (fun y => 1 - q y) y| ≤ η / 3 := by
      calc _ ≤ β * ε₁ := mul_le_mul_of_nonneg_left hKty hβ.le
        _ = η / 3 := by rw [hε₁]; field_simp
    have h2 : lam * (Kg * Mq) ≤ η / 3 := by
      calc lam * (Kg * Mq) ≤ (β * deltaN d s (n + 1)) * (Kg * Mq) :=
            mul_le_mul_of_nonneg_right hlamδ (by positivity)
        _ = (β * Kg * Mq) * deltaN d s (n + 1) := by ring
        _ ≤ K * deltaN d s (n + 1) := by
            refine mul_le_mul_of_nonneg_right ?_ hδ0
            rw [hK]; linarith [abs_nonneg Cd]
        _ ≤ η / 3 := hκK
    have h3 : |Cd| * deltaN d s (n + 1) ≤ η / 3 := by
      refine le_trans ?_ hκK
      refine mul_le_mul_of_nonneg_right ?_ hδ0
      rw [hK]
      have : 0 ≤ β * Kg * Mq := by positivity
      linarith
    linarith
  have hdev := pDens_dev hd hs0 hsd hρ hlam hln hη0.le hut x
  have : Real.exp (2 * η) = 1 + ε := by
    rw [hη, show 2 * (Real.log (1 + ε) / 2) = Real.log (1 + ε) by ring, Real.exp_log (by linarith)]
  linarith

end Unif5

section Absorb

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlamdef : lam = β / ((n + 1 : ℕ) : ℝ))

include hd hs0 hsd hβ hρ hn hlamdef

/-- The absorption inequality: if `|p - 1| ≤ 1` then `‖p - 1‖₂² ≤ 4 ‖D_N + e_N‖₂²`. -/
theorem absorb (hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ) {Mp Mq Kg : ℝ} (hMp : 1 ≤ Mp)
    (hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp)
    (hpl : ∀ y, Real.exp (-Mp) ≤ pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y)
    (hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq)
    (hKg : ∀ x : Torus d, ∫ y, |periodicRiesz d s (x - y)| ∂(withDensityReal ρ) ≤ Kg)
    (hz : ∀ y, |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1| ≤ 1) {B : ℝ}
    (hW : Integrable (fun x => (eFun (periodicRiesz d s) (withDensityReal ρ) n lam β x +
          insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x) ^ 2) (withDensityReal ρ))
    (hWB : ∫ x, (eFun (periodicRiesz d s) (withDensityReal ρ) n lam β x +
          insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x) ^ 2 ∂(withDensityReal ρ) ≤ B) :
    ∫ x, (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) ^ 2 ∂(withDensityReal ρ) ≤ 4 * B := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hp0 := pDens_pos hd hs0 hsd hρ hlam hln
  have hp1 := integral_pDens hd hs0 hsd hρ hlam hln
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set μ := withDensityReal ρ with hμdef
  set z : Torus d → ℝ := fun y => p y - 1 with hzdef
  have hzm : Measurable z := hpm.sub measurable_const
  set Kz : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ z with hKz
  have hKzm : Measurable Kz := measurable_Kt hd hs0 hsd hβ hρ hzm
  set c : ℝ := Real.log (∫ y, Real.exp (uIns (periodicRiesz d s) μ n lam β y) ∂μ) with hc
  set W : Torus d → ℝ := fun x => eFun (periodicRiesz d s) μ n lam β x +
    insDefect (periodicRiesz d s) μ n lam β x with hWdef
  have hE : ∀ x, Real.log (p x) + β * Kz x = W x - c := by
    intro x
    have h := cavity_eq_z hd hs0 hsd hβ hρ hn hlamdef hac hpb hqb x
    simp only [add_sub_cancel] at h
    simp only [hWdef, eFun, hKz, hzdef, hp]
    linarith
  have hlogb : ∀ y, |Real.log (p y)| ≤ Mp := by
    intro y
    rw [abs_le]; constructor
    · have := Real.log_le_log (Real.exp_pos _) (hpl y)
      rw [Real.log_exp] at this; exact this
    · have := Real.log_le_sub_one_of_pos (hp0 y)
      linarith [hpb y]
  have hKzb : ∀ x, |Kz x| ≤ Kg := by
    intro x
    obtain ⟨B', Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
    have h1 : ‖Kz x‖ ≤ ∫ y, |periodicRiesz d s (x - y)| ∂μ := by
      refine norm_integral_le_of_norm_le (hK.int x).abs (Filter.Eventually.of_forall fun y => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have := hz y
      calc |periodicRiesz d s (x - y)| * |z y| ≤ |periodicRiesz d s (x - y)| * 1 :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = _ := mul_one _
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hKg x)
  have hlogm : Measurable fun y => Real.log (p y) := Real.measurable_log.comp hpm
  have hWm : Measurable W := by
    have : W = fun x => Real.log (p x) + β * Kz x + c := by
      funext x; have := hE x; linarith
    rw [this]
    exact ((hlogm.add (hKzm.const_mul β)).add measurable_const)
  have hzi : Integrable z μ :=
    Integrable.of_bound (C := 1) hzm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hz y)
  have hz2i : Integrable (fun y => z y ^ 2) μ :=
    Integrable.of_bound (C := 1) (hzm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_pow]
      calc |z y| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hz y) 2
        _ = 1 := one_pow 2)
  have hI1 : Integrable (fun y => z y * Real.log (p y)) μ :=
    Integrable.of_bound (C := Mp) (hzm.mul hlogm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |z y| * |Real.log (p y)| ≤ 1 * Mp :=
            mul_le_mul (hz y) (hlogb y) (abs_nonneg _) zero_le_one
        _ = Mp := one_mul _)
  have hKzbn : 0 ≤ Kg := (abs_nonneg _).trans (hKzb 0)
  have hI2 : Integrable (fun y => z y * Kz y) μ :=
    Integrable.of_bound (C := Kg) (hzm.mul hKzm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |z y| * |Kz y| ≤ 1 * Kg :=
            mul_le_mul (hz y) (hKzb y) (abs_nonneg _) zero_le_one
        _ = Kg := one_mul _)
  have hI3 : Integrable (fun y => z y * W y) μ := by
    refine Integrable.mono' (hz2i.add hW) (hzm.mul hWm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    show |z y| * |W y| ≤ z y ^ 2 + W y ^ 2
    nlinarith [sq_nonneg (|z y| - |W y|), sq_abs (z y), sq_abs (W y), sq_nonneg (z y), sq_nonneg (W y)]
  -- the identity
  have hz0 : ∫ y, z y ∂μ = 0 := by
    simp only [hzdef]
    rw [integral_sub (Integrable.of_bound (C := Mp) hpm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (hp0 y)]; exact hpb y)) (integrable_const _), hp1]
    simp
  have hid : ∫ y, z y * Real.log (p y) ∂μ + β * ∫ y, z y * Kz y ∂μ = ∫ y, z y * W y ∂μ := by
    have h1 : ∫ y, (z y * Real.log (p y) + β * (z y * Kz y)) ∂μ = ∫ y, (z y * W y - c * z y) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      have := hE y
      show z y * Real.log (p y) + β * (z y * Kz y) = z y * W y - c * z y
      have h2 : z y * (Real.log (p y) + β * Kz y) = z y * (W y - c) := by rw [this]
      linarith [h2]
    rw [integral_add hI1 (hI2.const_mul β), integral_const_mul, integral_sub hI3 (hzi.const_mul c),
      integral_const_mul, hz0] at h1
    linarith
  -- positivity of the quadratic form
  have hnn : 0 ≤ ∫ y, z y * Kz y ∂μ := by
    have hmem : MemLp z 2 μ := MemLp.of_bound hzm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hz y)
    have := Kt_nonneg hd hs0 hsd hρ.density hΛ hmem
    simpa [mul_comm] using this
  -- the lower bound `z log p ≥ z² / 2`
  have hlow : ∀ y, z y ^ 2 / 2 ≤ z y * Real.log (p y) := by
    intro y
    have hpy := hp0 y
    have hzy : p y = 1 + z y := by simp [hzdef]
    by_cases h0 : 0 ≤ z y
    · have h1 := Real.one_sub_inv_le_log_of_pos hpy
      have h2 : 1 - (p y)⁻¹ = z y / p y := by
        rw [hzy]; field_simp; ring
      have h3 : z y / p y ≥ z y / 2 := by
        have : p y ≤ 2 := by have := (abs_le.1 (hz y)).2; linarith
        exact div_le_div_of_nonneg_left h0 hpy this
      have h4 : z y / 2 ≤ Real.log (p y) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h4 h0]
    · push Not at h0
      have h1 := Real.log_le_sub_one_of_pos hpy
      have h2 : Real.log (p y) ≤ z y := by rw [hzy] at h1 ⊢; linarith
      nlinarith [mul_le_mul_of_nonpos_left h2 h0.le, sq_nonneg (z y)]
  have hlowi : ∫ y, z y ^ 2 / 2 ∂μ ≤ ∫ y, z y * Real.log (p y) ∂μ :=
    integral_mono (hz2i.div_const 2) hI1 hlow
  have hCS : ∫ y, z y * W y ∂μ ≤ ∫ y, (z y ^ 2 / 4 + W y ^ 2) ∂μ := by
    refine integral_mono hI3 ((hz2i.div_const 4).add hW) fun y => ?_
    simp only [hWdef]
    nlinarith [sq_nonneg (z y / 2 - W y)]
  rw [integral_add (hz2i.div_const 4) hW, integral_div] at hCS
  rw [integral_div] at hlowi
  have hfin : (∫ y, z y ^ 2 ∂μ) / 2 ≤ (∫ y, z y ^ 2 ∂μ) / 4 + ∫ y, W y ^ 2 ∂μ := by
    have hβz : 0 ≤ β * ∫ y, z y * Kz y ∂μ := mul_nonneg hβ.le hnn
    linarith
  have : ∫ y, W y ^ 2 ∂μ ≤ B := hWB
  show ∫ y, z y ^ 2 ∂μ ≤ 4 * B
  linarith

end Absorb

section Final

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ)

include hd hs0 hsd hβ hρ

/-- `‖p_n - 1‖_{L²(μ)}² ≤ (C δ_{n+1})²` for every `n ≥ 1`. -/
theorem L2_all : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
    ∫ x, (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) ^ 2 ∂(withDensityReal ρ) ≤
      (C * deltaN d s (n + 1)) ^ 2 := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨n₀, hn₀⟩ := sup_dev_small hd hs0 hsd hβ hρ 1 one_pos
  obtain ⟨Cw, hCw0, hCw⟩ := w_L2 hd hs0 hsd hβ hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  obtain ⟨Kg, hKg0, hKg⟩ := convAbs_bound hd hs0 hsd hρ
  refine ⟨max (2 * Cw) (Mp * (n₀ + 1)), le_max_of_le_left (by positivity), fun n hn lam hlamdef => ?_⟩
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hp0 := pDens_pos hd hs0 hsd hρ hlam hln
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  by_cases hlarge : n₀ ≤ n
  · have hacq := (hMq (n + 1) hN)
    have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪ withDensityReal ρ := by
      subst hlam'; exact hacq.1
    have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
      subst hlam'; exact hacq.2
    have hpl : ∀ y, Real.exp (-Mp) ≤ pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y := by
      subst hlam'; exact fun y => (hMp (n + 1) hN y).1
    obtain ⟨hWi, hWB⟩ := hCw n hn lam hlamdef
    have := absorb hd hs0 hsd hβ hρ hn hlamdef hac hMp1 hpb hpl hqb hKg
      (fun y => hn₀ n hlarge hn lam hlamdef y) hWi hWB
    refine this.trans ?_
    have h2 : 2 * Cw ≤ max (2 * Cw) (Mp * (n₀ + 1)) := le_max_left _ _
    have h3 : 2 * Cw * deltaN d s (n + 1) ≤ max (2 * Cw) (Mp * (n₀ + 1)) * deltaN d s (n + 1) :=
      mul_le_mul_of_nonneg_right h2 hδ0
    have h4 : 0 ≤ 2 * Cw * deltaN d s (n + 1) := by positivity
    nlinarith [mul_self_le_mul_self h4 h3]
  · push Not at hlarge
    have hz : ∀ y, |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1| ≤ Mp := by
      intro y
      have := hp0 y; have := hpb y
      rw [abs_le]; constructor <;> linarith
    have hzm : Measurable fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1 :=
      hpm.sub measurable_const
    have hint : Integrable (fun y => (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1) ^ 2)
        (withDensityReal ρ) :=
      Integrable.of_bound (C := Mp ^ 2) (hzm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hz y) 2)
    have h1 : ∫ x, (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) ^ 2 ∂(withDensityReal ρ) ≤
        Mp ^ 2 := by
      have := integral_mono hint (integrable_const (Mp ^ 2)) (fun y => by
        simp only
        have := pow_le_pow_left₀ (abs_nonneg _) (hz y) 2
        rwa [sq_abs] at this)
      simpa using this
    refine h1.trans ?_
    have hδ : 1 ≤ (n₀ + 1 : ℝ) * deltaN d s (n + 1) := by
      have hinv := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
      have hnn : ((n + 1 : ℕ) : ℝ) ≤ (n₀ : ℝ) + 1 := by
        have : n + 1 ≤ n₀ := hlarge
        have : ((n + 1 : ℕ) : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast this
        linarith
      have h5 : 1 ≤ ((n₀ : ℝ) + 1) * ((n + 1 : ℕ) : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hN0]; linarith
      exact h5.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
    have h6 : Mp ≤ max (2 * Cw) (Mp * (n₀ + 1)) * deltaN d s (n + 1) := by
      calc Mp = Mp * 1 := (mul_one _).symm
        _ ≤ Mp * ((n₀ + 1 : ℝ) * deltaN d s (n + 1)) := mul_le_mul_of_nonneg_left hδ (by linarith)
        _ = (Mp * (n₀ + 1)) * deltaN d s (n + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0
    nlinarith [mul_self_le_mul_self (by linarith : 0 ≤ Mp) h6]

end Final


end MarginalAux

section FinalThm

open HRS.PoleCavityAux HRS.MarginalAux

variable {d : ℕ} {s : ℝ}

/-- Proposition 4.2 `M:A:prop:marginal` (source lines 3664-3672), full-law part of
`A:eq:both-marginals`: `‖dπ_N/dμ - 1‖_{L²(μ)} ≤ C δ_N` for `π_N = Q_{N,β}(μ)^{(1)}`, `N ≥ 2`.
The second summand (the calibrated reference `π_N^R`) is a proof-internal object and is not
specified. -/
theorem firstMarginal_density_L2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        eLpNorm (fun y => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
            (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1) 2
            (withDensityReal ρ) ≤ ENNReal.ofReal (C * deltaN d s N) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨C, hC0, hC⟩ := L2_all hd hs0 hsd hβ hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  refine ⟨C, fun N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn (lam := β / ((n + 1 : ℕ) : ℝ)) rfl
  have hae := rnDeriv_pi_eq hd hs0 hsd hρ hlam hln
  rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (n + 1) (Nat.succ_pos n)]
  refine ⟨?_, ?_⟩
  · rw [firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln]
    exact withDensity_absolutelyContinuous _ _
  · have hN' : 2 ≤ n + 1 := hN
    have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
    have hp0 := pDens_pos hd hs0 hsd hρ hlam hln
    have hz : ∀ y, |pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1| ≤ Mp := by
      intro y
      have h1 := hp0 y
      have h2 := (hMp (n + 1) hN' y).2
      simp only [Nat.add_sub_cancel] at h2
      rw [abs_le]; constructor <;> linarith
    have hmem : MemLp (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1)
        2 (withDensityReal ρ) :=
      MemLp.of_bound (hpm.sub measurable_const).aestronglyMeasurable Mp (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hz y)
    rw [eLpNorm_congr_ae (g := fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n
      (β / ((n + 1 : ℕ) : ℝ)) β y - 1) (hae.mono fun y hy => by simp only [hy])]
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hA := hC n hn (β / ((n + 1 : ℕ) : ℝ)) rfl
    have hδ0 : 0 ≤ deltaN d s (n + 1) := by
      have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
      exact (inv_nonneg.2 hN0.le).trans this
    have e : ∫ y, ‖pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1‖ ^
        (2 : ENNReal).toReal ∂(withDensityReal ρ) =
        ∫ y, (pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1) ^ 2
          ∂(withDensityReal ρ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [e]
    have h3 : (2 : ENNReal).toReal⁻¹ = 1 / 2 := by simp
    rw [h3, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.2 ⟨mul_nonneg hC0 hδ0, hA⟩

/-- Proposition 4.2, last sentence (source line 3672): the first-marginal densities tend to one
uniformly, `‖dπ_N/dμ - 1‖_{L^∞(μ)} → 0`. -/
theorem firstMarginal_density_uniform (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          |((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
              (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1| ≤ ε := by
  have hμ := isProbabilityMeasure_mu hρ
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := sup_dev_small hd hs0 hsd hβ hρ ε hε
  refine ⟨n₀ + 2, fun N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn (lam := β / ((n + 1 : ℕ) : ℝ)) rfl
  have hae := rnDeriv_pi_eq hd hs0 hsd hρ hlam hln
  rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (n + 1) (Nat.succ_pos n)]
  refine ⟨?_, ?_⟩
  · rw [firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln]
    exact withDensity_absolutelyContinuous _ _
  · filter_upwards [hae] with y hy
    rw [hy]
    exact hn₀ n (by omega) hn _ rfl y

end FinalThm


end HRS
