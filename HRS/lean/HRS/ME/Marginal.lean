import HRS.Main.HeadlineEquilibrium
import HRS.Main.EqBiasAux4
import HRS.Equilibrium.L49Aux15

/-!
# Chunk E, packet MARG: the marginal clauses of Proposition 2.10 (fixed-parameter forms)

Proofs of `critical_marginal_expansion_fixed` and `criticalBias_ne_zero_of_nonneg`
(specification in `HRS/ME/MarginalSpec.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Marginal

variable {d : ℕ}

open HRS HRS.Main HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp
  HRS.PDE

/-- `eLpNorm` of an `L²` function is the square root of its second moment. -/
theorem me_marg_eLpNorm_two_eq {μ : Measure (Torus d)} {F : Torus d → ℝ} (hF : MemLp F 2 μ) :
    eLpNorm F 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, F x ^ 2 ∂μ)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hF]
  congr 1
  have e1 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [e1, Real.sqrt_eq_rpow]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_two, sq_abs]
  norm_num

/-- Converse of `CavResp.eLpNorm_two_le`. -/
theorem me_marg_sqrt_le_of_eLpNorm {μ : Measure (Torus d)} {F : Torus d → ℝ} (hF : MemLp F 2 μ)
    {B : ℝ} (hB : 0 ≤ B) (h : eLpNorm F 2 μ ≤ ENNReal.ofReal B) :
    Real.sqrt (∫ x, F x ^ 2 ∂μ) ≤ B := by
  rw [me_marg_eLpNorm_two_eq hF] at h
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h

/-- The insertion defect is measurable (copy of the argument of `eqbias_L2_of_D`). -/
theorem me_marg_measurable_insDefect {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {n : ℕ} (hn0 : 0 < n) {lam : ℝ}
    (hlam : lam = β / ((n + 1 : ℕ) : ℝ)) :
    Measurable (insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
  obtain ⟨hlam0, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn0 hlam
  unfold insDefect
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam0
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hint : Measurable fun x : Torus d => ∫ Y : Config d n, ∑ j, periodicRiesz d s (x - Y j)
      ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
    have : StronglyMeasurable (Function.uncurry fun (x : Torus d) (Y : Config d n) =>
        ∑ j, periodicRiesz d s (x - Y j)) :=
      (Finset.measurable_sum _ fun j _ => hgm.comp (measurable_fst.sub
        ((measurable_pi_apply j).comp measurable_snd))).stronglyMeasurable
    exact (this.integral_prod_right'
      (ν := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)).measurable
  exact (Real.measurable_log.comp (measurable_phiIns hd hs0 hsd hρ hlam0 hln)).add
    (hint.const_mul _)

/-- Glue for one `N ≥ 2`: the cavity expansion, the insertion coefficient and the abstract
inversion step give the `L²` bound with `δ_N` replaced by `log N / N`. -/
theorem me_marg_glue {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (c₀ : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c₀) {N : ℕ} (hN : 2 ≤ N) {Cc Ci : ℝ}
    (hPac : firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
      withDensityReal ρ)
    (hFc : eLpNorm (fun y =>
        ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
            (withDensityReal ρ) y).toReal - 1 +
          β * Kop (periodicRiesz d s) (withDensityReal ρ)
            (fun y' => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
              (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) y -
          projMean (withDensityReal ρ) (insertionDefect d s c₀ β ρ N) y)
        2 (withDensityReal ρ) ≤ ENNReal.ofReal (Cc * Real.sqrt (Real.log N) / N))
    (hzc : ∀ᵐ y ∂(withDensityReal ρ),
        |((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
          (withDensityReal ρ) y).toReal - 1| ≤ Cc * Real.sqrt (deltaN d s N))
    (hDc0 : ∀ x, 0 ≤ insertionDefect d s c₀ β ρ N x ∧
      insertionDefect d s c₀ β ρ N x ≤ Cc * deltaN d s N)
    (hins : ∀ x, |insertionDefect d s c₀ β ρ N x - β ^ 2 * sphereArea d / d * ρ x * deltaN d s N|
      ≤ Ci * Real.sqrt (Real.log N) / N) :
    eLpNorm (fun y =>
        ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
            (withDensityReal ρ) y).toReal - 1 -
          Real.log N / N * (β ^ 2 * sphereArea d / d *
            responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ y))
        2 (withDensityReal ρ) ≤
      ENNReal.ofReal ((|Cc| + |Ci| + |β ^ 2 * sphereArea d / d| *
        Real.sqrt (∫ x, responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ x ^ 2
          ∂(withDensityReal ρ)) / Real.sqrt (Real.log 2)) * Real.sqrt (Real.log N) / N) := by
  have hs0 : 0 ≤ s := by rw [hcrit]; positivity
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  have hμP := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hℓ0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hℓ2 : Real.log 2 ≤ Real.log N := HRS.L49.l49_log_ge hN
  have hNδ : (N : ℝ) * deltaN d s N = 1 + Real.log N := N_mul_deltaN_crit hcrit (by omega)
  have hδpos : 0 < deltaN d s N := by
    have : 0 < (N : ℝ) * deltaN d s N := by rw [hNδ]; linarith
    exact pos_of_mul_pos_right this hN0.le
  have hδ' : deltaN d s N = (1 + Real.log N) / N := by
    rw [eq_div_iff hN0.ne']; linarith [hNδ, mul_comm (N : ℝ) (deltaN d s N)]
  -- the probability measure `P = firstMarginal (Q_N)`
  have hPprob : IsProbabilityMeasure (firstMarginal (modulatedGibbs (periodicRiesz d s) N β
      (withDensityReal ρ))) := by
    have hQ : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) := by
      rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ N (by omega)]
      exact cavity_isProb hd hs0 hsd β hρ N (β / N) (by positivity)
    exact HRS.CavResp.isProb_firstMarginal (by omega : 0 < N) _
  set μ := withDensityReal ρ with hμdef
  set P := firstMarginal (modulatedGibbs (periodicRiesz d s) N β μ) with hPdef
  have h1ℓ : 0 < 1 + Real.log N := by linarith
  have h1ℓne : (1 + Real.log N) ≠ 0 := h1ℓ.ne'
  have hδ' : deltaN d s N = (1 + Real.log N) / N := by
    rw [eq_div_iff hN0.ne']; linarith [hNδ, mul_comm (N : ℝ) (deltaN d s N)]
  have hgen : ∀ C : ℝ, C * Real.sqrt (Real.log N) / (1 + Real.log N) * deltaN d s N =
      C * Real.sqrt (Real.log N) / N := by
    intro C
    rw [hδ']
    field_simp
  -- the density `z₀ = dP/dμ - 1`, its measurability and the clamped version `z`
  have hz0m : Measurable (fun y => (P.rnDeriv μ y).toReal - 1) :=
    ((Measure.measurable_rnDeriv P μ).ennreal_toReal).sub_const 1
  set M : ℝ := |Cc| * Real.sqrt (deltaN d s N) with hM
  have hM0 : 0 ≤ M := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  set z : Torus d → ℝ := fun y => max (-M) (min M ((P.rnDeriv μ y).toReal - 1)) with hz
  have hzm : Measurable z :=
    Measurable.max measurable_const (Measurable.min measurable_const hz0m)
  have hzb : ∀ y, |z y| ≤ M := fun y => by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hzeq : z =ᵐ[μ] fun y => (P.rnDeriv μ y).toReal - 1 := by
    filter_upwards [hzc] with y hy
    have hyM : |(P.rnDeriv μ y).toReal - 1| ≤ M :=
      hy.trans (mul_le_mul_of_nonneg_right (le_abs_self Cc) (Real.sqrt_nonneg _))
    obtain ⟨h1, h2⟩ := abs_le.1 hyM
    simp only [hz]
    rw [min_eq_right h2, max_eq_right h1]
  have hzmem : MemLp z 2 μ := eqbias_memLp_of_bound hzm hzb
  -- the mean of `z` vanishes
  have hPint : Integrable (fun y => (P.rnDeriv μ y).toReal) μ := Measure.integrable_toReal_rnDeriv
  have hint0 : ∫ y, ((P.rnDeriv μ y).toReal - 1) ∂μ = 0 := by
    rw [integral_sub hPint (integrable_const 1), Measure.integral_toReal_rnDeriv hPac]
    simp
  have hz0int : ∫ y, z y ∂μ = 0 := by
    rw [integral_congr_ae hzeq]; exact hint0
  -- the response and the operator
  obtain ⟨Λ, H⟩ := eqbias_KS hd hs0 hsd hρ
  obtain ⟨hm, hp, he⟩ : MemLp (responseInverse (periodicRiesz d s) μ β ρ) 2 μ ∧
      pair μ (responseInverse (periodicRiesz d s) μ β ρ) = 0 ∧
      ∀ᵐ x ∂μ, responseInverse (periodicRiesz d s) μ β ρ x +
        β * Kop (periodicRiesz d s) μ (responseInverse (periodicRiesz d s) μ β ρ) x =
          projMean μ ρ x :=
    eqbias_response hd hs0 hsd hρ hβ.le
  set h := responseInverse (periodicRiesz d s) μ β ρ with hhdef
  have hKz : MemLp (Kop (periodicRiesz d s) μ z) 2 μ := (MFLinear.memLp_Kop H hzmem).1
  -- the insertion defect
  set D : Torus d → ℝ := insertionDefect d s c₀ β ρ N with hD
  have hDm : Measurable D := by
    have hfun : D = fun x => insDefect (periodicRiesz d s) μ (N - 1) (β / N) β x :=
      funext fun x => insertionDefect_eq_insDefect hd hs0 hsd c₀ β hβ hρ hN x
    rw [hfun]
    have hlam : β / (N : ℝ) = β / (((N - 1) + 1 : ℕ) : ℝ) := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ N)]
    exact me_marg_measurable_insDefect hd hs0 hsd hβ hρ (by omega : 0 < N - 1) hlam
  have hDb : ∀ x, |D x| ≤ |Cc| * deltaN d s N := fun x => by
    rw [abs_of_nonneg (hDc0 x).1]
    exact (hDc0 x).2.trans (mul_le_mul_of_nonneg_right (le_abs_self Cc) hδpos.le)
  have hDmem : MemLp D 2 μ := eqbias_memLp_of_bound hDm hDb
  have hprojD : MemLp (projMean μ D) 2 μ := hDmem.sub (memLp_const _)
  have hFm : MemLp (fun x => z x + β * Kop (periodicRiesz d s) μ z x - projMean μ D x) 2 μ :=
    (hzmem.add (hKz.const_mul β)).sub hprojD
  -- identification with the cavity expression
  have hKeq : Kop (periodicRiesz d s) μ z =
      Kop (periodicRiesz d s) μ (fun y => (P.rnDeriv μ y).toReal - 1) :=
    MFLinear.Kop_congr hzeq
  have hFeq : (fun x => z x + β * Kop (periodicRiesz d s) μ z x - projMean μ D x) =ᵐ[μ]
      (fun y => (P.rnDeriv μ y).toReal - 1 +
        β * Kop (periodicRiesz d s) μ (fun y' => (P.rnDeriv μ y').toReal - 1) y -
        projMean μ D y) := by
    filter_upwards [hzeq] with y hy
    rw [hKeq, hy]
  have hF' : eLpNorm (fun x => z x + β * Kop (periodicRiesz d s) μ z x - projMean μ D x) 2 μ ≤
      ENNReal.ofReal (|Cc| * Real.sqrt (Real.log N) / N) :=
    (eLpNorm_congr_ae hFeq).le.trans (hFc.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Cc)
        (Real.sqrt_nonneg _)) hN0.le)))
  have hsqF : Real.sqrt (∫ x, (z x + β * Kop (periodicRiesz d s) μ z x - projMean μ D x) ^ 2 ∂μ) ≤
      |Cc| * Real.sqrt (Real.log N) / N :=
    me_marg_sqrt_le_of_eLpNorm hFm (div_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      hN0.le) hF'
  -- the hypotheses of the abstract inversion step
  have hη0 : 0 ≤ |Cc| * Real.sqrt (Real.log N) / (1 + Real.log N) :=
    div_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) h1ℓ.le
  have hε0 : 0 ≤ |Ci| * Real.sqrt (Real.log N) / (1 + Real.log N) :=
    div_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) h1ℓ.le
  have hFb : Real.sqrt (∫ x, (z x + β * Kop (periodicRiesz d s) μ z x - projMean μ D x) ^ 2 ∂μ) ≤
      |Cc| * Real.sqrt (Real.log N) / (1 + Real.log N) * deltaN d s N := by
    rw [hgen]; exact hsqF
  have hDc : ∀ x, |D x - deltaN d s N * (β ^ 2 * sphereArea d / d) * ρ x| ≤
      |Ci| * Real.sqrt (Real.log N) / (1 + Real.log N) * deltaN d s N := by
    intro x
    have e : deltaN d s N * (β ^ 2 * sphereArea d / d) * ρ x =
        β ^ 2 * sphereArea d / d * ρ x * deltaN d s N := by ring
    rw [e, hgen]
    exact (hins x).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self Ci) (Real.sqrt_nonneg _)) hN0.le)
  have key := eqbias_abstract_step hd hs0 hsd hρ hβ hzm hzb hz0int hDm hDb hδpos
    (β ^ 2 * sphereArea d / d) hη0 hε0 hFm hFb hDc
  -- `L²` bound of the normalised error
  have hAmem : MemLp (fun x => (deltaN d s N)⁻¹ * z x - β ^ 2 * sphereArea d / d * h x) 2 μ :=
    (hzmem.const_mul _).sub (hm.const_mul _)
  have hA := CavResp.eLpNorm_two_le hAmem key
  have hH := CavResp.eLpNorm_two_le hm (le_refl (Real.sqrt (∫ x, h x ^ 2 ∂μ)))
  -- decomposition of the target
  have hG : (fun y => (P.rnDeriv μ y).toReal - 1 -
      Real.log N / N * (β ^ 2 * sphereArea d / d * h y)) =ᵐ[μ]
      (fun y => deltaN d s N * ((deltaN d s N)⁻¹ * z y - β ^ 2 * sphereArea d / d * h y)) +
      (fun y => 1 / (N : ℝ) * (β ^ 2 * sphereArea d / d * h y)) := by
    filter_upwards [hzeq] with y hy
    simp only [Pi.add_apply]
    rw [← hy, hδ']
    field_simp
    ring
  -- assemble the bound
  have hKpos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 (Real.log_pos one_lt_two)
  have hKle : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log N) := Real.sqrt_le_sqrt hℓ2
  have hHnn : 0 ≤ Real.sqrt (∫ x, h x ^ 2 ∂μ) := Real.sqrt_nonneg _
  have hcH : 0 ≤ |β ^ 2 * sphereArea d / d| * Real.sqrt (∫ x, h x ^ 2 ∂μ) :=
    mul_nonneg (abs_nonneg _) hHnn
  have hA1 : eLpNorm (fun y => deltaN d s N * ((deltaN d s N)⁻¹ * z y -
      β ^ 2 * sphereArea d / d * h y)) 2 μ ≤
      ENNReal.ofReal (deltaN d s N *
        (|Cc| * Real.sqrt (Real.log N) / (1 + Real.log N) +
          |Ci| * Real.sqrt (Real.log N) / (1 + Real.log N))) := by
    have e1 := eLpNorm_const_smul (𝕜 := ℝ) (deltaN d s N)
      (fun x => (deltaN d s N)⁻¹ * z x - β ^ 2 * sphereArea d / d * h x) 2 μ
    rw [Real.enorm_eq_ofReal hδpos.le] at e1
    rw [ENNReal.ofReal_mul hδpos.le]
    exact (le_of_eq e1).trans (mul_le_mul_of_nonneg_left hA zero_le)
  have hB2 : eLpNorm (fun y => 1 / (N : ℝ) * (β ^ 2 * sphereArea d / d * h y)) 2 μ ≤
      ENNReal.ofReal (|1 / (N : ℝ) * (β ^ 2 * sphereArea d / d)| *
        Real.sqrt (∫ x, h x ^ 2 ∂μ)) := by
    have e2 : (fun y => 1 / (N : ℝ) * (β ^ 2 * sphereArea d / d * h y)) =
        (1 / (N : ℝ) * (β ^ 2 * sphereArea d / d)) • h := by
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e2, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_left hH zero_le
  have hKey : |1 / (N : ℝ) * (β ^ 2 * sphereArea d / d)| * Real.sqrt (∫ x, h x ^ 2 ∂μ) ≤
      |β ^ 2 * sphereArea d / d| * Real.sqrt (∫ x, h x ^ 2 ∂μ) / Real.sqrt (Real.log 2) *
        Real.sqrt (Real.log N) / N := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
    have h3 : |β ^ 2 * sphereArea d / d| * Real.sqrt (∫ x, h x ^ 2 ∂μ) ≤
        |β ^ 2 * sphereArea d / d| * Real.sqrt (∫ x, h x ^ 2 ∂μ) / Real.sqrt (Real.log 2) *
          Real.sqrt (Real.log N) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hKpos]
      nlinarith [mul_nonneg hcH hKpos.le]
    calc 1 / (N : ℝ) * |β ^ 2 * sphereArea d / d| * Real.sqrt (∫ x, h x ^ 2 ∂μ)
        = (|β ^ 2 * sphereArea d / d| * Real.sqrt (∫ x, h x ^ 2 ∂μ)) / N := by ring
      _ ≤ (|β ^ 2 * sphereArea d / d| * Real.sqrt (∫ x, h x ^ 2 ∂μ) / Real.sqrt (Real.log 2) *
          Real.sqrt (Real.log N)) / N := div_le_div_of_nonneg_right h3 hN0.le
      _ = _ := by ring
  refine (eLpNorm_congr_ae hG).le.trans ((eLpNorm_add_le (by norm_num)).trans ?_)
  refine (add_le_add hA1 hB2).trans ?_
  have hcH' : 0 ≤ |1 / (N : ℝ) * (β ^ 2 * sphereArea d / d)| * Real.sqrt (∫ x, h x ^ 2 ∂μ) :=
    mul_nonneg (abs_nonneg _) hHnn
  rw [← ENNReal.ofReal_add (mul_nonneg hδpos.le (add_nonneg hη0 hε0)) hcH']
  apply ENNReal.ofReal_le_ofReal
  have hsum : deltaN d s N * (|Cc| * Real.sqrt (Real.log N) / (1 + Real.log N) +
      |Ci| * Real.sqrt (Real.log N) / (1 + Real.log N)) =
      |Cc| * Real.sqrt (Real.log N) / N + |Ci| * Real.sqrt (Real.log N) / N := by
    rw [mul_add, mul_comm (deltaN d s N), hgen, mul_comm (deltaN d s N), hgen]
  rw [hsum]
  have e : (|Cc| + |Ci| + |β ^ 2 * sphereArea d / d| * Real.sqrt (∫ x, h x ^ 2 ∂μ) /
      Real.sqrt (Real.log 2)) * Real.sqrt (Real.log N) / N =
      |Cc| * Real.sqrt (Real.log N) / N + |Ci| * Real.sqrt (Real.log N) / N +
        |β ^ 2 * sphereArea d / d| * Real.sqrt (∫ x, h x ^ 2 ∂μ) / Real.sqrt (Real.log 2) *
          Real.sqrt (Real.log N) / N := by ring
  rw [e]
  linarith [hKey]

/-- `c h ρ ∈ L²(dx)` for the response `h ∈ L²(μ)`, `μ = ρ dx` (`ρ` bounded and continuous). -/
theorem me_marg_memLp_vol {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {h : Torus d → ℝ}
    (hmh : MemLp h 2 (withDensityReal ρ)) (c : ℝ) :
    MemLp (fun x => c * h x * ρ x) 2 volume := by
  obtain ⟨g, hg, hhg⟩ := hmh.aestronglyMeasurable
  have hmeas : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
    ENNReal.measurable_ofReal.comp (eqbias_cont hρ).measurable
  have hvol : h =ᵐ[volume] g := by
    have h1 : ∀ᵐ x ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)), h x = g x := hhg
    filter_upwards [(ae_withDensity_iff hmeas).1 h1] with x hx
    exact hx (ENNReal.ofReal_pos.2 (hρ.pos x)).ne'
  have hAEh : AEStronglyMeasurable h volume := ⟨g, hg, hvol⟩
  have hAEf : AEStronglyMeasurable (fun x => c * h x * ρ x) volume :=
    (hAEh.const_mul c).mul (eqbias_cont hρ).aestronglyMeasurable
  have hI2 : Integrable (fun x => h x ^ 2) (withDensityReal ρ) :=
    (memLp_two_iff_integrable_sq hmh.aestronglyMeasurable).1 hmh
  have hI3 : Integrable (fun x => (ENNReal.ofReal (ρ x)).toReal • h x ^ 2) volume :=
    (integrable_withDensity_iff_integrable_smul' hmeas
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).1 hI2
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  have hI4 : Integrable (fun x => (c * h x * ρ x) ^ 2) volume := by
    refine Integrable.mono (hI3.const_mul (c ^ 2 * Λ)) (hAEf.pow 2) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    have hρx := hρ.pos x
    have hnn : 0 ≤ c ^ 2 * h x ^ 2 * ρ x := by positivity
    have key := mul_nonneg hnn (sub_nonneg.2 (hΛ x))
    have hgnn : 0 ≤ c ^ 2 * Λ * (ρ x * h x ^ 2) :=
      mul_nonneg (mul_nonneg (sq_nonneg c) hΛ0.le) (mul_nonneg hρx.le (sq_nonneg _))
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (c * h x * ρ x)), abs_of_nonneg hgnn,
      ENNReal.toReal_ofReal hρx.le, smul_eq_mul]
    nlinarith [key]
  exact (memLp_two_iff_integrable_sq hAEf).2 hI4

/-- The square-summability of the real Fourier coefficients of an `L²` function. -/
theorem me_marg_summable_sq {φ : Torus d → ℝ} (hφ : MemLp φ 2 volume) :
    Summable fun k : NonzeroLattice d => Torus.funRealCoeff φ k ^ 2 := by
  have hT := Torus.hasSum_sq_coeff hφ
  have hTs : Summable (fun n : Lattice d => Torus.cosCoeff φ n ^ 2 + Torus.sinCoeff φ n ^ 2) :=
    hT.summable
  have hTs' : Summable (fun k : NonzeroLattice d =>
      Torus.cosCoeff φ k.1 ^ 2 + Torus.sinCoeff φ k.1 ^ 2) :=
    hTs.comp_injective Subtype.val_injective
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (hTs'.mul_left 2)
  have := Torus.funRealCoeff_sq_add_neg (φ := φ) k
  nlinarith [sq_nonneg (Torus.funRealCoeff φ ⟨-k.1, neg_ne_zero.mpr k.2⟩)]

/-- Proposition 2.10 `M:H:prop:critical` (TeX L1044-1048). -/
theorem critical_marginal_expansion_fixed (hd : 2 ≤ d) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        eLpNorm (fun y =>
            ((firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β
                (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1 -
              Real.log N / N * (β ^ 2 * sphereArea d / d *
                responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ y))
          2 (withDensityReal ρ) ≤ ENNReal.ofReal (C * Real.sqrt (Real.log N) / N) := by
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hc : ∀ z, 0 ≤ periodicRiesz d ((d : ℝ) / 2) z + B := fun z => by linarith [hB z]
  obtain ⟨Cc, hcav⟩ := cavity_response_proof (s := (d : ℝ) / 2) hd rfl β hβ ρ hρ B hc
  obtain ⟨Ci, hins⟩ := insertion_coefficient_proof (s := (d : ℝ) / 2) hd rfl β hβ ρ hρ B hc
  refine ⟨|Cc| + |Ci| + |β ^ 2 * sphereArea d / d| *
      Real.sqrt (∫ x, responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ x ^ 2
        ∂(withDensityReal ρ)) / Real.sqrt (Real.log 2), fun N hN => ?_⟩
  obtain ⟨hx, ⟨hP, -, -⟩, hF, -, hz⟩ := hcav N hN
  refine ⟨hP, ?_⟩
  exact me_marg_glue hd rfl hβ hρ B hc hN hP hF hz (fun x => ⟨(hx x).2.2.1, (hx x).2.2.2.2⟩)
    (hins N hN)

/-- Proposition 2.10 `M:H:prop:critical` (TeX L1051-1052), for `m ≥ 0`. -/
theorem criticalBias_ne_zero_of_nonneg (hd : 2 ≤ d) (β : ℝ) (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (hnc : ∃ x y, ρ x ≠ ρ y) (m : ℝ) (hm : 0 ≤ m) :
    criticalBias d ((d : ℝ) / 2) β m ρ ≠ 0 := by
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hpos := eqbias_bias_pos hd hs0 hsd hρ hβ.le hnc
  obtain ⟨hmh, hp, -⟩ := eqbias_response hd hs0 hsd hρ hβ.le
  set h := responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ with hhdef
  set c : ℝ := β ^ 2 * sphereArea d / d with hcdef
  have hc0 : c ≠ 0 := by
    have hS : 0 < sphereArea d := HRS.StaticLimitsAux.sphereArea_pos hd
    have hd0 : (0 : ℝ) < d := by linarith
    have hβ2 : 0 < β ^ 2 := by positivity
    rw [hcdef]
    positivity
  have hρc : Continuous ρ := eqbias_cont hρ
  have hmeas : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
    ENNReal.measurable_ofReal.comp hρc.measurable
  have hfin : ∀ᵐ x ∂volume, ENNReal.ofReal (ρ x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  set f : Torus d → ℝ := fun x => c * h x * ρ x with hfdef
  have hfL2 : MemLp f 2 volume := me_marg_memLp_vol hρ hmh c
  have hsum := me_marg_summable_sq hfL2
  have hp' : ∫ x, h x ∂(withDensityReal ρ) = 0 := hp
  -- the Fourier coefficients of `f` vanish
  intro hzero
  unfold criticalBias NegSobolev.ofFun at hzero
  set F : NonzeroLattice d → ℝ := fun k => Torus.funRealCoeff f k with hF
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * F k) 2 := by
    rw [Torus.memℓp_two_iff]
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hsum
    have h1 : Lattice.jp k.1 ^ (-m) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one k.1) (by linarith)
    have h0 : 0 ≤ Lattice.jp k.1 ^ (-m) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
    have e : (Lattice.jp k.1 ^ (-m) * F k) ^ 2 = (Lattice.jp k.1 ^ (-m)) ^ 2 * F k ^ 2 := by ring
    rw [e]
    have h2 : (Lattice.jp k.1 ^ (-m)) ^ 2 ≤ 1 := by nlinarith
    show (Lattice.jp k.1 ^ (-m)) ^ 2 * F k ^ 2 ≤ Torus.funRealCoeff f k ^ 2
    nlinarith [sq_nonneg (F k)]
  have hcoef : ∀ k : NonzeroLattice d, Torus.funRealCoeff f k = 0 := by
    intro k
    have e1 : NegSobolev.fourierCoeff (NegSobolev.ofSeq m F) k = Torus.funRealCoeff f k := by
      unfold NegSobolev.fourierCoeff
      rw [NegSobolev.coord_ofSeq_of_mem F hmem k, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
      simp
      rfl
    have e2 : NegSobolev.fourierCoeff (NegSobolev.ofSeq m F) k = 0 := by
      have hc0' : NegSobolev.coord (0 : NegSobolev d m) k = 0 := rfl
      rw [hzero]
      simp only [NegSobolev.fourierCoeff, hc0', mul_zero]
    rw [← e1, e2]
  -- the mean of `f` vanishes, hence `∫ f² dx = 0`
  have hconv : ∫ x, h x * ρ x ∂volume = ∫ x, h x ∂(withDensityReal ρ) := by
    rw [withDensityReal, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ.density.nonneg x)]
    ring
  have hmean : Torus.mean f = 0 := by
    unfold Torus.mean
    have e : ∫ x, f x ∂volume = c * ∫ x, h x * ρ x ∂volume := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hfdef]; ring)
    rw [e, hconv, hp', mul_zero]
  have hsq : ∫ x, f x ^ 2 ∂volume = 0 := by
    rw [Torus.parseval_realCoeff f hfL2, hmean]
    have : ∑' k : NonzeroLattice d, Torus.funRealCoeff f k ^ 2 = 0 := by
      simp [hcoef]
    rw [this]; ring
  have hf0 : f =ᵐ[volume] 0 := by
    have hI : Integrable (fun x => f x ^ 2) volume :=
      (memLp_two_iff_integrable_sq hfL2.aestronglyMeasurable).1 hfL2
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hI).1 hsq
    filter_upwards [hz] with x hx
    have hx' : f x ^ 2 = 0 := hx
    exact pow_eq_zero_iff two_ne_zero |>.1 hx'
  -- hence `∫ h ρ dμ = 0`, contradicting positivity
  have hzero2 : ∫ x, h x * ρ x ∂(withDensityReal ρ) = 0 := by
    rw [withDensityReal, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
    have hae : (fun x => (ENNReal.ofReal (ρ x)).toReal • (h x * ρ x)) =ᵐ[volume] 0 := by
      filter_upwards [hf0] with x hx
      have hx' : f x = 0 := hx
      have h1 : c * (h x * ρ x) = 0 := by
        have e : f x = c * (h x * ρ x) := by simp only [hfdef]; ring
        rw [← e]; exact hx'
      have h2 : h x * ρ x = 0 := (mul_eq_zero.1 h1).resolve_left hc0
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ.density.nonneg x), Pi.zero_apply]
      rw [h2, mul_zero]
    rw [integral_congr_ae hae]
    simp
  linarith

end HRS.ME.Marginal

end
