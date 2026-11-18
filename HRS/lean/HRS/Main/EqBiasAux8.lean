import HRS.Main.EqBiasAux7
import HRS.Equilibrium.CavityMain

/-!
# EQ-BIAS, S5: the empirical potential under the pole laws is close to its mean-field value

`eqbias_field_small`: `sup_{x,t,y} E_{P_{x,t}} |v_Y(y)| → 0`, `v_Y(y) = λ ∑_{j≠i} g_+(y-y_j) - β g_+*μ(y)`,
by truncation `g_+ ∧ H`: variance of the bounded part (`var_fracF_le`), mean via `pole_dual` and the
`L²` closeness of the cavity marginal to `μ`, and the one-particle density bound for the tail.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ} {s : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.PDE

/-- The truncation tail `∫ (g_+ - g_+ ∧ H) → 0`. -/
theorem eqbias_tail_small (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∀ ε : ℝ, 0 < ε → ∃ H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H →
      ∫ w : Torus d, (gPlus d s c w - min (gPlus d s c w) H) ≤ ε := by
  intro ε hε
  have hgi : Integrable (gPlus d s c) (volume : Measure (Torus d)) :=
    (MFOneLe.integrable_periodicRiesz (by omega) s hs0 hsd).add (integrable_const c)
  have hgm : Measurable (gPlus d s c) := measurable_gPlus hd hs0 hsd c
  have hlim : Tendsto (fun H : ℝ => ∫ w : Torus d, (gPlus d s c w - min (gPlus d s c w) H))
      atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Torus d)))
      (F := fun (H : ℝ) (w : Torus d) => gPlus d s c w - min (gPlus d s c w) H)
      (f := fun _ => 0) (bound := fun w => |gPlus d s c w|) (l := atTop)
      (Eventually.of_forall fun H => (hgm.sub (hgm.min measurable_const)).aestronglyMeasurable)
      (eventually_atTop.2 ⟨0, fun H hH => Eventually.of_forall fun w => ?_⟩)
      hgi.abs ?_
    · simpa using this
    · have h0 : 0 ≤ gPlus d s c w := hc w
      rw [Real.norm_eq_abs, abs_of_nonneg (by simp [h0, le_refl]), abs_of_nonneg h0]
      have : 0 ≤ min (gPlus d s c w) H := le_min h0 hH
      linarith
    · refine Eventually.of_forall fun w => ?_
      refine tendsto_const_nhds.congr' ?_
      rw [EventuallyEq, eventually_atTop]
      exact ⟨gPlus d s c w, fun H hH => by simp [min_eq_left hH]⟩
  obtain ⟨H₀, hH₀⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
  refine ⟨H₀, fun H hH => ?_⟩
  have := hH₀ H hH
  rw [Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

/-- The truncation tail against `μ`, uniformly in `y`. -/
theorem eqbias_tail_mu (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∀ ε : ℝ, 0 < ε → ∃ H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H → ∀ y : Torus d,
      ∫ z, (gPlus d s c (y - z) - min (gPlus d s c (y - z)) H) ∂(withDensityReal ρ) ≤ ε := by
  intro ε hε
  haveI : (volume : Measure (Torus d)).IsNegInvariant := MFLinear.negInv
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  obtain ⟨H₀, hH₀⟩ := eqbias_tail_small hd hs0 hsd c hc (ε / Λ) (by positivity)
  refine ⟨max H₀ 0, fun H hH y => ?_⟩
  have hgi : Integrable (gPlus d s c) (volume : Measure (Torus d)) :=
    (MFOneLe.integrable_periodicRiesz (by omega) s hs0 hsd).add (integrable_const c)
  have hgm : Measurable (gPlus d s c) := measurable_gPlus hd hs0 hsd c
  have hH0 : 0 ≤ H := (le_max_right _ _).trans hH
  set r : Torus d → ℝ := fun w => gPlus d s c w - min (gPlus d s c w) H with hr
  have hrm : Measurable r := hgm.sub (hgm.min measurable_const)
  have hr0 : ∀ w, 0 ≤ r w := fun w => by
    simp only [hr]; linarith [min_le_left (gPlus d s c w) H]
  have hrle : ∀ w, r w ≤ gPlus d s c w := fun w => by
    have h0 : 0 ≤ gPlus d s c w := hc w
    have : 0 ≤ min (gPlus d s c w) H := le_min h0 hH0
    simp only [hr]; linarith
  have hri : Integrable r (volume : Measure (Torus d)) :=
    Integrable.mono' hgi hrm.aestronglyMeasurable (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hr0 w)]; exact hrle w)
  have e1 : ∫ z, (gPlus d s c (y - z) - min (gPlus d s c (y - z)) H) ∂(withDensityReal ρ) =
      ∫ z, ρ z * r (y - z) :=
    integral_withDensityReal_eq ρ hρ.density.measurable hρ.density.nonneg (fun z => r (y - z))
  rw [e1]
  have h2 : ∫ z, ρ z * r (y - z) ≤ ∫ z, Λ * r (y - z) :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => mul_nonneg (hρ.density.nonneg z) (hr0 _))
      ((hri.comp_sub_left y).const_mul Λ)
      (Eventually.of_forall fun z => mul_le_mul_of_nonneg_right (hΛ z) (hr0 _))
  rw [integral_const_mul, integral_sub_left_eq_self r (volume : Measure (Torus d)) y] at h2
  have h3 := hH₀ H ((le_max_left _ _).trans hH)
  have h4 : Λ * ∫ w, r w ≤ Λ * (ε / Λ) := mul_le_mul_of_nonneg_left h3 hΛ0.le
  have h5 : Λ * (ε / Λ) = ε := by field_simp
  linarith

/-- Mean of a bounded test function under a pole law, against `μ`. -/
theorem eqbias_pole_mean (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ n : ℕ, 0 < n → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f → ∀ K : ℝ, 0 ≤ K → (∀ y, |f y| ≤ K) →
      |∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n
            (β / ((n + 1 : ℕ) : ℝ)) β x t)) - ∫ y, f y ∂(withDensityReal ρ)| ≤
        Cm * K * (Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) + deltaN d s (n + 1)) := by
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨Cd, hCd0, hCd⟩ := pole_dual hd hs0 hsd hβ hρ
  obtain ⟨CL, hCL0, hCL⟩ := cavity_L2 hd hs0 hsd hβ hρ
  obtain ⟨C2, hC20, hC2⟩ := L2_all hd hs0 hsd hβ hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  refine ⟨Cd + CL + C2, by positivity, fun n hn x t ht f hfm K hK hf => ?_⟩
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlamdef
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  set δ := deltaN d s (n + 1) with hδ
  have hδ0 : 0 ≤ δ := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hsq0 : 0 ≤ Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := Real.sqrt_nonneg _
  have hfmem : MemLp f 2 (withDensityReal ρ) := eqbias_memLp_of_bound hfm hf
  have hfi : Integrable f (withDensityReal ρ) := hfmem.integrable one_le_two
  have hf2 : Real.sqrt (∫ y, f y ^ 2 ∂(withDensityReal ρ)) ≤ K := by
    refine Real.sqrt_le_iff.2 ⟨hK, ?_⟩
    calc ∫ y, f y ^ 2 ∂(withDensityReal ρ) ≤ ∫ _y, K ^ 2 ∂(withDensityReal ρ) :=
          integral_mono hfmem.integrable_sq (integrable_const _) fun y => by
            have := hf y
            nlinarith [abs_nonneg (f y), sq_abs (f y)]
      _ = K ^ 2 := by simp
  -- pole versus cavity
  have h1 : |∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)) -
      ∫ y, f y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β))| ≤
      Cd * Real.sqrt (∫ y, f y ^ 2 ∂(withDensityReal ρ)) * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) :=
    hCd (n + 1) hN x t ht f hfm K hf
  have h1' : |∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)) -
      ∫ y, f y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β))| ≤
      Cd * K * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := by
    refine h1.trans ?_
    have := mul_le_mul_of_nonneg_left hf2 hCd0
    nlinarith [mul_le_mul_of_nonneg_right this hsq0]
  -- cavity versus `μ`
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := (hMq (n + 1) hN).1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ),
      qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := (hMq (n + 1) hN).2
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  haveI hcav := cavity_isProb hd hs0 hsd β hρ n lam hlam
  haveI hν := isProb_firstMarginal hn (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)
  obtain ⟨hqi, hq1, hqeq⟩ := dens_facts hac
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  have hint : ∫ y, f y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)) =
      ∫ y, q y * f y ∂(withDensityReal ρ) := by
    have hqeq' : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) =
        (withDensityReal ρ).withDensity fun y => ENNReal.ofReal (q y) := hqeq
    calc _ = ∫ y, f y ∂((withDensityReal ρ).withDensity fun y => ENNReal.ofReal (q y)) := by
          rw [← hqeq']
      _ = _ := integral_withDensity_real hqm hq0 f
  have hp0 : ∀ y, 0 < p y := pDens_pos hd hs0 hsd hρ hlam hln
  have hpb : ∀ y, p y ≤ Mp := fun y => (hMp (n + 1) hN y).2
  have hqmem : MemLp (fun y => q y - p y) 2 (withDensityReal ρ) := by
    refine MemLp.of_bound (hqm.sub hpm).aestronglyMeasurable (Mq + Mp) ?_
    filter_upwards [hqb] with y hy
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hq0 y, hp0 y, hpb y]
  have hpmem : MemLp (fun y => p y - 1) 2 (withDensityReal ρ) :=
    eqbias_memLp_of_bound (hpm.sub measurable_const) (M := Mp) (fun y => by
      rw [abs_le]; constructor <;> linarith [hp0 y, hpb y, hMp1])
  have hL0 := hCL n hn lam hlamdef
  have hL : Real.sqrt (∫ y, (q y - p y) ^ 2 ∂(withDensityReal ρ)) ≤
      CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := by
    refine le_trans (le_of_eq ?_) hL0
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)
  have hC2' : Real.sqrt (∫ y, (p y - 1) ^ 2 ∂(withDensityReal ρ)) ≤ C2 * δ :=
    Real.sqrt_le_iff.2 ⟨by positivity, by simpa using hC2 n hn lam hlamdef⟩
  have hsum := sqrt_int_add_le hqmem hpmem
  have hqp : ∀ y, (q y - p y) + (p y - 1) = q y - 1 := fun y => by ring
  have hsum2 : Real.sqrt (∫ y, (q y - 1) ^ 2 ∂(withDensityReal ρ)) ≤
      Real.sqrt (∫ y, (q y - p y) ^ 2 ∂(withDensityReal ρ)) +
        Real.sqrt (∫ y, (p y - 1) ^ 2 ∂(withDensityReal ρ)) := by
    have e : ∫ y, (q y - 1) ^ 2 ∂(withDensityReal ρ) =
        ∫ y, ((q y - p y) + (p y - 1)) ^ 2 ∂(withDensityReal ρ) :=
      integral_congr_ae (Eventually.of_forall fun y => by ring)
    rw [e]; exact hsum
  have hqmem1 : MemLp (fun y => q y - 1) 2 (withDensityReal ρ) := by
    have e : (fun y => q y - 1) = (fun y => q y - p y) + (fun y => p y - 1) := by
      funext y; simp only [Pi.add_apply]; ring
    rw [e]; exact hqmem.add hpmem
  have hcs := EF.cs_integral hfmem hqmem1
  have hfq : ∫ y, q y * f y ∂(withDensityReal ρ) - ∫ y, f y ∂(withDensityReal ρ) =
      ∫ y, f y * (q y - 1) ∂(withDensityReal ρ) := by
    have hqf : Integrable (fun y => q y * f y) (withDensityReal ρ) :=
      Integrable.mono' (hqi.mul_const K) (hqm.mul hfm).aestronglyMeasurable
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 y)]
          exact mul_le_mul_of_nonneg_left (hf y) (hq0 y))
    rw [← integral_sub hqf hfi]
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)
  have hmid : |∫ y, f y * (q y - 1) ∂(withDensityReal ρ)| ≤
      K * (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + C2 * δ) := by
    have hA : 0 ≤ ∫ y, f y ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun y => sq_nonneg _
    have hB : 0 ≤ ∫ y, (q y - 1) ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun y => sq_nonneg _
    have h2 : |∫ y, f y * (q y - 1) ∂(withDensityReal ρ)| ≤
        Real.sqrt (∫ y, f y ^ 2 ∂(withDensityReal ρ)) *
          Real.sqrt (∫ y, (q y - 1) ^ 2 ∂(withDensityReal ρ)) := by
      rw [← Real.sqrt_mul hA]
      exact Real.abs_le_sqrt hcs
    refine h2.trans ?_
    have h3 : Real.sqrt (∫ y, (q y - 1) ^ 2 ∂(withDensityReal ρ)) ≤
        CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + C2 * δ := by
      refine hsum2.trans ?_
      exact add_le_add hL hC2'
    exact mul_le_mul hf2 h3 (Real.sqrt_nonneg _) hK
  have hfin : |∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)) -
      ∫ y, f y ∂(withDensityReal ρ)| ≤
      |∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)) -
        ∫ y, f y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β))| +
      |∫ y, f y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)) -
        ∫ y, f y ∂(withDensityReal ρ)| := by
    have := abs_sub_le (∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)))
      (∫ y, f y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)))
      (∫ y, f y ∂(withDensityReal ρ))
    exact this
  have hBC : |∫ y, f y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)) -
      ∫ y, f y ∂(withDensityReal ρ)| ≤
      K * (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + C2 * δ) := by
    rw [hint, hfq]; exact hmid
  have e1 := mul_nonneg hCd0 (mul_nonneg hK hδ0)
  have e2 := mul_nonneg hCL0 (mul_nonneg hK hδ0)
  have e3 := mul_nonneg hC20 (mul_nonneg hK hsq0)
  have hfinal : Cd * K * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) +
      K * (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + C2 * δ) ≤
      (Cd + CL + C2) * K * (Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + δ) := by nlinarith
  linarith [hfin, h1', hBC, hfinal]

theorem eqbias_gTrunc_bounds {H : ℝ} (hH : 0 ≤ H) {c : ℝ} (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (z : Torus d) :
    0 ≤ gTrunc d s c H z ∧ gTrunc d s c H z ≤ H ∧ gTrunc d s c H z ≤ gPlus d s c z := by
  unfold gTrunc
  exact ⟨le_min (hc z) hH, min_le_right _ _, min_le_left _ _⟩

set_option maxHeartbeats 3200000 in
/-- The `H`-dependent `L¹` bound for the cavity field under the pole law. -/
theorem eqbias_field_L1_H (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ Cv Cm M1 : ℝ, 0 ≤ Cv ∧ 0 ≤ Cm ∧ 0 ≤ M1 ∧ ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ x : Torus d,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d, ∀ H : ℝ, 0 ≤ H →
      Integrable (fun Y => |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y|)
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
      ∫ Y, |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y|
        ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
        β * H * Real.sqrt (Cv / ((N - 1 : ℕ) : ℝ)) +
          β * Cm * H * (Real.sqrt (deltaN d s N / (N : ℝ)) + deltaN d s N) +
          2 * (β / N) * H +
          β * (1 + M1) * ∫ z, (gPlus d s c (y - z) - min (gPlus d s c (y - z)) H) ∂(withDensityReal ρ) := by
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨C1, hC1, hvar⟩ := PoleCavityAux.pole_variance_clause hd hs0 hsd β hβ ρ hρ
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  obtain ⟨Cm0, hCm0, hCm⟩ := eqbias_pole_mean hd hs0 hsd hβ hρ
  obtain ⟨M1, hM1, hMarg⟩ := pole_marg_le hd hs0 hsd hβ hρ
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  refine ⟨C1 * Real.exp (β * B), Cm0, M1, by positivity, hCm0, hM1.le, ?_⟩
  intro N hN x t ht y H hH0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : 0 < N - 1 := by omega
  have hn' : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by
    rw [hn']
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlam : 0 ≤ β / N := by positivity
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  set P := poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t with hP
  set ν := firstMarginal P with hν
  have hgm := PoleCavityAux.measurable_gPlus hd hs0 hsd c
  set f : Torus d → ℝ := fun z => gTrunc d s c H (y - z) with hf
  have hfm : Measurable f := (hgm.comp (measurable_const.sub measurable_id)).min measurable_const
  have hf0 : ∀ z, 0 ≤ f z := fun z => (eqbias_gTrunc_bounds hH0 hc (y - z)).1
  have hfH : ∀ z, f z ≤ H := fun z => (eqbias_gTrunc_bounds hH0 hc (y - z)).2.1
  have hfG : ∀ z, f z ≤ gPlus d s c (y - z) := fun z => (eqbias_gTrunc_bounds hH0 hc (y - z)).2.2
  have hfb : ∀ z, |f z| ≤ H := fun z => by rw [abs_of_nonneg (hf0 z)]; exact hfH z
  set r : Torus d → ℝ := fun z => gPlus d s c (y - z) - gTrunc d s c H (y - z) with hr
  have hr0 : ∀ z, 0 ≤ r z := fun z => sub_nonneg.2 (hfG z)
  have hrm : Measurable r :=
    (hgm.comp (measurable_const.sub measurable_id)).sub
      ((hgm.comp (measurable_const.sub measurable_id)).min measurable_const)
  have hGfr : ∀ z, gPlus d s c (y - z) = f z + r z := fun z => by simp only [hf, hr]; ring
  set h := convMeasure (gPlus d s c) (withDensityReal ρ) y with hh
  set A : Config d (N - 1) → ℝ := fun Y => (β / N) * ((N - 1 : ℕ) : ℝ) * fracF f Y with hA
  set EA : ℝ := (β / N) * ((N - 1 : ℕ) : ℝ) * ∫ z, f z ∂ν with hEA
  set R : Config d (N - 1) → ℝ := fun Y => (β / N) * ∑ j, r (Y j) with hR
  -- pointwise bound
  have hpt : ∀ Y : Config d (N - 1), |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y| ≤
      |A Y - EA| + |EA - β * h| + (β / N) * H + R Y := by
    intro Y
    have e1 : ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), gPlus d s c (y - Y j) =
        (∑ j, f (Y j)) - f (Y ⟨0, hn⟩) + ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) := by
      rw [Finset.sum_congr rfl (fun j _ => hGfr (Y j)), Finset.sum_add_distrib,
        Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    have e2 : A Y = (β / N) * ∑ j, f (Y j) := by
      simp only [hA]; unfold fracF
      have : ((N - 1 : ℕ) : ℝ) ≠ 0 := hn0.ne'
      field_simp
    have e3 : cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y =
        (A Y - EA) + (EA - β * h) - (β / N) * f (Y ⟨0, hn⟩) +
          (β / N) * ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) := by
      unfold cavityField
      rw [e1, ← hh, e2]; ring
    rw [e3]
    have hr1 : 0 ≤ ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) :=
      Finset.sum_nonneg fun j _ => hr0 _
    have hr2 : ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) ≤ ∑ j, r (Y j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ => hr0 _
    have h3 : (β / N) * f (Y ⟨0, hn⟩) ≤ (β / N) * H := mul_le_mul_of_nonneg_left (hfH _) hlam
    have h3' : 0 ≤ (β / N) * f (Y ⟨0, hn⟩) := mul_nonneg hlam (hf0 _)
    have h4 : (β / N) * ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) ≤ R Y :=
      mul_le_mul_of_nonneg_left hr2 hlam
    have h4' : 0 ≤ (β / N) * ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) :=
      mul_nonneg hlam hr1
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (A Y - EA), neg_abs_le (EA - β * h), le_abs_self (A Y - EA),
      le_abs_self (EA - β * h)]
  have hvm : Measurable fun Y : Config d (N - 1) =>
      cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y := by
    unfold cavityField
    exact ((Finset.measurable_sum _ fun j _ =>
      hgm.comp (measurable_const.sub (measurable_pi_apply j))).const_mul _).sub measurable_const
  have hfrm : Measurable (fracF (n := N - 1) f) := measurable_fracF hfm
  have hmem : MemLp (fracF (n := N - 1) f) 2 P :=
    MemLp.of_bound hfrm.aestronglyMeasurable H (Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs]; exact abs_fracF_le hn hfb Y)
  have hfrint : Integrable (fracF (n := N - 1) f) P := hmem.integrable (by norm_num)
  have hEF : ∫ Y, fracF f Y ∂P = ∫ z, f z ∂ν :=
    integral_fracF hn hfm hfb P (poleLaw_exchangeable hd hs0 hsd β hρ (N - 1) (β / N) hlam x t)
  have hc0 : 0 ≤ (β / N) * ((N - 1 : ℕ) : ℝ) := by positivity
  have hc1 : (β / N) * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [hn', div_mul_eq_mul_div, div_le_iff₀ hN0]; nlinarith
  have hAEA : ∀ Y, A Y - EA =
      (β / N) * ((N - 1 : ℕ) : ℝ) * (fracF f Y - ∫ Y', fracF f Y' ∂P) := by
    intro Y; rw [hEF]; simp only [hA, hEA]; ring
  have hI1 : Integrable (fun Y => |A Y - EA|) P :=
    (((hfrint.const_mul ((β / N) * ((N - 1 : ℕ) : ℝ))).sub (integrable_const EA))).abs
  -- T1
  have hT1 : ∫ Y, |A Y - EA| ∂P ≤ β * H * Real.sqrt (C1 * Real.exp (β * B) / ((N - 1 : ℕ) : ℝ)) := by
    have e1 : ∫ Y, |A Y - EA| ∂P =
        (β / N) * ((N - 1 : ℕ) : ℝ) * ∫ Y, |fracF f Y - ∫ Y', fracF f Y' ∂P| ∂P := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
      show |A Y - EA| = _
      rw [hAEA Y, abs_mul, abs_of_nonneg hc0]
    have e2 := l1_le_sqrt_var hmem
    have hvar' := var_fracF_le hd hs0 hsd hβ hρ hC1 hvar hB0 hB hN x ht hfm hfb
    have hf2 : ∫ z, f z ^ 2 ∂(withDensityReal ρ) ≤ H ^ 2 := by
      calc ∫ z, f z ^ 2 ∂(withDensityReal ρ) ≤ ∫ _z, H ^ 2 ∂(withDensityReal ρ) :=
            integral_mono (eqbias_memLp_of_bound hfm hfb).integrable_sq (integrable_const _)
              fun z => by nlinarith [abs_nonneg (f z), sq_abs (f z), hfb z]
        _ = H ^ 2 := by simp
    have hVar : Var[fracF (n := N - 1) f; P] ≤ C1 * Real.exp (β * B) * H ^ 2 / ((N - 1 : ℕ) : ℝ) := by
      refine hvar'.trans ?_
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf2 (by positivity)) hn0.le
    have e3 : Real.sqrt (Var[fracF (n := N - 1) f; P]) ≤
        H * Real.sqrt (C1 * Real.exp (β * B) / ((N - 1 : ℕ) : ℝ)) := by
      refine (Real.sqrt_le_sqrt hVar).trans (le_of_eq ?_)
      rw [show C1 * Real.exp (β * B) * H ^ 2 / ((N - 1 : ℕ) : ℝ) =
        H ^ 2 * (C1 * Real.exp (β * B) / ((N - 1 : ℕ) : ℝ)) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hH0]
    rw [e1]
    have := mul_le_mul hc1 (e2.trans e3) (integral_nonneg fun Y => abs_nonneg _) hβ.le
    linarith
  -- the tail `r`
  have hGi : Integrable (fun z => gPlus d s c (y - z)) (withDensityReal ρ) := by
    obtain ⟨B', Cc', hB0', hK'⟩ := kerData_periodicRiesz hd hs0 hsd hρ
    exact (hK'.int y).add (integrable_const c)
  have hfi : Integrable f (withDensityReal ρ) := (eqbias_memLp_of_bound hfm hfb).integrable one_le_two
  have hri : Integrable r (withDensityReal ρ) :=
    Integrable.mono' hGi hrm.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hr0 z)]
      have : 0 ≤ f z := hf0 z
      have := hGfr z
      linarith)
  have hhsplit : h = ∫ z, f z ∂(withDensityReal ρ) + ∫ z, r z ∂(withDensityReal ρ) := by
    rw [← integral_add hfi hri]
    show ∫ z, gPlus d s c (y - z) ∂(withDensityReal ρ) = _
    exact integral_congr_ae (Eventually.of_forall fun z => hGfr z)
  have hrmu : ∫⁻ z, ENNReal.ofReal (r z) ∂(withDensityReal ρ) =
      ENNReal.ofReal (∫ z, r z ∂(withDensityReal ρ)) :=
    (ofReal_integral_eq_lintegral_ofReal hri (Eventually.of_forall hr0)).symm
  have hηr : 0 ≤ ∫ z, r z ∂(withDensityReal ρ) := integral_nonneg hr0
  obtain ⟨hac1, hmap⟩ := hMarg N hN x t ht
  have hR0 : ∀ Y, 0 ≤ R Y := fun Y => mul_nonneg hlam (Finset.sum_nonneg fun j _ => hr0 _)
  have hRm : Measurable R :=
    (Finset.measurable_sum _ fun j _ => hrm.comp (measurable_pi_apply j)).const_mul _
  have hRlint : ∫⁻ Y, ENNReal.ofReal (R Y) ∂P ≤
      ENNReal.ofReal (β * M1 * ∫ z, r z ∂(withDensityReal ρ)) := by
    have e1 : ∀ Y : Config d (N - 1), ENNReal.ofReal (R Y) =
        ∑ j, ENNReal.ofReal ((β / N) * r (Y j)) := fun Y => by
      simp only [hR]
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg hlam (hr0 _)]
    have hφm : Measurable fun z => ENNReal.ofReal ((β / N) * r z) :=
      ENNReal.measurable_ofReal.comp (hrm.const_mul _)
    have e2 : ∀ j : Fin (N - 1), ∫⁻ Y, ENNReal.ofReal ((β / N) * r (Y j)) ∂P ≤
        ENNReal.ofReal M1 * (ENNReal.ofReal (β / N) * ENNReal.ofReal (∫ z, r z ∂(withDensityReal ρ))) :=
      fun j => by
        rw [← lintegral_map hφm (measurable_pi_apply j)]
        calc _ ≤ ∫⁻ z, ENNReal.ofReal ((β / N) * r z) ∂(ENNReal.ofReal M1 • withDensityReal ρ) :=
              lintegral_mono' (hmap j) le_rfl
          _ = ENNReal.ofReal M1 * ∫⁻ z, ENNReal.ofReal ((β / N) * r z) ∂(withDensityReal ρ) :=
              lintegral_smul_measure _ _
          _ ≤ _ := by
              refine mul_le_mul' le_rfl ?_
              simp_rw [ENNReal.ofReal_mul hlam]
              rw [lintegral_const_mul _ (show Measurable fun z => ENNReal.ofReal (r z) from
                ENNReal.measurable_ofReal.comp hrm), hrmu]
    calc ∫⁻ Y, ENNReal.ofReal (R Y) ∂P = ∫⁻ Y, ∑ j, ENNReal.ofReal ((β / N) * r (Y j)) ∂P :=
          lintegral_congr e1
      _ = ∑ j, ∫⁻ Y, ENNReal.ofReal ((β / N) * r (Y j)) ∂P :=
          lintegral_finset_sum _ fun j _ => hφm.comp (measurable_pi_apply j)
      _ ≤ ∑ _j : Fin (N - 1), ENNReal.ofReal M1 *
            (ENNReal.ofReal (β / N) * ENNReal.ofReal (∫ z, r z ∂(withDensityReal ρ))) :=
          Finset.sum_le_sum fun j _ => e2 j
      _ = ENNReal.ofReal (((N - 1 : ℕ) : ℝ) * (M1 * ((β / N) * ∫ z, r z ∂(withDensityReal ρ)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_mul hM1.le, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc ((N - 1 : ℕ) : ℝ) * (M1 * ((β / N) * ∫ z, r z ∂(withDensityReal ρ)))
              = (((N - 1 : ℕ) : ℝ) * (β / N)) * (M1 * ∫ z, r z ∂(withDensityReal ρ)) := by ring
            _ ≤ β * (M1 * ∫ z, r z ∂(withDensityReal ρ)) :=
                mul_le_mul_of_nonneg_right (by linarith [hc1, mul_comm ((N - 1 : ℕ) : ℝ) (β / N)])
                  (by positivity)
            _ = _ := by ring
  obtain ⟨hRi, hRle⟩ := integ_of_lint hRm hR0 (by positivity) hRlint
  -- T2
  have hN1 : N - 1 + 1 = N := by omega
  have hm := hCm (N - 1) hn x t ht f hfm H hH0 hfb
  rw [hN1] at hm
  have hT2 : |EA - β * h| ≤ β * Cm0 * H * (Real.sqrt (deltaN d s N / (N : ℝ)) + deltaN d s N) +
      (β / N) * H + β * ∫ z, r z ∂(withDensityReal ρ) := by
    have hf1 : ∫ z, f z ∂(withDensityReal ρ) ≤ H := by
      calc ∫ z, f z ∂(withDensityReal ρ) ≤ ∫ _z, H ∂(withDensityReal ρ) :=
            integral_mono hfi (integrable_const _) hfH
        _ = H := by simp
    have hf1' : 0 ≤ ∫ z, f z ∂(withDensityReal ρ) := integral_nonneg hf0
    have e : EA - β * h = (β / N) * ((N - 1 : ℕ) : ℝ) * (∫ z, f z ∂ν - ∫ z, f z ∂(withDensityReal ρ)) -
        (β / N) * ∫ z, f z ∂(withDensityReal ρ) - β * ∫ z, r z ∂(withDensityReal ρ) := by
      rw [hhsplit, hEA, hn']
      field_simp
      ring
    rw [e]
    have h1 : |(β / N) * ((N - 1 : ℕ) : ℝ) * (∫ z, f z ∂ν - ∫ z, f z ∂(withDensityReal ρ))| ≤
        β * (Cm0 * H * (Real.sqrt (deltaN d s N / (N : ℝ)) + deltaN d s N)) := by
      rw [abs_mul, abs_of_nonneg hc0]
      exact mul_le_mul hc1 hm (abs_nonneg _) hβ.le
    have h2 : |(β / N) * ∫ z, f z ∂(withDensityReal ρ)| ≤ (β / N) * H := by
      rw [abs_of_nonneg (mul_nonneg hlam hf1')]
      exact mul_le_mul_of_nonneg_left hf1 hlam
    have h3 : |β * ∫ z, r z ∂(withDensityReal ρ)| = β * ∫ z, r z ∂(withDensityReal ρ) :=
      abs_of_nonneg (mul_nonneg hβ.le hηr)
    have := abs_sub (a := (β / N) * ((N - 1 : ℕ) : ℝ) * (∫ z, f z ∂ν - ∫ z, f z ∂(withDensityReal ρ)) -
        (β / N) * ∫ z, f z ∂(withDensityReal ρ)) (b := β * ∫ z, r z ∂(withDensityReal ρ))
    have h4 := abs_sub ((β / N) * ((N - 1 : ℕ) : ℝ) * (∫ z, f z ∂ν - ∫ z, f z ∂(withDensityReal ρ)))
      ((β / N) * ∫ z, f z ∂(withDensityReal ρ))
    nlinarith [h1, h2, h3, this, h4]
  -- assemble
  have hmid : Integrable (fun Y => |A Y - EA| + |EA - β * h| + (β / N) * H + R Y) P :=
    ((hI1.add (integrable_const _)).add (integrable_const _)).add hRi
  have hvint : Integrable (fun Y => |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y|) P :=
    Integrable.mono' hmid hvm.abs.aestronglyMeasurable (Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs, abs_abs]; exact hpt Y)
  refine ⟨hvint, ?_⟩
  have hbd : ∫ Y, |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y| ∂P ≤
      ∫ Y, (|A Y - EA| + |EA - β * h| + (β / N) * H + R Y) ∂P :=
    integral_mono_of_nonneg (Eventually.of_forall fun Y => abs_nonneg _) hmid
      (Eventually.of_forall hpt)
  have hsumint : ∫ Y, (|A Y - EA| + |EA - β * h| + (β / N) * H + R Y) ∂P =
      ∫ Y, |A Y - EA| ∂P + |EA - β * h| + (β / N) * H + ∫ Y, R Y ∂P := by
    have i2 : Integrable (fun Y => |A Y - EA| + |EA - β * h|) P := hI1.add (integrable_const _)
    have i3 : Integrable (fun Y => |A Y - EA| + |EA - β * h| + (β / N) * H) P :=
      i2.add (integrable_const _)
    rw [integral_add i3 hRi, integral_add i2 (integrable_const _), integral_add hI1 (integrable_const _)]
    simp
  have hfinal : ∫ Y, |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y| ∂P ≤
      β * H * Real.sqrt (C1 * Real.exp (β * B) / ((N - 1 : ℕ) : ℝ)) +
        (β * Cm0 * H * (Real.sqrt (deltaN d s N / (N : ℝ)) + deltaN d s N) +
          (β / N) * H + β * ∫ z, r z ∂(withDensityReal ρ)) + (β / N) * H +
        β * M1 * ∫ z, r z ∂(withDensityReal ρ) := by
    rw [hsumint] at hbd
    linarith [hT1, hT2, hRle]
  have hfinal' : ∫ Y, |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y| ∂P ≤
      β * H * Real.sqrt (C1 * Real.exp (β * B) / ((N - 1 : ℕ) : ℝ)) +
        β * Cm0 * H * (Real.sqrt (deltaN d s N / (N : ℝ)) + deltaN d s N) +
        2 * (β / N) * H +
        β * (1 + M1) * ∫ z, (gPlus d s c (y - z) - min (gPlus d s c (y - z)) H) ∂(withDensityReal ρ) := by
    have e : ∫ z, (gPlus d s c (y - z) - min (gPlus d s c (y - z)) H) ∂(withDensityReal ρ) =
        ∫ z, r z ∂(withDensityReal ρ) := rfl
    rw [e]
    nlinarith [hfinal]
  exact hfinal'

/-- Elementary asymptotics: `a √(Cv/(N-1)) + b (√(δ_N/N) + δ_N) + e/N → 0`. -/
theorem eqbias_small_N (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) {a b e Cv : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) (hCv : 0 ≤ Cv) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N →
      a * Real.sqrt (Cv / ((N - 1 : ℕ) : ℝ)) +
        b * (Real.sqrt (deltaN d s N / (N : ℝ)) + deltaN d s N) + e / N ≤ ε := by
  obtain ⟨hs0, hp1, hp2⟩ := eqbias_p_range hs1 hsd hd
  set p : ℝ := (d : ℝ) / s with hp
  have hT0 : Tendsto (fun N : ℕ => ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have hT1 : Tendsto (fun N : ℕ => Real.sqrt (Cv / ((N - 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => Cv / ((N - 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      hT0.const_div_atTop Cv
    have := h1.sqrt
    rwa [Real.sqrt_zero] at this
  have hδ : Tendsto (fun N : ℕ => deltaN d s N) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(p - 1))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    refine h1.congr (fun N => ?_)
    rw [eqbias_deltaN hs1 N]; congr 1; ring
  have hδ0 : ∀ N : ℕ, 0 ≤ deltaN d s N := fun N => by
    rw [eqbias_deltaN hs1 N]; positivity
  have hT2 : Tendsto (fun N : ℕ => Real.sqrt (deltaN d s N / (N : ℝ))) atTop (𝓝 0) := by
    have hsq : Tendsto (fun N : ℕ => Real.sqrt (deltaN d s N)) atTop (𝓝 0) := by
      have := hδ.sqrt
      rwa [Real.sqrt_zero] at this
    refine squeeze_zero (fun N => Real.sqrt_nonneg _) (fun N => ?_) hsq
    refine Real.sqrt_le_sqrt ?_
    by_cases hN : (N : ℝ) = 0
    · rw [hN, div_zero]; exact hδ0 N
    · have hN1 : (1 : ℝ) ≤ N := by
        have : 1 ≤ N := by
          rcases Nat.eq_zero_or_pos N with h | h
          · exact absurd (by simp [h]) hN
          · exact h
        exact_mod_cast this
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hδ0 N]
  have hT3 : Tendsto (fun N : ℕ => e / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop e
  have hsum : Tendsto (fun N : ℕ => a * Real.sqrt (Cv / ((N - 1 : ℕ) : ℝ)) +
      b * (Real.sqrt (deltaN d s N / (N : ℝ)) + deltaN d s N) + e / N) atTop (𝓝 0) := by
    have := ((hT1.const_mul a).add ((hT2.add hδ).const_mul b)).add hT3
    simpa using this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hε))
  exact ⟨N₀, fun N hN _ => (hN₀ N hN).le⟩

/-- The empirical potential under the pole laws is uniformly close to its mean-field value. -/
theorem eqbias_field_small (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ hN : 2 ≤ N, N₀ ≤ N → ∀ x : Torus d,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      Integrable (fun Y => |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y|)
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
      ∫ Y, |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y|
        ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤ ε := by
  have hs0 : 0 ≤ s := (eqbias_p_range hs1 hsd hd).1.le
  intro ε hε
  obtain ⟨Cv, Cm, M1, hCv, hCm, hM1, hmain⟩ := eqbias_field_L1_H hd hs0 hsd hβ hρ c hc
  have hδ' : 0 < ε / (2 * (β * (1 + M1))) := by positivity
  obtain ⟨H₀, hH₀⟩ := eqbias_tail_mu hd hs0 hsd c hc hρ _ hδ'
  set H : ℝ := max H₀ 0 with hH
  have hH0 : 0 ≤ H := le_max_right _ _
  obtain ⟨N₀, hN₀⟩ := eqbias_small_N hd hs1 hsd (a := β * H) (b := β * Cm * H) (e := 2 * β * H)
    (Cv := Cv) (by positivity) (by positivity) (by positivity) hCv (ε := ε / 2) (by positivity)
  refine ⟨N₀, fun N hN hN0 x t ht y => ?_⟩
  obtain ⟨hint, hbd⟩ := hmain N hN x t ht y H hH0
  refine ⟨hint, hbd.trans ?_⟩
  have h1 := hN₀ N hN0 hN
  have h2 := hH₀ H (le_max_left _ _) y
  have h3 : β * (1 + M1) * ∫ z, (gPlus d s c (y - z) - min (gPlus d s c (y - z)) H)
      ∂(withDensityReal ρ) ≤ ε / 2 := by
    have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ β * (1 + M1) by positivity)
    have e : β * (1 + M1) * (ε / (2 * (β * (1 + M1)))) = ε / 2 := by field_simp
    linarith
  have e1 : β * H * Real.sqrt (Cv / ((N - 1 : ℕ) : ℝ)) +
      β * Cm * H * (Real.sqrt (deltaN d s N / (N : ℝ)) + deltaN d s N) + 2 * (β / N) * H =
      β * H * Real.sqrt (Cv / ((N - 1 : ℕ) : ℝ)) +
        β * Cm * H * (Real.sqrt (deltaN d s N / (N : ℝ)) + deltaN d s N) + 2 * β * H / N := by
    ring
  linarith

end Main

end HRS

end
