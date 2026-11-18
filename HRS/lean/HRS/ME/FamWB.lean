import HRS.MD.EQBurnCltFinal
import HRS.Equilibrium.ResponseSubGaussian
import HRS.PDE.TorusFPSpec

/-!
# Packet W2 (namespace `HRS.ME.FamW`): `E[Y_{N,0}^2] -> C_{beta,mu_0}(cos_k, cos_k)`

At `theta = 0` the rate potential vanishes, `rateV k beta 0 = 0`, and the finite-particle variance
`rateVarN d s k beta N 0 = E[Y_{N,0}^2]` converges to the susceptibility covariance of the thermal
density `rho0` of `rateV k beta 0`.

Route.  (1) The static CLT `HRS.MD.EQBurnClt.eq_static_clt_proof` (smooth `V = 0`, `phi = cos_k`) states
`ConvergesInLaw` of the laws of `Y_{N,0}` (the coordinate `linCoord (firstMarginal P_N) cos_k` is `rateY ... 0`
by unfolding) to the centred Gaussian `gaussianLaw C`.  (2) The sub-Gaussian bound
`HRS.response_subGaussian_proof` (with `a = b = 0`; the family of thermal densities is modified at `0` to be
`rho0`) gives `nu {|z| > x} <= 4 exp(-x^2/(2D))` for the laws of `Y_N` (`N >= 2`) and for the Gaussian.
(3) Abstract analysis (all in `ENNReal`/real integrals, with Mathlib's layer-cake formula): for the truncation
`min(z^2, L^2)` (bounded continuous) the weak convergence applies, and the excess `(z^2 - L^2)_+` has
`nu`-integral at most `8 D exp(-L^2/(2D))`, uniformly; hence second moments converge
(`tendsto_integral_sq`).  (4) `E[G^2] = C` for `G ~ N(0, C)` since `C >= 0` (the lower bound of
`susceptibilityCov_bounds`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.ME.FamW

/-- The excess `(z² - L²)₊`. -/
def excess (L z : ℝ) : ℝ := max (z ^ 2 - L ^ 2) 0

/-- The truncation `min(z², L²)` as a bounded continuous function. -/
def trunc (L : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun z => min (z ^ 2) (L ^ 2), by fun_prop⟩ (L ^ 2)
    (fun x y => by
      have h1 : 0 ≤ min (x ^ 2) (L ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
      have h2 : 0 ≤ min (y ^ 2) (L ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
      have h3 : min (x ^ 2) (L ^ 2) ≤ L ^ 2 := min_le_right _ _
      have h4 : min (y ^ 2) (L ^ 2) ≤ L ^ 2 := min_le_right _ _
      rw [Real.dist_eq, abs_le]
      constructor <;> simp only [ContinuousMap.coe_mk] <;> linarith)

theorem trunc_apply (L z : ℝ) : trunc L z = min (z ^ 2) (L ^ 2) := rfl

theorem excess_add_trunc (L z : ℝ) : z ^ 2 = trunc L z + excess L z := by
  rw [trunc_apply, excess]
  rcases le_total (z ^ 2) (L ^ 2) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

theorem continuous_excess (L : ℝ) : Continuous (excess L) := by
  unfold excess; fun_prop

theorem excess_nonneg (L z : ℝ) : 0 ≤ excess L z := le_max_right _ _

/-- Layer-cake bound for the excess under a sub-Gaussian tail. -/
theorem lintegral_excess_le (ν : Measure ℝ) (D : ℝ) (hD : 0 < D)
    (htail : ∀ x : ℝ, 0 ≤ x → ν {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))))
    (L : ℝ) :
    ∫⁻ z, ENNReal.ofReal (excess L z) ∂ν ≤ ENNReal.ofReal (8 * D * Real.exp (-L ^ 2 / (2 * D))) := by
  rw [lintegral_eq_lintegral_meas_lt ν (Filter.Eventually.of_forall (excess_nonneg L))
    (continuous_excess L).measurable.aemeasurable]
  have hc : (0 : ℝ) < 2 * D := by linarith
  have hneg : -(1 / (2 * D)) < 0 := by
    have : 0 < 1 / (2 * D) := by positivity
    linarith
  set c : ℝ := 4 * Real.exp (-L ^ 2 / (2 * D)) with hcdef
  have hmono : ∀ t ∈ Set.Ioi (0 : ℝ),
      ν {z | t < excess L z} ≤ ENNReal.ofReal (c * Real.exp (-(1 / (2 * D)) * t)) := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    set x : ℝ := Real.sqrt (L ^ 2 + t) with hx
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have hx2 : x ^ 2 = L ^ 2 + t := Real.sq_sqrt (by positivity)
    refine le_trans (measure_mono ?_) ((htail x hx0).trans (le_of_eq ?_))
    · intro z hz
      have hz : t < excess L z := hz
      have h1 : t < z ^ 2 - L ^ 2 := by
        unfold excess at hz
        rcases le_total (z ^ 2 - L ^ 2) 0 with h | h
        · rw [max_eq_right h] at hz; linarith
        · rw [max_eq_left h] at hz; exact hz
      show x < |z|
      rw [hx, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
    · have e : -(L ^ 2 + t) / (2 * D) = -L ^ 2 / (2 * D) + -(1 / (2 * D)) * t := by
        field_simp; ring
      rw [hx2, hcdef, mul_assoc, ← Real.exp_add, e]
  have hint : IntegrableOn (fun t : ℝ => c * Real.exp (-(1 / (2 * D)) * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi hneg 0).const_mul c
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  calc ∫⁻ t in Set.Ioi (0 : ℝ), ν {z | t < excess L z}
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-(1 / (2 * D)) * t)) :=
        setLIntegral_mono' measurableSet_Ioi hmono
    _ = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), c * Real.exp (-(1 / (2 * D)) * t)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun t => by positivity)).symm
    _ = ENNReal.ofReal (8 * D * Real.exp (-L ^ 2 / (2 * D))) := by
        rw [integral_const_mul, integral_exp_mul_Ioi hneg 0, hcdef]
        simp only [mul_zero, Real.exp_zero]
        congr 1
        field_simp
        ring

/-- Real-integral form of the tail bound for the excess. -/
theorem excess_integrals (ν : Measure ℝ) [IsFiniteMeasure ν] (D : ℝ) (hD : 0 < D)
    (htail : ∀ x : ℝ, 0 ≤ x → ν {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))))
    (L : ℝ) :
    Integrable (excess L) ν ∧ 0 ≤ ∫ z, excess L z ∂ν ∧
      ∫ z, excess L z ∂ν ≤ 8 * D * Real.exp (-L ^ 2 / (2 * D)) := by
  have hle := lintegral_excess_le ν D hD htail L
  have hfin : ∫⁻ z, ENNReal.ofReal (excess L z) ∂ν < ∞ :=
    lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  have hint : Integrable (excess L) ν := by
    refine ⟨(continuous_excess L).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (excess_nonneg L))]
    exact hfin
  refine ⟨hint, integral_nonneg (excess_nonneg L), ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (excess_nonneg L))
    (continuous_excess L).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

theorem integral_sq_split (ν : Measure ℝ) [IsFiniteMeasure ν] (D : ℝ) (hD : 0 < D)
    (htail : ∀ x : ℝ, 0 ≤ x → ν {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))))
    (L : ℝ) :
    ∫ z, z ^ 2 ∂ν = ∫ z, trunc L z ∂ν + ∫ z, excess L z ∂ν := by
  obtain ⟨hint, -, -⟩ := excess_integrals ν D hD htail L
  have ht : Integrable (trunc L) ν := (trunc L).integrable ν
  have e : (fun z : ℝ => z ^ 2) = fun z => trunc L z + excess L z := funext (excess_add_trunc L)
  rw [e]
  exact integral_add ht hint

/-- Convergence in law plus a uniform sub-Gaussian tail gives convergence of second moments. -/
theorem tendsto_integral_sq (μ : ℕ → Measure ℝ) (γ : Measure ℝ) [IsFiniteMeasure γ]
    (D : ℝ) (hD : 0 < D) (hfin : ∀ N, 2 ≤ N → IsFiniteMeasure (μ N))
    (htail : ∀ N, 2 ≤ N → ∀ x : ℝ, 0 ≤ x →
      μ N {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))))
    (htailγ : ∀ x : ℝ, 0 ≤ x → γ {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))))
    (hconv : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ x, f x ∂(μ N)) atTop (𝓝 (∫ x, f x ∂γ))) :
    Tendsto (fun N => ∫ z, z ^ 2 ∂(μ N)) atTop (𝓝 (∫ z, z ^ 2 ∂γ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc : (0 : ℝ) < 2 * D := by linarith
  have hB : Tendsto (fun L : ℝ => 8 * D * Real.exp (-L ^ 2 / (2 * D))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => -L ^ 2 / (2 * D)) atTop atBot := by
      have : Tendsto (fun L : ℝ => L ^ 2 / (2 * D)) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).atTop_div_const hc
      have e : (fun L : ℝ => -L ^ 2 / (2 * D)) = Neg.neg ∘ (fun L : ℝ => L ^ 2 / (2 * D)) := by
        funext L; simp [neg_div]
      rw [e]
      exact tendsto_neg_atTop_atBot.comp this
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (8 * D)
  obtain ⟨L, hL, hL0⟩ := ((hB.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).and
    (eventually_ge_atTop (0 : ℝ))).exists
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (hconv (trunc L)) (ε / 2) (by positivity)
  refine ⟨max N0 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : N0 ≤ N := le_trans (le_max_left _ _) hN
  haveI := hfin N hN2
  obtain ⟨-, h0, h1⟩ := excess_integrals (μ N) D hD (htail N hN2) L
  obtain ⟨-, g0, g1⟩ := excess_integrals γ D hD htailγ L
  have hs1 := integral_sq_split (μ N) D hD (htail N hN2) L
  have hs2 := integral_sq_split γ D hD htailγ L
  have hd := hN0 N hN1
  rw [Real.dist_eq, abs_lt] at hd
  rw [Real.dist_eq, hs1, hs2, abs_lt]
  constructor <;> linarith [hd.1, hd.2]

section Main

variable {d : ℕ} {s : ℝ}

/-- The covariance `C_{beta,mu}(cos_k, cos_k) >= 0` for the thermal density of the potential `rateV k beta 0`. -/
theorem cov_nonneg (hd : 2 ≤ d) (hsd : s < d) {β : ℝ} (hβ : 0 < β) (k : Lattice d)
    (ρ0 : Torus d → ℝ) (hρ0 : IsThermalDensity (periodicRiesz d s) (rateV k β 0) β ρ0)
    (hs0 : 0 ≤ s) :
    0 ≤ susceptibilityCov (periodicRiesz d s) (withDensityReal ρ0) β
      (Torus.cosMode k) (Torus.cosMode k) := by
  have hVc : Continuous (rateV k β 0) := Q32c.q32c_rateV_continuous k 0
  have hVM : ∀ x, |rateV k β 0 x| ≤ |(0 : ℝ)| / β := Q32c.q32c_rateV_abs_le k hβ 0
  obtain ⟨Λ, hΛ⟩ := q32a_thermal_bounded_above hd hs0 hsd hVc hVM hβ.le hρ0
  obtain ⟨hprob, _⟩ := hρ0
  haveI : IsProbabilityMeasure (withDensityReal ρ0) := isProb_withDensityReal hprob
  have hφL2 : MemLp (Torus.cosMode k) 2 (withDensityReal ρ0) :=
    MemLp.of_bound (Torus.continuous_cosMode k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => Torus.norm_cosMode_le k x)
  obtain ⟨c, C, hc, H⟩ := susceptibilityCov_bounds hd hs0 hsd ρ0 hprob Λ hΛ β hβ.le
  refine le_trans ?_ (H _ hφL2).1
  refine mul_nonneg hc.le ?_
  unfold l2Inner
  exact integral_nonneg fun x => mul_self_nonneg _

/-- `P_{N,theta}` of the rate family is a probability measure (`N > 0`). -/
theorem rateGibbs_isProb' (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    IsProbabilityMeasure (rateGibbs d s k β θ N) := by
  have hs0 : 0 < s := by
    have h1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨gm, hgm, c, hc, hgc, hgm_ae⟩ := resp_good_kernel hd hs0 hsd
  exact q32d_isProb gm hgm hgm_ae hβ hc hgc hN k θ

/-- **W2.**  At `θ = 0`, `E[Y_{N,0}²] = rateVarN d s k β N 0` converges to the susceptibility covariance
`C_{β,μ_0}(cos_k, cos_k)` of the thermal density `ρ0` of `rateV k β 0 = 0`. -/
theorem rateVarN_zero_tendsto {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d)
    {β : ℝ} (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ρ0 : Torus d → ℝ)
    (hρ0 : IsThermalDensity (periodicRiesz d s) (rateV k β 0) β ρ0) :
    Filter.Tendsto (fun N : ℕ => rateVarN d s k β N 0) Filter.atTop
      (nhds (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ0) β
        (Torus.cosMode k) (Torus.cosMode k))) := by
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hd1 : 1 ≤ d := by omega
  have hVz : rateV k β 0 = fun _ => 0 := by funext x; simp [rateV]
  have hV : Torus.IsSmooth (rateV k β 0) := by rw [hVz]; exact d1_isSmooth_const 0
  have hφ : Torus.IsSmooth (Torus.cosMode k) := d1_isSmooth_cosMode k
  have hclt := HRS.MD.EQBurnClt.eq_static_clt_proof hd hs0 hsd (rateV k β 0) hV β hβ ρ0 hρ0
    (Torus.cosMode k) hφ
  -- the family of thermal densities, equal to `ρ0` at `θ = 0`
  have hex : ∀ θ : ℝ, ∃ ρ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ := fun θ =>
    let ⟨ρ, h, _, _⟩ := PDE.MFThermalAssembly.thermal_exists_continuous hd1 s hs0 hsd
      (rateV k β θ) (Q32c.q32c_rateV_continuous k θ) β hβ
    ⟨ρ, h⟩
  choose ρ hρ using hex
  have hρ' : ∀ θ : ℝ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β
      (if θ = 0 then ρ0 else ρ θ) := by
    intro θ
    by_cases h : θ = 0
    · subst h; simpa using hρ0
    · simpa [h] using hρ θ
  obtain ⟨D, hD2, hD⟩ := response_subGaussian_proof hd hs hsd β hβ k hk
    (fun θ => if θ = 0 then ρ0 else ρ θ) hρ' 0 0
  have hD0 : 0 < D := by linarith
  have hcov := cov_nonneg hd hsd hβ k ρ0 hρ0 hs0
  set C : ℝ := susceptibilityCov (periodicRiesz d s) (withDensityReal ρ0) β
    (Torus.cosMode k) (Torus.cosMode k) with hC
  -- the laws of `Y_{N,0}`
  set μ : ℕ → Measure ℝ := fun N => (rateGibbs d s k β 0 N).map (rateY d s k β N 0) with hμ
  have hY : ∀ N : ℕ, Measurable (rateY d s k β N 0) := fun N =>
    HRS.MD.EQBurnClt.eqclt_linCoord_meas
      (firstMarginal (canonicalGibbs (periodicRiesz d s) (rateV k β 0) N β)) hφ
  have hprob : ∀ N : ℕ, 0 < N → IsProbabilityMeasure (μ N) := fun N hN => by
    haveI := rateGibbs_isProb' hd hs hsd hβ k hN 0
    exact (Measure.isProbabilityMeasure_map_iff (hY N).aemeasurable).2 inferInstance
  set γ : Measure ℝ := gaussianReal 0 C.toNNReal with hγ
  have hconv : ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun N => ∫ x, f x ∂(μ N)) atTop (𝓝 (∫ x, f x ∂γ)) := fun f => hclt f
  have htail : ∀ N : ℕ, 2 ≤ N → ∀ x : ℝ, 0 ≤ x →
      μ N {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))) := by
    intro N hN x hx
    have h := hD x hx N hN 0 ⟨le_rfl, le_rfl⟩
    rw [hμ]
    simp only
    rw [Measure.map_apply (hY N) (measurableSet_lt measurable_const continuous_abs.measurable)]
    exact le_trans le_self_add h
  have htailγ : ∀ x : ℝ, 0 ≤ x →
      γ {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))) := by
    intro x hx
    have h := hD x hx 2 le_rfl 0 ⟨le_rfl, le_rfl⟩
    refine le_trans (le_trans ?_ le_add_self) h
    simp [hγ, hC]
  have key := tendsto_integral_sq μ γ D hD0
    (fun N hN => by have := hprob N (by omega); infer_instance) htail htailγ hconv
  have hvar : ∀ N : ℕ, rateVarN d s k β N 0 = ∫ z, z ^ 2 ∂(μ N) := by
    intro N
    unfold rateVarN
    rw [hμ]
    simp only
    rw [integral_map (hY N).aemeasurable (by fun_prop)]
  have hsecond : ∫ z, z ^ 2 ∂γ = C := by
    have h1 : variance id γ = ∫ z, id z ^ 2 ∂γ :=
      variance_of_integral_eq_zero aemeasurable_id (integral_id_gaussianReal)
    have h2 : variance id γ = (C.toNNReal : ℝ) := variance_id_gaussianReal
    simp only [id] at h1
    rw [← h1, h2, Real.coe_toNNReal _ hcov]
  simp_rw [hvar]
  rw [← hsecond]
  exact key

end Main

end HRS.ME.FamW

end
