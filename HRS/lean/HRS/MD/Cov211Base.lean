import HRS.Equilibrium.TRRFinal
import HRS.Equilibrium.ResponseSubGaussian
import HRS.Prob.CLT

/-!
# Packet COV211, the rate family: smoothness of `M`, `C`, the finite-`N` identities

Setting of Prop. 2.11: `d ≥ 2`, `d/2 ≤ s < d`, `β > 0`, `k ≠ 0`, thermal densities `ρ θ` of the
potentials `rateV k β θ`.  We put `M θ = pair (ρ θ dx) φ`, `C θ = susceptibilityCov`, `φ = cos_k`.

* `M` is `C^∞` (`TRR.Rc` and a continuous linear functional), `M' = C`, so `C` is continuous;
* `C ≥ 0`, `C ≤ 1`; `C_N ≥ 0`;
* `∫_a^b (C_N - C) = (M_N - M)(b) - (M_N - M)(a)` for `N ≥ 2`;
* the laws `rateLaw`, `rateGaussian` (copies of `HRS.Main.rateLaw`, `HRS.Main.rateGaussian`, same body),
  their second moments and sub-Gaussian tails.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MD.Cov211

open HRS

variable {d : ℕ} {s : ℝ}

/-- Copy of `HRS.Main.rateLaw` (same body). -/
def rateLaw (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (N : ℕ) (θ : ℝ) : Measure ℝ :=
  (rateGibbs d s k β θ N).map (rateY d s k β N θ)

/-- Copy of `HRS.Main.rateGaussian` (same body). -/
def rateGaussian (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (ρθ : Torus d → ℝ) : Measure ℝ :=
  gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρθ) β
    (Torus.cosMode k) (Torus.cosMode k))

/-- `M θ = μ_θ(φ)`. -/
abbrev covM (d : ℕ) (s : ℝ) (β : ℝ) (k : Lattice d) (ρ : ℝ → Torus d → ℝ) (θ : ℝ) : ℝ :=
  pair (withDensityReal (ρ θ)) (Torus.cosMode k)

/-- `C θ = C_{β,μ_θ}(φ,φ)`. -/
abbrev covC (d : ℕ) (s : ℝ) (β : ℝ) (k : Lattice d) (ρ : ℝ → Torus d → ℝ) (θ : ℝ) : ℝ :=
  susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β (Torus.cosMode k)
    (Torus.cosMode k)

theorem s_nonneg (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) : 0 ≤ s := by
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem M_hasDerivAt (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (θ : ℝ) :
    HasDerivAt (covM d s β k ρ) (covC d s β k ρ θ) θ :=
  (TRR.thermal_response_rates_proof hd hs hsd β hβ k hk ρ hρ).2.2.1 θ

/-- `θ ↦ μ_θ(φ)` is `C^∞`. -/
theorem M_contDiff (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (covM d s β k ρ) := by
  have hs0 : 0 ≤ s := s_nonneg hd hs
  have hρe : ∀ θ', ρ θ' = ⇑(TRR.Rc hd hs0 hsd hβ k θ') := fun θ' =>
    TRR.trr_rho_eq_Rc hd hs0 hsd hβ k θ' (hρ θ')
  set ℓ : TRR.Cb d →L[ℝ] ℝ :=
    TRR.intC.comp (ContinuousLinearMap.mul ℝ (TRR.Cb d) (TRR.cosC k)) with hℓ
  have hpair : ∀ θ', covM d s β k ρ θ' = ℓ (TRR.Rc hd hs0 hsd hβ k θ') := by
    intro θ'
    show pair (withDensityReal (ρ θ')) (Torus.cosMode k) = _
    rw [hρe θ']
    unfold pair
    rw [TRR.trr_integral_wd (TRR.Rc hd hs0 hsd hβ k θ').continuous.measurable
      (fun x => (TRR.Rc_pos hd hs0 hsd hβ k θ' x).le)]
    simp only [hℓ, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.mul_apply', TRR.intC_apply, ContinuousMap.mul_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show _ = Torus.cosMode k x * _
    ring
  have e : covM d s β k ρ = ℓ ∘ TRR.Rc hd hs0 hsd hβ k := funext hpair
  rw [e]
  exact ℓ.contDiff.comp (TRR.contDiff_Rc hd hs0 hsd hβ k)

theorem C_continuous (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) :
    Continuous (covC d s β k ρ) := by
  have h1 : Continuous (deriv (covM d s β k ρ)) :=
    (M_contDiff hd hs hsd β hβ k ρ hρ).continuous_deriv (by simp)
  have : covC d s β k ρ = deriv (covM d s β k ρ) :=
    funext fun θ => (M_hasDerivAt hd hs hsd β hβ k hk ρ hρ θ).deriv.symm
  rw [this]; exact h1

theorem C_nonneg (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (θ : ℝ) :
    0 ≤ covC d s β k ρ θ := by
  have hs0 : 0 ≤ s := s_nonneg hd hs
  have hVc : Continuous (rateV k β θ) := by
    unfold rateV
    exact (continuous_const.mul (Torus.continuous_cosMode k)).div_const β
  have hVM : ∀ x, |rateV k β θ x| ≤ |θ| / β := by
    intro x
    have hc : |Torus.cosMode k x| ≤ 1 := by
      have := Torus.norm_cosMode_le k x
      rwa [Real.norm_eq_abs] at this
    unfold rateV
    rw [abs_div, abs_mul, abs_neg, abs_of_pos hβ]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg θ) hc) hβ.le
  obtain ⟨Λ, hΛ⟩ := q32a_thermal_bounded_above hd hs0 hsd hVc hVM hβ.le (hρ θ)
  obtain ⟨hprob, _⟩ := hρ θ
  haveI : IsProbabilityMeasure (withDensityReal (ρ θ)) := isProb_withDensityReal hprob
  have hφL2 : MemLp (Torus.cosMode k) 2 (withDensityReal (ρ θ)) :=
    MemLp.of_bound (Torus.continuous_cosMode k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => Torus.norm_cosMode_le k x)
  obtain ⟨c, C, hc, H⟩ := susceptibilityCov_bounds hd hs0 hsd (ρ θ) hprob Λ hΛ β hβ.le
  have := (H _ hφL2).1
  refine le_trans ?_ this
  refine mul_nonneg hc.le ?_
  unfold l2Inner
  exact integral_nonneg fun x => mul_self_nonneg _

theorem C_le_one (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (θ : ℝ) :
    covC d s β k ρ θ ≤ 1 :=
  susceptibilityCov_cosMode_le_one hd hs hsd β hβ k hk ρ hρ θ

/-! ### Finite-`N` identities -/

theorem rateGibbs_isProb (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    IsProbabilityMeasure (rateGibbs d s k β θ N) := by
  have hs0 : 0 < s := by
    have h1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨gm, hgm, c, hc, hgc, hgm_ae⟩ := resp_good_kernel hd hs0 hsd
  exact q32d_isProb gm hgm hgm_ae hβ hc hgc hN k θ

theorem rateVarN_nonneg (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (N : ℕ) (θ : ℝ) :
    0 ≤ rateVarN d s k β N θ := by
  unfold rateVarN
  exact integral_nonneg fun X => sq_nonneg _

/-- `∫_a^b (C_N - C) = (M_N - M)(b) - (M_N - M)(a)`. -/
theorem integral_CN_sub_C (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) {N : ℕ} (hN : 2 ≤ N)
    (a b : ℝ) :
    ∫ θ in a..b, (rateVarN d s k β N θ - covC d s β k ρ θ) =
      (rateMeanN d s k β N b - covM d s β k ρ b) - (rateMeanN d s k β N a - covM d s β k ρ a) := by
  obtain ⟨-, hV, hM, -⟩ := finite_response_rates hd hs hsd β hβ k hk N hN
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ =>
    rateMeanN d s k β N θ - covM d s β k ρ θ) (fun θ _ =>
    (hM θ).sub (M_hasDerivAt hd hs hsd β hβ k hk ρ hρ θ)) ?_
  exact (hV.continuous.sub (C_continuous hd hs hsd β hβ k hk ρ hρ)).intervalIntegrable _ _

theorem rateVarN_continuous (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) {N : ℕ} (hN : 2 ≤ N) :
    Continuous (rateVarN d s k β N) :=
  (finite_response_rates hd hs hsd β hβ k hk N hN).2.1.continuous

/-! ### The laws -/

theorem rateY_measurable (k : Lattice d) (β θ : ℝ) (N : ℕ) :
    Measurable (rateY d s k β N θ) :=
  (q32d_rateY_cont k β θ N).measurable

theorem rateLaw_isProb (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    IsProbabilityMeasure (rateLaw d s k β N θ) := by
  have := rateGibbs_isProb hd hs hsd hβ k hN θ
  unfold rateLaw
  exact (Measure.isProbabilityMeasure_map_iff (rateY_measurable k β θ N).aemeasurable).2 this

/-- The Gaussian `rateGaussian` is a centered Gaussian of variance `C θ` (when `C θ ≥ 0`). -/
theorem rateGaussian_isProb (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (ρθ : Torus d → ℝ) :
    IsProbabilityMeasure (rateGaussian d s k β ρθ) := by
  unfold rateGaussian gaussianLaw
  infer_instance

/-- Second moment of `rateLaw` is `C_N`. -/
theorem integral_sq_rateLaw (k : Lattice d) (β : ℝ) (N : ℕ) (θ : ℝ) :
    ∫ z, z ^ 2 ∂(rateLaw d s k β N θ) = rateVarN d s k β N θ := by
  unfold rateLaw rateVarN
  rw [integral_map (rateY_measurable k β θ N).aemeasurable
    (by fun_prop : Measurable (fun z : ℝ => z ^ 2)).aestronglyMeasurable]

/-- Second moment of `rateGaussian` is `C` (for `C ≥ 0`). -/
theorem integral_sq_rateGaussian (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (ρθ : Torus d → ℝ)
    (h : 0 ≤ susceptibilityCov (periodicRiesz d s) (withDensityReal ρθ) β (Torus.cosMode k)
      (Torus.cosMode k)) :
    ∫ z, z ^ 2 ∂(rateGaussian d s k β ρθ) =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρθ) β (Torus.cosMode k)
        (Torus.cosMode k) := by
  unfold rateGaussian gaussianLaw
  set v := susceptibilityCov (periodicRiesz d s) (withDensityReal ρθ) β (Torus.cosMode k)
    (Torus.cosMode k)
  have h1 : (variance (fun x : ℝ => x) (gaussianReal 0 (Real.toNNReal v))) = (Real.toNNReal v : ℝ) :=
    variance_id_gaussianReal
  have h2 : ∫ x, x ∂(gaussianReal 0 (Real.toNNReal v)) = 0 := integral_id_gaussianReal
  have h4 := variance_of_integral_eq_zero (X := fun x : ℝ => x)
    (μ := gaussianReal 0 (Real.toNNReal v)) aemeasurable_id h2
  rw [Real.coe_toNNReal _ h] at h1
  rw [h4] at h1
  exact h1

end HRS.MD.Cov211
