import HRS.MS.WrRefMargAux2

/-!
# HRS.MS.WrRefMargAux3 -- calibrated reference marginal, part 3: `L²` and uniform bounds (WR-13e)

Packet WR-13e (T11 of `docs/WR_B_PLAN.md`), third helper file (second half of the packet).  Euclidean port of
`HRS/Equilibrium/ReferenceMarginal.lean` lines 2353-2620 (`core_L2`), 2671-2748 (`small_field`),
3131-3394 (`core_unif`) and the three final theorems (1787, 2755, 3401).

Main theorems (all constants are quantified before `ρ, β ∈ (0, βp], N` and are uniform in the probability
densities `ρ ≤ M`; `μ = withDensityReal ρ`, `π^R_N = firstMarginal (RN q μ Ψ β N)`):
* `wr13e_reference_marginal_density_L2`: `‖dπ^R_N/dμ - 1‖_{L²(μ)} ≤ C δ_N` for `N ≥ N₀`;
* `wr13e_reference_marginal_density_uniform`: `‖dπ^R_N/dμ - 1‖_∞ → 0`, uniformly in `ρ ≤ M`, `β ≤ βp`;
* `wr13e_hh_eq` (Aux1): the calibration identity `⟪t_N, Ξ x⟫ = -β (k * (π^R - μ))(x) + const`.
The sup bound `dπ^R_N/dμ ≤ C` is `wr13e_reference_marginal_density_le` (Aux1).

Hypotheses: `KappaSmall βp a` with `a = wr13e_a d s τ M = max M 0 * ∫ q_τ` (smallness of `β ∫ q_τ`; this is
available by taking `τ` small, since `∫ q_τ = c τ^{(d-s)/2}`), `FeatHyp Ψ (kTau d s τ)`.
Adjustments with respect to the torus statements: `β ∈ (0, βp]` instead of a fixed `β`; `M` need not be `≥ 1`;
the absorption step uses `K_g ≥ 0` (`wr13c_Kmu_nonneg`) instead of positivity of Fourier coefficients.
Helper lemmas carry the prefix `wr13e_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.External HRS.MS.Psd

variable {d : ℕ}

section Assemble

/-- Pure-analysis assembly: Minkowski for `Φ = D + β cv + λ Q_ν` and the absorption step. -/
theorem wr13e_L2_assemble {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {β lam Cν e1 e2 e3 : ℝ}
    (hβ : 0 ≤ β) (hCν1 : 1 ≤ Cν) {θ : Euc d → ℝ} (hθm : Measurable θ) (hθ0 : ∀ x, 0 < θ x)
    (hθC : ∀ᵐ x ∂μ, θ x ≤ Cν) (hθ1 : ∫ x, θ x ∂μ = 1)
    {Dfun cv Qν Kz : Euc d → ℝ} (hDm : Measurable Dfun) (hcvm : Measurable cv)
    (hQm : Measurable Qν) (hD : eLpNorm Dfun 2 μ ≤ ENNReal.ofReal e1)
    (hcvn : eLpNorm cv 2 μ ≤ ENNReal.ofReal e2)
    (hQ : eLpNorm (fun x => lam * Qν x) 2 μ ≤ ENNReal.ofReal e3) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (he3 : 0 ≤ e3) (hKz2 : MemLp Kz 2 μ) (hnn : 0 ≤ ∫ x, Kz x * (θ x - 1) ∂μ) {c : ℝ}
    (heq : ∀ x, Real.log (θ x) + β * Kz x = Dfun x + β * cv x + lam * Qν x + c) :
    eLpNorm (fun x => θ x - 1) 2 μ ≤ ENNReal.ofReal (Cν * (e1 + β * e2 + e3)) := by
  have hCν0 : 0 ≤ Cν := by linarith
  have hΦe : (fun x => Dfun x + β * cv x + lam * Qν x) =
      (Dfun + fun x => β * cv x) + fun x => lam * Qν x := by
    funext x; simp
  have e2' : eLpNorm (fun x => β * cv x) 2 μ = ENNReal.ofReal β * eLpNorm cv 2 μ := by
    have := eLpNorm_const_smul (p := 2) (μ := μ) β cv
    rw [show (fun x => β * cv x) = β • cv from rfl, this, Real.enorm_of_nonneg hβ]
  have hΦnorm : eLpNorm (fun x => Dfun x + β * cv x + lam * Qν x) 2 μ ≤
      ENNReal.ofReal (e1 + β * e2 + e3) := by
    rw [hΦe]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine (add_le_add_left (eLpNorm_add_le (by norm_num)) _).trans ?_
    rw [e2']
    calc eLpNorm Dfun 2 μ + ENNReal.ofReal β * eLpNorm cv 2 μ + eLpNorm (fun x => lam * Qν x) 2 μ
        ≤ ENNReal.ofReal e1 + ENNReal.ofReal β * ENNReal.ofReal e2 + ENNReal.ofReal e3 := by
          gcongr
      _ = ENNReal.ofReal (e1 + β * e2 + e3) := by
          rw [← ENNReal.ofReal_mul hβ, ← ENNReal.ofReal_add he1 (by positivity),
            ← ENNReal.ofReal_add (by positivity) he3]
  have hΦmem : MemLp (fun x => Dfun x + β * cv x + lam * Qν x) 2 μ :=
    lt_of_le_of_lt hΦnorm ENNReal.ofReal_lt_top
  have habs := wr13e_absorption hβ hθm hθ0 hCν1 hθC hθ1 hΦmem hKz2 hnn heq
  refine habs.trans ?_
  calc ENNReal.ofReal Cν * eLpNorm (fun x => Dfun x + β * cv x + lam * Qν x) 2 μ
      ≤ ENNReal.ofReal Cν * ENNReal.ofReal (e1 + β * e2 + e3) := by gcongr
    _ = ENNReal.ofReal (Cν * (e1 + β * e2 + e3)) := by rw [← ENNReal.ofReal_mul hCν0]

end Assemble

section CvBound

/-- **The convolution term of the cavity equation** (torus `core_L2`, clipping part): if `ν ≤ Cν μ` is a
probability measure within event distance `κ0/N` of `θ μ`, then `x ↦ q*θ(x) - q*ν(x)` is the measurable
function `q * (ρ (θc - θ'c))`, with `L²(μ)` norm `≤ C δ_N`. -/
theorem wr13e_cv_bound (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (M : ℝ)
    {Cν : ℝ} (hCν1 : 1 ≤ Cν) {κ0 : ℝ} (hκ0 : 0 ≤ κ0) :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ ∀ n : ℕ, N0 ≤ n + 1 → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ θ : Euc d → ℝ, Measurable θ → (∀ x, 0 < θ x) →
      (∀ᵐ y ∂(HRS.Whole.withDensityReal ρ), θ y ≤ Cν) →
      ∀ ν : Measure (Euc d), IsProbabilityMeasure ν → ν ≤ ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ →
      (∀ A : Set (Euc d), MeasurableSet A →
        |((HRS.Whole.withDensityReal ρ).withDensity (fun y => ENNReal.ofReal (θ y))).real A - ν.real A| ≤
          κ0 / ((n + 1 : ℕ) : ℝ)) →
      ∃ F : Euc d → ℝ, Measurable F ∧
        (∀ x, (∫ y, qTau d s τ (x - y) * θ y ∂(HRS.Whole.withDensityReal ρ)) -
          ∫ y, qTau d s τ (x - y) ∂ν = F x) ∧
        eLpNorm F 2 (HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (C * deltaN d s (n + 1)) := by
  have hCν0 : 0 ≤ Cν := by linarith
  obtain ⟨Ccv, Ncv, hCcv0, hcv⟩ := wr13e_cv_L2 hd hs hsd hτ (max M 0 * Cν) M (2 * κ0)
  refine ⟨Ccv, Ncv, hCcv0, ?_⟩
  intro n hn ρ hρ hM θ hθm hθ0 hθC ν hνp hνle hTVθ
  haveI hμp := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hM'ρ : ∀ x, ρ x ≤ max M 0 := fun x => (hM x).trans (le_max_left _ _)
  have hM'0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hq0m : Measurable (qTau d s τ : Euc d → ℝ) := wr12_qTau_meas
  have hq00 : ∀ z : Euc d, 0 ≤ qTau d s τ z := fun z => qTau_nonneg hs z
  have hqint : Integrable (qTau d s τ : Euc d → ℝ) := (qTau_integrable_integral hs hsd hτ).1

  -- clipped densities
  set θc : Euc d → ℝ := fun y => min (θ y) Cν with hθc
  have hθcm : Measurable θc := hθm.min measurable_const
  have hθc0 : ∀ y, 0 ≤ θc y := fun y => le_min (hθ0 y).le hCν0
  have hθcb : ∀ y, θc y ≤ Cν := fun y => min_le_right _ _
  have hθc_ae : ∀ᵐ y ∂(HRS.Whole.withDensityReal ρ), θc y = θ y := hθC.mono fun y hy => min_eq_left hy
  haveI hνfin : IsFiniteMeasure ν := inferInstance
  haveI hlebd : ν.HaveLebesgueDecomposition (HRS.Whole.withDensityReal ρ) :=
    Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
  have hνac : ν ≪ HRS.Whole.withDensityReal ρ := Measure.absolutelyContinuous_of_le_smul hνle
  have hν_rn := HRS.PoleCavityAux.rnDeriv_le_of_le_withDensity (HRS.Whole.withDensityReal ρ) ν
    (fun _ => ENNReal.ofReal Cν) (by rw [withDensity_const]; exact hνle)
  set θ' : Euc d → ℝ := fun y => (ν.rnDeriv (HRS.Whole.withDensityReal ρ) y).toReal with hθ'
  set θ'c : Euc d → ℝ := fun y => min (θ' y) Cν with hθ'c
  have hθ'm : Measurable θ' := (Measure.measurable_rnDeriv ν (HRS.Whole.withDensityReal ρ)).ennreal_toReal
  have hθ'cm : Measurable θ'c := hθ'm.min measurable_const
  have hθ'c0 : ∀ y, 0 ≤ θ'c y := fun y => le_min ENNReal.toReal_nonneg hCν0
  have hθ'cb : ∀ y, θ'c y ≤ Cν := fun y => min_le_right _ _
  have hνeq : ν = (HRS.Whole.withDensityReal ρ).withDensity (fun y => ENNReal.ofReal (θ'c y)) := by
    calc ν = (HRS.Whole.withDensityReal ρ).withDensity (ν.rnDeriv (HRS.Whole.withDensityReal ρ)) :=
          (Measure.withDensity_rnDeriv_eq ν (HRS.Whole.withDensityReal ρ) hνac).symm
      _ = _ := by
        refine withDensity_congr_ae ?_
        filter_upwards [Measure.rnDeriv_lt_top ν (HRS.Whole.withDensityReal ρ), hν_rn.2] with y h1 h2
        have h3 : (ν.rnDeriv (HRS.Whole.withDensityReal ρ) y).toReal ≤ Cν :=
          ENNReal.toReal_le_of_le_ofReal hCν0 h2
        simp only [hθ'c, hθ', min_eq_left h3, ENNReal.ofReal_toReal h1.ne]
  have hπeq' : (HRS.Whole.withDensityReal ρ).withDensity (fun y => ENNReal.ofReal (θ y)) =
      (HRS.Whole.withDensityReal ρ).withDensity (fun y => ENNReal.ofReal (θc y)) := by
    refine withDensity_congr_ae ?_
    filter_upwards [hθc_ae] with y hy
    rw [hy]
  have hθci : Integrable θc (HRS.Whole.withDensityReal ρ) := Integrable.of_bound hθcm.aestronglyMeasurable Cν
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hθc0 y)]; exact hθcb y)
  have hθ'ci : Integrable θ'c (HRS.Whole.withDensityReal ρ) := Integrable.of_bound hθ'cm.aestronglyMeasurable Cν
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hθ'c0 y)]; exact hθ'cb y)
  have hTV : ∫ y, |θc y - θ'c y| ∂(HRS.Whole.withDensityReal ρ) ≤ 2 * (κ0 / ((n + 1 : ℕ) : ℝ)) := by
    refine RefMarg.integral_abs_sub_le hθcm hθ'cm hθc0 hθ'c0 hθci hθ'ci (fun A hA => ?_)
    rw [← hπeq', ← hνeq]
    exact hTVθ A hA
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by
    show (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.succ_pos n
  have hNpos : 0 < N := by linarith
  set δ : ℝ := deltaN d s (n + 1) with hδdef
  have hδ1 : N⁻¹ ≤ δ := HRS.WeakRef.inv_le_deltaN hd hs.le hsd (Nat.succ_pos n)
  set w : Euc d → ℝ := fun y => ρ y * (θc y - θ'c y) with hw
  have hwm : Measurable w := hρ.measurable.mul (hθcm.sub hθ'cm)
  have hρi : Integrable ρ := HRS.Whole.Q34.integrable_of_isProbDensity hρ
  have hdiff : ∀ y, |θc y - θ'c y| ≤ Cν := fun y => by
    rw [abs_le]; constructor <;> linarith [hθc0 y, hθ'c0 y, hθcb y, hθ'cb y]
  have hwb : ∀ y, |w y| ≤ max M 0 * Cν := fun y => by
    simp only [hw]
    rw [abs_mul, abs_of_nonneg (hρ.nonneg y)]
    exact mul_le_mul (hM'ρ y) (hdiff y) (abs_nonneg _) hM'0
  have hwi : Integrable w := by
    refine Integrable.mono' (hρi.mul_const Cν) hwm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg y)]
    exact mul_le_mul_of_nonneg_left (hdiff y) (hρ.nonneg y)
  have hwL1 : ∫ y, |w y| ≤ 2 * κ0 * Real.sqrt (δ / N) := by
    have e : ∫ y, |w y| = ∫ y, |θc y - θ'c y| ∂(HRS.Whole.withDensityReal ρ) := by
      rw [wr13e_integral_nu hρ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hw]
      rw [abs_mul, abs_of_nonneg (hρ.nonneg y)]
    rw [e]
    refine hTV.trans ?_
    have h1 : N⁻¹ ≤ Real.sqrt (δ / N) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_right hδ1 (inv_nonneg.2 hNpos.le)
    calc 2 * (κ0 / N) = 2 * κ0 * N⁻¹ := by rw [div_eq_mul_inv]; ring
      _ ≤ 2 * κ0 * Real.sqrt (δ / N) := by gcongr
  obtain ⟨hcvint, hcvmem, hcvnorm⟩ := hcv (n + 1) hn ρ hρ hM w hwm hwb hwi hwL1
  refine ⟨fun x => ∫ y, qTau d s τ (x - y) * w y, ?_, ?_, hcvnorm⟩
  · exact RefMarg.measurable_integral_kernel (F := fun p : Euc d × Euc d => qTau d s τ (p.1 - p.2) * w p.2)
      ((wr12_qTau_meas.comp (measurable_fst.sub measurable_snd)).mul (hwm.comp measurable_snd))
  · intro x
    have e1 : ∫ y, qTau d s τ (x - y) * θ y ∂(HRS.Whole.withDensityReal ρ) =
        ∫ y, qTau d s τ (x - y) * θc y ∂(HRS.Whole.withDensityReal ρ) :=
      integral_congr_ae (hθc_ae.mono fun y hy => by
        show qTau d s τ (x - y) * θ y = qTau d s τ (x - y) * θc y; rw [hy])
    rw [e1]
    have := wr13e_cv_identity hρ hM'ρ hq0m hq00 hqint hθcm hθ'cm hθc0 hθ'c0 hθcb hθ'cb x
    rw [← hνeq] at this
    exact this

end CvBound

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Ψ : Euc d → H}

set_option maxHeartbeats 1600000 in
/-- **`L²` core** (torus `core_L2`): under the field bound `|⟪t_N, Ξ⟫| ≤ 1`, the first marginal of `R_N` has
`‖dπ_N/dμ - 1‖_{L²(μ)} ≤ C δ_N` for `N ≥ N₁`. -/
theorem wr13e_core_L2 (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (βp M : ℝ) (hβp : 0 < βp) (hκ : KappaSmall βp (wr13e_a d s τ M))
    (hΨ : FeatHyp Ψ (kTau d s τ)) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N₁ ≤ N →
      ∀ (ht : ∀ x, |inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)
          (Xi (HRS.Whole.withDensityReal ρ) Ψ x)| ≤ 1),
      HRS.Whole.firstMarginal
          (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)
        ≪ HRS.Whole.withDensityReal ρ ∧
        eLpNorm (fun y => ((HRS.Whole.firstMarginal
            (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)).rnDeriv
            (HRS.Whole.withDensityReal ρ) y).toReal - 1) 2 (HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  have ha : 0 ≤ wr13e_a d s τ M := wr13e_a_nonneg hs hsd hτ M
  obtain ⟨a, ha_def⟩ : ∃ a, a = wr13e_a d s τ M := ⟨_, rfl⟩
  rw [← ha_def] at ha hκ
  obtain ⟨Cν, hCν⟩ : ∃ Cν, Cν = Real.exp ((βp * a + 1) + 0 + βp * a) := ⟨_, rfl⟩
  have hCν1 : 1 ≤ Cν := by rw [hCν]; exact Real.one_le_exp (by positivity)
  have hCν0 : 0 ≤ Cν := by linarith
  obtain ⟨CD, hCD0, hD⟩ := wr13e_cavD hd hs hsd hτ βp M hCν1
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀, κ₀ = 4 * Cν * (βp * a) := ⟨_, rfl⟩
  have hκ₀0 : 0 ≤ κ₀ := by rw [hκ₀]; positivity
  obtain ⟨Ccv, Ncv, hCcv0, hcvb⟩ := wr13e_cv_bound hd hs hsd hτ M hCν1 hκ₀0
  obtain ⟨Cphi, hCphi⟩ : ∃ Cphi, Cphi = CD + βp * Ccv + βp * (Cν * a) := ⟨_, rfl⟩
  have hCphi0 : 0 ≤ Cphi := by rw [hCphi]; positivity
  refine ⟨Cν * Cphi, max Ncv 2, ?_⟩
  intro ρ hρ hM β hβ hβp' N hN ht
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  haveI hμp := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hK : EWeakKernel (HRS.Whole.withDensityReal ρ) a (fun x y : Euc d => qTau d s τ (x - y)) := by
    rw [ha_def]; exact wr13e_weak hd hs hsd hτ hρ hM
  have hcal := wr13e_calFeat hΨ
  have hqe : ∀ z : Euc d, qTau d s τ (-z) = qTau d s τ z := fun z => wr12_qTau_even z
  obtain ⟨V, hV⟩ : ∃ V, V = wr13e_weakPotK hK ha hβ.le hcal
      (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β (n + 1)) ht :=
    ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; exact div_nonneg hβ.le (Nat.cast_nonneg _)
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = wr13e_theta V lam n := ⟨_, rfl⟩
  have hθ0 : ∀ x, 0 < θ x := by rw [hθdef]; exact wr13e_theta_pos V hlam0 n
  have hθm : Measurable θ := by rw [hθdef]; exact wr13e_measurable_theta V hlam0 n
  have hθ1 : ∫ x, θ x ∂(HRS.Whole.withDensityReal ρ) = 1 := by
    rw [hθdef]; exact wr13e_integral_theta V hlam0 n
  have hβa : β * a ≤ βp * a := mul_le_mul_of_nonneg_right hβp' ha
  have hVexp : Real.exp (V.M + V.M' + β * V.γ) ≤ Cν := by
    rw [hV, hCν]
    show Real.exp ((β * a + 1) + 0 + β * a) ≤ _
    exact Real.exp_le_exp.2 (by linarith)
  have hκβ : KappaSmall β a := KappaSmall.mono hκ hβ.le ha hβa
  have hκV : weakKappa V β ≤ 1 / 2 := by
    have e : weakKappa V β = 4 * Real.exp (2 * (β * a) + 1) * (β * a) := by
      rw [hV]
      unfold weakKappa
      show 4 * Real.exp ((β * a + 1) + 0 + β * a) * (β * a) = _
      congr 2; ring
    rw [e]; exact hκβ
  have hκVle : weakKappa V β ≤ κ₀ := by
    have e : weakKappa V β = 4 * Real.exp ((β * a + 1) + 0 + β * a) * (β * a) := by
      rw [hV]; rfl
    rw [e, hκ₀, hCν]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num))
      hβa (by positivity) (by positivity)
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hπle : HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) Ψ β (n + 1)) ≤ ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ := by
    refine (wr13e_firstMarginal_RN_leK hK ha hβ hcal (Nat.succ_le_succ (Nat.zero_le n)) ht).trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    rw [hCν]; exact Real.exp_le_exp.2 (by linarith)
  have hπeq := wr13e_firstMarginal_RN_eq hK ha hβ hcal ht (n := n)
  rw [← hV, ← hlam, ← hθdef] at hπeq
  have hνle : RefMarg.cavMarg V lam n ≤ ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ := by
    have h1 := RefMarg.marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simp)
      (fun e : Empty => e.elim) 0
    rw [← hlam] at h1
    refine h1.trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  haveI hνp : IsProbabilityMeasure (RefMarg.cavMarg V lam n) := by
    haveI := isProb_pinnedLaw V hlam0 n (fun e : Empty => e.elim)
    unfold RefMarg.cavMarg; infer_instance
  haveI : IsFiniteMeasure (HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))) :=
    ⟨lt_of_le_of_lt (hπle Set.univ) (by simp [Measure.smul_apply])⟩
  have hπ_ac := HRS.PoleCavityAux.rnDeriv_le_of_le_withDensity (HRS.Whole.withDensityReal ρ)
    (HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) Ψ β (n + 1)))
    (fun _ => ENNReal.ofReal Cν) (by rw [withDensity_const]; exact hπle)
  have hrn : (HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))).rnDeriv (HRS.Whole.withDensityReal ρ)
      =ᵐ[HRS.Whole.withDensityReal ρ] fun y => ENNReal.ofReal (θ y) := by
    rw [hπeq]; exact Measure.rnDeriv_withDensity _ (ENNReal.measurable_ofReal.comp hθm)
  have hθC : ∀ᵐ y ∂(HRS.Whole.withDensityReal ρ), θ y ≤ Cν := by
    filter_upwards [hrn, hπ_ac.2] with y h1 h2
    rw [h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h2
  refine ⟨hπ_ac.1, ?_⟩
  have hfin : (fun y => ((HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))).rnDeriv (HRS.Whole.withDensityReal ρ) y).toReal - 1)
      =ᵐ[HRS.Whole.withDensityReal ρ] fun y => θ y - 1 := by
    filter_upwards [hrn] with y h1
    rw [h1, ENNReal.toReal_ofReal (hθ0 y).le]
  rw [eLpNorm_congr_ae hfin]
  have hCz : ∀ᵐ y ∂(HRS.Whole.withDensityReal ρ), |θ y - 1| ≤ Cν := hθC.mono fun y hy => by
    rw [abs_le]; constructor <;> linarith [hθ0 y]
  have hCz' : ∀ᵐ y ∂(HRS.Whole.withDensityReal ρ), |wr13e_theta
      (wr13e_weakPotK hK ha hβ.le hcal
        (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β (n + 1)) ht)
      (β / ((n + 1 : ℕ) : ℝ)) n y - 1| ≤ Cν := by
    rw [← hV, ← hlam, ← hθdef]; exact hCz
  obtain ⟨c', hc'⟩ := wr13e_cavity_equation (k := kTau d s τ) (q0 := qTau d s τ) hΨ hK ha hqe hβ ht
    (n := n) (Cz := Cν) hCz'
  rw [← hV, ← hlam, ← hθdef] at hc'
  -- the convolution term
  have hTVθ : ∀ A : Set (Euc d), MeasurableSet A →
      |((HRS.Whole.withDensityReal ρ).withDensity (fun y => ENNReal.ofReal (θ y))).real A -
        (RefMarg.cavMarg V lam n).real A| ≤ κ₀ / ((n + 1 : ℕ) : ℝ) := by
    intro A hA
    have hκV' : weakKappa (wr13e_weakPotK hK ha hβ.le hcal
        (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β (n + 1)) ht) β ≤ 1 / 2 := by
      rw [← hV]; exact hκV
    have h1 := wr13e_event_pi_nu hK ha hβ hcal ht hκV' hA (n := n)
    rw [← hV, ← hlam, hπeq] at h1
    refine h1.trans ?_
    exact div_le_div_of_nonneg_right hκVle (Nat.cast_nonneg _)
  obtain ⟨F, hFm, hFid, hFnorm⟩ := hcvb n (le_trans (le_max_left _ _) hN) ρ hρ hM θ hθm hθ0 hθC
    (RefMarg.cavMarg V lam n) hνp hνle hTVθ
  -- the rate
  have hN2 : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have : 2 ≤ n + 1 := by omega
    exact_mod_cast this
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  have hδ0 : 0 ≤ deltaN d s (n + 1) := HRS.deltaN_nonneg s (by omega)
  have hδ1 : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ deltaN d s (n + 1) :=
    HRS.WeakRef.inv_le_deltaN hd hs.le hsd (by omega)
  have hlam_le : lam ≤ β * deltaN d s (n + 1) := by
    have : lam = β * (((n + 1 : ℕ) : ℝ))⁻¹ := by rw [hlam]; ring
    rw [this]; exact mul_le_mul_of_nonneg_left hδ1 hβ.le
  -- the cavity correction `D`
  have hDb : ∀ x, 0 ≤ Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) +
        lam * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V lam n) ∧
      Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) +
        lam * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V lam n) ≤ CD * deltaN d s (n + 1) := by
    intro x
    have := hD ρ hρ hM V (fun _ _ => by rw [hV]; rfl) (by rw [hV]; exact ha_def.le) β hβ hβp' hVexp hκV
      (n + 1) n (Nat.le_succ n) x
    rw [hlam]; exact this
  have hDm : Measurable fun x => Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) +
      lam * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V lam n) := by
    refine ((Real.measurable_log.comp (RefMarg.measurable_cavU V hlam0 n _)).add (measurable_const.mul ?_))
    exact RefMarg.measurable_integral_kernel (F := fun p : Euc d × Euc d => V.q p.2 p.1)
      (V.measurable_q.comp (measurable_snd.prodMk measurable_fst))
  have hDL2 : eLpNorm (fun x => Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) +
      lam * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V lam n)) 2 (HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (CD * deltaN d s (n + 1)) :=
    RefMarg.eLpNorm_two_le_const hDm.aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (hDb x).1]; exact (hDb x).2
  -- the term `lam * q*ν`
  have hq0m : Measurable (qTau d s τ : Euc d → ℝ) := wr12_qTau_meas
  have hQνm : Measurable fun x => ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n) :=
    RefMarg.measurable_integral_kernel (F := fun p : Euc d × Euc d => qTau d s τ (p.1 - p.2))
      (hq0m.comp (measurable_fst.sub measurable_snd))
  have hQb : ∀ x, 0 ≤ ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n) ∧
      ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n) ≤ Cν * a := by
    intro x
    refine ⟨integral_nonneg fun y => qTau_nonneg hs _, ?_⟩
    have hqxi : Integrable (fun y => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) :=
      hK.wr1_integrable_row x
    calc ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n)
        ≤ Cν * ∫ y, qTau d s τ (x - y) ∂(HRS.Whole.withDensityReal ρ) :=
          wr13e_integral_le_of_le_smul hνle hCν0 (fun y => qTau_nonneg hs _) hqxi
      _ ≤ Cν * a := mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hCν0
  have hQL2 : eLpNorm (fun x => lam * ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n)) 2
      (HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (βp * (Cν * a) * deltaN d s (n + 1)) :=
    RefMarg.eLpNorm_two_le_const (hQνm.const_mul lam).aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (mul_nonneg hlam0 (hQb x).1)]
      calc lam * ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n)
          ≤ (β * deltaN d s (n + 1)) * (Cν * a) :=
            mul_le_mul hlam_le (hQb x).2 (hQb x).1 (by positivity)
        _ ≤ βp * (Cν * a) * deltaN d s (n + 1) := by
            have : β * deltaN d s (n + 1) * (Cν * a) = β * (Cν * a) * deltaN d s (n + 1) := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβp' (by positivity)) hδ0
  -- the kernel `K_g`
  have hzm : Measurable fun y => θ y - 1 := hθm.sub_const 1
  have hzb : ∀ᵐ y ∂(HRS.Whole.withDensityReal ρ), ‖θ y - 1‖ ≤ Cν :=
    hCz.mono fun y hy => by rwa [Real.norm_eq_abs]
  have hz2 : MemLp (fun y => θ y - 1) 2 (HRS.Whole.withDensityReal ρ) :=
    MemLp.of_bound hzm.aestronglyMeasurable Cν hzb
  have hM'ρ : ∀ x, ρ x ≤ max M 0 := fun x => (hM x).trans (le_max_left _ _)
  have hKzeq : ∀ x, wr13e_Kt (fun w => kTau d s τ w + qTau d s τ w) (HRS.Whole.withDensityReal ρ)
      (fun y => θ y - 1) x =
      ∫ y, HRS.Whole.rieszKernel d s (x - y) * (θ y - 1) ∂(HRS.Whole.withDensityReal ρ) := by
    intro x
    simp only [wr13e_Kt]
    refine integral_congr_ae ?_
    filter_upwards [wr3_ae_ne hd ρ x] with y hy
    have hz : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    rw [riesz_heat_split hs hτ hz]
    ring
  obtain ⟨CS, hCS0, hCS⟩ := wr13c_schur_W_real hd hs.le hsd (max M 0)
  have hSchur := (hCS ρ hρ hM'ρ 1 zero_le_one (fun x y => HRS.Whole.rieszKernel d s (x - y))
      ((HRS.Whole.Q34.measurable_rieszKernel hs.ne').comp (measurable_fst.sub measurable_snd))
      (fun x y hxy => by
        have h1 := wr13e_g_eq_weight (d := d) hs (x - y)
        have h2 := wr3_rieszWeight_nonneg (d := d) s (x - y)
        show |HRS.Whole.rieszKernel d s (x - y)| ≤ 1 * (1 + HRS.Whole.rieszWeight s (x - y))
        rw [h1, abs_of_nonneg h2]; linarith)
      (fun y => θ y - 1) hzm hz2).1
  have hKeq : (fun x => wr13e_Kt (fun w => kTau d s τ w + qTau d s τ w) (HRS.Whole.withDensityReal ρ)
      (fun y => θ y - 1) x) =
      fun x => ∫ y, HRS.Whole.rieszKernel d s (x - y) * (θ y - 1) ∂(HRS.Whole.withDensityReal ρ) :=
    funext hKzeq
  have hKz2 : MemLp (fun x => wr13e_Kt (fun w => kTau d s τ w + qTau d s τ w)
      (HRS.Whole.withDensityReal ρ) (fun y => θ y - 1) x) 2 (HRS.Whole.withDensityReal ρ) := by
    rw [hKeq]; exact hSchur
  have hnn : 0 ≤ ∫ x, wr13e_Kt (fun w => kTau d s τ w + qTau d s τ w) (HRS.Whole.withDensityReal ρ)
      (fun y => θ y - 1) x * (θ x - 1) ∂(HRS.Whole.withDensityReal ρ) := by
    have := (wr13c_Kmu_nonneg hd hs hsd hρ hM'ρ hzm hz2).2
    simp_rw [hKzeq]; exact this
  -- the equation
  have heq : ∀ x, Real.log (θ x) + β * wr13e_Kt (fun w => kTau d s τ w + qTau d s τ w)
        (HRS.Whole.withDensityReal ρ) (fun y => θ y - 1) x =
      (Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) +
        lam * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V lam n)) + β * F x +
      lam * ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n) + c' := by
    intro x
    have := hc' x
    rw [hFid x] at this
    linarith
  have hass := wr13e_L2_assemble (μ := HRS.Whole.withDensityReal ρ) (lam := lam) (e1 := CD * deltaN d s (n + 1))
    (e2 := Ccv * deltaN d s (n + 1)) (e3 := βp * (Cν * a) * deltaN d s (n + 1)) hβ.le hCν1 hθm hθ0 hθC hθ1
    hDm hFm hQνm hDL2 hFnorm hQL2 (by positivity) (by positivity) (by positivity) hKz2 hnn heq
  refine hass.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hCphi]
  have hδ' := hδ0
  have : β * (Ccv * deltaN d s (n + 1)) ≤ βp * (Ccv * deltaN d s (n + 1)) :=
    mul_le_mul_of_nonneg_right hβp' (by positivity)
  have h2 : Cν * (CD * deltaN d s (n + 1) + β * (Ccv * deltaN d s (n + 1)) +
      βp * (Cν * a) * deltaN d s (n + 1)) ≤
      Cν * (CD * deltaN d s (n + 1) + βp * (Ccv * deltaN d s (n + 1)) +
      βp * (Cν * a) * deltaN d s (n + 1)) := by gcongr
  refine h2.trans (le_of_eq ?_)
  ring

end Core

section Small

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Uniform smallness of the calibration field** `‖⟪t_N, Ξ⟫‖_∞ → 0` (torus `small_field`): for every
`ε > 0` there is `N₀` with `|⟪t_N, Ξ x⟫| ≤ ε` for all `N ≥ N₀`, `β ∈ (0, βp]`, `ρ ≤ M`.  Obtained from
`euc_field_small` applied to the rescaled feature map `ε'⁻¹ Ψ`. -/
theorem wr13e_field_small_eps (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (βp M : ℝ) {Ψ : Euc d → H} (hΨ : FeatHyp Ψ (kTau d s τ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N₀ ≤ N → ∀ x : Euc d,
        |inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)
          (Xi (HRS.Whole.withDensityReal ρ) Ψ x)| ≤ ε := by
  intro ε hε
  set ε' : ℝ := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  set c : ℝ := ε'⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 hε'0
  have hc1 : 1 ≤ c := one_le_inv_iff₀.2 ⟨hε'0, hε'1⟩
  have hcal := wr13e_calFeat hΨ
  set B : ℝ := Real.sqrt (kTau d s τ 0) with hB
  have hcal' : CalFeat (fun x => c • Ψ x) (c * B) :=
    ⟨continuous_const.smul hcal.cont, fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
      exact mul_le_mul_of_nonneg_left (hcal.bound x) hc0.le⟩
  obtain ⟨N0, hN01, hN0⟩ := euc_field_small hd hs hsd βp M (c * B) (H := H)
  refine ⟨N0, fun ρ hρ hM β hβ hβp N hN x => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hK := wr13e_weak hd hs hsd hτ hρ hM
  have hN' : 0 < N := by omega
  have h1 := tN_norm_le hK hcal hβ hN'
  have hXi : ∀ y, Xi μ (fun x => c • Ψ x) y = c • Xi μ Ψ y := fun y => by
    unfold Xi
    rw [integral_smul, smul_sub]
  have hemp : ∀ X : Fin N → Euc d, empXi μ (fun x => c • Ψ x) X = c • empXi μ Ψ X := fun X => by
    unfold empXi
    simp_rw [hXi]
    rw [← Finset.smul_sum, smul_comm]
  have hint : ∫ X, empXi μ (fun x => c • Ψ x) X ∂(pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) N β μ)
      = c • ∫ X, empXi μ Ψ X ∂(pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) N β μ) := by
    simp_rw [hemp]
    exact integral_smul _ _
  have hcond : ‖tN (fun x y : Euc d => qTau d s τ (x - y)) μ Ψ β N‖ ≤ β * ‖∫ X, empXi μ (fun x => c • Ψ x) X
      ∂(pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) N β μ)‖ := by
    rw [hint, norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    exact le_mul_of_one_le_left (norm_nonneg _) hc1
  have h2 := hN0 τ hτ ρ hρ hM β hβ hβp N hN (fun x => c • Ψ x) hcal' _ hcond x
  rw [hXi, real_inner_smul_right, abs_mul, abs_of_pos hc0] at h2
  have h3 : |inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) μ Ψ β N) (Xi μ Ψ x)| ≤ ε' := by
    have : |inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) μ Ψ β N) (Xi μ Ψ x)| * c ≤ 1 := by
      linarith
    have e : |inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) μ Ψ β N) (Xi μ Ψ x)| =
        (|inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) μ Ψ β N) (Xi μ Ψ x)| * c) * ε' := by
      rw [hc]; field_simp
    rw [e]
    calc _ ≤ 1 * ε' := mul_le_mul_of_nonneg_right this hε'0.le
      _ = ε' := one_mul _
  exact h3.trans (min_le_left _ _)

end Small

section Final

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Ψ : Euc d → H}

/-- **`‖dπ^R_N/dμ - 1‖_{L²(μ)} ≤ C δ_N`** (TeX `euc-reference-marginal`, second bound; torus
`reference_marginal_density_L2`), uniformly in the probability densities `ρ ≤ M` and `β ∈ (0, βp]`. -/
theorem wr13e_reference_marginal_density_L2 (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (βp M : ℝ) (hβp : 0 < βp) (hκ : KappaSmall βp (wr13e_a d s τ M))
    (hΨ : FeatHyp Ψ (kTau d s τ)) :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N₀ ≤ N →
      HRS.Whole.firstMarginal
          (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)
        ≪ HRS.Whole.withDensityReal ρ ∧
        eLpNorm (fun y => ((HRS.Whole.firstMarginal
            (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)).rnDeriv
            (HRS.Whole.withDensityReal ρ) y).toReal - 1) 2 (HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨C, N1, hcore⟩ := wr13e_core_L2 hd hs hsd hτ βp M hβp hκ hΨ
  obtain ⟨N2, hsmall⟩ := wr13e_field_small_eps hd hs hsd hτ βp M hΨ 1 one_pos
  refine ⟨C, max N1 N2, fun ρ hρ hM β hβ hβp' N hN => ?_⟩
  exact hcore ρ hρ hM β hβ hβp' N (le_trans (le_max_left _ _) hN)
    (fun x => hsmall ρ hρ hM β hβ hβp' N (le_trans (le_max_right _ _) hN) x)

end Final

section ConvDiff

open HRS.External.Entropy in
/-- **Truncation estimate** (torus `conv_diff_le`): for probability measures `P, Q ≤ Cb μ` and a nonnegative
measurable row `r` with `∫ (r - K)₊ dμ ≤ T`, `|∫ r dP - ∫ r dQ| ≤ K ‖P - Q‖_TV + 2 Cb T`. -/
theorem wr13e_conv_diff_le {α : Type*} [MeasurableSpace α] {μ P Q : Measure α} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {Cb : ℝ} (hCb : 0 ≤ Cb) (hP : P ≤ ENNReal.ofReal Cb • μ)
    (hQ : Q ≤ ENNReal.ofReal Cb • μ) {r : α → ℝ} (hrm : Measurable r) (hr0 : ∀ y, 0 ≤ r y) {K T : ℝ}
    (hK : 0 ≤ K) (hTi : Integrable (fun y => max (r y - K) 0) μ)
    (hT : ∫ y, max (r y - K) 0 ∂μ ≤ T) :
    |∫ y, r y ∂P - ∫ y, r y ∂Q| ≤ K * tvDist P Q + 2 * (Cb * T) := by
  set g1 : α → ℝ := fun y => min (r y) K with hg1
  set g2 : α → ℝ := fun y => max (r y - K) 0 with hg2
  have hg1m : Measurable g1 := hrm.min measurable_const
  have hg2m : Measurable g2 := (hrm.sub_const K).max measurable_const
  have hg10 : ∀ y, 0 ≤ g1 y := fun y => le_min (hr0 y) hK
  have hg20 : ∀ y, 0 ≤ g2 y := fun y => le_max_right _ _
  have hsplit : ∀ y, r y = g1 y + g2 y := by
    intro y
    simp only [hg1, hg2]
    rcases le_total (r y) K with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have hg2i : ∀ Pm : Measure α, Pm ≤ ENNReal.ofReal Cb • μ → Integrable g2 Pm := fun Pm h =>
    Integrable.mono_measure (hTi.smul_measure ENNReal.ofReal_ne_top) h
  have hg1i : ∀ (Pm : Measure α) [IsProbabilityMeasure Pm], Integrable g1 Pm := fun Pm _ =>
    Integrable.of_bound hg1m.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg10 y)]; exact min_le_right _ _)
  have e : ∀ (Pm : Measure α) [IsProbabilityMeasure Pm], Pm ≤ ENNReal.ofReal Cb • μ →
      ∫ y, r y ∂Pm = ∫ y, g1 y ∂Pm + ∫ y, g2 y ∂Pm := by
    intro Pm _ hR
    rw [← integral_add (hg1i Pm) (hg2i Pm hR)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hsplit y)
  have hI2 : ∀ Pm : Measure α, Pm ≤ ENNReal.ofReal Cb • μ → ∫ y, g2 y ∂Pm ≤ Cb * T := fun Pm hR =>
    (wr13e_integral_le_of_le_smul hR hCb hg20 hTi).trans (mul_le_mul_of_nonneg_left hT hCb)
  have hI20 : ∀ Pm : Measure α, 0 ≤ ∫ y, g2 y ∂Pm := fun Pm => integral_nonneg hg20
  rw [e P hP, e Q hQ]
  have hTV := wr12_abs_integral_sub_le_tvDist_of_nonneg P Q hg1m hK hg10 (fun y => min_le_right _ _)
  have h2 := hI2 P hP
  have h3 := hI2 Q hQ
  have h4 := hI20 P
  have h5 := hI20 Q
  rw [abs_le] at hTV ⊢
  constructor <;> linarith [hTV.1, hTV.2]

end ConvDiff

section Unif

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Ψ : Euc d → H}

set_option maxHeartbeats 1600000 in
/-- **Uniform core** (torus `core_unif`): `‖dπ_N/dμ - 1‖_∞ → 0` uniformly, given the uniform smallness of
the calibration field and of `‖π⁰_N - μ‖_TV`. -/
theorem wr13e_core_unif (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (βp M : ℝ) (hβp : 0 < βp) (hκ : KappaSmall βp (wr13e_a d s τ M))
    (hΨ : FeatHyp Ψ (kTau d s τ))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N₀ ≤ N → ∀ x : Euc d,
        |inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)
          (Xi (HRS.Whole.withDensityReal ρ) Ψ x)| ≤ ε)
    {ε₀ : ℕ → ℝ} (hε₀ : Tendsto ε₀ atTop (𝓝 0)) {N₃ : ℕ}
    (hTV0 : ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ β : ℝ, 0 < β → β ≤ βp →
      ∀ n : ℕ, N₃ ≤ n + 1 → 1 ≤ n →
      HRS.External.Entropy.tvDist (HRS.Whole.firstMarginal
        (pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) (n + 1) β (HRS.Whole.withDensityReal ρ)))
        (HRS.Whole.withDensityReal ρ) ≤ ε₀ (n + 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₁ : ℕ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N₁ ≤ N →
      HRS.Whole.firstMarginal
          (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)
        ≪ HRS.Whole.withDensityReal ρ ∧
        ∀ᵐ y ∂(HRS.Whole.withDensityReal ρ),
          |((HRS.Whole.firstMarginal
            (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)).rnDeriv
            (HRS.Whole.withDensityReal ρ) y).toReal - 1| ≤ ε := by
  intro ε hε
  have hd1 : 1 ≤ d := by omega
  have ha : 0 ≤ wr13e_a d s τ M := wr13e_a_nonneg hs hsd hτ M
  obtain ⟨a, ha_def⟩ : ∃ a, a = wr13e_a d s τ M := ⟨_, rfl⟩
  rw [← ha_def] at ha hκ
  obtain ⟨Cν, hCν⟩ : ∃ Cν, Cν = Real.exp ((βp * a + 1) + 0 + βp * a) := ⟨_, rfl⟩
  have hCν1 : 1 ≤ Cν := by rw [hCν]; exact Real.one_le_exp (by positivity)
  have hCν0 : 0 ≤ Cν := by linarith
  obtain ⟨CD, hCD0, hD⟩ := wr13e_cavD hd1 hs hsd hτ βp M hCν1
  obtain ⟨Ca, Cb, hCa, hCb, hrow⟩ := wr3_row_bounds_real_integral hd1 hs.le hsd 1 (max M 0)
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀, κ₀ = 4 * Cν * (βp * a) := ⟨_, rfl⟩
  have hκ₀0 : 0 ≤ κ₀ := by rw [hκ₀]; positivity
  -- the exponent of the tail bound
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = HRS.WeakRef.sigmaOf d s := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; exact HRS.WeakRef.sigmaOf_pos hd1 hs.le
  have hσd : σ < d := by rw [hσ]; exact HRS.WeakRef.sigmaOf_lt hd1 hsd
  rw [← hσ] at hrow
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 - (d : ℝ) / σ := ⟨_, rfl⟩
  rw [← he] at hrow
  have hepos : 0 < (d : ℝ) / σ - 1 := by
    have : 1 < (d : ℝ) / σ := by rw [lt_div_iff₀ hσ0]; linarith
    linarith
  -- the constants
  obtain ⟨Es, hEs⟩ : ∃ Es, Es = Real.log (1 + ε) / 2 := ⟨_, rfl⟩
  have hEs0 : 0 < Es := by
    have : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    rw [hEs]; positivity
  obtain ⟨ε', hε'⟩ : ∃ ε', ε' = Es / 5 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hKex : ∃ K : ℝ, 1 ≤ K ∧ 2 * (βp * (Cν * (Ca * K ^ e))) ≤ ε' := by
    have hlim : Tendsto (fun K : ℝ => K ^ (-((d : ℝ) / σ - 1))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hepos
    have hlim2 : Tendsto (fun K : ℝ => 2 * (βp * (Cν * (Ca * K ^ (-((d : ℝ) / σ - 1)))))) atTop (𝓝 0) := by
      have := (((hlim.const_mul Ca).const_mul Cν).const_mul βp).const_mul 2
      simpa using this
    obtain ⟨K, hK⟩ := (eventually_ge_atTop (1 : ℝ)).and (hlim2.eventually (gt_mem_nhds hε'0)) |>.exists
    refine ⟨K, hK.1, ?_⟩
    have e' : e = -((d : ℝ) / σ - 1) := by rw [he]; ring
    rw [e']; exact hK.2.le
  obtain ⟨K, hK1, hKT⟩ := hKex
  have hKpos : 0 < K := by linarith
  obtain ⟨τ', hτ'⟩ : ∃ τ', τ' = ε' / (βp * K) := ⟨_, rfl⟩
  have hτ'0 : 0 < τ' := by rw [hτ']; positivity
  obtain ⟨εh, hεh⟩ : ∃ εh, εh = min 1 (min ε' (τ' / (12 * Cν))) := ⟨_, rfl⟩
  have hεh0 : 0 < εh := by
    rw [hεh]
    refine lt_min one_pos (lt_min hε'0 ?_)
    have : 0 < 12 * Cν := by positivity
    positivity
  have hεh1 : εh ≤ 1 := by rw [hεh]; exact min_le_left _ _
  have hεh2 : εh ≤ ε' := by rw [hεh]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hεh3 : 4 * Cν * εh ≤ τ' / 3 := by
    have h1 : εh ≤ τ' / (12 * Cν) := by rw [hεh]; exact (min_le_right _ _).trans (min_le_right _ _)
    have h12 : 0 < 12 * Cν := by positivity
    calc 4 * Cν * εh ≤ 4 * Cν * (τ' / (12 * Cν)) := by gcongr
      _ = τ' / 3 := by field_simp; ring
  obtain ⟨Nh, hNh⟩ := hsmall εh hεh0
  -- the large-`N` conditions
  have hb : ∀ᶠ N : ℕ in atTop, κ₀ / (N : ℝ) ≤ τ' / 3 := by
    have : Tendsto (fun N : ℕ => κ₀ / (N : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat κ₀
    exact this.eventually (ge_mem_nhds (by positivity))
  have hc' : ∀ᶠ N : ℕ in atTop, ε₀ N ≤ τ' / 3 := hε₀.eventually (ge_mem_nhds (by positivity))
  have hd' : ∀ᶠ N : ℕ in atTop, βp * (Cν * a) / (N : ℝ) ≤ ε' := by
    have : Tendsto (fun N : ℕ => βp * (Cν * a) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    exact this.eventually (ge_mem_nhds hε'0)
  have he' : ∀ᶠ N : ℕ in atTop, CD * deltaN d s N ≤ ε' := by
    have := (RefMarg.tendsto_deltaN hd hs.le hsd).const_mul CD
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds hε'0)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hb.and (hc'.and (hd'.and he')))
  refine ⟨max (max (max Nh N₂) 2) N₃, fun ρ hρ hM β hβ hβp' N hN0' => ?_⟩
  have hN : max (max Nh N₂) 2 ≤ N := le_trans (le_max_left _ _) hN0'
  have hN3 : N₃ ≤ N := le_trans (le_max_right _ _) hN0'
  have hNh' : Nh ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hNb, hNc, hNd, hNe⟩ := hN₂ N hN₂'
  have hεhN := hNh ρ hρ hM β hβ hβp' N hNh'
  have ht : ∀ x, |inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)
      (Xi (HRS.Whole.withDensityReal ρ) Ψ x)| ≤ 1 := fun x => (hεhN x).trans hεh1
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  haveI hμp := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hK : EWeakKernel (HRS.Whole.withDensityReal ρ) a (fun x y : Euc d => qTau d s τ (x - y)) := by
    rw [ha_def]; exact wr13e_weak hd1 hs hsd hτ hρ hM
  have hcal := wr13e_calFeat hΨ
  have hqe : ∀ z : Euc d, qTau d s τ (-z) = qTau d s τ z := fun z => wr12_qTau_even z
  obtain ⟨V, hV⟩ : ∃ V, V = wr13e_weakPotK hK ha hβ.le hcal
      (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β (n + 1)) ht :=
    ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; exact div_nonneg hβ.le (Nat.cast_nonneg _)
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = wr13e_theta V lam n := ⟨_, rfl⟩
  have hθ0 : ∀ x, 0 < θ x := by rw [hθdef]; exact wr13e_theta_pos V hlam0 n
  have hθm : Measurable θ := by rw [hθdef]; exact wr13e_measurable_theta V hlam0 n
  have hβa : β * a ≤ βp * a := mul_le_mul_of_nonneg_right hβp' ha
  have hVexp : Real.exp (V.M + V.M' + β * V.γ) ≤ Cν := by
    rw [hV, hCν]
    show Real.exp ((β * a + 1) + 0 + β * a) ≤ _
    exact Real.exp_le_exp.2 (by linarith)
  have hκβ : KappaSmall β a := KappaSmall.mono hκ hβ.le ha hβa
  have hκV : weakKappa V β ≤ 1 / 2 := by
    have e : weakKappa V β = 4 * Real.exp (2 * (β * a) + 1) * (β * a) := by
      rw [hV]
      unfold weakKappa
      show 4 * Real.exp ((β * a + 1) + 0 + β * a) * (β * a) = _
      congr 2; ring
    rw [e]; exact hκβ
  have hκVle : weakKappa V β ≤ κ₀ := by
    have e : weakKappa V β = 4 * Real.exp ((β * a + 1) + 0 + β * a) * (β * a) := by
      rw [hV]; rfl
    rw [e, hκ₀, hCν]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num))
      hβa (by positivity) (by positivity)
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hπle : HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) Ψ β (n + 1)) ≤ ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ := by
    refine (wr13e_firstMarginal_RN_leK hK ha hβ hcal (Nat.succ_le_succ (Nat.zero_le n)) ht).trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    rw [hCν]; exact Real.exp_le_exp.2 (by linarith)
  have hπeq := wr13e_firstMarginal_RN_eq hK ha hβ hcal ht (n := n)
  rw [← hV, ← hlam, ← hθdef] at hπeq
  have hνle : RefMarg.cavMarg V lam n ≤ ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ := by
    have h1 := RefMarg.marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simp)
      (fun e : Empty => e.elim) 0
    rw [← hlam] at h1
    refine h1.trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  haveI hνp : IsProbabilityMeasure (RefMarg.cavMarg V lam n) := by
    haveI := isProb_pinnedLaw V hlam0 n (fun e : Empty => e.elim)
    unfold RefMarg.cavMarg; infer_instance
  haveI : IsFiniteMeasure (HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))) :=
    ⟨lt_of_le_of_lt (hπle Set.univ) (by simp [Measure.smul_apply])⟩
  have hπ_ac := HRS.PoleCavityAux.rnDeriv_le_of_le_withDensity (HRS.Whole.withDensityReal ρ)
    (HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) Ψ β (n + 1)))
    (fun _ => ENNReal.ofReal Cν) (by rw [withDensity_const]; exact hπle)
  refine ⟨hπ_ac.1, ?_⟩
  have hrn : (HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))).rnDeriv (HRS.Whole.withDensityReal ρ)
      =ᵐ[HRS.Whole.withDensityReal ρ] fun y => ENNReal.ofReal (θ y) := by
    rw [hπeq]; exact Measure.rnDeriv_withDensity _ (ENNReal.measurable_ofReal.comp hθm)
  -- total variation of `μ` and `ν`
  have hTVμν : HRS.External.Entropy.tvDist (HRS.Whole.withDensityReal ρ) (RefMarg.cavMarg V lam n) ≤ τ' := by
    refine RefMarg.tvDist_le_of_forall _ _ fun A hA => ?_
    haveI hR0p : IsProbabilityMeasure (pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) (n + 1) β
        (HRS.Whole.withDensityReal ρ)) := hK.wr11_isProb_R0 hβ.le hN0
    have hR0m : HRS.Whole.firstMarginal (pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) (n + 1) β
        (HRS.Whole.withDensityReal ρ)) =
        (pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) (n + 1) β (HRS.Whole.withDensityReal ρ)).map
          (fun X => X ⟨0, Nat.succ_pos n⟩) := by
      unfold HRS.Whole.firstMarginal; rw [dif_pos (Nat.succ_pos n)]
    haveI hR0mp : IsProbabilityMeasure ((pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) (n + 1) β
        (HRS.Whole.withDensityReal ρ)).map (fun X => X ⟨0, Nat.succ_pos n⟩)) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 inferInstance
    have h1 := hTV0 ρ hρ hM β hβ hβp' n hN3 hn
    rw [hR0m] at h1
    have h1' := HRS.External.Entropy.abs_le_tvDist ((pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y))
      (n + 1) β (HRS.Whole.withDensityReal ρ)).map (fun X => X ⟨0, Nat.succ_pos n⟩))
      (HRS.Whole.withDensityReal ρ) hA
    have hκV' : weakKappa (wr13e_weakPotK hK ha hβ.le hcal
        (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β (n + 1)) ht) β ≤ 1 / 2 := by
      rw [← hV]; exact hκV
    have h2 := wr13e_tv_RN_R0 hK ha hβ hcal ht hκV' hεhN hA (n := n)
    have h3 := wr13e_event_pi_nu hK ha hβ hcal ht hκV' hA (n := n)
    rw [← hV, ← hlam] at h3
    have hexp : 4 * Real.exp ((β * a + 1) + 0 + β * a) * εh ≤ 4 * Cν * εh := by
      refine mul_le_mul_of_nonneg_right ?_ hεh0.le
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [hCν]; exact Real.exp_le_exp.2 (by linarith)
    have hA1 : |((pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) (n + 1) β
        (HRS.Whole.withDensityReal ρ)).map (fun X => X ⟨0, Nat.succ_pos n⟩)).real A -
        (HRS.Whole.withDensityReal ρ).real A| ≤ τ' / 3 := h1'.trans (h1.trans hNc)
    have hA2 : |(HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
        (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))).real A -
        ((pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) (n + 1) β
        (HRS.Whole.withDensityReal ρ)).map (fun X => X ⟨0, Nat.succ_pos n⟩)).real A| ≤ τ' / 3 :=
      h2.trans (hexp.trans hεh3)
    have hA3 : |(HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
        (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))).real A - (RefMarg.cavMarg V lam n).real A| ≤ τ' / 3 :=
      h3.trans ((div_le_div_of_nonneg_right hκVle (Nat.cast_nonneg _)).trans hNb)
    rw [abs_le] at hA1 hA2 hA3 ⊢
    constructor <;> linarith [hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2]
  -- the pointwise bound of `φ + log u`
  have hM'ρ : ∀ x, ρ x ≤ max M 0 := fun x => (hM x).trans (le_max_left _ _)
  have hμle : HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ := by
    intro A
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hCν1)
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hVqx : ∀ x y, V.q y x = qTau d s τ (x - y) := fun x y => by
    rw [hV]
    show qTau d s τ (y - x) = qTau d s τ (x - y)
    rw [← hqe (x - y), neg_sub]
  obtain ⟨Dfun, hDfun⟩ : ∃ Dfun : Euc d → ℝ, Dfun = fun x => Real.log (RefMarg.cavU V lam n
      (fun e : Empty => e.elim) x) + lam * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V lam n) := ⟨_, rfl⟩
  obtain ⟨Qν, hQν⟩ : ∃ Qν : Euc d → ℝ, Qν = fun x => ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n) :=
    ⟨_, rfl⟩
  obtain ⟨gfun, hgfun⟩ : ∃ gfun : Euc d → ℝ, gfun = fun x => V.φ x +
      Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) := ⟨_, rfl⟩
  have hQb : ∀ x, 0 ≤ Qν x ∧ Qν x ≤ Cν * a := by
    intro x
    rw [hQν]
    refine ⟨integral_nonneg fun y => qTau_nonneg hs _, ?_⟩
    have hqxi : Integrable (fun y => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) :=
      hK.wr1_integrable_row x
    calc ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n)
        ≤ Cν * ∫ y, qTau d s τ (x - y) ∂(HRS.Whole.withDensityReal ρ) :=
          wr13e_integral_le_of_le_smul hνle hCν0 (fun y => qTau_nonneg hs _) hqxi
      _ ≤ Cν * a := mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hCν0
  have hn1 : lam * n = β - lam := by
    have : lam * ((n : ℝ) + 1) = β := by rw [hlam]; push_cast; field_simp
    linarith
  have hDb : ∀ x, 0 ≤ Dfun x ∧ Dfun x ≤ CD * deltaN d s (n + 1) := by
    intro x
    have := hD ρ hρ hM V (fun _ _ => by rw [hV]; rfl) (by rw [hV]; exact ha_def.le) β hβ hβp' hVexp hκV
      (n + 1) n (Nat.le_succ n) x
    rw [← hlam] at this
    rw [hDfun]; exact this
  have hgb : ∀ x, |gfun x| ≤ Es := by
    intro x
    have hqxm : Measurable fun y : Euc d => qTau d s τ (x - y) :=
      (wr12_qTau_meas (d := d) (s := s) (τ := τ)).comp (measurable_const.sub measurable_id)
    have hrowx := hrow ρ hρ hM'ρ (fun x y : Euc d => qTau d s τ (x - y)) hK.meas
      (fun x y => qTau_nonneg hs _) (fun x y hxy => wr13e_qTau_envelope hs hτ (sub_ne_zero.2 hxy)) x
    obtain ⟨hTi, hTb⟩ := hrowx.1 K hKpos
    have hdiff := wr13e_conv_diff_le (μ := HRS.Whole.withDensityReal ρ) (P := HRS.Whole.withDensityReal ρ)
      (Q := RefMarg.cavMarg V lam n) hCν0 hμle hνle hqxm (fun y => qTau_nonneg hs _) hKpos.le hTi hTb
    have hd1' : |(∫ y, qTau d s τ (x - y) ∂(HRS.Whole.withDensityReal ρ)) - Qν x| ≤
        K * τ' + 2 * (Cν * (Ca * K ^ e)) := by
      have hQx : Qν x = ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n) := by rw [hQν]
      rw [hQx]
      refine hdiff.trans ?_
      have : K * HRS.External.Entropy.tvDist (HRS.Whole.withDensityReal ρ) (RefMarg.cavMarg V lam n) ≤ K * τ' :=
        mul_le_mul_of_nonneg_left hTVμν hKpos.le
      linarith
    have ex : gfun x = β * ((∫ y, qTau d s τ (x - y) ∂(HRS.Whole.withDensityReal ρ)) - Qν x) + lam * Qν x +
        inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))
          (Xi (HRS.Whole.withDensityReal ρ) Ψ x) + Dfun x := by
      have e1 : V.φ x = β * ∫ y, qTau d s τ (x - y) ∂(HRS.Whole.withDensityReal ρ) +
          inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))
            (Xi (HRS.Whole.withDensityReal ρ) Ψ x) := by rw [hV]; rfl
      have e2 : Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) = Dfun x - lam * n * Qν x := by
        rw [hDfun, hQν]
        simp only
        have : (∫ y, V.q y x ∂(RefMarg.cavMarg V lam n)) = ∫ y, qTau d s τ (x - y) ∂(RefMarg.cavMarg V lam n) := by
          simp_rw [hVqx x]
        rw [this]; ring
      rw [hgfun]
      simp only
      rw [e1, e2, hn1]
      ring
    have h1 : |β * ((∫ y, qTau d s τ (x - y) ∂(HRS.Whole.withDensityReal ρ)) - Qν x)| ≤ ε' + ε' := by
      rw [abs_mul, abs_of_pos hβ]
      calc β * |(∫ y, qTau d s τ (x - y) ∂(HRS.Whole.withDensityReal ρ)) - Qν x|
          ≤ βp * (K * τ' + 2 * (Cν * (Ca * K ^ e))) :=
            mul_le_mul hβp' hd1' (abs_nonneg _) hβp.le
        _ = βp * K * τ' + 2 * (βp * (Cν * (Ca * K ^ e))) := by ring
        _ ≤ ε' + ε' := by
            have : βp * K * τ' = ε' := by rw [hτ']; field_simp
            linarith
    have h2 : |lam * Qν x| ≤ ε' := by
      rw [abs_of_nonneg (mul_nonneg hlam0 (hQb x).1)]
      calc lam * Qν x ≤ lam * (Cν * a) := mul_le_mul_of_nonneg_left (hQb x).2 hlam0
        _ = β * (Cν * a) / ((n + 1 : ℕ) : ℝ) := by rw [hlam]; ring
        _ ≤ βp * (Cν * a) / ((n + 1 : ℕ) : ℝ) := by
            gcongr
        _ ≤ ε' := hNd
    have h3 := (hεhN x).trans hεh2
    have h4 : |Dfun x| ≤ ε' := by
      rw [abs_of_nonneg (hDb x).1]; exact (hDb x).2.trans hNe
    rw [ex]
    have := abs_add_le (β * ((∫ y, qTau d s τ (x - y) ∂(HRS.Whole.withDensityReal ρ)) - Qν x) + lam * Qν x +
      inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))
        (Xi (HRS.Whole.withDensityReal ρ) Ψ x)) (Dfun x)
    have := abs_add_le (β * ((∫ y, qTau d s τ (x - y) ∂(HRS.Whole.withDensityReal ρ)) - Qν x) + lam * Qν x)
      (inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β (n + 1))
        (Xi (HRS.Whole.withDensityReal ρ) Ψ x))
    have := abs_add_le (β * ((∫ y, qTau d s τ (x - y) ∂(HRS.Whole.withDensityReal ρ)) - Qν x)) (lam * Qν x)
    have hEs5 : Es = 5 * ε' := by rw [hε']; ring
    linarith
  -- normalisation
  have hZeq : ∫ x, RefMarg.cavTheta V lam n (fun e : Empty => e.elim) x ∂(HRS.Whole.withDensityReal ρ) =
      ∫ x, Real.exp (gfun x) ∂(HRS.Whole.withDensityReal ρ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Real.exp (pinField V lam (fun e : Empty => e.elim) x) *
        RefMarg.cavU V lam n (fun e : Empty => e.elim) x = Real.exp (gfun x)
    rw [hgfun]
    simp only
    rw [Real.exp_add, Real.exp_log (RefMarg.cavU_pos V hlam0 (fun e : Empty => e.elim) n x),
      RefMarg.pinField_empty]
  have hZi : Integrable (fun x => Real.exp (gfun x)) (HRS.Whole.withDensityReal ρ) := by
    have e : (fun x => Real.exp (gfun x)) =
        fun x => RefMarg.cavTheta V lam n (fun e : Empty => e.elim) x := by
      funext x
      show Real.exp (gfun x) = Real.exp (pinField V lam (fun e : Empty => e.elim) x) *
        RefMarg.cavU V lam n (fun e : Empty => e.elim) x
      rw [hgfun]
      simp only
      rw [Real.exp_add, Real.exp_log (RefMarg.cavU_pos V hlam0 (fun e : Empty => e.elim) n x),
        RefMarg.pinField_empty]
    rw [e]
    exact RefMarg.integrable_cavTheta V hlam0 (fun e : Empty => e.elim) n
  have hZhi : ∫ x, Real.exp (gfun x) ∂(HRS.Whole.withDensityReal ρ) ≤ Real.exp Es := by
    calc ∫ x, Real.exp (gfun x) ∂(HRS.Whole.withDensityReal ρ) ≤ ∫ _x, Real.exp Es ∂(HRS.Whole.withDensityReal ρ) :=
          integral_mono hZi (integrable_const _) fun x => Real.exp_le_exp.2 ((abs_le.1 (hgb x)).2)
      _ = Real.exp Es := by simp
  have hZlo : Real.exp (-Es) ≤ ∫ x, Real.exp (gfun x) ∂(HRS.Whole.withDensityReal ρ) := by
    calc Real.exp (-Es) = ∫ _x, Real.exp (-Es) ∂(HRS.Whole.withDensityReal ρ) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hZi fun x => Real.exp_le_exp.2 ((abs_le.1 (hgb x)).1)
  have hlogZ : |Real.log (∫ x, RefMarg.cavTheta V lam n (fun e : Empty => e.elim) x
      ∂(HRS.Whole.withDensityReal ρ))| ≤ Es := by
    rw [hZeq]
    have hZpos : 0 < ∫ x, Real.exp (gfun x) ∂(HRS.Whole.withDensityReal ρ) :=
      lt_of_lt_of_le (Real.exp_pos _) hZlo
    rw [abs_le]
    constructor
    · calc -Es = Real.log (Real.exp (-Es)) := (Real.log_exp _).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos _) hZlo
    · calc Real.log (∫ x, Real.exp (gfun x) ∂(HRS.Whole.withDensityReal ρ)) ≤ Real.log (Real.exp Es) :=
            Real.log_le_log hZpos hZhi
        _ = Es := Real.log_exp _
  have hlogθ : ∀ x, |Real.log (θ x)| ≤ 2 * Es := by
    intro x
    have h0 := wr13e_log_theta_eq V hlam0 n x
    rw [← hθdef] at h0
    have e : Real.log (θ x) = gfun x - Real.log (∫ x', RefMarg.cavTheta V lam n
        (fun e : Empty => e.elim) x' ∂(HRS.Whole.withDensityReal ρ)) := by
      rw [h0, hgfun]
    rw [e]
    calc |gfun x - Real.log (∫ x', RefMarg.cavTheta V lam n (fun e : Empty => e.elim) x'
          ∂(HRS.Whole.withDensityReal ρ))| ≤
        |gfun x| + |Real.log (∫ x', RefMarg.cavTheta V lam n (fun e : Empty => e.elim) x'
          ∂(HRS.Whole.withDensityReal ρ))| := abs_sub _ _
      _ ≤ 2 * Es := by linarith [hgb x]
  have hε2 : Real.exp (2 * Es) - 1 = ε := by
    rw [hEs, show 2 * (Real.log (1 + ε) / 2) = Real.log (1 + ε) by ring, Real.exp_log (by linarith)]
    ring
  filter_upwards [hrn] with y h1
  rw [h1, ENNReal.toReal_ofReal (hθ0 y).le]
  have := RefMarg.abs_sub_one_le_of_abs_log_le (hθ0 y) (hlogθ y)
  rw [hε2] at this
  exact this

end Unif

section Final3

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Ψ : Euc d → H}

/-- **`‖dπ^R_N/dμ - 1‖_∞ → 0`** (TeX `euc-reference-marginal`, third bound; torus
`reference_marginal_density_uniform`), uniformly in the probability densities `ρ ≤ M` and `β ∈ (0, βp]`. -/
theorem wr13e_reference_marginal_density_uniform (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d)
    {τ : ℝ} (hτ : 0 < τ) (βp M : ℝ) (hβp : 0 < βp) (hκ : KappaSmall βp (wr13e_a d s τ M))
    (hΨ : FeatHyp Ψ (kTau d s τ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N₀ ≤ N →
      HRS.Whole.firstMarginal
          (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)
        ≪ HRS.Whole.withDensityReal ρ ∧
        ∀ᵐ y ∂(HRS.Whole.withDensityReal ρ),
          |((HRS.Whole.firstMarginal
            (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)).rnDeriv
            (HRS.Whole.withDensityReal ρ) y).toReal - 1| ≤ ε := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC0, hTV⟩ := euc_tv_R0_le hd1 hs hsd M
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hy : 0 < 1 - s / d := by rw [sub_pos, div_lt_one hd0]; exact hsd
  have hlim : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (s / d - 1)) Filter.atTop (nhds 0) := by
    have := (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop
    refine this.congr fun N => ?_
    simp only [Function.comp]
    congr 1; ring
  have hε₀ : Filter.Tendsto (fun N : ℕ => Real.sqrt (βp * (C * (N : ℝ) ^ (s / d - 1)) / 2)) Filter.atTop
      (nhds 0) := by
    have h2 : Filter.Tendsto (fun N : ℕ => βp * (C * (N : ℝ) ^ (s / d - 1)) / 2) Filter.atTop (nhds 0) := by
      simpa using ((hlim.const_mul C).const_mul βp).div_const 2
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at this
    exact this
  refine wr13e_core_unif hd hs hsd hτ βp M hβp hκ hΨ
    (wr13e_field_small_eps hd1 hs hsd hτ βp M hΨ) hε₀ (N₃ := 1) ?_
  intro ρ hρ hM β hβ hβp' n hN3 hn
  refine (hTV τ hτ ρ hρ hM β hβ.le (n + 1) hN3).trans (Real.sqrt_le_sqrt ?_)
  have h0 : 0 ≤ C * (((n + 1 : ℕ) : ℝ)) ^ (s / d - 1) :=
    mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have : β * (C * (((n + 1 : ℕ) : ℝ)) ^ (s / d - 1)) ≤ βp * (C * (((n + 1 : ℕ) : ℝ)) ^ (s / d - 1)) :=
    mul_le_mul_of_nonneg_right hβp' h0
  linarith

end Final3

end HRS.MS.Wr
