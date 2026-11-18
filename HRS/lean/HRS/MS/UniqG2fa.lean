import HRS.MS.UniqG2a
import HRS.MS.UniqM2Moll

/-!
# G2fa of `UniqPlan.md`: time regularity of the dissipation `D_c(σ) = ∫ ς_c^σ |∇ z_ε(σ)|²`

* `g2fa_time_cont`: for each `x`, `j`, the map `σ ↦ ∂_j z_ε(σ,x)` is continuous on `[0,t]`
  (it is the pairing of `z σ` with the `C_c^∞` function `y ↦ ∂_jη_ε(x-y)`, hence an indefinite integral).
* `g2fa_dissipation`: `D_c` is a.e.-strongly measurable on `[0,t]` and bounded by a constant independent of `c`.
* `g2fa_dissipation_integrable`: `D_c` is interval integrable on `[0,t]`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Interval ContDiff

namespace HRS.MS.UniqG2fa

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqT3 HRS.MS.UniqE1 HRS.MS.UniqC3

variable {d : ℕ}

/-- The test function `ψ_{x,j}(y) = (∂_jη_ε)(x - y)`. -/
def psiJ (ε : ℝ) (x : Euc d) (j : Fin d) : Euc d → ℝ :=
  fun y => fderiv ℝ (eta d ε) (x - y) (EuclideanSpace.single j 1)

theorem psiJ_contDiff (ε : ℝ) (x : Euc d) (j : Fin d) : ContDiff ℝ ∞ (psiJ ε x j) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ (eta d ε)) := (eta_contDiff (d := d) (ε := ε)).fderiv_right (by simp)
  exact (h1.comp (contDiff_const.sub contDiff_id)).clm_apply contDiff_const

theorem psiJ_compact {ε : ℝ} (hε : 0 < ε) (x : Euc d) (j : Fin d) :
    HasCompactSupport (psiJ ε x j) := by
  have h := ((eta_hasCompactSupport (d := d) hε).fderiv ℝ).comp_homeomorph (Homeomorph.subLeft x)
  exact h.comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) (by simp)

/-- `∂_j (η_ε * u)(x) = ∫ u(y) (∂_jη_ε)(x - y) dy`. -/
theorem g2fa_fderiv_eq {ε : ℝ} (hε : 0 < ε) {u : Euc d → ℝ} (hu : LocallyIntegrable u volume)
    (x : Euc d) (j : Fin d) :
    fderiv ℝ (moll d ε u) x (EuclideanSpace.single j 1) = ∫ y, u y * psiJ ε x j y := by
  set e : Euc d := EuclideanSpace.single j 1 with he
  have hηc := eta_hasCompactSupport (d := d) hε
  have hη1 : ContDiff ℝ 1 (eta d ε) := (eta_contDiff (d := d) (ε := ε)).of_le (by simp)
  rw [moll_eq_cv, fderiv_cv hu hηc hη1, cv_apply]
  have hco : Continuous (fun y => fderiv ℝ (eta d ε) (x - y)) :=
    ((eta_contDiff (d := d) (ε := ε)).continuous_fderiv (by simp)).comp
      (continuous_const.sub continuous_id)
  have hcs : HasCompactSupport (fun y => fderiv ℝ (eta d ε) (x - y)) :=
    (hηc.fderiv ℝ).comp_homeomorph (Homeomorph.subLeft x)
  have hint : Integrable (fun y => u y • fderiv ℝ (eta d ε) (x - y)) volume :=
    hu.integrable_smul_right_of_hasCompactSupport hco hcs
  rw [ContinuousLinearMap.integral_apply hint e]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [psiJ, he]

/-- `σ ↦ ∂_j z_ε(σ,x)` is continuous on `[0,t]`. -/
theorem g2fa_time_cont {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {t : ℝ} (ht0 : 0 ≤ t)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {ε : ℝ} (hε : 0 < ε)
    (hzL : ∀ τ ∈ Icc (0 : ℝ) t, LocallyIntegrable (z τ) volume) (x : Euc d) (j : Fin d) :
    ContinuousOn (fun σ => fderiv ℝ (moll d ε (z σ)) x (EuclideanSpace.single j 1)) (Icc 0 t) := by
  set ψ := psiJ ε x j with hψ
  have hrep : ∀ τ ∈ Icc (0 : ℝ) t,
      ∫ y, z τ y * ψ y = ∫ σ in Icc (0 : ℝ) τ, forwardPairing D ρ t σ (z σ) ψ := by
    intro τ hτ
    have h := hz.eq ψ (psiJ_contDiff ε x j) (psiJ_compact hε x j) τ hτ
    have h0 : (∫ y, z 0 y * ψ y) = 0 := by
      have : (fun y => z 0 y * ψ y) =ᵐ[volume] fun _ => 0 := by
        filter_upwards [hz.init] with y hy
        simp [hy]
      rw [integral_congr_ae this]; simp
    rw [h0, zero_add] at h
    exact h
  have hint := hz.integrable ψ (psiJ_contDiff ε x j) (psiJ_compact hε x j)
  have hcont : ContinuousOn
      (fun τ => ∫ σ in (0 : ℝ)..τ, forwardPairing D ρ t σ (z σ) ψ) (Icc 0 t) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := t)
      (f := fun σ => forwardPairing D ρ t σ (z σ) ψ) (by rwa [uIcc_of_le ht0])
    rwa [uIcc_of_le ht0] at this
  refine hcont.congr fun τ hτ => ?_
  simp only
  rw [g2fa_fderiv_eq hε (hzL τ hτ) x j, hrep τ hτ, intervalIntegral.integral_of_le hτ.1,
    integral_Icc_eq_integral_Ioc]

/-- The operator norm of a functional on `ℝ^d` is the `ℓ²` norm of its coordinates. -/
theorem g2fa_norm_sq_eq (L : Euc d →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ j, (L (EuclideanSpace.single j 1)) ^ 2 := by
  set g := (InnerProductSpace.toDual ℝ (Euc d)).symm L with hg
  have h1 : ‖L‖ = ‖g‖ := ((InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map L).symm
  have h2 : ∀ j, g j = L (EuclideanSpace.single j 1) := fun j => by
    have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := (EuclideanSpace.single j 1 : Euc d))
      (y := L)
    rw [← this, EuclideanSpace.inner_single_right]
    simp [hg]
  rw [h1, EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs, h2]

/-- Time clamping into `[0,t]`. -/
def cl (t σ : ℝ) : ℝ := max 0 (min σ t)

theorem cl_cont (t : ℝ) : Continuous (cl t) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem cl_mem {t : ℝ} (ht0 : 0 ≤ t) (σ : ℝ) : cl t σ ∈ Icc (0 : ℝ) t :=
  ⟨le_max_left _ _, max_le ht0 (min_le_right _ _)⟩

theorem cl_eq {t : ℝ} {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) t) : cl t σ = σ := by
  simp only [cl]
  rw [min_eq_left hσ.2, max_eq_right hσ.1]

/-- Measurability of the gradient components of the clamped mollification. -/
theorem g2fa_meas_comp {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {t : ℝ} (ht0 : 0 ≤ t)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {ε : ℝ} (hε : 0 < ε)
    (hzL : ∀ τ ∈ Icc (0 : ℝ) t, LocallyIntegrable (z τ) volume) (j : Fin d) :
    Measurable (Function.uncurry fun (σ : ℝ) (x : Euc d) =>
      fderiv ℝ (moll d ε (z (cl t σ))) x (EuclideanSpace.single j 1)) := by
  refine measurable_uncurry_of_continuous_of_measurable
    (fun x => (g2fa_time_cont ht0 hz hε hzL x j).comp_continuous (cl_cont t) (cl_mem ht0))
    (fun σ => ?_)
  exact (((moll_contDiff hε (hzL _ (cl_mem ht0 σ))).continuous_fderiv (by simp)).clm_apply
    continuous_const).measurable


/-- **G2fa.** The dissipation `D_c(σ) = ∫ ς_c^σ |∇ z_ε(σ)|²` is measurable on `[0,t]` and bounded by a
constant independent of `c` and `σ`. -/
theorem g2fa_dissipation {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {t : ℝ} (ht0 : 0 ≤ t) {m : ℕ}
    {Cb K : ℝ} {χ χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hχ : IsUlocCutoff χ)
    (hF : FlowBundle d m Cb t χ χh (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ K)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {B : ℝ}
    (hzu : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 1 χ (z τ) ≤ ENNReal.ofReal B) {ε : ℝ} (hε : 0 < ε) :
    (∀ c : Euc d, AEStronglyMeasurable
        (fun σ => ∫ x, varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε (z σ)) x‖ ^ 2)
        (volume.restrict (Icc 0 t))) ∧
    ∃ Bd : ℝ, ∀ c : Euc d, ∀ σ ∈ Icc (0 : ℝ) t,
      ∫ x, varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε (z σ)) x‖ ^ 2 ≤ Bd := by
  have hLM : ∀ τ ∈ Icc (0 : ℝ) t, LocMass (max B 0) (z τ) := fun τ hτ =>
    locMass_of_ulocNormE hχ (le_max_right _ _)
      ((hzu τ hτ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hzL : ∀ τ ∈ Icc (0 : ℝ) t, LocallyIntegrable (z τ) volume := fun τ hτ =>
    (hLM τ hτ).locallyIntegrable
  refine ⟨fun c => ?_, ?_⟩
  · have hςm : Measurable (Function.uncurry fun (σ : ℝ) (x : Euc d) =>
        varsigma χ Ψ (cl t σ) c x) := by
      refine measurable_uncurry_of_continuous_of_measurable (fun x => ?_) (fun σ => ?_)
      · have h1 : ContinuousOn (fun σ : ℝ => varsigma χ Ψ σ c x) (Icc 0 t) :=
          (hF.cont c).comp (f := fun σ : ℝ => (σ, x)) (by fun_prop)
            (fun σ hσ => ⟨hσ, mem_univ _⟩)
        exact h1.comp_continuous (cl_cont t) (cl_mem ht0)
      · exact (hF.contDiff _ (cl_mem ht0 σ) c).continuous.measurable
    have Hmeas : Measurable (fun p : ℝ × Euc d => varsigma χ Ψ (cl t p.1) c p.2 *
        ∑ j, (fderiv ℝ (moll d ε (z (cl t p.1))) p.2 (EuclideanSpace.single j 1)) ^ 2) :=
      hςm.mul (Finset.measurable_sum _ fun j _ =>
        (g2fa_meas_comp ht0 hz hε hzL j).pow_const 2)
    have hSM := Hmeas.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))
    refine hSM.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun σ hσ => ?_)
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [cl_eq hσ, g2fa_norm_sq_eq]
  · obtain ⟨C, hC0, hC⟩ := moll_iteratedFDeriv_le (d := d) hε 1
    set L : ℝ := 2 * Real.exp (Cb * t) with hL
    refine ⟨(C * max B 0) ^ 2 * volume.real (closedBall (0 : Euc d) L), fun c σ hσ => ?_⟩
    have hbd : ∀ x, ‖fderiv ℝ (moll d ε (z σ)) x‖ ≤ C * max B 0 := fun x => by
      have := hC (max B 0) (z σ) (le_max_right _ _) (hLM σ hσ) x
      rwa [norm_iteratedFDeriv_one] at this
    have hi : Integrable ((closedBall (Ψ σ c) L).indicator fun _ => (C * max B 0) ^ 2) volume :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
    calc ∫ x, varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε (z σ)) x‖ ^ 2
        ≤ ∫ x, (closedBall (Ψ σ c) L).indicator (fun _ => (C * max B 0) ^ 2) x := by
          refine integral_mono_of_nonneg
            (Eventually.of_forall fun x => mul_nonneg (hF.range σ hσ c x).1 (sq_nonneg _))
            hi (Eventually.of_forall fun x => ?_)
          by_cases hx : x ∈ closedBall (Ψ σ c) L
          · rw [indicator_of_mem hx]
            have h1 := (hF.range σ hσ c x).2
            have h0 := (hF.range σ hσ c x).1
            have h2 : ‖fderiv ℝ (moll d ε (z σ)) x‖ ^ 2 ≤ (C * max B 0) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hbd x) 2
            calc varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε (z σ)) x‖ ^ 2
                ≤ 1 * (C * max B 0) ^ 2 := mul_le_mul h1 h2 (sq_nonneg _) zero_le_one
              _ = _ := one_mul _
          · rw [indicator_of_notMem hx]
            have : varsigma χ Ψ σ c x = 0 :=
              image_eq_zero_of_notMem_tsupport (fun h => hx (hF.supp σ hσ c h))
            beta_reduce
            rw [this, zero_mul]
      _ = (C * max B 0) ^ 2 * volume.real (closedBall (0 : Euc d) L) := by
          rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul,
            Measure.real, Measure.real, Measure.addHaar_closedBall_center, mul_comm]

/-- **G2fa, corollary.** `D_c` is interval integrable on `[0,t]`. -/
theorem g2fa_dissipation_integrable {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {t : ℝ} (ht0 : 0 ≤ t)
    {m : ℕ} {Cb K : ℝ} {χ χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hχ : IsUlocCutoff χ)
    (hF : FlowBundle d m Cb t χ χh (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ K)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {B : ℝ}
    (hzu : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 1 χ (z τ) ≤ ENNReal.ofReal B) {ε : ℝ} (hε : 0 < ε)
    (c : Euc d) :
    IntervalIntegrable
      (fun σ => ∫ x, varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε (z σ)) x‖ ^ 2)
      volume 0 t := by
  obtain ⟨hm, Bd, hBd⟩ := g2fa_dissipation ht0 hχ hF hz hzu hε
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]
  refine Integrable.of_bound (hm c) Bd ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun σ hσ => ?_)
  have hnn : 0 ≤ ∫ x, varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε (z σ)) x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (hF.range σ hσ c x).1 (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hBd c σ hσ

end HRS.MS.UniqG2fa
