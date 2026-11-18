import HRS.MS.WhoAux7
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# S54 part 8: differentiation under the time integral
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff Matrix

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem who_clm_decomp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : Euc d →L[ℝ] E) :
    T = ∑ l : Fin d, (EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).smulRight (T (EuclideanSpace.single l 1)) := by
  ext v
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp [map_sum, map_smul]

/-- difference quotients converge to the derivative -/
theorem who_slope_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {P : Euc d → E} {x : Euc d}
    (hP : DifferentiableAt ℝ P x) (l : Fin d) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) • (P (x + (1 / ((n : ℝ) + 1)) • EuclideanSpace.single l (1 : ℝ)) - P x))
      atTop (𝓝 (fderiv ℝ P x (EuclideanSpace.single l 1))) := by
  have hg : HasDerivAt (fun t : ℝ => P (x + t • EuclideanSpace.single l (1 : ℝ)))
      (fderiv ℝ P x (EuclideanSpace.single l 1)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • (EuclideanSpace.single l (1 : ℝ) : Euc d))
        (EuclideanSpace.single l (1 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single l (1 : ℝ) : Euc d)).const_add x
    have h2 : HasFDerivAt P (fderiv ℝ P x) (x + (0 : ℝ) • (EuclideanSpace.single l (1 : ℝ) : Euc d)) := by
      simpa using hP.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have := (hasDerivAt_iff_tendsto_slope_zero.1 hg)
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, one_div, inv_eq_zero]
    positivity
  refine (this.comp ht).congr fun n => ?_
  simp only [Function.comp, zero_add, one_div, inv_inv, zero_smul, add_zero]

/-- measurability of the iterated derivatives of a measurable family -/
theorem who_sm_iter {Ω : Type*} [MeasurableSpace Ω] {G : Ω → Euc d → ℝ} {k : ℕ}
    (hG : ∀ a0, ContDiff ℝ k (G a0)) (hm : ∀ x, StronglyMeasurable fun a0 => G a0 x) :
    ∀ i ≤ k, ∀ x, StronglyMeasurable fun a0 => iteratedFDeriv ℝ i (G a0) x := by
  intro i
  induction i with
  | zero =>
    intro _ x
    have : (fun a0 => iteratedFDeriv ℝ 0 (G a0) x) =
        fun a0 => (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm (G a0 x) := by
      funext a0; rw [iteratedFDeriv_zero_eq_comp]; rfl
    rw [this]
    exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.continuous.comp_stronglyMeasurable (hm x)
  | succ i ih =>
    intro hi x
    have hik : i ≤ k := by omega
    have hdiff : ∀ a0, DifferentiableAt ℝ (iteratedFDeriv ℝ i (G a0)) x := fun a0 =>
      ((hG a0).differentiable_iteratedFDeriv (by exact_mod_cast (by omega : i < k))) x
    have hfd : StronglyMeasurable fun a0 => fderiv ℝ (iteratedFDeriv ℝ i (G a0)) x := by
      set E := ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ
      have hcomp : ∀ l : Fin d, StronglyMeasurable fun a0 =>
          fderiv ℝ (iteratedFDeriv ℝ i (G a0)) x (EuclideanSpace.single l 1) := fun l => by
        refine stronglyMeasurable_of_tendsto atTop (f := fun (n : ℕ) (a0 : Ω) =>
          ((n : ℝ) + 1) • (iteratedFDeriv ℝ i (G a0) (x + (1 / ((n : ℝ) + 1)) • EuclideanSpace.single l (1 : ℝ)) -
            iteratedFDeriv ℝ i (G a0) x)) (fun n => ((ih hik _).sub (ih hik x)).const_smul' _) ?_
        exact tendsto_pi_nhds.2 fun a0 => who_slope_tendsto (hdiff a0) l
      have hfun : (fun a0 => fderiv ℝ (iteratedFDeriv ℝ i (G a0)) x) = fun a0 =>
          ∑ l : Fin d, ((ContinuousLinearMap.smulRightL ℝ (Euc d) E) (EuclideanSpace.proj l : Euc d →L[ℝ] ℝ))
            (fderiv ℝ (iteratedFDeriv ℝ i (G a0)) x (EuclideanSpace.single l 1)) := by
        funext a0
        conv_lhs => rw [who_clm_decomp (fderiv ℝ (iteratedFDeriv ℝ i (G a0)) x)]
        rfl
      rw [hfun]
      exact Finset.stronglyMeasurable_fun_sum _ fun l _ =>
        ((ContinuousLinearMap.smulRightL ℝ (Euc d) E) (EuclideanSpace.proj l : Euc d →L[ℝ] ℝ)).continuous.comp_stronglyMeasurable (hcomp l)
    have : (fun a0 => iteratedFDeriv ℝ (i + 1) (G a0) x) = fun a0 =>
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) ℝ).symm
          (fderiv ℝ (iteratedFDeriv ℝ i (G a0)) x) := by
      funext a0; rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    rw [this]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) ℝ).symm.continuous.comp_stronglyMeasurable hfd


/-- clamping to `[0,τ]` -/
def clampT (τ σ : ℝ) : ℝ := max 0 (min σ τ)

theorem who_clamp_mem {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) : clampT τ σ ∈ Set.Icc (0 : ℝ) τ :=
  ⟨le_max_left _ _, max_le hτ (min_le_right _ _)⟩

theorem who_clamp_eq {τ σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) τ) : clampT τ σ = σ := by
  unfold clampT; rw [min_eq_left hσ.2, max_eq_right hσ.1]

theorem who_clamp_cont (τ : ℝ) : Continuous (clampT τ) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- differentiation under the time integral -/
theorem who_int_time {τ : ℝ} (hτ : 0 < τ) {G : ℝ → Euc d → ℝ} {k : ℕ} {K : ℝ}
    (hG : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ContDiff ℝ k (G σ))
    (hb : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i (G σ) x‖ ≤ K)
    (hc : ∀ x, ContinuousOn (fun σ => G σ x) (Set.Icc 0 τ)) :
    ContDiff ℝ k (fun x => ∫ σ in Set.Ioc 0 τ, G σ x) ∧ ∀ i ≤ k, ∀ x,
      iteratedFDeriv ℝ i (fun x => ∫ σ in Set.Ioc 0 τ, G σ x) x =
        ∫ σ in Set.Ioc 0 τ, iteratedFDeriv ℝ i (G σ) x := by
  set Gt : ℝ → Euc d → ℝ := fun σ => G (clampT τ σ) with hGt
  have hGt1 : ∀ σ, ContDiff ℝ k (Gt σ) := fun σ => hG _ (who_clamp_mem hτ.le σ)
  have hGt2 : ∀ x, Continuous fun σ => Gt σ x := fun x =>
    (hc x).comp_continuous (who_clamp_cont τ) (who_clamp_mem hτ.le)
  have hsm := who_sm_iter hGt1 (fun x => (hGt2 x).stronglyMeasurable)
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) τ)) := ⟨by simp⟩
  obtain ⟨hcd, hit⟩ := HRS.MS.Lc.lc4_iteratedFDeriv_integral (μ := volume.restrict (Set.Ioc (0 : ℝ) τ)) Gt k hGt1
    (Φ := fun _ => K) (integrable_const _) (fun i hi σ x => hb _ (who_clamp_mem hτ.le σ) i hi x)
    (fun i hi x => (hsm i hi x).aestronglyMeasurable)
  have hint : ∀ x, ∫ σ in Set.Ioc 0 τ, Gt σ x = ∫ σ in Set.Ioc 0 τ, G σ x := fun x =>
    setIntegral_congr_fun measurableSet_Ioc fun σ hσ => by
      simp only [hGt, who_clamp_eq (Set.Ioc_subset_Icc_self hσ)]
  have hfun : (fun x => ∫ σ in Set.Ioc 0 τ, Gt σ x) = fun x => ∫ σ in Set.Ioc 0 τ, G σ x := funext hint
  rw [hfun] at hcd hit
  refine ⟨hcd, fun i hi x => ?_⟩
  rw [hit i hi x]
  exact setIntegral_congr_fun measurableSet_Ioc fun σ hσ => by
    simp only [hGt, who_clamp_eq (Set.Ioc_subset_Icc_self hσ)]

/-- joint measurability of the iterated derivatives -/
theorem who_joint_sm {τ : ℝ} (hτ : 0 < τ) {G : ℝ → Euc d → ℝ} {k : ℕ}
    (hG : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ContDiff ℝ k (G σ))
    (hc : ∀ x, ContinuousOn (fun σ => G σ x) (Set.Icc 0 τ)) {i : ℕ} (hi : i ≤ k) :
    Measurable (Function.uncurry fun (x : Euc d) (σ : ℝ) => ‖iteratedFDeriv ℝ i (G (clampT τ σ)) x‖) := by
  have hGt1 : ∀ σ, ContDiff ℝ k (G (clampT τ σ)) := fun σ => hG _ (who_clamp_mem hτ.le σ)
  have hGt2 : ∀ x, Continuous fun σ => G (clampT τ σ) x := fun x =>
    (hc x).comp_continuous (who_clamp_cont τ) (who_clamp_mem hτ.le)
  have hsm := who_sm_iter hGt1 (fun x => (hGt2 x).stronglyMeasurable)
  have := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (u := fun (x : Euc d) (σ : ℝ) => iteratedFDeriv ℝ i (G (clampT τ σ)) x)
    (fun σ => ((hGt1 σ).continuous_iteratedFDeriv (by exact_mod_cast hi)))
    (fun x => hsm i hi x)
  exact this.norm.measurable


/-- the sup bound of the derivatives of `ouSg` -/
theorem who_ouSg_sup (Q : Matrix (Fin d) (Fin d) ℝ) (ν η : ℝ) {j : ℕ} {H : Euc d → ℝ} (hH : ContDiff ℝ j H)
    {B : ℝ} (hB : ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i H y‖ ≤ B) {i : ℕ} (hi : i ≤ j) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (ouSg Q ν η H) x‖ ≤ ‖ouExp Q η‖ ^ i * B := by
  have hfun : ouSg Q ν η H = fun x => ∫ w, (fun _ : Euc d => (1 : ℝ)) w * H (ouExp Q η x + sOU Q ν η w)
      ∂(stdGaussian (Euc d)) := by
    funext x; rw [who_ouSg_eq Q ν η hH.continuous x]; simp
  rw [hfun, (who_gav_smooth (ouExp Q η) (sOU Q ν η) hH hB continuous_const (integrable_const _)).2 i hi x]
  refine (norm_integral_le_of_norm_le_const (C := ‖ouExp Q η‖ ^ i * B) (Filter.Eventually.of_forall fun w => ?_)).trans ?_
  · simp only [one_smul]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h3 : ∏ _l : Fin i, ‖ouExp Q η‖ = ‖ouExp Q η‖ ^ i := by simp
    rw [h3, mul_comm]
    exact mul_le_mul_of_nonneg_left (hB i hi _) (by positivity)
  · simp


theorem who_sing_int {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) = ENNReal.ofReal (2 * τ ^ (1 / 2 : ℝ)) := by
  have hii : IntervalIntegrable (fun σ : ℝ => (τ - σ) ^ (-(1 / 2 : ℝ))) volume 0 τ := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (by norm_num) (a := 0) (b := τ)).comp_sub_left τ
    simpa using this.symm
  have hval : ∫ σ in (0 : ℝ)..τ, (τ - σ) ^ (-(1 / 2 : ℝ)) = 2 * τ ^ (1 / 2 : ℝ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) τ]
    rw [sub_self, sub_zero, integral_rpow (Or.inl (by norm_num))]
    norm_num
    ring
  have hnn : ∀ᵐ σ ∂(volume.restrict (Set.Ioc (0 : ℝ) τ)), 0 ≤ (τ - σ) ^ (-(1 / 2 : ℝ)) :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun σ hσ =>
      Real.rpow_nonneg (sub_nonneg.2 hσ.2) _)
  rw [← hval, intervalIntegral.integral_of_le hτ.le,
    ofReal_integral_eq_lintegral_ofReal ((intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).1 hii) hnn]
  exact setLIntegral_congr Ioo_ae_eq_Ioc


theorem who_cs_sing {τ : ℝ} (hτ : 0 < τ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ σ in Set.Ioo 0 τ, g σ) ^ 2 ≤ ENNReal.ofReal (2 * τ ^ (1 / 2 : ℝ)) *
      ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g σ ^ 2 := by
  have hpt : ∀ σ ∈ Set.Ioo (0 : ℝ) τ, ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) *
      (ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g σ) = g σ := by
    intro σ hσ
    have hu : 0 < τ - σ := sub_pos.2 hσ.2
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _), ← Real.rpow_add hu]
    norm_num
  have hma : Measurable fun σ : ℝ => ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_id).pow_const _)
  have hmb : Measurable fun σ : ℝ => ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g σ :=
    (ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_id).pow_const _)).mul hg
  have h := who_cs_density (μ := volume.restrict (Set.Ioo (0 : ℝ) τ)) hma hmb
  rw [setLIntegral_congr_fun measurableSet_Ioo (fun σ hσ => hpt σ hσ)] at h
  rw [who_sing_int hτ] at h
  refine h.trans (mul_le_mul' le_rfl (le_of_eq ?_))
  refine setLIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
  have hu : 0 < τ - σ := sub_pos.2 hσ.2
  show ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) * (ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g σ) ^ 2 =
    ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g σ ^ 2
  rw [mul_pow, ← mul_assoc, ← ENNReal.ofReal_pow (Real.rpow_nonneg hu.le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _)]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le, ← Real.rpow_add hu]
  norm_num


theorem who_ouSg_smooth (Q : Matrix (Fin d) (Fin d) ℝ) (ν η : ℝ) {j : ℕ} {H : Euc d → ℝ} (hH : ContDiff ℝ j H)
    {B : ℝ} (hB : ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i H y‖ ≤ B) : ContDiff ℝ j (ouSg Q ν η H) := by
  have hfun : ouSg Q ν η H = fun x => ∫ w, (fun _ : Euc d => (1 : ℝ)) w * H (ouExp Q η x + sOU Q ν η w)
      ∂(stdGaussian (Euc d)) := by
    funext x; rw [who_ouSg_eq Q ν η hH.continuous x]; simp
  rw [hfun]
  exact (who_gav_smooth (ouExp Q η) (sOU Q ν η) hH hB continuous_const (integrable_const _)).1

theorem who_sing_pt {Cw T η : ℝ} (hCw : 0 ≤ Cw) (hη : η ∈ Set.Ioc (0 : ℝ) T) :
    ENNReal.ofReal (η ^ (1 / 2 : ℝ)) * ENNReal.ofReal (Cw * (1 + η⁻¹)) ≤
      ENNReal.ofReal (Cw * (T + 1)) * ENNReal.ofReal (η ^ (-(1 / 2 : ℝ))) := by
  have hη0 : η ≠ 0 := hη.1.ne'
  have hi : 0 ≤ η⁻¹ := inv_nonneg.2 hη.1.le
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hη.1.le _), ← ENNReal.ofReal_mul (mul_nonneg hCw (by linarith [hη.1, hη.2]))]
  apply ENNReal.ofReal_le_ofReal
  have h1 : η ^ (1 / 2 : ℝ) = η ^ (-(1 / 2 : ℝ)) * η := by
    rw [← Real.rpow_add_one hη.1.ne']; norm_num
  have h2 : η ^ (-(1 / 2 : ℝ)) ≥ 0 := Real.rpow_nonneg hη.1.le _
  calc η ^ (1 / 2 : ℝ) * (Cw * (1 + η⁻¹)) = Cw * η ^ (-(1 / 2 : ℝ)) * (η + 1) := by
        rw [h1]; field_simp
    _ ≤ Cw * η ^ (-(1 / 2 : ℝ)) * (T + 1) := by
        gcongr; linarith [hη.2]
    _ = _ := by ring


set_option maxHeartbeats 0 in
/-- **the weighted bound of the Duhamel integral** -/
theorem who_Vw (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ψ : SchwartzMap (Euc d) ℝ) {c : Euc d → Euc d} (hc : IsSmoothBounded c) {P : ℝ}
    (hP : (d : ℝ) / 2 < P) (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {τ : ℝ}, 0 < τ → τ ≤ T → ∀ {w : ℝ → Euc d → ℝ} {B : ℝ},
      (∀ σ ∈ Set.Icc (0 : ℝ) τ, ContDiff ℝ ((r + 3 : ℕ) : WithTop ℕ∞) (w σ) ∧
        ∀ l ≤ r + 3, ∀ y, ‖iteratedFDeriv ℝ l (w σ) y‖ ≤ B) →
      (∀ x, ContinuousOn (fun σ => ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ)) x) (Set.Icc 0 τ)) →
      ContDiff ℝ r (fun x => ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ)) x) ∧
      ∀ i ≤ r, wSq P (fun x => ‖iteratedFDeriv ℝ i
          (fun x => ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ)) x) x‖) ≤
        ENNReal.ofReal C * ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) * Nsq r P (w σ) := by
  have hP0 : 0 ≤ P := by linarith [show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity]
  have hsd : s < (d : ℝ) := by linarith
  obtain ⟨Cp, hCp0, hpert⟩ := who_pert_sup hs0 hsd M ψ hc r
  obtain ⟨Cw, hCw0, hWp⟩ := who_Wpert hd hs0 hs1 M ψ hc hP Q hν T r
  obtain ⟨K0, a0, lam0, hK01, -, -, hU⟩ := who_ou_unif Q hν T
  refine ⟨2 * (max T 0) ^ (1 / 2 : ℝ) * (Cw * (max T 0 + 1)), by positivity, ?_⟩
  intro τ hτ hτT w B hw hcont
  have hT0 : 0 < T := hτ.trans_le hτT
  have hmax : max T 0 = T := max_eq_left hT0.le
  rw [hmax]
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → Euc d → ℝ, ∀ σ x, G σ x = ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ)) x :=
    ⟨_, fun _ _ => rfl⟩
  have hGfun : ∀ σ, G σ = ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ)) := fun σ => funext (hGdef σ)
  have hcont' : ∀ x, ContinuousOn (fun σ => G σ x) (Set.Icc 0 τ) := fun x => by
    simp_rw [hGdef]; exact hcont x
  have hpσ : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ContDiff ℝ r (ulPert s M ψ c (w σ)) ∧
      ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (ulPert s M ψ c (w σ)) y‖ ≤ Cp * B := fun σ hσ =>
    hpert (hw σ hσ).1 (hw σ hσ).2
  have hη : ∀ σ ∈ Set.Icc (0 : ℝ) τ, τ - σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨sub_nonneg.2 hσ.2, by linarith [hσ.1]⟩
  have hGc : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ContDiff ℝ r (G σ) := fun σ hσ => by
    rw [hGfun σ]
    exact who_ouSg_smooth Q ν (τ - σ) (hpσ σ hσ).1 (B := Cp * B) (fun i hi y => (hpσ σ hσ).2 i hi y)
  have hGb : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ i ≤ r, ∀ x, ‖iteratedFDeriv ℝ i (G σ) x‖ ≤ K0 ^ r * (Cp * B) := by
    intro σ hσ i hi x
    rw [hGfun σ]
    refine (who_ouSg_sup Q ν (τ - σ) (hpσ σ hσ).1 (B := Cp * B) (fun i hi y => (hpσ σ hσ).2 i hi y) hi x).trans ?_
    have hE := (hU (τ - σ) (hη σ hσ)).1
    have hB0 : 0 ≤ Cp * B := by
      have := (hpσ σ hσ).2 0 (Nat.zero_le _) 0
      exact (norm_nonneg _).trans this
    calc ‖ouExp Q (τ - σ)‖ ^ i * (Cp * B) ≤ K0 ^ i * (Cp * B) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hE i) hB0
      _ ≤ K0 ^ r * (Cp * B) := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK01 hi) hB0
  obtain ⟨hVc, hVd⟩ := who_int_time hτ hGc hGb hcont'
  have hV : (fun x => ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ)) x) =
      fun x => ∫ σ in Set.Ioc 0 τ, G σ x := by
    funext x; rw [intervalIntegral.integral_of_le hτ.le]; simp_rw [hGdef]
  rw [hV]
  refine ⟨hVc, fun i hi => ?_⟩
  have hJ := who_joint_sm hτ hGc hcont' hi
  obtain ⟨g, hgdef⟩ : ∃ g : Euc d → ℝ → ℝ≥0∞, ∀ x σ,
      g x σ = ENNReal.ofReal ‖iteratedFDeriv ℝ i (G (clampT τ σ)) x‖ := ⟨_, fun _ _ => rfl⟩
  have hgm : ∀ x, Measurable (g x) := fun x => by
    have : g x = fun σ => ENNReal.ofReal ‖iteratedFDeriv ℝ i (G (clampT τ σ)) x‖ := funext (hgdef x)
    rw [this]
    have h1 : Measurable fun σ : ℝ => ‖iteratedFDeriv ℝ i (G (clampT τ σ)) x‖ := by
      have h2 : Measurable fun σ : ℝ => ((x, σ) : Euc d × ℝ) := measurable_const.prodMk measurable_id
      exact hJ.comp h2
    exact ENNReal.measurable_ofReal.comp h1
  have hgm2 : Measurable (Function.uncurry g) := by
    have : Function.uncurry g = fun p : Euc d × ℝ => ENNReal.ofReal ‖iteratedFDeriv ℝ i (G (clampT τ p.2)) p.1‖ := by
      funext p; exact hgdef p.1 p.2
    rw [this]
    exact ENNReal.measurable_ofReal.comp hJ
  have hgG : ∀ x, ∀ σ ∈ Set.Ioo (0 : ℝ) τ, g x σ = ENNReal.ofReal ‖iteratedFDeriv ℝ i (G σ) x‖ := by
    intro x σ hσ
    rw [hgdef, who_clamp_eq (Set.Ioo_subset_Icc_self hσ)]
  have hpoint : ∀ x, ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun x => ∫ σ in Set.Ioc 0 τ, G σ x) x‖ ^ 2 ≤
      ENNReal.ofReal (2 * τ ^ (1 / 2 : ℝ)) *
        ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g x σ ^ 2 := by
    intro x
    rw [hVd i hi x]
    have h1 := who_ofReal_norm_integral_le (volume.restrict (Set.Ioc (0 : ℝ) τ))
      (fun σ => iteratedFDeriv ℝ i (G σ) x)
    have h2 : ∫⁻ σ in Set.Ioc 0 τ, ENNReal.ofReal ‖iteratedFDeriv ℝ i (G σ) x‖ =
        ∫⁻ σ in Set.Ioo 0 τ, g x σ := by
      rw [setLIntegral_congr Ioo_ae_eq_Ioc.symm]
      exact setLIntegral_congr_fun measurableSet_Ioo fun σ hσ => (hgG x σ hσ).symm
    exact (pow_le_pow_left' (h1.trans h2.le) 2).trans (who_cs_sing hτ (hgm x))
  have hwm : Measurable fun x : Euc d => ENNReal.ofReal (wt P x) := ENNReal.measurable_ofReal.comp (who_wt_meas P)
  have hFm : Measurable (Function.uncurry fun (x : Euc d) (σ : ℝ) =>
      ENNReal.ofReal (wt P x) * (ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g x σ ^ 2)) := by
    refine (hwm.comp measurable_fst).mul ?_
    exact ((ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_snd).pow_const _))).mul
      (hgm2.pow_const 2)
  rw [who_wSq_eq_sq P _ (fun _ => norm_nonneg _)]
  calc ∫⁻ x, ENNReal.ofReal (wt P x) * ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun x => ∫ σ in Set.Ioc 0 τ, G σ x) x‖ ^ 2
      ≤ ∫⁻ x, ENNReal.ofReal (wt P x) * (ENNReal.ofReal (2 * τ ^ (1 / 2 : ℝ)) *
          ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g x σ ^ 2) :=
        lintegral_mono fun x => mul_le_mul' le_rfl (hpoint x)
    _ = ENNReal.ofReal (2 * τ ^ (1 / 2 : ℝ)) * ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) *
          wSq P (fun x => ‖iteratedFDeriv ℝ i (G σ) x‖) := by
        have h1 : ∀ x : Euc d, ENNReal.ofReal (wt P x) * (ENNReal.ofReal (2 * τ ^ (1 / 2 : ℝ)) *
            ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g x σ ^ 2) =
            ENNReal.ofReal (2 * τ ^ (1 / 2 : ℝ)) * ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal (wt P x) *
              (ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g x σ ^ 2) := fun x => by
          rw [mul_left_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [h1]
        have hm2 : Measurable fun x : Euc d => ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal (wt P x) *
            (ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g x σ ^ 2) := hFm.lintegral_prod_right'
        rw [lintegral_const_mul _ hm2, lintegral_lintegral_swap hFm.aemeasurable]
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
        have : ∀ x : Euc d, ENNReal.ofReal (wt P x) * (ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * g x σ ^ 2) =
            ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * (ENNReal.ofReal (wt P x) *
              ENNReal.ofReal ‖iteratedFDeriv ℝ i (G σ) x‖ ^ 2) := fun x => by
          rw [hgG x σ hσ]; ring
        simp_rw [this]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, who_wSq_eq_sq P _ (fun _ => norm_nonneg _)]
    _ ≤ ENNReal.ofReal (2 * τ ^ (1 / 2 : ℝ)) * ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal (Cw * (T + 1)) *
          (ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) * Nsq r P (w σ)) := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioo fun σ hσ => ?_)
        have hσ' : σ ∈ Set.Icc (0 : ℝ) τ := Set.Ioo_subset_Icc_self hσ
        have hηI : τ - σ ∈ Set.Ioc (0 : ℝ) T := ⟨sub_pos.2 hσ.2, by linarith [hσ.1]⟩
        have hwσ : CbCls (r + 3) (w σ) := ⟨(hw σ hσ').1, B, fun l hl => (hw σ hσ').2 l hl⟩
        have h1 := hWp (τ - σ) hηI hwσ hi
        rw [hGfun σ]
        calc ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * wSq P (fun x => ‖iteratedFDeriv ℝ i
              (ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ))) x‖)
            ≤ ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * (ENNReal.ofReal (Cw * (1 + (τ - σ)⁻¹)) * Nsq r P (w σ)) :=
              mul_le_mul' le_rfl h1
          _ = (ENNReal.ofReal ((τ - σ) ^ (1 / 2 : ℝ)) * ENNReal.ofReal (Cw * (1 + (τ - σ)⁻¹))) * Nsq r P (w σ) := by
              rw [mul_assoc]
          _ ≤ (ENNReal.ofReal (Cw * (T + 1)) * ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ)))) * Nsq r P (w σ) :=
              mul_le_mul' (who_sing_pt hCw0 hηI) le_rfl
          _ = _ := by rw [mul_assoc]
    _ = ENNReal.ofReal (2 * τ ^ (1 / 2 : ℝ)) * (ENNReal.ofReal (Cw * (T + 1)) *
          ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) * Nsq r P (w σ)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 * T ^ (1 / 2 : ℝ) * (Cw * (T + 1))) *
          ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) * Nsq r P (w σ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have : τ ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hτ.le hτT (by norm_num)
        have hC : 0 ≤ Cw * (T + 1) := mul_nonneg hCw0 (by linarith)
        nlinarith [mul_nonneg hC (Real.rpow_nonneg hτ.le (1 / 2 : ℝ))]

end HRS.MS.Who
