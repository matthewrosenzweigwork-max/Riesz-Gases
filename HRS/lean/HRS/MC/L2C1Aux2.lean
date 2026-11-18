import HRS.MC.L2C1Aux1

/-!
# Packet L2C-1, helper 2: the Lyapunov argument for the frozen semigroup (abstract frozen data)

For frozen data `H : FrozenHyp d s (2 * mStar d + 4) …` and continuous `ψ ∈ H^{mStar+4}`
(in particular every smooth `ψ`), with `S(v) = Q_β U^{0,v}` the centered frozen semigroup:

* `F(v) = ⟨y_v, R y_v⟩_{L²(μ_β)}` (`y_v` the `L²(μ_β)` class of `S(v)ψ`, `R = A⁻¹`) satisfies
  `F' = -2β⁻¹ ∫ρ_β|∇S(v)ψ|²` (`HRS.PDE.MFLinear.frozen_F_props`);
* the weighted Poincaré inequality and the equivalence of `⟨y,Ry⟩` with `‖y‖²` give `F' ≤ -a F`,
  hence the exponential decay (1);
* the integrated gradient bound (2) is `susceptibilityCov_eq_integral` (the improper FTC for `F`)
  together with `susceptibilityCov_bounds`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.L2C1

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

variable {d : ℕ}

/-- Comparison of the `L²(μ)` and `L²(dx)` norms of a continuous function, `c₀ ≤ ρ ≤ Λ₀`. -/
theorem l2c1_l2Inner_bounds {ρ : Torus d → ℝ} (hprob : IsProbDensity ρ) (hρc : Continuous ρ)
    {c₀ Λ₀ : ℝ} (hlow : ∀ x, c₀ ≤ ρ x) (hup : ∀ x, ρ x ≤ Λ₀) {f : Torus d → ℝ}
    (hf : Continuous f) :
    c₀ * ∫ x, f x ^ 2 ≤ l2Inner (withDensityReal ρ) f f ∧
      l2Inner (withDensityReal ρ) f f ≤ Λ₀ * ∫ x, f x ^ 2 := by
  rw [MFAdjoint.l2Inner_mu hprob]
  have hi : ∀ g : Torus d → ℝ, Continuous g → Integrable g := fun g hg =>
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i1 : Integrable (fun x => f x ^ 2) := hi _ (hf.pow 2)
  have i2 : Integrable (fun x => ρ x * (f x * f x)) := hi _ (hρc.mul (hf.mul hf))
  constructor
  · rw [← integral_const_mul]
    refine integral_mono (i1.const_mul c₀) i2 fun x => ?_
    have := hlow x
    nlinarith [sq_nonneg (f x)]
  · rw [← integral_const_mul]
    refine integral_mono i2 (i1.const_mul Λ₀) fun x => ?_
    have := hup x
    nlinarith [sq_nonneg (f x)]

theorem l2c1_norm_sq_pL {ρ : Torus d → ℝ} [IsFiniteMeasure (withDensityReal ρ)]
    {G : ℝ → Torus d → ℝ} {v : ℝ} (hc : Continuous (G v)) :
    ‖pL (withDensityReal ρ) G v‖ ^ 2 = l2Inner (withDensityReal ρ) (G v) (G v) := by
  rw [sq, ← real_inner_self_eq_norm_mul_norm, innerLp_eq_l2Inner]
  exact l2Inner_congr_ae (pL_ae hc) (pL_ae hc)

/-- The Lyapunov argument at the level of frozen data. -/
theorem l2c1_frozen (hd : 2 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ ψ : Torus d → ℝ, Continuous ψ →
      MemSobolev ((mStar d : ℝ) + 4) ψ → ∀ τ : ℝ, 0 ≤ τ →
      l2NormSq (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
        C * Real.exp (-c * τ) * l2NormSq (projMean (withDensityReal ρβ) ψ) ∧
      ∫ v in Set.Icc (0 : ℝ) τ, ∫ x, ‖Torus.grad
          (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ v ψ) x‖ ^ 2 ≤
        C * l2NormSq (projMean (withDensityReal ρβ) ψ) := by
  have h3 := ClassicalPart.three_le_mStar d
  have hd1 : 1 ≤ d := by omega
  have hKS := KS_of_frozen hd1 H
  have hPm := hKS.isProb
  have hρc : Continuous ρβ := H.cont (by omega)
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hc₀ := H.hc₀
  have hΛ0 : 0 < Λ₀ := lt_of_lt_of_le hc₀ ((H.hlow 0).trans (H.le_Lam 0))
  have hβ := H.hβ
  have hνβ : 0 < β⁻¹ := inv_pos.2 hβ
  obtain ⟨R, hRA, hAR, hRs, -⟩ := exists_inverse hd1 s H.hs0 H.hsd hKS hρc β hβ.le
  obtain ⟨κ₁, κ₂, hκ₁, hκ₂, hform⟩ := l2c1_form_bounds hd1 s H.hs0 H.hsd hKS hρc β hβ.le R hAR
  obtain ⟨cP, hcP, hPoin⟩ := exists_weighted_poincare (d := d) c₀ Λ₀ hc₀
  have hPo := hPoin ρβ hprob hρc H.hlow H.le_Lam
  obtain ⟨cS, CS, hcS, hSb⟩ := susceptibilityCov_bounds hd H.hs0 H.hsd ρβ hprob Λ₀ H.le_Lam β hβ.le
  set a : ℝ := 2 * β⁻¹ * cP / κ₂ with ha
  have ha0 : 0 < a := by positivity
  set A1 : ℝ := κ₁ * κ₂ * Λ₀ / c₀ with hA1
  set A2 : ℝ := c₀⁻¹ * (2 * β⁻¹)⁻¹ * (max CS 0 * Λ₀) with hA2
  have hA1n : 0 ≤ A1 := by positivity
  have hA2n : 0 ≤ A2 := by positivity
  refine ⟨A1 + A2 + 1, a, by positivity, ha0, fun ψ hψc hψm τ hτ => ?_⟩
  set Sg' : ℝ → Torus d → ℝ := fun v => Sg H v ψ with hSg'
  have hpath := fun v (hv : 0 ≤ v) => frozen_path_data hd1 H hψc hψm (T' := v + 1) (by linarith)
  have hC2 : ∀ v, 0 ≤ v → Torus.IsCk 2 (Sg H v ψ) := fun v hv =>
    (hpath v hv).1 v ⟨hv, by linarith⟩
  have hC1 : ∀ v, 0 ≤ v → Torus.IsCk 1 (Sg H v ψ) := fun v hv => (hC2 v hv).of_le (by norm_num)
  have hCont : ∀ v, 0 ≤ v → Continuous (Sg H v ψ) := fun v hv =>
    MFAux.continuous_of_isCk (hC1 v hv)
  have hpair0 : ∀ v, 0 ≤ v → pair (withDensityReal ρβ) (Sg H v ψ) = 0 := fun v hv =>
    (hpath v hv).2.1 v ⟨hv, by linarith⟩
  have Pψ := frozen_F_props hd1 H R hRA hRs hψc hψm hψc hψm
  set y : ℝ → Lp ℝ 2 (withDensityReal ρβ) := pL (withDensityReal ρβ) (fun v => Sg H v ψ) with hy
  set F : ℝ → ℝ := fun v => inner ℝ (y v) (R (y v)) with hF
  -- energy at time v
  set E : ℝ → ℝ := fun v => ∫ x, inner ℝ (Torus.grad (Sg H v ψ) x) (Torus.grad (Sg H v ψ) x) * ρβ x
    with hE
  have hE_eq : ∀ v, E v = ∫ x, ρβ x * ‖Torus.grad (Sg H v ψ) x‖ ^ 2 := by
    intro v
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [real_inner_self_eq_norm_sq, mul_comm]
  have hy2 : ∀ v, 0 ≤ v → ‖y v‖ ^ 2 = l2Inner (withDensityReal ρβ) (Sg H v ψ) (Sg H v ψ) :=
    fun v hv => l2c1_norm_sq_pL (G := fun v => Sg H v ψ) (hCont v hv)
  have hEpoin : ∀ v, 0 ≤ v → cP * ‖y v‖ ^ 2 ≤ E v := by
    intro v hv
    rw [hy2 v hv, hE_eq]
    exact hPo _ (hC1 v hv) (hpair0 v hv)
  -- the differential inequality
  have hder : ∀ v, 0 < v → HasDerivAt F (-(2 * β⁻¹ * E v)) v := Pψ.2.1
  have hle : ∀ v, 0 < v → -(2 * β⁻¹ * E v) ≤ -a * F v := by
    intro v hv
    have h1 := hEpoin v hv.le
    have h2 := (hform (y v)).2
    have h3 : F v ≤ κ₂ * ‖y v‖ ^ 2 := h2
    have h4 : a * F v ≤ 2 * β⁻¹ * cP * ‖y v‖ ^ 2 := by
      rw [ha, div_mul_eq_mul_div, div_le_iff₀ hκ₂]
      have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 * β⁻¹ * cP)
      nlinarith [this]
    have h5 : 2 * β⁻¹ * (cP * ‖y v‖ ^ 2) ≤ 2 * β⁻¹ * E v :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith [h4, h5]
  have hgron := fun τ' (h : 0 ≤ τ') => l2c1_gronwall Pψ.1 hder hle h
  -- initial value
  have hS0 : Sg H 0 ψ = projMean (withDensityReal ρβ) ψ := frozen_zero hd1 H hψc hψm
  have hQc : Continuous (projMean (withDensityReal ρβ) ψ) := by
    unfold projMean; exact hψc.sub continuous_const
  have hF0 : F 0 ≤ κ₂ * (Λ₀ * l2NormSq (projMean (withDensityReal ρβ) ψ)) := by
    have h1 : F 0 ≤ κ₂ * ‖y 0‖ ^ 2 := (hform (y 0)).2
    have h2 : ‖y 0‖ ^ 2 = l2Inner (withDensityReal ρβ) (projMean (withDensityReal ρβ) ψ)
        (projMean (withDensityReal ρβ) ψ) := by
      rw [hy2 0 le_rfl, hS0]
    have h3 := (l2c1_l2Inner_bounds hprob hρc H.hlow H.le_Lam hQc).2
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 hκ₂.le)
  have hQ0 : 0 ≤ l2NormSq (projMean (withDensityReal ρβ) ψ) :=
    integral_nonneg fun x => sq_nonneg _
  refine ⟨?_, ?_⟩
  · -- (1)
    have hb := (l2c1_l2Inner_bounds hprob hρc H.hlow H.le_Lam (hCont τ hτ)).1
    have hyτ : ‖y τ‖ ^ 2 ≤ κ₁ * F τ := (hform (y τ)).1
    have hFτ := hgron τ hτ
    have hexp : 0 < Real.exp (-a * τ) := Real.exp_pos _
    have step1 : c₀ * l2NormSq (Sg H τ ψ) ≤ κ₁ * (Real.exp (-a * τ) * F 0) := by
      have := hy2 τ hτ
      unfold l2NormSq
      calc c₀ * ∫ x, Sg H τ ψ x ^ 2 ≤ l2Inner (withDensityReal ρβ) (Sg H τ ψ) (Sg H τ ψ) := hb
        _ = ‖y τ‖ ^ 2 := this.symm
        _ ≤ κ₁ * F τ := hyτ
        _ ≤ κ₁ * (Real.exp (-a * τ) * F 0) := mul_le_mul_of_nonneg_left hFτ hκ₁.le
    have step2 : Real.exp (-a * τ) * F 0 ≤
        Real.exp (-a * τ) * (κ₂ * (Λ₀ * l2NormSq (projMean (withDensityReal ρβ) ψ))) :=
      mul_le_mul_of_nonneg_left hF0 hexp.le
    have step3 : l2NormSq (Sg H τ ψ) ≤ A1 * (Real.exp (-a * τ) * l2NormSq (projMean (withDensityReal ρβ) ψ)) := by
      rw [hA1, div_mul_eq_mul_div, le_div_iff₀ hc₀]
      nlinarith [mul_le_mul_of_nonneg_left step2 hκ₁.le]
    have hX : 0 ≤ Real.exp (-a * τ) * l2NormSq (projMean (withDensityReal ρβ) ψ) :=
      mul_nonneg hexp.le hQ0
    calc l2NormSq (Sg H τ ψ) ≤ A1 * (Real.exp (-a * τ) * l2NormSq (projMean (withDensityReal ρβ) ψ)) := step3
      _ ≤ (A1 + A2 + 1) * Real.exp (-a * τ) * l2NormSq (projMean (withDensityReal ρβ) ψ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith) hX
  · -- (2)
    obtain ⟨hint, hid⟩ := susceptibilityCov_eq_integral hd1 s νm νp c₀ Λ₀ β V ρβ H ψ ψ hψc hψm hψc hψm
    have hCb := (hSb ψ (hψc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).2
    have hl2 := (l2c1_l2Inner_bounds hprob hρc H.hlow H.le_Lam hQc).2
    have hl2n : 0 ≤ l2Inner (withDensityReal ρβ) (projMean (withDensityReal ρβ) ψ)
        (projMean (withDensityReal ρβ) ψ) := by
      rw [MFAdjoint.l2Inner_mu hprob]
      exact integral_nonneg fun x => mul_nonneg (hprob.nonneg x) (mul_self_nonneg _)
    have hCb' : susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β ψ ψ ≤
        max CS 0 * (Λ₀ * l2NormSq (projMean (withDensityReal ρβ) ψ)) :=
      hCb.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hl2n).trans
        (mul_le_mul_of_nonneg_left hl2 (le_max_right _ _)))
    -- the energy integral
    have hEn : 0 ≤ ∫ v in Set.Ici (0 : ℝ), E v :=
      setIntegral_nonneg measurableSet_Ici fun v hv => energy_nonneg hprob.nonneg
    have hEval : ∫ v in Set.Ici (0 : ℝ), E v =
        (2 * β⁻¹)⁻¹ * susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β ψ ψ := by
      have hid' : susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β ψ ψ =
          2 * β⁻¹ * ∫ v in Set.Ici (0 : ℝ), E v := hid
      rw [hid']
      field_simp
    have hmonoE : ∫ v in Set.Icc (0 : ℝ) τ, E v ≤ ∫ v in Set.Ici (0 : ℝ), E v :=
      setIntegral_mono_set hint (Filter.Eventually.of_forall fun v =>
          energy_nonneg hprob.nonneg) (Filter.Eventually.of_forall Set.Icc_subset_Ici_self)
    have hpt : ∫ v in Set.Icc (0 : ℝ) τ, ∫ x, ‖Torus.grad (Sg H v ψ) x‖ ^ 2 ≤
        ∫ v in Set.Icc (0 : ℝ) τ, c₀⁻¹ * E v := by
      refine integral_mono_of_nonneg ?_ ((hint.mono_set Set.Icc_subset_Ici_self).const_mul _) ?_
      · exact (ae_restrict_iff' measurableSet_Icc).2
          (Filter.Eventually.of_forall fun v _ => integral_nonneg fun x => sq_nonneg _)
      · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun v hv => ?_)
        have h1 := hC1 v hv.1
        have hgc := MFApriori.continuous_norm_grad_sq h1
        have h4 : c₀ * ∫ x, ‖Torus.grad (Sg H v ψ) x‖ ^ 2 ≤
            ∫ x, ρβ x * ‖Torus.grad (Sg H v ψ) x‖ ^ 2 := by
          rw [← integral_const_mul]
          exact integral_mono ((hgc.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).const_mul _)
            ((hρc.mul hgc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            fun x => mul_le_mul_of_nonneg_right (H.hlow x) (sq_nonneg _)
        show (∫ x, ‖Torus.grad (Sg H v ψ) x‖ ^ 2) ≤ c₀⁻¹ * E v
        rw [hE_eq v, le_inv_mul_iff₀ hc₀]
        exact h4
    rw [integral_const_mul] at hpt
    have hfin : ∫ v in Set.Icc (0 : ℝ) τ, ∫ x, ‖Torus.grad (Sg H v ψ) x‖ ^ 2 ≤
        A2 * l2NormSq (projMean (withDensityReal ρβ) ψ) := by
      calc _ ≤ c₀⁻¹ * ∫ v in Set.Icc (0 : ℝ) τ, E v := hpt
        _ ≤ c₀⁻¹ * ∫ v in Set.Ici (0 : ℝ), E v :=
          mul_le_mul_of_nonneg_left hmonoE (inv_nonneg.2 hc₀.le)
        _ = c₀⁻¹ * ((2 * β⁻¹)⁻¹ *
            susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β ψ ψ) := by rw [hEval]
        _ ≤ c₀⁻¹ * ((2 * β⁻¹)⁻¹ * (max CS 0 * (Λ₀ * l2NormSq (projMean (withDensityReal ρβ) ψ)))) := by
          gcongr
        _ = A2 * l2NormSq (projMean (withDensityReal ρβ) ψ) := by rw [hA2]; ring
    calc _ ≤ A2 * l2NormSq (projMean (withDensityReal ρβ) ψ) := hfin
      _ ≤ (A1 + A2 + 1) * l2NormSq (projMean (withDensityReal ρβ) ψ) :=
        mul_le_mul_of_nonneg_right (by linarith) hQ0

end HRS.MC.L2C1
