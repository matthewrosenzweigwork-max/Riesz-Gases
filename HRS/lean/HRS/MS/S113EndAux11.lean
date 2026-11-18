import HRS.MS.S113EndAux10
import HRS.MS.R2S11Aux14
import HRS.MS.R2S11Aux15

/-!
# S11.3 endpoint (worker S113X), part 11: measurability of `t ↦ L(t) = ‖∇u^t‖_∞` on the small class (X5)

Steps: (a) `ρ^t` is `C¹` (Sobolev embedding `Σ^m ↪ C¹` and `ρ^t = ρ_* + √ρ_* v_t`); (b) `t ↦ u^t(y)` is measurable for each `y` (difference
quotients of `log ρ^t`, measurability of the parametric convolution integral from the joint continuity of `(t,x) ↦ ρ^t(x)`);
(c) the operator norm of `Du^t(x)` over a countable dense set of `(x, v)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s113x_rho0_smooth (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {q β : ℝ} (hq : 0 < q) (hβ : 0 < β)
    {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) : ContDiff ℝ 1 ρ₀ := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd hq hβ
  have : ρ₀ = thermalDensity d s q β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd hq hβ hρ₀
  rw [this]
  exact hT.smooth.of_le (by exact_mod_cast le_top)

theorem s113x_class_c1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {q β : ℝ} (hq : 0 < q) (hβ : 0 < β)
    {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {m : ℕ} (hm : (1 : ℝ) + d / 2 < m) {r c₀ : ℝ}
    {f0 : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ 1 (ρ t) := by
  have hρ₀s := s113x_rho0_smooth hd hs0 hsd hq hβ hρ₀
  have hpos : ∀ x, 0 < ρ₀ x := (HRS.MS.MovEnt.s66_rho0_facts hd hs0 hsd hq hβ hρ₀).2.1
  have hcont : Continuous ρ₀ := hρ₀s.continuous
  have hv : Continuous (movV ρ₀ ρ t) := by
    unfold movV
    exact ((hρ.regular t ht).sub hcont).div (hcont.sqrt) (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
  obtain ⟨C, hC0, hC⟩ := HRS.MS.Mov63.mn_sobolev_emb_gen 1 m (by exact_mod_cast hm)
  obtain ⟨g, hgd, hfg, -⟩ := hC _ (hρ.weighted t ht).1
  have heq := HRS.MS.Mov63.mn_ae_eq_cont hv hgd.continuous hfg
  have hvd : ContDiff ℝ 1 (movV ρ₀ ρ t) := by
    rw [heq]; exact_mod_cast hgd
  have hsq : ContDiff ℝ 1 (fun x => Real.sqrt (ρ₀ x)) := hρ₀s.sqrt (fun x => (hpos x).ne')
  have e : ρ t = fun x => ρ₀ x + Real.sqrt (ρ₀ x) * movV ρ₀ ρ t x := by
    funext x
    unfold movV
    have := (Real.sqrt_pos.2 (hpos x)).ne'
    field_simp
    ring
  rw [e]
  exact hρ₀s.add (hsq.mul hvd)

theorem s113x_dirderiv_meas {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] {f : ℝ → Euc d → F} (y e : Euc d)
    (hdiff : ∀ t, DifferentiableAt ℝ (f t) y)
    (hm : ∀ z, Measurable fun t => f t z) : Measurable fun t => fderiv ℝ (f t) y e := by
  have hlim : ∀ t, Tendsto (fun n : ℕ => ((n : ℝ) + 1) • (f t (y + (1 / ((n : ℝ) + 1)) • e) - f t y))
      atTop (𝓝 (fderiv ℝ (f t) y e)) := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => y + s • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add y
    have hd : HasDerivAt (fun s : ℝ => f t (y + s • e)) (fderiv ℝ (f t) y e) 0 :=
      (hdiff t).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
    have hs := hd.tendsto_slope_zero
    have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Filter.Eventually.of_forall fun n =>
          (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity).ne'⟩
    have := hs.comp hseq
    refine this.congr fun n => ?_
    simp only [Function.comp, zero_add, zero_smul, add_zero]
    rw [one_div, inv_inv]
  refine measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.2 hlim)
  exact Measurable.const_smul ((hm _).sub (hm _)) _

theorem s113x_gradient_coord (g : Euc d → ℝ) (y : Euc d) (k : Fin d) :
    (gradient g y).ofLp k = fderiv ℝ g y (EuclideanSpace.single k 1) := by
  have h1 : inner ℝ (gradient g y) (EuclideanSpace.single k 1) = fderiv ℝ g y (EuclideanSpace.single k 1) :=
    InnerProductSpace.toDual_symm_apply
  rw [EuclideanSpace.inner_single_right] at h1
  simpa using h1

theorem s113x_gradient_meas {f : ℝ → Euc d → ℝ} (y : Euc d) (hdiff : ∀ t, DifferentiableAt ℝ (f t) y)
    (hm : ∀ z, Measurable fun t => f t z) : Measurable fun t => gradient (f t) y := by
  have hc : ∀ k : Fin d, Measurable fun t => (gradient (f t) y).ofLp k := fun k => by
    simp only [s113x_gradient_coord]
    exact s113x_dirderiv_meas y _ hdiff hm
  have := (WithLp.measurable_toLp 2 (∀ _ : Fin d, ℝ)).comp (measurable_pi_iff.2 hc)
  simpa [Function.comp_def] using this

theorem s113x_force_meas {g : Euc d → Euc d} (hg : Measurable g) {ρh : ℝ → Euc d → ℝ}
    (hρh : Continuous fun p : ℝ × Euc d => ρh p.1 p.2) (y : Euc d) :
    Measurable fun t => convGradConvW g (ρh t) y := by
  unfold convGradConvW
  have h1 : Measurable fun p : ℝ × Euc d => ρh p.1 p.2 := hρh.measurable
  have h2 : Measurable fun p : ℝ × Euc d => ρh p.1 y :=
    (hρh.comp (continuous_fst.prodMk continuous_const)).measurable
  have h3 : Measurable fun p : ℝ × Euc d => g (y - p.2) := hg.comp (measurable_const.sub measurable_snd)
  have hset : MeasurableSet {p : ℝ × Euc d | ‖y - p.2‖ ≤ 1 / 4} :=
    measurableSet_le (measurable_norm.comp (measurable_const.sub measurable_snd)) measurable_const
  have hf : Measurable fun p : ℝ × Euc d =>
      (if ‖y - p.2‖ ≤ 1 / 4 then (ρh p.1 p.2 - ρh p.1 y) • g (y - p.2) else ρh p.1 p.2 • g (y - p.2)) :=
    Measurable.ite hset ((h1.sub h2).smul h3) (h1.smul h3)
  exact (StronglyMeasurable.integral_prod_right (f := fun t y' =>
    (if ‖y - y'‖ ≤ 1 / 4 then (ρh t y' - ρh t y) • g (y - y') else ρh t y' • g (y - y')))
    hf.stronglyMeasurable).measurable

theorem s113x_opnorm_le_of_dense {A : Euc d →L[ℝ] Euc d} {B : ℝ} (hB : 0 ≤ B) {D : Set (Euc d)} (hD : Dense D)
    (h : ∀ v ∈ D, ‖A v‖ ≤ B * ‖v‖) : ‖A‖ ≤ B := by
  refine A.opNorm_le_bound hB fun v => ?_
  have hcl : IsClosed {v : Euc d | ‖A v‖ ≤ B * ‖v‖} :=
    isClosed_le (A.continuous.norm) (continuous_const.mul continuous_norm)
  have hsub : D ⊆ {v : Euc d | ‖A v‖ ≤ B * ‖v‖} := fun v hv => h v hv
  have := closure_minimal hsub hcl
  rw [hD.closure_eq] at this
  exact this (Set.mem_univ v)

theorem s113x_L_measurable_abs {u : ℝ → Euc d → Euc d} (hC1 : ∀ t, ContDiff ℝ 1 (u t))
    (hu : ∀ y, Measurable fun t => u t y)
    (hfin : ∀ t, (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (u t) x‖) < ⊤) :
    Measurable fun t => (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (u t) x‖).toReal := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Euc d)
  refine measurable_of_Iic fun B => ?_
  by_cases hB : B < 0
  · have : (fun t => (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (u t) x‖).toReal) ⁻¹' Set.Iic B = ∅ := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hB ENNReal.toReal_nonneg
    rw [this]; exact MeasurableSet.empty
  · push_neg at hB
    have hset : (fun t => (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (u t) x‖).toReal) ⁻¹' Set.Iic B =
        ⋂ x ∈ D, ⋂ v ∈ D, {t : ℝ | ‖fderiv ℝ (u t) x v‖ ≤ B * ‖v‖} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h x _ v _
        have h1 : ENNReal.ofReal ‖fderiv ℝ (u t) x‖ ≤ ⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (u t) x‖ :=
          le_iSup (fun x : Euc d => ENNReal.ofReal ‖fderiv ℝ (u t) x‖) x
        have h2 : ‖fderiv ℝ (u t) x‖ ≤ B := ((ENNReal.ofReal_le_iff_le_toReal (hfin t).ne).1 h1).trans h
        calc ‖fderiv ℝ (u t) x v‖ ≤ ‖fderiv ℝ (u t) x‖ * ‖v‖ := (fderiv ℝ (u t) x).le_opNorm v
          _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      · intro h
        have h1 : ∀ x ∈ D, ‖fderiv ℝ (u t) x‖ ≤ B := fun x hx =>
          s113x_opnorm_le_of_dense hB hDd (fun v hv => h x hx v hv)
        have h2 : ∀ x, ‖fderiv ℝ (u t) x‖ ≤ B := by
          have hcl : IsClosed {x : Euc d | ‖fderiv ℝ (u t) x‖ ≤ B} :=
            isClosed_le ((hC1 t).continuous_fderiv one_ne_zero).norm continuous_const
          have := closure_minimal (fun x hx => h1 x hx) hcl
          rw [hDd.closure_eq] at this
          exact fun x => this (Set.mem_univ x)
        exact ENNReal.toReal_le_of_le_ofReal hB (iSup_le fun x => ENNReal.ofReal_le_ofReal (h2 x))
    rw [hset]
    refine MeasurableSet.biInter hDc fun x _ => MeasurableSet.biInter hDc fun v _ => ?_
    have hm : Measurable fun t => fderiv ℝ (u t) x v :=
      s113x_dirderiv_meas (F := Euc d) x v (fun t => ((hC1 t).differentiable one_ne_zero) x) hu
    exact measurableSet_le hm.norm measurable_const

theorem s113x_rieszKernelGrad_meas (s : ℝ) : Measurable (rieszKernelGrad d s) := by
  unfold rieszKernelGrad gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)

/-- X5: measurability of `t ↦ L(t)` on `(0,∞)` for the small class. -/
theorem s113x_meas (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {q β : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ} {εstar r c₀ c C₁ : ℝ} (hj : 1 ≤ j)
    (hm : (d : ℝ) / 2 + j + 6 < m) (hC₁ : 0 < C₁) (hε : 0 < εstar) (hc₀ : 0 < c₀)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) :
    S113XMeas d s q β ρ₀ j m εstar r c₀ := by
  intro f0 hf0 ρ hρ'
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hmd : (d : ℝ) / 2 < m := by linarith
  have hm1 : (1 : ℝ) + d / 2 < m := by linarith
  have hρ₀s := s113x_rho0_smooth hd hs0 hsd hq hβ hρ₀
  have hρp : ∀ x, 0 < ρ₀ x := (HRS.MS.MovEnt.s66_rho0_facts hd hs0 hsd hq hβ hρ₀).2.1
  set ρh : ℝ → Euc d → ℝ := fun t => ρ ((t.toNNReal : ℝ≥0) : ℝ) with hρh
  have hcont : Continuous fun p : ℝ × Euc d => ρh p.1 p.2 :=
    (HRS.MS.R2S11.s11_class_continuous hρ₀s.continuous hρp hmd hρ').comp
      ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
  have hτ : ∀ t : ℝ, 0 ≤ ((t.toNNReal : ℝ≥0) : ℝ) := fun t => NNReal.coe_nonneg _
  have hpos : ∀ t z, 0 < ρh t z := fun t z =>
    (HRS.MS.MovEnt.s66_class_props hNL hf0 hρ' hc₀.le _ (hτ t)).2.1 z
  have hC1 : ∀ t, ContDiff ℝ 1 (ρh t) := fun t => s113x_class_c1 hd hs0 hsd hq hβ hρ₀ hm1 hρ' (hτ t)
  -- pointwise measurability of the velocity
  have hlog : ∀ z, Measurable fun t => Real.log (ρh t z) := fun z =>
    Real.measurable_log.comp (hcont.comp (continuous_id.prodMk continuous_const)).measurable
  have hgrad : ∀ y, Measurable fun t => gradient (fun z => Real.log (ρh t z)) y := fun y =>
    s113x_gradient_meas (f := fun t z => Real.log (ρh t z)) y (fun t =>
      (Real.differentiableAt_log (hpos t y).ne').comp y ((hC1 t).differentiable one_ne_zero y)) hlog
  have hu : ∀ y, Measurable fun t => movU d s q β (ρh t) y := fun y => by
    have h1 : Measurable fun t => β⁻¹ • gradient (fun z => Real.log (ρh t z)) y :=
      Measurable.const_smul (hgrad y) β⁻¹
    have h2 : Measurable fun t => convGradConvW (rieszKernelGrad d s) (ρh t) y :=
      s113x_force_meas (s113x_rieszKernelGrad_meas s) hcont y
    have h3 : Measurable fun t : ℝ => β⁻¹ • gradient (fun z => Real.log (ρh t z)) y + q • y :=
      h1.add measurable_const
    exact h3.add h2
  have hUC1 : ∀ t, ContDiff ℝ 1 (movU d s q β (ρh t)) := fun t => by
    obtain ⟨-, -, -, hdec⟩ := HRS.MS.MovEnt.s66_class_props hNL hf0 hρ' hc₀.le _ (hτ t)
    obtain ⟨-, -, hcd, -⟩ := hdec _ (hτ t)
    exact hcd.of_le (by exact_mod_cast hj)
  have hfin : ∀ t, (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (movU d s q β (ρh t)) x‖) < ⊤ := fun t =>
    s113x_L_sup_lt_top hj hNL hC₁ hε hc₀ hf0 hρ' (hτ t)
  have hmeas := s113x_L_measurable_abs hUC1 hu hfin
  refine hmeas.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  simp only [hρh, Real.coe_toNNReal t (le_of_lt ht)]
  rfl

end HRS.MS.S113BD
