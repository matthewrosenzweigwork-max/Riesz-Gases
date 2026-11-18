import HRS.MS.SA16PRiesz4

/-!
# SA16P, part 5: the Riesz representation theorem for `L^p`

`sa16p_riesz`: for Hölder conjugate `p, q` and `ℓ ∈ (L^p(μ))^*` (`μ` σ-finite) there is a measurable `g ∈ L^q` with
`‖g‖_q ≤ ‖ℓ‖` and `ℓ f = ∫ f g` for every `f ∈ L^p`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

section Final
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {h : α → ℝ} (hh : MemLp h (ENNReal.ofReal p) μ)
  (ℓ : Lp ℝ (ENNReal.ofReal p) μ →L[ℝ] ℝ)

/-- `∫⁻ ‖g‖^q ≤ ‖ℓ‖^q` by monotone convergence over the truncations -/
lemma sa16p_lintegral_bound {q : ℝ} (hpq : p.HolderConjugate q) (hhm : Measurable h)
    (hpos : ∀ x, 0 < h x) (hp : 1 < p) :
    ∫⁻ x, ‖sa16p_g hh ℓ hp x‖ₑ ^ q ∂μ ≤ ENNReal.ofReal (‖ℓ‖ ^ q) := by
  have hq : 1 < q := hpq.symm.lt
  have hq0 : 0 < q := by linarith
  have hgm := sa16p_g_measurable hh ℓ hhm hp
  set f : ℕ → α → ℝ≥0∞ := fun N => (sa16p_T hh ℓ hp N).indicator (fun x => ‖sa16p_g hh ℓ hp x‖ₑ ^ q)
    with hf
  have hfm : ∀ N, Measurable (f N) := fun N =>
    (hgm.enorm.pow_const _).indicator (sa16p_T_measurable hh ℓ hhm hp N)
  have hmono : Monotone f := by
    intro N M hNM x
    by_cases hx : x ∈ sa16p_T hh ℓ hp N
    · have hxM : x ∈ sa16p_T hh ℓ hp M := by
        obtain ⟨h1, h2⟩ := hx
        refine ⟨h1.trans (by exact_mod_cast hNM), le_trans ?_ h2⟩
        apply one_div_le_one_div_of_le (by positivity)
        have : (N : ℝ) ≤ M := by exact_mod_cast hNM
        linarith
      simp only [hf, Set.indicator_of_mem hx, Set.indicator_of_mem hxM, le_refl]
    · simp only [hf, Set.indicator_of_notMem hx, zero_le]
  have hsup : ∀ x, ⨆ N, f N x = ‖sa16p_g hh ℓ hp x‖ₑ ^ q := by
    intro x
    apply le_antisymm
    · refine iSup_le fun N => ?_
      by_cases hx : x ∈ sa16p_T hh ℓ hp N
      · simp only [hf, Set.indicator_of_mem hx, le_refl]
      · simp only [hf, Set.indicator_of_notMem hx, zero_le]
    · obtain ⟨N1, hN1⟩ := exists_nat_ge |sa16p_g hh ℓ hp x|
      obtain ⟨N2, hN2⟩ := exists_nat_ge (1 / h x)
      have hxT : x ∈ sa16p_T hh ℓ hp (max N1 N2) := by
        refine ⟨hN1.trans (by exact_mod_cast le_max_left _ _), ?_⟩
        have h2 : 1 / h x ≤ ((max N1 N2 : ℕ) : ℝ) + 1 := by
          have : (N2 : ℝ) ≤ ((max N1 N2 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
          linarith
        rw [div_le_iff₀ (by positivity)]
        have := (div_le_iff₀ (hpos x)).1 h2
        linarith [mul_comm (h x) (((max N1 N2 : ℕ) : ℝ) + 1)]
      refine le_iSup_of_le (max N1 N2) ?_
      simp only [hf, Set.indicator_of_mem hxT, le_refl]
  have hint : ∫⁻ x, ‖sa16p_g hh ℓ hp x‖ₑ ^ q ∂μ = ⨆ N, ∫⁻ x, f N x ∂μ := by
    rw [← lintegral_iSup hfm hmono]
    exact lintegral_congr fun x => (hsup x).symm
  rw [hint]
  refine iSup_le fun N => ?_
  obtain ⟨hI, hIb⟩ := sa16p_trunc hh ℓ hpq hhm hpos hp N
  have hnn : 0 ≤ᵐ[μ] (sa16p_T hh ℓ hp N).indicator (fun x => |sa16p_g hh ℓ hp x| ^ q) :=
    Eventually.of_forall fun x => by
      by_cases hx : x ∈ sa16p_T hh ℓ hp N
      · rw [Set.indicator_of_mem hx]; exact Real.rpow_nonneg (abs_nonneg _) _
      · simp [Set.indicator_of_notMem hx]
  have h1 := ofReal_integral_eq_lintegral_ofReal hI hnn
  have h2 : ∫⁻ x, f N x ∂μ = ∫⁻ x, ENNReal.ofReal
      ((sa16p_T hh ℓ hp N).indicator (fun x => |sa16p_g hh ℓ hp x| ^ q) x) ∂μ := by
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ sa16p_T hh ℓ hp N
    · simp only [hf, Set.indicator_of_mem hx]
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
    · simp [hf, Set.indicator_of_notMem hx]
  rw [h2, ← h1]
  exact ENNReal.ofReal_le_ofReal hIb

end Final

/-- **Riesz representation theorem for `L^p`**, `1 < p < ∞`, σ-finite measure. -/
theorem sa16p_riesz {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {p q : ℝ}
    (hpq : p.HolderConjugate q) [Fact (1 ≤ ENNReal.ofReal p)]
    (ℓ : Lp ℝ (ENNReal.ofReal p) μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, Measurable g ∧ MemLp g (ENNReal.ofReal q) μ ∧
      eLpNorm g (ENNReal.ofReal q) μ ≤ ENNReal.ofReal ‖ℓ‖ ∧
      ∀ f : Lp ℝ (ENNReal.ofReal p) μ, ℓ f = ∫ x, f x * g x ∂μ := by
  have hp : 1 < p := hpq.lt
  have hq : 1 < q := hpq.symm.lt
  obtain ⟨h, hhm, hpos, hh⟩ := sa16p_weight (μ := μ) hp
  have hgm : Measurable (sa16p_g hh ℓ hp) := sa16p_g_measurable hh ℓ hhm hp
  have hlint := sa16p_lintegral_bound hh ℓ hpq hhm hpos hp
  have hq0 : 0 < q := by linarith
  have hqe0 : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  have hgnorm : eLpNorm (sa16p_g hh ℓ hp) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal ‖ℓ‖ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqe0 ENNReal.ofReal_ne_top hgm.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq0.le]
    calc (∫⁻ x, ‖sa16p_g hh ℓ hp x‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (ENNReal.ofReal (‖ℓ‖ ^ q)) ^ (1 / q) :=
          ENNReal.rpow_le_rpow hlint (by positivity)
      _ = ENNReal.ofReal ‖ℓ‖ := by
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by positivity),
            ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hq0.ne', Real.rpow_one]
  have hgmem : MemLp (sa16p_g hh ℓ hp) (ENNReal.ofReal q) μ := lt_of_le_of_lt hgnorm ENNReal.ofReal_lt_top
  refine ⟨sa16p_g hh ℓ hp, hgm, hgmem, hgnorm, fun f => ?_⟩
  have := hpq.ennrealOfReal
  set g := sa16p_g hh ℓ hp with hg
  have hfg : Integrable (fun x => f x * g x) μ := (Lp.memLp f).integrable_mul hgmem
  have hfm : Measurable (f : α → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hGi := sa16p_G_integrable hh ℓ hp
  set S : ℕ → Set α := fun N => {x | |f x| ≤ N ∧ 1 / ((N : ℝ) + 1) ≤ h x} with hS
  have hSm : ∀ N, MeasurableSet (S N) := fun N =>
    (measurableSet_le hfm.abs measurable_const).inter (measurableSet_le measurable_const hhm)
  have hSev : ∀ x, ∀ᶠ N : ℕ in atTop, x ∈ S N := by
    intro x
    obtain ⟨N1, hN1⟩ := exists_nat_ge |f x|
    obtain ⟨N2, hN2⟩ := exists_nat_ge (1 / h x)
    refine Filter.eventually_atTop.2 ⟨max N1 N2, fun N hN => ⟨?_, ?_⟩⟩
    · exact hN1.trans (by exact_mod_cast le_trans (le_max_left _ _) hN)
    · have h2 : 1 / h x ≤ (N : ℝ) + 1 := by
        have : (N2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hN
        linarith
      rw [div_le_iff₀ (by positivity)]
      have := (div_le_iff₀ (hpos x)).1 h2
      linarith [mul_comm (h x) ((N : ℝ) + 1)]
  set s : ℕ → α → ℝ := fun N => (S N).indicator (fun x => f x / h x) with hs
  have hsm : ∀ N, Measurable (s N) := fun N => (hfm.div hhm).indicator (hSm N)
  have hsb : ∀ N x, |s N x| ≤ (N : ℝ) * ((N : ℝ) + 1) := by
    intro N x
    by_cases hx : x ∈ S N
    · simp only [hs, Set.indicator_of_mem hx]
      obtain ⟨h1, h2⟩ := hx
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have e2 : 1 / h x ≤ (N : ℝ) + 1 := by
        rw [div_le_iff₀ (hpos x)]
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).1 h2
        linarith [this, mul_comm (h x) ((N : ℝ) + 1)]
      rw [abs_div, abs_of_pos (hpos x), div_eq_mul_one_div]
      exact mul_le_mul h1 e2 (one_div_nonneg.2 (hpos x).le) hN0
    · simp only [hs, Set.indicator_of_notMem hx, abs_zero]
      positivity
  have hmN : ∀ N, MemLp (fun x => s N x * h x) (ENNReal.ofReal p) μ := fun N =>
    sa16p_mulh_memLp hh (hsm N).aestronglyMeasurable (hsb N)
  have eN : ∀ N, ℓ ((hmN N).toLp _) = ∫ x, s N x * sa16p_G hh ℓ hp x ∂μ := fun N =>
    sa16p_ell_bdd hh ℓ hp (hsm N) (hsb N) (hmN N)
  have hpt1 : ∀ N x, s N x * sa16p_G hh ℓ hp x = (S N).indicator (fun x => f x * g x) x := by
    intro N x
    by_cases hx : x ∈ S N
    · simp only [hs, Set.indicator_of_mem hx]
      have hG : sa16p_G hh ℓ hp x = g x * h x := sa16p_G_eq hh ℓ hpos hp x
      have hh0 := (hpos x).ne'
      rw [hG]
      field_simp
    · simp only [hs, Set.indicator_of_notMem hx, zero_mul]
  have hpt2 : ∀ N x, s N x * h x = (S N).indicator (fun x => f x) x := by
    intro N x
    by_cases hx : x ∈ S N
    · simp only [hs, Set.indicator_of_mem hx]
      have hh0 := (hpos x).ne'
      field_simp
    · simp only [hs, Set.indicator_of_notMem hx, zero_mul]
  have hp1 : (1 : ℝ) ≤ p := hp.le
  have hLp : Tendsto (fun N => (hmN N).toLp _) atTop (𝓝 ((Lp.memLp f).toLp f)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun N x => s N x * h x) hmN (f : α → ℝ) (Lp.memLp f)]
    refine sa16p_dct_Lp hp1 (g := fun x => ‖f x‖) (fun N => (hmN N).aestronglyMeasurable)
      (Lp.memLp f).aestronglyMeasurable (Lp.memLp f).norm (fun N => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [hpt2]
      by_cases hx : x ∈ S N
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
      · rw [Set.indicator_of_notMem hx]; simp
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hSev x] with N hN
      rw [hpt2, Set.indicator_of_mem hN]
  have h1 := (ℓ.continuous.tendsto _).comp hLp
  rw [Lp.toLp_coeFn f (Lp.memLp f)] at h1
  have h2 : Tendsto (fun N => ∫ x, s N x * sa16p_G hh ℓ hp x ∂μ) atTop (𝓝 (∫ x, f x * g x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f x * g x‖)
      (fun N => ((hsm N).aestronglyMeasurable).mul hGi.aestronglyMeasurable) hfg.norm
      (fun N => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [hpt1]
      by_cases hx : x ∈ S N
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, norm_zero]; exact norm_nonneg _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hSev x] with N hN
      rw [hpt1, Set.indicator_of_mem hN]
  have h3 : (fun N => ℓ ((hmN N).toLp _)) = fun N => ∫ x, s N x * sa16p_G hh ℓ hp x ∂μ := funext eN
  have h1' : Tendsto (fun N => ℓ ((hmN N).toLp _)) atTop (𝓝 (ℓ f)) := h1
  rw [h3] at h1'
  exact tendsto_nhds_unique h1' h2

end HRS.Whole.AppendixA.Phase2SA16P
