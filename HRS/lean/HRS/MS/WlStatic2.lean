import HRS.MS.WlStatic
import HRS.MS.R2MtAux2

/-!
# HRS.MS.WlStatic2 -- the crude quadratic estimate for a fixed `N` (WL-11 continuation)

Namespace `HRS.MS.Wl`, helper prefix `wl11_`.  Continuation of `HRS.MS.WlStatic` (which proves
`wl11_quad_large`).  Statements (no change of any frozen statement):
* `wl11_D_lintegral_le`: second moment of `D_N` from the pair second moments;
* `wl11_quad_crude`: for each fixed `N ≥ 2`, `Var_{Q_N}[D_N(h;ν)] ≤ C B²/N²` for `ν ∈ {μ, π_N}`
  (the constant depends on `N`, harmlessly: it is used only for the finitely many `N < N₁`);
* `wl11_quadratic_variance_bound`: conjunct 4 of `r2_log_static`, i.e. `QuadraticVarianceBound` for both centerings
  with the bound `C B²/N/N`, for every `N ≥ 2` (large `N` by `wl11_quad_large`, small `N` by `wl11_quad_crude`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-! ### The crude bound for a fixed `N` -/

/-- **Second moment of `D_N`** from the pair second moments: if `E_P ‖h(Y_a, Y_b)‖² ≤ W` for `a ≠ b` and
`|H_ν| ≤ H'`, then `E_P |D_N(h;ν)|² ≤ 3 W + 15 H'²`. -/
theorem wl11_D_lintegral_le {n : ℕ} (P : Measure (Fin (n + 1) → Euc d)) [IsProbabilityMeasure P]
    {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h)) (ν : Measure (Euc d))
    [IsProbabilityMeasure ν] {W H' : ℝ} (hW : 0 ≤ W)
    (hpair : ∀ a b : Fin (n + 1), a ≠ b → ∫⁻ Y, ‖h (Y a) (Y b)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal W)
    (hH' : ∀ x, |wr14a_Hc h ν x| ≤ H') :
    ∫⁻ Y, ‖HRS.Whole.centeredPairFunctional h Y ν‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (3 * W + 15 * H' ^ 2) := by
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hNn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by linarith
  have hc3 : (0 : ℝ) ≤ 3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hmeas : ∀ i j : Fin (n + 1), Measurable fun Y : Fin (n + 1) → Euc d => ‖h (Y i) (Y j)‖ₑ ^ 2 :=
    fun i j => ((wr14a_measurable_h_pair hm i j).enorm).pow_const 2
  have hH0 : 0 ≤ H' := (abs_nonneg _).trans (hH' 0)
  have hpt : ∀ Y : Fin (n + 1) → Euc d, ‖HRS.Whole.centeredPairFunctional h Y ν‖ₑ ^ 2 ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2
        + ENNReal.ofReal (15 * H' ^ 2) := by
    intro Y
    have h1 := wr14a_D_sq_le hN0 h ν hH' Y
    have e1 : ‖HRS.Whole.centeredPairFunctional h Y ν‖ₑ ^ 2 =
        ENNReal.ofReal (HRS.Whole.centeredPairFunctional h Y ν ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    have e2 : ∀ i j : Fin (n + 1), ‖h (Y i) (Y j)‖ₑ ^ 2 = ENNReal.ofReal (h (Y i) (Y j) ^ 2) := fun i j => by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e1]
    simp_rw [e2]
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), Finset.mul_sum]
    refine add_le_add (le_of_eq ?_) le_rfl
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_mul hc3]
  calc ∫⁻ Y, ‖HRS.Whole.centeredPairFunctional h Y ν‖ₑ ^ 2 ∂P
      ≤ ∫⁻ Y, (∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ‖h (Y i) (Y j)‖ₑ ^ 2 + ENNReal.ofReal (15 * H' ^ 2)) ∂P := lintegral_mono hpt
    _ = (∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ∫⁻ Y, ‖h (Y i) (Y j)‖ₑ ^ 2 ∂P) + ENNReal.ofReal (15 * H' ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        congr 1
        rw [lintegral_finsetSum Finset.univ (f := fun i (Y : Fin (n + 1) → Euc d) => ∑ j ∈ Finset.univ.erase i,
          ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2)
          (fun i _ => Finset.measurable_sum _ fun j _ => measurable_const.mul (hmeas i j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum (Finset.univ.erase i) (f := fun j (Y : Fin (n + 1) → Euc d) =>
          ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2)
          (fun j _ => measurable_const.mul (hmeas i j))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_const_mul _ (hmeas i j)]
    _ ≤ (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ENNReal.ofReal W) + ENNReal.ofReal (15 * H' ^ 2) := by
        gcongr with i _ j hj
        exact hpair i j (Finset.ne_of_mem_erase hj).symm
    _ ≤ ENNReal.ofReal (3 * W) + ENNReal.ofReal (15 * H' ^ 2) := by
        gcongr
        calc (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
              ENNReal.ofReal W)
            ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
              ENNReal.ofReal W := by
              refine Finset.sum_le_sum fun i _ => ?_
              exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
          _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) *
              W))) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              rw [ENNReal.ofReal_mul hNn, ENNReal.ofReal_mul hNn, ENNReal.ofReal_mul hc3,
                ENNReal.ofReal_natCast]
          _ = _ := by congr 1; field_simp
    _ = ENNReal.ofReal (3 * W + 15 * H' ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]

set_option maxHeartbeats 3200000 in
/-- **Quadratic estimate for a fixed `N ≥ 2`** (crude, constant depending on `N`): `Var_{Q_N}[D_N(h;ν)] ≤ C B²/N²`
for `ν ∈ {μ, π_N}`, uniformly in `ρ` and `β ∈ [β₋, β₊]`.  `Q_N` is the pinned law of the weak potential of `K`
(`wl_Q_eq_fieldLaw`): the pair second moments are `wr14a_pair_lintegral_le` (field `≤ β C_K`, kernel `K ≥ 0`),
the row `L²` bound is `wl_schur`, `|H_ν| ≤ c C_p B` is `wl10_Hc_bound`. -/
theorem wl11_quad_crude (hd : 2 ≤ d) (A βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) {N : ℕ} (hN : 2 ≤ N) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, βm ≤ β → β ≤ βp →
      ∀ (B : ℝ) (h : Euc d → Euc d → ℝ), Measurable (fun p : Euc d × Euc d => h p.1 p.2) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      ∀ ν ∈ ({HRS.Whole.withDensityReal ρ, HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs
          (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ))} : Set (Measure (Euc d))),
        evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν)
            (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 / N / N) := by
  have hβp0 : 0 < βp := hβm.trans_le hβ
  obtain ⟨Cs, hCs0, hCs⟩ := wl_schur hd A
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  obtain ⟨cH, hcH0, hHc⟩ := wl10_Hc_bound hd A
  obtain ⟨Cm, hCm1, hmarg⟩ := wl_marginal_L2 hd A βp hβp0.le
  set Cl' : ℝ := max Cl 0 with hCl'
  have hCl'0 : 0 ≤ Cl' := le_max_right _ _
  set Ebd : ℝ := Real.exp (βp * Cl' + 2 * (βp * CK)) with hEbd
  set Cp : ℝ := max Cm 1 with hCp
  have hCp1 : 1 ≤ Cp := le_max_right _ _
  have hCp0 : 0 ≤ Cp := by linarith
  set Wc : ℝ := Ebd * Cs with hWc
  have hWc0 : 0 ≤ Wc := by positivity
  refine ⟨(3 * Wc + 15 * (cH * Cp) ^ 2) * N * N, ?_⟩
  intro ρ hρ hA β hβ1 hβ2 B h hm hbd ν hν
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hB : 0 ≤ B := wl2_B_nonneg (by omega) hbd
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hNn : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hNn
  have hNR0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  obtain ⟨hK, hℓ, hℓle, hfield, hQeq⟩ := hQ ρ hρ hA β hβpos.le (n + 1) hNn
  set VK : WeakPotential μ := wlPot hK hCK0 hfield with hVKdef
  have hVK : VK.q = fun x y : Euc d => sphericalLogKernel x y := rfl
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβpos.le hNR0.le
  have hQpin : HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β μ =
      pinnedLaw VK (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    rw [hQeq VK hVK, wl5_pinnedLaw_empty]
    rfl
  haveI hQp : IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β μ) := by
    rw [hQpin]
    exact isProb_pinnedLaw VK hlam (n + 1) _
  set Q := HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β μ with hQ'
  -- the `L²` row bound
  have hrow2 : ∀ x, ∫⁻ z, ‖h x z‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (Cs * B ^ 2) := by
    intro x
    obtain ⟨-, hrows, -⟩ := hCs ρ hρ hA B h hm hbd
    obtain ⟨-, hi2, -, hle⟩ := hrows x
    have e : ∀ z, ‖h x z‖ₑ ^ 2 = ENNReal.ofReal (|h x z| ^ 2) := fun z => by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal hi2 (Filter.Eventually.of_forall fun z => by positivity)]
    exact ENNReal.ofReal_le_ofReal hle
  -- the constants of the weak potential
  have hM'le : VK.M' ≤ βp * Cl' := by
    show β * Cl / ((n + 1 : ℕ) : ℝ) ≤ _
    rw [div_le_iff₀ hNR0]
    have h1 : β * Cl ≤ β * Cl' := mul_le_mul_of_nonneg_left (le_max_left _ _) hβpos.le
    have h2 : β * Cl' ≤ βp * Cl' := mul_le_mul_of_nonneg_right hβ2 hCl'0
    have h3 : 0 ≤ βp * Cl' := by positivity
    nlinarith
  have hβCK : β * CK ≤ βp * CK := mul_le_mul_of_nonneg_right hβ2 hCK0
  have hpair : ∀ a b : Fin (n + 1), a ≠ b →
      ∫⁻ Y, ‖h (Y a) (Y b)‖ₑ ^ 2 ∂Q ≤ ENNReal.ofReal (Wc * B ^ 2) := by
    intro a b hab
    rw [hQpin]
    refine wr14a_pair_lintegral_le VK hβpos.le a b hab hm (fun x => ?_)
    calc ∫⁻ z, ‖h x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (VK.M' + β * VK.γ +
          pinField VK (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z)) ∂μ
        ≤ ∫⁻ z, ENNReal.ofReal Ebd * ‖h x z‖ₑ ^ 2 ∂μ := by
          refine lintegral_mono fun z => ?_
          rw [mul_comm]
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
          rw [pinField_pinsWith, RefMarg.pinField_empty]
          have h1 : VK.φ z ≤ β * CK := VK.φ_le z
          have h2 : 0 ≤ (β / ((n + 1 : ℕ) : ℝ)) * VK.q z x := mul_nonneg hlam (VK.q_nonneg _ _)
          have h3 : VK.γ = CK := rfl
          rw [h3]
          linarith
      _ = ENNReal.ofReal Ebd * ∫⁻ z, ‖h x z‖ₑ ^ 2 ∂μ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal Ebd * ENNReal.ofReal (Cs * B ^ 2) := by
          gcongr
          exact hrow2 x
      _ = ENNReal.ofReal (Wc * B ^ 2) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [hWc]; ring
  have key : ∀ ν : Measure (Euc d), IsProbabilityMeasure ν → ν ≤ ENNReal.ofReal Cp • μ →
      evariance (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X ν) Q ≤
        ENNReal.ofReal ((3 * Wc + 15 * (cH * Cp) ^ 2) * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * B ^ 2 /
          ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    intro ν hνp hνle
    have hH' : ∀ x, |wr14a_Hc h ν x| ≤ cH * Cp * B := hHc ρ hρ hA hνle hCp0 hB hbd
    have hF : Measurable (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X ν) :=
      wr14a_measurable_D hm ν
    have h1 : evariance (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X ν) Q ≤
        ∫⁻ X, ‖HRS.Whole.centeredPairFunctional h X ν‖ₑ ^ 2 ∂Q := by
      have := evariance_le_lintegral_sub Q hF.aestronglyMeasurable 0
      simpa using this
    refine h1.trans ((wl11_D_lintegral_le Q hm ν (by positivity) hpair hH').trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
    field_simp
  rcases hν with rfl | rfl
  · exact key _ inferInstance (Measure.le_iff'.2 fun A => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 hCp1))
  · obtain ⟨-, hπN, hsup, -, -⟩ := hmarg ρ hρ hA β hβpos hβ2 (n + 1) hN
    have hθb : ∀ x, wl_theta μ β (n + 1) x ≤ Cp := by
      intro x
      refine (hsup x).2.trans ?_
      have hr1 : (1 + ‖x‖ ^ 2) ^ (-(β / (2 * ((n + 1 : ℕ) : ℝ)))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖])
          (by have : 0 ≤ β / (2 * ((n + 1 : ℕ) : ℝ)) := by positivity
              linarith)
      calc Cm * (1 + ‖x‖ ^ 2) ^ (-(β / (2 * ((n + 1 : ℕ) : ℝ)))) ≤ Cm * 1 :=
            mul_le_mul_of_nonneg_left hr1 (by linarith)
        _ ≤ Cp := by rw [mul_one]; exact le_max_left _ _
    refine key _ (wr14a_isProb_firstMarginal hNn _) ?_
    rw [hπN]
    exact wl11_withDensity_le hθb

/-! ### Conjunct 4 of `r2_log_static` -/

/-- Large `N` in the form `Var ≤ C B²/N/N`. -/
theorem wl11_evariance_of_N_mul {N : ℕ} (hN : 0 < N) {e : ℝ≥0∞} {c : ℝ}
    (h : (N : ℝ≥0∞) * e ≤ ENNReal.ofReal (c / N)) : e ≤ ENNReal.ofReal (c / N / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  rw [ENNReal.ofReal_div_of_pos hNR, ENNReal.ofReal_natCast]
  rw [ENNReal.le_div_iff_mul_le (Or.inl h1) (Or.inl h2)]
  rw [mul_comm]
  exact h

/-- **Conjunct 4 of `r2_log_static`**: for every `N ≥ 2` (large `N` by `wl11_quad_large`, the finitely many
small `N` by `wl11_quad_crude`) and every `IsLogBoundedPairKernel B h`, `QuadraticVarianceBound h Q ν (C B²/N/N)`
for `ν = μ` and `ν = π_N`. -/
theorem wl11_quadratic_variance_bound (hd : 2 ≤ d) (βm βp A : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β ∈ Set.Icc βm βp, ∀ N : ℕ, 2 ≤ N → ∀ (B : ℝ) (h : Euc d → Euc d → ℝ), IsLogBoundedPairKernel B h →
        QuadraticVarianceBound h (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ))
          (HRS.Whole.withDensityReal ρ) (C * B ^ 2 / N / N) ∧
        QuadraticVarianceBound h (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ))
          (HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β
            (HRS.Whole.withDensityReal ρ))) (C * B ^ 2 / N / N) := by
  have hβp0 : 0 < βp := hβm.trans_le hβ
  obtain ⟨C1, N1, hlarge⟩ := wl11_quad_large hd A βm βp hβm hβ
  have hsmall : ∀ N : ℕ, ∃ Cn : ℝ, 2 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, βm ≤ β → β ≤ βp →
      ∀ (B : ℝ) (h : Euc d → Euc d → ℝ), Measurable (fun p : Euc d × Euc d => h p.1 p.2) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      ∀ ν ∈ ({HRS.Whole.withDensityReal ρ, HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs
          (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ))} : Set (Measure (Euc d))),
        evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν)
            (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (Cn * B ^ 2 / N / N) := by
    intro N
    by_cases hN : 2 ≤ N
    · obtain ⟨Cn, hCn⟩ := wl11_quad_crude hd A βm βp hβm hβ hN
      exact ⟨Cn, fun _ => hCn⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Cf hCf using hsmall
  obtain ⟨Cm, hCm1, hmarg⟩ := wl_marginal_L2 hd A βp hβp0.le
  set Cp : ℝ := max Cm 1 with hCp
  have hCp1 : 1 ≤ Cp := le_max_right _ _
  have hCp0 : 0 ≤ Cp := by linarith
  set S : ℝ := ∑ n ∈ Finset.range N1, |Cf n| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => abs_nonneg _
  refine ⟨max C1 S, ?_⟩
  intro ρ hρ hA β hβmem N hN B h hh
  obtain ⟨hβ1, hβ2⟩ := hβmem
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := wl_isProb hρ
  have hW := wl_gibbsWellDefined hd A ρ hρ hA β hβpos.le N (by omega)
  haveI hQp : IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β
      (HRS.Whole.withDensityReal ρ)) := HRS.MS.R2Mt.s92_isProb_Q hW
  have hvar : ∀ ν ∈ ({HRS.Whole.withDensityReal ρ, HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs
          (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ))} : Set (Measure (Euc d))),
        evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν)
            (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (max C1 S * B ^ 2 / N / N) := by
    intro ν hν
    by_cases hlt : N1 ≤ N
    · have := hlarge ρ hρ hA β hβ1 hβ2 N hlt hN B h hh.measurable hh.symm hh.bound ν hν
      refine (wl11_evariance_of_N_mul (by omega) this).trans (ENNReal.ofReal_le_ofReal ?_)
      gcongr
      exact le_max_left _ _
    · rw [not_le] at hlt
      refine (hCf N hN ρ hρ hA β hβ1 hβ2 B h hh.measurable hh.bound ν hν).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hle : Cf N ≤ S := by
        refine (le_abs_self _).trans ?_
        exact Finset.single_le_sum (f := fun n => |Cf n|) (fun n _ => abs_nonneg _) (Finset.mem_range.2 hlt)
      have : Cf N ≤ max C1 S := hle.trans (le_max_right _ _)
      gcongr
  have hπ : IsProbabilityMeasure (HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β
      (HRS.Whole.withDensityReal ρ))) := wr14a_isProb_firstMarginal (by omega) _
  have hπle : HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β
      (HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ := by
    obtain ⟨-, hπN, hsup, -, -⟩ := hmarg ρ hρ hA β hβpos hβ2 N hN
    rw [hπN]
    refine wl11_withDensity_le fun x => ?_
    refine (hsup x).2.trans ?_
    have hr1 : (1 + ‖x‖ ^ 2) ^ (-(β / (2 * (N : ℝ)))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖])
        (by have : 0 ≤ β / (2 * (N : ℝ)) := by positivity
            linarith)
    calc Cm * (1 + ‖x‖ ^ 2) ^ (-(β / (2 * (N : ℝ)))) ≤ Cm * 1 :=
          mul_le_mul_of_nonneg_left hr1 (by linarith)
      _ ≤ Cp := by rw [mul_one]; exact le_max_left _ _
  have hμle : HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ :=
    Measure.le_iff'.2 fun A => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 hCp1)
  refine ⟨?_, ?_⟩
  · obtain ⟨h1, h2⟩ := wl11_qvb_integrable hd A ρ hρ hA hμle hCp0 inferInstance hh.measurable hh.bound
    exact ⟨h1, h2, hvar _ (Or.inl rfl)⟩
  · obtain ⟨h1, h2⟩ := wl11_qvb_integrable hd A ρ hρ hA hπle hCp0 hπ hh.measurable hh.bound
    exact ⟨h1, h2, hvar _ (Or.inr rfl)⟩

end HRS.MS.Wl
