import HRS.MS.R2MtAux2

/-!
# HRS.MS.R2MtAux3 -- Step C of `round2_moment_transfer` (S9.2): second moment of `N F^k` under `μ^{⊗N}`, tail, main theorem

Packet S92, namespace `HRS.MS.R2Mt`, helper prefix `s92_`.

* `s92_ES`: Efron--Stein for `μ^{⊗N}` (Wu's inequality with `W ≡ 1`); `s92_var_D_le`, `s92_row_moment`, `s92_lin2`:
  variance of `D_N` through the rows `row_i` of `HRS.MS.Wr` and the second moment of an independent centred sum.
* `s92_second_moment`: `∫ |N F^k|² dμ^{⊗N} ≤ 100 ∫∫ k² dμ dμ` for symmetric measurable `k ∈ L²(μ⊗μ)` with integrable sections.
* `s92_tail_Q`, `s92_tail_key`, `s92_tail`: the tail `lim_j sup_N ‖N F^{h_j-h}‖_{L^r(P_N)} = 0` (plain and centred).
  Route (replaces the Marcinkiewicz--Zygmund/Rosenthal step of the brief, which is not needed): the `L²(μ^{⊗N})`
  bound above gives smallness in probability under `μ^{⊗N}`, transported to `Q` by `dQ/dμ^N ∈ L²(μ^{⊗N})`, and
  combined with the uniform moment bound of Step A (`s92_moment_Q`) for the kernel `h_j - h` (envelope `(C₁B+B)(1+W_s)`).
* `round2_moment_transfer_proof : type_of% @HRS.Whole.round2_moment_transfer` (statement unchanged); tie in
  `HRS/MS/R2Tie.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Mt

open HRS.Whole HRS.MS.Wr HRS.External

variable {d N : ℕ}

/-! ### Efron--Stein for the product measure -/

theorem s92_ES {E : Type*} [MeasurableSpace E] {n : ℕ} (μ : Measure E) [IsProbabilityMeasure μ]
    (F : (Fin n → E) → ℝ) (hF : Measurable F) :
    evariance F (Measure.pi fun _ : Fin n => μ) ≤
      ∑ i, ∫⁻ x, evariance (fun z => F (update x i z)) μ ∂(Measure.pi fun _ : Fin n => μ) := by
  have hW : Measurable (fun _ : Fin n → E => (1 : ℝ≥0∞)) := measurable_const
  have hsite : ∀ i x, siteKernel μ (fun _ : Fin n → E => (1 : ℝ≥0∞)) i x = μ := by
    intro i x
    rw [siteKernel_apply hW]
    simp [normalizer]
  have h := wu_resampling μ (fun _ : Fin n → E => (1 : ℝ≥0∞)) hW (fun _ => one_pos) 1
    (fun _ => by simp) (by simp) (fun _ _ => 0) (fun _ _ => le_rfl)
    (fun i j _ x y _ A _ => by simp [hsite]) 0 (fun i => by simp) F hF
  simpa [hsite] using h

theorem s92_pairEnergy_eq (k : Euc d → Euc d → ℝ) (X : EucConfig d N) (μ : Measure (Euc d)) :
    HRS.Whole.pairEnergy k X μ = (1 / 2) * centeredPairFunctional k X μ := by
  unfold HRS.Whole.pairEnergy centeredPairFunctional
  ring

/-- Variance of `D_N` by the rows: `Var D_N ≤ ∑_i E‖(2/N²) row_i‖²`. -/
theorem s92_var_D_le {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {k : Euc d → Euc d → ℝ}
    (hm : Measurable (Function.uncurry k)) (hsym : ∀ x y, k x y = k y x) (hN : 0 < N) :
    evariance (fun X : EucConfig d N => centeredPairFunctional k X μ) (Measure.pi fun _ : Fin N => μ) ≤
      ∑ i : Fin N, ∫⁻ X, ‖(2 / (N : ℝ) ^ 2) * wr14a_row k μ i X‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ) := by
  refine (s92_ES μ _ (wr14a_measurable_D hm μ)).trans (Finset.sum_le_sum fun i _ => ?_)
  have hrowm : Measurable (fun X : EucConfig d N => ‖(2 / (N : ℝ) ^ 2) * wr14a_row k μ i X‖ₑ ^ 2) :=
    ((measurable_enorm.comp ((wr14a_measurable_row hm μ i).const_mul _))).pow_const 2
  calc ∫⁻ x, evariance (fun z => centeredPairFunctional k (update x i z) μ) μ ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ∫⁻ x, ∫⁻ z, ‖(2 / (N : ℝ) ^ 2) * wr14a_row k μ i (update x i z)‖ₑ ^ 2 ∂μ
          ∂(Measure.pi fun _ : Fin N => μ) := by
        refine lintegral_mono fun x => ?_
        refine (evariance_le_lintegral_sub μ ((wr14a_measurable_D hm μ).comp
          (measurable_update x)).aestronglyMeasurable (wr14a_rest k μ i x)).trans (le_of_eq ?_)
        refine lintegral_congr fun z => ?_
        congr 2
        change centeredPairFunctional k (update x i z) μ - wr14a_rest k μ i x = _
        rw [wr14a_D_eq_row_add_rest hsym μ hN i (update x i z), wr14a_rest_update]
        ring
    _ = ∫⁻ X, ‖(2 / (N : ℝ) ^ 2) * wr14a_row k μ i X‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ) :=
        (lintegral_pi_update μ i hrowm).symm

/-! ### Second moment of an independent centred sum -/

theorem s92_lintegral_sq_eq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 2 ν) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, f x ^ 2 ∂ν) := by
  have hint : Integrable (fun x => f x ^ 2) ν := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem s92_lin2 {E : Type*} [MeasurableSpace E] {n : ℕ} (μ : Measure E) [IsProbabilityMeasure μ]
    {φ : E → ℝ} (hφ : Measurable φ) (h0 : ∫ y, φ y ∂μ = 0) (S : Finset (Fin n)) :
    ∫⁻ x : Fin n → E, ‖∑ j ∈ S, φ (x j)‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin n => μ) ≤
      (S.card : ℝ≥0∞) * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  by_cases htop : ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ = ⊤
  · rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    · rw [htop]
      have : (S.card : ℝ≥0∞) ≠ 0 := by simp [hne.card_pos.ne']
      rw [ENNReal.mul_top this]; exact le_top
  · have hmem : MemLp φ 2 μ := memLp_two_of_lintegral_lt_top μ hφ.aestronglyMeasurable (lt_top_iff_ne_top.2 htop)
    set π : Measure (Fin n → E) := Measure.pi fun _ : Fin n => μ with hπ
    set X : Fin n → (Fin n → E) → ℝ := fun j x => φ (x j) with hXdef
    have hX : ∀ j, MemLp (X j) 2 π := fun j =>
      hmem.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) j)
    have hind : iIndepFun (fun (j : Fin n) (x : Fin n → E) => x j) π :=
      iIndepFun_pi (fun _ => aemeasurable_id)
    have hindφ : iIndepFun X π := hind.comp (fun _ => φ) (fun _ => hφ)
    have hvar := IndepFun.variance_sum (s := S) (fun j _ => hX j) (fun i _ j _ hij => hindφ.indepFun hij)
    have hmean : ∀ j, ∫ x, X j x ∂π = 0 := fun j => by
      simp only [hXdef]
      rw [hπ, integral_comp_eval hφ.aestronglyMeasurable, h0]
    have hmeanSq : ∀ j, ∫ x, (X j x) ^ 2 ∂π = ∫ y, φ y ^ 2 ∂μ := fun j => by
      simp only [hXdef]
      have := integral_comp_eval (μ := fun _ : Fin n => μ) (i := j) (f := fun y => φ y ^ 2)
        (hφ.pow_const 2).aestronglyMeasurable
      simpa using this
    have hT : MemLp (∑ j ∈ S, X j) 2 π := memLp_finsetSum' S (fun j _ => hX j)
    have hTmean : ∫ x, (∑ j ∈ S, X j) x ∂π = 0 := by
      have : (∑ j ∈ S, X j) = fun x => ∑ j ∈ S, X j x := by
        funext x; simp [Finset.sum_apply]
      rw [this, integral_finsetSum _ (fun j _ => (hX j).integrable one_le_two)]
      exact Finset.sum_eq_zero fun j _ => hmean j
    have h1 : variance (∑ j ∈ S, X j) π = ∫ x, ((∑ j ∈ S, X j) x) ^ 2 ∂π := by
      rw [variance_of_integral_eq_zero hT.aestronglyMeasurable.aemeasurable hTmean]
    have h2 : ∀ j, variance (X j) π = ∫ y, φ y ^ 2 ∂μ := fun j => by
      rw [variance_of_integral_eq_zero (hX j).aestronglyMeasurable.aemeasurable (hmean j), hmeanSq j]
    have hsum : ∫ x, ((∑ j ∈ S, X j) x) ^ 2 ∂π = S.card * ∫ y, φ y ^ 2 ∂μ := by
      rw [← h1, hvar]
      simp [h2]
    have e1 : ∫⁻ x, ‖∑ j ∈ S, φ (x j)‖ₑ ^ 2 ∂π = ENNReal.ofReal (∫ x, ((∑ j ∈ S, X j) x) ^ 2 ∂π) := by
      rw [← s92_lintegral_sq_eq hT]
      refine lintegral_congr fun x => ?_
      simp [hXdef, Finset.sum_apply]
    rw [e1, hsum, s92_lintegral_sq_eq hmem, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp

/-! ### Second moment of a row -/

theorem s92_enorm_sq (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem s92_enorm_sq_add_le (a b : ℝ) : ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  rw [s92_enorm_sq, s92_enorm_sq, s92_enorm_sq]
  have h : ENNReal.ofReal (2 * a ^ 2 + 2 * b ^ 2) = 2 * ENNReal.ofReal (a ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [← h]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a - b)])

theorem s92_enorm_sq_sub_le (a b : ℝ) : ‖a - b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have := s92_enorm_sq_add_le a (-b)
  simpa [sub_eq_add_neg] using this

theorem s92_cK_measurable {μ : Measure (Euc d)} [SFinite μ] {k : Euc d → Euc d → ℝ}
    (hm : Measurable (Function.uncurry k)) : Measurable (Function.uncurry (wr14a_cK k μ)) := by
  have hH := wr14a_measurable_Hc hm μ
  unfold wr14a_cK
  exact ((hm.sub (hH.comp measurable_fst)).sub (hH.comp measurable_snd)).add_const _

theorem s92_integral_cK {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {k : Euc d → Euc d → ℝ}
    (hsec : ∀ x, Integrable (k x) μ) (hHint : Integrable (wr14a_Hc k μ) μ) (w : Euc d) :
    ∫ y, wr14a_cK k μ w y ∂μ = 0 := by
  unfold wr14a_cK
  have h2 : Integrable (fun y => k w y - wr14a_Hc k μ w) μ := (hsec w).sub (integrable_const _)
  have h1 : Integrable (fun y => k w y - wr14a_Hc k μ w - wr14a_Hc k μ y) μ := h2.sub hHint
  rw [integral_add h1 (integrable_const _), integral_sub h2 hHint,
    integral_sub (hsec w) (integrable_const _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have : ∫ y, wr14a_Hc k μ y ∂μ = wr14a_h0 k μ := rfl
  rw [this]
  unfold wr14a_Hc
  ring

theorem s92_row_moment {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {k : Euc d → Euc d → ℝ}
    (hm : Measurable (Function.uncurry k)) (hsec : ∀ x, Integrable (k x) μ)
    (hHint : Integrable (wr14a_Hc k μ) μ) (i : Fin N) :
    ∫⁻ X, ‖wr14a_row k μ i X‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ) ≤
      2 * ((N - 1 : ℕ) : ℝ≥0∞) * ∫⁻ w, ∫⁻ y, ‖wr14a_cK k μ w y‖ₑ ^ 2 ∂μ ∂μ +
        2 * ∫⁻ w, ‖wr14a_Hc k μ w‖ₑ ^ 2 ∂μ := by
  have hHm := wr14a_measurable_Hc hm μ
  have hcm := s92_cK_measurable (μ := μ) hm
  have hrowm : Measurable (fun X : EucConfig d N => ‖wr14a_row k μ i X‖ₑ ^ 2) :=
    (measurable_enorm.comp (wr14a_measurable_row hm μ i)).pow_const 2
  rw [lintegral_pi_update μ i hrowm]
  have hupd : ∀ (x : EucConfig d N) (w : Euc d), wr14a_row k μ i (update x i w) =
      ∑ j ∈ Finset.univ.erase i, wr14a_cK k μ w (x j) - wr14a_Hc k μ w := by
    intro x w
    unfold wr14a_row
    rw [update_self]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  simp_rw [hupd]
  have hjm : Measurable (Function.uncurry fun (x : EucConfig d N) (w : Euc d) =>
      ‖∑ j ∈ Finset.univ.erase i, wr14a_cK k μ w (x j) - wr14a_Hc k μ w‖ₑ ^ 2) := by
    refine (measurable_enorm.comp ?_).pow_const 2
    refine (Finset.measurable_sum _ fun j _ => ?_).sub (hHm.comp measurable_snd)
    exact hcm.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  rw [lintegral_lintegral_swap hjm.aemeasurable]
  have hpt : ∀ w, ∫⁻ x, ‖∑ j ∈ Finset.univ.erase i, wr14a_cK k μ w (x j) - wr14a_Hc k μ w‖ₑ ^ 2
        ∂(Measure.pi fun _ : Fin N => μ) ≤
      2 * (((N - 1 : ℕ) : ℝ≥0∞) * ∫⁻ y, ‖wr14a_cK k μ w y‖ₑ ^ 2 ∂μ) + 2 * ‖wr14a_Hc k μ w‖ₑ ^ 2 := by
    intro w
    have hcard : ((Finset.univ.erase i).card : ℝ≥0∞) = ((N - 1 : ℕ) : ℝ≥0∞) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
    have hlin := s92_lin2 μ (φ := wr14a_cK k μ w) (hcm.comp (measurable_const.prodMk measurable_id))
      (s92_integral_cK hsec hHint w) (Finset.univ.erase i)
    rw [hcard] at hlin
    calc ∫⁻ x, ‖∑ j ∈ Finset.univ.erase i, wr14a_cK k μ w (x j) - wr14a_Hc k μ w‖ₑ ^ 2
          ∂(Measure.pi fun _ : Fin N => μ)
        ≤ ∫⁻ x, (2 * ‖∑ j ∈ Finset.univ.erase i, wr14a_cK k μ w (x j)‖ₑ ^ 2 + 2 * ‖wr14a_Hc k μ w‖ₑ ^ 2)
          ∂(Measure.pi fun _ : Fin N => μ) := lintegral_mono fun x => s92_enorm_sq_sub_le _ _
      _ = 2 * ∫⁻ x, ‖∑ j ∈ Finset.univ.erase i, wr14a_cK k μ w (x j)‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ)
          + 2 * ‖wr14a_Hc k μ w‖ₑ ^ 2 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num), lintegral_const,
          measure_univ, mul_one]
      _ ≤ _ := by gcongr
  calc ∫⁻ w, ∫⁻ x, ‖∑ j ∈ Finset.univ.erase i, wr14a_cK k μ w (x j) - wr14a_Hc k μ w‖ₑ ^ 2
        ∂(Measure.pi fun _ : Fin N => μ) ∂μ
      ≤ ∫⁻ w, (2 * (((N - 1 : ℕ) : ℝ≥0∞) * ∫⁻ y, ‖wr14a_cK k μ w y‖ₑ ^ 2 ∂μ) + 2 * ‖wr14a_Hc k μ w‖ₑ ^ 2) ∂μ :=
        lintegral_mono hpt
    _ = _ := by
        have hm1 : Measurable (fun w => ‖wr14a_Hc k μ w‖ₑ ^ 2) := (measurable_enorm.comp hHm).pow_const 2
        have hm2 : Measurable (fun w => ∫⁻ y, ‖wr14a_cK k μ w y‖ₑ ^ 2 ∂μ) :=
          ((measurable_enorm.comp hcm).pow_const 2).lintegral_prod_right'
        rw [lintegral_add_right _ (hm1.const_mul _), lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul _ hm2, lintegral_const_mul _ hm1]
        ring

/-! ### Norm comparisons -/

/-- Jensen for a probability measure: `‖∫ f‖² ≤ ∫ ‖f‖²`. -/
theorem s92_enorm_integral_sq_le {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : Measurable f) : ‖∫ x, f x ∂ν‖ₑ ^ 2 ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  have h1 : ‖∫ x, f x ∂ν‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
  have h2 : ∫⁻ x, ‖f x‖ₑ ∂ν ≤ (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
      (measurable_enorm.comp hf).aemeasurable (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
    simpa using this
  calc ‖∫ x, f x ∂ν‖ₑ ^ 2 ≤ (∫⁻ x, ‖f x‖ₑ ∂ν) ^ 2 := pow_le_pow_left' h1 2
    _ ≤ ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))) ^ 2 := pow_le_pow_left' h2 2
    _ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        simp only [ENNReal.rpow_two]
        norm_num

section Norms

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {k : Euc d → Euc d → ℝ}

theorem s92_SH_le (hm : Measurable (Function.uncurry k)) :
    ∫⁻ w, ‖wr14a_Hc k μ w‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ :=
  lintegral_mono fun x => s92_enorm_integral_sq_le μ (k x) (wr14a_measurable_h_x hm x)

theorem s92_h0_sq_le (hm : Measurable (Function.uncurry k)) :
    ‖wr14a_h0 k μ‖ₑ ^ 2 ≤ ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ :=
  (s92_enorm_integral_sq_le μ (wr14a_Hc k μ) (wr14a_measurable_Hc hm μ)).trans (s92_SH_le hm)

theorem s92_Scc_le (hm : Measurable (Function.uncurry k)) :
    ∫⁻ w, ∫⁻ y, ‖wr14a_cK k μ w y‖ₑ ^ 2 ∂μ ∂μ ≤ 16 * ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ := by
  have hHm := wr14a_measurable_Hc hm μ
  set S2 := ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ with hS2
  set SH := ∫⁻ w, ‖wr14a_Hc k μ w‖ₑ ^ 2 ∂μ with hSH
  have hSH := s92_SH_le (μ := μ) hm
  have hh0 := s92_h0_sq_le (μ := μ) hm
  have hpt : ∀ w y, ‖wr14a_cK k μ w y‖ₑ ^ 2 ≤ 4 * ‖k w y‖ₑ ^ 2 + 4 * ‖wr14a_Hc k μ w‖ₑ ^ 2 +
      4 * ‖wr14a_Hc k μ y‖ₑ ^ 2 + 4 * ‖wr14a_h0 k μ‖ₑ ^ 2 := by
    intro w y
    unfold wr14a_cK
    have e : k w y - wr14a_Hc k μ w - wr14a_Hc k μ y + wr14a_h0 k μ =
        (k w y + -wr14a_Hc k μ w) + (-wr14a_Hc k μ y + wr14a_h0 k μ) := by ring
    rw [e]
    refine (s92_enorm_sq_add_le _ _).trans ?_
    have h1 := s92_enorm_sq_add_le (k w y) (-wr14a_Hc k μ w)
    have h2 := s92_enorm_sq_add_le (-wr14a_Hc k μ y) (wr14a_h0 k μ)
    have en : ∀ a : ℝ, ‖-a‖ₑ = ‖a‖ₑ := fun a => by rw [← ofReal_norm, ← ofReal_norm, norm_neg]
    rw [en] at h1
    rw [en] at h2
    calc 2 * ‖k w y + -wr14a_Hc k μ w‖ₑ ^ 2 + 2 * ‖-wr14a_Hc k μ y + wr14a_h0 k μ‖ₑ ^ 2
        ≤ 2 * (2 * ‖k w y‖ₑ ^ 2 + 2 * ‖wr14a_Hc k μ w‖ₑ ^ 2) +
          2 * (2 * ‖wr14a_Hc k μ y‖ₑ ^ 2 + 2 * ‖wr14a_h0 k μ‖ₑ ^ 2) := by gcongr
      _ = _ := by ring
  have hm1 : Measurable (fun w => ‖wr14a_Hc k μ w‖ₑ ^ 2) := (measurable_enorm.comp hHm).pow_const 2
  have hkm : ∀ w, Measurable (fun y => ‖k w y‖ₑ ^ 2) := fun w =>
    (measurable_enorm.comp (wr14a_measurable_h_x hm w)).pow_const 2
  calc ∫⁻ w, ∫⁻ y, ‖wr14a_cK k μ w y‖ₑ ^ 2 ∂μ ∂μ
      ≤ ∫⁻ w, ∫⁻ y, (4 * ‖k w y‖ₑ ^ 2 + 4 * ‖wr14a_Hc k μ w‖ₑ ^ 2 +
          4 * ‖wr14a_Hc k μ y‖ₑ ^ 2 + 4 * ‖wr14a_h0 k μ‖ₑ ^ 2) ∂μ ∂μ :=
        lintegral_mono fun w => lintegral_mono fun y => hpt w y
    _ = ∫⁻ w, (4 * ∫⁻ y, ‖k w y‖ₑ ^ 2 ∂μ + 4 * ‖wr14a_Hc k μ w‖ₑ ^ 2 + 4 * SH + 4 * ‖wr14a_h0 k μ‖ₑ ^ 2) ∂μ := by
        refine lintegral_congr fun w => ?_
        have m1 : Measurable (fun y => 4 * ‖k w y‖ₑ ^ 2) := (hkm w).const_mul 4
        have m2 : Measurable (fun y => 4 * ‖wr14a_Hc k μ y‖ₑ ^ 2) := hm1.const_mul 4
        rw [lintegral_add_right _ measurable_const, lintegral_add_right _ m2,
          lintegral_add_right _ measurable_const, lintegral_const_mul _ (hkm w), lintegral_const,
          lintegral_const_mul _ hm1, lintegral_const, measure_univ]
        simp only [mul_one]
        rfl
    _ ≤ 16 * S2 := by
        have hS : Measurable (fun w => ∫⁻ y, ‖k w y‖ₑ ^ 2 ∂μ) :=
          ((measurable_enorm.comp hm).pow_const 2).lintegral_prod_right'
        have m1 : Measurable (fun w => 4 * ∫⁻ y, ‖k w y‖ₑ ^ 2 ∂μ) := hS.const_mul 4
        have m2 : Measurable (fun w => 4 * ‖wr14a_Hc k μ w‖ₑ ^ 2) := hm1.const_mul 4
        rw [lintegral_add_right _ measurable_const, lintegral_add_right _ measurable_const,
          lintegral_add_right _ m2, lintegral_const_mul _ hS,
          lintegral_const, lintegral_const, lintegral_const_mul _ hm1, measure_univ]
        simp only [mul_one]
        calc 4 * S2 + 4 * SH + 4 * SH + 4 * ‖wr14a_h0 k μ‖ₑ ^ 2 ≤ 4 * S2 + 4 * S2 + 4 * S2 + 4 * S2 := by
              gcongr
          _ = 16 * S2 := by ring

end Norms

/-! ### The mean of `D_N` under `μ^{⊗N}` -/

theorem s92_pair_law {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {i j : Fin N} (hij : i ≠ j) :
    (Measure.pi fun _ : Fin N => μ).map (fun X : EucConfig d N => (X i, X j)) = μ.prod μ := by
  have hind : iIndepFun (fun (j : Fin N) (x : EucConfig d N) => x j) (Measure.pi fun _ : Fin N => μ) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h := (indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 (hind.indepFun hij)
  rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) j).map_eq] at h
  exact h

theorem s92_integral_pair {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {k : Euc d → Euc d → ℝ}
    (hm : Measurable (Function.uncurry k)) (hint : Integrable (Function.uncurry k) (μ.prod μ))
    {i j : Fin N} (hij : i ≠ j) :
    Integrable (fun X : EucConfig d N => k (X i) (X j)) (Measure.pi fun _ : Fin N => μ) ∧
      ∫ X : EucConfig d N, k (X i) (X j) ∂(Measure.pi fun _ : Fin N => μ) = wr14a_h0 k μ := by
  have hlaw := s92_pair_law (μ := μ) hij
  have hmeas : AEMeasurable (fun X : EucConfig d N => (X i, X j)) (Measure.pi fun _ : Fin N => μ) :=
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
  have hint' : Integrable (Function.uncurry k)
      ((Measure.pi fun _ : Fin N => μ).map (fun X : EucConfig d N => (X i, X j))) := by
    rw [hlaw]; exact hint
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable hmeas).1 hint', ?_⟩
  have h := integral_map hmeas (φ := fun X : EucConfig d N => (X i, X j)) (f := Function.uncurry k)
    (μ := Measure.pi fun _ : Fin N => μ) hm.aestronglyMeasurable
  rw [hlaw, integral_prod _ hint] at h
  exact h.symm

theorem s92_integral_D {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {k : Euc d → Euc d → ℝ}
    (hm : Measurable (Function.uncurry k)) (hint : Integrable (Function.uncurry k) (μ.prod μ))
    (hHint : Integrable (wr14a_Hc k μ) μ) (hN : 0 < N) :
    ∫ X : EucConfig d N, centeredPairFunctional k X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -wr14a_h0 k μ / N := by
  set π : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hπ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hI1 : ∀ i j : Fin N, j ∈ Finset.univ.erase i → Integrable (fun X : EucConfig d N => k (X i) (X j)) π :=
    fun i j hj => (s92_integral_pair hm hint (Finset.ne_of_mem_erase hj).symm).1
  have hI2 : ∀ i : Fin N, Integrable (fun X : EucConfig d N => ∫ y, k (X i) y ∂μ) π := fun i =>
    (measurePreserving_eval (fun _ : Fin N => μ) i).integrable_comp_of_integrable hHint
  have hint1 : Integrable (fun X : EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)) π :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj => hI1 i j hj
  have hint2 : Integrable (fun X : EucConfig d N => ∑ i, ∫ y, k (X i) y ∂μ) π :=
    integrable_finsetSum _ fun i _ => hI2 i
  have hm1 : ∫ X, ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j) ∂π = (N : ℝ) * ((N : ℝ) - 1) * wr14a_h0 k μ := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j hj => hI1 i j hj)]
    have : ∀ i : Fin N, ∫ X, ∑ j ∈ Finset.univ.erase i, k (X i) (X j) ∂π = ((N : ℝ) - 1) * wr14a_h0 k μ := by
      intro i
      rw [integral_finsetSum _ (fun j hj => hI1 i j hj)]
      rw [Finset.sum_congr rfl (fun j hj => (s92_integral_pair hm hint (Finset.ne_of_mem_erase hj).symm).2)]
      simp [Finset.card_erase_of_mem, Nat.cast_sub hN]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
    ring
  have hm2 : ∫ X, ∑ i, ∫ y, k (X i) y ∂μ ∂π = (N : ℝ) * wr14a_h0 k μ := by
    rw [integral_finsetSum _ (fun i _ => hI2 i)]
    have : ∀ i : Fin N, ∫ X, ∫ y, k (X i) y ∂μ ∂π = wr14a_h0 k μ := by
      intro i
      have := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) (f := wr14a_Hc k μ)
        (wr14a_measurable_Hc hm μ).aestronglyMeasurable
      exact this
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
  unfold centeredPairFunctional
  have hA : Integrable (fun X : EucConfig d N => 1 / (N : ℝ) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)) π :=
    hint1.const_mul _
  have hB : Integrable (fun X : EucConfig d N => 2 * (1 / (N : ℝ) * ∑ i, ∫ y, k (X i) y ∂μ)) π :=
    (hint2.const_mul _).const_mul _
  have hAB : Integrable (fun X : EucConfig d N => 1 / (N : ℝ) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j) -
      2 * (1 / (N : ℝ) * ∑ i, ∫ y, k (X i) y ∂μ)) π := hA.sub hB
  rw [integral_add hAB (integrable_const _), integral_sub hA hB, integral_const_mul,
    integral_const_mul, integral_const_mul, hm1, hm2]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have : ∫ x, ∫ y, k x y ∂μ ∂μ = wr14a_h0 k μ := rfl
  rw [this]
  field_simp
  ring

/-! ### The second moment bound -/

theorem s92_enorm_mul_sq (c r : ℝ) : ‖c * r‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ‖r‖ₑ ^ 2 := by
  rw [s92_enorm_sq, s92_enorm_sq, ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1; ring

section Var

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {k : Euc d → Euc d → ℝ}

theorem s92_row_le (hm : Measurable (Function.uncurry k)) (hsec : ∀ x, Integrable (k x) μ)
    (hHint : Integrable (wr14a_Hc k μ) μ) (hN : 0 < N) (i : Fin N) :
    ∫⁻ X, ‖wr14a_row k μ i X‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (34 * N) * ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ := by
  set S2 := ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ with hS2
  have h1 := s92_row_moment (N := N) hm hsec hHint i
  have h2 := s92_Scc_le (μ := μ) hm
  have h3 := s92_SH_le (μ := μ) hm
  have hcast : ((N - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((N : ℝ) - 1) := by
    rw [← ENNReal.ofReal_natCast, Nat.cast_sub (by omega)]; simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc _ ≤ 2 * ((N - 1 : ℕ) : ℝ≥0∞) * (16 * S2) + 2 * S2 := h1.trans (add_le_add (by gcongr) (by gcongr))
    _ = ENNReal.ofReal (32 * ((N : ℝ) - 1) + 2) * S2 := by
        have e : ENNReal.ofReal (32 * ((N : ℝ) - 1) + 2) = 32 * ENNReal.ofReal ((N : ℝ) - 1) + 2 := by
          rw [ENNReal.ofReal_add (by linarith) (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          simp
        rw [hcast, e]
        ring
    _ ≤ ENNReal.ofReal (34 * N) * S2 := by
        gcongr
        linarith

theorem s92_var_D_bound (hm : Measurable (Function.uncurry k)) (hsym : ∀ x y, k x y = k y x)
    (hsec : ∀ x, Integrable (k x) μ) (hHint : Integrable (wr14a_Hc k μ) μ) (hN : 0 < N) :
    evariance (fun X : EucConfig d N => centeredPairFunctional k X μ) (Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (136 / (N : ℝ) ^ 2) * ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ := by
  set S2 := ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ with hS2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine (s92_var_D_le hm hsym hN).trans ?_
  calc ∑ i : Fin N, ∫⁻ X, ‖(2 / (N : ℝ) ^ 2) * wr14a_row k μ i X‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ)
      = ∑ i : Fin N, ENNReal.ofReal ((2 / (N : ℝ) ^ 2) ^ 2) *
          ∫⁻ X, ‖wr14a_row k μ i X‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp_rw [s92_enorm_mul_sq]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∑ _i : Fin N, ENNReal.ofReal ((2 / (N : ℝ) ^ 2) ^ 2) * (ENNReal.ofReal (34 * N) * S2) :=
        Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (s92_row_le hm hsec hHint hN i)
    _ = ENNReal.ofReal (136 / (N : ℝ) ^ 2) * S2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
        ring

/-- **Second moment of `N F^k` under `μ^{⊗N}`**: `∫ (N F^k)² dμ^{⊗N} ≤ 100 ‖k‖²_{L²(μ⊗μ)}`. -/
theorem s92_second_moment (hm : Measurable (Function.uncurry k)) (hsym : ∀ x y, k x y = k y x)
    (hsec : ∀ x, Integrable (k x) μ) (hint : Integrable (Function.uncurry k) (μ.prod μ))
    (hHint : Integrable (wr14a_Hc k μ) μ) (hN : 0 < N) :
    ∫⁻ X : EucConfig d N, ‖(N : ℝ) * HRS.Whole.pairEnergy k X μ‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ) ≤
      100 * ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ := by
  set S2 := ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ with hS2
  set π : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hπ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hvar := s92_var_D_bound hm hsym hsec hHint hN
  have hmean := s92_integral_D hm hint hHint hN
  have hh0 := s92_h0_sq_le (μ := μ) hm
  have hDm : Measurable (fun X : EucConfig d N => centeredPairFunctional k X μ) := wr14a_measurable_D hm μ
  have e1 : ∀ X : EucConfig d N, ‖(N : ℝ) * HRS.Whole.pairEnergy k X μ‖ₑ ^ 2 =
      ENNReal.ofReal (((N : ℝ) / 2) ^ 2) * ‖centeredPairFunctional k X μ‖ₑ ^ 2 := by
    intro X
    rw [← s92_enorm_mul_sq, s92_pairEnergy_eq]
    congr 2; ring
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  set m : ℝ := -wr14a_h0 k μ / N with hm_def
  have hevar : evariance (fun X : EucConfig d N => centeredPairFunctional k X μ) π =
      ∫⁻ X, ‖centeredPairFunctional k X μ - m‖ₑ ^ 2 ∂π := by
    unfold evariance
    rw [hmean]
  have hD2 : ∫⁻ X, ‖centeredPairFunctional k X μ‖ₑ ^ 2 ∂π ≤
      2 * evariance (fun X : EucConfig d N => centeredPairFunctional k X μ) π + 2 * ‖m‖ₑ ^ 2 := by
    have hpt : ∀ X : EucConfig d N, ‖centeredPairFunctional k X μ‖ₑ ^ 2 ≤
        2 * ‖centeredPairFunctional k X μ - m‖ₑ ^ 2 + 2 * ‖m‖ₑ ^ 2 := by
      intro X
      have := s92_enorm_sq_add_le (centeredPairFunctional k X μ - m) m
      rwa [sub_add_cancel] at this
    calc ∫⁻ X, ‖centeredPairFunctional k X μ‖ₑ ^ 2 ∂π
        ≤ ∫⁻ X, (2 * ‖centeredPairFunctional k X μ - m‖ₑ ^ 2 + 2 * ‖m‖ₑ ^ 2) ∂π := lintegral_mono hpt
      _ = 2 * ∫⁻ X, ‖centeredPairFunctional k X μ - m‖ₑ ^ 2 ∂π + 2 * ‖m‖ₑ ^ 2 := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num), lintegral_const,
            measure_univ, mul_one]
      _ = _ := by rw [hevar]
  have hm2 : ‖m‖ₑ ^ 2 ≤ ENNReal.ofReal (1 / (N : ℝ) ^ 2) * S2 := by
    have : m = (-1 / (N : ℝ)) * wr14a_h0 k μ := by rw [hm_def]; ring
    rw [this, s92_enorm_mul_sq]
    have e : (-1 / (N : ℝ)) ^ 2 = 1 / (N : ℝ) ^ 2 := by rw [div_pow]; norm_num
    rw [e]
    exact mul_le_mul' le_rfl hh0
  have hfinal : ENNReal.ofReal (((N : ℝ) / 2) ^ 2) *
      (2 * (ENNReal.ofReal (136 / (N : ℝ) ^ 2) * S2) + 2 * (ENNReal.ofReal (1 / (N : ℝ) ^ 2) * S2)) =
      ENNReal.ofReal (137 / 2) * S2 := by
    have e : ((N : ℝ) / 2) ^ 2 * (2 * (136 / (N : ℝ) ^ 2) + 2 * (1 / (N : ℝ) ^ 2)) = 137 / 2 := by
      field_simp; ring
    have hl : ENNReal.ofReal (137 / 2) = ENNReal.ofReal (((N : ℝ) / 2) ^ 2) *
        (2 * ENNReal.ofReal (136 / (N : ℝ) ^ 2) + 2 * ENNReal.ofReal (1 / (N : ℝ) ^ 2)) := by
      rw [← e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
      simp
    rw [hl]
    ring
  calc ENNReal.ofReal (((N : ℝ) / 2) ^ 2) * ∫⁻ X, ‖centeredPairFunctional k X μ‖ₑ ^ 2 ∂π
      ≤ ENNReal.ofReal (((N : ℝ) / 2) ^ 2) *
          (2 * (ENNReal.ofReal (136 / (N : ℝ) ^ 2) * S2) + 2 * (ENNReal.ofReal (1 / (N : ℝ) ^ 2) * S2)) :=
        mul_le_mul' le_rfl (hD2.trans (add_le_add (mul_le_mul' le_rfl hvar) (mul_le_mul' le_rfl hm2)))
    _ = ENNReal.ofReal (137 / 2) * S2 := hfinal
    _ ≤ 100 * S2 := by
        gcongr
        rw [show (100 : ℝ≥0∞) = ENNReal.ofReal 100 by simp]
        exact ENNReal.ofReal_le_ofReal (by norm_num)

end Var

/-! ### The tail at the level of `Q` -/

theorem s92_withDensity_set_le {α : Type*} [MeasurableSpace α] (ν : Measure α) {ψ : α → ℝ≥0∞}
    (hψ : Measurable ψ) {A : Set α} (hA : MeasurableSet A) :
    (ν.withDensity ψ) A ≤ (∫⁻ x, ψ x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) * (ν A) ^ (1 / (2 : ℝ)) := by
  rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  have hind : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hψ.aemeasurable hind.aemeasurable
  have e1 : ∫⁻ x, A.indicator ψ x ∂ν = ∫⁻ x, (ψ * A.indicator (fun _ => (1 : ℝ≥0∞))) x ∂ν := by
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A <;> simp [hx]
  have e2 : ∫⁻ x, (A.indicator (fun _ => (1 : ℝ≥0∞)) x) ^ (2 : ℝ) ∂ν = ν A := by
    have : ∀ x, (A.indicator (fun _ => (1 : ℝ≥0∞)) x) ^ (2 : ℝ) = A.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      intro x; by_cases hx : x ∈ A <;> simp [hx]
    simp_rw [this]
    rw [lintegral_indicator_const hA, one_mul]
  rw [e1]
  rw [e2] at h
  exact h

theorem s92_tail_Q {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν] {ψ : α → ℝ≥0∞}
    (hψ : Measurable ψ) [IsProbabilityMeasure (ν.withDensity ψ)] {X : α → ℝ} (hX : Measurable X) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) {C2 Aψ : ℝ} (hC2 : ∫⁻ x, ‖X x‖ₑ ^ (2 * m) ∂(ν.withDensity ψ) ≤ ENNReal.ofReal C2)
    (hA : (∫⁻ x, ψ x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal Aψ) {s : ℝ≥0∞}
    (hs : ∫⁻ x, ‖X x‖ₑ ^ 2 ∂ν ≤ s) :
    ∫⁻ x, ‖X x‖ₑ ^ m ∂(ν.withDensity ψ) ≤ ENNReal.ofReal ε ^ m +
      (ENNReal.ofReal C2) ^ (1 / (2 : ℝ)) *
        (ENNReal.ofReal Aψ * (ENNReal.ofReal (ε ^ (-2 : ℤ)) * s) ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) := by
  refine (s92_tail_split (ν.withDensity ψ) hX m).trans (add_le_add le_rfl ?_)
  have hAm : MeasurableSet {x | ε < |X x|} := measurableSet_lt measurable_const hX.abs
  have hνA : ν {x | ε < |X x|} ≤ ENNReal.ofReal (ε ^ (-2 : ℤ)) * s := by
    have hsub : {x | ε < |X x|} ⊆ {x | ENNReal.ofReal (ε ^ 2) ≤ ‖X x‖ₑ ^ 2} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [s92_enorm_sq]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [abs_nonneg (X x), sq_abs (X x)])
    have hmk := meas_ge_le_lintegral_div (μ := ν) ((measurable_enorm.comp hX).pow_const 2).aemeasurable
      (ε := ENNReal.ofReal (ε ^ 2)) (by simp [hε.ne']) ENNReal.ofReal_ne_top
    calc ν {x | ε < |X x|} ≤ ν {x | ENNReal.ofReal (ε ^ 2) ≤ ‖X x‖ₑ ^ 2} := measure_mono hsub
      _ ≤ (∫⁻ x, ‖X x‖ₑ ^ 2 ∂ν) / ENNReal.ofReal (ε ^ 2) := hmk
      _ ≤ s / ENNReal.ofReal (ε ^ 2) := by gcongr
      _ = ENNReal.ofReal (ε ^ (-2 : ℤ)) * s := by
          rw [div_eq_mul_inv, mul_comm, ← ENNReal.ofReal_inv_of_pos (by positivity)]
          congr 2
  have hQA : (ν.withDensity ψ) {x | ε < |X x|} ≤ ENNReal.ofReal Aψ *
      (ENNReal.ofReal (ε ^ (-2 : ℤ)) * s) ^ (1 / (2 : ℝ)) :=
    (s92_withDensity_set_le ν hψ hAm).trans (mul_le_mul' hA (ENNReal.rpow_le_rpow hνA (by norm_num)))
  exact mul_le_mul' (ENNReal.rpow_le_rpow hC2 (by norm_num)) (ENNReal.rpow_le_rpow hQA (by norm_num))

/-! ### The kernels `h_j - h` -/

section Kernel

variable {s : ℝ}

theorem s92_finiteRank_meas {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : IsR2FiniteRankData c u) : Measurable (Function.uncurry (r2FiniteRankKernel c u)) := by
  unfold r2FiniteRankKernel
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact (measurable_const.mul ((hu.smooth a).continuous.measurable.comp measurable_fst)).mul
    ((hu.smooth b).continuous.measurable.comp measurable_snd)

theorem s92_finiteRank_symm {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : IsR2FiniteRankData c u) (x y : Euc d) :
    r2FiniteRankKernel c u x y = r2FiniteRankKernel c u y x := by
  unfold r2FiniteRankKernel
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hu.symm b a]; ring

theorem s92_diff_kernel {B C₁ : ℝ} {μ : Measure (Euc d)} {h : Euc d → Euc d → ℝ}
    {hj : ℕ → Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) (ha : IsRound2Approx s C₁ B μ h hj) (j : ℕ) :
    IsBoundedPairKernel s (C₁ * B + B) (fun x y => hj j x y - h x y) where
  measurable := by
    obtain ⟨m, c, u, hu, e⟩ := ha.finiteRank j
    have h1 : Measurable (Function.uncurry (hj j)) := by
      rw [e]; exact s92_finiteRank_meas hu
    exact h1.sub hh.measurable
  symm := by
    obtain ⟨m, c, u, hu, e⟩ := ha.finiteRank j
    intro x y
    rw [e, s92_finiteRank_symm hu x y, hh.symm x y]
  bound := by
    intro x y hxy
    have h1 := ha.envelope j x y hxy
    have h2 := hh.bound x y hxy
    calc |hj j x y - h x y| ≤ |hj j x y| + |h x y| := abs_sub _ _
      _ ≤ C₁ * B * (1 + rieszWeight s (x - y)) + B * (1 + rieszWeight s (x - y)) := add_le_add h1 h2
      _ = (C₁ * B + B) * (1 + rieszWeight s (x - y)) := by ring

theorem s92_kernel_integrable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) {B : ℝ} {k : Euc d → Euc d → ℝ}
    (hk : IsBoundedPairKernel s B k) :
    (∀ x, Integrable (k x) (HRS.Whole.withDensityReal ρ)) ∧
      Integrable (Function.uncurry k) ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) ∧
      Integrable (wr14a_Hc k (HRS.Whole.withDensityReal ρ)) (HRS.Whole.withDensityReal ρ) := by
  haveI := s92_isProb_mu hρ
  have hB : 0 ≤ B := wr14a_nonneg_of_bound hd (s := s) hk.bound
  have hν : HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal 1 • HRS.Whole.withDensityReal ρ := by simp
  have h1 : ∀ x, Integrable (k x) (HRS.Whole.withDensityReal ρ) := fun x =>
    wr14a_integrable_of_env_bound hd hs0 hsd M hρ hM hν zero_le_one hB (wr14a_measurable_h_x hk.measurable x)
      (fun y hy => hk.bound x y (Ne.symm hy))
  have h2 : Integrable (Function.uncurry k)
      ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) :=
    wr14a_pair_integrable hd hs0 hsd M hρ hM hν zero_le_one inferInstance hB hk.measurable hk.bound
  exact ⟨h1, h2, h2.integral_prod_left⟩

end Kernel

theorem s92_S2_eq {μ : Measure (Euc d)} [SFinite μ] {f : Euc d → Euc d → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    ∫⁻ x, ∫⁻ y, ‖f x y‖ₑ ^ 2 ∂μ ∂μ =
      (eLpNorm (fun p : Euc d × Euc d => f p.1 p.2) (ENNReal.ofReal 2) (μ.prod μ)) ^ 2 := by
  have hm : Measurable (fun p : Euc d × Euc d => f p.1 p.2) := hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) ENNReal.ofReal_ne_top hm.aestronglyMeasurable]
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  exact (lintegral_prod (fun p : Euc d × Euc d => ‖f p.1 p.2‖ₑ ^ 2)
    ((measurable_enorm.comp hm).pow_const 2).aemeasurable).symm

theorem s92_G_tendsto {c1 c2 c3 : ℝ≥0∞} (h1 : c1 ≠ ⊤) (h2 : c2 ≠ ⊤) (h3 : c3 ≠ ⊤) {f : ℕ → ℝ≥0∞}
    (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun j => c1 * (c2 * (c3 * f j) ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
  have hc : Continuous fun x : ℝ≥0∞ => c1 * (c2 * (c3 * x) ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) :=
    (ENNReal.continuous_const_mul h1).comp
      (ENNReal.continuous_rpow_const.comp ((ENNReal.continuous_const_mul h2).comp
        (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_const_mul h3))))
  have h0 : c1 * (c2 * (c3 * (0 : ℝ≥0∞)) ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) = 0 := by
    simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have := (hc.tendsto 0).comp hf
  rw [h0] at this
  exact this

/-! ### The tail theorem -/

theorem s92_psi_L2 {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ} {b A0 : ℝ}
    (hW : GibbsWellDefined G N b μ) (hW2 : GibbsWellDefined G N (2 * b) μ)
    (h1 : |Real.log (pairNormalizer G N b μ)| ≤ A0) (h2 : |Real.log (pairNormalizer G N (2 * b) μ)| ≤ A0) :
    (∫⁻ X, (s92_dens G N b μ X) ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin N => μ)) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (Real.exp (3 * A0 / 2)) := by
  have e : ∀ X, (s92_dens G N b μ X) ^ (2 : ℝ) = (s92_dens G N b μ X) ^ 2 := fun X => ENNReal.rpow_two _
  simp_rw [e]
  rw [s92_dens_sq_lintegral hW hW2]
  have hle := s92_psi_sq_le hW.normalizer_pos hW2.normalizer_pos h1 h2
  calc _ ≤ (ENNReal.ofReal (Real.exp (3 * A0))) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ENNReal.ofReal (Real.exp (3 * A0 / 2)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
      congr 2; ring

theorem s92_exists_real_le {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ θ : ℝ, 0 < θ ∧ ENNReal.ofReal θ ≤ ε := by
  by_cases ht : ε = ⊤
  · exact ⟨1, one_pos, by simp [ht]⟩
  · refine ⟨ε.toReal, ENNReal.toReal_pos hε.ne' ht, ?_⟩
    rw [ENNReal.ofReal_toReal ht]

/-- **The key estimate of Step C**: for every `θ > 0`, eventually in `j`, for all `N ≥ 2`,
`‖N F^{h_j - h}‖_{L^r(P_N)} ≤ θ`. -/
theorem s92_tail_key {ι : Type*} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L b p K B r C₁ : ℝ)
    (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r) {ρ : Euc d → ℝ} (hρ : IsRound2Density d s M L ρ)
    {P : ι → ∀ N, Measure (EucConfig d N)}
    (hP : ∀ i N, 2 ≤ N → HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) (P i N))
    {h : Euc d → Euc d → ℝ} {hj : ℕ → Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    (ha : IsRound2Approx s C₁ B (HRS.Whole.withDensityReal ρ) h hj) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ j in atTop, ∀ (i : ι) (N : ℕ), 2 ≤ N →
      eLpNorm (fun X : EucConfig d N => (N : ℝ) *
        pairEnergy (fun x y => hj j x y - h x y) X (HRS.Whole.withDensityReal ρ)) (ENNReal.ofReal r) (P i N) ≤
        ENNReal.ofReal θ := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hd1 : 1 ≤ d := by omega
  haveI hμ := s92_isProb_mu hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hcp : 1 < Real.conjExponent p := (Real.HolderConjugate.conjExponent hp).symm.lt
  set t : ℝ := r * Real.conjExponent p with ht
  have ht0 : 0 < t := mul_pos (by linarith) (by linarith)
  set m : ℕ := ⌈t⌉₊ with hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le ht0 (Nat.le_ceil t)
    exact_mod_cast this
  obtain ⟨C2, hC2nn, hC2⟩ := s92_moment_Q hd hs0 hs M L b (C₁ * B + B) hb (2 * m)
  obtain ⟨C0, hC0, hnorm⟩ := s92_normalizer_bounds hd hs0 hs M L b (2 * b) hb (by linarith)
  set K' : ℝ := max K 0 with hK'
  set θ' : ℝ := θ / (K' ^ (1 / r) + 1) with hθ'
  have hθ'0 : 0 < θ' := by positivity
  set ε : ℝ := θ' / 2 with hε
  have hε0 : 0 < ε := by positivity
  -- the smallness of the second moment
  set sj : ℕ → ℝ≥0∞ := fun j => (eLpNorm (fun p : Euc d × Euc d => hj j p.1 p.2 - h p.1 p.2)
    (ENNReal.ofReal 2) (μ.prod μ)) ^ 2 with hsj
  have hconv := ha.converges 2 (by norm_num) (by linarith)
  have hsjT : Tendsto sj atTop (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) ^ 2 = 0 := by simp
    have := ((ENNReal.continuous_pow 2).tendsto 0).comp hconv
    rw [h0] at this
    exact this
  have hfT : Tendsto (fun j => 100 * sj j) atTop (𝓝 0) := by
    have h0 : (100 : ℝ≥0∞) * 0 = 0 := by simp
    have := ((ENNReal.continuous_const_mul (by simp : (100 : ℝ≥0∞) ≠ ⊤)).tendsto 0).comp hsjT
    rw [h0] at this
    exact this
  have hGT := s92_G_tendsto (c1 := (ENNReal.ofReal C2) ^ (1 / (2 : ℝ))) (c2 := ENNReal.ofReal (Real.exp (3 * C0 / 2)))
    (c3 := ENNReal.ofReal (ε ^ (-2 : ℤ)))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top hfT
  have hcpos : (0 : ℝ≥0∞) < ENNReal.ofReal (θ' ^ m / 2) := ENNReal.ofReal_pos.2 (by positivity)
  filter_upwards [(tendsto_order.1 hGT).2 _ hcpos] with j hj'
  intro i N hN
  have hN0 : 0 < N := by omega
  have hk := s92_diff_kernel hh ha j
  obtain ⟨hsec, hint, hHint⟩ := s92_kernel_integrable hd1 hs0 hsd M hρ.prob hρ.bdd hk
  have hW := (hnorm ρ hρ N hN b ⟨le_rfl, by linarith⟩).1
  have hW2 := (hnorm ρ hρ N hN (2 * b) ⟨by linarith, le_rfl⟩).1
  have hl1 := (hnorm ρ hρ N hN b ⟨le_rfl, by linarith⟩).2
  have hl2 := (hnorm ρ hρ N hN (2 * b) ⟨by linarith, le_rfl⟩).2
  haveI hQprob := s92_isProb_Q (N := N) hW
  haveI hPprob : IsProbabilityMeasure (P i N) := (hP i N hN).1
  have hXm : Measurable (fun X : EucConfig d N => (N : ℝ) *
      pairEnergy (fun x y => hj j x y - h x y) X μ) :=
    measurable_const.mul (wr9_measurable_pairEnergy hk.measurable)
  -- second moment under the product measure
  have h2 := s92_second_moment (N := N) hk.measurable hk.symm hsec hint hHint hN0
  rw [s92_S2_eq hk.measurable] at h2
  -- Q-level pieces
  have hQeq : HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ =
      pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ := rfl
  have hGm := wr9_rieszKernel_pair_meas (d := d) s
  have hψm := s92_dens_meas (μ := μ) (N := N) hGm b
  have hdens := s92_pairGibbs_eq (N := N) hGm hW
  have hmom := hC2 ρ hρ _ hk N hN
  rw [hQeq, hdens] at hmom
  have hA := s92_psi_L2 hW hW2 hl1 hl2
  haveI : IsProbabilityMeasure ((Measure.pi fun _ : Fin N => μ).withDensity (s92_dens (fun x y => rieszKernel d s (x - y)) N b μ)) := by
    rw [← hdens]; exact hQprob
  have htail := s92_tail_Q (Measure.pi fun _ : Fin N => μ) hψm hXm m hε0 hmom hA
    (s := 100 * sj j) h2
  have hQmom : ∫⁻ X, ‖(N : ℝ) * pairEnergy (fun x y => hj j x y - h x y) X μ‖ₑ ^ m
      ∂((Measure.pi fun _ : Fin N => μ).withDensity (s92_dens (fun x y => rieszKernel d s (x - y)) N b μ)) ≤ ENNReal.ofReal (θ' ^ m) := by
    have hε1 : ε ^ m ≤ θ' ^ m / 2 := by
      rw [hε, div_pow]
      have h2m : (2 : ℝ) ≤ 2 ^ m := le_self_pow₀ (by norm_num) (by omega)
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h2m
    calc _ ≤ _ := htail
      _ ≤ ENNReal.ofReal (θ' ^ m / 2) + ENNReal.ofReal (θ' ^ m / 2) := by
          refine add_le_add ?_ hj'.le
          rw [← ENNReal.ofReal_pow hε0.le]
          exact ENNReal.ofReal_le_ofReal hε1
      _ = ENNReal.ofReal (θ' ^ m) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  have hQb0 := s92_eLpNorm_le_of_moment ((Measure.pi fun _ : Fin N => μ).withDensity (s92_dens (fun x y => rieszKernel d s (x - y)) N b μ)) hXm ht0 m
    (Nat.le_ceil t) (by positivity) hQmom
  have hroot : (θ' ^ m) ^ (1 / (m : ℝ)) = θ' := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hθ'0.le (by omega)
  rw [hroot, ← hdens, ← hQeq] at hQb0
  have hdensP : eLpNorm (fun X => ((P i N).rnDeriv (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) X).toReal)
      (ENNReal.ofReal p) (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) ≤ ENNReal.ofReal K' :=
    (hP i N hN).2.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hPb := s92_transfer _ (P i N) (hP i N hN).2.1 hp (le_max_right _ _) hdensP hXm (by linarith : 0 < r) hQb0
  refine hPb.trans (ENNReal.ofReal_le_ofReal ?_)
  have hκ : 0 ≤ K' ^ (1 / r) := by positivity
  rw [hθ', ← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith

theorem s92_tail {ι : Type*} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L b p K B r C₁ : ℝ)
    (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r) {ρ : Euc d → ℝ} (hρ : IsRound2Density d s M L ρ)
    {P : ι → ∀ N, Measure (EucConfig d N)}
    (hP : ∀ i N, 2 ≤ N → HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) (P i N))
    {h : Euc d → Euc d → ℝ} {hj : ℕ → Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    (ha : IsRound2Approx s C₁ B (HRS.Whole.withDensityReal ρ) h hj) :
    R2ActualFTail (ι := ι) (fun _ => HRS.Whole.withDensityReal ρ) r h hj P := by
  have hmain := fun θ (hθ : 0 < θ) => s92_tail_key hd hs0 hs M L b p K B r C₁ hb hp hr hρ hP hh ha hθ
  haveI := s92_isProb_mu hρ.prob
  constructor
  · rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨θ, hθ, hθε⟩ := s92_exists_real_le hε
    filter_upwards [hmain θ hθ] with j hj'
    exact iSup_le fun i => iSup_le fun N => (hj' i N.1 N.2).trans hθε
  · rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨θ, hθ, hθε⟩ := s92_exists_real_le hε
    filter_upwards [hmain (θ / 2) (by positivity)] with j hj'
    refine iSup_le fun i => iSup_le fun N => ?_
    have hN := N.2
    haveI : IsProbabilityMeasure (P i N.1) := (hP i N.1 hN).1
    have hk := s92_diff_kernel hh ha j
    have hXm : Measurable (fun X : EucConfig d N.1 => (N.1 : ℝ) *
        pairEnergy (fun x y => hj j x y - h x y) X (HRS.Whole.withDensityReal ρ)) :=
      measurable_const.mul (wr9_measurable_pairEnergy hk.measurable)
    have hc := s92_centered_le (P i N.1) hXm hr (by positivity : (0 : ℝ) ≤ θ / 2) (hj' i N.1 hN)
    have e : (fun X : EucConfig d N.1 => (N.1 : ℝ) *
        (pairEnergy (fun x y => hj j x y - h x y) X (HRS.Whole.withDensityReal ρ) -
          ∫ Y, pairEnergy (fun x y => hj j x y - h x y) Y (HRS.Whole.withDensityReal ρ) ∂(P i N.1))) =
        fun X => (N.1 : ℝ) * pairEnergy (fun x y => hj j x y - h x y) X (HRS.Whole.withDensityReal ρ) -
          ∫ Y, (N.1 : ℝ) * pairEnergy (fun x y => hj j x y - h x y) Y (HRS.Whole.withDensityReal ρ) ∂(P i N.1) := by
      funext X
      rw [integral_const_mul, mul_sub]
    show eLpNorm (fun X : EucConfig d N.1 => (N.1 : ℝ) *
        (pairEnergy (fun x y => hj j x y - h x y) X (HRS.Whole.withDensityReal ρ) -
          ∫ Y, pairEnergy (fun x y => hj j x y - h x y) Y (HRS.Whole.withDensityReal ρ) ∂(P i N.1)))
        (ENNReal.ofReal r) (P i N.1) ≤ ε
    rw [e]
    refine hc.trans ((le_of_eq ?_).trans hθε)
    congr 1; ring

/-- **Proposition S9.2** (`HRS.Whole.round2_moment_transfer`). -/
theorem round2_moment_transfer_proof : type_of% @HRS.Whole.round2_moment_transfer := by
  intro d hd s hs0 hs M L b p K B hb hp r hr
  obtain ⟨CF, hCF0, hCF⟩ := s92_F_bound hd hs0 hs M L b p K B r hb hp hr
  obtain ⟨CL, hCL0, hCL⟩ := s92_linear_bound hd hs0 hs M L b p K r hb hp hr
  refine ⟨max CF CL, fun ρ hρ P hP => ⟨fun h hh => ?_, ?_, fun C₁ h hj hh ha => ?_⟩⟩
  · intro i N hN
    obtain ⟨h1, h2⟩ := hCF ρ hρ h hh N hN (P N) (hP N hN)
    exact ⟨h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
      h2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  · intro i N hN a A ha hA
    have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
    exact (hCL ρ hρ N hN (P N) (hP N hN) a A ha hA).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0))
  · exact s92_tail (ι := Unit) hd hs0 hs M L b p K B r C₁ hb hp hr hρ (P := fun _ => P) (fun _ N hN => hP N hN) hh ha

end HRS.MS.R2Mt
