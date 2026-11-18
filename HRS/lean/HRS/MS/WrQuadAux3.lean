import HRS.MS.WrQuadAux2

/-!
# HRS.MS.WrQuadAux3 -- change of centering, transfer, small `N`, assembly of the quadratic clause (WR-14a, part 3)

Packet WR-14a of `docs/WR_B_PLAN.md` (T12), namespace `HRS.MS.Wr`, helper prefix `wr14a_`.  Euclidean port of
`quad_large:2244`, `quad_crude_Q:2108` and `quadStat_variance:2437` of `HRS/Equilibrium/QuadraticVariance.lean`.

Main statements (all constants quantified before `ρ ≤ M`, `β ∈ [β₋, β₊]`, `N`, `B`, `h`):
* `wr14a_kappaSmall_small_tau`: `KappaSmall β₊ (wr13e_a d s τ M)` for all small `τ` (the smallness hypothesis of
  `wr13e_reference_marginal_density_L2` / `_uniform`; `∫ q_τ = c τ^{(d-s)/2}`);
* `wr14a_quad_large`: for `N ≥ N₁`, `N Var_{Q_N}[D_N(h;ν)] ≤ C B² δ_N`, `ν ∈ {μ, π_N}`
  (reference bound `wr14a_quad_weak_bound` + change of centering `π^R → μ → π_N` by Schur's test
  `wr14a_change_term_le` with `wr13e_reference_marginal_density_L2`, `wr13d_marginal_density_bounds`,
  + transfer `variance_transfer`);
* `wr14a_quad_crude`: the same for each fixed `N ≥ 2` with a constant depending on `N` (crude density bound
  `Q ≤ e^{8 β N k_τ(0)} R_N`, valid for every `N`);
* `wr14a_quadratic_variance_bound`: the conjunct `QuadraticVarianceBound h Q μ (C B² δ_N / N)` and
  `QuadraticVarianceBound h Q (firstMarginal Q) (C B² δ_N / N)` for every `N ≥ 2` and every
  `IsBoundedPairKernel s B h` (conjunct 4 of `euc_static`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

open HRS.External HRS.MS.Psd

variable {d : ℕ} {s : ℝ}

/-! ### Smallness of `β₊ ∫ q_τ` for small `τ` and the uniform setup -/

/-- **`KappaSmall β₊ (wr13e_a d s τ M)` for all small `τ`** (`∫ q_τ = c τ^{(d-s)/2}`). -/
theorem wr14a_kappaSmall_small_tau (hs0 : 0 < s) (hsd : s < d) {βp : ℝ} (hβp : 0 ≤ βp) (M : ℝ) :
    ∃ τ0 : ℝ, 0 < τ0 ∧ ∀ {τ : ℝ}, 0 < τ → τ ≤ τ0 → KappaSmall βp (wr13e_a d s τ M) := by
  have hd0 : (0 : ℝ) < d := by linarith
  set α : ℝ := ((d : ℝ) - s) / 2 with hαdef
  have hα : 0 < α := by rw [hαdef]; linarith
  obtain ⟨δ, hδ, hK⟩ := exists_kappaSmall
  set X : ℝ := βp * (max M 0 * wr12_cq d s) with hXdef
  have hX : 0 ≤ X := mul_nonneg hβp (mul_nonneg (le_max_right _ _) (wr12_cq_nonneg hs0 hsd))
  refine ⟨(δ / (X + 1)) ^ (1 / α), Real.rpow_pos_of_pos (by positivity) _, fun {τ} hτ hττ0 => ?_⟩
  refine hK βp (wr13e_a d s τ M) hβp (wr13e_a_nonneg hs0 hsd hτ M) ?_
  have hτα : τ ^ α ≤ δ / (X + 1) := by
    have := Real.rpow_le_rpow hτ.le hττ0 hα.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one] at this
  have hτα0 : 0 ≤ τ ^ α := (Real.rpow_pos_of_pos hτ α).le
  have e : βp * wr13e_a d s τ M = X * τ ^ α := by
    unfold wr13e_a; rw [hXdef]; ring
  rw [e]
  calc X * τ ^ α ≤ X * (δ / (X + 1)) := mul_le_mul_of_nonneg_left hτα hX
    _ ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith

/-- The standing structure `TransferHyp` for the Riesz kernel, the heat split and the feature map. -/
theorem wr14a_transferHyp (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    TransferHyp (HRS.Whole.withDensityReal ρ) (wr13e_a d s τ M) (qTau d s τ) (kTau d s τ)
      (HRS.Whole.rieszKernel d s) (featMap d s τ) :=
  ⟨wr13e_weak hd hs0 hsd hτ hρ hM, wr13e_a_nonneg hs0 hsd hτ M, featMap_hyp hs0 hτ,
    fun x hx => riesz_heat_split hs0 hτ hx, wr12_atomless hd ρ⟩

/-- Uniform smallness `‖t_N · Ξ‖_∞ ≤ 1` for `N ≥ N₀` (`euc_field_small` and `tN_norm_le`). -/
theorem wr14a_field_small (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (βp M : ℝ) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {β : ℝ}, 0 < β → β ≤ βp → ∀ {N : ℕ}, N0 ≤ N → ∀ x : Euc d,
        |inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ)
          (featMap d s τ) β N) (Xi (HRS.Whole.withDensityReal ρ) (featMap d s τ) x)| ≤ 1 := by
  haveI := featMap_separableSpace (d := d) hs0 hτ
  obtain ⟨N0, hN0, hfs⟩ := euc_field_small (H := Lp (EuclideanSpace ℝ (Fin 2)) 2 (featMeasure d s τ))
    hd hs0 hsd βp M (Real.sqrt (kTau d s τ 0))
  refine ⟨N0, hN0, fun {ρ} hρ hM {β} hβ hβp {N} hN x => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hT := wr14a_transferHyp hd hs0 hsd hτ hρ hM
  have hN' : 0 < N := by omega
  exact hfs τ hτ ρ hρ hM β hβ hβp N hN (featMap d s τ) hT.calFeat _
    (tN_norm_le hT.weak hT.calFeat hβ hN') x

theorem wr14a_isProb_firstMarginal {N : ℕ} (hN : 0 < N) (P : Measure (Fin N → Euc d))
    [IsProbabilityMeasure P] : IsProbabilityMeasure (HRS.Whole.firstMarginal P) := by
  unfold HRS.Whole.firstMarginal
  rw [dif_pos hN]
  exact ⟨by rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]; simp⟩

theorem wr14a_nonneg_of_bound (hd : 1 ≤ d) {B : ℝ} {h : Euc d → Euc d → ℝ}
    (hh : ∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) : 0 ≤ B := by
  haveI : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Euc d)
  have h1 := hh x y hxy
  have h2 : 1 ≤ 1 + HRS.Whole.rieszWeight s (x - y) := by
    linarith [wr3_rieszWeight_nonneg (d := d) s (x - y)]
  by_contra hB
  push Not at hB
  nlinarith [abs_nonneg (h x y)]

/-! ### The quadratic estimate for large `N` -/

set_option maxHeartbeats 3200000 in
/-- **Quadratic estimate for `N ≥ N₁`** (TeX `euc-quadratic`, large `N`): for `ν ∈ {μ, π_N}`,
`N Var_{Q_N}[D_N(h;ν)] ≤ C B² δ_N`, uniformly in `ρ ≤ M`, `β ∈ [β₋, β₊]`. -/
theorem wr14a_quad_large (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβ : βm ≤ βp) (M : ℝ) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ {N : ℕ}, N₁ ≤ N → 2 ≤ N →
      ∀ (B : ℝ) (h : Euc d → Euc d → ℝ), Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ ν ∈ ({HRS.Whole.withDensityReal ρ, HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs
          (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ))} : Set (Measure (Euc d))),
        (N : ℝ≥0∞) * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν)
            (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
  have hd1 : 1 ≤ d := by omega
  have hβp0 : 0 < βp := hβm.trans_le hβ
  obtain ⟨τ0, hτ0, hκτ⟩ := wr14a_kappaSmall_small_tau hs0 hsd hβp0.le M
  have hκ : KappaSmall βp (wr13e_a d s τ0 M) := hκτ hτ0 le_rfl
  haveI := featMap_separableSpace (d := d) hs0 hτ0
  obtain ⟨N0, hN0, hfs⟩ := wr14a_field_small hd1 hs0 hsd hτ0 βp M
  obtain ⟨CR, N3, hR2⟩ := wr13e_reference_marginal_density_L2 hd1 hs0 hsd hτ0 βp M hβp0 hκ
    (featMap_hyp hs0 hτ0)
  obtain ⟨CF, hF2⟩ := wr13d_marginal_density_bounds hd hs0 hsd hβm hβ M
  set a : ℝ := wr13e_a d s τ0 M with ha_def
  have ha : 0 ≤ a := wr13e_a_nonneg hs0 hsd hτ0 M
  set k0 : ℝ := kTau d s τ0 0 with hk0def
  have hk0 : 0 ≤ k0 := (featMap_hyp hs0 hτ0).k_zero_nonneg
  obtain ⟨CW, hCW0, hCW⟩ := wr14a_quad_weak_bound hd hs0 hsd (βp := βp) hβm M (βp * a + 1) 0 a k0 hk0
  obtain ⟨cch, hcch0, hch⟩ := wr14a_change_term_le hd1 hs0.le hsd M
  set KQ : ℝ := Real.exp (4 * βp * k0) with hKQ
  have hKQ1 : 1 ≤ KQ := Real.one_le_exp (by positivity)
  set E : ℝ := Real.exp ((βp * a + 1) + 0 + βp * a) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set Cp : ℝ := max (max 1 E) CF with hCp
  have hCp0 : 0 ≤ Cp := le_trans zero_le_one ((le_max_left _ _).trans (le_max_left _ _))
  set Cb : ℝ := max CR 0 + max CF 0 with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨KQ * (2 * CW + 16 * (cch * Cp * Cb ^ 2)) + 1, max (max N0 N3) 2, ?_⟩
  intro ρ hρ hM β hβ1 hβ2 N hN hN2 B h hm hsym hh ν hν
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hNN0 : N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN3 : N3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hB : 0 ≤ B := wr14a_nonneg_of_bound hd1 hh
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hNn : 0 < n + 1 := Nat.succ_pos n
  have hδ0 : 0 < deltaN d s (n + 1) := HRS.Quad.deltaN_pos hd hs0.le hsd hNn
  have hδ1 : deltaN d s (n + 1) ≤ 1 := HRS.Quad.deltaN_le_one hd hs0.le hsd hNn
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hT := wr14a_transferHyp hd1 hs0 hsd hτ0 hρ hM
  have hsmall := hfs hρ hM hβpos hβ2 hNN0
  have hκβ : KappaSmall β a := KappaSmall.mono hκ hβpos.le ha (mul_le_mul_of_nonneg_right hβ2 ha)
  set V := weakPotE hT.weak ha hβpos.le hT.calFeat
    (tN (fun x y : Euc d => qTau d s τ0 (x - y)) μ (featMap d s τ0) β (n + 1)) hsmall with hV
  have hRN : RN (fun x y : Euc d => qTau d s τ0 (x - y)) μ (featMap d s τ0) β (n + 1) =
      pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) :=
    RN_eq_pinnedLaw hT.weak ha hβpos.le hT.calFeat hNn hsmall
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotE_le hT.weak ha hβpos.le hT.calFeat _ hsmall hκβ
  haveI hRp : IsProbabilityMeasure (RN (fun x y : Euc d => qTau d s τ0 (x - y)) μ (featMap d s τ0) β (n + 1)) :=
    isProb_RN hT.weak hT.calFeat hβpos.le hNn
  haveI hQp : IsProbabilityMeasure (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) (n + 1) β μ) :=
    wr11b_isProb_Q hT hβpos hNn
  set Q := HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) (n + 1) β μ with hQ
  set R0 := pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) with hR0
  haveI hR0p : IsProbabilityMeasure R0 := by rw [← hRN]; exact hRp
  set π0 : Measure (Euc d) := R0.map (fun X => X 0) with hπ0
  haveI hπ0p : IsProbabilityMeasure π0 := inferInstance
  have hπeq : HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ0 (x - y)) μ (featMap d s τ0) β (n + 1))
      = π0 := by
    unfold HRS.Whole.firstMarginal
    rw [dif_pos hNn, hRN]
    rfl
  have hπ0le : π0 ≤ ENNReal.ofReal Cp • μ := by
    have h1 := wr13e_firstMarginal_RN_leK hT.weak ha hβpos hT.calFeat (N := n + 1) hNn hsmall
    rw [hπeq] at h1
    refine h1.trans ?_
    refine Measure.le_iff'.2 fun A => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_left _ _))
    rw [hE]
    refine Real.exp_le_exp.2 ?_
    have h1 : β * a ≤ βp * a := mul_le_mul_of_nonneg_right hβ2 ha
    linarith
  -- the density estimates
  obtain ⟨hπRac, hπR2⟩ := hR2 ρ hρ hM β hβpos hβ2 (n + 1) hNN3
  rw [hπeq] at hπRac hπR2
  obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hF2 ρ hρ hM β ⟨hβ1, hβ2⟩ (n + 1) hN2
  have hπNeq : HRS.Whole.firstMarginal Q = μ.withDensity (fun x => ENNReal.ofReal (φ x)) := hφeq
  have hπNle : HRS.Whole.firstMarginal Q ≤ ENNReal.ofReal Cp • μ := by
    rw [hπNeq]
    refine Measure.le_iff.2 fun A hA => ?_
    rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    exact (hφb x).2.trans ((le_max_right _ _))
  have hπNac : HRS.Whole.firstMarginal Q ≪ μ := by rw [hπNeq]; exact withDensity_absolutelyContinuous _ _
  have hνfacts : IsProbabilityMeasure ν ∧ ν ≤ ENNReal.ofReal Cp • μ ∧ ν ≪ μ ∧
      eLpNorm (fun y => (ν.rnDeriv μ y).toReal - (π0.rnDeriv μ y).toReal) 2 μ ≤
        ENNReal.ofReal (Cb * deltaN d s (n + 1)) := by
    rcases hν with rfl | rfl
    · refine ⟨inferInstance, Measure.le_iff'.2 fun A => ?_, Measure.AbsolutelyContinuous.refl _, ?_⟩
      · rw [Measure.smul_apply, smul_eq_mul]
        exact le_mul_of_one_le_left bot_le
          (ENNReal.one_le_ofReal.2 ((le_max_left _ _).trans (le_max_left _ _)))
      · have e : (fun y => (μ.rnDeriv μ y).toReal - (π0.rnDeriv μ y).toReal) =ᵐ[μ]
            fun y => -((π0.rnDeriv μ y).toReal - 1) := by
          filter_upwards [Measure.rnDeriv_self μ] with y hy
          simp [hy]
        rw [eLpNorm_congr_ae e]
        refine (le_of_eq (eLpNorm_neg _ _ _)).trans (hπR2.trans (ENNReal.ofReal_le_ofReal ?_))
        refine mul_le_mul_of_nonneg_right ?_ hδ0.le
        have := le_max_left CR 0
        have := le_max_right CF 0
        rw [hCb]; linarith
    · refine ⟨wr14a_isProb_firstMarginal hNn _, hπNle, hπNac, ?_⟩
      have hrn : (fun y => ((HRS.Whole.firstMarginal Q).rnDeriv μ y).toReal) =ᵐ[μ] φ := by
        rw [hπNeq]
        filter_upwards [Measure.rnDeriv_withDensity μ (f := fun x => ENNReal.ofReal (φ x))
          (ENNReal.measurable_ofReal.comp hφm)] with y hy
        rw [hy, ENNReal.toReal_ofReal (hφb y).1]
      have e : (fun y => ((HRS.Whole.firstMarginal Q).rnDeriv μ y).toReal - (π0.rnDeriv μ y).toReal)
          =ᵐ[μ] (fun y => φ y - 1) - fun y => (π0.rnDeriv μ y).toReal - 1 := by
        filter_upwards [hrn] with y hy
        simp only [Pi.sub_apply, hy]; ring
      rw [eLpNorm_congr_ae e]
      refine (eLpNorm_sub_le (by norm_num)).trans ?_
      have hφn' : eLpNorm (fun x => φ x - 1) 2 μ ≤ ENNReal.ofReal (CF * deltaN d s (n + 1)) :=
        wr13d_eLpNorm_le_of_sqrt hφ2 hφn
      refine (add_le_add hφn' hπR2).trans ?_
      have hCF : CF * deltaN d s (n + 1) ≤ max CF 0 * deltaN d s (n + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le
      have hCR : CR * deltaN d s (n + 1) ≤ max CR 0 * deltaN d s (n + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le
      calc ENNReal.ofReal (CF * deltaN d s (n + 1)) + ENNReal.ofReal (CR * deltaN d s (n + 1))
          ≤ ENNReal.ofReal (max CF 0 * deltaN d s (n + 1)) + ENNReal.ofReal (max CR 0 * deltaN d s (n + 1)) :=
            add_le_add (ENNReal.ofReal_le_ofReal hCF) (ENNReal.ofReal_le_ofReal hCR)
        _ = ENNReal.ofReal (Cb * deltaN d s (n + 1)) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity), hCb]
            congr 1; ring
  obtain ⟨hνp, hνle, hνac, hνL2⟩ := hνfacts
  have hF : Measurable (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X ν) :=
    wr14a_measurable_D hm ν
  have step1 : ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
        HRS.Whole.centeredPairFunctional h X ν) Q ≤
      ENNReal.ofReal KQ * (((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
        HRS.Whole.centeredPairFunctional h X ν) R0) := by
    have h1 := variance_transfer hT hβpos hNn hsmall hκβ _ hF.aestronglyMeasurable
    rw [hRN] at h1
    have h2 : ENNReal.ofReal (Real.exp (4 * β * kTau d s τ0 0)) ≤ ENNReal.ofReal KQ := by
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have : β * k0 ≤ βp * k0 := mul_le_mul_of_nonneg_right hβ2 hk0
      linarith
    calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
          HRS.Whole.centeredPairFunctional h X ν) Q
        ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (Real.exp (4 * β * kTau d s τ0 0)) *
            evariance (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X ν) R0) := by
          gcongr
      _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal KQ *
            evariance (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X ν) R0) := by
          gcongr
      _ = _ := by ring
  have step2 := wr14a_evariance_quad_change (N := n + 1) V hβpos.le hκV hm ν
  have hq : ∀ x y : Euc d, x ≠ y → HRS.Whole.rieszWeight s (x - y) - k0 ≤ V.q x y := by
    intro x y hxy
    have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
    have h1 := riesz_heat_split (d := d) hs0 hτ0 hz
    have h2 := kTau_le_zero (d := d) hs0 hτ0 (x - y)
    rw [wr13e_g_eq_weight hs0] at h1
    show HRS.Whole.rieszWeight s (x - y) - k0 ≤ qTau d s τ0 (x - y)
    linarith
  have hVM : V.M ≤ βp * a + 1 := by
    show β * a + 1 ≤ βp * a + 1
    have := mul_le_mul_of_nonneg_right hβ2 ha
    linarith
  have step3 := hCW hρ hM V hVM (le_refl _) (le_refl _) hq hβ1 hβ2 hn1 hκV B hB h hm hsym hh
  have step4 := hch hρ hM hCp0 hB hm hh (π := π0) (ν := ν) hπ0le hνle hπRac hνac
  have step5 : (eLpNorm (fun y => (ν.rnDeriv μ y).toReal - (π0.rnDeriv μ y).toReal) 2 μ) ^ 2 ≤
      ENNReal.ofReal (Cb ^ 2 * deltaN d s (n + 1)) := by
    refine (pow_le_pow_left' hνL2 2).trans ?_
    rw [← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (Cb * deltaN d s (n + 1)) ^ 2 = Cb ^ 2 * (deltaN d s (n + 1) * deltaN d s (n + 1)) := by ring
    rw [this]
    have h2 : deltaN d s (n + 1) * deltaN d s (n + 1) ≤ deltaN d s (n + 1) := by nlinarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hcomb := HRS.Quad.ofReal_comb (K := KQ) (a := CW * B ^ 2 * deltaN d s (n + 1))
    (b := cch * Cp * B ^ 2) (c := Cb ^ 2 * deltaN d s (n + 1)) (by positivity) (by positivity)
    (by positivity) (by positivity)
  calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
        HRS.Whole.centeredPairFunctional h X ν) Q
      ≤ ENNReal.ofReal KQ * (((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
          HRS.Whole.centeredPairFunctional h X ν) R0) := step1
    _ ≤ ENNReal.ofReal KQ * (2 * ENNReal.ofReal (CW * B ^ 2 * deltaN d s (n + 1)) +
          16 * (ENNReal.ofReal (cch * Cp * B ^ 2) * ENNReal.ofReal (Cb ^ 2 * deltaN d s (n + 1)))) := by
        refine mul_le_mul' le_rfl (step2.trans ?_)
        refine add_le_add ?_ ?_
        · rw [mul_assoc]
          exact mul_le_mul' le_rfl step3
        · exact mul_le_mul' le_rfl (step4.trans (mul_le_mul' le_rfl step5))
    _ = ENNReal.ofReal (KQ * (2 * (CW * B ^ 2 * deltaN d s (n + 1)) +
          16 * ((cch * Cp * B ^ 2) * (Cb ^ 2 * deltaN d s (n + 1))))) := hcomb
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 0 ≤ B ^ 2 * deltaN d s (n + 1) := by positivity
        nlinarith [h1]

/-! ### Small `N`: the crude bound -/

/-- **Crude density bound, every `N ≥ 1`**: `Q ≤ e^{8 β N k(0)} R_N` (the logarithmic weight satisfies
`‖S_N - √N Ξ̄_N‖² ≤ 16 N k(0)`, so the normalising constant is `≥ e^{-8 β N k(0)}`). -/
theorem wr14a_Q_le_crude {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q k g : Euc d → ℝ} {Ψ : Euc d → H} {N : ℕ}
    {β : ℝ} (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N) :
    HRS.Whole.modulatedGibbs g N β μ ≤
      ENNReal.ofReal (Real.exp (8 * β * N * k 0)) • RN (wr11b_dk q) μ Ψ β N := by
  haveI := wr11b_isProb_RN h hβ.le hN
  have hk0 : 0 ≤ k 0 := h.feat.k_zero_nonneg
  have hQ : HRS.Whole.modulatedGibbs g N β μ = (RN (wr11b_dk q) μ Ψ β N).withDensity
      (fun X => ENNReal.ofReal (Real.exp (wr11b_logW q μ Ψ β N X) /
        ∫ Y, Real.exp (wr11b_logW q μ Ψ β N Y) ∂(RN (wr11b_dk q) μ Ψ β N))) :=
    h.Q_eq_RN_tilted hβ hN
  rw [hQ]
  set c : ℝ := 8 * β * N * k 0 with hc
  have hlow : ∀ X, -c ≤ wr11b_logW q μ Ψ β N X := by
    intro X
    rw [wr11b_logW_eq]
    have h1 := wr11b_norm_D_le h hβ.le hN X
    have h0 := norm_nonneg (wr11b_D q μ Ψ β N X)
    have h2 : ‖wr11b_D q μ Ψ β N X‖ ^ 2 ≤ (Real.sqrt N * (4 * Real.sqrt (k 0))) ^ 2 := by gcongr
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), Real.sq_sqrt hk0] at h2
    rw [hc]
    nlinarith
  have hZ : Real.exp (-c) ≤ ∫ Y, Real.exp (wr11b_logW q μ Ψ β N Y) ∂(RN (wr11b_dk q) μ Ψ β N) := by
    have := integral_mono (μ := RN (wr11b_dk q) μ Ψ β N) (integrable_const (Real.exp (-c)))
      (wr11b_integrable_exp_logW h hβ) (fun X => Real.exp_le_exp.2 (hlow X))
    simpa using this
  have hZpos : 0 < Real.exp (-c) := Real.exp_pos _
  intro S
  rw [withDensity_apply' _ S, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in S, ENNReal.ofReal (Real.exp (wr11b_logW q μ Ψ β N x) /
        ∫ Y, Real.exp (wr11b_logW q μ Ψ β N Y) ∂(RN (wr11b_dk q) μ Ψ β N)) ∂(RN (wr11b_dk q) μ Ψ β N)
      ≤ ∫⁻ _x in S, ENNReal.ofReal (Real.exp c) ∂(RN (wr11b_dk q) μ Ψ β N) := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ (hZpos.trans_le hZ)]
        have h1 : Real.exp (wr11b_logW q μ Ψ β N x) ≤ 1 := Real.exp_le_one_iff.2 (wr11b_logW_nonpos hβ x)
        calc Real.exp (wr11b_logW q μ Ψ β N x) ≤ 1 := h1
          _ = Real.exp c * Real.exp (-c) := by rw [← Real.exp_add]; simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le
    _ = _ := by rw [setLIntegral_const]

/-- A measure with a bounded density with respect to `μ` is dominated by `C μ` and `≪ μ`. -/
theorem wr14a_le_of_hasMarginalDensityBounds {μ π : Measure (Euc d)} {C r : ℝ}
    (hπ : HRS.Whole.HasMarginalDensityBounds π μ C r) : π ≤ ENNReal.ofReal C • μ ∧ π ≪ μ := by
  obtain ⟨φ, hφm, hφeq, hφb, -, -⟩ := hπ
  refine ⟨?_, by rw [hφeq]; exact withDensity_absolutelyContinuous _ _⟩
  rw [hφeq]
  refine Measure.le_iff.2 fun A hA => ?_
  rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hφb x).2

set_option maxHeartbeats 3200000 in
/-- **Quadratic estimate for a fixed `N ≥ 2`** (crude, constant depending on `N`):
`N Var_{Q_N}[D_N(h;ν)] ≤ C B² δ_N`, `ν ∈ {μ, π_N}`, uniformly in `ρ ≤ M`, `β ∈ [β₋, β₊]`. -/
theorem wr14a_quad_crude (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβ : βm ≤ βp) (M : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ C : ℝ, ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {β : ℝ}, βm ≤ β → β ≤ βp →
      ∀ (B : ℝ) (h : Euc d → Euc d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ ν ∈ ({HRS.Whole.withDensityReal ρ, HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs
          (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ))} : Set (Measure (Euc d))),
        (N : ℝ≥0∞) * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν)
            (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
  have hd1 : 1 ≤ d := by omega
  have hβp0 : 0 < βp := hβm.trans_le hβ
  have hτ : (0 : ℝ) < 1 := one_pos
  haveI := featMap_separableSpace (d := d) hs0 hτ
  set a : ℝ := wr13e_a d s 1 M with ha_def
  have ha : 0 ≤ a := wr13e_a_nonneg hs0 hsd hτ M
  set k0 : ℝ := kTau d s 1 0 with hk0def
  have hk0 : 0 ≤ k0 := (featMap_hyp hs0 hτ).k_zero_nonneg
  obtain ⟨CF, hF2⟩ := wr13d_marginal_density_bounds hd hs0 hsd hβm hβ M
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hNn : 0 < n + 1 := Nat.succ_pos n
  obtain ⟨Cc, hCc0, hCc⟩ := wr14a_quad_crude_weak hd hs0 hsd hβm M (βp * a + 4 * βp * k0) 0 a k0 hk0
    (βp := βp) (n := n) hn1
  set K' : ℝ := Real.exp (8 * βp * ((n + 1 : ℕ) : ℝ) * k0) with hK'
  have hK'0 : 0 < K' := Real.exp_pos _
  set Cp : ℝ := max 1 CF with hCp
  have hCp0 : 0 ≤ Cp := le_trans zero_le_one (le_max_left _ _)
  have hδ := HRS.Quad.deltaN_pos hd hs0.le hsd hNn
  refine ⟨((n + 1 : ℕ) : ℝ) * K' * Cc * (1 + Cp ^ 2) / deltaN d s (n + 1), ?_⟩
  intro ρ hρ hM β hβ1 hβ2 B h hm hh ν hν
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hB : 0 ≤ B := wr14a_nonneg_of_bound hd1 hh
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hT := wr14a_transferHyp hd1 hs0 hsd hτ hρ hM
  have ht0 : ∀ x, |inner ℝ (tN (fun x y : Euc d => qTau d s 1 (x - y)) μ (featMap d s 1) β (n + 1))
      (Xi μ (featMap d s 1) x)| ≤ 4 * βp * k0 := fun x => by
    have h1 := wr13e_abs_tN_inner_le hT.weak hT.calFeat hβpos hNn x
    rw [Real.sq_sqrt hk0] at h1
    have : β * k0 ≤ βp * k0 := mul_le_mul_of_nonneg_right hβ2 hk0
    linarith
  set V := wr13e_weakPotK hT.weak ha hβpos.le hT.calFeat
    (tN (fun x y : Euc d => qTau d s 1 (x - y)) μ (featMap d s 1) β (n + 1)) ht0 with hV
  have hRN : RN (fun x y : Euc d => qTau d s 1 (x - y)) μ (featMap d s 1) β (n + 1) =
      pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    rw [wr13e_RN_eq_fieldLawK hT.weak ha hβpos.le hT.calFeat hNn ht0, RefMarg.pinnedLaw_empty]
  haveI hQp : IsProbabilityMeasure (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) (n + 1) β μ) :=
    wr11b_isProb_Q hT hβpos hNn
  have hq : ∀ x y : Euc d, x ≠ y → HRS.Whole.rieszWeight s (x - y) - k0 ≤ V.q x y := by
    intro x y hxy
    have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
    have h1 := riesz_heat_split (d := d) hs0 hτ hz
    have h2 := kTau_le_zero (d := d) hs0 hτ (x - y)
    rw [wr13e_g_eq_weight hs0] at h1
    show HRS.Whole.rieszWeight s (x - y) - k0 ≤ qTau d s 1 (x - y)
    linarith
  have hVM : V.M ≤ βp * a + 4 * βp * k0 := by
    show β * a + 4 * βp * k0 ≤ βp * a + 4 * βp * k0
    have := mul_le_mul_of_nonneg_right hβ2 ha
    linarith
  have hQK := wr14a_Q_le_crude hT hβpos hNn
  rw [hRN] at hQK
  have hK'' : ENNReal.ofReal (Real.exp (8 * β * ((n + 1 : ℕ) : ℝ) * kTau d s 1 0)) ≤ ENNReal.ofReal K' := by
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have : β * (((n + 1 : ℕ) : ℝ) * k0) ≤ βp * (((n + 1 : ℕ) : ℝ) * k0) :=
      mul_le_mul_of_nonneg_right hβ2 (by positivity)
    linarith
  have key : ∀ ν : Measure (Euc d), IsProbabilityMeasure ν → ν ≤ ENNReal.ofReal Cp • μ →
      ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
          HRS.Whole.centeredPairFunctional h X ν)
          (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) (n + 1) β μ) ≤
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * K' * Cc * (1 + Cp ^ 2) / deltaN d s (n + 1) * B ^ 2 *
          deltaN d s (n + 1)) := by
    intro ν hνp hνle
    have hbd := hCc hρ hM V hVM (le_refl _) (le_refl _) hq hβ1 hβ2 B hB h hm hh hCp0 ν hνle
    have hF : Measurable (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X ν) :=
      wr14a_measurable_D hm ν
    have h1 : evariance (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X ν)
        (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) (n + 1) β μ) ≤
        ∫⁻ X, ‖HRS.Whole.centeredPairFunctional h X ν‖ₑ ^ 2
          ∂(HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) (n + 1) β μ) := by
      have := evariance_le_lintegral_sub (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) (n + 1) β μ)
        hF.aestronglyMeasurable 0
      simpa using this
    have h2 : ∫⁻ X, ‖HRS.Whole.centeredPairFunctional h X ν‖ₑ ^ 2
          ∂(HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) (n + 1) β μ)
        ≤ ENNReal.ofReal K' * ∫⁻ X, ‖HRS.Whole.centeredPairFunctional h X ν‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
      calc _ ≤ ∫⁻ X, ‖HRS.Whole.centeredPairFunctional h X ν‖ₑ ^ 2
              ∂(ENNReal.ofReal (Real.exp (8 * β * ((n + 1 : ℕ) : ℝ) * kTau d s 1 0)) •
                pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
            lintegral_mono' hQK le_rfl
        _ = ENNReal.ofReal (Real.exp (8 * β * ((n + 1 : ℕ) : ℝ) * kTau d s 1 0)) *
            ∫⁻ X, ‖HRS.Whole.centeredPairFunctional h X ν‖ₑ ^ 2
              ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
            rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ _ := by gcongr
    calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
          HRS.Whole.centeredPairFunctional h X ν)
          (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) (n + 1) β μ)
        ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal K' * ENNReal.ofReal (Cc * (1 + Cp ^ 2) * B ^ 2)) := by
          gcongr
          exact h1.trans (h2.trans (by gcongr))
      _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * K' * Cc * (1 + Cp ^ 2) / deltaN d s (n + 1) * B ^ 2 *
          deltaN d s (n + 1)) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hK'0.le, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  rcases hν with rfl | rfl
  · refine key _ inferInstance (Measure.le_iff'.2 fun A => ?_)
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 (le_max_left _ _))
  · obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hF2 ρ hρ hM β ⟨hβ1, hβ2⟩ (n + 1) hN
    have hπle : HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) (n + 1) β μ) ≤
        ENNReal.ofReal Cp • μ := by
      rw [hφeq]
      refine Measure.le_iff.2 fun A hA => ?_
      rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
      exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal ((hφb x).2.trans (le_max_right _ _))
    exact key _ (wr14a_isProb_firstMarginal hNn _) hπle

/-! ### Assembly: `QuadraticVarianceBound` for `ν = μ` and `ν = π_N` -/

theorem wr14a_isProb_Q (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal ρ)) := by
  haveI := featMap_separableSpace (d := d) hs0 (one_pos : (0 : ℝ) < 1)
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  exact wr11b_isProb_Q (wr14a_transferHyp hd hs0 hsd one_pos hρ hM) hβ hN

theorem wr14a_evariance_div {V : ℝ≥0∞} {X : ℝ} {N : ℕ} (hN : 0 < N)
    (h : (N : ℝ≥0∞) * V ≤ ENNReal.ofReal X) : V ≤ ENNReal.ofReal (X / N) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast,
    ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.2 hN.ne')) (Or.inl (ENNReal.natCast_ne_top N))]
  rwa [mul_comm]

/-- Absolute integrability of an envelope-bounded kernel against `ν ⊗ ν` for `ν ≤ Cp μ`. -/
theorem wr14a_pair_integrable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {ν : Measure (Euc d)} {Cp : ℝ}, ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → 0 ≤ Cp →
      IsProbabilityMeasure ν → ∀ {B : ℝ}, 0 ≤ B → ∀ {h : Euc d → Euc d → ℝ},
      Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) →
      Integrable (fun p : Euc d × Euc d => h p.1 p.2) (ν.prod ν) := by
  obtain ⟨c, hc0, hHc⟩ := wr14a_Hc_bound hd hs0 hsd M
  intro ρ hρ hM ν Cp hν hCp hνp B hB h hm hh
  have hm' : Measurable (fun p : Euc d × Euc d => h p.1 p.2) := hm
  rw [integrable_prod_iff hm'.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · exact wr14a_integrable_of_env_bound hd hs0 hsd M hρ hM hν hCp hB (wr14a_measurable_h_x hm x)
      (fun y hy => hh x y (Ne.symm hy))
  · have hbd : ∀ x, |∫ y, ‖h x y‖ ∂ν| ≤ c * Cp * B := by
      intro x
      have := hHc hρ hM hν hCp hB (h := fun x y => |h x y|) (fun x y hxy => by
        rw [abs_abs]; exact hh x y hxy) x
      simpa [wr14a_Hc, Real.norm_eq_abs] using this
    have hmeas : Measurable (fun x : Euc d => ∫ y, ‖h x y‖ ∂ν) :=
      (hm'.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    refine Integrable.of_bound hmeas.aestronglyMeasurable (c * Cp * B)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hbd x

/-- Monotonicity of `QuadraticVarianceBound` in the bound. -/
theorem wr14a_qvb_mono {N : ℕ} {h : Euc d → Euc d → ℝ} {Q : Measure (Fin N → Euc d)}
    {ν : Measure (Euc d)} {b b' : ℝ} (hb : b ≤ b') (H : HRS.Whole.QuadraticVarianceBound h Q ν b) :
    HRS.Whole.QuadraticVarianceBound h Q ν b' :=
  ⟨H.1, H.2.1, H.2.2.trans (ENNReal.ofReal_le_ofReal hb)⟩

/-- **The quadratic clause of `euc_static` (conjunct 4)**: there is `C` (quantified before `ρ ≤ M`,
`β ∈ [β₋, β₊]`, `N ≥ 2`, `B`, `h`) such that for every `IsBoundedPairKernel s B h`,
`QuadraticVarianceBound h Q_N μ (C B² δ_N / N)` and `QuadraticVarianceBound h Q_N π_N (C B² δ_N / N)`,
`μ = ρ dx`, `π_N = Q_N^{(1)}`.  (Any larger constant also works, `wr14a_qvb_mono`.) -/
theorem wr14a_quadratic_variance_bound (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβ : βm ≤ βp) (M : ℝ) :
    ∃ C : ℝ, ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {β : ℝ}, β ∈ Set.Icc βm βp → ∀ {N : ℕ}, 2 ≤ N → ∀ (B : ℝ) (h : Euc d → Euc d → ℝ),
      HRS.Whole.IsBoundedPairKernel s B h →
      HRS.Whole.QuadraticVarianceBound h
        (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ))
        (HRS.Whole.withDensityReal ρ) (C * B ^ 2 * deltaN d s N / N) ∧
      HRS.Whole.QuadraticVarianceBound h
        (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ))
        (HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
          (HRS.Whole.withDensityReal ρ))) (C * B ^ 2 * deltaN d s N / N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, N₁, h1⟩ := wr14a_quad_large hd hs0 hsd hβm hβ M
  obtain ⟨CF, hF2⟩ := wr13d_marginal_density_bounds hd hs0 hsd hβm hβ M
  have hc : ∀ N : ℕ, ∃ C : ℝ, 2 ≤ N → ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {β : ℝ}, βm ≤ β → β ≤ βp →
      ∀ (B : ℝ) (h : Euc d → Euc d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ ν ∈ ({HRS.Whole.withDensityReal ρ, HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs
          (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ))} : Set (Measure (Euc d))),
        (N : ℝ≥0∞) * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν)
            (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
    intro N
    by_cases hN : 2 ≤ N
    · obtain ⟨C, hC⟩ := wr14a_quad_crude hd hs0 hsd hβm hβ M hN
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Cs hCs using hc
  refine ⟨|C₁| + ∑ N ∈ Finset.range N₁, |Cs N|, ?_⟩
  intro ρ hρ hM β hβmem N hN B h hBK
  obtain ⟨hβ1, hβ2⟩ := hβmem
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hNpos : 0 < N := by omega
  have hB : 0 ≤ B := wr14a_nonneg_of_bound hd1 hBK.bound
  have hm : Measurable (Function.uncurry h) := hBK.measurable
  have hD : 0 ≤ B ^ 2 * deltaN d s N := by
    have := HRS.Quad.deltaN_pos hd hs0.le hsd (N := N) hNpos
    positivity
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  haveI hQp := wr14a_isProb_Q hd1 hs0 hsd hρ hM hβpos hNpos (N := N)
  have hvar : ∀ ν ∈ ({HRS.Whole.withDensityReal ρ, HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs
          (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ))} : Set (Measure (Euc d))),
        (N : ℝ≥0∞) * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν)
            (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal ((|C₁| + ∑ N ∈ Finset.range N₁, |Cs N|) * B ^ 2 * deltaN d s N) := by
    intro ν hν
    by_cases hNN : N₁ ≤ N
    · refine (h1 hρ hM hβ1 hβ2 hNN hN B h hm hBK.symm hBK.bound ν hν).trans (ENNReal.ofReal_le_ofReal ?_)
      have h2 : C₁ ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
        have := le_abs_self C₁
        have : 0 ≤ ∑ N ∈ Finset.range N₁, |Cs N| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        linarith
      nlinarith [mul_le_mul_of_nonneg_right h2 hD]
    · have hlt : N < N₁ := not_le.1 hNN
      refine (hCs N hN hρ hM hβ1 hβ2 B h hm hBK.bound ν hν).trans (ENNReal.ofReal_le_ofReal ?_)
      have h2 : Cs N ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
        have h3 : |Cs N| ≤ ∑ N ∈ Finset.range N₁, |Cs N| :=
          Finset.single_le_sum (f := fun N => |Cs N|) (fun M _ => abs_nonneg (Cs M)) (Finset.mem_range.2 hlt)
        have := le_abs_self (Cs N)
        have := abs_nonneg C₁
        linarith
      nlinarith [mul_le_mul_of_nonneg_right h2 hD]
  obtain ⟨hπle, hπac⟩ := wr14a_le_of_hasMarginalDensityBounds (hF2 ρ hρ hM β ⟨hβ1, hβ2⟩ N hN)
  have hπp := wr14a_isProb_firstMarginal hNpos (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
    (HRS.Whole.withDensityReal ρ))
  have hμle : HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal 1 • HRS.Whole.withDensityReal ρ := by simp
  have hCF0 : 0 ≤ max CF 0 := le_max_right _ _
  have hπle' : HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal (max CF 0) • HRS.Whole.withDensityReal ρ :=
    hπle.trans (by
      refine Measure.le_iff'.2 fun A => ?_
      rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
  have mk : ∀ ν : Measure (Euc d), IsProbabilityMeasure ν →
      ∀ {Cp : ℝ}, 0 ≤ Cp → ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ →
      (N : ℝ≥0∞) * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν)
            (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal ((|C₁| + ∑ N ∈ Finset.range N₁, |Cs N|) * B ^ 2 * deltaN d s N) →
      HRS.Whole.QuadraticVarianceBound h
        (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ν
        ((|C₁| + ∑ N ∈ Finset.range N₁, |Cs N|) * B ^ 2 * deltaN d s N / N) := by
    intro ν hνp Cp hCp hνle hv
    refine ⟨fun x => wr14a_integrable_of_env_bound hd1 hs0.le hsd M hρ hM hνle hCp hB
      (wr14a_measurable_h_x hm x) (fun y hy => hBK.bound x y (Ne.symm hy)),
      wr14a_pair_integrable hd1 hs0.le hsd M hρ hM hνle hCp hνp hB hm hBK.bound, ?_⟩
    exact wr14a_evariance_div hNpos hv
  exact ⟨mk _ inferInstance zero_le_one hμle
      (hvar _ (Set.mem_insert _ _)),
    mk _ hπp hCF0 hπle' (hvar _ (Set.mem_insert_of_mem _ rfl))⟩

end HRS.MS.Wr
