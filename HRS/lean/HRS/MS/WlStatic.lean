import HRS.MS.WlQuadAux3
import HRS.MS.WlLin
import HRS.MS.WlMargAux2
import HRS.MS.Comm

/-!
# HRS.MS.WlStatic -- assembly of `r2_log_static` and `r2_log_static_commutator` (WL-11)

Packet WL-11 of `docs/WR_LOG_PLAN.md` (Step 12), namespace `HRS.MS.Wl`, helper prefix `wl11_`.  The statements are
exactly the frozen `HRS.Whole.r2_log_static` and `HRS.Whole.r2_log_static_commutator` (no adjustment).

Main statements.
* `wl11_quad_large`: for `N ≥ N₁`, `N Var_{Q_N}[D_N(h;ν)] ≤ C B²/N` for `ν ∈ {μ, π_N}` (transfer `wl_transfer`
  `Var_Q ≤ e^{4βk₀} Var_{R_N}`, change of centering `π^R → ν` by `wr14a_evariance_quad_change`, the reference
  estimate `wl_quad_ref` `Var_{R_N}(D_N(h;π^R)) ≤ C B²/N²`, the change term `wl11_change_term_le` with the
  `L²(μ)` estimates `‖θ_R - 1‖, ‖θ_N - 1‖ ≤ C/N` of `wl_ref_marginal_L2`, `wl_marginal_L2`);
* `wl11_quad_crude`: for each fixed `N ≥ 2`, `E_Q |D_N(h;ν)|² ≤ C_N B²` (the same bound without smallness: `Q` is the
  pinned law of the weak potential `wlPot` of `K`, pair second moments by `wr14a_pair_lintegral_le`, the square
  `wr14a_D_sq_le`, `H_ν` bounded by `wl10_Hc_bound`);
* `wl11_quadratic_variance_bound`: conjunct 4 of `r2_log_static`;
* `r2_log_static_proof : type_of% @HRS.Whole.r2_log_static` (conjunct 1 `wl_gibbsWellDefined`, conjunct 2
  `wl_static_linear`, conjunct 3 `wl_hasLogMarginalDensityBounds`, conjunct 4 `wl11_quadratic_variance_bound`);
* `r2_log_static_commutator_proof : type_of% @HRS.Whole.r2_log_static_commutator` (conjunct 4 with `B = Λ`,
  `h = commutatorKernel d 0 v`, `commutatorKernel_log_isBounded_proof`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-! ### The quadratic estimate for large `N` -/

set_option maxHeartbeats 3200000 in
/-- **Quadratic estimate for `N ≥ N₁`**: for `ν ∈ {μ, π_N}`, `N Var_{Q_N}[D_N(h;ν)] ≤ C B²/N`, uniformly in `ρ`
(with `HasSphericalBound A ρ`), `β ∈ [β₋, β₊]`. -/
theorem wl11_quad_large (hd : 2 ≤ d) (A βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ N : ℕ, N₁ ≤ N → 2 ≤ N →
      ∀ (B : ℝ) (h : Euc d → Euc d → ℝ), Measurable (fun p : Euc d × Euc d => h p.1 p.2) →
      (∀ x y, h x y = h y x) → (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      ∀ ν ∈ ({HRS.Whole.withDensityReal ρ, HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs
          (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ))} : Set (Measure (Euc d))),
        (N : ℝ≥0∞) * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν)
            (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 / N) := by
  have hβp0 : 0 < βp := hβm.trans_le hβ
  obtain ⟨Mt, hMt1, htr⟩ := wl_transfer hd A βp 0
  obtain ⟨Mr, hMr1, hrefL2⟩ := wl_ref_marginal_L2 hd A βp hβp0.le
  obtain ⟨Mq, hMq1, hquad⟩ := wl_quad_ref hd A βp hβp0.le
  obtain ⟨Md, hMd1, hdata⟩ := wl11_ref_pinned hd A βp hβp0.le
  obtain ⟨Cqq, hCqq0, hCqq⟩ := wl_qm_weak hd A
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  obtain ⟨Cm, hCm1, hmarg⟩ := wl_marginal_L2 hd A βp hβp0.le
  obtain ⟨cch, hcch0, hch⟩ := wl11_change_term_le hd A
  set M : ℕ := max (max Mt Mr) (max Mq Md) with hM
  have hMt' : Mt ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMr' : Mr ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hMq' : Mq ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMd' : Md ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hM1 : 1 ≤ M := hMt1.trans hMt'
  obtain ⟨Nt, htr'⟩ := htr M hMt'
  obtain ⟨Nr, Cr, hNr2, hCr1, hr⟩ := hrefL2 M hMr'
  obtain ⟨Nq, Cqr, hNq2, hCqr0, hqr⟩ := hquad M hMq'
  obtain ⟨Nd, hNd2, hdd⟩ := hdata M hMd'
  set Cp : ℝ := max Cr Cm with hCp
  have hCp1 : 1 ≤ Cp := hCr1.trans (le_max_left _ _)
  have hCp0 : 0 ≤ Cp := by linarith
  set Cb : ℝ := Cr + Cm with hCb
  have hCb0 : 0 ≤ Cb := by linarith
  set k0 : ℝ := wl_k0 M with hk0def
  have hk0 : 0 ≤ k0 := wl_k0_nonneg M
  set KQ : ℝ := Real.exp (4 * βp * k0) with hKQ
  have hKQ0 : 0 < KQ := Real.exp_pos _
  refine ⟨KQ * (2 * Cqr + 16 * (cch * Cp * Cb ^ 2)), max (max Nt Nr) (max Nq Nd), ?_⟩
  intro ρ hρ hA β hβ1 hβ2 N hN hN2 B h hm hsym hbd ν hν
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hNt : Nt ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNr : Nr ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNq : Nq ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNd : Nd ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hB : 0 ≤ B := wl2_B_nonneg (by omega) hbd
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hNn : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hNn
  have hNR0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  -- the field ensemble
  obtain ⟨hK, hℓ, hℓle, hfield, hQeq⟩ := hQ ρ hρ hA β hβpos.le (n + 1) hNn
  set VK : WeakPotential μ := wlPot hK hCK0 hfield with hVKdef
  have hVK : VK.q = fun x y : Euc d => sphericalLogKernel x y := rfl
  have hQeq' : HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β μ =
      fieldLaw VK (wl_Qfield μ β (n + 1)) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) := hQeq VK hVK
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβpos.le hNR0.le
  haveI hQp : IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β μ) := by
    rw [hQeq']
    exact (fieldSpec (V := VK) hfield hlam (n + 1)).isProb
  set Q := HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β μ with hQ'
  -- the weak reference potential
  have hqq := hCqq ρ hρ hA M hM1
  have hzero : IsField μ (fun _ : Euc d => (0 : ℝ)) 0 0 :=
    ⟨measurable_const, fun _ => le_rfl, integrable_const _, by simp⟩
  set VQ : WeakPotential μ := wlPot hqq (mul_nonneg hCqq0 (Real.rpow_nonneg (Nat.cast_nonneg M) _)) hzero
    with hVQdef
  have hVQ : VQ.q = wl_qm (d := d) M := rfl
  have hz : WlFam 0 β (n + 1) (n + 1) (fun i : Fin 0 => (i.elim0 : ℝ)) (fun i : Fin 0 => (i.elim0 : Euc d))
      (fun _ => (0 : ℝ)) :=
    ⟨hNn, le_rfl, hβpos.le, by norm_num, fun a => a.elim0, fun a => a.elim0, measurable_const,
      fun x => by simp⟩
  have hPQ : wl5_Pens μ VK (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun _ => (0 : ℝ))
      (fun i : Fin 0 => (i.elim0 : ℝ)) (fun i : Fin 0 => (i.elim0 : Euc d)) = Q := by
    rw [hQeq']
    unfold wl5_Pens
    congr 1
    funext x
    simp only [wl4b_psi, wl4b_g, wl_Qfield, Finset.univ_eq_empty, Finset.sum_empty, mul_zero,
      sub_zero, add_zero]
    have hN0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := hNR0.ne'
    field_simp
    ring
  have hRN5 : wl5_RN μ VQ M β (n + 1) (n + 1) (fun _ => (0 : ℝ)) (fun i : Fin 0 => (i.elim0 : ℝ))
      (fun i : Fin 0 => (i.elim0 : Euc d)) = wl9_RN μ M VQ β (n + 1) := rfl
  obtain ⟨-, -, hvt⟩ := htr' ρ hρ hA β hβpos hβ2 (n + 1) (n + 1) hNt (by omega) 0
    (fun i : Fin 0 => (i.elim0 : ℝ)) (fun i : Fin 0 => (i.elim0 : Euc d)) (fun _ => (0 : ℝ)) hz VK VQ hVK hVQ
  obtain ⟨V', hκ, hRN⟩ := hdd ρ hρ hA β hβpos hβ2 (n + 1) hNd VQ hVQ
  obtain ⟨-, θR, hθRm, hθRb, hθRπ, hθR2m, hθR2, -⟩ := hr ρ hρ hA β hβpos hβ2 (n + 1) hNr VQ hVQ
  obtain ⟨hθNm, hπN, hsup, hθN2m, hθN2⟩ := hmarg ρ hρ hA β hβpos hβ2 (n + 1) hN2
  set R := pinnedLaw V' (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) with hR
  haveI hRp : IsProbabilityMeasure R := isProb_pinnedLaw V' hlam (n + 1) _
  -- the first marginal of the reference
  have hπ0 : R.map (fun X => X 0) = μ.withDensity (fun x => ENNReal.ofReal (θR x)) := by
    rw [← hRN, ← wl6_firstMarginal_def (d := d) n]
    exact hθRπ
  -- the density of `ν`
  have hθNb : ∀ x, 0 ≤ wl_theta μ β (n + 1) x ∧ wl_theta μ β (n + 1) x ≤ Cp := by
    intro x
    obtain ⟨h0, h1⟩ := hsup x
    refine ⟨h0, h1.trans ?_⟩
    have hr1 : (1 + ‖x‖ ^ 2) ^ (-(β / (2 * ((n + 1 : ℕ) : ℝ)))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖])
        (by have : 0 ≤ β / (2 * ((n + 1 : ℕ) : ℝ)) := by positivity
            linarith)
    calc Cm * (1 + ‖x‖ ^ 2) ^ (-(β / (2 * ((n + 1 : ℕ) : ℝ)))) ≤ Cm * 1 :=
          mul_le_mul_of_nonneg_left hr1 (by linarith)
      _ ≤ Cp := by rw [mul_one]; exact le_max_right _ _
  have hνfacts : ∃ φ : Euc d → ℝ, Measurable φ ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ Cp) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (φ x)) ∧ IsProbabilityMeasure ν ∧
      eLpNorm (fun y => φ y - θR y) 2 μ ≤ ENNReal.ofReal (Cb / ((n + 1 : ℕ) : ℝ)) := by
    rcases hν with rfl | rfl
    · refine ⟨fun _ => 1, measurable_const, fun x => ⟨zero_le_one, hCp1⟩, by simp, inferInstance, ?_⟩
      have e : (fun y => (fun _ : Euc d => (1 : ℝ)) y - θR y) = -(fun x => θR x - 1) := by
        funext y; simp
      rw [e, eLpNorm_neg]
      refine hθR2.trans (ENNReal.ofReal_le_ofReal ?_)
      exact div_le_div_of_nonneg_right (by rw [hCb]; linarith [le_max_left Cr Cm, hCm1]) hNR0.le
    · refine ⟨wl_theta μ β (n + 1), hθNm, hθNb, hπN, wr14a_isProb_firstMarginal hNn _, ?_⟩
      have e : (fun y => wl_theta μ β (n + 1) y - θR y) =
          (fun x => wl_theta μ β (n + 1) x - 1) - fun x => θR x - 1 := by
        funext y; simp
      rw [e]
      refine (eLpNorm_sub_le (by norm_num)).trans ?_
      refine (add_le_add hθN2 hθR2).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [hCb]; ring
  obtain ⟨φ, hφm, hφb, rfl, hνp, hφL2⟩ := hνfacts
  have hF : Measurable (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X
      (μ.withDensity fun x => ENNReal.ofReal (φ x))) := wr14a_measurable_D hm _
  -- step 1: the transfer `Q → R_N`
  have step1 : ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
        HRS.Whole.centeredPairFunctional h X (μ.withDensity fun x => ENNReal.ofReal (φ x))) Q ≤
      ENNReal.ofReal KQ * (((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
        HRS.Whole.centeredPairFunctional h X (μ.withDensity fun x => ENNReal.ofReal (φ x))) R) := by
    have h1 := hvt _ (hF.aestronglyMeasurable (μ := wl5_RN μ VQ M β (n + 1) (n + 1) (fun _ => (0 : ℝ))
      (fun i : Fin 0 => (i.elim0 : ℝ)) (fun i : Fin 0 => (i.elim0 : Euc d))))
    rw [hPQ, hRN5, hRN] at h1
    have h2 : ENNReal.ofReal (Real.exp (4 * (((n + 1 : ℕ) : ℝ) * (β / ((n + 1 : ℕ) : ℝ))) * wl_k0 M)) ≤
        ENNReal.ofReal KQ := by
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have e : ((n + 1 : ℕ) : ℝ) * (β / ((n + 1 : ℕ) : ℝ)) = β := by field_simp
      rw [e]
      have : β * k0 ≤ βp * k0 := mul_le_mul_of_nonneg_right hβ2 hk0
      linarith
    calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
          HRS.Whole.centeredPairFunctional h X (μ.withDensity fun x => ENNReal.ofReal (φ x))) Q
        ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (Real.exp (4 * (((n + 1 : ℕ) : ℝ) *
            (β / ((n + 1 : ℕ) : ℝ))) * wl_k0 M)) * evariance (fun X : Fin (n + 1) → Euc d =>
              HRS.Whole.centeredPairFunctional h X (μ.withDensity fun x => ENNReal.ofReal (φ x))) R) := by
          gcongr
      _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal KQ * evariance (fun X : Fin (n + 1) → Euc d =>
              HRS.Whole.centeredPairFunctional h X (μ.withDensity fun x => ENNReal.ofReal (φ x))) R) := by
          gcongr
      _ = _ := by ring
  -- step 2: change of centering
  have step2 := wr14a_evariance_quad_change (N := n + 1) V' hβpos.le hκ hm (μ.withDensity fun x => ENNReal.ofReal (φ x))
  rw [hπ0] at step2
  -- step 3: the reference estimate
  have step3 := hqr ρ hρ hA β hβpos hβ2 (n + 1) hNq VQ hVQ B h hm hsym hbd
  rw [hθRπ, hRN] at step3
  -- step 4: the change term
  have step4 := hch ρ hρ hA hCp0 hm hsym hbd hφm hθRm hφb
    (fun x => ⟨(hθRb x).1, (hθRb x).2.trans (le_max_left _ _)⟩)
  have step5 : (eLpNorm (fun y => φ y - θR y) 2 μ) ^ 2 ≤ ENNReal.ofReal ((Cb / ((n + 1 : ℕ) : ℝ)) ^ 2) := by
    refine (pow_le_pow_left' hφL2 2).trans ?_
    rw [← ENNReal.ofReal_pow (by positivity)]
  have hcomb := HRS.Quad.ofReal_comb (K := KQ) (a := Cqr * B ^ 2 / ((n + 1 : ℕ) : ℝ))
    (b := cch * Cp * B ^ 2) (c := (Cb / ((n + 1 : ℕ) : ℝ)) ^ 2) hKQ0.le (by positivity) (by positivity)
    (by positivity)
  have e2 : ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (Cqr * B ^ 2 / ((n + 1 : ℕ) : ℝ)) ) =
      ENNReal.ofReal (Cqr * B ^ 2) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNR0.le]
    congr 1; field_simp
  calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
        HRS.Whole.centeredPairFunctional h X (μ.withDensity fun x => ENNReal.ofReal (φ x))) Q
      ≤ ENNReal.ofReal KQ * (((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
          HRS.Whole.centeredPairFunctional h X (μ.withDensity fun x => ENNReal.ofReal (φ x))) R) := step1
    _ ≤ ENNReal.ofReal KQ * (2 * ENNReal.ofReal (Cqr * B ^ 2 / ((n + 1 : ℕ) : ℝ)) +
          16 * (ENNReal.ofReal (cch * Cp * B ^ 2) * ENNReal.ofReal ((Cb / ((n + 1 : ℕ) : ℝ)) ^ 2))) := by
        refine mul_le_mul' le_rfl (step2.trans ?_)
        refine add_le_add ?_ ?_
        · -- `2 N Var_R(D(h;π^R)) ≤ 2 Cqr B² / N`
          have h3 : ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d =>
              HRS.Whole.centeredPairFunctional h X (μ.withDensity fun x => ENNReal.ofReal (θR x))) R ≤
              ENNReal.ofReal (Cqr * B ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
            refine (mul_le_mul' le_rfl step3).trans (le_of_eq ?_)
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNR0.le]
            congr 1; field_simp
          rw [mul_assoc]
          exact mul_le_mul' le_rfl h3
        · exact mul_le_mul' le_rfl (step4.trans (mul_le_mul' le_rfl step5))
    _ = ENNReal.ofReal (KQ * (2 * (Cqr * B ^ 2 / ((n + 1 : ℕ) : ℝ)) +
          16 * ((cch * Cp * B ^ 2) * (Cb / ((n + 1 : ℕ) : ℝ)) ^ 2))) := hcomb
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hu0 : 0 < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
        have hu1 : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 := by rw [div_le_one hNR0]; exact hNR
        have e1 : Cqr * B ^ 2 / ((n + 1 : ℕ) : ℝ) = Cqr * B ^ 2 * (1 / ((n + 1 : ℕ) : ℝ)) := by ring
        have e2 : (cch * Cp * B ^ 2) * (Cb / ((n + 1 : ℕ) : ℝ)) ^ 2 =
            (cch * Cp * Cb ^ 2 * B ^ 2) * ((1 / ((n + 1 : ℕ) : ℝ)) * (1 / ((n + 1 : ℕ) : ℝ))) := by
          field_simp
        have e3 : KQ * (2 * Cqr + 16 * (cch * Cp * Cb ^ 2)) * B ^ 2 / ((n + 1 : ℕ) : ℝ) =
            KQ * (2 * Cqr + 16 * (cch * Cp * Cb ^ 2)) * B ^ 2 * (1 / ((n + 1 : ℕ) : ℝ)) := by ring
        rw [e1, e2, e3]
        have h4 : (1 / ((n + 1 : ℕ) : ℝ)) * (1 / ((n + 1 : ℕ) : ℝ)) ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
          mul_le_of_le_one_left hu0.le hu1
        have h5 : (cch * Cp * Cb ^ 2 * B ^ 2) * ((1 / ((n + 1 : ℕ) : ℝ)) * (1 / ((n + 1 : ℕ) : ℝ))) ≤
            (cch * Cp * Cb ^ 2 * B ^ 2) * (1 / ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        have key : 2 * (Cqr * B ^ 2 * (1 / ((n + 1 : ℕ) : ℝ))) +
            16 * ((cch * Cp * Cb ^ 2 * B ^ 2) * ((1 / ((n + 1 : ℕ) : ℝ)) * (1 / ((n + 1 : ℕ) : ℝ)))) ≤
            (2 * Cqr + 16 * (cch * Cp * Cb ^ 2)) * B ^ 2 * (1 / ((n + 1 : ℕ) : ℝ)) := by
          nlinarith [h5]
        calc _ ≤ KQ * ((2 * Cqr + 16 * (cch * Cp * Cb ^ 2)) * B ^ 2 * (1 / ((n + 1 : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left key hKQ0.le
          _ = _ := by ring

end HRS.MS.Wl
