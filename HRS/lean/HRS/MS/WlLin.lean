import HRS.MS.WlTrAux2

/-!
# HRS.MS.WlLin -- calibrated transfer for the family, pole-linear variance, small `N`, conjuncts 1-2 of
`r2_log_static` (WL-5, part 3)

Packet WL-5 of `docs/WR_LOG_PLAN.md` (Step 7 of the proof of `r2_log_static`).  Infrastructure lemmas, not
manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl5_`.  Notation: `μ = withDensityReal ρ`,
`K = sphericalLogKernel`, `q_M = wl_qm M`, `Ψ = wl_psi M`, `k0 = wl_k0 M`, `λ = β/N`, `b = nλ`, `n` free
coordinates, poles `z_a` with weights `t_a`, field `v` (the family `WlFam` of `WlSmlAux2`).

Ensembles (`wl5_Pens`, `wl5_R0`, `wl5_RN`).
* `P = wl5_Pens = fieldLaw V_K ψ_K λ n`, `ψ_K = wl4b_psi μ K λ n v t z`  (full kernel `K`, the pole law);
* `R0 = wl5_R0 = fieldLaw V_q ψ_q λ n`, `ψ_q = wl4b_psi μ q_M λ n v t z`  (weak reference, tail kernel);
* `R_N = wl5_RN = wl4_RN (1/n) b μ Ψ R0`  (calibrated reference of `WlCalAux1`).
For `n = N`, `p = 0`, `v = 0`: `P = Q_N = modulatedGibbs (rieszKernel d 0) N β μ` (`wl_Q_eq_fieldLaw`).

Main statements (constants `∃ M0, ∀ M ≥ M0, ∃ N0 C` quantified after `d, A, βp, C0` and before
`ρ, β, N, n, poles, v`; hypotheses `N0 ≤ N ≤ n + 2`, `0 < β ≤ βp`, `WlFam`, `V_K.q = K`, `V_q.q = q_M`):
* `wl_transfer`: `P ≤ e^{4 b k0} • R_N`; the trace `∫ ‖S_n - √n Ξ̄‖² dR_N ≤ 8 k0`; and the variance transfer
  `evariance F P ≤ e^{4 b k0} evariance F R_N` for every `F` a.e. strongly measurable for `R_N`
  (port of `WrTr:294, :359`);
* `wl_pole_linear`: `evariance (∑ f(x_i)) P ≤ C n ∫ |f|² e^{-λ ∑ a t_a K(x, z_a)} dμ` for measurable `f`
  (TeX `r2-log-pole-linear`);
* `wl_pole_linear_small`: the same bound for the finitely many small `N` (crude bound with the pole factors
  retained: drop the pair interaction and use Jensen for the normaliser);
* `wl_gibbsWellDefined`: conjunct 1 of `r2_log_static`, directly from the crude data of `WlEnsAux2`
  (no `euclidean_pressure_proof` is needed);
* `wl_static_linear`: conjunct 2 of `r2_log_static`: `evariance (linStat f) Q ≤ ofReal (C/N * ∫ f²)` for every
  `f ∈ L²(μ)` (not necessarily measurable), all `N ≥ 2`, `β ∈ [βm, βp]`.

Adjustments with respect to the plan (documented, harmless): the statements are `∃ M0 ∀ M ≥ M0` (the head
index `M` is chosen by the consumer); the weak potentials `V_K`, `V_q` are arbitrary with the stated `V.q`
(the ensembles depend on `V` only through `V.q`); the poles `t_a ∈ [0,1]` with weights are part of the field.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-! ### The three ensembles of the family -/

/-- `P`: the pole law with the full kernel `K` and the family field. -/
def wl5_Pens (μ : Measure (Euc d)) (VK : WeakPotential μ) (lam : ℝ) (n : ℕ) (v : Euc d → ℝ) {p : ℕ}
    (t : Fin p → ℝ) (z : Fin p → Euc d) : Measure (Fin n → Euc d) :=
  fieldLaw VK (wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) lam n v t z) lam n

/-- `R0`: the weak reference with the tail kernel `q_M` and the same field. -/
def wl5_R0 (μ : Measure (Euc d)) (VQ : WeakPotential μ) (M : ℕ) (lam : ℝ) (n : ℕ) (v : Euc d → ℝ)
    {p : ℕ} (t : Fin p → ℝ) (z : Fin p → Euc d) : Measure (Fin n → Euc d) :=
  fieldLaw VQ (wl4b_psi μ (wl_qm (d := d) M) lam n v t z) lam n

/-- `R_N`: the calibrated reference (`wl4_RN`, `c = 1/n`, coupling `b = n λ`, `λ = β/N`). -/
def wl5_RN (μ : Measure (Euc d)) (VQ : WeakPotential μ) (M : ℕ) (β : ℝ) (N n : ℕ) (v : Euc d → ℝ)
    {p : ℕ} (t : Fin p → ℝ) (z : Fin p → Euc d) : Measure (Fin n → Euc d) :=
  wl4_RN (1 / (n : ℝ)) ((n : ℝ) * (β / N)) μ (wl_psi M) (wl5_R0 μ VQ M (β / N) n v t z)

/-! ### One member of the family -/

section Member

/-- **One member of the family.**  Under the local hypotheses (kernel/field row bounds, Dobrushin smallness
`hκ`, calibration smallness `hsmall`) the transfer, the trace, the variance transfer and the pole-linear bound
hold for `P`, `R_N`. -/
theorem wl5_member {μ : Measure (Euc d)} [IsProbabilityMeasure μ] (hat : ∀ x, μ {x} = 0)
    {CK : ℝ} (hK : EWeakKernel μ CK (fun x y : Euc d => sphericalLogKernel x y)) (hCK0 : 0 ≤ CK)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {Cl : ℝ} (hℓle : ∫ x, logWeight x ∂μ ≤ Cl)
    (hCl0 : 0 ≤ Cl) (M : ℕ) {aq Cqb : ℝ} (hq : EWeakKernel μ aq (wl_qm (d := d) M)) (haq : 0 ≤ aq)
    (haqC : aq ≤ Cqb) {C0 β βq : ℝ} (hβ : 0 < β) (hβq : β ≤ βq) {N n : ℕ} {p : ℕ}
    {t : Fin p → ℝ} {z : Fin p → Euc d} {v : Euc d → ℝ} (hF : WlFam C0 β N n t z v)
    (VK VQ : WeakPotential μ) (hVK : VK.q = fun x y : Euc d => sphericalLogKernel x y)
    (hVQ : VQ.q = wl_qm (d := d) M)
    (hsmall : ∀ x, |inner ℝ (wl4_tN (1 / (n : ℝ)) ((n : ℝ) * (β / N)) μ (wl_psi M)
      (wl5_R0 μ VQ M (β / N) n v t z)) (Xi μ (wl_psi M) x)| ≤ 1)
    {Mf M₁f : ℝ} (hMf : βq * Cqb + C0 + 1 ≤ Mf) (hM₁f : βq * Cl + C0 + 2 * βq * CK + 1 ≤ M₁f)
    (hκ : ∀ {φ : Euc d → ℝ} {M₀ M₁ : ℝ} (hφ : IsField μ φ M₀ M₁), M₀ ≤ Mf → M₁ ≤ M₁f →
      weakKappa (wlPot hq haq hφ) β ≤ 1 / 2) :
    wl5_Pens μ VK (β / N) n v t z ≤
        ENNReal.ofReal (Real.exp (4 * ((n : ℝ) * (β / N)) * wl_k0 M)) • wl5_RN μ VQ M β N n v t z ∧
      ∫ X, ‖wr11b_Sstat μ (wl_psi M) X - Real.sqrt n • ∫ Y, empXi μ (wl_psi M) Y ∂(wl5_RN μ VQ M β N n v t z)‖ ^ 2
        ∂(wl5_RN μ VQ M β N n v t z) ≤ 8 * wl_k0 M ∧
      (∀ F : (Fin n → Euc d) → ℝ, AEStronglyMeasurable F (wl5_RN μ VQ M β N n v t z) →
        evariance F (wl5_Pens μ VK (β / N) n v t z) ≤
          ENNReal.ofReal (Real.exp (4 * ((n : ℝ) * (β / N)) * wl_k0 M)) *
            evariance F (wl5_RN μ VQ M β N n v t z)) ∧
      (∀ f : Euc d → ℝ, Measurable f →
        evariance (fun X : Fin n → Euc d => ∑ i, f (X i)) (wl5_Pens μ VK (β / N) n v t z) ≤
          ENNReal.ofReal (Real.exp (4 * βq * wl_k0 M)) *
            (2 * n * (ENNReal.ofReal (Real.exp (Mf + (M₁f + βq * Cqb))) *
              ∫⁻ x, ENNReal.ofReal (Real.exp (-((β / N) * ∑ a, t a * sphericalLogKernel x (z a)))) *
                ‖f x‖ₑ ^ 2 ∂μ))) := by
  have hn := hF.one_le
  have hnN := hF.n_le
  haveI hNZ : NeZero n := ⟨by omega⟩
  have hC0 : 0 ≤ C0 := hF.C0_nonneg
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hNnat : 0 < N := lt_of_lt_of_le hn hnN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hlam : 0 ≤ β / N := div_nonneg hβ.le hN0.le
  have hlam0 : 0 < β / N := div_pos hβ hN0
  have hnl : 0 ≤ (n : ℝ) * (β / N) := mul_nonneg hn0.le hlam
  have hbpos : 0 < (n : ℝ) * (β / N) := mul_pos hn0 hlam0
  have hbq : (n : ℝ) * (β / N) ≤ βq := by
    have hr1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast hnN)
    have : (n : ℝ) * (β / N) = β * ((n : ℝ) / N) := by ring
    rw [this]
    calc β * ((n : ℝ) / N) ≤ β * 1 := mul_le_mul_of_nonneg_left hr1 hβ.le
      _ = β := mul_one _
      _ ≤ βq := hβq
  have hlamq : β / N ≤ βq := by
    have : β / N = β * (1 / (N : ℝ)) := by ring
    have hN1 : (1 : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast hNnat)
    rw [this]
    calc β * (1 / (N : ℝ)) ≤ β * 1 := mul_le_mul_of_nonneg_left hN1 hβ.le
      _ = β := mul_one _
      _ ≤ βq := hβq
  have hC0N : C0 / N ≤ C0 := by
    have : C0 / N = C0 * (1 / (N : ℝ)) := by ring
    have hN1 : (1 : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast hNnat)
    rw [this]
    calc C0 * (1 / (N : ℝ)) ≤ C0 * 1 := mul_le_mul_of_nonneg_left hN1 hC0
      _ = C0 := mul_one _
  have hCqb : 0 ≤ Cqb := haq.trans haqC
  have hβq0 : 0 ≤ βq := hβ.le.trans hβq
  have hS := hF.sum_t_le
  have hS0 : 0 ≤ ∑ a, t a := Finset.sum_nonneg fun a _ => hF.t_nonneg a
  -- fields
  have hg := wl4b_isField_g hK hCK0 hℓ hℓle hlam hF.v_meas hF.v_bdd t hF.t_nonneg z
  have hψQ : IsField μ (wl4b_psi μ (wl_qm (d := d) M) (β / N) n v t z)
      ((n : ℝ) * (β / N) * aq + C0 / N) ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK)) := by
    have := wl_isField_add (wl_isField_rowInt hq haq hnl) hg
    exact wl_isField_mono this le_rfl (by linarith)
  haveI hR0 : IsProbabilityMeasure (wl5_R0 μ VQ M (β / N) n v t z) :=
    (fieldSpec (V := VQ) hψQ hlam n).isProb
  have hΨ := wl_psi_calFeat (d := d) M
  set tt := wl4_tN (1 / (n : ℝ)) ((n : ℝ) * (β / N)) μ (wl_psi M) (wl5_R0 μ VQ M (β / N) n v t z)
    with htt
  have hψ' : IsField μ (fun x => wl4b_psi μ (wl_qm (d := d) M) (β / N) n v t z x +
        inner ℝ tt (Xi μ (wl_psi M) x))
      ((n : ℝ) * (β / N) * aq + C0 / N + 1)
      (((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK)) + 1) := by
    have := wl_isField_add hψQ (wl_isField_bdd (μ := μ)
      (v := fun x => inner ℝ tt (Xi μ (wl_psi M) x))
      (continuous_const.inner hΨ.continuous_Xi).measurable hsmall)
    exact this
  have hRN : wl5_RN μ VQ M β N n v t z = fieldLaw VQ (fun x => wl4b_psi μ (wl_qm (d := d) M) (β / N) n v t z x +
      inner ℝ tt (Xi μ (wl_psi M) x)) (β / N) n :=
    wl5_RN_eq_fieldLaw hψQ hlam hΨ 1 _ n hsmall
  have hMψ : (n : ℝ) * (β / N) * aq + C0 / N + 1 ≤ Mf := by
    have : (n : ℝ) * (β / N) * aq ≤ βq * Cqb := mul_le_mul hbq haqC haq hβq0
    linarith
  have hM₁ψ : ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK)) + 1 ≤ M₁f := by
    have h1 : (β / N) * Cl ≤ βq * Cl := mul_le_mul_of_nonneg_right hlamq hCl0
    have h2 : (β / N) * ((∑ a, t a) * CK) ≤ βq * (2 * CK) :=
      mul_le_mul hlamq (mul_le_mul_of_nonneg_right hS hCK0)
        (mul_nonneg hS0 hCK0) hβq0
    linarith
  have hκ' := hκ hψ' hMψ hM₁ψ
  haveI hνprob : IsProbabilityMeasure (wl5_RN μ VQ M β N n v t z) :=
    wl4_isProb_RN (c := 1 / (n : ℝ)) (β := (n : ℝ) * (β / N)) hΨ
  have hWu : ∀ f : Euc d → ℝ, Measurable f →
      evariance (fun X : Fin n → Euc d => ∑ i, f (X i)) (wl5_RN μ VQ M β N n v t z) ≤
        2 * n * evariance f ((wl5_RN μ VQ M β N n v t z).map (fun X => X 0)) := by
    intro f hf
    rw [hRN]
    exact wl5_wu_linear hq haq hψ' hβ.le hNnat hnN hκ' VQ hVQ f hf
  have hBsq : Real.sqrt (wl_k0 M) ^ 2 = wl_k0 M := Real.sq_sqrt (wl_k0_nonneg M)
  have htr0 : ∫ X, ‖wl5_D μ (wl_psi M) (wl5_RN μ VQ M β N n v t z) X‖ ^ 2 ∂(wl5_RN μ VQ M β N n v t z) ≤
      8 * Real.sqrt (wl_k0 M) ^ 2 := wl5_trace_le hΨ hn hWu
  have hP : wl5_Pens μ VK (β / N) n v t z = (wl5_R0 μ VQ M (β / N) n v t z).tilted
      (fun X : Fin n → Euc d => -(((n : ℝ) * (β / N)) / 2) * ‖wr11b_Sstat μ (wl_psi M) X‖ ^ 2) :=
    wl5_P_eq_tilted hat hK hCK0 M hq haq hg hlam hn VK VQ hVK hVQ
  have hPν : wl5_Pens μ VK (β / N) n v t z = (wl5_RN μ VQ M β N n v t z).tilted
      (wl5_logW ((n : ℝ) * (β / N)) μ (wl_psi M) (wl5_RN μ VQ M β N n v t z)) :=
    wl5_P_eq_RN_tilted hΨ hbpos hn hP
  have hle : wl5_Pens μ VK (β / N) n v t z ≤
      ENNReal.ofReal (Real.exp (4 * ((n : ℝ) * (β / N)) * wl_k0 M)) • wl5_RN μ VQ M β N n v t z := by
    rw [hPν]
    have := wl5_tilted_le_smul hΨ hbpos hn htr0
    rw [hBsq] at this
    exact this
  have hvt : ∀ F : (Fin n → Euc d) → ℝ, AEStronglyMeasurable F (wl5_RN μ VQ M β N n v t z) →
      evariance F (wl5_Pens μ VK (β / N) n v t z) ≤
        ENNReal.ofReal (Real.exp (4 * ((n : ℝ) * (β / N)) * wl_k0 M)) *
          evariance F (wl5_RN μ VQ M β N n v t z) := by
    intro F hFm
    rw [hPν]
    have := wl5_variance_transfer_tilted hΨ hbpos hn htr0 F hFm
    rw [hBsq] at this
    exact this
  refine ⟨hle, ?_, hvt, ?_⟩
  · have htr : ∫ X, ‖wl5_D μ (wl_psi M) (wl5_RN μ VQ M β N n v t z) X‖ ^ 2 ∂(wl5_RN μ VQ M β N n v t z) ≤
        8 * wl_k0 M := by
      rw [hBsq] at htr0
      exact htr0
    exact htr
  · intro f hf
    have hFm : Measurable fun X : Fin n → Euc d => ∑ i, f (X i) :=
      Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
    have hw : ∀ x, wl4b_psi μ (wl_qm (d := d) M) (β / N) n v t z x + inner ℝ tt (Xi μ (wl_psi M) x) ≤
        Mf - (β / N) * ∑ a, t a * sphericalLogKernel x (z a) := by
      intro x
      have h1 : rowIntE (wl_qm (d := d) M) μ x ≤ aq := hq.wr1_rowInt_le haq x
      have h2 : (n : ℝ) * (β / N) * rowIntE (wl_qm (d := d) M) μ x ≤ βq * Cqb :=
        mul_le_mul hbq (h1.trans haqC) (hq.wr1_rowInt_nonneg x) hβq0
      have h3 := wl2_logWeight_nonneg x
      have h4 : v x ≤ C0 := (le_abs_self _).trans ((hF.v_bdd x).trans hC0N)
      have h5 := (abs_le.1 (hsmall x)).2
      have h6 : 0 ≤ (β / N) * logWeight x := mul_nonneg hlam h3
      unfold wl4b_psi wl4b_g
      nlinarith
    have hΛ : (((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK)) + 1) + (β / N) * n * aq ≤
        M₁f + βq * Cqb := by
      have : (β / N) * n * aq ≤ βq * Cqb := by
        have e : (β / N) * n * aq = (n : ℝ) * (β / N) * aq := by ring
        rw [e]
        exact mul_le_mul hbq haqC haq hβq0
      linarith
    have hres := wl5_resampling_w hq haq hψ' hβ.le hNnat hnN hκ' VQ hVQ
      (w := fun x => (β / N) * ∑ a, t a * sphericalLogKernel x (z a)) hw hΛ f hf
    rw [← hRN] at hres
    refine (hvt _ hFm.aestronglyMeasurable).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) hres
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbq (by norm_num)) (wl_k0_nonneg M)

end Member

/-! ### Uniform in `ρ, β, N, n`, poles, field -/

section Main

/-- **The family theorem** (all four conclusions at once).  Constants: `∃ M0`, then for `M ≥ M0`, `∃ N0 C`
(depending on `d, A, βp, C0, M` only), uniform over `ρ`, `β ∈ (0, βp]`, `N0 ≤ N ≤ n + 2`, the poles and the
field of `WlFam`. -/
theorem wl5_main (hd : 2 ≤ d) (A βp C0 : ℝ) : ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
    ∃ N0 : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N n : ℕ, N0 ≤ N → N ≤ n + 2 →
        ∀ (p : ℕ) (t : Fin p → ℝ) (z : Fin p → Euc d) (v : Euc d → ℝ), WlFam C0 β N n t z v →
        ∀ VK VQ : WeakPotential (HRS.Whole.withDensityReal ρ),
          VK.q = (fun x y : Euc d => sphericalLogKernel x y) → VQ.q = wl_qm (d := d) M →
          wl5_Pens (HRS.Whole.withDensityReal ρ) VK (β / N) n v t z ≤
              ENNReal.ofReal (Real.exp (4 * ((n : ℝ) * (β / N)) * wl_k0 M)) •
                wl5_RN (HRS.Whole.withDensityReal ρ) VQ M β N n v t z ∧
            ∫ X, ‖wr11b_Sstat (HRS.Whole.withDensityReal ρ) (wl_psi M) X - Real.sqrt n •
                ∫ Y, empXi (HRS.Whole.withDensityReal ρ) (wl_psi M) Y
                  ∂(wl5_RN (HRS.Whole.withDensityReal ρ) VQ M β N n v t z)‖ ^ 2
              ∂(wl5_RN (HRS.Whole.withDensityReal ρ) VQ M β N n v t z) ≤ 8 * wl_k0 M ∧
            (∀ F : (Fin n → Euc d) → ℝ,
              AEStronglyMeasurable F (wl5_RN (HRS.Whole.withDensityReal ρ) VQ M β N n v t z) →
              evariance F (wl5_Pens (HRS.Whole.withDensityReal ρ) VK (β / N) n v t z) ≤
                ENNReal.ofReal (Real.exp (4 * ((n : ℝ) * (β / N)) * wl_k0 M)) *
                  evariance F (wl5_RN (HRS.Whole.withDensityReal ρ) VQ M β N n v t z)) ∧
            (∀ f : Euc d → ℝ, Measurable f →
              evariance (fun X : Fin n → Euc d => ∑ i, f (X i))
                  (wl5_Pens (HRS.Whole.withDensityReal ρ) VK (β / N) n v t z) ≤
                ENNReal.ofReal C * (n * ∫⁻ x, ENNReal.ofReal
                  (Real.exp (-((β / N) * ∑ a, t a * sphericalLogKernel x (z a)))) * ‖f x‖ₑ ^ 2
                    ∂(HRS.Whole.withDensityReal ρ))) := by
  obtain ⟨CK, hCK0, hCK⟩ := wl_K_weak hd A
  obtain ⟨Cl, hCl⟩ := wl_logmoment hd A 1
  obtain ⟨hCq0, hCq⟩ := wl4b_Cq_spec hd A
  set Cq : ℝ := wl4b_Cq d A with hCqdef
  set βq : ℝ := max βp 0 with hβq
  have hβq0 : 0 ≤ βq := le_max_right _ _
  set Cl' : ℝ := max Cl 0 with hCl'
  have hCl'0 : 0 ≤ Cl' := le_max_right _ _
  set Mf : ℝ := βq * Cq + C0 + 1 with hMfdef
  set M₁f : ℝ := βq * Cl' + C0 + 2 * βq * CK + 1 with hM₁fdef
  obtain ⟨M0, hM0, hhead⟩ := wl_kappa_head (by omega : 1 ≤ d) hCq0 βp Mf M₁f
  refine ⟨M0, hM0, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := hM0.trans hM
  obtain ⟨N0, hN0⟩ := wl_field_small hd A βp C0 M hM1
  set k0 : ℝ := wl_k0 M with hk0
  refine ⟨N0, Real.exp (4 * βq * k0) * (2 * Real.exp (Mf + (M₁f + βq * Cq))), by positivity,
    fun ρ hρ hA β hβ hβp N n hNN hNn p t z v hF => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  intro VK VQ hVK hVQ
  have hat : ∀ x, μ {x} = 0 := wl_atomless (by omega) ρ
  have hK := hCK ρ hρ hA
  obtain ⟨hℓ, hℓle⟩ := hCl ρ hρ hA
  simp only [pow_one] at hℓ hℓle
  have hq := hCq ρ hρ hA M hM1
  have hrp0 : 0 ≤ (M : ℝ) ^ (-((d : ℝ) / 2)) := Real.rpow_nonneg (Nat.cast_nonneg M) _
  have hrp1 : (M : ℝ) ^ (-((d : ℝ) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hM1) (by
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith)
  have haq : 0 ≤ Cq * (M : ℝ) ^ (-((d : ℝ) / 2)) := mul_nonneg hCq0 hrp0
  have haqC : Cq * (M : ℝ) ^ (-((d : ℝ) / 2)) ≤ Cq := by nlinarith
  have hsmall : ∀ x : Euc d, |inner ℝ (wl4_tN (1 / (n : ℝ)) ((n : ℝ) * (β / N)) μ (wl_psi M)
      (wl5_R0 μ VQ M (β / N) n v t z)) (Xi μ (wl_psi M) x)| ≤ 1 :=
    hN0 ρ hρ hA β hβ hβp N n hNN hNn p t z v hF VQ hVQ
  have hκ : ∀ {φ : Euc d → ℝ} {M₀ M₁ : ℝ} (hφ : IsField μ φ M₀ M₁), M₀ ≤ Mf → M₁ ≤ M₁f →
      weakKappa (wlPot hq haq hφ) β ≤ 1 / 2 := fun hφ h0 h1 =>
    (hhead M hM μ (wl_qm M) hq haq hφ h0 h1 β hβ.le hβp).le
  obtain ⟨h1, h2, h3, h4⟩ := wl5_member hat hK hCK0 hℓ (le_trans hℓle (le_max_left _ _)) hCl'0 M hq haq haqC
    hβ (hβp.trans (le_max_left _ _)) hF VK VQ hVK hVQ hsmall (le_refl _) (le_refl _) hκ
  refine ⟨h1, h2, h3, fun f hf => ?_⟩
  refine (h4 f hf).trans (le_of_eq ?_)
  simp only [hMfdef, hM₁fdef, hβq, hCl', hk0]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (by norm_num)]
  simp only [ENNReal.ofReal_ofNat]
  ring

/-- **`wl_transfer`** (TeX `r2-log-calibrated-transfer`, port of `WrTr:294, :359`): `P ≤ e^{4 b k0} • R_N`,
the trace bound `∫ ‖S_n - √n Ξ̄‖² dR_N ≤ 8 k0` and the variance transfer
`evariance F P ≤ e^{4 b k0} evariance F R_N` for every `F` a.e. strongly measurable for `R_N`. -/
theorem wl_transfer (hd : 2 ≤ d) (A βp C0 : ℝ) : ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
    ∃ N0 : ℕ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N n : ℕ, N0 ≤ N → N ≤ n + 2 →
        ∀ (p : ℕ) (t : Fin p → ℝ) (z : Fin p → Euc d) (v : Euc d → ℝ), WlFam C0 β N n t z v →
        ∀ VK VQ : WeakPotential (HRS.Whole.withDensityReal ρ),
          VK.q = (fun x y : Euc d => sphericalLogKernel x y) → VQ.q = wl_qm (d := d) M →
          wl5_Pens (HRS.Whole.withDensityReal ρ) VK (β / N) n v t z ≤
              ENNReal.ofReal (Real.exp (4 * ((n : ℝ) * (β / N)) * wl_k0 M)) •
                wl5_RN (HRS.Whole.withDensityReal ρ) VQ M β N n v t z ∧
            ∫ X, ‖wr11b_Sstat (HRS.Whole.withDensityReal ρ) (wl_psi M) X - Real.sqrt n •
                ∫ Y, empXi (HRS.Whole.withDensityReal ρ) (wl_psi M) Y
                  ∂(wl5_RN (HRS.Whole.withDensityReal ρ) VQ M β N n v t z)‖ ^ 2
              ∂(wl5_RN (HRS.Whole.withDensityReal ρ) VQ M β N n v t z) ≤ 8 * wl_k0 M ∧
            (∀ F : (Fin n → Euc d) → ℝ,
              AEStronglyMeasurable F (wl5_RN (HRS.Whole.withDensityReal ρ) VQ M β N n v t z) →
              evariance F (wl5_Pens (HRS.Whole.withDensityReal ρ) VK (β / N) n v t z) ≤
                ENNReal.ofReal (Real.exp (4 * ((n : ℝ) * (β / N)) * wl_k0 M)) *
                  evariance F (wl5_RN (HRS.Whole.withDensityReal ρ) VQ M β N n v t z)) := by
  obtain ⟨M0, hM0, h⟩ := wl5_main hd A βp C0
  refine ⟨M0, hM0, fun M hM => ?_⟩
  obtain ⟨N0, C, -, h'⟩ := h M hM
  exact ⟨N0, fun ρ hρ hA β hβ hβp N n hN hNn p t z v hF VK VQ hVK hVQ =>
    let r := h' ρ hρ hA β hβ hβp N n hN hNn p t z v hF VK VQ hVK hVQ
    ⟨r.1, r.2.1, r.2.2.1⟩⟩

/-- **`wl_pole_linear`** (TeX `r2-log-pole-linear`): `Var_P(∑ f(x_i)) ≤ C n ∫ |f|² e^{-λ ∑ t_a K(x, z_a)} dμ`
for measurable `f` (`evariance`, no integrability hypothesis). -/
theorem wl_pole_linear (hd : 2 ≤ d) (A βp C0 : ℝ) : ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
    ∃ N0 : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N n : ℕ, N0 ≤ N → N ≤ n + 2 →
        ∀ (p : ℕ) (t : Fin p → ℝ) (z : Fin p → Euc d) (v : Euc d → ℝ), WlFam C0 β N n t z v →
        ∀ VK VQ : WeakPotential (HRS.Whole.withDensityReal ρ),
          VK.q = (fun x y : Euc d => sphericalLogKernel x y) → VQ.q = wl_qm (d := d) M →
          ∀ f : Euc d → ℝ, Measurable f →
            evariance (fun X : Fin n → Euc d => ∑ i, f (X i))
                (wl5_Pens (HRS.Whole.withDensityReal ρ) VK (β / N) n v t z) ≤
              ENNReal.ofReal C * (n * ∫⁻ x, ENNReal.ofReal
                (Real.exp (-((β / N) * ∑ a, t a * sphericalLogKernel x (z a)))) * ‖f x‖ₑ ^ 2
                  ∂(HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨M0, hM0, h⟩ := wl5_main hd A βp C0
  refine ⟨M0, hM0, fun M hM => ?_⟩
  obtain ⟨N0, C, hC, h'⟩ := h M hM
  exact ⟨N0, C, hC, fun ρ hρ hA β hβ hβp N n hN hNn p t z v hF VK VQ hVK hVQ =>
    (h' ρ hρ hA β hβ hβp N n hN hNn p t z v hF VK VQ hVK hVQ).2.2.2⟩

end Main

/-! ### Conjunct 1: the Gibbs law is well defined -/

section Gibbs

open HRS.Whole

/-- **Conjunct 1 of `r2_log_static`** (every `β ≥ 0`, `N ≥ 1`): `GibbsWellDefined` for the pair kernel
`rieszKernel d 0 (x - y) = K(x,y) - ℓ(x) - ℓ(y)`, from the row bounds of `K`, `ℓ ∈ L¹(μ)`, the pointwise bound
`e^{-β N F_N^g} ≤ e^{β N a}` and the Jensen lower bound of the normaliser (`wl3_crude_data`). -/
theorem wl_gibbsWellDefined (hd : 2 ≤ d) (A : ℝ) : ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
    HasSphericalBound A ρ → ∀ β : ℝ, 0 ≤ β → ∀ N : ℕ, 1 ≤ N →
      HRS.Whole.GibbsWellDefined (fun x y : Euc d => rieszKernel d 0 (x - y)) N β
        (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, Cl, hC0, h⟩ := wl_Q_eq_fieldLaw hd A
  intro ρ hρ hA β hβ N hN
  haveI := wl_isProb hρ
  obtain ⟨hK, hℓ, -, -, -⟩ := h ρ hρ hA β hβ N hN
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hKo : Wr8Ok μ (fun x y : Euc d => sphericalLogKernel x y) := (hK.rowOKE hC0).wr8_ok
  have hGe : (fun x y : Euc d => rieszKernel d 0 (x - y)) =
      fun x y => sphericalLogKernel x y - (logWeight x + logWeight y) := by
    funext x y
    simp only [rieszKernel, sphericalLogKernel, ite_true]
    ring
  have hGo : Wr8Ok μ (fun x y : Euc d => rieszKernel d 0 (x - y)) := by
    rw [hGe]; exact wl3_wr8_sub hKo (wl3_wr8_L hℓ)
  obtain ⟨hw, hZ⟩ := wl3_crude_data hK hC0 hℓ hβ hN
  refine ⟨fun x => hGo.int x, hGo.prod, ?_, ?_⟩
  · have hFeq : (fun X : HRS.Whole.EucConfig d N => HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ) =
        fun X => modEnergyE (fun x y : Euc d => sphericalLogKernel x y) X μ +
          (1 / (N : ℝ) ^ 2) * ∑ i, logWeight (X i) := funext fun X => wl_energy_eq hK hC0 hℓ hN X
    have hm : Measurable (fun X : HRS.Whole.EucConfig d N => HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ) := by
      rw [hFeq]
      exact (hK.wr12_measurable_energy N).add
        ((Finset.measurable_sum _ fun i _ =>
          wl2_logWeight_measurable.comp (measurable_pi_apply i)).const_mul _)
    refine Integrable.of_bound (Real.measurable_exp.comp ((hm.const_mul (-β * N)))).aestronglyMeasurable
      (Real.exp (β * N * C)) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hw X
  · rw [HRS.Whole.pairNormalizer_diff]
    exact lt_of_lt_of_le (Real.exp_pos _) hZ

end Gibbs

/-! ### Conjunct 2: linear statistics for every `N ≥ 2` -/

section Linear

/-- Variance of a sum of i.i.d. coordinates (copy of `wr14b_evariance_sum_pi`). -/
lemma wl5_evariance_sum_pi {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (N : ℕ) :
    evariance (fun X : Fin N → Euc d => ∑ i, f (X i)) (Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (N * ∫ x, f x ^ 2 ∂μ) := by
  have hmem : ∀ i : Fin N, MemLp (fun X : Fin N → Euc d => f (X i)) 2 (Measure.pi fun _ : Fin N => μ) :=
    fun i => hf2.comp_measurePreserving (measurePreserving_eval _ i)
  have hS : MemLp (fun X : Fin N → Euc d => ∑ i, f (X i)) 2 (Measure.pi fun _ : Fin N => μ) := by
    have := memLp_finsetSum' (s := Finset.univ) (fun i _ => hmem i)
    convert this using 1
    funext X
    simp [Finset.sum_apply]
  rw [← hS.ofReal_variance_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hv := variance_sum_pi (μ := fun _ : Fin N => μ) (X := fun _ => f) (fun _ => hf2)
  have e : (fun X : Fin N → Euc d => ∑ i, f (X i)) = ∑ i : Fin N, fun ω : Fin N → Euc d => f (ω i) := by
    funext X
    simp [Finset.sum_apply]
  rw [e, hv]
  have h1 : variance f μ ≤ ∫ x, f x ^ 2 ∂μ := by
    have := variance_le_expectation_sq (μ := μ) hf.aestronglyMeasurable
    simpa using this
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N)

lemma wl5_lintegral_sq {μ : Measure (Euc d)} {f : Euc d → ℝ} (hf2 : MemLp f 2 μ) :
    ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf2.integrable_sq
    (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun z => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- **Conjunct 2 of `r2_log_static`**: `evariance (linStat f) Q_N ≤ ofReal (C/N ∫ f²)` for every `f ∈ L²(μ)`
(not necessarily measurable), all `N ≥ 2`, `β ∈ [βm, βp]`, uniformly in the probability densities with the
spherical bound.  For `N ≥ N0` it is `wl_pole_linear` with no poles (`P = Q_N`, `n = N`, `v = 0`); for
`N < N0` it is the crude bound `wl_Q_le_crude`. -/
theorem wl_static_linear (hd : 2 ≤ d) (βm βp A : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β ∈ Set.Icc βm βp, ∀ N : ℕ, 2 ≤ N → ∀ f : Euc d → ℝ,
        MemLp f 2 (HRS.Whole.withDensityReal ρ) →
        evariance (HRS.Whole.linStat f)
            (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨M0, hM0, hmain⟩ := wl_pole_linear hd A βp 0
  obtain ⟨N0, C1, hC1, h1⟩ := hmain M0 le_rfl
  obtain ⟨Cq, hCq0, hCq⟩ := wl_qm_weak hd A
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  obtain ⟨Cc, Clc, hCc0, hcrude⟩ := wl_Q_le_crude hd A
  set βq : ℝ := max βp 0 with hβq
  have hβq0 : 0 ≤ βq := le_max_right _ _
  set Cs : ℝ := Real.exp (βq * N0 * Cc + βq * max Clc 0) with hCs
  refine ⟨max C1 Cs, ?_⟩
  intro ρ hρ hA β hβmem N hN f hf2
  obtain ⟨hβ1, hβ2⟩ := hβmem
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : 1 ≤ N := by omega
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set Q := HRS.Whole.modulatedGibbs (rieszKernel d 0) N β μ with hQdef
  have hat : ∀ x, μ {x} = 0 := wl_atomless (by omega) ρ
  -- a measurable representative
  have hfm : AEStronglyMeasurable f μ := hf2.aestronglyMeasurable
  set f' : Euc d → ℝ := hfm.mk f with hf'
  have hf'm : Measurable f' := hfm.stronglyMeasurable_mk.measurable
  have hae : f =ᵐ[μ] f' := hfm.ae_eq_mk
  have hf'2 : MemLp f' 2 μ := hf2.ae_eq hae
  have hint : ∫ x, f' x ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ :=
    integral_congr_ae (hae.mono fun x hx => by simp [hx])
  have hI : 0 ≤ ∫ x, f' x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hmax1 : C1 ≤ max C1 Cs := le_max_left _ _
  -- the field ensemble
  obtain ⟨hK, hℓ, hℓle, hfield, hQeq⟩ := hQ ρ hρ hA β hβpos.le N hN1
  set VK : WeakPotential μ := wlPot hK hCK0 hfield with hVKdef
  have hVK : VK.q = fun x y : Euc d => sphericalLogKernel x y := rfl
  have hQeq' : Q = fieldLaw VK (wl_Qfield μ β N) (β / N) N := hQeq VK hVK
  have hlam : 0 ≤ β / N := div_nonneg hβpos.le hN'.le
  haveI hQprob : IsProbabilityMeasure Q := by
    rw [hQeq']
    exact (fieldSpec (V := VK) hfield hlam N).isProb
  -- the crude bound
  have hcr := hcrude ρ hρ hA β hβpos.le N hN1
  have hQac : Q ≪ Measure.pi fun _ : Fin N => μ := Measure.absolutelyContinuous_of_le_smul hcr
  have hFm : Measurable fun X : Fin N → Euc d => ∑ i, f' (X i) :=
    Finset.measurable_sum _ fun j _ => hf'm.comp (measurable_pi_apply j)
  have hS : evariance (fun X : Fin N → Euc d => ∑ i, f' (X i)) Q ≤
      ENNReal.ofReal (max C1 Cs * N * ∫ x, f' x ^ 2 ∂μ) := by
    by_cases hNN : N0 ≤ N
    · -- large `N`: `Q = P` with no poles
      have hz : WlFam 0 β N N (fun i : Fin 0 => (i.elim0 : ℝ)) (fun i : Fin 0 => (i.elim0 : Euc d))
          (fun _ => (0 : ℝ)) :=
        ⟨hN1, le_rfl, hβpos.le, by norm_num, fun a => a.elim0, fun a => a.elim0, measurable_const,
          fun x => by simp⟩
      have hqq := hCq ρ hρ hA M0 hM0
      have hzero : IsField μ (fun _ : Euc d => (0 : ℝ)) 0 0 :=
        ⟨measurable_const, fun _ => le_rfl, integrable_const _, by simp⟩
      set VQ : WeakPotential μ := wlPot hqq (mul_nonneg hCq0 (Real.rpow_nonneg (Nat.cast_nonneg M0) _))
        hzero with hVQdef
      have hVQ : VQ.q = wl_qm (d := d) M0 := rfl
      have hPQ : wl5_Pens μ VK (β / N) N (fun _ => (0 : ℝ)) (fun i : Fin 0 => (i.elim0 : ℝ))
          (fun i : Fin 0 => (i.elim0 : Euc d)) = Q := by
        rw [hQeq']
        unfold wl5_Pens
        congr 1
        funext x
        simp only [wl4b_psi, wl4b_g, wl_Qfield, Finset.univ_eq_empty, Finset.sum_empty, mul_zero,
          sub_zero, add_zero]
        have hN0 : (N : ℝ) ≠ 0 := hN'.ne'
        field_simp
        ring
      have := h1 ρ hρ hA β hβpos hβ2 N N hNN (by omega) 0 (fun i : Fin 0 => (i.elim0 : ℝ))
        (fun i : Fin 0 => (i.elim0 : Euc d)) (fun _ => (0 : ℝ)) hz VK VQ hVK hVQ f' hf'm
      rw [hPQ] at this
      simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, neg_zero, Real.exp_zero,
        ENNReal.ofReal_one, one_mul] at this
      refine this.trans ?_
      rw [wl5_lintegral_sq hf'2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
        ← ENNReal.ofReal_mul hC1]
      refine ENNReal.ofReal_le_ofReal ?_
      calc C1 * (N * ∫ x, f' x ^ 2 ∂μ) = C1 * N * ∫ x, f' x ^ 2 ∂μ := by ring
        _ ≤ max C1 Cs * N * ∫ x, f' x ^ 2 ∂μ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax1 hN'.le) hI
    · -- small `N`: the crude bound
      push Not at hNN
      have hCsN : Real.exp (β * N * Cc + β * Clc) ≤ max C1 Cs := by
        refine le_trans ?_ (le_max_right _ _)
        refine Real.exp_le_exp.2 ?_
        have hNN' : (N : ℝ) ≤ N0 := by exact_mod_cast hNN.le
        have hβ' : β ≤ βq := hβ2.trans (le_max_left _ _)
        have h2 : β * N * Cc ≤ βq * N0 * Cc :=
          mul_le_mul_of_nonneg_right (mul_le_mul hβ' hNN' hN'.le hβq0) hCc0
        have h3 : β * Clc ≤ βq * max Clc 0 :=
          calc β * Clc ≤ β * max Clc 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hβpos.le
            _ ≤ βq * max Clc 0 := mul_le_mul_of_nonneg_right hβ' (le_max_right _ _)
        linarith
      refine (evariance_le_lintegral_sub Q hFm.aestronglyMeasurable
        (∫ X, ∑ i, f' (X i) ∂(Measure.pi fun _ : Fin N => μ))).trans ?_
      calc _ ≤ ∫⁻ X, ‖∑ i, f' (X i) - ∫ X, ∑ i, f' (X i) ∂(Measure.pi fun _ : Fin N => μ)‖ₑ ^ 2
            ∂(ENNReal.ofReal (Real.exp (β * N * Cc + β * Clc)) • Measure.pi fun _ : Fin N => μ) :=
            lintegral_mono' hcr le_rfl
        _ = ENNReal.ofReal (Real.exp (β * N * Cc + β * Clc)) *
            evariance (fun X : Fin N → Euc d => ∑ i, f' (X i)) (Measure.pi fun _ : Fin N => μ) := by
            rw [lintegral_smul_measure, smul_eq_mul]
            rfl
        _ ≤ ENNReal.ofReal (Real.exp (β * N * Cc + β * Clc)) *
            ENNReal.ofReal (N * ∫ x, f' x ^ 2 ∂μ) :=
            mul_le_mul' le_rfl (wl5_evariance_sum_pi hf'm hf'2 N)
        _ ≤ ENNReal.ofReal (max C1 Cs) * ENNReal.ofReal (N * ∫ x, f' x ^ 2 ∂μ) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal hCsN) le_rfl
        _ = _ := by
            rw [← ENNReal.ofReal_mul ((Real.exp_pos _).le.trans hCsN)]
            congr 1
            ring
  -- a.e. identification of the statistics
  have hpi : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ i, f (X i) = f' (X i) := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hae
  have hlin : HRS.Whole.linStat f =ᵐ[Q] fun X : Fin N → Euc d => (N : ℝ)⁻¹ * ∑ i, f' (X i) := by
    filter_upwards [hQac.ae_le hpi] with X hX
    unfold HRS.Whole.linStat
    rw [HRS.Whole.pair_empirical hNpos]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hX i
  rw [evariance_congr hlin, evariance_mul, ← hint]
  calc ENNReal.ofReal (((N : ℝ)⁻¹) ^ 2) * evariance (fun X : Fin N → Euc d => ∑ i, f' (X i)) Q
      ≤ ENNReal.ofReal (((N : ℝ)⁻¹) ^ 2) * ENNReal.ofReal (max C1 Cs * N * ∫ x, f' x ^ 2 ∂μ) :=
        mul_le_mul' le_rfl hS
    _ = ENNReal.ofReal (max C1 Cs / N * ∫ x, f' x ^ 2 ∂μ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end Linear

/-! ### The pole law for small `N`: the crude bound with the pole factors retained -/

section Small

/-- **Jensen lower bound of the normaliser** of a field ensemble with kernel `K`, background `(nλ) K*μ` and
a one-body field `g` with `∫ g ≥ -m`: `E_π[e^{f}] ≥ e^{-n m}`. -/
theorem wl5_Z_lower {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {CK : ℝ}
    (hK : EWeakKernel μ CK (fun x y : Euc d => sphericalLogKernel x y)) (hCK0 : 0 ≤ CK)
    {g : Euc d → ℝ} {G0 m : ℝ} (hg : IsField μ g G0 m) {lam : ℝ} (hlam : 0 ≤ lam) {n : ℕ} (hn : 1 ≤ n)
    (VK : WeakPotential μ) (hVK : VK.q = fun x y : Euc d => sphericalLogKernel x y) :
    Real.exp (-((n : ℝ) * m)) ≤ ∫ y, Real.exp (∑ i, (((n : ℝ) * lam) *
      rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ (y i) + g (y i)) -
        lam * HRS.External.pairEnergy VK y) ∂(Measure.pi fun _ : Fin n => μ) := by
  set π : Measure (Fin n → Euc d) := Measure.pi fun _ : Fin n => μ with hπ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnl : 0 ≤ (n : ℝ) * lam := mul_nonneg hn0.le hlam
  have hψ := wl_isField_add (wl_isField_rowInt hK hCK0 hnl) hg
  have hokK : Wr8Ok μ (fun x y : Euc d => sphericalLogKernel x y) := (hK.rowOKE hCK0).wr8_ok
  have hEm : Measurable (fun y : Fin n → Euc d =>
      modEnergyE (fun x y : Euc d => sphericalLogKernel x y) y μ) := hK.wr12_measurable_energy n
  have hEi : Integrable (fun y : Fin n → Euc d =>
      modEnergyE (fun x y : Euc d => sphericalLogKernel x y) y μ) π := wr8_integrable_modEnergyE hokK
  have hgi : ∀ i : Fin n, Integrable (fun y : Fin n → Euc d => g (y i)) π := fun i =>
    integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) hg.integrable
  have hgm : Measurable (fun y : Fin n → Euc d => ∑ i, g (y i)) :=
    Finset.measurable_sum _ fun i _ => hg.measurable.comp (measurable_pi_apply i)
  have hsum_i : Integrable (fun y : Fin n → Euc d => ∑ i, g (y i)) π :=
    integrable_finsetSum _ fun i _ => hgi i
  set IK : ℝ := ∫ x, ∫ w, sphericalLogKernel x w ∂μ ∂μ with hIK
  have hfe : (fun y : Fin n → Euc d => ∑ i, (((n : ℝ) * lam) *
      rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ (y i) + g (y i)) -
        lam * HRS.External.pairEnergy VK y) =
      fun y => (∑ i, g (y i) - lam * (n : ℝ) ^ 2 *
        modEnergyE (fun x y : Euc d => sphericalLogKernel x y) y μ) + lam * (n : ℝ) ^ 2 / 2 * IK :=
    funext fun y => wl4b_exponent_eq VK hVK hn lam g y
  have hA : Integrable (fun y : Fin n → Euc d => ∑ i, g (y i) -
      lam * (n : ℝ) ^ 2 * modEnergyE (fun x y : Euc d => sphericalLogKernel x y) y μ) π :=
    hsum_i.sub (hEi.const_mul _)
  have hfSi : Integrable (fun y : Fin n → Euc d => ∑ i, (((n : ℝ) * lam) *
      rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ (y i) + g (y i)) -
        lam * HRS.External.pairEnergy VK y) π := by
    rw [hfe]
    exact hA.add (integrable_const _)
  have hexpi := wl5_integrable_exp_field (V := VK) hψ hlam n
  have hmean : ∫ y, (∑ i, g (y i) - lam * (n : ℝ) ^ 2 *
      modEnergyE (fun x y : Euc d => sphericalLogKernel x y) y μ) ∂π =
      (n : ℝ) * (∫ x, g x ∂μ) + lam * n / 2 * ∫ q : Euc d × Euc d,
        sphericalLogKernel q.1 q.2 ∂(μ.prod μ) := by
    rw [integral_sub hsum_i (hEi.const_mul _), integral_const_mul, integral_finsetSum _ fun i _ => hgi i,
      wr8_integral_modEnergyE hokK hn]
    have : ∀ i : Fin n, ∫ y : Fin n → Euc d, g (y i) ∂π = ∫ x, g x ∂μ :=
      fun i => integral_comp_eval (μ := fun _ : Fin n => μ) (i := i) hg.integrable.aestronglyMeasurable
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := hn0.ne'
    field_simp
    ring
  have hP0 : 0 ≤ ∫ q : Euc d × Euc d, sphericalLogKernel q.1 q.2 ∂(μ.prod μ) :=
    integral_nonneg fun q => HRS.MS.Comm.comm_log_nonneg _ _
  have hIK0 : 0 ≤ IK := integral_nonneg fun x => integral_nonneg fun w => HRS.MS.Comm.comm_log_nonneg _ _
  have hlow : -((n : ℝ) * m) ≤ ∫ y, (∑ i, ((n : ℝ) * lam * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ (y i)
      + g (y i)) - lam * HRS.External.pairEnergy VK y) ∂π := by
    rw [hfe, integral_add hA (integrable_const _), hmean]
    simp only [integral_const, smul_eq_mul]
    have h1 : -m ≤ ∫ x, g x ∂μ := hg.ge
    have h2 : 0 ≤ lam * n / 2 * ∫ q : Euc d × Euc d, sphericalLogKernel q.1 q.2 ∂(μ.prod μ) := by positivity
    have h3 : 0 ≤ lam * (n : ℝ) ^ 2 / 2 * IK := by positivity
    have h4 := mul_le_mul_of_nonneg_left h1 hn0.le
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
    linarith
  have hj := ConvexOn.map_integral_le (μ := π) convexOn_exp Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hfSi hexpi
  exact (Real.exp_le_exp.2 hlow).trans hj

/-- **Crude pole-linear bound** (one family member, explicit constant).  The density of `P` against `μ^{⊗n}`
is `≤ e^{n (M0 + m)} e^{-w(y_i)}` for every `i` (drop the nonnegative pair interaction and the other poles;
Jensen for the normaliser), hence `∫⁻ ‖∑ f(y_i)‖² dP ≤ n² e^{n(M0+m)} ∫⁻ ‖f‖² e^{-w} dμ`. -/
theorem wl5_pens_crude {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {CK : ℝ}
    (hK : EWeakKernel μ CK (fun x y : Euc d => sphericalLogKernel x y)) (hCK0 : 0 ≤ CK)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {Cl : ℝ} (hℓle : ∫ x, logWeight x ∂μ ≤ Cl)
    {C0 β : ℝ} {N n p : ℕ} {t : Fin p → ℝ} {z : Fin p → Euc d} {v : Euc d → ℝ}
    (hF : WlFam C0 β N n t z v) (VK : WeakPotential μ)
    (hVK : VK.q = fun x y : Euc d => sphericalLogKernel x y) (f : Euc d → ℝ) (hf : Measurable f) :
    evariance (fun X : Fin n → Euc d => ∑ i, f (X i)) (wl5_Pens μ VK (β / N) n v t z) ≤
      ENNReal.ofReal ((n : ℝ) * Real.exp ((n : ℝ) * (((n : ℝ) * (β / N) * CK + C0 / N) +
          ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK))))) *
        (n * ∫⁻ x, ENNReal.ofReal (Real.exp (-((β / N) * ∑ a, t a * sphericalLogKernel x (z a)))) *
          ‖f x‖ₑ ^ 2 ∂μ) := by
  set π : Measure (Fin n → Euc d) := Measure.pi fun _ : Fin n => μ with hπ
  have hn := hF.one_le
  have hnN := hF.n_le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hNnat : 0 < N := lt_of_lt_of_le hn hnN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hlam : 0 ≤ β / N := div_nonneg hF.β_nonneg hN0.le
  have hnl : 0 ≤ (n : ℝ) * (β / N) := mul_nonneg hn0.le hlam
  have hg := wl4b_isField_g hK hCK0 hℓ hℓle hlam hF.v_meas hF.v_bdd t hF.t_nonneg z
  have hψ : IsField μ (wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z)
      ((n : ℝ) * (β / N) * CK + C0 / N)
      ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK)) := by
    have := wl_isField_add (wl_isField_rowInt hK hCK0 hnl) hg
    exact wl_isField_mono this le_rfl (by linarith)
  have hPT := wl4b_fieldLaw_eq_tilted (V := VK) hψ hlam n
  haveI hP : IsProbabilityMeasure (wl5_Pens μ VK (β / N) n v t z) :=
    (fieldSpec (V := VK) hψ hlam n).isProb
  have hZ := wl5_Z_lower hK hCK0 hg hlam hn VK hVK
  have hZpos : 0 < ∫ y, Real.exp (∑ i, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y i) -
      (β / N) * HRS.External.pairEnergy VK y) ∂π := lt_of_lt_of_le (Real.exp_pos _) hZ
  -- the pole weight
  have hw0 : ∀ x, 0 ≤ (β / N) * ∑ a, t a * sphericalLogKernel x (z a) := fun x =>
    mul_nonneg hlam (Finset.sum_nonneg fun a _ =>
      mul_nonneg (hF.t_nonneg a) (HRS.MS.Comm.comm_log_nonneg _ _))
  have hwm : Measurable (fun x : Euc d => (β / N) * ∑ a, t a * sphericalLogKernel x (z a)) :=
    (Finset.measurable_sum _ fun a _ => (wl_K_measurable.comp
      (measurable_id.prodMk (measurable_const (a := z a)))).const_mul (t a)).const_mul _
  have hψw : ∀ x, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z x ≤
      ((n : ℝ) * (β / N) * CK + C0 / N) - (β / N) * ∑ a, t a * sphericalLogKernel x (z a) := by
    intro x
    have h1 : rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ x ≤ CK := hK.wr1_rowInt_le hCK0 x
    have h2 : (n : ℝ) * (β / N) * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ x ≤
        (n : ℝ) * (β / N) * CK := mul_le_mul_of_nonneg_left h1 hnl
    have h4 : v x ≤ C0 / N := (le_abs_self _).trans (hF.v_bdd x)
    have h5 : 0 ≤ (β / N) * logWeight x := mul_nonneg hlam (wl2_logWeight_nonneg x)
    unfold wl4b_psi wl4b_g
    linarith
  have hpt : ∀ (i : Fin n) (y : Fin n → Euc d),
      Real.exp (∑ i, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y i) -
        (β / N) * HRS.External.pairEnergy VK y) /
          (∫ y, Real.exp (∑ i, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y i) -
            (β / N) * HRS.External.pairEnergy VK y) ∂π) ≤
        Real.exp ((n : ℝ) * (((n : ℝ) * (β / N) * CK + C0 / N) +
          ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK)))) *
          Real.exp (-((β / N) * ∑ a, t a * sphericalLogKernel (y i) (z a))) := by
    intro i y
    rw [div_le_iff₀ hZpos]
    have h1 : ∑ i, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y i) -
        (β / N) * HRS.External.pairEnergy VK y ≤
        (n : ℝ) * ((n : ℝ) * (β / N) * CK + C0 / N) - (β / N) * ∑ a, t a * sphericalLogKernel (y i) (z a) := by
      have hle : ∀ j, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y j) ≤
          (n : ℝ) * (β / N) * CK + C0 / N := fun j => hψ.le _
      have hsplit : ∑ j, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y j) =
          wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y i) +
            ∑ j ∈ Finset.univ.erase i,
              wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y j) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      have hrest : ∑ j ∈ Finset.univ.erase i,
          wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y j) ≤
          ((n : ℝ) - 1) * ((n : ℝ) * (β / N) * CK + C0 / N) := by
        calc _ ≤ ∑ _j ∈ Finset.univ.erase i, ((n : ℝ) * (β / N) * CK + C0 / N) :=
              Finset.sum_le_sum fun j _ => hle j
          _ = ((n : ℝ) - 1) * ((n : ℝ) * (β / N) * CK + C0 / N) := by
              rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
              simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              rw [Nat.cast_sub hn]
              simp
      have h2 := mul_nonneg hlam (pairEnergy_nonneg VK y)
      have h3 := hψw (y i)
      linarith
    set Zv : ℝ := ∫ y, Real.exp (∑ i, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y i) -
            (β / N) * HRS.External.pairEnergy VK y) ∂π with hZv
    calc Real.exp (∑ i, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y i) -
          (β / N) * HRS.External.pairEnergy VK y)
        ≤ Real.exp ((n : ℝ) * ((n : ℝ) * (β / N) * CK + C0 / N) -
            (β / N) * ∑ a, t a * sphericalLogKernel (y i) (z a)) := Real.exp_le_exp.2 h1
      _ = Real.exp ((n : ℝ) * (((n : ℝ) * (β / N) * CK + C0 / N) +
          ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK)))) *
          Real.exp (-((β / N) * ∑ a, t a * sphericalLogKernel (y i) (z a))) *
          Real.exp (-((n : ℝ) * ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK)))) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ (by positivity)
  -- assemble
  have hFm : Measurable fun X : Fin n → Euc d => ∑ i, f (X i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  refine (evariance_le_lintegral_sub _ hFm.aestronglyMeasurable 0).trans ?_
  rw [show wl5_Pens μ VK (β / N) n v t z = π.tilted _ from hPT, lintegral_tilted]
  have hcs : ∀ y : Fin n → Euc d, ‖(∑ i, f (y i)) - 0‖ₑ ^ 2 ≤ (n : ℝ≥0∞) * ∑ i, ‖f (y i)‖ₑ ^ 2 := by
    intro y
    rw [sub_zero, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => f (y i))
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    calc ENNReal.ofReal ((∑ i, f (y i)) ^ 2) ≤ ENNReal.ofReal ((n : ℝ) * ∑ i, f (y i) ^ 2) :=
          ENNReal.ofReal_le_ofReal h1
      _ = (n : ℝ≥0∞) * ∑ i, ‖f (y i)‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  set gg : Euc d → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Real.exp (-((β / N) * ∑ a, t a * sphericalLogKernel x (z a)))) * ‖f x‖ₑ ^ 2 with hgg
  have hggm : Measurable gg := by
    refine (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hwm.neg)).mul ?_
    exact (hf.enorm).pow_const 2
  set dens : (Fin n → Euc d) → ℝ≥0∞ := fun y => ENNReal.ofReal
    (Real.exp (∑ i, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y i) -
      (β / N) * HRS.External.pairEnergy VK y) /
      ∫ y, Real.exp (∑ i, wl4b_psi μ (fun x y : Euc d => sphericalLogKernel x y) (β / N) n v t z (y i) -
        (β / N) * HRS.External.pairEnergy VK y) ∂π) with hdens
  calc ∫⁻ y, dens y * ‖(∑ i, f (y i)) - 0‖ₑ ^ 2 ∂π
      ≤ ∫⁻ y, dens y * ((n : ℝ≥0∞) * ∑ i, ‖f (y i)‖ₑ ^ 2) ∂π :=
        lintegral_mono fun y => mul_le_mul' le_rfl (hcs y)
    _ = (n : ℝ≥0∞) * ∑ i : Fin n, ∫⁻ y, dens y * ‖f (y i)‖ₑ ^ 2 ∂π := by
        have e : ∀ y : Fin n → Euc d, dens y * ((n : ℝ≥0∞) * ∑ i, ‖f (y i)‖ₑ ^ 2) =
            (n : ℝ≥0∞) * ∑ i, dens y * ‖f (y i)‖ₑ ^ 2 := fun y => by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        simp_rw [e]
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)]
        congr 1
        have hdm : Measurable dens := by
          rw [hdens]
          refine ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp ?_).div_const _)
          exact (Finset.measurable_sum _ fun i _ => hψ.measurable.comp (measurable_pi_apply i)).sub
            ((measurable_pairEnergy VK).const_mul _)
        rw [lintegral_finset_sum _ fun i _ => ?_]
        exact (hdm.mul ((hf.comp (measurable_pi_apply i)).enorm.pow_const 2))
    _ ≤ (n : ℝ≥0∞) * ∑ i : Fin n, ENNReal.ofReal (Real.exp ((n : ℝ) * (((n : ℝ) * (β / N) * CK + C0 / N) +
          ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK))))) * ∫⁻ x, gg x ∂μ := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => ?_)
        calc ∫⁻ y, dens y * ‖f (y i)‖ₑ ^ 2 ∂π
            ≤ ∫⁻ y, ENNReal.ofReal (Real.exp ((n : ℝ) * (((n : ℝ) * (β / N) * CK + C0 / N) +
          ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK))))) * gg (y i) ∂π := by
              refine lintegral_mono fun y => ?_
              simp only [hgg, hdens]
              rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
              exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hpt i y)) le_rfl
          _ = ENNReal.ofReal (Real.exp ((n : ℝ) * (((n : ℝ) * (β / N) * CK + C0 / N) +
          ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK))))) * ∫⁻ x, gg x ∂μ := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              congr 1
              exact (measurePreserving_eval (fun _ : Fin n => μ) i).lintegral_comp hggm
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul hn0.le, ENNReal.ofReal_natCast]
        simp only [hgg]
        ring

/-- **`wl_pole_linear_small`**: the pole-linear bound for the finitely many small `N ≤ N0` (all `n ≤ N`),
with a constant depending on `d, A, βp, C0, N0` only (crude bound, pole factors retained). -/
theorem wl_pole_linear_small (hd : 2 ≤ d) (A βp C0 : ℝ) (N0 : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, 0 ≤ β → β ≤ βp → ∀ N n : ℕ, N ≤ N0 →
        ∀ (p : ℕ) (t : Fin p → ℝ) (z : Fin p → Euc d) (v : Euc d → ℝ), WlFam C0 β N n t z v →
        ∀ VK : WeakPotential (HRS.Whole.withDensityReal ρ),
          VK.q = (fun x y : Euc d => sphericalLogKernel x y) →
          ∀ f : Euc d → ℝ, Measurable f →
            evariance (fun X : Fin n → Euc d => ∑ i, f (X i))
                (wl5_Pens (HRS.Whole.withDensityReal ρ) VK (β / N) n v t z) ≤
              ENNReal.ofReal C * (n * ∫⁻ x, ENNReal.ofReal
                (Real.exp (-((β / N) * ∑ a, t a * sphericalLogKernel x (z a)))) * ‖f x‖ₑ ^ 2
                  ∂(HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨CK, hCK0, hCK⟩ := wl_K_weak hd A
  obtain ⟨Cl, hCl⟩ := wl_logmoment hd A 1
  set βq : ℝ := max βp 0 with hβq
  have hβq0 : 0 ≤ βq := le_max_right _ _
  set Cl' : ℝ := max Cl 0 with hCl'
  have hCl'0 : 0 ≤ Cl' := le_max_right _ _
  set Kc : ℝ := βq * CK + C0 + (βq * Cl' + C0 + 2 * βq * CK) with hKc
  refine ⟨N0 * Real.exp (N0 * Kc), by positivity, fun ρ hρ hA β hβ0 hβp N n hNN p t z v hF VK hVK f hf => ?_⟩
  haveI := wl_isProb hρ
  obtain ⟨hℓ, hℓle⟩ := hCl ρ hρ hA
  simp only [pow_one] at hℓ hℓle
  have hK := hCK ρ hρ hA
  have hC0 : 0 ≤ C0 := hF.C0_nonneg
  have hn := hF.one_le
  have hnN := hF.n_le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hn hnN
  have hlam : 0 ≤ β / N := div_nonneg hβ0 hN0.le
  have hβ' : β ≤ βq := hβp.trans (le_max_left _ _)
  have hbq : (n : ℝ) * (β / N) ≤ βq := by
    have hr1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast hnN)
    have : (n : ℝ) * (β / N) = β * ((n : ℝ) / N) := by ring
    rw [this]
    calc β * ((n : ℝ) / N) ≤ β * 1 := mul_le_mul_of_nonneg_left hr1 hβ0
      _ = β := mul_one _
      _ ≤ βq := hβ'
  have hlamq : β / N ≤ βq := by
    have : β / N = β * (1 / (N : ℝ)) := by ring
    have hN1 : (1 : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast lt_of_lt_of_le hn hnN)
    rw [this]
    calc β * (1 / (N : ℝ)) ≤ β * 1 := mul_le_mul_of_nonneg_left hN1 hβ0
      _ = β := mul_one _
      _ ≤ βq := hβ'
  have hC0N : C0 / N ≤ C0 := by
    have : C0 / N = C0 * (1 / (N : ℝ)) := by ring
    have hN1 : (1 : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast lt_of_lt_of_le hn hnN)
    rw [this]
    calc C0 * (1 / (N : ℝ)) ≤ C0 * 1 := mul_le_mul_of_nonneg_left hN1 hC0
      _ = C0 := mul_one _
  have hS := hF.sum_t_le
  have hS0 : 0 ≤ ∑ a, t a := Finset.sum_nonneg fun a _ => hF.t_nonneg a
  have hC0Nn : 0 ≤ C0 / N := div_nonneg hC0 hN0.le
  have hin0 : 0 ≤ ((n : ℝ) * (β / N) * CK + C0 / N) +
      ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK)) := by
    have h1 : 0 ≤ (n : ℝ) * (β / N) * CK := by positivity
    have h2 : 0 ≤ (β / N) * ((∑ a, t a) * CK) := by positivity
    have h3 : 0 ≤ (β / N) * (∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ)) :=
      mul_nonneg hlam (integral_nonneg fun x => wl2_logWeight_nonneg x)
    have h4 : (β / N) * (∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ)) ≤ (β / N) * Cl :=
      mul_le_mul_of_nonneg_left hℓle hlam
    linarith
  have hinc : ((n : ℝ) * (β / N) * CK + C0 / N) +
      ((β / N) * Cl + C0 / N + (β / N) * ((∑ a, t a) * CK)) ≤ Kc := by
    have h1 : (n : ℝ) * (β / N) * CK ≤ βq * CK := mul_le_mul_of_nonneg_right hbq hCK0
    have h2 : (β / N) * Cl ≤ βq * Cl' :=
      calc (β / N) * Cl ≤ (β / N) * Cl' := mul_le_mul_of_nonneg_left (le_max_left _ _) hlam
        _ ≤ βq * Cl' := mul_le_mul_of_nonneg_right hlamq hCl'0
    have h3 : (β / N) * ((∑ a, t a) * CK) ≤ βq * (2 * CK) :=
      mul_le_mul hlamq (mul_le_mul_of_nonneg_right hS hCK0) (mul_nonneg hS0 hCK0) hβq0
    simp only [hKc]
    linarith
  have hnN0 : (n : ℝ) ≤ N0 := by exact_mod_cast hnN.trans hNN
  refine (wl5_pens_crude hK hCK0 hℓ hℓle hF VK hVK f hf).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  refine mul_le_mul hnN0 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
  exact mul_le_mul hnN0 hinc hin0 (by positivity)

end Small

end HRS.MS.Wl
