import HRS.MS.WlSmlAux1
import HRS.MS.WlCalAux1
import HRS.MS.WrPoleAux1

/-!
# WL-4b (part 2): weak entropy, total variation and smallness of the calibration field, uniformly over the family

Packet WL-4b of `docs/WR_LOG_PLAN.md` (Step 6, S3.5 `r2_log_static`), namespace `HRS.MS.Wl`, helper prefix
`wl4b_`.  Infrastructure lemmas, not manuscript rows.  Notation: `μ = withDensityReal ρ`, `K = sphericalLogKernel`,
`ℓ = logWeight`, `q_M = wl_qm M`, `Ψ = wl_psi M`, `Ξ = Xi μ Ψ`.

**The family `F`** (`WlFam`, Step 5 of the plan).  Parameters `C0 ≥ 0`, `β ≥ 0`, `N`, `n` (the number of free
coordinates, `1 ≤ n ≤ N`; in the application `N - 2 ≤ n ≤ N`), `p ≤ 2` poles `z_a ∈ ℝ^d` (arbitrary positions) with
weights `t_a ∈ [0,1]`, and a measurable one-body field `v` with `‖v‖_∞ ≤ C0/N`.  With `λ = β/N` the reference
ensemble is
`R0 = fieldLaw V ψ λ n`, `V.q = q_M` (the weak potential of the tail kernel; only `V.q` enters the law),
`ψ = wl4b_psi = (nλ) · rowIntE q_M μ + h_N + v - λ ∑_a t_a K(·, z_a)`, `h_N = -λ ℓ`,
i.e. the weak ensemble of the TeX (pair interaction and background `nλ q_M μ` with the tail kernel, the full
fields of `eq:r2-log-general-field`, poles with the original kernel `K`).  (The TeX normalisation of the background
by `nλ` instead of `β` differs from `β` by `(N-n) λ rowIntE ≤ 2 C/N`, absorbed into `v`.)

Main results (constants `∃ C` quantified after `d, A, βp, C0, M` and before `ρ, β, N, n, poles, v`, hence
uniform over the family and over `ρ`):
* `wl_klDiv`: `R0` is a probability measure and `KL(R0 ‖ μ^{⊗n}) ≤ C log(e n)`;
* `wl_tv`: `‖R0^{(1)} - μ‖_TV ≤ √(C log(e n)/n/2)`;
* `wl_field_small`: there is `N0` such that for `N ≥ N0`, `N ≤ n + 2`, the calibration parameter
  `t = wl4_tN (1/n) (nλ) μ Ψ R0` (minimiser of `t ↦ (1/n) log R0[e^{∑ ⟪t, Ξ(x_i)⟫}] + ‖t‖²/(2nλ)`, WL-4a) satisfies
  `|⟪t, Ξ x⟫| ≤ 1` for every `x`, for every member of the family and every `ρ` (`β ∈ (0, βp]`);
* `wl_second_moment`: for `M ≥ M0(d, A, βp, C0)` and `V.γ ≤ C_q M^{-d/2}` (`wl4b_Cq`; Dobrushin smallness),
  `R0[‖μ_n(Ξ)‖²] ≤ C log(e n)/n` (`wr13b_field_second_moment_H`, `wl_tv`).

Adjustments with respect to the plan (documented, harmless): the family field has the background
`(nλ) q_M*μ` of the TeX (not `β q_M*μ`); `wl_energy_lower` is stated for injective `X`; the existence of a
calibration minimiser is not assumed (`wl4_tN` is the choice-function minimiser of WL-4a, which exists by
`wl4_exists_calib_min`; only its norm bound `wl4_tN_norm_le_empXi` is used); the poles carry the original kernel `K`
(they are `K`-poles in the TeX), the pair interaction and background carry `q_M`; the weak potential `V` enters only
through `V.q = q_M` (and `V.γ` in `wl_second_moment`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-! ### The family -/

/-- The one-body field `g = h_N + v - λ ∑_a t_a K(·, z_a)`, `h_N = -λ ℓ`. -/
def wl4b_g (lam : ℝ) (v : Euc d → ℝ) {p : ℕ} (t : Fin p → ℝ) (z : Fin p → Euc d) (x : Euc d) : ℝ :=
  -(lam * logWeight x) + v x - lam * ∑ a, t a * sphericalLogKernel x (z a)

/-- The full one-body field `ψ = (nλ) rowIntE q μ + g`. -/
def wl4b_psi (μ : Measure (Euc d)) (q : Euc d → Euc d → ℝ) (lam : ℝ) (n : ℕ) (v : Euc d → ℝ) {p : ℕ}
    (t : Fin p → ℝ) (z : Fin p → Euc d) : Euc d → ℝ :=
  fun x => ((n : ℝ) * lam) * rowIntE q μ x + wl4b_g lam v t z x

/-- **The family `F`**: `1 ≤ n ≤ N`, `β ≥ 0`, `p ≤ 2` poles with weights in `[0,1]`, a measurable field with
`‖v‖_∞ ≤ C0/N`. -/
structure WlFam (C0 β : ℝ) (N n : ℕ) {p : ℕ} (t : Fin p → ℝ) (z : Fin p → Euc d) (v : Euc d → ℝ) : Prop where
  one_le : 1 ≤ n
  n_le : n ≤ N
  β_nonneg : 0 ≤ β
  p_le : p ≤ 2
  t_nonneg : ∀ a, 0 ≤ t a
  t_le : ∀ a, t a ≤ 1
  v_meas : Measurable v
  v_bdd : ∀ x, |v x| ≤ C0 / N

lemma WlFam.C0_nonneg {C0 β : ℝ} {N n : ℕ} {p : ℕ} {t : Fin p → ℝ} {z : Fin p → Euc d} {v : Euc d → ℝ}
    (h : WlFam C0 β N n t z v) : 0 ≤ C0 := by
  have h0 := (abs_nonneg (v 0)).trans (h.v_bdd 0)
  have hN : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le h.one_le h.n_le
  exact (div_nonneg_iff.1 h0).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hN))

lemma WlFam.sum_t_le {C0 β : ℝ} {N n : ℕ} {p : ℕ} {t : Fin p → ℝ} {z : Fin p → Euc d} {v : Euc d → ℝ}
    (h : WlFam C0 β N n t z v) : ∑ a, t a ≤ 2 := by
  calc ∑ a, t a ≤ ∑ _a : Fin p, (1 : ℝ) := Finset.sum_le_sum fun a _ => h.t_le a
    _ = p := by simp
    _ ≤ 2 := by exact_mod_cast h.p_le

/-- `g` is an `IsField` with `M = b` and `M₁ = λ m + b + λ (∑ t) C_K`. -/
lemma wl4b_isField_g {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {CK : ℝ}
    (hK : EWeakKernel μ CK (fun x y : Euc d => sphericalLogKernel x y)) (hCK : 0 ≤ CK)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {m : ℝ} (hm : ∫ x, logWeight x ∂μ ≤ m) {lam : ℝ}
    (hlam : 0 ≤ lam) {v : Euc d → ℝ} (hv : Measurable v) {b : ℝ} (hb : ∀ x, |v x| ≤ b) {p : ℕ}
    (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) (z : Fin p → Euc d) :
    IsField μ (wl4b_g lam v t z) b (lam * m + b + lam * ((∑ a, t a) * CK)) := by
  have h1 := wl_isField_negMul (μ := μ) wl2_logWeight_measurable wl2_logWeight_nonneg hℓ hlam hm
  have h2 := wl_isField_bdd (μ := μ) hv hb
  have h3 := wl_isField_poles hK hCK t ht z hlam
  have h := wl_isField_add (wl_isField_add h1 h2) h3
  refine wl_isField_mono (wl_isField_congr h fun x => ?_) (le_of_eq (by ring)) (le_of_eq (by ring))
  simp only [wl4b_g]
  ring

/-- The constants of the family: kernel row bounds, `∫ ℓ`, and the lower bound of the energy of `q_M`. -/
theorem wl4b_data (hd : 2 ≤ d) (A : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ∃ CK Cl CE Cq : ℝ, 0 ≤ CK ∧ 0 ≤ Cl ∧ 0 ≤ CE ∧ 0 ≤ Cq ∧ ∀ ρ : Euc d → ℝ,
      HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
        EWeakKernel (HRS.Whole.withDensityReal ρ) CK (fun x y : Euc d => sphericalLogKernel x y) ∧
        Integrable (logWeight : Euc d → ℝ) (HRS.Whole.withDensityReal ρ) ∧
        ∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ) ≤ Cl ∧
        EWeakKernel (HRS.Whole.withDensityReal ρ) (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) (wl_qm (d := d) M) ∧
        ∀ n : ℕ, 1 ≤ n → ∀ X : Fin n → Euc d, Function.Injective X →
          -(CE * Real.log (Real.exp 1 * n)) ≤
            (n : ℝ) * HRS.Whole.pairEnergy (wl_qm M) X (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨CK, hCK0, hCK⟩ := wl_K_weak hd A
  obtain ⟨Cl, hCl⟩ := wl_logmoment hd A 1
  obtain ⟨CE, hCE0, hCE⟩ := wl_energy_lower hd A M
  obtain ⟨Cq, hCq0, hCq⟩ := wl_qm_weak hd A
  refine ⟨CK, max Cl 0, CE, Cq, hCK0, le_max_right _ _, hCE0, hCq0, fun ρ hρ hA => ?_⟩
  obtain ⟨hℓ, hℓle⟩ := hCl ρ hρ hA
  simp only [pow_one] at hℓ hℓle
  exact ⟨hCK ρ hρ hA, hℓ, hℓle.trans (le_max_left _ _), hCq ρ hρ hA M hM, hCE ρ hρ hA⟩


/-! ### Weak entropy -/

/-- `log (e n) ≥ 1` for `n ≥ 1`. -/
lemma wl4b_log_en_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ Real.log (Real.exp 1 * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_mul (Real.exp_pos 1).ne' hn0.ne', Real.log_exp]
  have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  linarith

/-- **`wl_klDiv`.**  The weak reference of the family is a probability measure and
`KL(R0 ‖ μ^{⊗n}) ≤ C log(e n)`, with `C` depending on `d, A, βp, C0, M` only. -/
theorem wl_klDiv (hd : 2 ≤ d) (A βp C0 : ℝ) (M : ℕ) (hM : 1 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, β ≤ βp →
      ∀ N n : ℕ, ∀ (p : ℕ) (t : Fin p → ℝ) (z : Fin p → Euc d) (v : Euc d → ℝ),
        WlFam C0 β N n t z v → ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ), V.q = wl_qm M →
          IsProbabilityMeasure (fieldLaw V (wl4b_psi (HRS.Whole.withDensityReal ρ) (wl_qm M) (β / N) n
            v t z) (β / N) n) ∧
          klDiv (fieldLaw V (wl4b_psi (HRS.Whole.withDensityReal ρ) (wl_qm M) (β / N) n v t z)
              (β / N) n) (Measure.pi fun _ : Fin n => HRS.Whole.withDensityReal ρ) ≤
            ENNReal.ofReal (C * Real.log (Real.exp 1 * n)) := by
  obtain ⟨CK, Cl, CE, Cq, hCK0, hCl0, hCE0, hCq0, hdat⟩ := wl4b_data hd A M hM
  set βq : ℝ := max βp 0 with hβq
  have hβq0 : 0 ≤ βq := le_max_right _ _
  refine ⟨βq * CE + 2 * max C0 0 + βq * Cl + 2 * βq * CK, by positivity,
    fun ρ hρ hA β hβp N n p t z v hF => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  intro V hV
  obtain ⟨hK, hℓ, hℓle, hq, hE⟩ := hdat ρ hρ hA
  have hn := hF.one_le
  have hnN := hF.n_le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hn hnN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hβ0 := hF.β_nonneg
  set lam : ℝ := β / N with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ0 hN0.le
  have haM : 0 ≤ Cq * (M : ℝ) ^ (-((d : ℝ) / 2)) :=
    mul_nonneg hCq0 (Real.rpow_nonneg (Nat.cast_nonneg M) _)
  have hg := wl4b_isField_g hK hCK0 hℓ hℓle hlam hF.v_meas hF.v_bdd t hF.t_nonneg z
  have hnl : 0 ≤ (n : ℝ) * lam := by positivity
  have hψ : IsField μ (wl4b_psi μ (wl_qm M) lam n v t z) _ _ :=
    wl_isField_add (wl_isField_rowInt hq haM hnl) hg
  haveI hPr : IsProbabilityMeasure (fieldLaw V (wl4b_psi μ (wl_qm M) lam n v t z) lam n) :=
    (fieldSpec (V := V) hψ hlam n).isProb
  refine ⟨hPr, ?_⟩
  have hat : ∀ x, μ {x} = 0 := wl_atomless (by omega) ρ
  set L : ℝ := Real.log (Real.exp 1 * n) with hL
  have hL1 : 1 ≤ L := wl4b_log_en_ge_one hn
  have hA' : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => μ),
      -(CE * L) ≤ (n : ℝ) * modEnergyE (wl_qm M) y μ := by
    filter_upwards [ae_injective_pi_Euc (N := n) hat] with y hy
    exact hE n hn y (fun i j hij => by_contra fun hne => hy i j hne hij)
  have hA0 : 0 ≤ CE * L := mul_nonneg hCE0 (by linarith)
  have hkl := wl4b_klDiv_field hq haM V hV hg hlam hn hA0 hA'
  refine hkl.trans (ENNReal.ofReal_le_ofReal ?_)
  -- numerics
  have hr1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast hnN)
  have hr0 : 0 ≤ (n : ℝ) / N := by positivity
  have ha_eq : lam * n = β * ((n : ℝ) / N) := by rw [hlamdef]; ring
  have ha0 : 0 ≤ lam * n := by positivity
  have ha1 : lam * n ≤ βq := by
    rw [ha_eq]
    calc β * ((n : ℝ) / N) ≤ β * 1 := mul_le_mul_of_nonneg_left hr1 hβ0
      _ = β := mul_one _
      _ ≤ βq := hβp.trans (le_max_left _ _)
  have hS := hF.sum_t_le
  have hS0 : 0 ≤ ∑ a, t a := Finset.sum_nonneg fun a _ => hF.t_nonneg a
  have h1 : lam * n * (CE * L) ≤ βq * (CE * L) := mul_le_mul_of_nonneg_right ha1 hA0
  have h2 : (n : ℝ) * (C0 / N) ≤ max C0 0 := by
    have : (n : ℝ) * (C0 / N) = C0 * ((n : ℝ) / N) := by ring
    rw [this]
    calc C0 * ((n : ℝ) / N) ≤ max C0 0 * ((n : ℝ) / N) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hr0
      _ ≤ max C0 0 * 1 := mul_le_mul_of_nonneg_left hr1 (le_max_right _ _)
      _ = max C0 0 := mul_one _
  have h3 : lam * n * Cl ≤ βq * Cl := mul_le_mul_of_nonneg_right ha1 hCl0
  have h4 : lam * n * ((∑ a, t a) * CK) ≤ βq * (2 * CK) :=
    mul_le_mul ha1 (mul_le_mul_of_nonneg_right hS hCK0) (by positivity) hβq0
  have e : lam * n * (CE * L) + n * (C0 / N + (lam * Cl + C0 / N + lam * ((∑ a, t a) * CK))) =
      lam * n * (CE * L) + 2 * ((n : ℝ) * (C0 / N)) + lam * n * Cl + lam * n * ((∑ a, t a) * CK) := by
    ring
  rw [e]
  have hfin : βq * (CE * L) + 2 * max C0 0 + βq * Cl + βq * (2 * CK) ≤
      (βq * CE + 2 * max C0 0 + βq * Cl + 2 * βq * CK) * L := by
    have hc0 : 0 ≤ 2 * max C0 0 + βq * Cl + βq * (2 * CK) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hL1 hc0]
  linarith


/-! ### Total variation of the first marginal -/

/-- **`wl_tv`.**  `‖R0^{(1)} - μ‖_TV ≤ √(C log(e n)/n/2)` (Pinsker + entropy subadditivity, `wr12_tv_of_kl`;
`R0` is exchangeable by `wl_fieldLaw_perm`). -/
theorem wl_tv (hd : 2 ≤ d) (A βp C0 : ℝ) (M : ℕ) (hM : 1 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, β ≤ βp →
      ∀ N n : ℕ, ∀ (p : ℕ) (t : Fin p → ℝ) (z : Fin p → Euc d) (v : Euc d → ℝ),
        WlFam C0 β N n t z v → ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ), V.q = wl_qm M →
          HRS.External.Entropy.tvDist
            (HRS.Whole.firstMarginal (fieldLaw V (wl4b_psi (HRS.Whole.withDensityReal ρ) (wl_qm M) (β / N) n v t z)
              (β / N) n)) (HRS.Whole.withDensityReal ρ) ≤
            Real.sqrt (C * Real.log (Real.exp 1 * n) / n / 2) := by
  obtain ⟨C, hC0, hC⟩ := wl_klDiv hd A βp C0 M hM
  refine ⟨C, hC0, fun ρ hρ hA β hβp N n p t z v hF V hV => ?_⟩
  haveI := wl_isProb hρ
  obtain ⟨hP, hkl⟩ := hC ρ hρ hA β hβp N n p t z v hF V hV
  haveI := hP
  have hn := hF.one_le
  have hex : HRS.External.Entropy.IsExchangeable
      (fieldLaw V (wl4b_psi (HRS.Whole.withDensityReal ρ) (wl_qm M) (β / N) n v t z) (β / N) n) :=
    fun σ => wl_fieldLaw_perm V _ _ σ
  have hK : 0 ≤ C * Real.log (Real.exp 1 * n) :=
    mul_nonneg hC0 (le_trans zero_le_one (wl4b_log_en_ge_one hn))
  have h := wr12_tv_of_kl (HRS.Whole.withDensityReal ρ) _ hex hK hkl ⟨0, hn⟩
  unfold HRS.Whole.firstMarginal
  rw [dif_pos (show 0 < n from hn)]
  exact h

/-! ### Smallness of the calibration field -/

/-- `log (e n) / n → 0`. -/
lemma wl4b_log_div_tendsto :
    Tendsto (fun n : ℕ => Real.log (Real.exp 1 * n) / n) atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h2 := h1.add h
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp, id]
  rw [Real.log_mul (Real.exp_pos 1).ne' hn0.ne', Real.log_exp]
  ring

/-- Quantitative smallness: `K √(Y log(e n)/n) ≤ 1` for all large `n`. -/
lemma wl4b_exists_n0 {K Y : ℝ} (hK : 0 ≤ K) (hY : 0 ≤ Y) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      K * Real.sqrt (Y * (Real.log (Real.exp 1 * n) / n)) ≤ 1 := by
  have hδ : 0 < 1 / (K ^ 2 * Y + 1) := by positivity
  obtain ⟨n1, hn1⟩ := eventually_atTop.1 ((tendsto_order.1 wl4b_log_div_tendsto).2 _ hδ)
  refine ⟨max n1 1, le_max_right _ _, fun n hn => ?_⟩
  have hn1' : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnn : 0 ≤ Real.log (Real.exp 1 * n) / n :=
    div_nonneg (le_trans zero_le_one (wl4b_log_en_ge_one hn1')) (Nat.cast_nonneg n)
  exact wr12_final_arith hK hY hnn (hn1 n (le_trans (le_max_left _ _) hn)).le

/-- **`wl_field_small`** (field smallness uniform over the family).  For `d ≥ 2`, `A, βp, C0` and a head index
`M ≥ 1` there is `N0` such that for every probability density `ρ` with the spherical bound `A`, every
`β ∈ (0, βp]`, all `N ≥ N0` and `n` with `N ≤ n + 2`, every member of the family `WlFam C0 β N n t z v`
(at most two poles at arbitrary positions with weights in `[0,1]`, a measurable field `v`, `‖v‖_∞ ≤ C0/N`), every
weak potential `V` with `V.q = q_M`, and every `x`, the calibration field of the reference ensemble
`R0 = fieldLaw V (wl4b_psi …) (β/N) n` satisfies `|⟪t_n, Ξ x⟫| ≤ 1`, where
`t_n = wl4_tN (1/n) (n (β/N)) μ (wl_psi M) R0` is the minimiser of
`t ↦ (1/n) log R0[e^{∑ ⟪t, Ξ(x_i)⟫}] + ‖t‖²/(2 n λ)`, `λ = β/N`. -/
theorem wl_field_small (hd : 2 ≤ d) (A βp C0 : ℝ) (M : ℕ) (hM : 1 ≤ M) : ∃ N0 : ℕ,
    ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 < β → β ≤ βp →
      ∀ N n : ℕ, N0 ≤ N → N ≤ n + 2 → ∀ (p : ℕ) (t : Fin p → ℝ) (z : Fin p → Euc d) (v : Euc d → ℝ),
        WlFam C0 β N n t z v → ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ), V.q = wl_qm M →
          ∀ x : Euc d,
            |inner ℝ (wl4_tN (1 / (n : ℝ)) ((n : ℝ) * (β / N)) (HRS.Whole.withDensityReal ρ) (wl_psi M)
                (fieldLaw V (wl4b_psi (HRS.Whole.withDensityReal ρ) (wl_qm M) (β / N) n v t z) (β / N) n))
              (Xi (HRS.Whole.withDensityReal ρ) (wl_psi M) x)| ≤ 1 := by
  obtain ⟨C, hC0, hC⟩ := wl_klDiv hd A βp C0 M hM
  obtain ⟨C', hC'0, hC'⟩ := wl_tv hd A βp C0 M hM
  set B : ℝ := Real.sqrt (wl_k0 M) with hB
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  set βq : ℝ := max βp 0 with hβq
  have hβq0 : 0 ≤ βq := le_max_right _ _
  obtain ⟨n0, hn0, hnsmall⟩ := wl4b_exists_n0 (K := 4 * B ^ 2 * βq) (Y := C' / 2) (by positivity) (by positivity)
  refine ⟨n0 + 2, fun ρ hρ hA β hβ hβp N n hN hNn p t z v hF => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  intro V hV x
  obtain ⟨hP, -⟩ := hC ρ hρ hA β hβp N n p t z v hF V hV
  haveI := hP
  set R0 := fieldLaw V (wl4b_psi μ (wl_qm M) (β / N) n v t z) (β / N) n with hR0
  have hn := hF.one_le
  have hnN := hF.n_le
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hn hnN
  have hnn0 : n0 ≤ n := by omega
  have hex : HRS.External.Entropy.IsExchangeable R0 := fun σ => wl_fieldLaw_perm V _ _ σ
  have hCal := wl_psi_calFeat (d := d) M
  have hβ' : 0 < (n : ℝ) * (β / N) := by positivity
  have hc : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have h1 := wl4_tN_norm_le_empXi (μ := μ) (P := R0) hCal hn hc hβ'
  have h2 := wr12_norm_empXi_le hn μ R0 hex hCal
  have h3 := hC' ρ hρ hA β hβp N n p t z v hF V hV
  have hXi := wr12_norm_Xi_le μ hCal x
  have htv0 := HRS.External.Entropy.tvDist_nonneg (HRS.Whole.firstMarginal R0) μ
  set tv := HRS.External.Entropy.tvDist (HRS.Whole.firstMarginal R0) μ with htv
  set tN := wl4_tN (1 / (n : ℝ)) ((n : ℝ) * (β / N)) μ (wl_psi M) R0 with htN
  have hcoef : (n : ℝ) * (β / N) * (1 / (n : ℝ)) * n = (n : ℝ) * (β / N) := by
    field_simp
  rw [hcoef] at h1
  have hnl1 : (n : ℝ) * (β / N) ≤ βq := by
    have : (n : ℝ) * (β / N) = β * ((n : ℝ) / N) := by ring
    rw [this]
    have hr1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast hnN)
    calc β * ((n : ℝ) / N) ≤ β * 1 := mul_le_mul_of_nonneg_left hr1 hβ.le
      _ = β := mul_one _
      _ ≤ βq := hβp.trans (le_max_left _ _)
  have hnl0 : 0 ≤ (n : ℝ) * (β / N) := hβ'.le
  have hsq : Real.sqrt (C' * Real.log (Real.exp 1 * n) / n / 2) =
      Real.sqrt (C' / 2 * (Real.log (Real.exp 1 * n) / n)) := by
    congr 1; ring
  have hfin := hnsmall n hnn0
  calc |inner ℝ tN (Xi μ (wl_psi M) x)| ≤ ‖tN‖ * ‖Xi μ (wl_psi M) x‖ := abs_real_inner_le_norm _ _
    _ ≤ ((n : ℝ) * (β / N) * (2 * B * tv)) * (2 * B) := by
        refine mul_le_mul ?_ hXi (norm_nonneg _) (by positivity)
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hnl0)
    _ = ((n : ℝ) * (β / N)) * (4 * B ^ 2) * tv := by ring
    _ ≤ (4 * B ^ 2 * βq) * tv := by
        have : (n : ℝ) * (β / N) * (4 * B ^ 2) ≤ 4 * B ^ 2 * βq := by
          nlinarith [mul_le_mul_of_nonneg_left hnl1 (by positivity : (0 : ℝ) ≤ 4 * B ^ 2)]
        exact mul_le_mul_of_nonneg_right this htv0
    _ ≤ (4 * B ^ 2 * βq) * Real.sqrt (C' / 2 * (Real.log (Real.exp 1 * n) / n)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hsq]; exact h3
    _ ≤ 1 := hfin


/-! ### Second moment of the empirical feature statistic -/

/-- The row-bound constant `C_q` of the tail kernels `q_M` (`wl_qm_weak`), chosen once for `(d, A)`. -/
def wl4b_Cq (d : ℕ) (A : ℝ) : ℝ := if h : 2 ≤ d then (wl_qm_weak h A).choose else 0

lemma wl4b_Cq_spec (hd : 2 ≤ d) (A : ℝ) : 0 ≤ wl4b_Cq d A ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ M : ℕ, 1 ≤ M →
      EWeakKernel (HRS.Whole.withDensityReal ρ) (wl4b_Cq d A * (M : ℝ) ^ (-((d : ℝ) / 2)))
        (wl_qm (d := d) M) := by
  unfold wl4b_Cq
  rw [dif_pos hd]
  exact (wl_qm_weak hd A).choose_spec

/-- **`wl_second_moment`.**  For `M` at least a head index `M0` (depending on `d, A, βp, C0` only), the reference
ensemble of the family has `R0[‖μ_n(Ξ)‖²] ≤ C log(e n)/n`.  The Dobrushin smallness is the hypothesis of
`wr13b_field_second_moment_H`: `V.γ ≤ C_q M^{-d/2}` (`wl4b_Cq`; for `V = wlPot …` it holds with equality). -/
theorem wl_second_moment (hd : 2 ≤ d) (A βp C0 : ℝ) : ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, β ≤ βp → ∀ N n : ℕ, ∀ (p : ℕ) (t : Fin p → ℝ) (z : Fin p → Euc d) (v : Euc d → ℝ),
        WlFam C0 β N n t z v → ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ), V.q = wl_qm M →
          V.γ ≤ wl4b_Cq d A * (M : ℝ) ^ (-((d : ℝ) / 2)) →
          ∫ X, ‖empXi (HRS.Whole.withDensityReal ρ) (wl_psi M) X‖ ^ 2
              ∂(fieldLaw V (wl4b_psi (HRS.Whole.withDensityReal ρ) (wl_qm M) (β / N) n v t z) (β / N) n)
            ≤ C * Real.log (Real.exp 1 * n) / n := by
  obtain ⟨CK, hCK0, hCK⟩ := wl_K_weak hd A
  obtain ⟨Cl, hCl⟩ := wl_logmoment hd A 1
  obtain ⟨hCq0, hCq⟩ := wl4b_Cq_spec hd A
  set Cq : ℝ := wl4b_Cq d A with hCqdef
  set βq : ℝ := max βp 0 with hβq
  have hβq0 : 0 ≤ βq := le_max_right _ _
  set Cl' : ℝ := max Cl 0 with hCl'
  have hCl'0 : 0 ≤ Cl' := le_max_right _ _
  set C0' : ℝ := max C0 0 with hC0'
  have hC0'0 : 0 ≤ C0' := le_max_right _ _
  set Mf : ℝ := βq * Cq + C0' with hMf
  set Λ : ℝ := (βq * Cl' + C0' + 2 * βq * CK) + βq * Cq with hΛdef
  set Cexp : ℝ := 4 * Real.exp (Mf + Λ) * βq * Cq with hCexp
  obtain ⟨M0, hM0, hM0'⟩ := wl_exists_head (by omega : 1 ≤ d) Cexp (δ := 1 / 2) (by norm_num)
  refine ⟨M0, hM0, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := le_trans hM0 hM
  obtain ⟨C', hC'0, hC'⟩ := wl_tv hd A βp C0 M hM1
  obtain ⟨Ck, hCk0, hCk⟩ := wl_klDiv hd A βp C0 M hM1
  set B2 : ℝ := wl_k0 M with hB2
  have hB20 : 0 ≤ B2 := wl_k0_nonneg M
  refine ⟨8 * B2 + 2 * B2 * C', by positivity, fun ρ hρ hA β hβp N n p t z v hF => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  intro V hV hγ
  have hn := hF.one_le
  have hnN := hF.n_le
  haveI hNZ : NeZero n := ⟨by omega⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hn hnN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hβ0 := hF.β_nonneg
  set lam : ℝ := β / N with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ0 hN0.le
  obtain ⟨hℓ, hℓle⟩ := hCl ρ hρ hA
  simp only [pow_one] at hℓ hℓle
  have hK := hCK ρ hρ hA
  have hq := hCq ρ hρ hA M hM1
  have hrp0 : 0 ≤ (M : ℝ) ^ (-((d : ℝ) / 2)) := Real.rpow_nonneg (Nat.cast_nonneg M) _
  have hrp1 : (M : ℝ) ^ (-((d : ℝ) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hM1) (by
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith)
  have haM : 0 ≤ Cq * (M : ℝ) ^ (-((d : ℝ) / 2)) := mul_nonneg hCq0 hrp0
  have haMle : Cq * (M : ℝ) ^ (-((d : ℝ) / 2)) ≤ Cq := by nlinarith
  have hg := wl4b_isField_g hK hCK0 hℓ (hℓle.trans (le_max_left _ _) : ∫ x, logWeight x ∂μ ≤ Cl')
    hlam hF.v_meas hF.v_bdd t hF.t_nonneg z
  have hnl : 0 ≤ (n : ℝ) * lam := by positivity
  have hψ : IsField μ (wl4b_psi μ (wl_qm M) lam n v t z) _ _ :=
    wl_isField_add (wl_isField_rowInt hq haM hnl) hg
  obtain ⟨hP, -⟩ := hCk ρ hρ hA β hβp N n p t z v hF V hV
  haveI := hP
  set P0 := fieldLaw V (wl4b_psi μ (wl_qm M) lam n v t z) lam n with hP0
  -- numerical bounds
  have hr1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast hnN)
  have hr0 : 0 ≤ (n : ℝ) / N := by positivity
  have hnl_eq : (n : ℝ) * lam = β * ((n : ℝ) / N) := by rw [hlamdef]; ring
  have hnl1 : (n : ℝ) * lam ≤ βq := by
    rw [hnl_eq]
    calc β * ((n : ℝ) / N) ≤ β * 1 := mul_le_mul_of_nonneg_left hr1 hβ0
      _ = β := mul_one _
      _ ≤ βq := hβp.trans (le_max_left _ _)
  have hlam1 : lam ≤ βq := by
    have : lam = β * (1 / (N : ℝ)) := by rw [hlamdef]; ring
    have hN1 : (1 : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast le_trans hn hnN)
    rw [this]
    calc β * (1 / (N : ℝ)) ≤ β * 1 := mul_le_mul_of_nonneg_left hN1 hβ0
      _ = β := mul_one _
      _ ≤ βq := hβp.trans (le_max_left _ _)
  have hb1 : C0 / N ≤ C0' := by
    have : C0 / N = C0 * (1 / (N : ℝ)) := by ring
    have hN1 : (1 : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast le_trans hn hnN)
    have hN10 : (0 : ℝ) ≤ 1 / N := by positivity
    rw [this]
    calc C0 * (1 / (N : ℝ)) ≤ C0' * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hN10
      _ ≤ C0' * 1 := mul_le_mul_of_nonneg_left hN1 hC0'0
      _ = C0' := mul_one _
  have hγ0 : 0 ≤ V.γ := V.γ_nonneg
  have hγC : V.γ ≤ Cq := hγ.trans haMle
  have hS := hF.sum_t_le
  -- constants of `hψ`
  have hM₀ : (n : ℝ) * lam * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) + C0 / N ≤ Mf := by
    have : (n : ℝ) * lam * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) ≤ βq * Cq :=
      mul_le_mul hnl1 haMle haM hβq0
    linarith
  have hM₁ : 0 + (lam * Cl' + C0 / N + lam * ((∑ a, t a) * CK)) ≤ βq * Cl' + C0' + 2 * βq * CK := by
    have h1 : lam * Cl' ≤ βq * Cl' := mul_le_mul_of_nonneg_right hlam1 hCl'0
    have h2 : lam * ((∑ a, t a) * CK) ≤ βq * (2 * CK) :=
      mul_le_mul hlam1 (mul_le_mul_of_nonneg_right hS hCK0)
        (mul_nonneg (Finset.sum_nonneg fun a _ => hF.t_nonneg a) hCK0) hβq0
    linarith
  have hΛ : (0 + (lam * Cl' + C0 / N + lam * ((∑ a, t a) * CK))) + lam * n * V.γ ≤ Λ := by
    have h3 : lam * n * V.γ ≤ βq * Cq := by
      have : lam * n = (n : ℝ) * lam := by ring
      rw [this]
      exact mul_le_mul hnl1 hγC hγ0 hβq0
    rw [hΛdef]
    linarith
  have hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i,
      4 * Real.exp (((n : ℝ) * lam * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) + C0 / N) + Λ) * lam * V.γ ≤ 1 / 2 := by
    intro i
    have hc0 : 0 ≤ 4 * Real.exp (((n : ℝ) * lam * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) + C0 / N) + Λ) *
        lam * V.γ := mul_nonneg (mul_nonneg (by positivity) hlam) hγ0
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), nsmul_eq_mul]
    simp only [Finset.card_univ, Fintype.card_fin]
    have hcast : (((n - 1 : ℕ)) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    calc (((n - 1 : ℕ)) : ℝ) * (4 * Real.exp (((n : ℝ) * lam * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) + C0 / N) + Λ) *
          lam * V.γ) ≤ (n : ℝ) * (4 * Real.exp (((n : ℝ) * lam * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) + C0 / N) + Λ) *
          lam * V.γ) := mul_le_mul_of_nonneg_right hcast hc0
      _ = 4 * Real.exp (((n : ℝ) * lam * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) + C0 / N) + Λ) * ((n : ℝ) * lam) * V.γ := by
          ring
      _ ≤ 4 * Real.exp (Mf + Λ) * βq * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) := by
          have he : Real.exp (((n : ℝ) * lam * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) + C0 / N) + Λ) ≤
              Real.exp (Mf + Λ) := Real.exp_le_exp.2 (by linarith)
          have h4 : 4 * Real.exp (((n : ℝ) * lam * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) + C0 / N) + Λ) ≤
              4 * Real.exp (Mf + Λ) := by linarith
          calc 4 * Real.exp (((n : ℝ) * lam * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) + C0 / N) + Λ) *
                  ((n : ℝ) * lam) * V.γ
              ≤ 4 * Real.exp (Mf + Λ) * βq * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) :=
                mul_le_mul (mul_le_mul h4 hnl1 hnl (by positivity)) hγ hγ0 (by positivity)
            _ = 4 * Real.exp (Mf + Λ) * βq * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) := rfl
      _ = Cexp * (M : ℝ) ^ (-((d : ℝ) / 2)) := by rw [hCexp]; ring
      _ ≤ 1 / 2 := hM0' M hM
  -- feature data
  have hCal := wl_psi_calFeat (d := d) M
  set B : ℝ := Real.sqrt (wl_k0 M) with hB
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = B2 := Real.sq_sqrt hB20
  have hΞc : Continuous (Xi μ (wl_psi (d := d) M)) := by
    unfold Xi; exact (wl_psi_continuous M).sub continuous_const
  have hΞb : ∀ z, ‖Xi μ (wl_psi (d := d) M) z‖ ≤ 2 * B := fun z => wr12_norm_Xi_le μ hCal z
  have hmain := wr13b_field_second_moment_H (V := V) hψ hlam hΛ hrow hΞc hΞb (0 : EuclideanSpace ℝ
    (Σ j : Fin M, (Fin ((j : ℕ) + 1) → Fin (d + 2))))
  simp only [add_zero] at hmain
  -- identify with `empXi`
  have hn' : (n : ℝ) ≠ 0 := hn0.ne'
  have hemp : ∀ X : Fin n → Euc d, ‖empXi μ (wl_psi M) X‖ ^ 2 =
      (1 / (n : ℝ)) ^ 2 * ‖∑ i, Xi μ (wl_psi M) (X i)‖ ^ 2 := by
    intro X
    unfold empXi
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hint_sum : ∫ X, (‖empXi μ (wl_psi M) X‖ ^ 2) ∂P0 =
      (1 / (n : ℝ)) ^ 2 * ∫ X, (‖∑ i, Xi μ (wl_psi M) (X i)‖ ^ 2) ∂P0 := by
    simp_rw [hemp]
    exact integral_const_mul _ _
  have hmean : ∫ X, ∑ i, Xi μ (wl_psi M) (X i) ∂P0 = (n : ℝ) • ∫ X, empXi μ (wl_psi M) X ∂P0 := by
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [empXi, smul_smul]
    rw [mul_one_div_cancel hn', one_smul]
  have hex : HRS.External.Entropy.IsExchangeable P0 := fun σ => wl_fieldLaw_perm V _ _ σ
  have h2 := wr12_norm_empXi_le hn μ P0 hex hCal
  have h3 := hC' ρ hρ hA β hβp N n p t z v hF V hV
  have htv0 := HRS.External.Entropy.tvDist_nonneg (HRS.Whole.firstMarginal P0) μ
  set tv := HRS.External.Entropy.tvDist (HRS.Whole.firstMarginal P0) μ with htv
  set L : ℝ := Real.log (Real.exp 1 * n) with hL
  have hL1 : 1 ≤ L := wl4b_log_en_ge_one hn
  have htv2 : tv ^ 2 ≤ C' * L / n / 2 := by
    have hX : 0 ≤ C' * L / n / 2 := by positivity
    calc tv ^ 2 ≤ (Real.sqrt (C' * L / n / 2)) ^ 2 := pow_le_pow_left₀ htv0 h3 2
      _ = C' * L / n / 2 := Real.sq_sqrt hX
  have hnorm_mean : ‖∫ X, ∑ i, Xi μ (wl_psi M) (X i) ∂P0‖ ≤ n * (2 * B * tv) := by
    rw [hmean, norm_smul, Real.norm_eq_abs, abs_of_pos hn0]
    exact mul_le_mul_of_nonneg_left h2 hn0.le
  have hint0 : ∫ X, (‖Xi μ (wl_psi M) (X 0)‖ ^ 2) ∂P0 ≤ (2 * B) ^ 2 := by
    calc ∫ X, (‖Xi μ (wl_psi M) (X 0)‖ ^ 2) ∂P0 ≤ ∫ _X, (2 * B) ^ 2 ∂P0 :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => by positivity)
            (integrable_const _) (Filter.Eventually.of_forall fun X =>
              pow_le_pow_left₀ (norm_nonneg _) (hΞb _) 2)
      _ = (2 * B) ^ 2 := by simp
  have hsq_mean : ‖∫ X, ∑ i, Xi μ (wl_psi M) (X i) ∂P0‖ ^ 2 ≤ ((n : ℝ) * (2 * B * tv)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm_mean 2
  have hS2 : ∫ X, (‖∑ i, Xi μ (wl_psi M) (X i)‖ ^ 2) ∂P0 ≤
      2 * n * (2 * B) ^ 2 + ((n : ℝ) * (2 * B * tv)) ^ 2 := by
    refine hmain.trans ?_
    have := mul_le_mul_of_nonneg_left hint0 (by positivity : (0 : ℝ) ≤ 2 * n)
    linarith
  rw [hint_sum]
  have hfin : (1 / (n : ℝ)) ^ 2 * (2 * n * (2 * B) ^ 2 + ((n : ℝ) * (2 * B * tv)) ^ 2) =
      8 * B ^ 2 / n + 4 * B ^ 2 * tv ^ 2 := by
    field_simp
    ring
  calc (1 / (n : ℝ)) ^ 2 * ∫ X, (‖∑ i, Xi μ (wl_psi M) (X i)‖ ^ 2) ∂P0
      ≤ (1 / (n : ℝ)) ^ 2 * (2 * n * (2 * B) ^ 2 + ((n : ℝ) * (2 * B * tv)) ^ 2) :=
        mul_le_mul_of_nonneg_left hS2 (by positivity)
    _ = 8 * B ^ 2 / n + 4 * B ^ 2 * tv ^ 2 := hfin
    _ ≤ 8 * B2 / n + 4 * B2 * (C' * L / n / 2) := by
        rw [hBsq]
        have : 4 * B2 * tv ^ 2 ≤ 4 * B2 * (C' * L / n / 2) :=
          mul_le_mul_of_nonneg_left htv2 (by positivity)
        linarith
    _ ≤ (8 * B2 + 2 * B2 * C') * L / n := by
        have h8 : 8 * B2 / n ≤ 8 * B2 * L / n :=
          div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) hL1) hn0.le
        have : 4 * B2 * (C' * L / n / 2) = 2 * B2 * C' * L / n := by ring
        rw [this]
        have e : (8 * B2 + 2 * B2 * C') * L / n = 8 * B2 * L / n + 2 * B2 * C' * L / n := by ring
        rw [e]
        linarith

end HRS.MS.Wl
