import HRS.MS.WlMargAux2

/-!
# HRS.MS.WlRefAux1 -- calibrated reference marginal for S3.5, part 1: set-up, sup bound, calibration identity (WL-9a)

Packet WL-9a of `docs/WR_LOG_PLAN.md` (Step 11 of the proof of `r2_log_static`, TeX eq. `r2-log-reference-marginal`).
Infrastructure lemmas, not manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl9_`.  Port of
`HRS.MS.WrRefMargAux1` from the heat split `q_τ(x-y)` to the pair kernels `K = sphericalLogKernel = k_M + q_M`.

Notation.  `μ = withDensityReal ρ`, `q = wl_qm M` (tail kernel), `k = wl_km M` (head kernel), `Ψ = wl_psi M`
(`⟪Ψ x, Ψ y⟫ = k x y`), `λ = β / N`.  The weak reference of the calibration is the field ensemble
`R0 = wl9_R0 μ M V β N = fieldLaw V ψ0 λ N` (`V.q = q`) with one-body field
`ψ0 = wl9_psi0 = β rowIntE q μ - λ ℓ` (`= wl4b_psi` with `n = N`, no poles, `v = 0`), the calibration parameter is
`t_N = wl9_tN = wl4_tN (1/N) (Nλ) μ Ψ R0` (WL-4a), the calibrated reference is
`R_N = wl9_RN = wl4_RN (1/N) (Nλ) μ Ψ R0` and `ψ_R = wl9_psiR = ψ0 + ⟪t_N, Ξ⟫`.

Contents.
* `wl9_psi0_apply`, `wl9_isField_psi0`, `wl9_isField_psiR`: the fields and their `IsField` constants
  (`M = βa + 1`, `M₁ = (β/N) m + 1` when `|⟪t_N, Ξ⟫| ≤ 1`, which is `wl_field_small` for `N ≥ N₀`);
* `wl9_RN_eq`: `R_N = fieldLaw V ψ_R λ N` (a bounded perturbation of the field);
* `wl9_theta`, `wl9_firstMarginal_RN_eq`: the exact first marginal `π^R_N = μ.withDensity θ`, `θ = wl6_theta`;
  `wl9_theta_le`: the sup bound `θ ≤ exp(M + M₁ + λ n a)` (uniform in `N`);
* `wl9_hh_eq`: the calibration identity `⟪t_N, Ξ x⟫ = -β ∫ k(x,y)(θ(y) - 1) dμ(y) + c₀` (port of `wr13e_hh_eq`);
* `wl9_D`, `wl9_log_theta_eq` (generic in the field ensemble): the insertion defect `D = A_x(1) - E X_x` and the exact
  cavity equation `log θ = ψ + D - λ n (qν) - log Z`;
* `wl9_RN_isProb`, `wl9_R0_isProb`, `wl9_theta_le_ref`: `R_N`, `R0` are probability measures, `0 < θ ≤ e^{M+M₁+λ n a}`;
* `wl9_cavity_equation` (TeX `eq:r2-log-reference-equation`): `log θ + β K(θ - 1) = (D + h_N) + β q(π - ν) + λ qν + c`.

Adjustment with respect to the plan (documented, harmless): the generic lemmas take the bound `|⟪t_N, Ξ⟫| ≤ 1`
as a hypothesis (supplied by `wl_field_small` in `WlRefAux3`); the cavity ensemble has `n = N - 1` particles and
the same field `ψ_R` (the TeX "calibration field held fixed").
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-! ### Definitions -/

/-- The one-body field of the weak reference `R0`: `ψ0 = (Nλ) rowIntE q_M μ - λ ℓ` (`wl4b_psi`, `n = N`, no poles). -/
def wl9_psi0 (μ : Measure (Euc d)) (M : ℕ) (β : ℝ) (N : ℕ) : Euc d → ℝ :=
  wl4b_psi μ (wl_qm M) (β / N) N (fun _ => 0) (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (0 : Euc d))

/-- The weak reference `R0 = fieldLaw V ψ0 (β/N) N` (`V.q = q_M`). -/
def wl9_R0 (μ : Measure (Euc d)) (M : ℕ) (V : WeakPotential μ) (β : ℝ) (N : ℕ) :
    Measure (Fin N → Euc d) :=
  fieldLaw V (wl9_psi0 μ M β N) (β / N) N

/-- The calibration parameter `t_N` (WL-4a) of `R0`. -/
def wl9_tN (μ : Measure (Euc d)) (M : ℕ) (V : WeakPotential μ) (β : ℝ) (N : ℕ) :=
  wl4_tN (1 / (N : ℝ)) ((N : ℝ) * (β / N)) μ (wl_psi M) (wl9_R0 μ M V β N)

/-- The calibrated reference `R_N`: `R0` tilted by `∑_i ⟪t_N, Ξ(x_i)⟫`. -/
def wl9_RN (μ : Measure (Euc d)) (M : ℕ) (V : WeakPotential μ) (β : ℝ) (N : ℕ) :
    Measure (Fin N → Euc d) :=
  wl4_RN (1 / (N : ℝ)) ((N : ℝ) * (β / N)) μ (wl_psi M) (wl9_R0 μ M V β N)

/-- The field of `R_N`: `ψ_R = ψ0 + ⟪t_N, Ξ⟫`. -/
def wl9_psiR (μ : Measure (Euc d)) (M : ℕ) (V : WeakPotential μ) (β : ℝ) (N : ℕ) : Euc d → ℝ :=
  fun x => wl9_psi0 μ M β N x + inner ℝ (wl9_tN μ M V β N) (Xi μ (wl_psi M) x)

lemma wl9_Nlam {N : ℕ} (hN : 0 < N) (β : ℝ) : (N : ℝ) * (β / N) = β := by
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

lemma wl9_psi0_apply {N : ℕ} (hN : 0 < N) (μ : Measure (Euc d)) (M : ℕ) (β : ℝ) (x : Euc d) :
    wl9_psi0 μ M β N x = β * rowIntE (wl_qm M) μ x - (β / N) * logWeight x := by
  unfold wl9_psi0 wl4b_psi wl4b_g
  simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero, add_zero, wl9_Nlam hN]
  ring

/-! ### Fields -/

section Fields

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {M : ℕ} {a m : ℝ}

lemma wl9_isField_psi0 (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (hm : ∫ x, logWeight x ∂μ ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 0 < N) : IsField μ (wl9_psi0 μ M β N) (β * a) (β / N * m) := by
  have h1 := wl_isField_rowInt hq ha hβ
  have h2 := wl_isField_negMul (μ := μ) (f := logWeight) (wl2_logWeight_measurable (d := d))
    (fun x => wl2_logWeight_nonneg x) hℓ (c := β / N) (div_nonneg hβ (Nat.cast_nonneg N)) hm
  have h3 := wl_isField_add h1 h2
  refine wl_isField_congr (wl_isField_mono h3 (by simp) (by simp)) fun x => ?_
  rw [wl9_psi0_apply hN]
  ring

lemma wl9_isField_psiR (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (hm : ∫ x, logWeight x ∂μ ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 0 < N) (V : WeakPotential μ)
    (hc : ∀ x, |inner ℝ (wl9_tN μ M V β N) (Xi μ (wl_psi M) x)| ≤ 1) :
    IsField μ (wl9_psiR μ M V β N) (β * a + 1) (β / N * m + 1) :=
  wl_isField_add (wl9_isField_psi0 hq ha hℓ hm hβ hN)
    (wl_isField_bdd (wr12b_measurable_inner_Xi (wl_psi_calFeat M) (wl9_tN μ M V β N)) hc)

/-- **`R_N` is the weak ensemble of the field `ψ_R`** (bounded perturbation of the field of `R0`). -/
theorem wl9_RN_eq (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (hm : ∫ x, logWeight x ∂μ ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 0 < N) (V : WeakPotential μ)
    (hc : ∀ x, |inner ℝ (wl9_tN μ M V β N) (Xi μ (wl_psi M) x)| ≤ 1) :
    wl9_RN μ M V β N = fieldLaw V (wl9_psiR μ M V β N) (β / N) N :=
  wl5_RN_eq_fieldLaw (V := V) (wl9_isField_psi0 hq ha hℓ hm hβ hN) (div_nonneg hβ (Nat.cast_nonneg N))
    (wl_psi_calFeat M) 1 ((N : ℝ) * (β / N)) N hc

end Fields

/-! ### The exact first marginal of the calibrated reference and the sup bound -/

section Theta

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ}

/-- The first marginal of an `(m+2)`-particle field ensemble has the density `wl6_theta` (`n = m + 1`). -/
lemma wl9_marginal_eq (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a)
    (m : ℕ) :
    (fieldLaw V ψ lam (m + 2)).map (fun X => X 0) =
      μ.withDensity (fun x => ENNReal.ofReal (wl6_theta μ V.q ψ lam (m + 1) x)) := by
  have h := wl6_marginal_zero V hψ hlam hrow (m + 1)
  have e : wl6_dens μ V.q ψ lam (m + 1) = fun x => ENNReal.ofReal (wl6_theta μ V.q ψ lam (m + 1) x) :=
    funext fun x => wl6_dens_eq_theta V hψ hlam (m + 1) x
  rw [e] at h
  exact h

lemma wl9_theta_pos (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a)
    (n : ℕ) (x : E) : 0 < wl6_theta μ V.q ψ lam n x := by
  have hpole := wl6_isField_pole V hψ hlam hrow x
  unfold wl6_theta wl6_Phi
  exact div_pos (mul_pos (Real.exp_pos _) (div_pos (wl6_norm_toReal_pos V hpole hlam n)
    (wl6_norm_toReal_pos V hψ hlam n))) (wl6_Z_pos V hψ hlam n)

/-- **Sup bound** `θ ≤ e^{M} e^{M₁ + λ n a}` (uniform in the particle number). -/
lemma wl9_theta_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a)
    (n : ℕ) (x : E) :
    wl6_theta μ V.q ψ lam n x ≤ Real.exp M * Real.exp (M₁ + lam * n * a) :=
  (wl6_theta_le V hψ hlam hrow n x).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hψ.le x)) (Real.exp_pos _).le)

/-- **The cavity equation, exact form**: `log θ = ψ + log Φ - log Z`. -/
lemma wl9_log_theta (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a)
    (n : ℕ) (x : E) :
    Real.log (wl6_theta μ V.q ψ lam n x) =
      ψ x + Real.log (wl6_Phi μ V.q ψ lam n x) - Real.log (wl6_Z μ V.q ψ lam n) := by
  have hpole := wl6_isField_pole V hψ hlam hrow x
  have hΦ : 0 < wl6_Phi μ V.q ψ lam n x :=
    div_pos (wl6_norm_toReal_pos V hpole hlam n) (wl6_norm_toReal_pos V hψ hlam n)
  have hZ := wl6_Z_pos V hψ hlam n
  unfold wl6_theta
  rw [Real.log_div (mul_pos (Real.exp_pos _) hΦ).ne' hZ.ne', Real.log_mul (Real.exp_pos _).ne' hΦ.ne',
    Real.log_exp]

end Theta

/-! ### The insertion defect and the exact cavity equation (generic in the field ensemble) -/

section Cavity

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ}

/-- The insertion defect `D(x) = A_x(1) - E_{P_n^0} X_x` with `P_n^0 = fieldLaw V ψ lam n` the cavity ensemble and
`X_x = -lam ∑ q(Y_k, x)` the pole exponent: `A_x = cgf X_x P_n^0` (no derivative, hence no junk value). -/
def wl9_D (μ : Measure E) (q : E → E → ℝ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) (x : E) : ℝ :=
  cgf (wl7_poleExp q lam x (n := n)) (wl6_law μ q ψ lam n) 1 -
    ∫ Y, wl7_poleExp q lam x Y ∂(wl6_law μ q ψ lam n)

/-- `log Φ_x = A_x(1)`. -/
lemma wl9_log_Phi (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (n : ℕ)
    (x : E) :
    Real.log (wl6_Phi μ V.q ψ lam n x) = cgf (wl7_poleExp V.q lam x (n := n)) (wl6_law μ V.q ψ lam n) 1 := by
  rw [wl8_Phi_eq_integral V hψ hlam hrow n x]
  unfold cgf mgf
  congr 2
  funext Y
  simp only [one_mul]

/-- The mean of the pole exponent: `E_{P_n^0}[X_x] = -lam n ∫ q(y,x) dν_n(y)` (`n = m + 1`, exchangeability). -/
lemma wl9_integral_X (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a)
    (m : ℕ) (x : E) :
    ∫ Y, wl7_poleExp V.q lam x Y ∂(fieldLaw V ψ lam (m + 1)) =
      -lam * ((m + 1 : ℕ) : ℝ) * ∫ y, V.q y x ∂((fieldLaw V ψ lam (m + 1)).map (fun Y => Y 0)) := by
  have hfm : Measurable (fun y : E => V.q y x) :=
    V.measurable_q.comp (measurable_id.prodMk measurable_const)
  have hfi : Integrable (fun y : E => V.q y x) μ := by
    have := V.integrable_q x
    exact this.congr (Filter.Eventually.of_forall fun y => V.q_symm x y)
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
      Integrable (fun Y : Fin (m + 1) → E => V.q (Y j) x) (fieldLaw V ψ lam (m + 1)) := fun j _ =>
    wl7_integrable_coord V hψ hlam hrow m hfm hfi j
  have hcoord : ∀ j : Fin (m + 1), ∫ Y, V.q (Y j) x ∂(fieldLaw V ψ lam (m + 1)) =
      ∫ y, V.q y x ∂((fieldLaw V ψ lam (m + 1)).map (fun Y => Y 0)) := by
    intro j
    rw [← wl_fieldLaw_marginals_eq V ψ lam j 0, integral_map (measurable_pi_apply j).aemeasurable
      hfm.aestronglyMeasurable]
  have hfun : (fun Y : Fin (m + 1) → E => wl7_poleExp V.q lam x Y) =
      fun Y => -lam * ∑ j : Fin (m + 1), V.q (Y j) x := rfl
  rw [hfun, integral_const_mul, integral_finsetSum _ hint]
  have hsum : ∑ j : Fin (m + 1), ∫ Y, V.q (Y j) x ∂(fieldLaw V ψ lam (m + 1)) =
      ∑ _j : Fin (m + 1), ∫ y, V.q y x ∂((fieldLaw V ψ lam (m + 1)).map (fun Y => Y 0)) :=
    Finset.sum_congr rfl fun j _ => hcoord j
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The cavity equation, exact form** (`n = m + 1` cavity particles, `m + 2` particles in the ensemble):
`log θ(x) = ψ(x) + D(x) - lam (m+1) ∫ q(y,x) dν_n(y) - log Z`. -/
theorem wl9_log_theta_eq (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a)
    (m : ℕ) (x : E) :
    Real.log (wl6_theta μ V.q ψ lam (m + 1) x) =
      ψ x + wl9_D μ V.q ψ lam (m + 1) x -
        lam * ((m + 1 : ℕ) : ℝ) * ∫ y, V.q y x ∂((fieldLaw V ψ lam (m + 1)).map (fun Y => Y 0)) -
        Real.log (wl6_Z μ V.q ψ lam (m + 1)) := by
  have h1 := wl9_log_theta V hψ hlam hrow (m + 1) x
  have h2 := wl9_log_Phi V hψ hlam hrow (m + 1) x
  have h3 := wl9_integral_X V hψ hlam hrow m x
  rw [h1, h2]
  unfold wl9_D
  rw [show wl6_law μ V.q ψ lam (m + 1) = fieldLaw V ψ lam (m + 1) from rfl, h3]
  ring

end Cavity

/-! ### The calibrated reference: density `θ`, sup bound, calibration identity -/

section Ref

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {M : ℕ} {a m : ℝ}

/-- The density `θ = dπ^R_N/dμ` of the first marginal of `R_{m+2}`: `wl6_theta` of the field `ψ_R`
with `m + 1` cavity particles. -/
def wl9_theta (μ : Measure (Euc d)) (M : ℕ) (V : WeakPotential μ) (β : ℝ) (m : ℕ) : Euc d → ℝ :=
  wl6_theta μ V.q (wl9_psiR μ M V β (m + 2)) (β / ((m + 2 : ℕ) : ℝ)) (m + 1)

lemma wl9_hrow {V : WeakPotential μ} (hV : V.q = wl_qm (d := d) M)
    (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a) : ∀ x, ∫ y, V.q x y ∂μ ≤ a := fun x => by
  rw [hV]; exact hq.wr1_rowInt_le ha x

/-- **The first marginal of `R_N`** (`N = m + 2`) has the density `θ`. -/
theorem wl9_firstMarginal_RN_eq (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (hm : ∫ x, logWeight x ∂μ ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    (V : WeakPotential μ) (hV : V.q = wl_qm (d := d) M) (m' : ℕ)
    (hc : ∀ x, |inner ℝ (wl9_tN μ M V β (m' + 2)) (Xi μ (wl_psi M) x)| ≤ 1) :
    HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2)) =
      μ.withDensity (fun x => ENNReal.ofReal (wl9_theta μ M V β m' x)) := by
  have e := wl6_firstMarginal_def (d := d) (m' + 1) (wl9_RN μ M V β (m' + 2))
  refine e.trans ?_
  rw [wl9_RN_eq hq ha hℓ hm hβ (Nat.succ_pos _) V hc]
  exact wl9_marginal_eq V (wl9_isField_psiR hq ha hℓ hm hβ (Nat.succ_pos _) V hc)
    (div_nonneg hβ (Nat.cast_nonneg _)) (wl9_hrow hV hq ha) m'

/-- **`R_N` is a probability measure.** -/
theorem wl9_RN_isProb (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (hm : ∫ x, logWeight x ∂μ ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    (V : WeakPotential μ) (m' : ℕ)
    (hc : ∀ x, |inner ℝ (wl9_tN μ M V β (m' + 2)) (Xi μ (wl_psi M) x)| ≤ 1) :
    IsProbabilityMeasure (wl9_RN μ M V β (m' + 2)) := by
  rw [wl9_RN_eq hq ha hℓ hm hβ (Nat.succ_pos _) V hc]
  exact (fieldSpec (V := V) (wl9_isField_psiR hq ha hℓ hm hβ (Nat.succ_pos _) V hc)
    (div_nonneg hβ (Nat.cast_nonneg _)) (m' + 2)).isProb

/-- **Sup bound** (TeX `r2-log-reference-marginal`, first half): `dπ^R_N/dμ ≤ e^{βa + 1} e^{(β/N) m + 1 + (β/N) n a}`,
`n = N - 1` (uniform in `N` as soon as `|⟪t_N, Ξ⟫| ≤ 1`). -/
theorem wl9_theta_le_ref (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (hm : ∫ x, logWeight x ∂μ ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    (V : WeakPotential μ) (hV : V.q = wl_qm (d := d) M) (m' : ℕ)
    (hc : ∀ x, |inner ℝ (wl9_tN μ M V β (m' + 2)) (Xi μ (wl_psi M) x)| ≤ 1) (x : Euc d) :
    0 < wl9_theta μ M V β m' x ∧ wl9_theta μ M V β m' x ≤
      Real.exp (β * a + 1) * Real.exp (β / ((m' + 2 : ℕ) : ℝ) * m + 1 +
        β / ((m' + 2 : ℕ) : ℝ) * ((m' + 1 : ℕ) : ℝ) * a) :=
  have hψ := wl9_isField_psiR hq ha hℓ hm hβ (Nat.succ_pos (m' + 1)) V hc
  have hlam : 0 ≤ β / ((m' + 2 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  ⟨wl9_theta_pos V hψ hlam (wl9_hrow hV hq ha) (m' + 1) x,
    wl9_theta_le V hψ hlam (wl9_hrow hV hq ha) (m' + 1) x⟩

/-- `Ξ̄_N = E_{R_N} μ_N(Ξ) = ∫ Ξ dπ^R_N` (all one-coordinate marginals of a field ensemble coincide). -/
theorem wl9_empXi_integral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ψ : Euc d → H} {B : ℝ} (hΨ : CalFeat Ψ B) (V : WeakPotential μ) (ψ : Euc d → ℝ) (lam : ℝ) (m' : ℕ)
    [IsProbabilityMeasure (fieldLaw V ψ lam (m' + 2))] :
    ∫ X, empXi μ Ψ X ∂(fieldLaw V ψ lam (m' + 2)) =
      ∫ y, Xi μ Ψ y ∂((fieldLaw V ψ lam (m' + 2)).map (fun X => X 0)) := by
  set P := fieldLaw V ψ lam (m' + 2) with hP
  have hint : ∀ i : Fin (m' + 2), Integrable (fun X : Fin (m' + 2) → Euc d => Xi μ Ψ (X i)) P :=
    fun i => Integrable.of_bound
      (hΨ.continuous_Xi.stronglyMeasurable.comp_measurable (measurable_pi_apply i)).aestronglyMeasurable
      (2 * B) (Filter.Eventually.of_forall fun X => hΨ.norm_Xi_le _)
  have h2 : ∀ i : Fin (m' + 2), ∫ X : Fin (m' + 2) → Euc d, Xi μ Ψ (X i) ∂P =
      ∫ y, Xi μ Ψ y ∂(P.map (fun X => X 0)) := by
    intro i
    rw [← wl_fieldLaw_marginals_eq V ψ lam i 0, integral_map (measurable_pi_apply i).aemeasurable
      hΨ.continuous_Xi.stronglyMeasurable.aestronglyMeasurable]
  unfold empXi
  rw [integral_smul, integral_finsetSum _ fun i _ => hint i]
  simp_rw [h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : (1 / ((m' + 2 : ℕ) : ℝ)) * ((m' + 2 : ℕ) : ℝ) = 1 := by field_simp
  rw [this, one_smul]

/-- `R0` is a probability measure. -/
theorem wl9_R0_isProb (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (hm : ∫ x, logWeight x ∂μ ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    (V : WeakPotential μ) (N : ℕ) (hN : 0 < N) : IsProbabilityMeasure (wl9_R0 μ M V β N) :=
  (fieldSpec (V := V) (wl9_isField_psi0 hq ha hℓ hm hβ hN) (div_nonneg hβ (Nat.cast_nonneg N)) N).isProb

/-- **Calibration identity** (TeX `⟪t_N, Ξ(x)⟫ = -β k_M(π^R_N - μ)(x)` modulo a constant; port of `wr13e_hh_eq`):
`⟪t_N, Ξ x⟫ = -β ∫ k_M(x,y) (θ(y) - 1) dμ(y) + c₀`. -/
theorem wl9_hh_eq (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (hm : ∫ x, logWeight x ∂μ ≤ m) {β : ℝ} (hβ : 0 < β)
    (V : WeakPotential μ) (hV : V.q = wl_qm (d := d) M) (m' : ℕ)
    (hc : ∀ x, |inner ℝ (wl9_tN μ M V β (m' + 2)) (Xi μ (wl_psi M) x)| ≤ 1) :
    ∃ c₀ : ℝ, ∀ x, inner ℝ (wl9_tN μ M V β (m' + 2)) (Xi μ (wl_psi M) x) =
      -β * ∫ y, wl_km M x y * (wl9_theta μ M V β m' y - 1) ∂μ + c₀ := by
  have hcal := wl_psi_calFeat (d := d) M
  have hΨ := wl_psi_hyp (d := d) M
  haveI := wl9_RN_isProb hq ha hℓ hm hβ.le V m' hc
  haveI := wl9_R0_isProb hq ha hℓ hm hβ.le V (m' + 2) (Nat.succ_pos _)
  have hN0 : 0 < m' + 2 := Nat.succ_pos _
  set θ := wl9_theta μ M V β m' with hθdef
  have hψ := wl9_isField_psiR hq ha hℓ hm hβ.le hN0 V hc
  have hlam : 0 ≤ β / ((m' + 2 : ℕ) : ℝ) := div_nonneg hβ.le (Nat.cast_nonneg _)
  have hrow := wl9_hrow hV hq ha
  have hθ0 : ∀ x, 0 < θ x := fun x => wl9_theta_pos V hψ hlam hrow (m' + 1) x
  have hθm : Measurable θ := wl6_measurable_theta V hψ.measurable _ _
  have hmarg := wl9_firstMarginal_RN_eq hq ha hℓ hm hβ.le V hV m' hc
  have hRN := wl9_RN_eq hq ha hℓ hm hβ.le hN0 V hc
  have hfm : HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2)) =
      (wl9_RN μ M V β (m' + 2)).map (fun X => X 0) := wl6_firstMarginal_def (d := d) (m' + 1) _
  have hX : ∫ X, empXi μ (wl_psi M) X ∂(wl9_RN μ M V β (m' + 2)) =
      ∫ y, Xi μ (wl_psi M) y ∂(HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2))) := by
    rw [hfm]
    haveI : IsProbabilityMeasure (fieldLaw V (wl9_psiR μ M V β (m' + 2)) (β / ((m' + 2 : ℕ) : ℝ)) (m' + 2)) := by
      rw [← hRN]; infer_instance
    have := wl9_empXi_integral (μ := μ) hcal V (wl9_psiR μ M V β (m' + 2)) (β / ((m' + 2 : ℕ) : ℝ)) m'
    rw [← hRN] at this
    exact this
  have htN : wl9_tN μ M V β (m' + 2) =
      -(β) • ∫ X, empXi μ (wl_psi M) X ∂(wl9_RN μ M V β (m' + 2)) := by
    have h := wl4_tN_eq_empXi (μ := μ) (P := wl9_R0 μ M V β (m' + 2)) hcal hN0
      (c := 1 / ((m' + 2 : ℕ) : ℝ)) (β := ((m' + 2 : ℕ) : ℝ) * (β / ((m' + 2 : ℕ) : ℝ)))
      (by positivity) (by rw [wl9_Nlam hN0]; exact hβ)
    have e : ((m' + 2 : ℕ) : ℝ) * (β / ((m' + 2 : ℕ) : ℝ)) * (1 / ((m' + 2 : ℕ) : ℝ)) *
        ((m' + 2 : ℕ) : ℝ) = β := by
      have : ((m' + 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
      field_simp
    rw [e] at h
    exact h
  set Ξ := Xi μ (wl_psi M) with hΞ
  set Ψbar := ∫ y, wl_psi M y ∂μ with hΨbar
  have hu' : ∫ y, Ξ y ∂(HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2))) = ∫ y, θ y • Ξ y ∂μ := by
    rw [hmarg, integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (θ x))
      (ENNReal.measurable_ofReal.comp hθm) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (ENNReal.ofReal (θ y)).toReal • Ξ y = θ y • Ξ y
    rw [ENNReal.toReal_ofReal (hθ0 y).le]
  obtain ⟨hθbd⟩ : Nonempty (∃ Cθ : ℝ, ∀ x, |θ x| ≤ Cθ) := ⟨⟨_, fun x => by
    rw [abs_of_pos (hθ0 x)]
    exact (wl9_theta_le_ref hq ha hℓ hm hβ.le V hV m' hc x).2⟩⟩
  obtain ⟨Cθ, hCθ⟩ := hθbd
  have hθi : Integrable θ μ :=
    Integrable.of_bound hθm.aestronglyMeasurable Cθ (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hCθ x)
  have hθ1 : ∫ x, θ x ∂μ = 1 := by
    have h1 : (HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2))) Set.univ = 1 := by
      rw [hfm]
      exact measure_univ
    rw [hmarg, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => (hθ0 x).le)
      hθm.aestronglyMeasurable, h1]
    simp
  have hΞm : StronglyMeasurable Ξ := hcal.continuous_Xi.stronglyMeasurable
  have hΞi : ∀ x, Integrable (fun y => inner ℝ (Ξ x) (Ξ y) * θ y) μ := by
    intro x
    refine Integrable.bdd_mul (c := ‖Ξ x‖ * (2 * Real.sqrt (wl_k0 M))) hθi ?_ ?_
    · exact (continuous_const.inner hcal.continuous_Xi).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      calc ‖inner ℝ (Ξ x) (Ξ y)‖ ≤ ‖Ξ x‖ * ‖Ξ y‖ := norm_inner_le_norm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcal.norm_Xi_le y) (norm_nonneg _)
  have hΨi : Integrable (wl_psi (d := d) M) μ := hcal.integrable_Ψ
  set C1 : ℝ := ∫ y, inner ℝ Ψbar (wl_psi M y) * θ y ∂μ with hC1
  have hkm : ∀ x : Euc d, Measurable fun y => wl_km M x y := fun x =>
    Measurable.of_uncurry_left (f := fun x y : Euc d => wl_km M x y) (wl_km_measurable M)
  have hgi : ∀ x, Integrable (fun y => wl_km M x y * θ y) μ := by
    intro x
    refine Integrable.bdd_mul (c := wl_k0 M) hθi (hkm x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hΨ.abs_le _ _
  refine ⟨-β * (inner ℝ Ψbar Ψbar - C1), fun x => ?_⟩
  have hint : Integrable (fun y => θ y • Ξ y) μ := by
    refine Integrable.mono' (hθi.mul_const (2 * Real.sqrt (wl_k0 M)))
      (hθm.stronglyMeasurable.smul hΞm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hθ0 y)]
    exact mul_le_mul_of_nonneg_left (hcal.norm_Xi_le y) (hθ0 y).le
  have e1 : inner ℝ (wl9_tN μ M V β (m' + 2)) (Ξ x) = -β *
      inner ℝ (∫ y, Ξ y ∂(HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2)))) (Ξ x) := by
    rw [htN, hX, real_inner_smul_left]
  have e2 : inner ℝ (∫ y, Ξ y ∂(HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2)))) (Ξ x) =
      ∫ y, inner ℝ (Ξ x) (Ξ y) * θ y ∂μ := by
    rw [real_inner_comm, hu', ← integral_inner hint (Ξ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_right]
    ring
  have hexp : ∀ y, inner ℝ (Ξ x) (Ξ y) * θ y = wl_km M x y * θ y - inner ℝ (wl_psi M x) Ψbar * θ y -
      inner ℝ Ψbar (wl_psi M y) * θ y + inner ℝ Ψbar Ψbar * θ y := by
    intro y
    simp only [hΞ, Xi, ← hΨbar, inner_sub_left, inner_sub_right, wl_psi_inner]
    rw [real_inner_comm (wl_psi M y) Ψbar]
    ring
  have hi2 : Integrable (fun y => inner ℝ Ψbar (wl_psi M y) * θ y) μ := by
    refine Integrable.bdd_mul (c := ‖Ψbar‖ * Real.sqrt (wl_k0 M)) hθi
      (continuous_const.inner hΨ.continuous).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    calc ‖inner ℝ Ψbar (wl_psi M y)‖ ≤ ‖Ψbar‖ * ‖wl_psi M y‖ := norm_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcal.bound y) (norm_nonneg _)
  have e3 : ∫ y, inner ℝ (Ξ x) (Ξ y) * θ y ∂μ =
      ∫ y, wl_km M x y * θ y ∂μ - inner ℝ (wl_psi M x) Ψbar - C1 + inner ℝ Ψbar Ψbar := by
    simp_rw [hexp]
    have j2 : Integrable (fun y => inner ℝ (wl_psi M x) Ψbar * θ y) μ := hθi.const_mul _
    have j4 : Integrable (fun y => inner ℝ Ψbar Ψbar * θ y) μ := hθi.const_mul _
    have j12 : Integrable (fun y => wl_km M x y * θ y - inner ℝ (wl_psi M x) Ψbar * θ y) μ :=
      (hgi x).sub j2
    have j123 : Integrable (fun y => wl_km M x y * θ y - inner ℝ (wl_psi M x) Ψbar * θ y -
        inner ℝ Ψbar (wl_psi M y) * θ y) μ := j12.sub hi2
    rw [integral_add j123 j4, integral_sub j12 hi2, integral_sub (hgi x) j2,
      integral_const_mul, integral_const_mul, hθ1]
    ring
  have e4 : ∫ y, wl_km M x y * (θ y - 1) ∂μ = ∫ y, wl_km M x y * θ y ∂μ - inner ℝ (wl_psi M x) Ψbar := by
    have hg1 : Integrable (fun y => wl_km M x y) μ :=
      Integrable.of_bound (hkm x).aestronglyMeasurable (wl_k0 M)
        (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hΨ.abs_le _ _)
    have : ∫ y, wl_km M x y ∂μ = inner ℝ (wl_psi M x) Ψbar := by
      rw [hΨbar, ← integral_inner hΨi (wl_psi M x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      exact (wl_psi_inner M x y).symm
    simp_rw [mul_sub, mul_one]
    rw [integral_sub (hgi x) hg1, this]
  rw [e1, e2, e3, e4]
  ring

/-- **The exact cavity equation of the calibrated reference** (TeX `eq:r2-log-reference-equation`; port of
`wr13e_cavity_equation`).  With `θ = dπ^R_N/dμ`, `π = π^R_N`, `ν = ν^R_n` the first marginal of the cavity ensemble
(`n = N - 1` particles, the SAME field `ψ_R`, i.e. the calibration field is held fixed), `D` the insertion defect,
`h_N = -λ ℓ`, `λ = β/N` and `q = q_M`: for a constant `c` and every `x`,
`log θ(x) + β ∫ K(x,y)(θ(y) - 1) dμ(y) = (D(x) + h_N(x)) + β (q π - q ν)(x) + λ (q ν)(x) + c`. -/
theorem wl9_cavity_equation (hat : ∀ x, μ {x} = 0) (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (hm : ∫ x, logWeight x ∂μ ≤ m) {β : ℝ} (hβ : 0 < β)
    (V : WeakPotential μ) (hV : V.q = wl_qm (d := d) M) (m' : ℕ)
    (hc : ∀ x, |inner ℝ (wl9_tN μ M V β (m' + 2)) (Xi μ (wl_psi M) x)| ≤ 1) :
    ∃ c : ℝ, ∀ x : Euc d,
      Real.log (wl9_theta μ M V β m' x) +
          β * ∫ y, sphericalLogKernel x y * (wl9_theta μ M V β m' y - 1) ∂μ =
        (wl9_D μ V.q (wl9_psiR μ M V β (m' + 2)) (β / ((m' + 2 : ℕ) : ℝ)) (m' + 1) x -
            β / ((m' + 2 : ℕ) : ℝ) * logWeight x) +
          β * (∫ y, wl_qm M x y ∂(HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2))) -
            ∫ y, wl_qm M x y ∂((fieldLaw V (wl9_psiR μ M V β (m' + 2)) (β / ((m' + 2 : ℕ) : ℝ)) (m' + 1)).map
              (fun Y => Y 0))) +
          β / ((m' + 2 : ℕ) : ℝ) * ∫ y, wl_qm M x y ∂((fieldLaw V (wl9_psiR μ M V β (m' + 2))
            (β / ((m' + 2 : ℕ) : ℝ)) (m' + 1)).map (fun Y => Y 0)) + c := by
  have hN0 : 0 < m' + 2 := Nat.succ_pos _
  have hψ := wl9_isField_psiR hq ha hℓ hm hβ.le hN0 V hc
  have hlam : 0 ≤ β / ((m' + 2 : ℕ) : ℝ) := div_nonneg hβ.le (Nat.cast_nonneg _)
  have hrow := wl9_hrow hV hq ha
  obtain ⟨c₀, hc₀⟩ := wl9_hh_eq hq ha hℓ hm hβ V hV m' hc
  have hmarg := wl9_firstMarginal_RN_eq hq ha hℓ hm hβ.le V hV m' hc
  obtain ⟨Cθ, hCθ⟩ : ∃ Cθ : ℝ, ∀ x, 0 < wl9_theta μ M V β m' x ∧ wl9_theta μ M V β m' x ≤ Cθ :=
    ⟨_, fun x => wl9_theta_le_ref hq ha hℓ hm hβ.le V hV m' hc x⟩
  set θ := wl9_theta μ M V β m' with hθdef
  set lam : ℝ := β / ((m' + 2 : ℕ) : ℝ) with hlamdef
  have hθm : Measurable θ := wl6_measurable_theta V hψ.measurable _ _
  have hθb : ∀ y, |θ y - 1| ≤ Cθ + 1 := fun y => by
    rw [abs_le]; constructor <;> linarith [(hCθ y).1, (hCθ y).2]
  have hzi : Integrable (fun y => θ y - 1) μ :=
    Integrable.of_bound (hθm.sub_const 1).aestronglyMeasurable (Cθ + 1)
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hθb y)
  have hlamN : lam * ((m' + 1 : ℕ) : ℝ) + lam = β := by
    have : ((m' + 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
    rw [hlamdef]; push_cast; field_simp; ring
  refine ⟨c₀ - Real.log (wl6_Z μ V.q (wl9_psiR μ M V β (m' + 2)) lam (m' + 1)), fun x => ?_⟩
  have e0 := wl9_log_theta_eq V hψ hlam hrow m' x
  change Real.log (θ x) = _ at e0
  have e1 := hc₀ x
  have hkm : Measurable fun y => wl_km M x y :=
    Measurable.of_uncurry_left (f := fun x y : Euc d => wl_km M x y) (wl_km_measurable M)
  have hgk : Integrable (fun y => wl_km M x y * (θ y - 1)) μ := by
    refine Integrable.bdd_mul (c := wl_k0 M) hzi hkm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (wl_km_nonneg M x y)]; exact wl_km_le_k0 M x y
  have hq1 : Integrable (wl_qm (d := d) M x) μ := hq.wr1_integrable_row x
  have hgq : Integrable (fun y => wl_qm M x y * (θ y - 1)) μ := by
    have := Integrable.bdd_mul (c := Cθ + 1) hq1 hzi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hθb y)
    exact this.congr (Filter.Eventually.of_forall fun y => by simp [mul_comm])
  have hne : ∀ᵐ y ∂μ, y ≠ x := by
    rw [ae_iff]; simpa using hat x
  have hKe : ∫ y, sphericalLogKernel x y * (θ y - 1) ∂μ =
      ∫ y, wl_km M x y * (θ y - 1) ∂μ + ∫ y, wl_qm M x y * (θ y - 1) ∂μ := by
    rw [← integral_add hgk hgq]
    refine integral_congr_ae (hne.mono fun y hy => ?_)
    simp only
    rw [wl_K_eq M (Ne.symm hy)]; ring
  have hqπ : ∫ y, wl_qm M x y ∂(HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2))) =
      ∫ y, wl_qm M x y * θ y ∂μ := by
    rw [hmarg, integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (θ x))
      (ENNReal.measurable_ofReal.comp hθm) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (ENNReal.ofReal (θ y)).toReal • wl_qm M x y = wl_qm M x y * θ y
    rw [ENNReal.toReal_ofReal (hCθ y).1.le, smul_eq_mul, mul_comm]
  have hqθ1 : ∫ y, wl_qm M x y * (θ y - 1) ∂μ = ∫ y, wl_qm M x y * θ y ∂μ - rowIntE (wl_qm M) μ x := by
    have hqθ : Integrable (fun y => wl_qm M x y * θ y) μ := by
      have := hgq.add hq1
      exact this.congr (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring)
    unfold rowIntE
    rw [← integral_sub hqθ hq1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have hνq : ∫ y, V.q y x ∂((fieldLaw V (wl9_psiR μ M V β (m' + 2)) lam (m' + 1)).map (fun Y => Y 0)) =
      ∫ y, wl_qm M x y ∂((fieldLaw V (wl9_psiR μ M V β (m' + 2)) lam (m' + 1)).map (fun Y => Y 0)) := by
    simp_rw [hV, hq.symm _ x]
  rw [hνq] at e0
  have hψx : wl9_psiR μ M V β (m' + 2) x = β * rowIntE (wl_qm M) μ x - lam * logWeight x +
      (-β * ∫ y, wl_km M x y * (θ y - 1) ∂μ + c₀) := by
    show wl9_psi0 μ M β (m' + 2) x + inner ℝ (wl9_tN μ M V β (m' + 2)) (Xi μ (wl_psi M) x) = _
    rw [wl9_psi0_apply hN0, e1]
  rw [hψx] at e0
  rw [e0, hKe, hqθ1, hqπ]
  have e3 : lam * ((m' + 1 : ℕ) : ℝ) = β - lam := by linarith
  rw [e3]
  ring

end Ref

end HRS.MS.Wl
