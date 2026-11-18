import HRS.MS.WlEnsAux1

/-!
# HRS.MS.WlEnsAux2 -- field-ensemble layer for S3.5, part 2 (WL-3)

Packet WL-3 of `docs/WR_LOG_PLAN.md` (Step 4 end and Step 5).  Infrastructure lemmas, not manuscript rows.
Namespace `HRS.MS.Wl`, helper prefix `wl3_`.  Builds on `WlEnsAux1` (`wlPot`, `wl_Qfield`, `wl_Q_eq_fieldLaw`).

* **Field algebra** (`wl_isField_add`, `wl_isField_mono`, `wl_isField_rowInt`, `wl_isField_negMul`,
  `wl_isField_bdd`, `wl_isField_poles`, `wl_isField_family`): the one-body field of the family
  `φ = β rowIntE q μ - (β/N) ℓ + v - (β/N) ∑_b t_b q(·, z_b)` (`ℓ ≥ 0`, `|v| ≤ b`, `t_b ≥ 0`) is an
  `IsField μ φ M M₁` with `M = β a + b`, `M₁ = (β/N) ∫ ℓ + b + (β/N) (∑ t_b) a`.  The constants are uniform in
  `N` when `∫ ℓ`, `b N`, `∑ t_b` are bounded.  The poles with weights `t_b ∈ [0,1]` are put INTO the
  field (adjustment, harmless): the pins of `pinnedLaw` have the weight `1` only.
* **Kappa** (`weakKappa_wlPot`, `wl_kappa_lt_half`, `wl_kappa_le`, `wl_exists_head`,
  `wl_kappa_head`, `wl_qm_weak`): `weakKappa (wlPot …) β = 4 e^{M + M₁ + β a} β a`; it is `< 1/2` when `β a ≤ min 1
  (16 e^{M+M₁+1})⁻¹`; for `a = C M^{-d/2}` (head index `M`, tail kernel `wl_qm`) this holds for all large `M`
  (explicit threshold, depending on `β, C, M, M₁` upper bounds only).
* **Family bounds** (`wl_resampling`, `wl_linear`, `wl_dobrushin`, `wl_pin_tv_changed`, `wl_pin_tv_deleted`,
  `wl_pin_tv_removed`): the instances of `weak_resampling`, `weak_linear_variance_symm`, `rvh_pin_changed`,
  `rvh_pin_deleted`, `rvh_pin_removed` at `V = wlPot …`, with the hypothesis `κ ≤ 1/2` replaced by the explicit
  smallness `β a ≤ min 1 (16 e^{M+M₁+1})⁻¹`, and the pin bounds `C/N` with explicit `C = 8 e^{M+M₁+1} β a`.
* `wl_Q_le_crude` (abstract: `wl_Q_le_crude_abs`): `Q ≤ ofReal (exp (β N C + β Cℓ)) • μ^{⊗N}` for all `N ≥ 1`,
  `β ≥ 0` (Jensen for the normaliser: `K_{N,β} ≥ e^{-β ∫ℓ}`; `K ≥ 0`, `ℓ ≥ 0`).
* `wl_fieldLaw_perm`, `wl_fieldLaw_isExchangeable`, `wl_fieldLaw_marginals_eq`: `fieldLaw V ψ λ n` is invariant under
  coordinate permutations (a common field), hence exchangeable.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

/-! ### Algebra of one-body fields -/

section FieldAlgebra

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

lemma wl_isField_mono {ψ : E → ℝ} {M M₁ M' M₁' : ℝ} (h : IsField μ ψ M M₁) (hM : M ≤ M')
    (hM₁ : M₁ ≤ M₁') : IsField μ ψ M' M₁' :=
  ⟨h.measurable, fun z => (h.le z).trans hM, h.integrable, by linarith [h.ge]⟩

lemma wl_isField_add {ψ₁ ψ₂ : E → ℝ} {M₁ M₂ N₁ N₂ : ℝ} (h₁ : IsField μ ψ₁ M₁ N₁)
    (h₂ : IsField μ ψ₂ M₂ N₂) : IsField μ (fun x => ψ₁ x + ψ₂ x) (M₁ + M₂) (N₁ + N₂) :=
  ⟨h₁.measurable.add h₂.measurable, fun z => add_le_add (h₁.le z) (h₂.le z),
    h₁.integrable.add h₂.integrable, by
      rw [integral_add h₁.integrable h₂.integrable]
      linarith [h₁.ge, h₂.ge]⟩

/-- The field `β rowIntE q μ` is `IsField μ _ (β a) 0`. -/
lemma wl_isField_rowInt {a : ℝ} {q : E → E → ℝ} (hq : EWeakKernel μ a q) (ha : 0 ≤ a) {β : ℝ}
    (hβ : 0 ≤ β) : IsField μ (fun x => β * rowIntE q μ x) (β * a) 0 := by
  have hrow : Integrable (rowIntE q μ) μ := (hq.rowOKE ha).integrable_rowInt
  refine ⟨hq.wr1_measurable_rowInt.const_mul β, fun z => ?_, hrow.const_mul β, ?_⟩
  · exact mul_le_mul_of_nonneg_left (hq.wr1_rowInt_le ha z) hβ
  · rw [integral_const_mul]
    have : 0 ≤ ∫ x, rowIntE q μ x ∂μ := integral_nonneg fun x => hq.wr1_rowInt_nonneg x
    simpa using mul_nonneg hβ this

/-- A nonpositive field `-c f` with `f ≥ 0` integrable: `IsField μ _ 0 (c m)` when `∫ f ≤ m`. -/
lemma wl_isField_negMul {f : E → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f μ)
    {c m : ℝ} (hc : 0 ≤ c) (hm : ∫ x, f x ∂μ ≤ m) :
    IsField μ (fun x => -(c * f x)) 0 (c * m) := by
  refine ⟨(hfm.const_mul c).neg, fun z => ?_, (hfi.const_mul c).neg, ?_⟩
  · have := mul_nonneg hc (hf0 z)
    linarith
  · rw [integral_neg, integral_const_mul]
    have := mul_le_mul_of_nonneg_left hm hc
    linarith

/-- A bounded measurable field `|v| ≤ b`: `IsField μ v b b`. -/
lemma wl_isField_bdd {v : E → ℝ} (hv : Measurable v) {b : ℝ} (hb : ∀ x, |v x| ≤ b) :
    IsField μ v b b := by
  have hint : Integrable v μ :=
    Integrable.of_bound hv.aestronglyMeasurable b
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)
  refine ⟨hv, fun z => (le_abs_self _).trans (hb z), hint, ?_⟩
  have h1 : |∫ x, v x ∂μ| ≤ b := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := v) (C := b)
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)
    simpa using this
  linarith [neg_abs_le (∫ x, v x ∂μ)]

/-- The poles `-c ∑_b t_b q(·, z_b)` (`t_b ≥ 0`): `IsField μ _ 0 (c (∑ t_b) a)`. -/
lemma wl_isField_poles {a : ℝ} {q : E → E → ℝ} (hq : EWeakKernel μ a q) (ha : 0 ≤ a)
    {B : Type*} [Fintype B] (t : B → ℝ) (ht : ∀ b, 0 ≤ t b) (z : B → E) {c : ℝ} (hc : 0 ≤ c) :
    IsField μ (fun x => -(c * ∑ b, t b * q x (z b))) 0 (c * ((∑ b, t b) * a)) := by
  refine wl_isField_negMul (f := fun x => ∑ b, t b * q x (z b))
    (Finset.measurable_sum _ fun b _ => (hq.wr1_measurable_right (z b)).const_mul _)
    (fun x => Finset.sum_nonneg fun b _ => mul_nonneg (ht b) (hq.nonneg _ _))
    (integrable_finsetSum _ fun b _ => (hq.wr1_integrable_col (z b)).const_mul _) hc ?_
  rw [integral_finsetSum _ fun b _ => (hq.wr1_integrable_col (z b)).const_mul _]
  calc ∑ b, ∫ x, t b * q x (z b) ∂μ = ∑ b, t b * rowIntE q μ (z b) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_const_mul, hq.wr1_integral_col]
    _ ≤ ∑ b, t b * a := Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left (hq.wr1_rowInt_le ha _) (ht b)
    _ = (∑ b, t b) * a := by rw [Finset.sum_mul]

end FieldAlgebra

/-! ### The family field and its constants -/

section Family

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

lemma wl_isField_congr {ψ ψ' : E → ℝ} {M M₁ : ℝ} (h : IsField μ ψ M M₁) (he : ∀ x, ψ x = ψ' x) :
    IsField μ ψ' M M₁ := by
  have : ψ = ψ' := funext he
  rwa [← this]

/-- The one-body field of the family of Step 5:
`φ = β rowIntE q μ - (β/N) ℓ + v - (β/N) ∑_b t_b q(·, z_b)`. -/
def wlFamField (μ : Measure E) (q : E → E → ℝ) (β : ℝ) (N : ℕ) (ℓ v : E → ℝ) {B : Type*} [Fintype B]
    (t : B → ℝ) (z : B → E) (x : E) : ℝ :=
  β * rowIntE q μ x - (β / (N : ℝ)) * ℓ x + v x - (β / (N : ℝ)) * ∑ b, t b * q x (z b)

/-- **Constants of the family field.**  `ℓ ≥ 0` measurable integrable with `∫ ℓ ≤ m`, `|v| ≤ b`,
`t_b ≥ 0`, `β ≥ 0`: `IsField μ (wlFamField …) (β a + b) ((β/N) m + b + (β/N) ((∑ t_b) a))`. -/
theorem wl_isField_family {a : ℝ} {q : E → E → ℝ} (hq : EWeakKernel μ a q) (ha : 0 ≤ a) {β : ℝ}
    (hβ : 0 ≤ β) (N : ℕ) {ℓ v : E → ℝ} (hℓm : Measurable ℓ) (hℓ0 : ∀ x, 0 ≤ ℓ x)
    (hℓi : Integrable ℓ μ) {m : ℝ} (hm : ∫ x, ℓ x ∂μ ≤ m) (hv : Measurable v) {b : ℝ}
    (hb : ∀ x, |v x| ≤ b) {B : Type*} [Fintype B] (t : B → ℝ) (ht : ∀ i, 0 ≤ t i) (z : B → E) :
    IsField μ (wlFamField μ q β N ℓ v t z) (β * a + b)
      ((β / (N : ℝ)) * m + b + (β / (N : ℝ)) * ((∑ i, t i) * a)) := by
  have hc : 0 ≤ β / (N : ℝ) := div_nonneg hβ (Nat.cast_nonneg N)
  have h1 := wl_isField_rowInt hq ha hβ
  have h2 := wl_isField_negMul hℓm hℓ0 hℓi hc hm
  have h3 := wl_isField_bdd (μ := μ) hv hb
  have h4 := wl_isField_poles hq ha t ht z hc
  have h := wl_isField_add (wl_isField_add (wl_isField_add h1 h2) h3) h4
  refine wl_isField_mono (wl_isField_congr h fun x => ?_) (le_of_eq (by ring)) (le_of_eq (by ring))
  simp only [wlFamField]
  ring

/-- `weakKappa` of `wlPot` in closed form. -/
lemma wl_weakKappa_wlPot {a : ℝ} {q : E → E → ℝ} (hq : EWeakKernel μ a q) (ha : 0 ≤ a)
    {φ : E → ℝ} {M M₁ : ℝ} (hφ : IsField μ φ M M₁) (β : ℝ) :
    weakKappa (wlPot hq ha hφ) β = 4 * Real.exp (M + M₁ + β * a) * (β * a) := rfl

/-- **Smallness**: `β a ≤ min 1 (16 e^{M+M₁+1})⁻¹` gives `κ < 1/2`. -/
theorem wl_kappa_lt_half {a : ℝ} {q : E → E → ℝ} (hq : EWeakKernel μ a q) (ha : 0 ≤ a)
    {φ : E → ℝ} {M M₁ : ℝ} (hφ : IsField μ φ M M₁) {β : ℝ} (hβ : 0 ≤ β)
    (hs : β * a ≤ min 1 (1 / (16 * Real.exp (M + M₁ + 1)))) :
    weakKappa (wlPot hq ha hφ) β < 1 / 2 :=
  weakKappa_lt_half (wlPot hq ha hφ) hβ hs

/-- Under `β a ≤ 1`: `κ ≤ 4 e^{M+M₁+1} β a`. -/
lemma wl_kappa_le {a : ℝ} {q : E → E → ℝ} (hq : EWeakKernel μ a q) (ha : 0 ≤ a)
    {φ : E → ℝ} {M M₁ : ℝ} (hφ : IsField μ φ M M₁) {β : ℝ} (hβ : 0 ≤ β) (h1 : β * a ≤ 1) :
    weakKappa (wlPot hq ha hφ) β ≤ 4 * Real.exp (M + M₁ + 1) * (β * a) := by
  rw [wl_weakKappa_wlPot]
  have h0 : 0 ≤ β * a := mul_nonneg hβ ha
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (by linarith)) (by norm_num)) h0

end Family

/-! ### The tail kernel `q_M` as a weak kernel and the head index -/

variable {d : ℕ}

lemma wl3_tau_eq (x y : Euc d) : wl_tau x y = wl2_tau x y := by
  unfold wl2_tau wl2_c
  linarith [wl_one_sub_tau x y]

/-- Tie of the WL-1 tail kernel `wl_qm` to the WL-2 tail kernel `wl2_qm`. -/
theorem wl3_qm_eq (M : ℕ) (x y : Euc d) : wl_qm M x y = wl2_qm M x y := by
  rw [wl_qm_eq_tsum]
  unfold wl2_qm
  refine tsum_congr fun j => ?_
  unfold wl_term wl2_qterm
  rw [wl3_tau_eq]
  have e : M + 1 + j = (M + j) + 1 := by omega
  rw [e]
  push_cast
  ring

/-- **`q_M` is an `EWeakKernel`** with row constant `C M^{-d/2}` (`M ≥ 1`), `C` depending on `d, A` only. -/
theorem wl_qm_weak (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ M : ℕ, 1 ≤ M →
      EWeakKernel (HRS.Whole.withDensityReal ρ) (C * (M : ℝ) ^ (-((d : ℝ) / 2)))
        (wl_qm (d := d) M) := by
  obtain ⟨C, hC0, hC⟩ := wl_row_qm hd A
  refine ⟨C, hC0, fun ρ hρ hA M hM => ⟨wl_qm_measurable M, wl_qm_symm M, wl_qm_nonneg M,
    fun x => ?_⟩⟩
  obtain ⟨hint, hle⟩ := hC ρ hρ hA M hM x
  have hint' : Integrable (fun y => wl_qm M x y) (HRS.Whole.withDensityReal ρ) := by
    simpa only [← wl3_qm_eq] using hint
  have hle' : ∫ y, wl_qm M x y ∂(HRS.Whole.withDensityReal ρ) ≤ C * (M : ℝ) ^ (-((d : ℝ) / 2)) := by
    simpa only [← wl3_qm_eq] using hle
  have h1 := ofReal_integral_eq_lintegral_ofReal hint'
    (Filter.Eventually.of_forall fun y => wl_qm_nonneg M x y)
  rw [← h1]
  exact ENNReal.ofReal_le_ofReal hle'

/-- Existence of the head index: `C M^{-d/2} ≤ δ` for all large `M`. -/
lemma wl_exists_head (hd : 1 ≤ d) (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M → C * (M : ℝ) ^ (-((d : ℝ) / 2)) ≤ δ := by
  have hpos : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have ht : Filter.Tendsto (fun M : ℕ => (M : ℝ) ^ (-((d : ℝ) / 2))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
  have h2 := (ht.const_mul C).eventually (gt_mem_nhds (show C * 0 < δ by simpa using hδ))
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1 h2
  exact ⟨max M0 1, le_max_right _ _, fun M hM => (hM0 M ((le_max_left _ _).trans hM)).le⟩

/-- **Head index** (explicit smallness of `κ`).  For constants `C, β_+, M^f, M₁^f` there is `M0` such that for
every `M ≥ M0`, every probability measure `μ` on `ℝ^d`, every pair kernel with row constant `C M^{-d/2}`
and every field with constants `M ≤ M^f`, `M₁ ≤ M₁^f`, `0 ≤ β ≤ β_+`: `weakKappa < 1/2`.  The threshold
depends on `C, β_+, M^f, M₁^f, d` only (not on `N`, `ρ`). -/
theorem wl_kappa_head (hd : 1 ≤ d) {C : ℝ} (hC : 0 ≤ C) (βp Mf M₁f : ℝ) :
    ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M → ∀ (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
      (q : Euc d → Euc d → ℝ) (hq : EWeakKernel μ (C * (M : ℝ) ^ (-((d : ℝ) / 2))) q)
      (ha : 0 ≤ C * (M : ℝ) ^ (-((d : ℝ) / 2))) {φ : Euc d → ℝ} {M₀ M₁ : ℝ}
      (hφ : IsField μ φ M₀ M₁), M₀ ≤ Mf → M₁ ≤ M₁f → ∀ β : ℝ, 0 ≤ β → β ≤ βp →
        weakKappa (wlPot hq ha hφ) β < 1 / 2 := by
  set δ : ℝ := min 1 (1 / (16 * Real.exp (Mf + M₁f + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  obtain ⟨M0, hM0, hM⟩ := wl_exists_head hd (βp * C) hδpos
  refine ⟨M0, hM0, fun M hMM μ _ q hq ha φ M₀ M₁ hφ h0 h1 β hβ hβp => ?_⟩
  refine wl_kappa_lt_half hq ha hφ hβ ?_
  have hrp : 0 ≤ (M : ℝ) ^ (-((d : ℝ) / 2)) := Real.rpow_nonneg (Nat.cast_nonneg M) _
  have h2 : β * (C * (M : ℝ) ^ (-((d : ℝ) / 2))) ≤ δ := by
    calc β * (C * (M : ℝ) ^ (-((d : ℝ) / 2))) ≤ βp * (C * (M : ℝ) ^ (-((d : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_right hβp (mul_nonneg hC hrp)
      _ = βp * C * (M : ℝ) ^ (-((d : ℝ) / 2)) := by ring
      _ ≤ δ := hM M hMM
  refine h2.trans (min_le_min le_rfl ?_)
  refine one_div_le_one_div_of_le (by positivity) ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num)

/-! ### Family bounds: resampling, linear variance, pin comparison -/

section FamilyBounds

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {a : ℝ}
  {q : E → E → ℝ} {φ : E → ℝ} {M M₁ : ℝ} {β : ℝ} {N n : ℕ} {B : Type*} [Fintype B]

/-- **`wl_resampling`** (Wu's resampling inequality for the family ensemble).  `V = wlPot hq ha hφ`, pins
`z : B → E` (pair coefficient `β/N`), `n + |B| ≤ N`, and the explicit smallness `β a ≤ min 1 (16 e^{M+M₁+1})⁻¹`. -/
theorem wl_resampling (hq : EWeakKernel μ a q) (ha : 0 ≤ a) (hφ : IsField μ φ M M₁) (hβ : 0 ≤ β)
    (hN0 : 0 < N) (hN : n + Fintype.card B ≤ N) (z : B → E)
    (hs : β * a ≤ min 1 (1 / (16 * Real.exp (M + M₁ + 1)))) (F : (Fin n → E) → ℝ)
    (hF : Measurable F) :
    evariance F (pinnedLaw (wlPot hq ha hφ) (β / N) n z)
      ≤ 2 * ∑ i, ∫⁻ x, evariance (fun w => F (Function.update x i w))
          (siteKernel μ (pinnedDensity (wlPot hq ha hφ) (β / N) n z) i x)
            ∂(pinnedLaw (wlPot hq ha hφ) (β / N) n z) :=
  weak_resampling (wlPot hq ha hφ) hβ hN0 hN z (wl_kappa_lt_half hq ha hφ hβ hs).le F hF

/-- **`wl_linear`**: `Var(∑ f(y_i)) ≤ 2 n Var_{π}(f)` for the family ensemble (`π` its one-point
marginal, all marginals agree by exchangeability). -/
theorem wl_linear [NeZero n] (hq : EWeakKernel μ a q) (ha : 0 ≤ a) (hφ : IsField μ φ M M₁)
    (hβ : 0 ≤ β) (hN0 : 0 < N) (hN : n + Fintype.card B ≤ N) (z : B → E)
    (hs : β * a ≤ min 1 (1 / (16 * Real.exp (M + M₁ + 1)))) (f : E → ℝ) (hf : Measurable f) :
    evariance (fun y : Fin n → E => ∑ i, f (y i)) (pinnedLaw (wlPot hq ha hφ) (β / N) n z)
      ≤ 2 * n * evariance f ((pinnedLaw (wlPot hq ha hφ) (β / N) n z).map (fun x => x 0)) :=
  weak_linear_variance_symm (wlPot hq ha hφ) hβ hN0 hN z (wl_kappa_lt_half hq ha hφ hβ hs).le f hf

/-- **`wl_dobrushin`**: Dobrushin coefficients `c_ij ≤ C/N` with the explicit `C = 4 e^{M+M₁+1} β a`
(needs `β a ≤ 1`; here `C = wlPinC / 2`). -/
theorem wl_dobrushin (hq : EWeakKernel μ a q) (ha : 0 ≤ a) (hφ : IsField μ φ M M₁) (hβ : 0 ≤ β)
    (hN0 : 0 < N) (hN : n + Fintype.card B ≤ N) (z : B → E) (h1 : β * a ≤ 1) :
    ∀ i j : Fin n, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ S : Set E,
      MeasurableSet S →
      |(siteKernel μ (pinnedDensity (wlPot hq ha hφ) (β / N) n z) i x).real S
          - (siteKernel μ (pinnedDensity (wlPot hq ha hφ) (β / N) n z) i y).real S|
        ≤ 4 * Real.exp (M + M₁ + 1) * (β * a) / N := by
  intro i j hij x y hxy S hS
  refine (weak_dobrushin (wlPot hq ha hφ) hβ hN0 hN z i j hij x y hxy S hS).trans ?_
  exact div_le_div_of_nonneg_right (wl_kappa_le hq ha hφ hβ h1) (Nat.cast_nonneg N)

/-- The pin-comparison constant: `C = 8 e^{M+M₁+1} β a`, so the bounds below read `≤ C/N`. -/
def wlPinC (a M M₁ β : ℝ) : ℝ := 8 * Real.exp (M + M₁ + 1) * (β * a)

/-- **`wl_pin_tv_changed`**: replacing one pin changes every one-point marginal by `≤ C/N`
(`C = wlPinC`; needs `β a ≤ min 1 (16 e^{M+M₁+1})⁻¹`). -/
theorem wl_pin_tv_changed (hq : EWeakKernel μ a q) (ha : 0 ≤ a) (hφ : IsField μ φ M M₁)
    (hβ : 0 ≤ β) (hN0 : 0 < N) (hN : n + Fintype.card B ≤ N) (z z' : B → E) (b₀ : B)
    (hb : ∀ b, b ≠ b₀ → z b = z' b) (hs : β * a ≤ min 1 (1 / (16 * Real.exp (M + M₁ + 1))))
    (j : Fin n) {S : Set E} (hS : MeasurableSet S) :
    |((pinnedLaw (wlPot hq ha hφ) (β / N) n z).map (fun y => y j)).real S
        - ((pinnedLaw (wlPot hq ha hφ) (β / N) n z').map (fun y => y j)).real S|
      ≤ wlPinC a M M₁ β / N := by
  have h := rvh_pin_changed (wlPot hq ha hφ) hβ hN0 hN z z' b₀ hb
    (wl_kappa_lt_half hq ha hφ hβ hs).le j hS
  refine h.trans ?_
  have hk := wl_kappa_le hq ha hφ hβ (hs.trans (min_le_left _ _))
  unfold wlPinC
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  linarith

/-- **`wl_pin_tv_deleted`**: adding one pin `x` changes every one-point marginal by `≤ C/N`. -/
theorem wl_pin_tv_deleted (hq : EWeakKernel μ a q) (ha : 0 ≤ a) (hφ : IsField μ φ M M₁)
    (hβ : 0 ≤ β) (hN0 : 0 < N) (hN : n + (Fintype.card B + 1) ≤ N) (z : B → E) (x : E)
    (hs : β * a ≤ min 1 (1 / (16 * Real.exp (M + M₁ + 1)))) (j : Fin n) {S : Set E}
    (hS : MeasurableSet S) :
    |((pinnedLaw (wlPot hq ha hφ) (β / N) n (pinsWith z x)).map (fun y => y j)).real S
        - ((pinnedLaw (wlPot hq ha hφ) (β / N) n z).map (fun y => y j)).real S|
      ≤ wlPinC a M M₁ β / N := by
  have h := rvh_pin_deleted (wlPot hq ha hφ) hβ hN0 hN z x
    (wl_kappa_lt_half hq ha hφ hβ hs).le j hS
  refine h.trans ?_
  have hk := wl_kappa_le hq ha hφ hβ (hs.trans (min_le_left _ _))
  have h0 : 0 ≤ 4 * Real.exp (M + M₁ + 1) * (β * a) :=
    mul_nonneg (by positivity) (mul_nonneg hβ ha)
  unfold wlPinC
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  linarith

/-- **`wl_pin_tv_removed`**: removing one coordinate changes every one-point marginal by `≤ C/N`. -/
theorem wl_pin_tv_removed (hq : EWeakKernel μ a q) (ha : 0 ≤ a) (hφ : IsField μ φ M M₁)
    (hβ : 0 ≤ β) (hN0 : 0 < N) (hN : n + 1 + Fintype.card B ≤ N) (z : B → E)
    (hs : β * a ≤ min 1 (1 / (16 * Real.exp (M + M₁ + 1)))) (i : Fin (n + 1)) (j : Fin n)
    {S : Set E} (hS : MeasurableSet S) :
    |((pinnedLaw (wlPot hq ha hφ) (β / N) (n + 1) z).map (fun y => y (i.succAbove j))).real S
        - ((pinnedLaw (wlPot hq ha hφ) (β / N) n z).map (fun y => y j)).real S|
      ≤ wlPinC a M M₁ β / N := by
  have h := rvh_pin_removed (wlPot hq ha hφ) hβ hN0 hN z
    (wl_kappa_lt_half hq ha hφ hβ hs).le i j hS
  refine h.trans ?_
  have hk := wl_kappa_le hq ha hφ hβ (hs.trans (min_le_left _ _))
  have h0 : 0 ≤ 4 * Real.exp (M + M₁ + 1) * (β * a) :=
    mul_nonneg (by positivity) (mul_nonneg hβ ha)
  unfold wlPinC
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  linarith

end FamilyBounds

/-! ### Exchangeability of `fieldLaw` -/

/-- **Exchangeability of the field ensemble.**  `fieldLaw V ψ lam n` (one common one-body field `ψ`, symmetric
pair energy) is invariant under permutations of the coordinates.  (`wr12_pairGibbsLawE_exchangeable` does not
cover a field.) -/
theorem wl_fieldLaw_perm {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (fieldLaw V ψ lam n).map (fun y : Fin n → E => y ∘ σ) = fieldLaw V ψ lam n := by
  unfold fieldLaw
  have h1 : (fun X : Fin n → E => X ∘ σ) = ⇑(permEquiv (E := E) σ) := rfl
  rw [h1]
  exact map_withDensity_of_invariant (Measure.pi fun _ : Fin n => μ) (permEquiv σ) (pi_map_perm μ σ)
    (fieldDensity V ψ lam n) (fun X => fieldDensity_comp_perm V ψ lam σ X)

/-- `IsExchangeable` for the Euclidean field ensemble. -/
theorem wl_fieldLaw_isExchangeable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (V : WeakPotential μ) (ψ : Euc d → ℝ) (lam : ℝ) {n : ℕ} :
    HRS.Whole.IsExchangeable (fieldLaw V ψ lam n) :=
  fun σ => wl_fieldLaw_perm V ψ lam σ

/-- All one-point marginals of the field ensemble coincide (consequence of `wl_fieldLaw_perm`). -/
theorem wl_fieldLaw_marginals_eq {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsProbabilityMeasure μ] (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (i j : Fin n) :
    (fieldLaw V ψ lam n).map (fun y => y i) = (fieldLaw V ψ lam n).map (fun y => y j) := by
  have h := wl_fieldLaw_perm V ψ lam (Equiv.swap i j)
  have hm : Measurable (fun y : Fin n → E => y j) := measurable_pi_apply j
  have : (fieldLaw V ψ lam n).map (fun y => y i) =
      ((fieldLaw V ψ lam n).map (fun y : Fin n → E => y ∘ Equiv.swap i j)).map (fun y => y j) := by
    rw [Measure.map_map hm (measurable_pi_iff.2 fun k => measurable_pi_apply _)]
    congr 1
    funext y
    simp [Function.comp]
  rw [this, h]

/-! ### The crude bound `Q ≤ e^{β N a + β ∫ℓ} μ^{⊗N}` -/

section Crude

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ}

/-- **Jensen lower bound for the normaliser**: `exp(-β ∫ℓ) ≤ K_{N,β}(μ)` and the pointwise weight bound
`exp(-β N F_N^g) ≤ exp(β N a)`. -/
theorem wl3_crude_data (hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) :
    (∀ X : HRS.Whole.EucConfig d N,
      Real.exp (-β * N * HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ) ≤ Real.exp (β * N * a)) ∧
    Real.exp (-(β * ∫ x, logWeight x ∂μ)) ≤ HRS.Whole.gibbsNormalizer (rieszKernel d 0) N β μ := by
  set π : Measure (Fin N → Euc d) := Measure.pi fun _ : Fin N => μ with hπ
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hN'.ne'
  have hKo : Wr8Ok μ (fun x y : Euc d => sphericalLogKernel x y) := (hK.rowOKE ha).wr8_ok
  set I : ℝ := ∫ x, logWeight x ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => wl2_logWeight_nonneg x
  -- pointwise bound
  have hpt : ∀ X : HRS.Whole.EucConfig d N,
      -β * N * HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ ≤ β * N * a := by
    intro X
    have h1 := wl_energy_eq hK ha hℓ hN X
    have h2 := hK.wr1_pairWeight_le ha hβ hN X
    unfold pairWeightE at h2
    have h3 := Real.exp_le_exp.1 ((ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 h2)
    have h4 : 0 ≤ (1 / (N : ℝ) ^ 2) * ∑ i, logWeight (X i) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => wl2_logWeight_nonneg _)
    have h5 : HRS.Whole.pairEnergy (fun x y : Euc d => sphericalLogKernel x y) X μ =
        modEnergyE (fun x y : Euc d => sphericalLogKernel x y) X μ := rfl
    rw [h1, h5]
    nlinarith [mul_nonneg hβ hN'.le, mul_nonneg (mul_nonneg hβ hN'.le) h4]
  refine ⟨fun X => Real.exp_le_exp.2 (hpt X), ?_⟩
  -- Jensen
  have hEK : Integrable (fun X : Fin N → Euc d => modEnergyE (fun x y : Euc d => sphericalLogKernel x y) X μ) π :=
    wr8_integrable_modEnergyE hKo
  have hSℓ : Integrable (fun X : Fin N → Euc d => ∑ i, logWeight (X i)) π :=
    integrable_finsetSum _ fun i _ => integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hℓ
  have hFeq : (fun X : HRS.Whole.EucConfig d N => HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ) =
      fun X => modEnergyE (fun x y : Euc d => sphericalLogKernel x y) X μ
        + (1 / (N : ℝ) ^ 2) * ∑ i, logWeight (X i) := funext fun X => wl_energy_eq hK ha hℓ hN X
  have hFint : Integrable (fun X : HRS.Whole.EucConfig d N =>
      HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ) π := by
    rw [hFeq]; exact hEK.add (hSℓ.const_mul _)
  have hYint : Integrable (fun X : HRS.Whole.EucConfig d N =>
      -β * N * HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ) π := hFint.const_mul _
  have hWint : Integrable (fun X : HRS.Whole.EucConfig d N =>
      Real.exp (-β * N * HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ)) π :=
    Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable hYint.aestronglyMeasurable)
      (Real.exp (β * N * a)) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (hpt X))
  have hmean : ∫ X : HRS.Whole.EucConfig d N, HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ ∂π =
      -(1 / (2 * N)) * ∫ p : Euc d × Euc d, sphericalLogKernel p.1 p.2 ∂(μ.prod μ)
        + (1 / (N : ℝ) ^ 2) * ((N : ℝ) * I) := by
    have this : ∀ i : Fin N, ∫ X : Fin N → Euc d, logWeight (X i) ∂π = I := fun i =>
      integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) hℓ.aestronglyMeasurable
    have hs : ∑ i : Fin N, ∫ X : Fin N → Euc d, logWeight (X i) ∂π = N * I := by
      rw [Finset.sum_congr rfl fun i _ => this i]; simp
    rw [hFeq, integral_add hEK (hSℓ.const_mul _), integral_const_mul,
      wr8_integral_modEnergyE hKo hN, integral_finsetSum _ fun i _ =>
        integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hℓ, hs]
  have hGK : 0 ≤ ∫ p : Euc d × Euc d, sphericalLogKernel p.1 p.2 ∂(μ.prod μ) :=
    integral_nonneg fun p => HRS.MS.Comm.comm_log_nonneg _ _
  have hlow : -(β * I) ≤ ∫ X : HRS.Whole.EucConfig d N,
      -β * N * HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ ∂π := by
    rw [integral_const_mul, hmean]
    have : -β * N * (-(1 / (2 * N)) * ∫ p : Euc d × Euc d, sphericalLogKernel p.1 p.2 ∂(μ.prod μ)
        + (1 / (N : ℝ) ^ 2) * ((N : ℝ) * I)) =
        β / 2 * ∫ p : Euc d × Euc d, sphericalLogKernel p.1 p.2 ∂(μ.prod μ) - β * I := by
      field_simp
      ring
    rw [this]
    nlinarith [mul_nonneg hβ hGK]
  have hj := ConvexOn.map_integral_le (μ := π) convexOn_exp Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hYint hWint
  exact (Real.exp_le_exp.2 hlow).trans hj

/-- **`wl_Q_le_crude`** (abstract form).  `Q_{N,β} ≤ exp(β N a + β ∫ℓ) · μ^{⊗N}` for all `N ≥ 1`, `β ≥ 0`. -/
theorem wl_Q_le_crude_abs (hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) :
    HRS.Whole.modulatedGibbs (rieszKernel d 0) N β μ ≤
      ENNReal.ofReal (Real.exp (β * N * a + β * ∫ x, logWeight x ∂μ)) •
        Measure.pi fun _ : Fin N => μ := by
  obtain ⟨hw, hZ⟩ := wl3_crude_data hK ha hℓ hβ hN
  set π : Measure (Fin N → Euc d) := Measure.pi fun _ : Fin N => μ with hπ
  set I : ℝ := ∫ x, logWeight x ∂μ with hI
  unfold HRS.Whole.modulatedGibbs
  refine Measure.le_iff'.2 fun S => ?_
  have hinv : (ENNReal.ofReal (HRS.Whole.gibbsNormalizer (rieszKernel d 0) N β μ))⁻¹ ≤
      ENNReal.ofReal (Real.exp (β * I)) := by
    have h1 : ENNReal.ofReal (Real.exp (-(β * I))) ≤
        ENNReal.ofReal (HRS.Whole.gibbsNormalizer (rieszKernel d 0) N β μ) :=
      ENNReal.ofReal_le_ofReal hZ
    have h2 := ENNReal.inv_le_inv.2 h1
    rwa [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg] at h2
  rw [Measure.smul_apply, withDensity_apply' _ S, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  calc (ENNReal.ofReal (HRS.Whole.gibbsNormalizer (rieszKernel d 0) N β μ))⁻¹ *
        ∫⁻ X in S, ENNReal.ofReal (Real.exp (-β * N * HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ)) ∂π
      ≤ ENNReal.ofReal (Real.exp (β * I)) *
        ∫⁻ X in S, ENNReal.ofReal (Real.exp (β * N * a)) ∂π := by
        refine mul_le_mul' hinv (lintegral_mono fun X => ?_)
        exact ENNReal.ofReal_le_ofReal (hw X)
    _ = ENNReal.ofReal (Real.exp (β * N * a + β * I)) * π S := by
        rw [setLIntegral_const, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add]
        congr 3
        ring

end Crude

/-- **`wl_Q_le_crude`** (ρ-level, `N ≥ 1`).  `∃ C Cℓ`, for all `ρ`, `β ≥ 0`, `N ≥ 1`:
`Q_{N,β}(μ) ≤ ofReal (exp (β N C + β Cℓ)) • μ^{⊗N}`. -/
theorem wl_Q_le_crude (hd : 2 ≤ d) (A : ℝ) : ∃ C Cl : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 ≤ β → ∀ N : ℕ, 1 ≤ N →
      HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (Real.exp (β * N * C + β * Cl)) •
          Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ := by
  obtain ⟨C, Cl, hC0, h⟩ := wl_Q_eq_fieldLaw hd A
  refine ⟨C, Cl, hC0, fun ρ hρ hA β hβ N hN => ?_⟩
  have := wl_isProb hρ
  obtain ⟨hK, hℓ, hℓle, -, -⟩ := h ρ hρ hA β hβ N hN
  refine (wl_Q_le_crude_abs hK hC0 hℓ hβ hN).trans ?_
  refine Measure.le_iff'.2 fun S => ?_
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
  nlinarith [mul_le_mul_of_nonneg_left hℓle hβ]

end HRS.MS.Wl
