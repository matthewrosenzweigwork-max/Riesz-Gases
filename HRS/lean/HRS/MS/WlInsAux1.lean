import HRS.MS.WlCavAux2
import HRS.MS.WlLin
import HRS.MS.WrInsAux2

/-!
# HRS.MS.WlInsAux1 -- pole ensembles as exponential tilts, family membership, uniform pole variance (WL-7, part 1)

Packet WL-7 of `docs/WR_LOG_PLAN.md` (Step 9 of the proof of `r2_log_static`).  Infrastructure lemmas, not manuscript
rows.  Namespace `HRS.MS.Wl`, helper prefix `wl7_`.  Notation: `μ = withDensityReal ρ`, `K = sphericalLogKernel`,
`λ = β/N`, `n = N - 1` free particles, `P_n^0 = wl_cavLaw μ β N n`, `P_n^{x,t} = wl_poleLaw μ β N n t x`,
`X_x = wl7_X β N x = -λ ∑ K(x, ·)`.

* `wl7_pole_eq_tilted` (generic in a weak potential `V`): `wl6_law` of the pole field is the exponential tilt of the
  cavity law by `-c ∑ q(y_k, x)`; `wl7_poleLaw_eq_tilted`: `P^{x,t} = P_n^0.tilted (t X_x)` for `t ≥ 0`.
* `wl7_integrable_coord`, `wl7_integrable_X`: `X_x ∈ L¹(P_n^0)` (one-particle density bound `wl6_one_le` and exchangeability
  of the marginals), so that no Bochner junk value enters the right derivative.
* `wl7_poleLaw_eq_Pens`: for `n + 1 = N`, `P^{x,t}_n = wl5_Pens μ VK (β/N) n v ![t] ![x]` with `v = λ rowIntE K μ`
  (the pole ensemble is a member of the family `WlFam` of `WlSmlAux2`; the discrepancy `(N-n) λ rowIntE K μ` between the
  background `β Kμ` of `Q_N` and the background `(nλ) Kμ` of the family is the field `v`, `|v| ≤ βp C_K / N`).
* `wl7_pole_evariance` (uniform): for `d ≥ 2`, `A`, `βp` there is `C ≥ 0` (before `ρ, β, N, x, t, f`) with
  `evariance (∑ f(Y_i)) P^{x,t}_{N-1} ≤ C (N-1) ∫ ‖f‖² dμ` for every probability density `ρ` with `HasSphericalBound A ρ`,
  `β ∈ (0, βp]`, all `N ≥ 2`, `t ∈ [0,1]`, measurable `f` (`N ≥ N0`: `wl_pole_linear`; `N < N0`:
  `wl_pole_linear_small`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.External HRS.MS.Wr

section Generic

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- The exponent of the pole tilt: `-c ∑_k q(y_k, x)`. -/
def wl7_poleExp (q : E → E → ℝ) (c : ℝ) (x : E) {n : ℕ} (Y : Fin n → E) : ℝ :=
  -c * ∑ k, q (Y k) x

lemma wl7_poleExp_measurable (V : WeakPotential μ) (c : ℝ) (x : E) (n : ℕ) :
    Measurable (wl7_poleExp V.q c x (n := n)) :=
  (Finset.measurable_sum _ fun k _ =>
    V.measurable_q.comp ((measurable_pi_apply k).prodMk measurable_const)).const_mul _

lemma wl7_poleExp_le_zero (V : WeakPotential μ) {c : ℝ} (hc : 0 ≤ c) (x : E) {n : ℕ} (Y : Fin n → E) :
    wl7_poleExp V.q c x Y ≤ 0 := by
  unfold wl7_poleExp
  have : 0 ≤ ∑ k, V.q (Y k) x := Finset.sum_nonneg fun k _ => V.q_nonneg _ _
  nlinarith

/-- **The pole ensemble is the exponential tilt of the cavity ensemble**:
`P^{x,t} = P_n^0.tilted (-t λ ∑ q(y_k, x))` (`c = t λ`). -/
lemma wl7_pole_eq_tilted (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ} (hψ : IsField μ ψ M M₁)
    (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : E) :
    wl6_law μ V.q (wl6_pole V.q ψ c x) lam n =
      (wl6_law μ V.q ψ lam n).tilted (wl7_poleExp V.q c x (n := n)) := by
  have hpole := wl6_isField_pole V hψ hc hrow x
  set P0 := wl6_law μ V.q ψ lam n with hP0
  set w0 : (Fin n → E) → ℝ≥0∞ := wl6_weight V.q ψ lam with hw0
  set wp : (Fin n → E) → ℝ≥0∞ := wl6_weight V.q (wl6_pole V.q ψ c x) lam with hwp
  set N0 := wl6_norm μ V.q ψ lam n with hN0
  set Np := wl6_norm μ V.q (wl6_pole V.q ψ c x) lam n with hNp
  have hN00 : N0 ≠ 0 := wl6_norm_ne_zero V hψ n
  have hN0t : N0 ≠ ⊤ := wl6_norm_ne_top V hψ hlam n
  have hNp0 : Np ≠ 0 := wl6_norm_ne_zero V hpole n
  have hNpt : Np ≠ ⊤ := wl6_norm_ne_top V hpole hlam n
  set g : (Fin n → E) → ℝ≥0∞ := fun Y => ENNReal.ofReal (Real.exp (wl7_poleExp V.q c x Y)) with hg
  have hgm : Measurable g :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wl7_poleExp_measurable V c x n))
  have hwm : Measurable w0 := wl6_measurable_weight V hψ.measurable lam n
  have hwpm : Measurable wp := wl6_measurable_weight V hpole.measurable lam n
  have hwp_eq : ∀ Y, wp Y = g Y * w0 Y := fun Y => wl6_fieldWeight_pole V ψ lam c x Y
  have hD : Measurable (fun Y => w0 Y * N0⁻¹) := hwm.mul measurable_const
  have hNp_eq : Np = ∫⁻ Y, g Y * w0 Y ∂(Measure.pi fun _ : Fin n => μ) := by
    rw [hNp]
    unfold wl6_norm
    exact lintegral_congr hwp_eq
  have hint : ∫⁻ Y, g Y ∂P0 = N0⁻¹ * Np := by
    rw [hP0]
    unfold wl6_law
    rw [lintegral_withDensity_eq_lintegral_mul _ hD hgm, hNp_eq, ← lintegral_const_mul' _ _
      (ENNReal.inv_ne_top.2 hN00)]
    refine lintegral_congr fun Y => ?_
    simp only [Pi.mul_apply]
    ring
  have hpos : 0 < N0⁻¹ * Np := by
    refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hN0t) hNp0
  have hfin : N0⁻¹ * Np ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hN00) hNpt
  have hprob : IsProbabilityMeasure P0 := (fieldSpec (V := V) hψ hlam n).isProb
  have hbd : Integrable (fun Y => Real.exp (wl7_poleExp V.q c x Y)) P0 := by
    refine Integrable.of_bound (C := 1)
      (Real.measurable_exp.comp (wl7_poleExp_measurable V c x n)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (wl7_poleExp_le_zero V hc x Y)
  have hZ : ENNReal.ofReal (∫ Y, Real.exp (wl7_poleExp V.q c x Y) ∂P0) = N0⁻¹ * Np := by
    rw [ofReal_integral_eq_lintegral_ofReal hbd (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
      ← hint]
  have hZpos : 0 < ∫ Y, Real.exp (wl7_poleExp V.q c x Y) ∂P0 := integral_exp_pos hbd
  have hP0def : P0 = (Measure.pi fun _ : Fin n => μ).withDensity fun Y => w0 Y * N0⁻¹ := rfl
  unfold Measure.tilted
  have hdens : (fun Y => ENNReal.ofReal (Real.exp (wl7_poleExp V.q c x Y) /
      ∫ Y, Real.exp (wl7_poleExp V.q c x Y) ∂P0)) = fun Y => g Y * (N0⁻¹ * Np)⁻¹ := by
    funext Y
    rw [ENNReal.ofReal_div_of_pos hZpos, hZ, div_eq_mul_inv]
  rw [hdens]
  conv_rhs => rw [hP0def]
  have hmul : (Measure.pi fun _ : Fin n => μ).withDensity
      ((fun Y => w0 Y * N0⁻¹) * fun Y => g Y * (N0⁻¹ * Np)⁻¹) =
      ((Measure.pi fun _ : Fin n => μ).withDensity fun Y => w0 Y * N0⁻¹).withDensity
        (fun Y => g Y * (N0⁻¹ * Np)⁻¹) :=
    withDensity_mul _ hD (hgm.mul measurable_const)
  rw [← hmul]
  refine congrArg (fun f => (Measure.pi fun _ : Fin n => μ).withDensity f) ?_
  funext Y
  have e1 : (N0⁻¹ * Np)⁻¹ = N0 * Np⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hN0t)) (Or.inl (ENNReal.inv_ne_top.2 hN00)),
      inv_inv]
  have e2 : N0⁻¹ * N0 = 1 := ENNReal.inv_mul_cancel hN00 hN0t
  show wp Y * Np⁻¹ = w0 Y * N0⁻¹ * (g Y * (N0⁻¹ * Np)⁻¹)
  rw [hwp_eq Y, e1]
  calc g Y * w0 Y * Np⁻¹ = (N0⁻¹ * N0) * (g Y * w0 Y * Np⁻¹) := by rw [e2, one_mul]
    _ = _ := by ring

/-- Integrability of one-coordinate functions under the field ensemble: every `f ∈ L¹(μ)` is integrable along
every coordinate of `fieldLaw V ψ lam (m+1)` (one-particle density bound and exchangeability of the marginals). -/
lemma wl7_integrable_coord (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ} (hψ : IsField μ ψ M M₁)
    (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (m : ℕ) {f : E → ℝ} (hfm : Measurable f)
    (hf : Integrable f μ) (j : Fin (m + 1)) :
    Integrable (fun Y : Fin (m + 1) → E => f (Y j)) (fieldLaw V ψ lam (m + 1)) := by
  have h1 := wl6_one_le V hψ hlam hrow m
  have hmarg : (fieldLaw V ψ lam (m + 1)).map (fun Y => Y j) ≤
      (ENNReal.ofReal (Real.exp (M₁ + lam * m * a)) * ENNReal.ofReal (Real.exp M)) • μ := by
    rw [wl_fieldLaw_marginals_eq V ψ lam j 0]
    refine wl6_le_smul_trans h1 ?_ le_rfl
    refine Measure.le_iff.2 fun A hA => ?_
    rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hψ.le x))
  have hi : Integrable f ((fieldLaw V ψ lam (m + 1)).map (fun Y => Y j)) :=
    (hf.smul_measure (c := ENNReal.ofReal (Real.exp (M₁ + lam * m * a)) *
      ENNReal.ofReal (Real.exp M)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ENNReal.ofReal_ne_top)).mono_measure hmarg
  exact (integrable_map_measure hfm.aestronglyMeasurable (measurable_pi_apply j).aemeasurable).1 hi

end Generic

/-! ### The Euclidean ensembles of `Q_N` -/

section EucPart

variable {d : ℕ}

/-- The pole exponent `X_x(Y) = -(β/N) ∑_i K(x, Y_i)` (`K = sphericalLogKernel`), so that
`exp (t X_x) = exp (-t λ ∑ K(x, y_i))`, `λ = β/N`. -/
def wl7_X (β : ℝ) (N : ℕ) (x : Euc d) {n : ℕ} (Y : Fin n → Euc d) : ℝ :=
  -(β / (N : ℝ)) * ∑ i, sphericalLogKernel x (Y i)

lemma wl7_X_measurable (β : ℝ) (N : ℕ) (x : Euc d) (n : ℕ) : Measurable (wl7_X β N x (n := n)) :=
  (Finset.measurable_sum _ fun i _ =>
    wl_K_measurable.comp (measurable_const.prodMk (measurable_pi_apply i))).const_mul _

lemma wl7_X_le_zero {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) (x : Euc d) {n : ℕ} (Y : Fin n → Euc d) :
    wl7_X β N x Y ≤ 0 := by
  unfold wl7_X
  have h1 : 0 ≤ ∑ i, sphericalLogKernel x (Y i) :=
    Finset.sum_nonneg fun i _ => HRS.MS.Comm.comm_log_nonneg x (Y i)
  have h2 : -(β / (N : ℝ)) ≤ 0 := neg_nonpos.2 (div_nonneg hβ (Nat.cast_nonneg _))
  exact mul_nonpos_of_nonpos_of_nonneg h2 h1

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ}

/-- The weak potential of the field ensembles of `Q_N` (kernel `K`, field `wl_Qfield`). -/
def wl7_V (hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) : WeakPotential μ :=
  wlPot hK ha (wl_isField_Qfield hK ha hℓ hβ N)

lemma wl7_hlam {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) : 0 ≤ β / (N : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)

section Ens

variable (hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y)) (ha : 0 ≤ a)
  (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {β : ℝ} (hβ : 0 ≤ β) (N : ℕ)

include hK ha hℓ hβ

lemma wl7_hrow : ∀ x, ∫ y, (wl7_V hK ha hℓ hβ N).q x y ∂μ ≤ a := fun x => hK.wr1_rowInt_le ha x

lemma wl7_cavLaw_eq (n : ℕ) : wl_cavLaw μ β N n =
    fieldLaw (wl7_V hK ha hℓ hβ N) (wl_Qfield μ β N) (β / N) n := rfl

lemma wl7_poleLaw_eq (t : ℝ) (x : Euc d) (n : ℕ) : wl_poleLaw μ β N n t x =
    fieldLaw (wl7_V hK ha hℓ hβ N) (wl6_pole (wl7_V hK ha hℓ hβ N).q (wl_Qfield μ β N) (t * (β / N)) x)
      (β / N) n := rfl

lemma wl7_cav_isProb (n : ℕ) : IsProbabilityMeasure (wl_cavLaw μ β N n) := by
  rw [wl7_cavLaw_eq hK ha hℓ hβ N n]
  exact (fieldSpec (V := wl7_V hK ha hℓ hβ N) (wl_isField_Qfield hK ha hℓ hβ N)
    (wl7_hlam hβ N) n).isProb

lemma wl7_pole_isProb {t : ℝ} (ht : 0 ≤ t) (x : Euc d) (n : ℕ) :
    IsProbabilityMeasure (wl_poleLaw μ β N n t x) := by
  rw [wl7_poleLaw_eq hK ha hℓ hβ N t x n]
  exact (fieldSpec (V := wl7_V hK ha hℓ hβ N)
    (wl6_isField_pole (wl7_V hK ha hℓ hβ N) (wl_isField_Qfield hK ha hℓ hβ N)
      (mul_nonneg ht (wl7_hlam hβ N)) (wl7_hrow hK ha hℓ hβ N) x) (wl7_hlam hβ N) n).isProb

lemma wl7_poleLaw_zero (x : Euc d) (n : ℕ) : wl_poleLaw μ β N n 0 x = wl_cavLaw μ β N n := by
  unfold wl_poleLaw wl_cavLaw wl6_pole
  simp

/-- **The pole ensemble is the tilt of the cavity ensemble by the pole exponent**:
`P^{x,t}_n = P_n^0.tilted (t X_x)`, `t ≥ 0`. -/
lemma wl7_poleLaw_eq_tilted {t : ℝ} (ht : 0 ≤ t) (x : Euc d) (n : ℕ) :
    wl_poleLaw μ β N n t x = (wl_cavLaw μ β N n).tilted (fun Y => t * wl7_X β N x Y) := by
  have h := wl7_pole_eq_tilted (wl7_V hK ha hℓ hβ N) (wl_isField_Qfield hK ha hℓ hβ N)
    (wl7_hlam hβ N) (wl7_hrow hK ha hℓ hβ N) (mul_nonneg ht (wl7_hlam hβ N)) n x
  have hfun : (fun Y : Fin n → Euc d => t * wl7_X β N x Y) =
      wl7_poleExp (wl7_V hK ha hℓ hβ N).q (t * (β / N)) x := by
    funext Y
    unfold wl7_X wl7_poleExp
    have : ∑ i, sphericalLogKernel x (Y i) = ∑ i, (wl7_V hK ha hℓ hβ N).q (Y i) x :=
      Finset.sum_congr rfl fun i _ => wl_K_symm x (Y i)
    rw [this]
    ring
  rw [hfun]
  exact h

lemma wl7_cav_exchangeable (n : ℕ) : HRS.External.Entropy.IsExchangeable (wl_cavLaw μ β N n) := by
  rw [wl7_cavLaw_eq hK ha hℓ hβ N n]
  exact wl_fieldLaw_isExchangeable _ _ _

lemma wl7_pole_exchangeable (t : ℝ) (x : Euc d) (n : ℕ) :
    HRS.External.Entropy.IsExchangeable (wl_poleLaw μ β N n t x) := by
  rw [wl7_poleLaw_eq hK ha hℓ hβ N t x n]
  exact wl_fieldLaw_isExchangeable _ _ _

/-- `X_x ∈ L¹(P_n^0)` for `n = m + 1` (one-particle density bound, exchangeability). -/
lemma wl7_integrable_X (m : ℕ) (x : Euc d) :
    Integrable (wl7_X β N x (n := m + 1)) (wl_cavLaw μ β N (m + 1)) := by
  rw [wl7_cavLaw_eq hK ha hℓ hβ N (m + 1)]
  refine (integrable_finsetSum _ fun j _ => ?_).const_mul _
  exact wl7_integrable_coord (wl7_V hK ha hℓ hβ N) (wl_isField_Qfield hK ha hℓ hβ N)
    (wl7_hlam hβ N) (wl7_hrow hK ha hℓ hβ N) m (hK.wr1_measurable_left x) (hK.wr1_integrable_row x) j

/-- **The pole ensemble is a member of the family `WlFam`** (one pole `z = x` of weight `t`, field
`v = λ rowIntE K μ`, `n + 1 = N`): `P^{x,t}_n = wl5_Pens μ VK (β/N) n v t z` for every `VK` with `VK.q = K`. -/
lemma wl7_poleLaw_eq_Pens {n : ℕ} (hn : n + 1 = N) (t : ℝ) (x : Euc d) (VK : WeakPotential μ)
    (hVK : VK.q = fun x y : Euc d => sphericalLogKernel x y) :
    wl_poleLaw μ β N n t x = wl5_Pens μ VK (β / N)  n
      (fun y => (β / N) * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ y)
      (fun _ : Fin 1 => t) (fun _ : Fin 1 => x) := by
  rw [wl7_poleLaw_eq hK ha hℓ hβ N t x n]
  unfold wl5_Pens
  rw [wl6_fieldLaw_eq, wl6_fieldLaw_eq, hVK]
  show wl6_law μ (fun x y : Euc d => sphericalLogKernel x y) _ (β / N) n = _
  congr 1
  funext y
  have hN : ((n : ℝ) + 1) = N := by exact_mod_cast hn
  unfold wl6_pole wl_Qfield wl4b_psi wl4b_g
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have hq : (wl7_V hK ha hℓ hβ N).q y x = sphericalLogKernel y x := rfl
  rw [hq]
  have h1 : (n : ℝ) * (β / N) + β / N = β := by
    have : (N : ℝ) ≠ 0 := by rw [← hN]; positivity
    rw [← hN] at this ⊢
    field_simp
  linear_combination (rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ y) * h1.symm

end Ens

end EucPart

/-! ### Uniform variance of linear statistics under the pole ensembles -/

section PoleVar

variable {d : ℕ}

/-- **Pole-ensemble linear variance** (`wl_pole_linear` with the pole at `x`, `n = N - 1`, `v = λ rowIntE K μ`).
`C` depends on `d, A, βp` only (quantified before `ρ, β, N, x, t, f`): for every probability density `ρ` with
`HasSphericalBound A ρ`, `β ∈ (0, βp]`, every `N ≥ 2` (for `N ≥ N0` by the calibrated transfer, for the finitely many
smaller `N` by the crude bound), every pole `x`, weight `t ∈ [0,1]` and measurable `f`:
`Var_{P^{x,t}_{N-1}} (∑ f(Y_i)) ≤ C (N-1) ∫ |f|² dμ` (the pole factor `≤ 1` is dropped). -/
theorem wl7_pole_evariance (hd : 2 ≤ d) (A βp : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
      ∀ x : Euc d, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ f : Euc d → ℝ, Measurable f →
        evariance (fun Y : Fin (N - 1) → Euc d => ∑ i, f (Y i))
            (wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x) ≤
          ENNReal.ofReal C * (((N - 1 : ℕ) : ℝ≥0∞) * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  obtain ⟨Cq, hCq0, hCq⟩ := wl_qm_weak hd A
  obtain ⟨M0, hM0, hlin⟩ := wl_pole_linear hd A βp (βp * CK)
  obtain ⟨N0, C1, hC10, h1⟩ := hlin M0 le_rfl
  obtain ⟨C2, hC20, h2⟩ := wl_pole_linear_small hd A βp (βp * CK) N0
  refine ⟨max C1 C2, le_max_of_le_left hC10, fun ρ hρ hA β hβ hββp N hN x t ht0 ht1 f hf => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hK, hℓ, -, -, -⟩ := hQ ρ hρ hA β hβ.le N (by omega)
  set n : ℕ := N - 1 with hn
  have hnN : n + 1 = N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set VK : WeakPotential μ := wl7_V hK hCK0 hℓ hβ.le N with hVK
  have hq := hCq ρ hρ hA M0 hM0
  have haq : 0 ≤ Cq * (M0 : ℝ) ^ (-((d : ℝ) / 2)) := mul_nonneg hCq0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  set VQ : WeakPotential μ := wlPot hq haq (wl_isField_bdd (μ := μ) (v := fun _ => (0 : ℝ))
    measurable_const (b := 0) (by simp)) with hVQ
  have hv : ∀ y, |(β / N) * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ y| ≤ βp * CK / N := by
    intro y
    have h0 := hK.wr1_rowInt_nonneg y
    have h1' := hK.wr1_rowInt_le hCK0 y
    rw [abs_of_nonneg (mul_nonneg (div_nonneg hβ.le hNpos.le) h0), div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hNpos]
    exact mul_le_mul hββp h1' h0 (hβ.le.trans hββp)
  have hF : WlFam (βp * CK) β N n (fun _ : Fin 1 => t) (fun _ : Fin 1 => x)
      (fun y => (β / N) * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ y) :=
    { one_le := by omega
      n_le := by omega
      β_nonneg := hβ.le
      p_le := by norm_num
      t_nonneg := fun _ => ht0
      t_le := fun _ => ht1
      v_meas := (hK.wr1_measurable_rowInt).const_mul _
      v_bdd := hv }
  rw [wl7_poleLaw_eq_Pens hK hCK0 hℓ hβ.le N hnN t x VK rfl]
  have hmain : evariance (fun Y : Fin n → Euc d => ∑ i, f (Y i))
      (wl5_Pens μ VK (β / N) n (fun y => (β / N) * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ y)
        (fun _ : Fin 1 => t) (fun _ : Fin 1 => x)) ≤
      ENNReal.ofReal (max C1 C2) * (n * ∫⁻ y, ENNReal.ofReal (Real.exp (-((β / N) *
        ∑ a : Fin 1, (fun _ : Fin 1 => t) a * sphericalLogKernel y ((fun _ : Fin 1 => x) a)))) * ‖f y‖ₑ ^ 2 ∂μ) := by
    by_cases hNN : N0 ≤ N
    · exact (h1 ρ hρ hA β hβ hββp N n hNN (by omega) 1 _ _ _ hF VK VQ rfl rfl f hf).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
    · exact (h2 ρ hρ hA β hβ.le hββp N n (by omega) 1 _ _ _ hF VK rfl f hf).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl)
  refine hmain.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl (lintegral_mono fun y => ?_)))
  have hexp : ENNReal.ofReal (Real.exp (-((β / N) *
      ∑ a : Fin 1, (fun _ : Fin 1 => t) a * sphericalLogKernel y ((fun _ : Fin 1 => x) a)))) ≤ 1 := by
    refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
    have : 0 ≤ (β / N) * ∑ a : Fin 1, (fun _ : Fin 1 => t) a * sphericalLogKernel y ((fun _ : Fin 1 => x) a) :=
      mul_nonneg (div_nonneg hβ.le hNpos.le) (Finset.sum_nonneg fun a _ =>
        mul_nonneg ht0 (HRS.MS.Comm.comm_log_nonneg y x))
    linarith
  calc _ ≤ 1 * ‖f y‖ₑ ^ 2 := mul_le_mul' hexp le_rfl
    _ = _ := one_mul _

end PoleVar

end HRS.MS.Wl
