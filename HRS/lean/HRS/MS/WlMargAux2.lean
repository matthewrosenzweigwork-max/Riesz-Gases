import HRS.MS.WlMargAux1

/-!
# HRS.MS.WlMargAux2 -- the marginal equation, absorption, `HasLogMarginalDensityBounds` (WL-8, part 2)

Packet WL-8 of `docs/WR_LOG_PLAN.md` (Step 10 of the proof of `r2_log_static`, conjunct 3).  Infrastructure
lemmas, not manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl8_`.  Notation: `μ = withDensityReal ρ`,
`K = sphericalLogKernel`, `ℓ = logWeight`, `λ = β/N`, `n = N - 1`, `Q = modulatedGibbs (rieszKernel d 0) N β μ`,
`π_N = HRS.Whole.firstMarginal Q = μ.withDensity θ`, `θ = wl_theta μ β N`, `ν_n = HRS.Whole.firstMarginal (wl_cavLaw μ β N (N-1))`,
`h_N = wl_hN β N = -λ ℓ`, `D_N = wl_insDefect μ β N (N-1)`, `Z = wl_cavZ μ β N`.

* `wl8_Phi_eq_integral`, `wl8_cavPhi_eq`: the pole factor `Φ_x = N_n(pole at x)/N_n` equals `P_n^0[e^{-λ ∑ K(x,y_i)}]`,
  so `log Φ_x = A_x(1) = wl_insPressure ... x 1` (all quantities finite and positive, no junk).
* `wl8_cav_marginal_le`: `ν_n ≤ Cν • μ` (one-particle bound `wl6_one_le`), `ν_n` a probability measure.
* `wl8_insPressure_deriv`: `D_N(x) = A_x(1) - E_{P_n^0}[X_x]` and `E_{P_n^0}[X_x] = -λ n ∫ K(x,y) dν_n(y)`
  (exchangeability: all one-point marginals of `P_n^0` equal `ν_n`).
* **`wl_marginal_equation`** (TeX `eq:r2-log-marginal-equation`): for every `x`
  `log θ(x) + β ∫ K(x,y)(θ(y) - 1) dμ(y) = (D_N(x) + h_N(x)) + β (∫ K(x,y) dπ_N(y) - ∫ K(x,y) dν_n(y))
   + λ ∫ K(x,y) dν_n(y) - log Z`  (`c_N = log Z`; `K(μ z_N) = K π_N - Kμ`, the `β Kμ` terms cancel).
* **`wl_marginal_L2`**: `‖z_N‖_{L²(μ)} ≤ C/N` with `z_N = θ - 1` (`wr13e_L2_assemble`/`wr13e_absorption`, with
  `wl8_K_psd`, `wl8_cv_L2`, `wl_insertion_defect`, `wl_cavity_tv`, `wl_density_sup`).
* **`wl_hasLogMarginalDensityBounds`**: the frozen predicate `HasLogMarginalDensityBounds` of
  `HRS/Whole/Static.lean` (conjunct 3 of `r2_log_static`), for all `ρ` with `HasSphericalBound A ρ`,
  `β ∈ [βm, βp]`, `N ≥ 2`, with the version `φ = θ` (already a pointwise bound for every `x`: `wl_density_sup`
  gives `0 ≤ θ(x) ≤ C(1+|x|²)^{-β/(2N)}` for all `x`, so no truncation is needed).

Adjustment with respect to the plan (documented, harmless): no truncation of a version and no separate small-`N`
argument are needed, because `wl_density_sup`, `wl_insertion_defect` and `wl_cavity_tv` are already uniform over
all `N ≥ 2` and give the pointwise bounds for every `x`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.External HRS.MS.Wr

/-! ### The pole factor is a Laplace transform of the cavity law -/

section Generic

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- `Φ_x = N_n(pole at x) / N_n = ∫ exp(-lam ∑ q(y_k, x)) dP_n^0`. -/
lemma wl8_Phi_eq_integral (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ} (hψ : IsField μ ψ M M₁)
    (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (n : ℕ) (x : E) :
    wl6_Phi μ V.q ψ lam n x = ∫ Y, Real.exp (wl7_poleExp V.q lam x Y) ∂(wl6_law μ V.q ψ lam n) := by
  have hpole := wl6_isField_pole V hψ hlam hrow x
  set P0 := wl6_law μ V.q ψ lam n with hP0
  set w0 : (Fin n → E) → ℝ≥0∞ := wl6_weight V.q ψ lam with hw0
  set N0 := wl6_norm μ V.q ψ lam n with hN0
  set Np := wl6_norm μ V.q (wl6_pole V.q ψ lam x) lam n with hNp
  have hN00 : N0 ≠ 0 := wl6_norm_ne_zero V hψ n
  have hN0t : N0 ≠ ⊤ := wl6_norm_ne_top V hψ hlam n
  have hNpt : Np ≠ ⊤ := wl6_norm_ne_top V hpole hlam n
  set g : (Fin n → E) → ℝ≥0∞ := fun Y => ENNReal.ofReal (Real.exp (wl7_poleExp V.q lam x Y)) with hg
  have hgm : Measurable g :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wl7_poleExp_measurable V lam x n))
  have hwm : Measurable w0 := wl6_measurable_weight V hψ.measurable lam n
  have hwp_eq : ∀ Y, wl6_weight V.q (wl6_pole V.q ψ lam x) lam Y = g Y * w0 Y :=
    fun Y => wl6_fieldWeight_pole V ψ lam lam x Y
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
  have hprob : IsProbabilityMeasure P0 := (fieldSpec (V := V) hψ hlam n).isProb
  have hbd : Integrable (fun Y => Real.exp (wl7_poleExp V.q lam x Y)) P0 := by
    refine Integrable.of_bound (C := 1)
      (Real.measurable_exp.comp (wl7_poleExp_measurable V lam x n)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (wl7_poleExp_le_zero V hlam x Y)
  have hZ : ENNReal.ofReal (∫ Y, Real.exp (wl7_poleExp V.q lam x Y) ∂P0) = N0⁻¹ * Np := by
    rw [ofReal_integral_eq_lintegral_ofReal hbd (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
      ← hint]
  have hfin : N0⁻¹ * Np ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hN00) hNpt
  have h1 : ∫ Y, Real.exp (wl7_poleExp V.q lam x Y) ∂P0 = (N0⁻¹ * Np).toReal := by
    rw [← hZ, ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)]
  rw [h1, ENNReal.toReal_mul, ENNReal.toReal_inv]
  unfold wl6_Phi
  rw [← hNp, ← hN0]
  ring

end Generic

/-! ### The cavity ensemble of `Q_N` -/

section Euc

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ}
  (hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y)) (ha : 0 ≤ a)
  (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {β : ℝ} (hβ : 0 ≤ β)

include hK ha hℓ hβ

/-- `Φ_x = P_n^0[e^{X_x}]` with `X_x = -λ ∑ K(x, y_i)` (`N = m + 2`, `n = m + 1`). -/
lemma wl8_cavPhi_eq (m : ℕ) (x : Euc d) :
    wl_cavPhi μ β (m + 2) x =
      ∫ Y, Real.exp (wl7_X β (m + 2) x Y) ∂(wl_cavLaw μ β (m + 2) (m + 1)) := by
  have h := wl8_Phi_eq_integral (wl7_V hK ha hℓ hβ (m + 2)) (wl_isField_Qfield hK ha hℓ hβ (m + 2))
    (wl7_hlam hβ (m + 2)) (wl7_hrow hK ha hℓ hβ (m + 2)) (m + 1) x
  unfold wl_cavPhi
  refine h.trans ?_
  show _ = ∫ Y, Real.exp (wl7_X β (m + 2) x Y)
    ∂(wl6_law μ wl6_K (wl_Qfield μ β (m + 2)) (β / ((m + 2 : ℕ) : ℝ)) (m + 1))
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  show Real.exp (wl7_poleExp (fun x y : Euc d => sphericalLogKernel x y) (β / ((m + 2 : ℕ) : ℝ)) x Y) = _
  congr 1
  unfold wl7_X wl7_poleExp
  have : ∑ i, sphericalLogKernel x (Y i) = ∑ i, sphericalLogKernel (Y i) x :=
    Finset.sum_congr rfl fun i _ => wl_K_symm x (Y i)
  rw [this]

lemma wl8_cavPhi_pos (m : ℕ) (x : Euc d) : 0 < wl_cavPhi μ β (m + 2) x := by
  have hψ := wl_isField_Qfield hK ha hℓ hβ (m + 2)
  have hpole := wl6_isField_pole (wl7_V hK ha hℓ hβ (m + 2)) hψ (wl7_hlam hβ (m + 2))
    (wl7_hrow hK ha hℓ hβ (m + 2)) x
  exact div_pos (wl6_norm_toReal_pos (wl7_V hK ha hℓ hβ (m + 2)) hpole (wl7_hlam hβ (m + 2)) (m + 1))
    (wl6_norm_toReal_pos (wl7_V hK ha hℓ hβ (m + 2)) hψ (wl7_hlam hβ (m + 2)) (m + 1))

lemma wl8_cavZ_pos (m : ℕ) : 0 < wl_cavZ μ β (m + 2) :=
  wl6_Z_pos (wl7_V hK ha hℓ hβ (m + 2)) (wl_isField_Qfield hK ha hℓ hβ (m + 2)) (wl7_hlam hβ (m + 2)) (m + 1)

/-- `log θ = β Kμ + h_N + log Φ - log Z`. -/
lemma wl8_log_theta (m : ℕ) (x : Euc d) :
    Real.log (wl_theta μ β (m + 2) x) = β * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ x +
      wl_hN β (m + 2) x + Real.log (wl_cavPhi μ β (m + 2) x) - Real.log (wl_cavZ μ β (m + 2)) := by
  have h1 := wl8_cavPhi_pos hK ha hℓ hβ m x
  have h2 := wl8_cavZ_pos hK ha hℓ hβ m
  unfold wl_theta
  rw [Real.log_div (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) h1).ne' h2.ne',
    Real.log_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne' h1.ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]

/-- `log Φ_x = A_x(1)`. -/
lemma wl8_log_cavPhi (m : ℕ) (x : Euc d) :
    Real.log (wl_cavPhi μ β (m + 2) x) = wl_insPressure μ β (m + 2) (m + 1) x 1 := by
  rw [wl8_cavPhi_eq hK ha hℓ hβ m x, wl7_insPressure_eq_cgf]
  unfold cgf mgf
  congr 2
  funext Y
  simp only [one_mul]

/-- The mean of the pole exponent: `E_{P_n^0}[X_x] = -λ n ∫ K(x,y) dν_n(y)` (exchangeability). -/
lemma wl8_integral_X (m : ℕ) (x : Euc d) :
    ∫ Y, wl7_X β (m + 2) x Y ∂(wl_cavLaw μ β (m + 2) (m + 1)) =
      -(β / ((m + 2 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) *
        ∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal (wl_cavLaw μ β (m + 2) (m + 1))) := by
  have hcoord : ∀ j : Fin (m + 1), ∫ Y, sphericalLogKernel x (Y j) ∂(wl_cavLaw μ β (m + 2) (m + 1)) =
      ∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal (wl_cavLaw μ β (m + 2) (m + 1))) := by
    intro j
    have hKm : Measurable (fun y : Euc d => sphericalLogKernel x y) :=
      Measurable.of_uncurry_left (f := fun x y : Euc d => sphericalLogKernel x y) wl_K_measurable
    have e1 : HRS.Whole.firstMarginal (wl_cavLaw μ β (m + 2) (m + 1)) =
        (wl_cavLaw μ β (m + 2) (m + 1)).map (fun Y => Y 0) :=
      wl6_firstMarginal_def m (wl_cavLaw μ β (m + 2) (m + 1))
    have hmarg := wl_fieldLaw_marginals_eq (wl7_V hK ha hℓ hβ (m + 2))
      (wl_Qfield μ β (m + 2)) (β / ((m + 2 : ℕ) : ℝ)) j 0
    calc ∫ Y, sphericalLogKernel x (Y j) ∂(wl_cavLaw μ β (m + 2) (m + 1))
        = ∫ y, sphericalLogKernel x y ∂((wl_cavLaw μ β (m + 2) (m + 1)).map (fun Y => Y j)) :=
          (integral_map (measurable_pi_apply j).aemeasurable hKm.aestronglyMeasurable).symm
      _ = ∫ y, sphericalLogKernel x y ∂((wl_cavLaw μ β (m + 2) (m + 1)).map (fun Y => Y 0)) := by
          rw [show (wl_cavLaw μ β (m + 2) (m + 1)).map (fun Y => Y j) =
            (wl_cavLaw μ β (m + 2) (m + 1)).map (fun Y => Y 0) from hmarg]
      _ = _ := by rw [e1]
  have hKm : Measurable (fun y : Euc d => sphericalLogKernel x y) :=
    Measurable.of_uncurry_left (f := fun x y : Euc d => sphericalLogKernel x y) wl_K_measurable
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
      Integrable (fun Y : Fin (m + 1) → Euc d => sphericalLogKernel x (Y j))
        (wl_cavLaw μ β (m + 2) (m + 1)) := fun j _ =>
    wl7_integrable_coord (wl7_V hK ha hℓ hβ (m + 2)) (wl_isField_Qfield hK ha hℓ hβ (m + 2))
      (wl7_hlam hβ (m + 2)) (wl7_hrow hK ha hℓ hβ (m + 2)) m hKm (hK.wr1_integrable_row x) j
  generalize wl_cavLaw μ β (m + 2) (m + 1) = P0 at hcoord hint ⊢
  have hfun : (fun Y : Fin (m + 1) → Euc d => wl7_X β (m + 2) x Y) =
      fun Y => -(β / ((m + 2 : ℕ) : ℝ)) * ∑ j : Fin (m + 1), sphericalLogKernel x (Y j) := rfl
  rw [hfun, integral_const_mul, integral_finset_sum _ hint]
  have hsum : ∑ j : Fin (m + 1), ∫ Y, sphericalLogKernel x (Y j) ∂P0 =
      ∑ _j : Fin (m + 1), ∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal P0) :=
    Finset.sum_congr rfl fun j _ => hcoord j
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **Cavity marginal bound**: `ν_n ≤ e^{M₁ + λ m a} e^{M} μ` (one-particle bound `wl6_one_le`; `N = m + 2`,
`n = m + 1` particles). -/
lemma wl8_cav_marg_le (m : ℕ) :
    HRS.Whole.firstMarginal (wl_cavLaw μ β (m + 2) (m + 1)) ≤
      ENNReal.ofReal (Real.exp ((β / ((m + 2 : ℕ) : ℝ)) * ∫ x, logWeight x ∂μ +
        (β / ((m + 2 : ℕ) : ℝ)) * m * a) * Real.exp (β * a)) • μ := by
  have hψ := wl_isField_Qfield hK ha hℓ hβ (m + 2)
  have h1 := wl6_one_le (wl7_V hK ha hℓ hβ (m + 2)) hψ (wl7_hlam hβ (m + 2))
    (wl7_hrow hK ha hℓ hβ (m + 2)) m
  have h2 : μ.withDensity (fun x => ENNReal.ofReal (Real.exp (wl_Qfield μ β (m + 2) x))) ≤
      ENNReal.ofReal (Real.exp (β * a)) • μ := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hψ.le x))
  rw [wl6_firstMarginal_def m, wl7_cavLaw_eq hK ha hℓ hβ (m + 2) (m + 1)]
  refine wl6_le_smul_trans h1 h2 (le_of_eq (ENNReal.ofReal_mul (Real.exp_pos _).le).symm)

/-- `ν_n` is a probability measure. -/
lemma wl8_cav_marg_isProb (m : ℕ) :
    IsProbabilityMeasure (HRS.Whole.firstMarginal (wl_cavLaw μ β (m + 2) (m + 1))) := by
  have := wl7_cav_isProb hK ha hℓ hβ (m + 2) (m + 1)
  rw [wl6_firstMarginal_def m]
  infer_instance

/-- **The logarithm of the marginal density** (exact insertion, TeX before `eq:r2-log-marginal-equation`):
`log θ(x) = β Kμ(x) + (D_N(x) + h_N(x)) - λ n ∫ K(x,y) dν_n(y) - log Z`, given the right derivative of `A_x` at `0`
(`wl_insertion_defect`). -/
lemma wl8_log_theta_eq (m : ℕ) (x : Euc d)
    (hD : HasDerivWithinAt (wl_insPressure μ β (m + 2) (m + 1) x)
      (∫ Y, wl7_X β (m + 2) x Y ∂(wl_cavLaw μ β (m + 2) (m + 1))) (Ici 0) 0) :
    Real.log (wl_theta μ β (m + 2) x) =
      β * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ x +
        (wl_insDefect μ β (m + 2) (m + 1) x + wl_hN β (m + 2) x) -
        (β / ((m + 2 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) *
          ∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal (wl_cavLaw μ β (m + 2) (m + 1))) -
        Real.log (wl_cavZ μ β (m + 2)) := by
  have h1 := wl8_log_theta hK ha hℓ hβ m x
  have h2 := wl8_log_cavPhi hK ha hℓ hβ m x
  have h3 := wl8_integral_X hK ha hℓ hβ m x
  have h4 : wl_insDefect μ β (m + 2) (m + 1) x =
      wl_insPressure μ β (m + 2) (m + 1) x 1 -
        ∫ Y, wl7_X β (m + 2) x Y ∂(wl_cavLaw μ β (m + 2) (m + 1)) := by
    unfold wl_insDefect
    rw [hD.derivWithin (uniqueDiffWithinAt_Ici 0)]
  rw [h1, h2]
  have h5 : wl_insPressure μ β (m + 2) (m + 1) x 1 = wl_insDefect μ β (m + 2) (m + 1) x +
      ∫ Y, wl7_X β (m + 2) x Y ∂(wl_cavLaw μ β (m + 2) (m + 1)) := by rw [h4]; ring
  rw [h5, h3]
  ring

end Euc

/-! ### The marginal equation -/

section Main

variable {d : ℕ}

/-- **Marginal equation** (TeX `eq:r2-log-marginal-equation`).  For `d ≥ 2`, a probability density `ρ` with
`HasSphericalBound A ρ`, `β > 0`, `N ≥ 2`, every `x`, with `μ = ρ dx`, `θ = wl_theta μ β N = dπ_N/dμ`,
`π_N = firstMarginal Q_N`, `ν_n = firstMarginal (wl_cavLaw μ β N (N-1))`, `Z = wl_cavZ μ β N`:
`log θ(x) + β ∫ K(x,y)(θ(y) - 1) dμ(y) = (D_N(x) + h_N(x)) + β (∫ K(x,y) dπ_N(y) - ∫ K(x,y) dν_n(y))
 + (β/N) ∫ K(x,y) dν_n(y) - log Z` (so `c_N = log Z`). -/
theorem wl_marginal_equation (hd : 2 ≤ d) (A : ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hA : HasSphericalBound A ρ) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N) (x : Euc d) :
    Real.log (wl_theta (HRS.Whole.withDensityReal ρ) β N x) +
        β * ∫ y, sphericalLogKernel x y * (wl_theta (HRS.Whole.withDensityReal ρ) β N y - 1)
          ∂(HRS.Whole.withDensityReal ρ) =
      (wl_insDefect (HRS.Whole.withDensityReal ρ) β N (N - 1) x + wl_hN β N x) +
        β * (∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal
              (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ))) -
            ∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal
              (wl_cavLaw (HRS.Whole.withDensityReal ρ) β N (N - 1)))) +
        (β / (N : ℝ)) * ∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal
              (wl_cavLaw (HRS.Whole.withDensityReal ρ) β N (N - 1))) -
        Real.log (wl_cavZ (HRS.Whole.withDensityReal ρ) β N) := by
  obtain ⟨C0, Cl, hC0, h⟩ := wl_Q_eq_fieldLaw hd A
  obtain ⟨hK, hℓ, hℓle, hfield, hQ⟩ := h ρ hρ hA β hβ.le N (by omega)
  have := wl_isProb hρ
  obtain ⟨Cθ, hCθ1, hθ⟩ := wl_density_sup hd β A hβ.le
  obtain ⟨hθm, hπ, -, -, hθsup, -⟩ := hθ ρ hρ hA β hβ.le le_rfl N hN
  obtain ⟨Cd, hCd0, hd'⟩ := wl_insertion_defect hd A β
  obtain ⟨-, -, -, hderiv, -⟩ := hd' ρ hρ hA β hβ le_rfl N hN x
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hlog := wl8_log_theta_eq hK hC0 hℓ hβ.le m x hderiv
  set θ := wl_theta μ β (m + 2) with hθdef
  have hθ0 : ∀ y, 0 ≤ θ y := fun y => (hθsup y).1
  have hθle : ∀ y, θ y ≤ Cθ := fun y => by
    refine (hθsup y).2.trans ?_
    have hr : (1 + ‖y‖ ^ 2) ^ (-(β / (2 * ((m + 2 : ℕ) : ℝ)))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖y‖])
        (neg_nonpos.2 (div_nonneg hβ.le (by positivity)))
    nlinarith
  have hKx : Measurable (fun y : Euc d => sphericalLogKernel x y) :=
    Measurable.of_uncurry_left (f := fun x y : Euc d => sphericalLogKernel x y) wl_K_measurable
  have hKi : Integrable (fun y => sphericalLogKernel x y) μ := hK.wr1_integrable_row x
  have hKθ : Integrable (fun y => sphericalLogKernel x y * θ y) μ := by
    refine Integrable.mono' (hKi.mul_const Cθ) (hKx.mul hθm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (HRS.MS.Comm.comm_log_nonneg x y), abs_of_nonneg (hθ0 y)]
    exact mul_le_mul_of_nonneg_left (hθle y) (HRS.MS.Comm.comm_log_nonneg x y)
  have e1 : ∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal
      (HRS.Whole.modulatedGibbs (rieszKernel d 0) (m + 2) β μ)) = ∫ y, sphericalLogKernel x y * θ y ∂μ := by
    have hfm : Measurable (fun y => ENNReal.ofReal (θ y)) := ENNReal.measurable_ofReal.comp hθm
    rw [hπ, integral_withDensity_eq_integral_toReal_smul hfm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hθ0 y), mul_comm]
  have e2 : ∫ y, sphericalLogKernel x y * (θ y - 1) ∂μ =
      ∫ y, sphericalLogKernel x y * θ y ∂μ - rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ x := by
    unfold rowIntE
    rw [← integral_sub hKθ hKi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  show Real.log (θ x) + β * ∫ y, sphericalLogKernel x y * (θ y - 1) ∂μ =
      (wl_insDefect μ β (m + 2) (m + 1) x + wl_hN β (m + 2) x) +
        β * (∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal
              (HRS.Whole.modulatedGibbs (rieszKernel d 0) (m + 2) β μ)) -
            ∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal (wl_cavLaw μ β (m + 2) (m + 1)))) +
        (β / ((m + 2 : ℕ) : ℝ)) * ∫ y, sphericalLogKernel x y ∂(HRS.Whole.firstMarginal
              (wl_cavLaw μ β (m + 2) (m + 1))) - Real.log (wl_cavZ μ β (m + 2))
  rw [hlog, e1, e2]
  push_cast
  field_simp
  ring

end Main

/-! ### Uniform bounds -/

section Uniform

variable {d : ℕ}

lemma wl8_le_smul_mono {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {c c' : ℝ≥0∞} (h : ν ≤ c • μ)
    (hc : c ≤ c') : ν ≤ c' • μ := by
  refine Measure.le_iff'.2 fun s => ?_
  have := Measure.le_iff'.1 h s
  simp only [Measure.smul_apply, smul_eq_mul] at this ⊢
  exact this.trans (mul_le_mul' hc le_rfl)

/-- **Uniform cavity marginal bound**: `ν_n` is a probability measure with `ν_n ≤ Cν • μ`, `Cν ≥ 1` depending on
`d, A, βp` only (quantified before `ρ, β, N`). -/
theorem wl8_cav_marg_uniform (hd : 2 ≤ d) (A βp : ℝ) (hβp : 0 ≤ βp) : ∃ Cν : ℝ, 1 ≤ Cν ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
      IsProbabilityMeasure (HRS.Whole.firstMarginal (wl_cavLaw (HRS.Whole.withDensityReal ρ) β N (N - 1))) ∧
      HRS.Whole.firstMarginal (wl_cavLaw (HRS.Whole.withDensityReal ρ) β N (N - 1)) ≤
        ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ := by
  obtain ⟨C0, Cl, hC0, h⟩ := wl_Q_eq_fieldLaw hd A
  set Cl' : ℝ := max Cl 0 with hCl'
  have hCl'0 : 0 ≤ Cl' := le_max_right _ _
  have hE0 : 0 ≤ βp * Cl' + βp * C0 + βp * C0 := by positivity
  refine ⟨Real.exp (βp * Cl' + βp * C0 + βp * C0), Real.one_le_exp hE0, fun ρ hρ hA β hβ hββp N hN => ?_⟩
  obtain ⟨hK, hℓ, hℓle, hfield, hQ⟩ := h ρ hρ hA β hβ.le N (by omega)
  have := wl_isProb hρ
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  refine ⟨wl8_cav_marg_isProb hK hC0 hℓ hβ.le m, ?_⟩
  refine wl8_le_smul_mono (wl8_cav_marg_le hK hC0 hℓ hβ.le m) (ENNReal.ofReal_le_ofReal ?_)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hN1 : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hlam : β / ((m + 2 : ℕ) : ℝ) ≤ β := div_le_self hβ.le hN1
  have hlam0 : 0 ≤ β / ((m + 2 : ℕ) : ℝ) := div_nonneg hβ.le (by linarith)
  have hl0 : 0 ≤ ∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ) :=
    integral_nonneg fun x => wl2_logWeight_nonneg x
  have hl1 : ∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ) ≤ Cl' := hℓle.trans (le_max_left _ _)
  have h1 : β / ((m + 2 : ℕ) : ℝ) * ∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ) ≤ βp * Cl' :=
    calc _ ≤ β * ∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ) := mul_le_mul_of_nonneg_right hlam hl0
      _ ≤ β * Cl' := mul_le_mul_of_nonneg_left hl1 hβ.le
      _ ≤ βp * Cl' := mul_le_mul_of_nonneg_right hββp hCl'0
  have h2 : β / ((m + 2 : ℕ) : ℝ) * m * C0 ≤ βp * C0 := by
    have : β / ((m + 2 : ℕ) : ℝ) * m ≤ β := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      push_cast
      nlinarith
    calc _ ≤ β * C0 := mul_le_mul_of_nonneg_right this hC0
      _ ≤ βp * C0 := mul_le_mul_of_nonneg_right hββp hC0
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h3 : β * C0 ≤ βp * C0 := mul_le_mul_of_nonneg_right hββp hC0
  linarith

/-- **`L²` norm of the one-body field**: `‖h_N‖_{L²(μ)} ≤ (β/N) C` (`μ(ℓ²) ≤ C²`, `wl_logmoment 2`). -/
theorem wl8_hN_L2 (hd : 2 ≤ d) (A : ℝ) : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 ≤ β → ∀ N : ℕ,
      eLpNorm (fun x => wl_hN β N x) 2 (HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (β / (N : ℝ) * Cq) := by
  obtain ⟨Cl2, hCl2⟩ := wl_logmoment hd A 2
  refine ⟨Real.sqrt (max Cl2 0), Real.sqrt_nonneg _, fun ρ hρ hA β hβ N => ?_⟩
  obtain ⟨hint, hle⟩ := hCl2 ρ hρ hA
  have := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set lam : ℝ := β / (N : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hβ (Nat.cast_nonneg N)
  have hs0 : 0 ≤ lam * Real.sqrt (max Cl2 0) := mul_nonneg hlam0 (Real.sqrt_nonneg _)
  have hfm : Measurable (fun x : Euc d => wl_hN β N x) := by
    unfold wl_hN
    exact (wl2_logWeight_measurable (d := d)).const_mul _
  refine wl8_eLpNorm_two_le hfm.aestronglyMeasurable ?_
  have hpt : ∀ x : Euc d, ‖wl_hN β N x‖ₑ ^ 2 = ENNReal.ofReal (lam ^ 2 * logWeight x ^ 2) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    unfold wl_hN
    congr 1
    rw [← hlam]
    ring
  have hi : Integrable (fun x : Euc d => lam ^ 2 * logWeight x ^ 2) μ := hint.const_mul _
  calc ∫⁻ x, ‖wl_hN β N x‖ₑ ^ 2 ∂μ = ∫⁻ x, ENNReal.ofReal (lam ^ 2 * logWeight x ^ 2) ∂μ :=
        lintegral_congr hpt
    _ = ENNReal.ofReal (∫ x, lam ^ 2 * logWeight x ^ 2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hi
          (Filter.Eventually.of_forall fun x => by positivity)).symm
    _ ≤ ENNReal.ofReal ((lam * Real.sqrt (max Cl2 0)) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, mul_pow, Real.sq_sqrt (le_max_right _ _)]
        exact mul_le_mul_of_nonneg_left (hle.trans (le_max_left _ _)) (sq_nonneg _)
    _ = ENNReal.ofReal (lam * Real.sqrt (max Cl2 0)) ^ 2 := ENNReal.ofReal_pow hs0 2

end Uniform

/-! ### Absorption: `‖z_N‖_{L²(μ)} ≤ C/N` -/

section Absorb

variable {d : ℕ}

/-- **`wl_marginal_L2`** (TeX `eq:r2-log-main-linear`, the marginal `L²` estimate, via the marginal equation and
absorption).  For `d ≥ 2`, `A`, `βp ≥ 0` there is `C ≥ 1` (before `ρ, β, N`) such that for every probability
density `ρ` with `HasSphericalBound A ρ`, `β ∈ (0, βp]`, `N ≥ 2`, with `μ = ρ dx`, `θ = wl_theta μ β N` and
`Q_N = modulatedGibbs (rieszKernel d 0) N β μ`: `θ` is measurable, `firstMarginal Q_N = μ.withDensity θ`,
`0 ≤ θ(x) ≤ C (1+|x|²)^{-β/(2N)}` for every `x`, `θ - 1 ∈ L²(μ)` and `‖θ - 1‖_{L²(μ)} ≤ C/N`. -/
theorem wl_marginal_L2 (hd : 2 ≤ d) (A βp : ℝ) (hβp : 0 ≤ βp) : ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
      Measurable (wl_theta (HRS.Whole.withDensityReal ρ) β N) ∧
      HRS.Whole.firstMarginal
          (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)) =
        (HRS.Whole.withDensityReal ρ).withDensity
          (fun x => ENNReal.ofReal (wl_theta (HRS.Whole.withDensityReal ρ) β N x)) ∧
      (∀ x, 0 ≤ wl_theta (HRS.Whole.withDensityReal ρ) β N x ∧
        wl_theta (HRS.Whole.withDensityReal ρ) β N x ≤ C * (1 + ‖x‖ ^ 2) ^ (-(β / (2 * (N : ℝ))))) ∧
      MemLp (fun x => wl_theta (HRS.Whole.withDensityReal ρ) β N x - 1) 2 (HRS.Whole.withDensityReal ρ) ∧
      eLpNorm (fun x => wl_theta (HRS.Whole.withDensityReal ρ) β N x - 1) 2 (HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (C / (N : ℝ)) := by
  obtain ⟨C0, Cl, hC0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  obtain ⟨Cθ, hCθ1, hθ⟩ := wl_density_sup hd βp A hβp
  obtain ⟨Cd, hCd0, hd'⟩ := wl_insertion_defect hd A βp
  obtain ⟨Ctv, hCtv0, htv⟩ := wl_cavity_tv hd A βp
  obtain ⟨Ccv, hCcv0, hcv⟩ := wl8_cv_L2 hd A
  obtain ⟨C1, hC10, hC1⟩ := wl8_K_row_integrable hd A
  obtain ⟨Cq, hCq0, hq⟩ := wl8_hN_L2 hd A
  obtain ⟨Cν, hCν1, hν⟩ := wl8_cav_marg_uniform hd A βp hβp
  obtain ⟨Cc, hCc0, hconv⟩ := wl8_conv_L2 hd A
  have hCν0 : 0 ≤ Cν := by linarith
  set a1 : ℝ := Cd + βp * Cq with ha1
  set a2 : ℝ := 2 * Ccv * Ctv with ha2
  set a3 : ℝ := βp * (Cν * C1) with ha3
  set Cf : ℝ := Cθ * (a1 + βp * a2 + a3) with hCf
  have hCθ0 : 0 ≤ Cθ := by linarith
  have ha10 : 0 ≤ a1 := by positivity
  have ha20 : 0 ≤ a2 := by positivity
  have ha30 : 0 ≤ a3 := by positivity
  refine ⟨max Cθ Cf, le_trans hCθ1 (le_max_left _ _), fun ρ hρ hA β hβ hββp N hN => ?_⟩
  have hμp := wl_isProb hρ
  obtain ⟨hK, hℓ, hℓle, hfield, hQ'⟩ := hQ ρ hρ hA β hβ.le N (by omega)
  obtain ⟨hθm, hπ, hΦ, hZ, hθsup, hπle⟩ := hθ ρ hρ hA β hβ.le hββp N hN
  obtain ⟨hνprob, hνle⟩ := hν ρ hρ hA β hβ hββp N hN
  have hDefect := hd' ρ hρ hA β hβ hββp N hN
  have hTV := htv ρ hρ hA β hβ hββp N hN
  have hhN := hq ρ hρ hA β hβ.le N
  have heqN := fun x => wl_marginal_equation hd A hρ hA hβ hN x
  -- the probability measures `Q_N` and `π_N`
  have hQprob : IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)) := by
    rw [hQ' (wl7_V hK hC0 hℓ hβ.le N) rfl]
    exact (fieldSpec (V := wl7_V hK hC0 hℓ hβ.le N) (wl_isField_Qfield hK hC0 hℓ hβ.le N)
      (wl7_hlam hβ.le N) N).isProb
  have hπprob : IsProbabilityMeasure (HRS.Whole.firstMarginal
      (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ))) := by
    unfold HRS.Whole.firstMarginal
    rw [dif_pos (by omega : 0 < N)]
    infer_instance
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set θ : Euc d → ℝ := wl_theta μ β (m + 2) with hθdef
  set π : Measure (Euc d) := HRS.Whole.firstMarginal
    (HRS.Whole.modulatedGibbs (rieszKernel d 0) (m + 2) β μ) with hπdef
  set ν : Measure (Euc d) := HRS.Whole.firstMarginal (wl_cavLaw μ β (m + 2) (m + 2 - 1)) with hνdef
  have hNpos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  set Nr : ℝ := ((m + 2 : ℕ) : ℝ) with hNr
  -- pointwise facts on `θ`
  have hθ0 : ∀ y, 0 ≤ θ y := fun y => (hθsup y).1
  have hrpow : ∀ y : Euc d, (1 + ‖y‖ ^ 2) ^ (-(β / (2 * Nr))) ≤ 1 := fun y =>
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖y‖])
      (neg_nonpos.2 (div_nonneg hβ.le (by positivity)))
  have hθle : ∀ y, θ y ≤ Cθ := fun y => by
    refine (hθsup y).2.trans ?_
    nlinarith [hrpow y, Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖y‖ ^ 2) (-(β / (2 * Nr)))]
  have hθpos : ∀ y, 0 < θ y := fun y => by
    simp only [hθdef, wl_theta]
    exact div_pos (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (wl8_cavPhi_pos hK hC0 hℓ hβ.le m y))
      (wl8_cavZ_pos hK hC0 hℓ hβ.le m)
  have hwm : Measurable (fun y => θ y - 1) := hθm.sub_const 1
  have hwb : ∀ y, |θ y - 1| ≤ Cθ + 1 := fun y => by
    rw [abs_le]; constructor <;> linarith [hθ0 y, hθle y]
  have hwi : Integrable (fun y => θ y - 1) μ :=
    Integrable.of_bound hwm.aestronglyMeasurable (Cθ + 1)
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hwb y)
  have hθi : Integrable θ μ :=
    Integrable.of_bound hθm.aestronglyMeasurable Cθ
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hθ0 y)]; exact hθle y)
  have hθ1 : ∫ y, θ y ∂μ = 1 := by
    have h1 : π Set.univ = 1 := measure_univ
    rw [hπ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hθ0) hθm.aestronglyMeasurable, h1]
    simp
  have hz0 : ∫ y, (θ y - 1) ∂μ = 0 := by
    rw [integral_sub hθi (integrable_const _), hθ1]
    simp
  -- the convolution `K z`
  set Kz : Euc d → ℝ := fun x => ∫ y, sphericalLogKernel x y * (θ y - 1) ∂μ with hKz
  obtain ⟨hKzm, hKzn⟩ := hconv ρ hρ hA (fun y => θ y - 1) hwm hwi
  have hKz2 : MemLp Kz 2 μ := lt_of_le_of_lt hKzn ENNReal.ofReal_lt_top
  have hnn : 0 ≤ ∫ x, Kz x * (θ x - 1) ∂μ :=
    wl8_K_psd hd A hρ hA hwm hwb hz0
  -- the difference of the two potentials
  have hπle' : π ≤ ENNReal.ofReal (max Cθ Cν) • μ :=
    wl8_le_smul_mono hπle (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hνle' : ν ≤ ENNReal.ofReal (max Cθ Cν) • μ :=
    wl8_le_smul_mono hνle (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  obtain ⟨hcvm, hcvn⟩ := hcv ρ hρ hA (max Cθ Cν) (le_trans hCθ0 (le_max_left _ _)) π ν hπprob hνprob hπle' hνle'
    (Ctv / Nr) hTV
  set cv : Euc d → ℝ := fun x => ∫ y, sphericalLogKernel x y ∂π - ∫ y, sphericalLogKernel x y ∂ν with hcvdef
  set Qν : Euc d → ℝ := fun x => ∫ y, sphericalLogKernel x y ∂ν with hQν
  have hQνm : Measurable Qν := RefMarg.measurable_integral_kernel
    (F := fun p : Euc d × Euc d => sphericalLogKernel p.1 p.2) wl_K_measurable
  have hQνb : ∀ x, |(β / Nr) * Qν x| ≤ (β / Nr) * (Cν * C1) := fun x => by
    have hKi := (hC1 ρ hρ hA x).1
    have h0 : 0 ≤ Qν x := integral_nonneg fun y => HRS.MS.Comm.comm_log_nonneg x y
    have h1 : Qν x ≤ Cν * C1 := by
      refine (wr13e_integral_le_of_le_smul hνle hCν0 (fun y => HRS.MS.Comm.comm_log_nonneg x y) hKi).trans ?_
      exact mul_le_mul_of_nonneg_left (hC1 ρ hρ hA x).2 hCν0
    rw [abs_of_nonneg (mul_nonneg (div_nonneg hβ.le hNpos.le) h0)]
    exact mul_le_mul_of_nonneg_left h1 (div_nonneg hβ.le hNpos.le)
  have hQn : eLpNorm (fun x => (β / Nr) * Qν x) 2 μ ≤ ENNReal.ofReal ((β / Nr) * (Cν * C1)) :=
    RefMarg.eLpNorm_two_le_const (hQνm.const_mul _).aestronglyMeasurable hQνb
  -- the remainder `D_N + h_N`
  set Dfun : Euc d → ℝ := fun x => wl_insDefect μ β (m + 2) (m + 2 - 1) x + wl_hN β (m + 2) x with hDfun
  have heq : ∀ x, Real.log (θ x) + β * Kz x = Dfun x + β * cv x + (β / Nr) * Qν x + (-Real.log (wl_cavZ μ β (m + 2))) := by
    intro x
    have := heqN x
    simp only [hDfun, hcvdef, hQν, hKz, hNr]
    linarith
  have hDfun_eq : Dfun = fun x => Real.log (θ x) + β * Kz x - β * cv x - (β / Nr) * Qν x +
      Real.log (wl_cavZ μ β (m + 2)) := by
    funext x
    have := heq x
    linarith
  have hDm : Measurable Dfun := by
    rw [hDfun_eq]
    exact ((((Real.measurable_log.comp hθm).add (hKzm.const_mul β)).sub (hcvm.const_mul β)).sub
      (hQνm.const_mul _)).add measurable_const
  have hhNm : Measurable (fun x : Euc d => wl_hN β (m + 2) x) := by
    unfold wl_hN
    exact (wl2_logWeight_measurable (d := d)).const_mul _
  have hDm' : Measurable (fun x : Euc d => wl_insDefect μ β (m + 2) (m + 2 - 1) x) := by
    have : (fun x : Euc d => wl_insDefect μ β (m + 2) (m + 2 - 1) x) =
        fun x => Dfun x - wl_hN β (m + 2) x := by
      funext x; simp only [hDfun]; ring
    rw [this]
    exact hDm.sub hhNm
  have hDb : ∀ x, |wl_insDefect μ β (m + 2) (m + 2 - 1) x| ≤ Cd / Nr := fun x => by
    obtain ⟨-, -, -, -, hD0, hD1, -⟩ := hDefect x
    rw [abs_of_nonneg hD0]
    exact hD1
  have hDn : eLpNorm (fun x => wl_insDefect μ β (m + 2) (m + 2 - 1) x) 2 μ ≤ ENNReal.ofReal (Cd / Nr) :=
    RefMarg.eLpNorm_two_le_const hDm'.aestronglyMeasurable hDb
  have hD : eLpNorm Dfun 2 μ ≤ ENNReal.ofReal ((Cd + βp * Cq) / Nr) := by
    have h1 : Dfun = (fun x => wl_insDefect μ β (m + 2) (m + 2 - 1) x) + fun x => wl_hN β (m + 2) x := rfl
    rw [h1]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine (add_le_add hDn hhN).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (Cd + βp * Cq) / Nr = Cd / Nr + βp / Nr * Cq := by field_simp
    rw [this]
    have : β / Nr * Cq ≤ βp / Nr * Cq :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hββp hNpos.le) hCq0
    linarith
  have he1 : 0 ≤ (Cd + βp * Cq) / Nr := by positivity
  have he2 : 0 ≤ Ccv * (2 * (Ctv / Nr)) := by positivity
  have he3 : 0 ≤ (β / Nr) * (Cν * C1) := by positivity
  have hfin := wr13e_L2_assemble (μ := μ) (β := β) (lam := β / Nr) (Cν := Cθ)
    (e1 := (Cd + βp * Cq) / Nr) (e2 := Ccv * (2 * (Ctv / Nr))) (e3 := (β / Nr) * (Cν * C1))
    hβ.le hCθ1 hθm hθpos (Filter.Eventually.of_forall hθle) hθ1 hDm hcvm hQνm hD hcvn hQn he1 he2 he3
    hKz2 hnn heq
  have hkey : Cθ * ((Cd + βp * Cq) / Nr + β * (Ccv * (2 * (Ctv / Nr))) + (β / Nr) * (Cν * C1)) ≤
      max Cθ Cf / Nr := by
    have e : Cθ * ((Cd + βp * Cq) / Nr + β * (Ccv * (2 * (Ctv / Nr))) + (β / Nr) * (Cν * C1)) =
        Cθ * (a1 + β * a2 + β * (Cν * C1)) / Nr := by
      simp only [ha1, ha2]
      field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hNpos.le
    refine le_trans ?_ (le_max_right _ _)
    rw [hCf]
    refine mul_le_mul_of_nonneg_left ?_ hCθ0
    have h2 : β * a2 ≤ βp * a2 := mul_le_mul_of_nonneg_right hββp ha20
    have h3 : β * (Cν * C1) ≤ a3 := by
      rw [ha3]; exact mul_le_mul_of_nonneg_right hββp (by positivity)
    linarith
  have hnorm : eLpNorm (fun x => θ x - 1) 2 μ ≤ ENNReal.ofReal (max Cθ Cf / Nr) :=
    hfin.trans (ENNReal.ofReal_le_ofReal hkey)
  refine ⟨hθm, hπ, fun x => ⟨(hθsup x).1, ?_⟩, lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top, hnorm⟩
  exact (hθsup x).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (by positivity) _))

end Absorb

/-! ### Conjunct 3 of `r2_log_static` -/

section Final

variable {d : ℕ}

/-- **`wl_hasLogMarginalDensityBounds`** (conjunct 3 of `r2_log_static`, `W:eq:r2-log-main-linear`).  For `d ≥ 2`,
`0 < βm ≤ βp`, `A` there is `C` (quantified before `ρ, β, N`) such that for every probability density `ρ` with
`HasSphericalBound A ρ`, every `β ∈ [βm, βp]` and every `N ≥ 2`, the first marginal of
`modulatedGibbs (rieszKernel d 0) N β (withDensityReal ρ)` satisfies the frozen predicate
`HasLogMarginalDensityBounds` of `HRS/Whole/Static.lean` (the density version is `θ = wl_theta`, bounded by
`C (1+|x|²)^{-β/(2N)}` for every `x`, with `‖θ - 1‖_{L²(μ)} ≤ C/N`). -/
theorem wl_hasLogMarginalDensityBounds (hd : 2 ≤ d) (βm βp A : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β ∈ Set.Icc βm βp, ∀ N : ℕ, 2 ≤ N →
        HasLogMarginalDensityBounds
          (HRS.Whole.firstMarginal
            (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)))
          (HRS.Whole.withDensityReal ρ) C β N := by
  have hβp : 0 ≤ βp := by linarith
  obtain ⟨C, hC1, h⟩ := wl_marginal_L2 hd A βp hβp
  refine ⟨C, fun ρ hρ hA β hββ N hN => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hββ.1
  obtain ⟨hθm, hπ, hsup, hmem, hnorm⟩ := h ρ hρ hA β hβ0 hββ.2 N hN
  refine ⟨wl_theta (HRS.Whole.withDensityReal ρ) β N, hθm, hπ, hsup, hmem, ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  unfold l2Norm
  have e : ∫ x, (wl_theta (HRS.Whole.withDensityReal ρ) β N x - 1) ^ 2 ∂(HRS.Whole.withDensityReal ρ) =
      (eLpNorm (fun x => wl_theta (HRS.Whole.withDensityReal ρ) β N x - 1) 2
        (HRS.Whole.withDensityReal ρ)).toReal ^ 2 := by
    rw [← RefMarg.integral_mul_self_eq hmem]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [e, Real.sqrt_sq ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (by linarith) hNpos.le) hnorm

end Final

end HRS.MS.Wl
