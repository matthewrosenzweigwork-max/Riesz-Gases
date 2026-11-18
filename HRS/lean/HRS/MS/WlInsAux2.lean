import HRS.MS.WlInsAux1

/-!
# HRS.MS.WlInsAux2 -- insertion defect and cavity total variation (WL-7, part 2)

Packet WL-7 of `docs/WR_LOG_PLAN.md` (Step 9 of the proof of `r2_log_static`).  Infrastructure lemmas, not manuscript
rows.  Namespace `HRS.MS.Wl`, helper prefix `wl7_`.  Builds on `WlInsAux1`, `WlCavAux2` (`wl_cavLaw`, `wl_poleLaw`,
`wl_cavity_disintegration`), `WlLin` (`wl_pole_linear`) and the generic fragments of `WrInsAux1-2`
(`wr13c2_hasDerivWithinAt`, `wr13c2_var_fracIn_le`, `wr13c2_sqrt_chain`, ...).

Main statements (constants `C` depend on `d, A, βp` only and are quantified before `ρ, β, N, x`; uniform over all
probability densities `ρ` with `HasSphericalBound A ρ`, `β ∈ (0, βp]`, all `N ≥ 2` (for `N ≥ N0` by the calibrated
transfer of `WlLin`, for the finitely many smaller `N` by its crude bound), all `x`):

* `wl_insertion_defect`: with `A_x(t) = wl_insPressure = log P_n^0 [e^{-tλ ∑ K(x,y_i)}]`, `A_x'' = Var_{P^{x,t}}(X_x) =
  λ² Var(∑ K(x,y_i)) ∈ [0, C/N]` on `(0,1]` (the underlying `evariance` is `≤ C N`), `A_x` has the right derivative
  `E_{P_n^0} X_x` at `0` and `0 ≤ D_N(x) = A_x(1) - A_x'(0) = wl_insDefect ≤ C/N`; also `A_x(1) - 2 A_x(1/2) ≤ C/N`;
* `wl_cavity_tv`: `‖π_N - ν_n‖_TV ≤ C/N` with `π_N = firstMarginal (modulatedGibbs (rieszKernel d 0) N β μ)` and
  `ν_n = firstMarginal (wl_cavLaw μ β N (N - 1))` (exponential-family TV `EF.ef_tv`, pole variance of the fraction of
  particles in a set, second difference of `wl_insertion_defect`, exact disintegration `wl_cavity_disintegration`).

Adjustments with respect to the plan (documented, harmless): `β > 0` (as in `wl_pole_linear`); no truncation of `K` is
needed (the row moments `wl_row_pow` are used directly; the pole-linear variance is already available for the full
kernel `K`); the variance bound is uniform in `t ∈ (0,1]`, so the `t`-integral of the variance in `EF.ef_main` is trivial
(no radial integrals); `A_x'(0)` is the right derivative (`wr13c2_hasDerivWithinAt`), `wl_insDefect` uses `derivWithin`
but `wl_insertion_defect` also states the `HasDerivWithinAt`, so no junk value occurs.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.External HRS.MS.Wr

variable {d : ℕ}

/-! ### Definitions -/

/-- The insertion pressure `A_x(t) = log P_n^0 [ e^{-t λ ∑_i K(x, y_i)} ]`, `λ = β/N`, `P_n^0 = wl_cavLaw`. -/
def wl_insPressure (μ : Measure (Euc d)) (β : ℝ) (N n : ℕ) (x : Euc d) (t : ℝ) : ℝ :=
  Real.log (∫ Y, Real.exp (-(t * (β / N)) * ∑ i, sphericalLogKernel x (Y i)) ∂(wl_cavLaw μ β N n))

/-- The insertion defect `D_N(x) = A_x(1) - A_x'(0)` (right derivative at `0`). -/
def wl_insDefect (μ : Measure (Euc d)) (β : ℝ) (N n : ℕ) (x : Euc d) : ℝ :=
  wl_insPressure μ β N n x 1 - derivWithin (wl_insPressure μ β N n x) (Ici 0) 0

lemma wl7_insPressure_eq_cgf (μ : Measure (Euc d)) (β : ℝ) (N n : ℕ) (x : Euc d) :
    wl_insPressure μ β N n x = cgf (wl7_X β N x (n := n)) (wl_cavLaw μ β N n) := by
  funext t
  unfold wl_insPressure cgf mgf
  congr 2
  funext Y
  congr 1
  unfold wl7_X
  ring

/-- `∫ K(x,y)² dμ ≤ C₂` as an `ENNReal` bound on `‖K‖ₑ²`. -/
lemma wl7_lintegral_sq_K {μ : Measure (Euc d)} {C2 : ℝ} (x : Euc d)
    (hi : Integrable (fun y => sphericalLogKernel x y ^ 2) μ)
    (hle : ∫ y, sphericalLogKernel x y ^ 2 ∂μ ≤ C2) :
    ∫⁻ y, ‖sphericalLogKernel x y‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal C2 := by
  have e : ∀ y, ‖sphericalLogKernel x y‖ₑ ^ 2 = ENNReal.ofReal (sphericalLogKernel x y ^ 2) := fun y => by
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun y => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

/-- Variance of the pole exponent: `Var[X_x; P] = λ² Var[∑ K(x,y_i); P]`. -/
lemma wl7_variance_X (β : ℝ) (N : ℕ) (x : Euc d) {n : ℕ} (P : Measure (Fin n → Euc d)) :
    Var[wl7_X β N x (n := n); P] =
      (β / N) ^ 2 * (evariance (fun Y : Fin n → Euc d => ∑ i, sphericalLogKernel x (Y i)) P).toReal := by
  have := variance_const_mul (-(β / N)) (fun Y : Fin n → Euc d => ∑ i, sphericalLogKernel x (Y i)) P
  rw [neg_sq] at this
  exact this

/-- **Uniform variance of the pole exponent**: `Var_{P^{x,t}}(X_x) = λ² Var(∑ K(x,y_i)) ≤ C/N` and
`evariance (∑ K(x,y_i)) ≤ C N`, for `t ∈ [0,1]`. -/
theorem wl7_var_X (hd : 2 ≤ d) (A βp : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
      ∀ x : Euc d, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        evariance (fun Y : Fin (N - 1) → Euc d => ∑ i, sphericalLogKernel x (Y i))
            (wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x) ≤ ENNReal.ofReal (C * N) ∧
        0 ≤ Var[wl7_X β N x (n := N - 1); wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x] ∧
        Var[wl7_X β N x (n := N - 1); wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x] ≤
          βp ^ 2 * C / N := by
  obtain ⟨C1, hC10, h1⟩ := wl7_pole_evariance hd A βp
  obtain ⟨C2, hC20, h2⟩ := wl_row_pow hd A 2
  refine ⟨C1 * C2, mul_nonneg hC10 hC20, fun ρ hρ hA β hβ hββp N hN x t ht0 ht1 => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : (((N - 1 : ℕ) : ℝ)) ≤ N := by exact_mod_cast (by omega : N - 1 ≤ N)
  have hKm : Measurable (fun y => sphericalLogKernel x y) := by
    have h : Measurable ((fun p : Euc d × Euc d => sphericalLogKernel p.1 p.2) ∘ (fun y : Euc d => (x, y))) :=
      wl_K_measurable.comp (measurable_const.prodMk measurable_id)
    exact h
  have hev : evariance (fun Y : Fin (N - 1) → Euc d => ∑ i, sphericalLogKernel x (Y i))
      (wl_poleLaw μ β N (N - 1) t x) ≤ ENNReal.ofReal (C1 * C2 * N) := by
    refine (h1 ρ hρ hA β hβ hββp N hN x t ht0 ht1 (fun y => sphericalLogKernel x y) hKm).trans ?_
    refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl
      (wl7_lintegral_sq_K x (h2 ρ hρ hA x).1 (h2 ρ hρ hA x).2))).trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul hC10]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right hn hC20
    nlinarith
  refine ⟨hev, variance_nonneg _ _, ?_⟩
  rw [wl7_variance_X]
  have hts : (evariance (fun Y : Fin (N - 1) → Euc d => ∑ i, sphericalLogKernel x (Y i))
      (wl_poleLaw μ β N (N - 1) t x)).toReal ≤ C1 * C2 * N :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hev).trans
      (by rw [ENNReal.toReal_ofReal (by positivity)])
  have hb2 : (β / N) ^ 2 ≤ (βp / N) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hβ.le hNpos.le) (div_le_div_of_nonneg_right hββp hNpos.le) 2
  calc (β / N) ^ 2 * _ ≤ (βp / N) ^ 2 * (C1 * C2 * N) :=
        mul_le_mul hb2 hts ENNReal.toReal_nonneg (by positivity)
    _ = βp ^ 2 * (C1 * C2) / N := by field_simp

/-! ### The exponential-family derivatives of the insertion pressure -/

section Deriv

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ}
  (hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y)) (ha : 0 ≤ a)
  (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {β : ℝ} (hβ : 0 ≤ β) (N : ℕ)

include hK ha hℓ hβ

/-- First and second derivative of `A_x` on `(0, ∞)`: `A_x'(t) = E_{P^{x,t}} X_x` and `A_x''(t) = Var_{P^{x,t}} X_x`
(`= λ² Var(∑ K(x,y_i))`), for `n` free particles, `n ≥ 1`. -/
lemma wl7_hasDerivAt {n : ℕ} (hn : 0 < n) (x : Euc d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (wl_insPressure μ β N n x) (∫ Y, wl7_X β N x Y ∂(wl_poleLaw μ β N n t x)) t ∧
    HasDerivAt (fun u => ∫ Y, wl7_X β N x Y ∂(wl_poleLaw μ β N n u x))
      (Var[wl7_X β N x (n := n); wl_poleLaw μ β N n t x]) t := by
  haveI := wl7_cav_isProb hK ha hℓ hβ N n
  have hXm := wl7_X_measurable β N x n
  have hb := wl7_X_le_zero hβ N x (n := n)
  refine ⟨?_, ?_⟩
  · have h := HRS.MarginalAux.EF.hasDerivAt_cgf (P := wl_cavLaw μ β N n) hXm hb ht
    rw [← wl7_poleLaw_eq_tilted hK ha hℓ hβ N ht.le x n, ← wl7_insPressure_eq_cgf] at h
    exact h
  · have h := HRS.MarginalAux.EF.hasDerivAt_mean (P := wl_cavLaw μ β N n) hXm hb ht
    rw [← wl7_poleLaw_eq_tilted hK ha hℓ hβ N ht.le x n] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with u hu
    rw [wl7_poleLaw_eq_tilted hK ha hℓ hβ N (le_of_lt hu) x n]

/-- **Defect from a variance bound**: if `Var_{P^{x,t}} X_x ≤ W` for `t ∈ (0,1]`, then the insertion pressure has the
right derivative `E_{P_n^0} X_x` at `0`, `0 ≤ D_N(x) ≤ W` and `A_x(1) - 2 A_x(1/2) ≤ W/2`. -/
lemma wl7_defect_of_var {n : ℕ} (hn : 0 < n) (x : Euc d) {W : ℝ} (hW : 0 ≤ W)
    (hvar : ∀ t ∈ Ioc (0 : ℝ) 1, Var[wl7_X β N x (n := n); wl_poleLaw μ β N n t x] ≤ W) :
    HasDerivWithinAt (wl_insPressure μ β N n x) (∫ Y, wl7_X β N x Y ∂(wl_cavLaw μ β N n)) (Ici 0) 0 ∧
    0 ≤ wl_insDefect μ β N n x ∧ wl_insDefect μ β N n x ≤ W ∧
    wl_insPressure μ β N n x 1 - 2 * wl_insPressure μ β N n x (1 / 2) ≤ W / 2 := by
  haveI := wl7_cav_isProb hK ha hℓ hβ N n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hXm := wl7_X_measurable β N x (m + 1)
  have hb := wl7_X_le_zero hβ N x (n := m + 1)
  have hXi := wl7_integrable_X hK ha hℓ hβ N m x
  have hder : HasDerivWithinAt (wl_insPressure μ β N (m + 1) x)
      (∫ Y, wl7_X β N x Y ∂(wl_cavLaw μ β N (m + 1))) (Ici 0) 0 := by
    rw [wl7_insPressure_eq_cgf]
    exact wr13c2_hasDerivWithinAt hXm hb hXi
  have hw : ∀ t ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (Var[wl7_X β N x (n := m + 1);
      (wl_cavLaw μ β N (m + 1)).tilted (fun Y => t * wl7_X β N x Y)]) ≤ (fun _ : ℝ => ENNReal.ofReal W) t := by
    intro t ht
    rw [← wl7_poleLaw_eq_tilted hK ha hℓ hβ N ht.1.le x (m + 1)]
    exact ENNReal.ofReal_le_ofReal (hvar t ht)
  have hWfin : ∫⁻ _t in Ioc (0 : ℝ) 1, ENNReal.ofReal W ≠ ∞ := by
    simp
  obtain ⟨h1, h2⟩ := HRS.MarginalAux.EF.ef_main hXm hb hXi (fun _ => ENNReal.ofReal W) hw hWfin
  have hint : (∫⁻ _t in Ioc (0 : ℝ) 1, ENNReal.ofReal W).toReal = W := by
    simp [hW]
  rw [hint] at h1 h2
  have hge := HRS.MarginalAux.EF.ef_cgf_ge hXm hb hXi
  have hdef : wl_insDefect μ β N (m + 1) x = wl_insPressure μ β N (m + 1) x 1 -
      ∫ Y, wl7_X β N x Y ∂(wl_cavLaw μ β N (m + 1)) := by
    unfold wl_insDefect
    rw [hder.derivWithin (uniqueDiffWithinAt_Ici 0)]
  have e1 := congrFun (wl7_insPressure_eq_cgf μ β N (m + 1) x) 1
  have e2 := congrFun (wl7_insPressure_eq_cgf μ β N (m + 1) x) (1 / 2)
  refine ⟨hder, ?_, ?_, ?_⟩
  · rw [hdef, e1]; linarith
  · rw [hdef, e1]; linarith
  · rw [e1, e2]; linarith

end Deriv

/-! ### Main statement: the insertion defect -/

/-- **Insertion defect** (Step 9 of `r2_log_static`, TeX `eq:r2-log-insertion`).  For `d ≥ 2`, `A`, `βp` there is one
constant `C ≥ 0` (quantified before `ρ, β, N, x`; it depends on `d, A, βp` only) such that for every probability
density `ρ` with `HasSphericalBound A ρ`, every `β ∈ (0, βp]`, every `N ≥ 2` (all `N`: `N ≥ N0` through the calibrated
transfer of `WlLin`, the finitely many smaller `N` through the crude bound) and every `x`, with `μ = ρ dx`,
`n = N - 1`, `P_n^0 = wl_cavLaw μ β N n` (a probability measure), `P^{x,t} = wl_poleLaw μ β N n t x`,
`X_x = wl7_X β N x = -(β/N) ∑ K(x, ·)` and `A_x = wl_insPressure μ β N n x`:

* `A_x` is differentiable on `(0, ∞)` with `A_x'(t) = E_{P^{x,t}} X_x` and `A_x''(t) = Var_{P^{x,t}} X_x`
  (`= λ² Var(∑ K(x,y_i))`);
* for `t ∈ (0,1]`: `Var_{P^{x,t}}(∑ K(x,y_i)) ≤ C N` (as an `evariance`, so non-vacuous), `0 ≤ A_x''(t) ≤ C/N`;
* `A_x` has the right derivative `E_{P_n^0} X_x` at `0` (`HasDerivWithinAt`, no junk value of `derivWithin`);
* `0 ≤ D_N(x) = A_x(1) - A_x'(0) ≤ C/N` (`wl_insDefect`);
* `A_x(1) - 2 A_x(1/2) ≤ C/N`.

Adjustment with respect to the plan: `β > 0` (as in `wl_pole_linear`); the sharper constant `βp² C₀` of the proof is
absorbed into `C`. -/
theorem wl_insertion_defect (hd : 2 ≤ d) (A βp : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
      ∀ x : Euc d,
        IsProbabilityMeasure (wl_cavLaw (HRS.Whole.withDensityReal ρ) β N (N - 1)) ∧
        (∀ t : ℝ, 0 < t →
          HasDerivAt (wl_insPressure (HRS.Whole.withDensityReal ρ) β N (N - 1) x)
            (∫ Y, wl7_X β N x Y ∂(wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x)) t ∧
          HasDerivAt (fun u => ∫ Y, wl7_X β N x Y ∂(wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) u x))
            (Var[wl7_X β N x (n := N - 1); wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x]) t) ∧
        (∀ t ∈ Ioc (0 : ℝ) 1,
          evariance (fun Y : Fin (N - 1) → Euc d => ∑ i, sphericalLogKernel x (Y i))
              (wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x) ≤ ENNReal.ofReal (C * N) ∧
          0 ≤ Var[wl7_X β N x (n := N - 1); wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x] ∧
          Var[wl7_X β N x (n := N - 1); wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x] ≤ C / N) ∧
        HasDerivWithinAt (wl_insPressure (HRS.Whole.withDensityReal ρ) β N (N - 1) x)
          (∫ Y, wl7_X β N x Y ∂(wl_cavLaw (HRS.Whole.withDensityReal ρ) β N (N - 1))) (Ici 0) 0 ∧
        0 ≤ wl_insDefect (HRS.Whole.withDensityReal ρ) β N (N - 1) x ∧
        wl_insDefect (HRS.Whole.withDensityReal ρ) β N (N - 1) x ≤ C / N ∧
        wl_insPressure (HRS.Whole.withDensityReal ρ) β N (N - 1) x 1 -
          2 * wl_insPressure (HRS.Whole.withDensityReal ρ) β N (N - 1) x (1 / 2) ≤ C / N := by
  obtain ⟨Cv, hCv0, hv⟩ := wl7_var_X hd A βp
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  refine ⟨βp ^ 2 * Cv + Cv, by positivity, fun ρ hρ hA β hβ hββp N hN x => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hK, hℓ, -, -, -⟩ := hQ ρ hρ hA β hβ.le N (by omega)
  have hn : 0 < N - 1 := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hCle : βp ^ 2 * Cv ≤ βp ^ 2 * Cv + Cv := le_add_of_nonneg_right hCv0
  have hCle' : Cv ≤ βp ^ 2 * Cv + Cv := le_add_of_nonneg_left (by positivity)
  have hvar : ∀ t ∈ Ioc (0 : ℝ) 1, Var[wl7_X β N x (n := N - 1); wl_poleLaw μ β N (N - 1) t x] ≤
      (βp ^ 2 * Cv + Cv) / N := fun t ht =>
    ((hv ρ hρ hA β hβ hββp N hN x t ht.1.le ht.2).2.2).trans
      (div_le_div_of_nonneg_right hCle hNpos.le)
  obtain ⟨hder0, hD0, hD1, hD2⟩ := wl7_defect_of_var hK hCK0 hℓ hβ.le N hn x
    (div_nonneg (by positivity) hNpos.le) hvar
  refine ⟨wl7_cav_isProb hK hCK0 hℓ hβ.le N _, fun t ht => wl7_hasDerivAt hK hCK0 hℓ hβ.le N hn x ht,
    fun t ht => ?_, hder0, hD0, hD1, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hv ρ hρ hA β hβ hββp N hN x t ht.1.le ht.2
    refine ⟨h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCle' hNpos.le)), h2,
      h3.trans (div_le_div_of_nonneg_right hCle hNpos.le)⟩
  · refine hD2.trans ?_
    have : 0 ≤ (βp ^ 2 * Cv + Cv) / N := div_nonneg (by positivity) hNpos.le
    linarith [div_le_div_of_nonneg_right (le_refl ((βp ^ 2 * Cv + Cv))) hNpos.le,
      show (βp ^ 2 * Cv + Cv) / N / 2 ≤ (βp ^ 2 * Cv + Cv) / N by linarith]

/-! ### Cavity total variation -/

section TV

/-- Variance of the fraction of particles in `S` under the pole ensembles: `≤ K₁/n`, uniformly. -/
theorem wl7_var_fracIn (hd : 2 ≤ d) (A βp : ℝ) : ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
      ∀ x : Euc d, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ S : Set (Euc d), MeasurableSet S →
        Var[wr13c2_fracIn (n := N - 1) S; wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x] ≤
          K1 / ((N - 1 : ℕ) : ℝ) := by
  obtain ⟨C1, hC10, h1⟩ := wl7_pole_evariance hd A βp
  refine ⟨C1, hC10, fun ρ hρ hA β hβ hββp N hN x t ht0 ht1 S hS => ?_⟩
  haveI := wl_isProb hρ
  have hf : Measurable (S.indicator (fun _ : Euc d => (1 : ℝ))) := measurable_const.indicator hS
  have h3 : ∫⁻ y, ‖S.indicator (fun _ : Euc d => (1 : ℝ)) y‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ 1 := by
    calc _ ≤ ∫⁻ _y, (1 : ℝ≥0∞) ∂(HRS.Whole.withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          by_cases h : y ∈ S <;> simp [Set.indicator, h]
      _ = 1 := by simp
  have h5 : evariance (fun Y : EucConfig d (N - 1) => ∑ i, S.indicator (fun _ : Euc d => (1 : ℝ)) (Y i))
      (wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) t x) ≤
      ENNReal.ofReal (C1 * ((N - 1 : ℕ) : ℝ)) := by
    refine (h1 ρ hρ hA β hβ hββp N hN x t ht0 ht1 _ hf).trans ?_
    rw [ENNReal.ofReal_mul hC10, ENNReal.ofReal_natCast]
    exact mul_le_mul' le_rfl (by simpa using mul_le_mul' (le_refl (((N - 1 : ℕ) : ℝ≥0∞))) h3)
  exact wr13c2_var_fracIn_le (by omega) hC10 h5

/-- **Pole tilt moves the one-coordinate law by `O(1/N)`**: `|P^{x,1}(Y_0 ∈ S) - P_n^0(Y_0 ∈ S)| ≤ Kt / N`,
uniformly in `x` (exponential-family TV `EF.ef_tv`, the pole variance of `wl7_var_fracIn` and the second difference
of `wl_insertion_defect`). -/
theorem wl7_tv_pole (hd : 2 ≤ d) (A βp : ℝ) : ∃ Kt : ℝ, 0 ≤ Kt ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, ∀ hN : 2 ≤ N,
      ∀ x : Euc d, ∀ S : Set (Euc d), MeasurableSet S →
        |(wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) 1 x
            {Y : Fin (N - 1) → Euc d | Y ⟨0, by omega⟩ ∈ S}).toReal -
          (wl_cavLaw (HRS.Whole.withDensityReal ρ) β N (N - 1)
            {Y : Fin (N - 1) → Euc d | Y ⟨0, by omega⟩ ∈ S}).toReal| ≤ Kt / N := by
  obtain ⟨K1, hK10, hK1⟩ := wl7_var_fracIn hd A βp
  obtain ⟨Cd, hCd0, hCd⟩ := wl_insertion_defect hd A βp
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  set K2 : ℝ := Cd * Real.exp Cd with hK2
  refine ⟨2 * Real.sqrt (2 * (K1 * K2)), by positivity, fun ρ hρ hA β hβ hββp N hN x S hS => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hK, hℓ, -, -, -⟩ := hQ ρ hρ hA β hβ.le N (by omega)
  haveI hP0 := wl7_cav_isProb hK hCK0 hℓ hβ.le N (N - 1)
  have hpos : 0 < N - 1 := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hpos
  have hnN : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set P0 := wl_cavLaw μ β N (N - 1) with hP0def
  set S' : Set (Fin (N - 1) → Euc d) := {Y | Y ⟨0, hpos⟩ ∈ S} with hS'
  have hXm := wl7_X_measurable β N x (N - 1)
  have hb := wl7_X_le_zero hβ.le N x (n := N - 1)
  obtain ⟨-, -, -, -, -, -, hΔ⟩ := hCd ρ hρ hA β hβ hββp N hN x
  rw [wl7_insPressure_eq_cgf] at hΔ
  have hδ0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hδ1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hN0]; exact_mod_cast (by omega : 1 ≤ N)
  have hΔ' : cgf (wl7_X β N x (n := N - 1)) P0 1 - 2 * cgf (wl7_X β N x (n := N - 1)) P0 (1 / 2) ≤
      Cd * (1 / (N : ℝ)) := by
    rw [mul_one_div]
    exact hΔ
  have hee := wr13c2_exp_sub_one_le _ Cd (1 / (N : ℝ)) hδ0 hδ1 hCd0 hΔ'
  have e1 : P0.tilted (wl7_X β N x (n := N - 1)) = wl_poleLaw μ β N (N - 1) 1 x := by
    have := wl7_poleLaw_eq_tilted hK hCK0 hℓ hβ.le N zero_le_one x (N - 1)
    simp only [one_mul] at this
    exact this.symm
  have e0 : P0 = wl_poleLaw μ β N (N - 1) 0 x := (wl7_poleLaw_zero hK hCK0 hℓ hβ.le N x (N - 1)).symm
  haveI hP1 := wl7_pole_isProb hK hCK0 hℓ hβ.le N zero_le_one x (N - 1)
  have htv := HRS.MarginalAux.EF.ef_tv (P := P0) hXm hb (wr13c2_measurable_fracIn (n := N - 1) hS)
    (fun Y => wr13c2_abs_fracIn_le hpos S Y)
  have hint1 : ∫ Y, wr13c2_fracIn S Y ∂(P0.tilted (wl7_X β N x (n := N - 1))) =
      (wl_poleLaw μ β N (N - 1) 1 x S').toReal := by
    rw [e1]
    exact wr13c2_integral_fracIn hpos hS _ (wl7_pole_exchangeable hK hCK0 hℓ hβ.le N 1 x (N - 1))
  have hint0 : ∫ Y, wr13c2_fracIn S Y ∂P0 = (P0 S').toReal :=
    wr13c2_integral_fracIn hpos hS P0 (wl7_cav_exchangeable hK hCK0 hℓ hβ.le N (N - 1))
  have hV0 : Var[wr13c2_fracIn (n := N - 1) S; P0] ≤ K1 / ((N - 1 : ℕ) : ℝ) := by
    rw [e0]
    exact hK1 ρ hρ hA β hβ hββp N hN x 0 le_rfl zero_le_one S hS
  have hV1 : Var[wr13c2_fracIn (n := N - 1) S; P0.tilted (wl7_X β N x (n := N - 1))] ≤
      K1 / ((N - 1 : ℕ) : ℝ) := by
    rw [e1]
    exact hK1 ρ hρ hA β hβ hββp N hN x 1 zero_le_one le_rfl S hS
  rw [hint1, hint0] at htv
  refine htv.trans ?_
  refine (wr13c2_sqrt_chain (n := ((N - 1 : ℕ) : ℝ)) (N := (N : ℝ)) hn0 hN0 hnN hK10
    (by positivity) hδ0 hV0 hV1 hee).trans (le_of_eq ?_)
  have : Real.sqrt (1 / (N : ℝ) / N) = 1 / N := by
    rw [show 1 / (N : ℝ) / N = (1 / N) ^ 2 by ring, Real.sqrt_sq hδ0]
  rw [this]
  ring

/-- Exact disintegration of the first marginal of `Q_N` over the pole laws:
`π_N(S) = ∫ P^{x,1}(Y_0 ∈ S) dπ_N(x)` (from `wl_cavity_disintegration` and exchangeability of `Q_N`). -/
theorem wl7_disint (hd : 2 ≤ d) {A : ℝ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hA : HasSphericalBound A ρ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 2 ≤ N) {S : Set (Euc d)}
    (hS : MeasurableSet S) :
    HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)) S =
      ∫⁻ x, wl_poleLaw (HRS.Whole.withDensityReal ρ) β N (N - 1) 1 x
          {Y : Fin (N - 1) → Euc d | Y ⟨0, by omega⟩ ∈ S}
        ∂(HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β
          (HRS.Whole.withDensityReal ρ))) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  set Q := HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β (HRS.Whole.withDensityReal ρ) with hQ
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set F : Euc d × (Fin n → Euc d) → ℝ≥0∞ := fun p => S.indicator (fun _ => (1 : ℝ≥0∞)) (p.2 i0) with hF
  have hFm : Measurable F :=
    (measurable_const.indicator hS).comp ((measurable_pi_apply i0).comp measurable_snd)
  have key := wl_cavity_disintegration hd hρ hA hβ n F hFm
  have hex : HRS.External.Entropy.IsExchangeable Q :=
    HRS.Whole.modulatedGibbs_isExchangeable (rieszKernel d 0) β _ (fun z => HRS.Whole.rieszKernel_neg z)
  have hLHS : ∫⁻ X : Fin (n + 1) → Euc d, F (X 0, Fin.tail X) ∂Q = HRS.Whole.firstMarginal Q S := by
    have h1 : ∀ X : Fin (n + 1) → Euc d, F (X 0, Fin.tail X) =
        ((fun X : Fin (n + 1) → Euc d => X (Fin.succ i0)) ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) X := by
      intro X
      by_cases h : X (Fin.succ i0) ∈ S <;> simp [F, Set.indicator, h, Fin.tail]
    simp_rw [h1]
    rw [lintegral_indicator_const ((measurable_pi_apply (Fin.succ i0)) hS), one_mul,
      ← Measure.map_apply (measurable_pi_apply (Fin.succ i0)) hS, wl6_firstMarginal_def,
      hex.marginal_eq (Fin.succ i0) 0]
  rw [← hLHS, key]
  refine lintegral_congr fun x => ?_
  have h2 : ∀ Y : Fin n → Euc d, F (x, Y) =
      ({Y : Fin n → Euc d | Y i0 ∈ S}).indicator (fun _ => (1 : ℝ≥0∞)) Y := by
    intro Y
    by_cases h : Y i0 ∈ S <;> simp [F, Set.indicator, h]
  simp_rw [h2]
  have hm : MeasurableSet {Y : Fin n → Euc d | Y i0 ∈ S} := (measurable_pi_apply i0) hS
  rw [lintegral_indicator_const hm, one_mul]
  rfl

/-- **Cavity total variation** (TeX `eq:r2-log-cavity-TV`): `‖π_N - ν_n‖_TV ≤ C/N` with `π_N = Q_N^{(1)}` the first
marginal of `Q_N = modulatedGibbs (rieszKernel d 0) N β μ` and `ν_n = (P_n^0)^{(1)}` the first marginal of the cavity
ensemble `wl_cavLaw μ β N (N - 1)`.  `C` depends on `d, A, βp` only (before `ρ, β, N`); all `N ≥ 2`, `β ∈ (0, βp]`. -/
theorem wl_cavity_tv (hd : 2 ≤ d) (A βp : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
      HRS.Whole.tvDist
        (HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)))
        (HRS.Whole.firstMarginal (wl_cavLaw (HRS.Whole.withDensityReal ρ) β N (N - 1))) ≤ C / N := by
  obtain ⟨Kt, hKt0, hKt⟩ := wl7_tv_pole hd A βp
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  refine ⟨Kt, hKt0, fun ρ hρ hA β hβ hββp N hN => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hK, hℓ, -, -, hQeq⟩ := hQ ρ hρ hA β hβ.le N (by omega)
  haveI hP0 := wl7_cav_isProb hK hCK0 hℓ hβ.le N (N - 1)
  have hpos : 0 < N - 1 := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI hQp : IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β μ) := by
    rw [hQeq (wl7_V hK hCK0 hℓ hβ.le N) rfl]
    exact (fieldSpec (V := wl7_V hK hCK0 hℓ hβ.le N) (wl_isField_Qfield hK hCK0 hℓ hβ.le N)
      (wl7_hlam hβ.le N) N).isProb
  set π : Measure (Euc d) := HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β μ)
    with hπ
  haveI hπp : IsProbabilityMeasure π := by
    rw [hπ]
    unfold HRS.Whole.firstMarginal
    rw [dif_pos (by omega : 0 < N)]
    infer_instance
  set K : ℝ := Kt / N with hK'
  have hK0 : 0 ≤ K := by positivity
  unfold HRS.Whole.tvDist
  refine Real.iSup_le (fun E => ?_) (by positivity)
  obtain ⟨S, hS⟩ := E
  show |(π S).toReal - ((HRS.Whole.firstMarginal (wl_cavLaw μ β N (N - 1))) S).toReal| ≤ Kt / N
  set S' : Set (Fin (N - 1) → Euc d) := {Y | Y ⟨0, hpos⟩ ∈ S} with hS'
  have hν : HRS.Whole.firstMarginal (wl_cavLaw μ β N (N - 1)) S = wl_cavLaw μ β N (N - 1) S' := by
    unfold HRS.Whole.firstMarginal
    rw [dif_pos hpos, Measure.map_apply (measurable_pi_apply (⟨0, hpos⟩ : Fin (N - 1))) hS]
    rfl
  rw [hν]
  have hdis := wl7_disint hd hρ hA hβ.le hN hS
  have hpt : ∀ x : Euc d,
      wl_poleLaw μ β N (N - 1) 1 x S' ≤ wl_cavLaw μ β N (N - 1) S' + ENNReal.ofReal K ∧
      wl_cavLaw μ β N (N - 1) S' ≤ wl_poleLaw μ β N (N - 1) 1 x S' + ENNReal.ofReal K := by
    intro x
    haveI := wl7_pole_isProb hK hCK0 hℓ hβ.le N zero_le_one x (N - 1)
    exact wr13c2_ennreal_close (measure_ne_top _ _) (measure_ne_top _ _)
      (hKt ρ hρ hA β hβ hββp N hN x S hS)
  have hπA : π S ≤ wl_cavLaw μ β N (N - 1) S' + ENNReal.ofReal K := by
    rw [hπ, hdis]
    calc ∫⁻ x, wl_poleLaw μ β N (N - 1) 1 x S' ∂π
        ≤ ∫⁻ _x, (wl_cavLaw μ β N (N - 1) S' + ENNReal.ofReal K) ∂π :=
          lintegral_mono fun x => (hpt x).1
      _ = _ := by simp
  have hAπ : wl_cavLaw μ β N (N - 1) S' ≤ π S + ENNReal.ofReal K := by
    rw [hπ, hdis]
    calc wl_cavLaw μ β N (N - 1) S'
        = ∫⁻ _x, wl_cavLaw μ β N (N - 1) S' ∂π := by simp
      _ ≤ ∫⁻ x, (wl_poleLaw μ β N (N - 1) 1 x S' + ENNReal.ofReal K) ∂π :=
          lintegral_mono fun x => (hpt x).2
      _ = ∫⁻ x, wl_poleLaw μ β N (N - 1) 1 x S' ∂π + ENNReal.ofReal K := by
          rw [lintegral_add_right _ measurable_const]
          simp
  exact wr13c2_real_close (measure_ne_top _ _) (measure_ne_top _ _) hK0 hπA hAπ

end TV

end HRS.MS.Wl
