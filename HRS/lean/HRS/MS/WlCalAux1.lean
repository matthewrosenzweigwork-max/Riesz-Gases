import HRS.MS.WrCal

/-!
# HRS.MS.WlCalAux1 -- the calibration minimiser over an abstract reference measure (WL-4a, S3.5)

Packet WL-4a of `docs/WR_LOG_PLAN.md` (contract C4).  The calibration of `HRS.MS.WrCal` is typed to the
weak reference `R0 = pairGibbsLawE q N β μ`.  For the logarithmic static row (S3.5) the reference is a
`fieldLaw` with a field and poles, so this file restates the calibration over an arbitrary probability
measure `P` on `Fin n → Euc d`; nothing here mentions a kernel (`EWeakKernel`) or a field.

Setting: `μ` a probability measure on `Euc d` (it only enters through the centering `Xi μ Ψ`),
`Ψ : Euc d → H` with `CalFeat Ψ B` (continuous and bounded), `H` a real Hilbert space, `P` a probability
measure on `Fin n → Euc d`.  The defs `Xi`, `Yf`, `empXi`, `wr11_S` of `WrCal` are reused.

Adjustments with respect to the plan (documented, harmless):
* the normalisation is the explicit pair `(c, β)` of `wr11_obj`: `wl4_calibObj c β μ Ψ P t =
  c * log E_P exp (Yf t) + ‖t‖²/(2β)`; `WrCal` is the case `c = 1/N`, `P = R0` (`wl4_calibObj_eq_calibObj`,
  `wl4_tN_eq_tN`);
* stationarity is stated for the unnormalised statistic `S = ∑ Ξ(x_i)` (`wl4_tN_eq`, valid for every `n`) and
  for the empirical average (`wl4_tN_eq_empXi`: `t = -(β c n) • E_{R_N} μ_n(Ξ)`, `0 < n`; for `c = 1/n` this
  is `t = -β • E_{R_N} μ_n(Ξ)`, `wl4_tN_eq_empXi_inv`); the norm bound is `‖t‖ ≤ β c n ‖E_P μ_n(Ξ)‖`
  (`wl4_tN_norm_le_empXi`, `‖t‖ ≤ β ‖E_P μ_n(Ξ)‖` for `c = 1/n`);
* extra, cheap consumers' lemmas: `wl4_RN_le_smul` (`wl4_tilt_le_smul`) (bounded density of `R_N` against `P`),
  `wl4_RN_eq_withDensity_of` and `wl4_RN_absolutelyContinuous_of` (transfer of a density of `P` against a
  reference such as `Measure.pi`).

Exports (names in `HRS.MS.Wl`):
* defs `wl4_calibF`, `wl4_calibObj`, `wl4_tN`, `wl4_RN`;
* `wl4_exists_calib_min`, `wl4_calib_min_unique`, `wl4_tN_spec`, `wl4_tN_eq`, `wl4_tN_eq_empXi`,
  `wl4_tN_norm_le`, `wl4_tN_norm_le_empXi`;
* `wl4_isProb_RN`, `wl4_RN_eq_withDensity`, `wl4_RN_absolutelyContinuous`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.MS.Wr

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The log-partition function `t ↦ log E_P exp (Yf t)` over an abstract reference measure `P`. -/
def wl4_calibF (μ : Measure (Euc d)) (Ψ : Euc d → H) {n : ℕ} (P : Measure (Fin n → Euc d))
    (t : H) : ℝ :=
  Real.log (∫ X, Real.exp (Yf μ Ψ t X) ∂P)

/-- The calibration objective `c * log E_P exp (Yf t) + ‖t‖²/(2β)`. -/
def wl4_calibObj (c β : ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) {n : ℕ}
    (P : Measure (Fin n → Euc d)) (t : H) : ℝ :=
  c * wl4_calibF μ Ψ P t + ‖t‖ ^ 2 / (2 * β)

open Classical in
/-- The calibration parameter: a minimiser of `wl4_calibObj` (`0` if there is none; existence is
`wl4_exists_calib_min`, it is `Classical.choose` of that statement). -/
def wl4_tN (c β : ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) {n : ℕ} (P : Measure (Fin n → Euc d)) : H :=
  if h : ∃ t, ∀ s, wl4_calibObj c β μ Ψ P t ≤ wl4_calibObj c β μ Ψ P s then h.choose else 0

/-- The calibrated reference `R_N = P` tilted by `Yf (t_N)`. -/
def wl4_RN (c β : ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) {n : ℕ} (P : Measure (Fin n → Euc d)) :
    Measure (Fin n → Euc d) :=
  P.tilted (Yf μ Ψ (wl4_tN c β μ Ψ P))

/-- `R_N` has density `exp (Yf t_N) / Z` against `P`, `Z = ∫ exp (Yf t_N) dP`. -/
theorem wl4_RN_eq_withDensity (c β : ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) {n : ℕ}
    (P : Measure (Fin n → Euc d)) :
    wl4_RN c β μ Ψ P = P.withDensity (fun X => ENNReal.ofReal
      (Real.exp (Yf μ Ψ (wl4_tN c β μ Ψ P) X) /
        ∫ Y, Real.exp (Yf μ Ψ (wl4_tN c β μ Ψ P) Y) ∂P)) := rfl

/-- `R_N` is absolutely continuous with respect to `P`. -/
theorem wl4_RN_absolutelyContinuous (c β : ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) {n : ℕ}
    (P : Measure (Fin n → Euc d)) : wl4_RN c β μ Ψ P ≪ P := by
  rw [wl4_RN_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

section Basic

variable [CompleteSpace H] {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Ψ : Euc d → H} {B : ℝ}
  {n : ℕ} {P : Measure (Fin n → Euc d)} [IsProbabilityMeasure P] {c β : ℝ}

lemma wl4_calibObj_eq : wl4_calibObj c β μ Ψ P = wr11_obj c β P (wr11_S μ Ψ) := by
  funext t
  unfold wl4_calibObj wl4_calibF wr11_obj wr11_cF wr11_Z
  simp_rw [wr11_Yf_eq]

lemma wl4_RN_eq_tilted :
    wl4_RN c β μ Ψ P = P.tilted (wr11_Ya (wr11_S μ Ψ) (wl4_tN c β μ Ψ P)) := by
  unfold wl4_RN; rw [wr11_Yf_funext]

/-- The objective is continuous. -/
lemma wl4_continuous_calibObj (h : CalFeat Ψ B) (c β : ℝ) :
    Continuous (wl4_calibObj c β μ Ψ P) := by
  rw [wl4_calibObj_eq]
  exact wr11_continuous_obj h.wr11_bdd _ _

/-- The objective is `(1/β)`-strongly convex on all of `H` (`0 ≤ c`, `0 < β`). -/
theorem wl4_calibObj_strongConvexOn (h : CalFeat Ψ B) (hc : 0 ≤ c) (hβ : 0 < β) :
    StrongConvexOn Set.univ (1 / β) (wl4_calibObj c β μ Ψ P) := by
  rw [wl4_calibObj_eq]
  exact wr11_strongConvexOn_obj h.wr11_bdd hc hβ

/-- **Existence of the calibration minimiser** (strong convexity and the parallelogram law). -/
theorem wl4_exists_calib_min (h : CalFeat Ψ B) (hc : 0 ≤ c) (hβ : 0 < β) :
    ∃ t, ∀ s, wl4_calibObj c β μ Ψ P t ≤ wl4_calibObj c β μ Ψ P s := by
  rw [wl4_calibObj_eq]
  exact wr11_exists_obj_min h.wr11_bdd hc hβ

/-- The calibration minimiser is unique. -/
theorem wl4_calib_min_unique (h : CalFeat Ψ B) (hc : 0 ≤ c) (hβ : 0 < β) {t₁ t₂ : H}
    (h₁ : ∀ s, wl4_calibObj c β μ Ψ P t₁ ≤ wl4_calibObj c β μ Ψ P s)
    (h₂ : ∀ s, wl4_calibObj c β μ Ψ P t₂ ≤ wl4_calibObj c β μ Ψ P s) : t₁ = t₂ := by
  rw [wl4_calibObj_eq] at h₁ h₂
  exact wr11_obj_unique h.wr11_bdd hc hβ h₁ h₂

/-- `wl4_tN` is a minimiser of `wl4_calibObj`. -/
theorem wl4_tN_spec (h : CalFeat Ψ B) (hc : 0 ≤ c) (hβ : 0 < β) (s : H) :
    wl4_calibObj c β μ Ψ P (wl4_tN c β μ Ψ P) ≤ wl4_calibObj c β μ Ψ P s := by
  have hex := wl4_exists_calib_min (μ := μ) (P := P) h hc hβ
  unfold wl4_tN
  rw [dif_pos hex]
  exact hex.choose_spec s

lemma wl4_tN_min_obj (h : CalFeat Ψ B) (hc : 0 ≤ c) (hβ : 0 < β) :
    ∀ s, wr11_obj c β P (wr11_S μ Ψ) (wl4_tN c β μ Ψ P) ≤ wr11_obj c β P (wr11_S μ Ψ) s := by
  intro s
  rw [← wl4_calibObj_eq]
  exact wl4_tN_spec h hc hβ s

/-- **Stationarity**: `t_N = -(β c) • E_{R_N} ∑_i Ξ(x_i)` (any `n`, `0 < c`, `0 < β`). -/
theorem wl4_tN_eq (h : CalFeat Ψ B) (hc : 0 < c) (hβ : 0 < β) :
    wl4_tN c β μ Ψ P = -(β * c) • ∫ X, wr11_S μ Ψ X ∂(wl4_RN c β μ Ψ P) := by
  have hst := wr11_stationary h.wr11_bdd hc hβ (wl4_tN_min_obj (μ := μ) (P := P) h hc.le hβ)
  rw [wl4_RN_eq_tilted]
  exact hst

/-- **Stationarity for the empirical average** (`0 < n`): `t_N = -(β c n) • E_{R_N} μ_n(Ξ)`.
For `c = 1/n` this is `-β • E_{R_N} μ_n(Ξ)` (`wl4_tN_eq_empXi_inv`). -/
theorem wl4_tN_eq_empXi (h : CalFeat Ψ B) (hn : 0 < n) (hc : 0 < c) (hβ : 0 < β) :
    wl4_tN c β μ Ψ P = -(β * c * n) • ∫ X, empXi μ Ψ X ∂(wl4_RN c β μ Ψ P) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have e : ∫ X, empXi μ Ψ X ∂(wl4_RN c β μ Ψ P) =
      (1 / (n : ℝ)) • ∫ X, wr11_S μ Ψ X ∂(wl4_RN c β μ Ψ P) := by
    simp_rw [wr11_empXi_eq]
    exact integral_smul _ _
  rw [e, smul_smul, wl4_tN_eq h hc hβ]
  congr 1
  field_simp

/-- The case `c = 1/n`: `t_N = -β • E_{R_N} μ_n(Ξ)` (the normalisation of `WrCal`). -/
theorem wl4_tN_eq_empXi_inv (h : CalFeat Ψ B) (hn : 0 < n) (hβ : 0 < β) :
    wl4_tN (1 / (n : ℝ)) β μ Ψ P = -β • ∫ X, empXi μ Ψ X ∂(wl4_RN (1 / (n : ℝ)) β μ Ψ P) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  rw [wl4_tN_eq_empXi h hn hc hβ]
  congr 1
  field_simp

/-- **Norm bound**: `‖t_N‖ ≤ β c ‖E_P ∑_i Ξ(x_i)‖`. -/
theorem wl4_tN_norm_le (h : CalFeat Ψ B) (hc : 0 < c) (hβ : 0 < β) :
    ‖wl4_tN c β μ Ψ P‖ ≤ β * c * ‖∫ X, wr11_S μ Ψ X ∂P‖ :=
  wr11_norm_le h.wr11_bdd hc hβ (wl4_tN_min_obj (μ := μ) (P := P) h hc.le hβ)

/-- **Norm bound for the empirical average**: `‖t_N‖ ≤ β c n ‖E_P μ_n(Ξ)‖` (`0 < n`).
For `c = 1/n` this is `‖t_N‖ ≤ β ‖E_P μ_n(Ξ)‖`. -/
theorem wl4_tN_norm_le_empXi (h : CalFeat Ψ B) (hn : 0 < n) (hc : 0 < c) (hβ : 0 < β) :
    ‖wl4_tN c β μ Ψ P‖ ≤ β * c * n * ‖∫ X, empXi μ Ψ X ∂P‖ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ∫ X, empXi μ Ψ X ∂P = (1 / (n : ℝ)) • ∫ X, wr11_S μ Ψ X ∂P := by
    simp_rw [wr11_empXi_eq]
    exact integral_smul _ _
  have h1 := wl4_tN_norm_le (μ := μ) (P := P) h hc hβ
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖wl4_tN c β μ Ψ P‖ ≤ β * c * ‖∫ X, wr11_S μ Ψ X ∂P‖ := h1
    _ = _ := by field_simp

/-- The normalising constant `∫ exp (Yf t) dP` is positive. -/
lemma wl4_Z_pos (h : CalFeat Ψ B) (t : H) : 0 < ∫ X, Real.exp (Yf μ Ψ t X) ∂P := by
  simp_rw [wr11_Yf_eq]
  exact wr11_Z_pos h.wr11_bdd t

/-- The calibrated reference is a probability measure. -/
theorem wl4_isProb_RN (h : CalFeat Ψ B) :
    IsProbabilityMeasure (wl4_RN c β μ Ψ P) := by
  unfold wl4_RN
  have := h.integrable_exp_Yf (μ := μ) P (wl4_tN c β μ Ψ P) 1
  simp only [one_mul] at this
  exact isProbabilityMeasure_tilted this

/-- If `P` has density `f` against `Q`, then `R_N` has density `f * exp (Yf t_N)/Z` against `Q`. -/
theorem wl4_RN_eq_withDensity_of (h : CalFeat Ψ B) {Q : Measure (Fin n → Euc d)}
    {f : (Fin n → Euc d) → ℝ≥0∞} (hf : Measurable f) (hP : P = Q.withDensity f) :
    wl4_RN c β μ Ψ P = Q.withDensity (fun X => f X * ENNReal.ofReal
      (Real.exp (Yf μ Ψ (wl4_tN c β μ Ψ P) X) /
        ∫ Y, Real.exp (Yf μ Ψ (wl4_tN c β μ Ψ P) Y) ∂P)) := by
  have hg : Measurable fun X : Fin n → Euc d => ENNReal.ofReal
      (Real.exp (Yf μ Ψ (wl4_tN c β μ Ψ P) X) /
        ∫ Y, Real.exp (Yf μ Ψ (wl4_tN c β μ Ψ P) Y) ∂P) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (h.measurable_Yf _)).div_const _)
  calc wl4_RN c β μ Ψ P = P.withDensity _ := wl4_RN_eq_withDensity c β μ Ψ P
    _ = (Q.withDensity f).withDensity _ := by rw [← hP]
    _ = _ := (withDensity_mul Q hf hg).symm

/-- If `P ≪ Q` then `R_N ≪ Q`. -/
theorem wl4_RN_absolutelyContinuous_of {Q : Measure (Fin n → Euc d)} (hPQ : P ≪ Q) :
    wl4_RN c β μ Ψ P ≪ Q :=
  (wl4_RN_absolutelyContinuous c β μ Ψ P).trans hPQ

/-- Tie to `WrCal`: for `P = R0 = pairGibbsLawE q N β μ` and `c = 1/N` the objective is `calibObj`. -/
lemma wl4_calibObj_eq_calibObj (q : Euc d → Euc d → ℝ) (N : ℕ) (β : ℝ) :
    wl4_calibObj (1 / (N : ℝ)) β μ Ψ (pairGibbsLawE q N β μ) = calibObj q μ Ψ β N := by
  funext t
  unfold wl4_calibObj wl4_calibF calibObj calibF
  ring

/-- Tie to `WrCal`: for `P = R0` and `c = 1/N` the minimiser is `tN`. -/
lemma wl4_tN_eq_tN (q : Euc d → Euc d → ℝ) (N : ℕ) (β : ℝ) :
    wl4_tN (1 / (N : ℝ)) β μ Ψ (pairGibbsLawE q N β μ) = tN q μ Ψ β N := by
  have e := wl4_calibObj_eq_calibObj (μ := μ) (Ψ := Ψ) q N β
  unfold wl4_tN tN
  rw [e]

/-- Tie to `WrCal`: the calibrated references agree. -/
lemma wl4_RN_eq_RN (q : Euc d → Euc d → ℝ) (N : ℕ) (β : ℝ) :
    wl4_RN (1 / (N : ℝ)) β μ Ψ (pairGibbsLawE q N β μ) = RN q μ Ψ β N := by
  unfold wl4_RN RN
  rw [wl4_tN_eq_tN]

/-- The density of `R_N` against `P` is bounded: `R_N ≤ exp (2 ‖t‖ n (2B)) • P` (any `t`). -/
theorem wl4_tilt_le_smul (h : CalFeat Ψ B) (t : H) :
    P.tilted (Yf μ Ψ t) ≤ ENNReal.ofReal (Real.exp (2 * (‖t‖ * (n * (2 * B))))) • P := by
  set T : ℝ := ‖t‖ * (n * (2 * B)) with hT
  have hY : ∀ X : Fin n → Euc d, |Yf μ Ψ t X| ≤ T := fun X => h.abs_Yf_le (μ := μ) t X
  have hZ : Real.exp (-T) ≤ ∫ X, Real.exp (Yf μ Ψ t X) ∂P := by
    have hint := h.integrable_exp_Yf (μ := μ) P t 1
    simp only [one_mul] at hint
    calc Real.exp (-T) = ∫ _X, Real.exp (-T) ∂P := by simp
      _ ≤ _ := integral_mono (integrable_const _) hint fun X =>
        Real.exp_le_exp.2 (by linarith [neg_abs_le (Yf μ Ψ t X), hY X])
  have hg : ∀ X : Fin n → Euc d, ENNReal.ofReal (Real.exp (Yf μ Ψ t X) / ∫ Y, Real.exp (Yf μ Ψ t Y) ∂P) ≤
      ENNReal.ofReal (Real.exp (2 * T)) := by
    intro X
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : 0 < Real.exp (-T) := Real.exp_pos _
    rw [div_le_iff₀ (lt_of_lt_of_le hpos hZ)]
    calc Real.exp (Yf μ Ψ t X) ≤ Real.exp T := Real.exp_le_exp.2 ((le_abs_self _).trans (hY X))
      _ = Real.exp (2 * T) * Real.exp (-T) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le
  rw [Measure.le_iff]
  intro S hS
  change (P.withDensity _) S ≤ _
  rw [withDensity_apply _ hS, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ X in S, _ ∂P ≤ ∫⁻ _X in S, ENNReal.ofReal (Real.exp (2 * T)) ∂P :=
        lintegral_mono hg
    _ = _ := by rw [setLIntegral_const]

theorem wl4_RN_le_smul (h : CalFeat Ψ B) :
    wl4_RN c β μ Ψ P ≤
      ENNReal.ofReal (Real.exp (2 * (‖wl4_tN c β μ Ψ P‖ * (n * (2 * B))))) • P :=
  wl4_tilt_le_smul h _

end Basic

end HRS.MS.Wl
