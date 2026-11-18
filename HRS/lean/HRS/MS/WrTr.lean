import HRS.MS.WrTrAux2

/-!
# HRS.MS.WrTr -- trace bound, `dQ/dR_N ≤ C`, variance transfer (WR-11b, T6)

Packet WR-11b of `docs/WR_B_PLAN.md` (T6; TeX `euc-transfer`, `euc-feature-trace`), namespace `HRS.MS.Wr`,
helper prefix `wr11b_`.  Euclidean port of `HRS/Equilibrium/CalibratedReference.lean:1097-1359` with the
feature space `ℝ^M` replaced by a separable real Hilbert space `H`.

Setting: `TransferHyp μ a q k g Ψ` (`WrTrAux1`): `μ` an atomless probability measure on `Euc d`,
`(x, y) ↦ q (x - y)` an `EWeakKernel μ a` (the `q_τ` of the heat split), `Ψ` a feature map with Gram kernel
`k (x - y)` (`FeatHyp Ψ k`), `g = q + k` off the origin.  `R_N = RN (q (x-y)) μ Ψ β N` is the calibrated weak
reference (`WrCal`), `Q = modulatedGibbs g N β μ`.  The two smallness hypotheses are explicit:
`ht : ∀ x, |⟪t_N, Ξ x⟫| ≤ 1` (`hsmall`, the conclusion of `euc_field_small` of WR-12a combined with
`tN_norm_le`) and `hκ : wr11b_KappaSmall β a` (`4 e^{2βa+1} β a ≤ 1/2`, smallness of the weak coupling).

Exported statements (names in `HRS.MS.Wr`):
* `trace_le`: `∫ ‖S_N - √N Ξ̄_N‖² dR_N ≤ 8 k(0)`;
* `TransferHyp.Q_le_smul_RN`: `Q ≤ ofReal (exp (4 β k(0))) • R_N`;
* `TransferHyp.variance_transfer`: `evariance F Q ≤ ofReal (exp (4 β k(0))) * evariance F R_N`
  for every `F` that is a.e. strongly measurable for `R_N` (no integrability hypothesis);
* `euc_*` corollaries for the Riesz kernel `g = rieszKernel d s`, the heat split `q = qTau`, `k = kTau` and the
  feature map `featMap d s τ`: the constants are uniform in the density `ρ ≤ M`, in `β ∈ (0, βp]` and in `N ≥ N0`.

Adjustment with respect to the plan (documented, harmless): the trace bound is proved with the constant `8 k(0)`
(the torus constant `8 g_L(0)`), the plan's `C k(0)`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `D_N = S_N - √N Ξ̄_N`. -/
def wr11b_D (q : Euc d → ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) (β : ℝ) (N : ℕ)
    (X : Fin N → Euc d) : H :=
  wr11b_Sstat μ Ψ X - Real.sqrt N • Xibar (wr11b_dk q) μ Ψ β N

theorem wr11b_logW_eq (q : Euc d → ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) (β : ℝ) (N : ℕ)
    (X : Fin N → Euc d) :
    wr11b_logW q μ Ψ β N X = -(β / 2) * ‖wr11b_D q μ Ψ β N X‖ ^ 2 := rfl

section Main

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q k g : Euc d → ℝ} {Ψ : Euc d → H}
  {N : ℕ} {β : ℝ} [CompleteSpace H]

theorem wr11b_isProb_RN (h : TransferHyp μ a q k g Ψ) (hβ : 0 ≤ β) (hN : 0 < N) :
    IsProbabilityMeasure (RN (wr11b_dk q) μ Ψ β N) :=
  isProb_RN h.weak h.calFeat hβ hN

theorem wr11b_norm_empXi_le (h : TransferHyp μ a q k g Ψ) (hN : 0 < N) (X : Fin N → Euc d) :
    ‖empXi μ Ψ X‖ ≤ 2 * Real.sqrt (k 0) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [wr11_empXi_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have : ‖wr11_S μ Ψ X‖ ≤ N * (2 * Real.sqrt (k 0)) := (h.calFeat.wr11_bdd (N := N)).bound X
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hN']
  linarith

theorem wr11b_norm_Xibar_le (h : TransferHyp μ a q k g Ψ) (hβ : 0 ≤ β) (hN : 0 < N) :
    ‖Xibar (wr11b_dk q) μ Ψ β N‖ ≤ 2 * Real.sqrt (k 0) := by
  haveI := wr11b_isProb_RN h hβ hN
  have := norm_integral_le_of_norm_le_const (μ := RN (wr11b_dk q) μ Ψ β N)
    (f := empXi μ Ψ (N := N)) (C := 2 * Real.sqrt (k 0))
    (Eventually.of_forall fun X => wr11b_norm_empXi_le h hN X)
  simpa [Xibar] using this

theorem wr11b_norm_D_le (h : TransferHyp μ a q k g Ψ) (hβ : 0 ≤ β) (hN : 0 < N) (X : Fin N → Euc d) :
    ‖wr11b_D q μ Ψ β N X‖ ≤ Real.sqrt N * (4 * Real.sqrt (k 0)) := by
  unfold wr11b_D wr11b_Sstat
  calc ‖Real.sqrt N • empXi μ Ψ X - Real.sqrt N • Xibar (wr11b_dk q) μ Ψ β N‖
      ≤ ‖Real.sqrt N • empXi μ Ψ X‖ + ‖Real.sqrt N • Xibar (wr11b_dk q) μ Ψ β N‖ := norm_sub_le _ _
    _ = Real.sqrt N * ‖empXi μ Ψ X‖ + Real.sqrt N * ‖Xibar (wr11b_dk q) μ Ψ β N‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt N * (2 * Real.sqrt (k 0)) + Real.sqrt N * (2 * Real.sqrt (k 0)) := by
        gcongr
        · exact wr11b_norm_empXi_le h hN X
        · exact wr11b_norm_Xibar_le h hβ hN
    _ = _ := by ring

theorem wr11b_continuous_D (h : TransferHyp μ a q k g Ψ) :
    Continuous (wr11b_D q μ Ψ β N) :=
  (wr11b_continuous_Sstat h).sub continuous_const

/-- For every `v : H`: `E_{R_N} ⟪v, S_N - √N Ξ̄_N⟫² ≤ 2 E_{R_N} ⟪v, Ξ(x_1)⟫²`. -/
theorem wr11b_inner_sq_le (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : wr11b_KappaSmall β a)
    [NeZero N] (v : H) :
    ∫ X, (inner ℝ v (wr11b_D q μ Ψ β N X)) ^ 2 ∂(RN (wr11b_dk q) μ Ψ β N) ≤
      2 * ∫ X, (inner ℝ v (Xi μ Ψ (X 0))) ^ 2 ∂(RN (wr11b_dk q) μ Ψ β N) := by
  haveI := wr11b_isProb_RN h hβ.le hN
  set Pn := RN (wr11b_dk q) μ Ψ β N with hR
  set f : Euc d → ℝ := fun x => inner ℝ v (Xi μ Ψ x) with hf
  have hfm : Measurable f := (wr11b_continuous_inner_Xi h v).measurable
  have hfb : ∀ x, |f x| ≤ ‖v‖ * (2 * Real.sqrt (k 0)) := fun x =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (h.calFeat.norm_Xi_le x) (norm_nonneg _))
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set G : (Fin N → Euc d) → ℝ := fun X => ∑ i, f (X i) with hG
  have hGm : Measurable G := Finset.measurable_sum _ fun j _ => hfm.comp (measurable_pi_apply j)
  have hE : ∀ X, inner ℝ v (wr11b_D q μ Ψ β N X) =
      Real.sqrt N * ((1 / (N : ℝ)) * G X - ∫ Y, (1 / (N : ℝ)) * G Y ∂Pn) := by
    intro X
    have hemp : ∀ Y : Fin N → Euc d, inner ℝ v (empXi μ Ψ Y) = (1 / (N : ℝ)) * G Y := by
      intro Y
      unfold empXi
      rw [real_inner_smul_right, inner_sum]
    have e1 : inner ℝ v (Xibar (wr11b_dk q) μ Ψ β N) = ∫ Y, (1 / (N : ℝ)) * G Y ∂Pn := by
      unfold Xibar
      rw [← integral_inner (h.calFeat.integrable_empXi Pn) v]
      exact integral_congr_ae (Eventually.of_forall hemp)
    unfold wr11b_D wr11b_Sstat
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, hemp, e1]
    ring
  have hvar := wr11b_var_sum_le h hβ.le hN ht hκ f hfm _ hfb
  have hint1 : ∫ X, (inner ℝ v (wr11b_D q μ Ψ β N X)) ^ 2 ∂Pn =
      N * variance (fun X => (1 / (N : ℝ)) * G X) Pn := by
    rw [variance_eq_integral ((hGm.const_mul _).aemeasurable)]
    simp_rw [hE, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    rw [integral_const_mul]
  have hvar2 : variance (fun X => (1 / (N : ℝ)) * G X) Pn = (1 / (N : ℝ)) ^ 2 * variance G Pn :=
    variance_const_mul _ _ _
  have hπ : variance f (Pn.map (fun X => X 0)) ≤ ∫ X, (f (X 0)) ^ 2 ∂Pn := by
    have := variance_le_expectation_sq (μ := Pn.map (fun X : Fin N → Euc d => X 0)) (X := f)
      hfm.aestronglyMeasurable
    refine this.trans (le_of_eq ?_)
    rw [integral_map (measurable_pi_apply 0).aemeasurable (hfm.pow_const 2).aestronglyMeasurable]
    rfl
  rw [hint1, hvar2]
  have hv0 : 0 ≤ variance f (Pn.map (fun X => X 0)) := variance_nonneg _ _
  calc (N : ℝ) * ((1 / (N : ℝ)) ^ 2 * variance G Pn) ≤
      (N : ℝ) * ((1 / (N : ℝ)) ^ 2 * (2 * N * variance f (Pn.map (fun X => X 0)))) := by
        gcongr
    _ = 2 * variance f (Pn.map (fun X => X 0)) := by field_simp
    _ ≤ 2 * ∫ X, (f (X 0)) ^ 2 ∂Pn := by linarith

/-- The trace over a finite orthonormal family: `E_{R_N} ∑_j ⟪e_j, D_N⟫² ≤ 8 k(0)`. -/
theorem wr11b_fin_trace (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : wr11b_KappaSmall β a)
    [NeZero N] {n : ℕ} (e : Fin n → H) (he : Orthonormal ℝ e) :
    ∫ X, ∑ j, (inner ℝ (e j) (wr11b_D q μ Ψ β N X)) ^ 2 ∂(RN (wr11b_dk q) μ Ψ β N) ≤ 8 * k 0 := by
  haveI := wr11b_isProb_RN h hβ.le hN
  set Pn := RN (wr11b_dk q) μ Ψ β N with hR
  have hk0 : 0 ≤ k 0 := h.feat.k_zero_nonneg
  have hDi : ∀ v : H, Integrable (fun X => (inner ℝ v (wr11b_D q μ Ψ β N X)) ^ 2) Pn := fun v =>
    Integrable.of_bound
      (((continuous_const.inner (wr11b_continuous_D h)).pow 2).aestronglyMeasurable)
      ((‖v‖ * (Real.sqrt N * (4 * Real.sqrt (k 0)))) ^ 2) (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hx : |inner ℝ v (wr11b_D q μ Ψ β N X)| ≤ ‖v‖ * (Real.sqrt N * (4 * Real.sqrt (k 0))) :=
          (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (wr11b_norm_D_le h hβ.le hN X) (norm_nonneg _))
        exact sq_le_sq' (by linarith [abs_le.1 hx]) (by linarith [abs_le.1 hx]))
  have hgi : ∀ v : H, Integrable (fun X : Fin N → Euc d => (inner ℝ v (Xi μ Ψ (X 0))) ^ 2) Pn :=
    fun v => Integrable.of_bound
      (((continuous_const.inner (h.calFeat.continuous_Xi.comp (continuous_apply 0))).pow 2).aestronglyMeasurable)
      ((‖v‖ * (2 * Real.sqrt (k 0))) ^ 2) (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hx : |inner ℝ v (Xi μ Ψ (X 0))| ≤ ‖v‖ * (2 * Real.sqrt (k 0)) :=
          (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (h.calFeat.norm_Xi_le _) (norm_nonneg _))
        exact sq_le_sq' (by linarith [abs_le.1 hx]) (by linarith [abs_le.1 hx]))
  rw [integral_finsetSum _ fun j _ => hDi (e j)]
  have hbess : ∀ X : Fin N → Euc d,
      ∑ j, (inner ℝ (e j) (Xi μ Ψ (X 0))) ^ 2 ≤ 4 * k 0 := fun X => by
    have h1 := he.sum_inner_products_le (Xi μ Ψ (X 0)) (s := Finset.univ)
    simp only [Real.norm_eq_abs, sq_abs] at h1
    refine h1.trans ?_
    have h2 := h.calFeat.norm_Xi_le (μ := μ) (X 0)
    have h3 : ‖Xi μ Ψ (X 0)‖ ^ 2 ≤ (2 * Real.sqrt (k 0)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc ‖Xi μ Ψ (X 0)‖ ^ 2 ≤ (2 * Real.sqrt (k 0)) ^ 2 := h3
      _ = 4 * k 0 := by rw [mul_pow, Real.sq_sqrt hk0]; ring
  calc ∑ j, ∫ X, (inner ℝ (e j) (wr11b_D q μ Ψ β N X)) ^ 2 ∂Pn
      ≤ ∑ j, 2 * ∫ X, (inner ℝ (e j) (Xi μ Ψ (X 0))) ^ 2 ∂Pn :=
        Finset.sum_le_sum fun j _ => wr11b_inner_sq_le h hβ hN ht hκ (e j)
    _ = 2 * ∫ X, ∑ j, (inner ℝ (e j) (Xi μ Ψ (X 0))) ^ 2 ∂Pn := by
        rw [← Finset.mul_sum, ← integral_finsetSum _ fun j _ => hgi (e j)]
    _ ≤ 2 * ∫ _X, 4 * k 0 ∂Pn := by
        exact mul_le_mul_of_nonneg_left (integral_mono (integrable_finsetSum _ fun j _ => hgi (e j))
          (integrable_const _) hbess) (by norm_num)
    _ = 8 * k 0 := by simp; ring

variable [TopologicalSpace.SeparableSpace H]

/-- **The trace bound** (`euc-feature-trace`): `∫ ‖S_N - √N Ξ̄_N‖² dR_N ≤ 8 k(0)`. -/
theorem trace_le (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N)
    (hsmall : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1)
    (hκ : wr11b_KappaSmall β a) :
    ∫ X, ‖wr11b_Sstat μ Ψ X - Real.sqrt N • Xibar (wr11b_dk q) μ Ψ β N‖ ^ 2
      ∂(RN (wr11b_dk q) μ Ψ β N) ≤ 8 * k 0 := by
  haveI := wr11b_isProb_RN h hβ.le hN
  haveI : NeZero N := ⟨hN.ne'⟩
  exact wr11b_trace_limit (RN (wr11b_dk q) μ Ψ β N) (wr11b_continuous_D h).stronglyMeasurable
    (wr11b_norm_D_le h hβ.le hN) (fun n e he => wr11b_fin_trace h hβ hN hsmall hκ e he)

/-! ### The bounded density and the transfer -/

theorem wr11b_continuous_logW (h : TransferHyp μ a q k g Ψ) :
    Continuous (wr11b_logW q μ Ψ β N) :=
  continuous_const.mul ((wr11b_continuous_D h).norm.pow 2)

theorem wr11b_logW_nonpos (hβ : 0 < β) (X : Fin N → Euc d) : wr11b_logW q μ Ψ β N X ≤ 0 := by
  rw [wr11b_logW_eq]
  have : 0 ≤ (β / 2) * ‖wr11b_D q μ Ψ β N X‖ ^ 2 := by positivity
  linarith

theorem wr11b_integrable_logW (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N)
    {P : Measure (Fin N → Euc d)} [IsFiniteMeasure P] : Integrable (wr11b_logW q μ Ψ β N) P := by
  set C := Real.sqrt N * (4 * Real.sqrt (k 0)) with hC
  refine Integrable.of_bound (wr11b_continuous_logW h).aestronglyMeasurable ((β / 2) * C ^ 2)
    (Eventually.of_forall fun X => ?_)
  have h1 := wr11b_norm_D_le h hβ.le hN X
  have h0 := norm_nonneg (wr11b_D q μ Ψ β N X)
  rw [Real.norm_eq_abs, wr11b_logW_eq, abs_of_nonpos (by
    have : 0 ≤ (β / 2) * ‖wr11b_D q μ Ψ β N X‖ ^ 2 := by positivity
    linarith)]
  have : ‖wr11b_D q μ Ψ β N X‖ ^ 2 ≤ C ^ 2 := by gcongr
  nlinarith

theorem wr11b_integrable_exp_logW (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β)
    {P : Measure (Fin N → Euc d)} [IsFiniteMeasure P] :
    Integrable (fun X => Real.exp (wr11b_logW q μ Ψ β N X)) P :=
  Integrable.of_bound (Real.continuous_exp.comp (wr11b_continuous_logW h)).aestronglyMeasurable 1
    (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (wr11b_logW_nonpos hβ X))

/-- Jensen: `E[Y] ≤ log E[exp Y]`. -/
theorem wr11b_log_integral_exp_ge {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {Y : α → ℝ} (hY : Integrable Y P)
    (hE : Integrable (fun x => Real.exp (Y x)) P) :
    ∫ x, Y x ∂P ≤ Real.log (∫ x, Real.exp (Y x) ∂P) := by
  set a := ∫ x, Y x ∂P
  have hpos : 0 < ∫ x, Real.exp (Y x) ∂P := integral_exp_pos hE
  rw [Real.le_log_iff_exp_le hpos]
  have h1 : ∀ x, Real.exp a * (Y x - a + 1) ≤ Real.exp (Y x) := by
    intro x
    have := Real.add_one_le_exp (Y x - a)
    calc Real.exp a * (Y x - a + 1) ≤ Real.exp a * Real.exp (Y x - a) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = Real.exp (Y x) := by rw [← Real.exp_add]; ring_nf
  have h2 : ∫ x, Real.exp a * (Y x - a + 1) ∂P = Real.exp a := by
    have hi : Integrable (fun x => Y x - a) P := hY.sub (integrable_const _)
    rw [integral_const_mul, integral_add hi (integrable_const _), integral_sub hY (integrable_const _)]
    simp [a]
  rw [← h2]
  exact integral_mono ((hY.sub (integrable_const _)).add (integrable_const _) |>.const_mul _) hE h1

/-- **Denominator bound** (Jensen + trace): `E_{R_N}[e^{-β‖S_N-√NΞ̄_N‖²/2}] ≥ e^{-4β k(0)}`. -/
theorem wr11b_exp_le_integral_exp_logW (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N)
    (hsmall : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : wr11b_KappaSmall β a) :
    Real.exp (-(4 * β * k 0)) ≤ ∫ X, Real.exp (wr11b_logW q μ Ψ β N X) ∂(RN (wr11b_dk q) μ Ψ β N) := by
  haveI := wr11b_isProb_RN h hβ.le hN
  have hJ := wr11b_log_integral_exp_ge (wr11b_integrable_logW h hβ hN (P := RN (wr11b_dk q) μ Ψ β N))
    (wr11b_integrable_exp_logW h hβ (P := RN (wr11b_dk q) μ Ψ β N))
  have hpos := integral_exp_pos (μ := RN (wr11b_dk q) μ Ψ β N) (f := wr11b_logW q μ Ψ β N)
    (wr11b_integrable_exp_logW h hβ)
  have htr := trace_le h hβ hN hsmall hκ
  have hint : ∫ X, wr11b_logW q μ Ψ β N X ∂(RN (wr11b_dk q) μ Ψ β N) =
      -(β / 2) * ∫ X, ‖wr11b_Sstat μ Ψ X - Real.sqrt N • Xibar (wr11b_dk q) μ Ψ β N‖ ^ 2
        ∂(RN (wr11b_dk q) μ Ψ β N) := by
    simp_rw [wr11b_logW_eq]
    rw [integral_const_mul]
    rfl
  have : -(4 * β * k 0) ≤ ∫ X, wr11b_logW q μ Ψ β N X ∂(RN (wr11b_dk q) μ Ψ β N) := by
    rw [hint]
    nlinarith
  exact (Real.le_log_iff_exp_le hpos).1 (this.trans hJ)

/-- **`A:eq:bounded-transfer`, pointwise**: the density `e^{ψ}/E_{R_N}[e^{ψ}]` is `≤ e^{4β k(0)}`. -/
theorem wr11b_density_le (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N)
    (hsmall : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : wr11b_KappaSmall β a)
    (X : Fin N → Euc d) :
    Real.exp (wr11b_logW q μ Ψ β N X) /
        ∫ Y, Real.exp (wr11b_logW q μ Ψ β N Y) ∂(RN (wr11b_dk q) μ Ψ β N) ≤
      Real.exp (4 * β * k 0) := by
  have hlow := wr11b_exp_le_integral_exp_logW h hβ hN hsmall hκ
  have hpos : 0 < Real.exp (-(4 * β * k 0)) := Real.exp_pos _
  have h1 : Real.exp (wr11b_logW q μ Ψ β N X) ≤ 1 := Real.exp_le_one_iff.2 (wr11b_logW_nonpos hβ X)
  rw [div_le_iff₀ (hpos.trans_le hlow)]
  calc Real.exp (wr11b_logW q μ Ψ β N X) ≤ 1 := h1
    _ = Real.exp (4 * β * k 0) * Real.exp (-(4 * β * k 0)) := by rw [← Real.exp_add]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le

/-- **`A:eq:bounded-transfer`** (`dQ/dR_N ≤ C`), `C = e^{4β k(0)}`; `Q_{N,β}(μ)` is the modulated Gibbs
measure of the kernel `g = q + k` (off the origin).  Hypotheses: `hsmall : ‖t_N·Ξ‖_∞ ≤ 1` and `hκ` (smallness
of `β a`); both hold for `N ≥ N0` uniformly in `ρ ≤ M` (`euc_Q_le_smul_RN`). -/
theorem Q_le_smul_RN (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N)
    (hsmall : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : wr11b_KappaSmall β a) :
    HRS.Whole.modulatedGibbs g N β μ ≤
      ENNReal.ofReal (Real.exp (4 * β * k 0)) • RN (wr11b_dk q) μ Ψ β N := by
  haveI := wr11b_isProb_RN h hβ.le hN
  have hQ : HRS.Whole.modulatedGibbs g N β μ = (RN (wr11b_dk q) μ Ψ β N).withDensity
      (fun X => ENNReal.ofReal (Real.exp (wr11b_logW q μ Ψ β N X) /
        ∫ Y, Real.exp (wr11b_logW q μ Ψ β N Y) ∂(RN (wr11b_dk q) μ Ψ β N))) :=
    h.Q_eq_RN_tilted hβ hN
  rw [hQ]
  intro s
  rw [withDensity_apply' _ s, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in s, ENNReal.ofReal (Real.exp (wr11b_logW q μ Ψ β N x) /
        ∫ Y, Real.exp (wr11b_logW q μ Ψ β N Y) ∂(RN (wr11b_dk q) μ Ψ β N)) ∂(RN (wr11b_dk q) μ Ψ β N)
      ≤ ∫⁻ _x in s, ENNReal.ofReal (Real.exp (4 * β * k 0)) ∂(RN (wr11b_dk q) μ Ψ β N) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (wr11b_density_le h hβ hN hsmall hκ x)
    _ = _ := by rw [setLIntegral_const]

theorem wr11b_isProb_Q (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N) :
    IsProbabilityMeasure (HRS.Whole.modulatedGibbs g N β μ) := by
  haveI := wr11b_isProb_RN h hβ.le hN
  rw [h.Q_eq_RN_tilted hβ hN]
  exact isProbabilityMeasure_tilted (wr11b_integrable_exp_logW h hβ)

/-- Real form of the variance transfer, for `F ∈ L²(R_N)`. -/
theorem wr11b_variance_transfer_real (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N)
    (hsmall : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : wr11b_KappaSmall β a)
    (F : (Fin N → Euc d) → ℝ) (hF : MemLp F 2 (RN (wr11b_dk q) μ Ψ β N)) :
    variance F (HRS.Whole.modulatedGibbs g N β μ) ≤
      Real.exp (4 * β * k 0) * variance F (RN (wr11b_dk q) μ Ψ β N) := by
  haveI := wr11b_isProb_RN h hβ.le hN
  haveI hQp := wr11b_isProb_Q h hβ hN
  have hQ := h.Q_eq_RN_tilted hβ hN
  have hle := Q_le_smul_RN h hβ hN hsmall hκ
  set P := RN (wr11b_dk q) μ Ψ β N with hP
  set Q := HRS.Whole.modulatedGibbs g N β μ with hQdef
  set a₀ := ∫ X, F X ∂P with ha
  have hac : Q ≪ P := by rw [hQ]; exact tilted_absolutelyContinuous _ _
  have hFQ : AEStronglyMeasurable F Q := hF.aestronglyMeasurable.mono_ac hac
  have h1 : variance F Q = variance (fun X => F X + (-a₀)) Q := (variance_add_const hFQ _).symm
  have h2 : variance (fun X => F X + (-a₀)) Q ≤ ∫ X, (F X + (-a₀)) ^ 2 ∂Q := by
    have := variance_le_expectation_sq (μ := Q) (X := fun X => F X + (-a₀))
      (hFQ.add aestronglyMeasurable_const)
    simpa using this
  have hsq : Integrable (fun X => (F X + (-a₀)) ^ 2) P := by
    have := (hF.sub (memLp_const a₀)).integrable_sq
    simpa [sub_eq_add_neg] using this
  have h3 : ∫ X, (F X + (-a₀)) ^ 2 ∂Q ≤ Real.exp (4 * β * k 0) * ∫ X, (F X + (-a₀)) ^ 2 ∂P := by
    have hsq' : Integrable (fun X => (F X + (-a₀)) ^ 2)
        (ENNReal.ofReal (Real.exp (4 * β * k 0)) • P) :=
      hsq.smul_measure ENNReal.ofReal_ne_top
    calc ∫ X, (F X + (-a₀)) ^ 2 ∂Q
        ≤ ∫ X, (F X + (-a₀)) ^ 2 ∂(ENNReal.ofReal (Real.exp (4 * β * k 0)) • P) :=
          integral_mono_measure hle (Eventually.of_forall fun X => sq_nonneg _) hsq'
      _ = _ := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have h4 : ∫ X, (F X + (-a₀)) ^ 2 ∂P = variance F P := by
    rw [variance_eq_integral hF.aemeasurable]
    simp [sub_eq_add_neg, ha]
  rw [h1]
  refine h2.trans (h3.trans ?_)
  rw [h4]

/-- **`A:eq:variance-transfer`**: `Var_Q(F) ≤ e^{4β k(0)} Var_{R_N}(F)` (extended-real variances, so that no
integrability hypothesis on `F` is needed; `F` only has to be a.e. strongly measurable for `R_N`). -/
theorem variance_transfer (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N)
    (hsmall : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : wr11b_KappaSmall β a)
    (F : (Fin N → Euc d) → ℝ) (hF : AEStronglyMeasurable F (RN (wr11b_dk q) μ Ψ β N)) :
    evariance F (HRS.Whole.modulatedGibbs g N β μ) ≤
      ENNReal.ofReal (Real.exp (4 * β * k 0)) * evariance F (RN (wr11b_dk q) μ Ψ β N) := by
  haveI := wr11b_isProb_RN h hβ.le hN
  haveI hQp := wr11b_isProb_Q h hβ hN
  by_cases hmem : MemLp F 2 (RN (wr11b_dk q) μ Ψ β N)
  · have hle := Q_le_smul_RN h hβ hN hsmall hκ
    have hmemQ : MemLp F 2 (HRS.Whole.modulatedGibbs g N β μ) :=
      (hmem.smul_measure ENNReal.ofReal_ne_top).mono_measure hle
    rw [← ofReal_variance hmem, ← ofReal_variance hmemQ,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (wr11b_variance_transfer_real h hβ hN hsmall hκ F hmem)
  · have htop : evariance F (RN (wr11b_dk q) μ Ψ β N) = ⊤ := by
      by_contra hne
      exact hmem ((evariance_lt_top_iff_memLp hF).1 (lt_top_iff_ne_top.2 hne))
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne']
    exact le_top

/-- **Linear statistics under `Q`** (conjunct 2 of the frozen statement, for `N ≥ N0`): transfer + Wu,
`Var_Q(∑_i f(x_i)) ≤ e^{4β k(0)} · 2N · Var_{π_N^R}(f)`, `π_N^R` the one-point marginal of `R_N`. -/
theorem linear_variance_Q (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N)
    (hsmall : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : wr11b_KappaSmall β a)
    [NeZero N] (f : Euc d → ℝ) (hf : Measurable f) :
    evariance (fun X : Fin N → Euc d => ∑ i, f (X i)) (HRS.Whole.modulatedGibbs g N β μ) ≤
      ENNReal.ofReal (Real.exp (4 * β * k 0)) *
        (2 * N * evariance f ((RN (wr11b_dk q) μ Ψ β N).map (fun X => X 0))) := by
  have hF : Measurable fun X : Fin N → Euc d => ∑ i, f (X i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  exact (variance_transfer h hβ hN hsmall hκ _ hF.aestronglyMeasurable).trans
    (mul_le_mul' le_rfl (wr11b_evar_sum_le h hβ.le hN hsmall hκ f hf))

end Main

/-! ### The Riesz kernel: uniform constants -/

section Concrete

open HRS.Whole HRS.MS.Psd

/-- The row bound `M ∫ q_τ = M · c_q τ^{(d-s)/2}` of the weak kernel `q_τ (x - y)` for `μ = ρ dx`, `ρ ≤ M`. -/
def wr11b_aRow (d : ℕ) (s M τ : ℝ) : ℝ :=
  M * (aDS d s / (((d : ℝ) - s) / 2) * τ ^ (((d : ℝ) - s) / 2))

theorem wr11b_kappaSmall_of_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / (16 * Real.exp 3)) :
    4 * Real.exp (2 * x + 1) * x ≤ 1 / 2 := by
  have he : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hx1 : x ≤ 1 / 16 := by
    refine hx.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h1 : Real.exp (2 * x + 1) ≤ Real.exp 3 := Real.exp_le_exp.2 (by linarith)
  calc 4 * Real.exp (2 * x + 1) * x ≤ 4 * Real.exp 3 * (1 / (16 * Real.exp 3)) := by
        gcongr
    _ = 1 / 4 := by field_simp; norm_num
    _ ≤ 1 / 2 := by norm_num

/-- **Uniform setup for the Riesz kernel.**  For `0 < s < d` and any `βp, M` there are `τ > 0` and `N0` such that,
for every probability density `ρ ≤ M`, `β ∈ (0, βp]` and `N ≥ N0`, the data `(μ = ρ dx, q = q_τ, k = k_τ,
g = HRS.Whole.rieszKernel d s, Ψ = featMap d s τ)` satisfy `TransferHyp`, the smallness `‖t_N·Ξ‖_∞ ≤ 1`
(from `euc_field_small` of WR-12a and `tN_norm_le`) and the Wu smallness `hκ`. -/
theorem euc_transfer_setup (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (βp M : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N0 ≤ N →
        TransferHyp (HRS.Whole.withDensityReal ρ) (wr11b_aRow d s M τ) (qTau d s τ) (kTau d s τ)
          (HRS.Whole.rieszKernel d s) (featMap d s τ) ∧
        (∀ x : Euc d, |inner ℝ (tN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ)
          (featMap d s τ) β N) (Xi (HRS.Whole.withDensityReal ρ) (featMap d s τ) x)| ≤ 1) ∧
        wr11b_KappaSmall β (wr11b_aRow d s M τ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set α : ℝ := ((d : ℝ) - s) / 2 with hαdef
  have hα : 0 < α := by rw [hαdef]; linarith
  set c : ℝ := aDS d s / α with hcdef
  have hc0 : 0 ≤ c := wr12_cq_nonneg hs hsd
  set ε : ℝ := 1 / (16 * Real.exp 3) with hεdef
  have hε : 0 < ε := by positivity
  set X : ℝ := max βp 0 * max M 0 * c with hXdef
  have hX : 0 ≤ X := by positivity
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = (ε / (X + 1)) ^ (1 / α) := ⟨_, rfl⟩
  have hτ : 0 < τ := by rw [hτdef]; exact Real.rpow_pos_of_pos (by positivity) _
  have hτα : τ ^ α = ε / (X + 1) := by
    rw [hτdef, ← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one]
  have hτα0 : 0 ≤ τ ^ α := (Real.rpow_pos_of_pos hτ α).le
  obtain ⟨N0, hN0, hfs⟩ := euc_field_small (H := Lp (EuclideanSpace ℝ (Fin 2)) 2 (featMeasure d s τ))
    hd hs hsd βp M (Real.sqrt (kTau d s τ 0))
  haveI := featMap_separableSpace (d := d) hs hτ
  refine ⟨τ, hτ, N0, hN0, fun ρ hρ hM β hβ hβp N hN => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have ha : 0 ≤ wr11b_aRow d s M τ := by
    unfold wr11b_aRow; rw [← hαdef, ← hcdef]; positivity
  have hT : TransferHyp (HRS.Whole.withDensityReal ρ) (wr11b_aRow d s M τ) (qTau d s τ) (kTau d s τ)
      (HRS.Whole.rieszKernel d s) (featMap d s τ) :=
    ⟨wr12_qTau_weak hd hs hsd hτ hρ hM, ha, featMap_hyp hs hτ,
      fun x hx => riesz_heat_split hs hτ hx, wr12_atomless hd ρ⟩
  refine ⟨hT, ?_, ?_⟩
  · have hN' : 0 < N := by omega
    intro x
    exact hfs τ hτ ρ hρ hM β hβ hβp N hN (featMap d s τ) hT.calFeat _
      (tN_norm_le hT.weak hT.calFeat hβ hN') x
  · -- `β a ≤ ε`
    have hβa : β * wr11b_aRow d s M τ ≤ ε := by
      unfold wr11b_aRow
      rw [← hαdef, ← hcdef]
      have h1 : β * (M * (c * τ ^ α)) ≤ max βp 0 * (max M 0 * (c * τ ^ α)) := by
        have hb : β ≤ max βp 0 := hβp.trans (le_max_left _ _)
        have hm : M ≤ max M 0 := le_max_left _ _
        have hcτ : 0 ≤ c * τ ^ α := mul_nonneg hc0 hτα0
        gcongr
      calc β * (M * (c * τ ^ α)) ≤ max βp 0 * (max M 0 * (c * τ ^ α)) := h1
        _ = X * τ ^ α := by rw [hXdef]; ring
        _ = X * (ε / (X + 1)) := by rw [hτα]
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            nlinarith
    have hβa0 : 0 ≤ β * wr11b_aRow d s M τ := mul_nonneg hβ.le ha
    exact wr11b_kappaSmall_of_le hβa0 hβa

/-- **Transfer for the Riesz kernel** (`euc-transfer`, `euc-feature-trace`): for `0 < s < d` and `βp, M` there are
`τ > 0` and `N0` such that for every probability density `ρ ≤ M`, `β ∈ (0, βp]`, `N ≥ N0`, with
`μ = ρ dx`, `R_N = RN (q_τ(x-y)) μ (featMap d s τ) β N`, `k₀ = k_τ(0)`:
the trace bound `∫ ‖S_N - √N Ξ̄_N‖² dR_N ≤ 8 k₀`, the density bound `Q ≤ e^{4 β k₀} R_N`
for `Q = HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β μ`, and the variance transfer
`evariance F Q ≤ e^{4 β k₀} evariance F R_N`. -/
theorem euc_transfer (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (βp M : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N0 ≤ N →
        (∫ X, ‖wr11b_Sstat (HRS.Whole.withDensityReal ρ) (featMap d s τ) X - Real.sqrt N •
            Xibar (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) (featMap d s τ) β N‖ ^ 2
          ∂(RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) (featMap d s τ) β N)
          ≤ 8 * kTau d s τ 0) ∧
        HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (Real.exp (4 * β * kTau d s τ 0)) •
            RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) (featMap d s τ) β N ∧
        ∀ F : (Fin N → Euc d) → ℝ, AEStronglyMeasurable F
          (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) (featMap d s τ) β N) →
          evariance F (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
            ENNReal.ofReal (Real.exp (4 * β * kTau d s τ 0)) *
              evariance F
                (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) (featMap d s τ) β N) := by
  obtain ⟨τ, hτ, N0, hN0, hset⟩ := euc_transfer_setup hd hs hsd βp M
  haveI := featMap_separableSpace (d := d) hs hτ
  refine ⟨τ, hτ, N0, hN0, fun ρ hρ hM β hβ hβp N hN => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  obtain ⟨hT, hsmall, hκ⟩ := hset ρ hρ hM β hβ hβp N hN
  have hN' : 0 < N := by omega
  exact ⟨trace_le hT hβ hN' hsmall hκ, Q_le_smul_RN hT hβ hN' hsmall hκ,
    fun F hF => variance_transfer hT hβ hN' hsmall hκ F hF⟩

/-- **Linear statistics for the Riesz kernel** (conjunct 2 of `euc_static`, `N ≥ N0`): with the data of
`euc_transfer`, `Var_Q(∑_i f(x_i)) ≤ e^{4β k₀} · 2N · Var_{π^R_N}(f)` for every measurable `f`. -/
theorem euc_linear_variance (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (βp M : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ (N : ℕ) [NeZero N], N0 ≤ N → ∀ f : Euc d → ℝ, Measurable f →
        evariance (fun X : Fin N → Euc d => ∑ i, f (X i))
            (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (Real.exp (4 * β * kTau d s τ 0)) *
            (2 * N * evariance f
              ((RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ)
                (featMap d s τ) β N).map (fun X => X 0))) := by
  obtain ⟨τ, hτ, N0, hN0, hset⟩ := euc_transfer_setup hd hs hsd βp M
  haveI := featMap_separableSpace (d := d) hs hτ
  refine ⟨τ, hτ, N0, hN0, fun ρ hρ hM β hβ hβp N _ hN f hf => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  obtain ⟨hT, hsmall, hκ⟩ := hset ρ hρ hM β hβ hβp N hN
  have hN' : 0 < N := by omega
  exact linear_variance_Q hT hβ hN' hsmall hκ f hf

end Concrete

end HRS.MS.Wr
