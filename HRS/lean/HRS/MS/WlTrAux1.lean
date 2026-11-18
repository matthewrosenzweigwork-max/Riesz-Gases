import HRS.MS.WlCalAux1
import HRS.MS.WrTr

/-!
# HRS.MS.WlTrAux1 -- calibrated transfer over an abstract reference measure (WL-5, part 1)

Packet WL-5 of `docs/WR_LOG_PLAN.md` (Step 7 of the proof of `r2_log_static`).  Infrastructure lemmas, not
manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl5_`.  Port of `HRS.MS.WrTr` / `WrTrAux1-2`
(`wr11b_*`) from the Euclidean weak reference `RN` to the abstract calibrated reference
`ν = wl4_RN (1/n) b μ Ψ P0` of `WlCalAux1` (`P0` an arbitrary probability measure on `Fin n → ℝ^d`,
`b = n λ`); nothing here mentions kernels or fields.

Setting.  `Ψ : ℝ^d → H` with `CalFeat Ψ B` (`H` a real Hilbert space, separable for the trace),
`t = wl4_tN (1/n) b μ Ψ P0`, `ν = P0` tilted by `∑ ⟪t, Ξ(x_i)⟫`, `Ξ̄ = E_R μ_n(Ξ)`,
`D = S_n - √n Ξ̄` (`wl5_D`), `S_n = √n μ_n(Ξ)` (`wr11b_Sstat`).  The only analytic input on `ν` is Wu's
inequality as a hypothesis `hWu : Var_R(∑ f(x_i)) ≤ 2 n Var_{ν^{(1)}}(f)` (it is supplied by `WlTrAux2`).

Exports (names in `HRS.MS.Wl`):
* `wl5_trace_le`: `∫ ‖S_n - √n Ξ̄‖² dR ≤ 8 B²` (`trace` bound, trace constant `8 k0` for `B² = k0`);
* `wl5_P_eq_RN_tilted`: if `P = P0` tilted by `-(b/2)‖S_n‖²` then `P = ν` tilted by `-(b/2)‖D‖²`
  (completion of the square, `t = -b Ξ̄`);
* `wl5_P_le_smul`: `P ≤ e^{4 b B²} • ν` (`A:eq:bounded-transfer`);
* `wl5_variance_transfer`: `evariance F P ≤ e^{4 b B²} * evariance F ν` for every `F` a.e. strongly
  measurable for `ν` (no integrability hypothesis);
* `wl5_isProb_P`.

Adjustment with respect to the plan (documented, harmless): the statements are over the abstract `P0` and use
`B` (`CalFeat Ψ B`) with `B² = k0` in the application (`wl_psi_calFeat`: `B = √(k0 M)`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.MS.Wr

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `D = S_n - √n Ξ̄`, `Ξ̄ = E_R μ_n(Ξ)`. -/
def wl5_D (μ : Measure (Euc d)) (Ψ : Euc d → H) {n : ℕ} (ν : Measure (Fin n → Euc d))
    (X : Fin n → Euc d) : H :=
  wr11b_Sstat μ Ψ X - Real.sqrt n • ∫ Y, empXi μ Ψ Y ∂ν

/-- The log-density `-(b/2) ‖D‖²` of `P` against `ν`. -/
def wl5_logW (b : ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) {n : ℕ} (ν : Measure (Fin n → Euc d))
    (X : Fin n → Euc d) : ℝ :=
  -(b / 2) * ‖wl5_D μ Ψ ν X‖ ^ 2

section Generic

variable [CompleteSpace H] {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Ψ : Euc d → H} {B : ℝ}
  {n : ℕ} {ν : Measure (Fin n → Euc d)}

lemma wl5_norm_empXi_le (hΨ : CalFeat Ψ B) (hn : 0 < n) (X : Fin n → Euc d) :
    ‖empXi μ Ψ X‖ ≤ 2 * B := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [wr11_empXi_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have : ‖wr11_S μ Ψ X‖ ≤ n * (2 * B) := (hΨ.wr11_bdd (N := n)).bound X
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn']
  linarith

lemma wl5_norm_Xibar_le [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hn : 0 < n) :
    ‖∫ Y, empXi μ Ψ Y ∂ν‖ ≤ 2 * B := by
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := empXi μ Ψ (N := n)) (C := 2 * B)
    (Eventually.of_forall fun X => wl5_norm_empXi_le hΨ hn X)
  simpa using this

lemma wl5_norm_D_le [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hn : 0 < n) (X : Fin n → Euc d) :
    ‖wl5_D μ Ψ ν X‖ ≤ Real.sqrt n * (4 * B) := by
  unfold wl5_D wr11b_Sstat
  calc ‖Real.sqrt n • empXi μ Ψ X - Real.sqrt n • ∫ Y, empXi μ Ψ Y ∂ν‖
      ≤ ‖Real.sqrt n • empXi μ Ψ X‖ + ‖Real.sqrt n • ∫ Y, empXi μ Ψ Y ∂ν‖ := norm_sub_le _ _
    _ = Real.sqrt n * ‖empXi μ Ψ X‖ + Real.sqrt n * ‖∫ Y, empXi μ Ψ Y ∂ν‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt n * (2 * B) + Real.sqrt n * (2 * B) := by
        gcongr
        · exact wl5_norm_empXi_le hΨ hn X
        · exact wl5_norm_Xibar_le hΨ hn
    _ = _ := by ring

lemma wl5_continuous_empXi (hΨ : CalFeat Ψ B) : Continuous (empXi μ Ψ (N := n)) := by
  have e : empXi μ Ψ = fun X : Fin n → Euc d => (1 / (n : ℝ)) • wr11_S μ Ψ X := rfl
  rw [e]
  exact hΨ.continuous_S.const_smul _

lemma wl5_continuous_Sstat (hΨ : CalFeat Ψ B) : Continuous (wr11b_Sstat μ Ψ (N := n)) :=
  (wl5_continuous_empXi hΨ).const_smul _

lemma wl5_continuous_D (hΨ : CalFeat Ψ B) : Continuous (wl5_D μ Ψ ν) :=
  (wl5_continuous_Sstat hΨ).sub continuous_const

lemma wl5_continuous_inner_Xi (hΨ : CalFeat Ψ B) (t : H) :
    Continuous (fun x => inner ℝ t (Xi μ Ψ x)) :=
  continuous_const.inner hΨ.continuous_Xi

/-- Wu's inequality in real form for bounded `f` (from the `evariance` hypothesis). -/
lemma wl5_var_sum_le [NeZero n] [IsProbabilityMeasure ν]
    (hWu : ∀ f : Euc d → ℝ, Measurable f →
      evariance (fun X : Fin n → Euc d => ∑ i, f (X i)) ν ≤
        2 * n * evariance f (ν.map (fun X => X 0)))
    (f : Euc d → ℝ) (hf : Measurable f) (Bf : ℝ) (hB : ∀ x, |f x| ≤ Bf) :
    variance (fun X : Fin n → Euc d => ∑ i, f (X i)) ν ≤
      2 * n * variance f (ν.map (fun X => X 0)) := by
  have key := hWu f hf
  have hF : Measurable fun X : Fin n → Euc d => ∑ i, f (X i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have hf2 : MemLp f 2 (ν.map (fun X => X 0)) :=
    MemLp.of_bound hf.aestronglyMeasurable Bf
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hF2 : MemLp (fun X : Fin n → Euc d => ∑ i, f (X i)) 2 ν :=
    MemLp.of_bound hF.aestronglyMeasurable (n * Bf)
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        calc |∑ i, f (X i)| ≤ ∑ i, |f (X i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, Bf := Finset.sum_le_sum fun i _ => hB _
          _ = n * Bf := by simp)
  rw [← ofReal_variance hf2, ← ofReal_variance hF2] at key
  have h0 : 0 ≤ 2 * (n : ℝ) * variance f (ν.map (fun X => X 0)) :=
    mul_nonneg (by positivity) (variance_nonneg _ _)
  have e : (2 : ℝ≥0∞) * n * ENNReal.ofReal (variance f (ν.map (fun X => X 0))) =
      ENNReal.ofReal (2 * n * variance f (ν.map (fun X => X 0))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [e, ENNReal.ofReal_le_ofReal_iff h0] at key
  exact key

/-- For every `v : H`: `E_R ⟪v, D⟫² ≤ 2 E_R ⟪v, Ξ(x_1)⟫²`. -/
lemma wl5_inner_sq_le [NeZero n] [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hn : 0 < n)
    (hWu : ∀ f : Euc d → ℝ, Measurable f →
      evariance (fun X : Fin n → Euc d => ∑ i, f (X i)) ν ≤
        2 * n * evariance f (ν.map (fun X => X 0))) (v : H) :
    ∫ X, (inner ℝ v (wl5_D μ Ψ ν X)) ^ 2 ∂ν ≤
      2 * ∫ X, (inner ℝ v (Xi μ Ψ (X 0))) ^ 2 ∂ν := by
  set f : Euc d → ℝ := fun x => inner ℝ v (Xi μ Ψ x) with hf
  have hfm : Measurable f := (wl5_continuous_inner_Xi hΨ v).measurable
  have hfb : ∀ x, |f x| ≤ ‖v‖ * (2 * B) := fun x =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hΨ.norm_Xi_le x) (norm_nonneg _))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set G : (Fin n → Euc d) → ℝ := fun X => ∑ i, f (X i) with hG
  have hGm : Measurable G := Finset.measurable_sum _ fun j _ => hfm.comp (measurable_pi_apply j)
  have hE : ∀ X, inner ℝ v (wl5_D μ Ψ ν X) =
      Real.sqrt n * ((1 / (n : ℝ)) * G X - ∫ Y, (1 / (n : ℝ)) * G Y ∂ν) := by
    intro X
    have hemp : ∀ Y : Fin n → Euc d, inner ℝ v (empXi μ Ψ Y) = (1 / (n : ℝ)) * G Y := by
      intro Y
      unfold empXi
      rw [real_inner_smul_right, inner_sum]
    have e1 : inner ℝ v (∫ Y, empXi μ Ψ Y ∂ν) = ∫ Y, (1 / (n : ℝ)) * G Y ∂ν := by
      rw [← integral_inner (hΨ.integrable_empXi ν) v]
      exact integral_congr_ae (Eventually.of_forall hemp)
    unfold wl5_D wr11b_Sstat
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, hemp, e1]
    ring
  have hvar := wl5_var_sum_le hWu f hfm _ hfb
  have hint1 : ∫ X, (inner ℝ v (wl5_D μ Ψ ν X)) ^ 2 ∂ν =
      n * variance (fun X => (1 / (n : ℝ)) * G X) ν := by
    rw [variance_eq_integral ((hGm.const_mul _).aemeasurable)]
    simp_rw [hE, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [integral_const_mul]
  have hvar2 : variance (fun X => (1 / (n : ℝ)) * G X) ν = (1 / (n : ℝ)) ^ 2 * variance G ν :=
    variance_const_mul _ _ _
  have hπ : variance f (ν.map (fun X => X 0)) ≤ ∫ X, (f (X 0)) ^ 2 ∂ν := by
    have := variance_le_expectation_sq (μ := ν.map (fun X : Fin n → Euc d => X 0)) (X := f)
      hfm.aestronglyMeasurable
    refine this.trans (le_of_eq ?_)
    rw [integral_map (measurable_pi_apply 0).aemeasurable (hfm.pow_const 2).aestronglyMeasurable]
    rfl
  rw [hint1, hvar2]
  have hv0 : 0 ≤ variance f (ν.map (fun X => X 0)) := variance_nonneg _ _
  calc (n : ℝ) * ((1 / (n : ℝ)) ^ 2 * variance G ν) ≤
      (n : ℝ) * ((1 / (n : ℝ)) ^ 2 * (2 * n * variance f (ν.map (fun X => X 0)))) := by
        gcongr
    _ = 2 * variance f (ν.map (fun X => X 0)) := by field_simp
    _ ≤ 2 * ∫ X, (f (X 0)) ^ 2 ∂ν := by linarith

/-- The trace over a finite orthonormal family: `E_R ∑_j ⟪e_j, D⟫² ≤ 8 B²`. -/
lemma wl5_fin_trace [NeZero n] [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hn : 0 < n)
    (hWu : ∀ f : Euc d → ℝ, Measurable f →
      evariance (fun X : Fin n → Euc d => ∑ i, f (X i)) ν ≤
        2 * n * evariance f (ν.map (fun X => X 0)))
    {m : ℕ} (e : Fin m → H) (he : Orthonormal ℝ e) :
    ∫ X, ∑ j, (inner ℝ (e j) (wl5_D μ Ψ ν X)) ^ 2 ∂ν ≤ 8 * B ^ 2 := by
  have hDi : ∀ v : H, Integrable (fun X => (inner ℝ v (wl5_D μ Ψ ν X)) ^ 2) ν := fun v =>
    Integrable.of_bound
      (((continuous_const.inner (wl5_continuous_D hΨ)).pow 2).aestronglyMeasurable)
      ((‖v‖ * (Real.sqrt n * (4 * B))) ^ 2) (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hx : |inner ℝ v (wl5_D μ Ψ ν X)| ≤ ‖v‖ * (Real.sqrt n * (4 * B)) :=
          (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (wl5_norm_D_le hΨ hn X) (norm_nonneg _))
        exact sq_le_sq' (by linarith [abs_le.1 hx]) (by linarith [abs_le.1 hx]))
  have hgi : ∀ v : H, Integrable (fun X : Fin n → Euc d => (inner ℝ v (Xi μ Ψ (X 0))) ^ 2) ν :=
    fun v => Integrable.of_bound
      (((continuous_const.inner (hΨ.continuous_Xi.comp (continuous_apply 0))).pow 2).aestronglyMeasurable)
      ((‖v‖ * (2 * B)) ^ 2) (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hx : |inner ℝ v (Xi μ Ψ (X 0))| ≤ ‖v‖ * (2 * B) :=
          (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (hΨ.norm_Xi_le _) (norm_nonneg _))
        exact sq_le_sq' (by linarith [abs_le.1 hx]) (by linarith [abs_le.1 hx]))
  rw [integral_finsetSum _ fun j _ => hDi (e j)]
  have hbess : ∀ X : Fin n → Euc d,
      ∑ j, (inner ℝ (e j) (Xi μ Ψ (X 0))) ^ 2 ≤ 4 * B ^ 2 := fun X => by
    have h1 := he.sum_inner_products_le (Xi μ Ψ (X 0)) (s := Finset.univ)
    simp only [Real.norm_eq_abs, sq_abs] at h1
    refine h1.trans ?_
    have h2 := hΨ.norm_Xi_le (μ := μ) (X 0)
    have h3 : ‖Xi μ Ψ (X 0)‖ ^ 2 ≤ (2 * B) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc ‖Xi μ Ψ (X 0)‖ ^ 2 ≤ (2 * B) ^ 2 := h3
      _ = 4 * B ^ 2 := by ring
  calc ∑ j, ∫ X, (inner ℝ (e j) (wl5_D μ Ψ ν X)) ^ 2 ∂ν
      ≤ ∑ j, 2 * ∫ X, (inner ℝ (e j) (Xi μ Ψ (X 0))) ^ 2 ∂ν :=
        Finset.sum_le_sum fun j _ => wl5_inner_sq_le hΨ hn hWu (e j)
    _ = 2 * ∫ X, ∑ j, (inner ℝ (e j) (Xi μ Ψ (X 0))) ^ 2 ∂ν := by
        rw [← Finset.mul_sum, ← integral_finsetSum _ fun j _ => hgi (e j)]
    _ ≤ 2 * ∫ _X, 4 * B ^ 2 ∂ν := by
        exact mul_le_mul_of_nonneg_left (integral_mono (integrable_finsetSum _ fun j _ => hgi (e j))
          (integrable_const _) hbess) (by norm_num)
    _ = 8 * B ^ 2 := by simp; ring

/-- **The trace bound**: `∫ ‖S_n - √n Ξ̄‖² dR ≤ 8 B²`. -/
theorem wl5_trace_le [TopologicalSpace.SeparableSpace H] [NeZero n] [IsProbabilityMeasure ν]
    (hΨ : CalFeat Ψ B) (hn : 0 < n)
    (hWu : ∀ f : Euc d → ℝ, Measurable f →
      evariance (fun X : Fin n → Euc d => ∑ i, f (X i)) ν ≤
        2 * n * evariance f (ν.map (fun X => X 0))) :
    ∫ X, ‖wl5_D μ Ψ ν X‖ ^ 2 ∂ν ≤ 8 * B ^ 2 := by
  exact wr11b_trace_limit ν (wl5_continuous_D hΨ).stronglyMeasurable
    (wl5_norm_D_le hΨ hn) (fun m e he => wl5_fin_trace hΨ hn hWu e he)

end Generic

section Transfer

variable [CompleteSpace H] {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Ψ : Euc d → H} {B : ℝ}
  {n : ℕ} {ν : Measure (Fin n → Euc d)} {b : ℝ}

lemma wl5_logW_nonpos (hb : 0 < b) (X : Fin n → Euc d) : wl5_logW b μ Ψ ν X ≤ 0 := by
  unfold wl5_logW
  have : 0 ≤ (b / 2) * ‖wl5_D μ Ψ ν X‖ ^ 2 := by positivity
  linarith

lemma wl5_continuous_logW (hΨ : CalFeat Ψ B) :
    Continuous (wl5_logW b μ Ψ ν) :=
  continuous_const.mul ((wl5_continuous_D hΨ).norm.pow 2)

lemma wl5_integrable_logW [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hb : 0 < b) (hn : 0 < n)
    {P : Measure (Fin n → Euc d)} [IsFiniteMeasure P] : Integrable (wl5_logW b μ Ψ ν) P := by
  set C := Real.sqrt n * (4 * B) with hC
  refine Integrable.of_bound (wl5_continuous_logW hΨ).aestronglyMeasurable ((b / 2) * C ^ 2)
    (Eventually.of_forall fun X => ?_)
  have h1 : ‖wl5_D μ Ψ ν X‖ ≤ Real.sqrt n * (4 * B) := wl5_norm_D_le hΨ hn X
  have h0 := norm_nonneg (wl5_D μ Ψ ν X)
  rw [Real.norm_eq_abs, wl5_logW, abs_of_nonpos (by
    have : 0 ≤ (b / 2) * ‖wl5_D μ Ψ ν X‖ ^ 2 := by positivity
    linarith)]
  have : ‖wl5_D μ Ψ ν X‖ ^ 2 ≤ C ^ 2 := by gcongr
  nlinarith

lemma wl5_integrable_exp_logW (hΨ : CalFeat Ψ B) (hb : 0 < b)
    {P : Measure (Fin n → Euc d)} [IsFiniteMeasure P] :
    Integrable (fun X => Real.exp (wl5_logW b μ Ψ ν X)) P :=
  Integrable.of_bound (Real.continuous_exp.comp (wl5_continuous_logW hΨ)).aestronglyMeasurable 1
    (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (wl5_logW_nonpos hb X))

/-- **Denominator bound** (Jensen + trace): `E_R[e^{-(b/2)‖D‖²}] ≥ e^{-4 b B²}`. -/
lemma wl5_exp_le_integral_exp_logW [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hb : 0 < b)
    (hn : 0 < n) (htr : ∫ X, ‖wl5_D μ Ψ ν X‖ ^ 2 ∂ν ≤ 8 * B ^ 2) :
    Real.exp (-(4 * b * B ^ 2)) ≤ ∫ X, Real.exp (wl5_logW b μ Ψ ν X) ∂ν := by
  have hi1 : Integrable (wl5_logW b μ Ψ ν) ν := wl5_integrable_logW hΨ hb hn
  have hi2 : Integrable (fun X => Real.exp (wl5_logW b μ Ψ ν X)) ν := wl5_integrable_exp_logW hΨ hb
  have hJ := wr11b_log_integral_exp_ge hi1 hi2
  have hpos := integral_exp_pos (μ := ν) (f := wl5_logW b μ Ψ ν) (wl5_integrable_exp_logW hΨ hb)
  have hint : ∫ X, wl5_logW b μ Ψ ν X ∂ν = -(b / 2) * ∫ X, ‖wl5_D μ Ψ ν X‖ ^ 2 ∂ν := by
    simp_rw [wl5_logW]
    rw [integral_const_mul]
  have : -(4 * b * B ^ 2) ≤ ∫ X, wl5_logW b μ Ψ ν X ∂ν := by
    rw [hint]
    nlinarith
  exact (Real.le_log_iff_exp_le hpos).1 (this.trans hJ)

/-- Pointwise: the density `e^{logW}/E_R[e^{logW}]` is `≤ e^{4 b B²}`. -/
lemma wl5_density_le [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hb : 0 < b) (hn : 0 < n)
    (htr : ∫ X, ‖wl5_D μ Ψ ν X‖ ^ 2 ∂ν ≤ 8 * B ^ 2) (X : Fin n → Euc d) :
    Real.exp (wl5_logW b μ Ψ ν X) / ∫ Y, Real.exp (wl5_logW b μ Ψ ν Y) ∂ν ≤
      Real.exp (4 * b * B ^ 2) := by
  have hlow := wl5_exp_le_integral_exp_logW hΨ hb hn htr
  have hpos : 0 < Real.exp (-(4 * b * B ^ 2)) := Real.exp_pos _
  have h1 : Real.exp (wl5_logW b μ Ψ ν X) ≤ 1 := Real.exp_le_one_iff.2 (wl5_logW_nonpos hb X)
  rw [div_le_iff₀ (hpos.trans_le hlow)]
  calc Real.exp (wl5_logW b μ Ψ ν X) ≤ 1 := h1
    _ = Real.exp (4 * b * B ^ 2) * Real.exp (-(4 * b * B ^ 2)) := by rw [← Real.exp_add]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le

/-- `ν` tilted by `logW` is dominated by `e^{4 b B²} ν`. -/
theorem wl5_tilted_le_smul [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hb : 0 < b) (hn : 0 < n)
    (htr : ∫ X, ‖wl5_D μ Ψ ν X‖ ^ 2 ∂ν ≤ 8 * B ^ 2) :
    ν.tilted (wl5_logW b μ Ψ ν) ≤ ENNReal.ofReal (Real.exp (4 * b * B ^ 2)) • ν := by
  rw [Measure.le_iff]
  intro s hs
  rw [tilted_apply' _ _ hs, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in s, ENNReal.ofReal (Real.exp (wl5_logW b μ Ψ ν x) /
        ∫ Y, Real.exp (wl5_logW b μ Ψ ν Y) ∂ν) ∂ν
      ≤ ∫⁻ _x in s, ENNReal.ofReal (Real.exp (4 * b * B ^ 2)) ∂ν :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (wl5_density_le hΨ hb hn htr x)
    _ = _ := by rw [setLIntegral_const]

theorem wl5_isProb_tilted [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hb : 0 < b) :
    IsProbabilityMeasure (ν.tilted (wl5_logW b μ Ψ ν)) :=
  isProbabilityMeasure_tilted (wl5_integrable_exp_logW hΨ hb)

/-- Real form of the variance transfer for `F ∈ L²(ν)`. -/
lemma wl5_variance_transfer_real [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hb : 0 < b)
    (hn : 0 < n) (htr : ∫ X, ‖wl5_D μ Ψ ν X‖ ^ 2 ∂ν ≤ 8 * B ^ 2)
    (F : (Fin n → Euc d) → ℝ) (hF : MemLp F 2 ν) :
    variance F (ν.tilted (wl5_logW b μ Ψ ν)) ≤
      Real.exp (4 * b * B ^ 2) * variance F ν := by
  haveI hQp : IsProbabilityMeasure (ν.tilted (wl5_logW b μ Ψ ν)) := wl5_isProb_tilted hΨ hb
  have hle := wl5_tilted_le_smul hΨ hb hn htr
  set Q := ν.tilted (wl5_logW b μ Ψ ν) with hQdef
  set a₀ := ∫ X, F X ∂ν with ha
  have hac : Q ≪ ν := tilted_absolutelyContinuous _ _
  have hFQ : AEStronglyMeasurable F Q := hF.aestronglyMeasurable.mono_ac hac
  have h1 : variance F Q = variance (fun X => F X + (-a₀)) Q := (variance_add_const hFQ _).symm
  have h2 : variance (fun X => F X + (-a₀)) Q ≤ ∫ X, (F X + (-a₀)) ^ 2 ∂Q := by
    have := variance_le_expectation_sq (μ := Q) (X := fun X => F X + (-a₀))
      (hFQ.add aestronglyMeasurable_const)
    simpa using this
  have hsq : Integrable (fun X => (F X + (-a₀)) ^ 2) ν := by
    have := (hF.sub (memLp_const a₀)).integrable_sq
    simpa [sub_eq_add_neg] using this
  have h3 : ∫ X, (F X + (-a₀)) ^ 2 ∂Q ≤ Real.exp (4 * b * B ^ 2) * ∫ X, (F X + (-a₀)) ^ 2 ∂ν := by
    have hsq' : Integrable (fun X => (F X + (-a₀)) ^ 2)
        (ENNReal.ofReal (Real.exp (4 * b * B ^ 2)) • ν) :=
      hsq.smul_measure ENNReal.ofReal_ne_top
    calc ∫ X, (F X + (-a₀)) ^ 2 ∂Q
        ≤ ∫ X, (F X + (-a₀)) ^ 2 ∂(ENNReal.ofReal (Real.exp (4 * b * B ^ 2)) • ν) :=
          integral_mono_measure hle (Eventually.of_forall fun X => sq_nonneg _) hsq'
      _ = _ := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have h4 : ∫ X, (F X + (-a₀)) ^ 2 ∂ν = variance F ν := by
    rw [variance_eq_integral hF.aemeasurable]
    simp [sub_eq_add_neg, ha]
  rw [h1]
  refine h2.trans (h3.trans ?_)
  rw [h4]

/-- **`A:eq:variance-transfer`** for the tilt of `ν`: `Var_Q(F) ≤ e^{4 b B²} Var_R(F)` (extended-real
variances). -/
theorem wl5_variance_transfer_tilted [IsProbabilityMeasure ν] (hΨ : CalFeat Ψ B) (hb : 0 < b)
    (hn : 0 < n) (htr : ∫ X, ‖wl5_D μ Ψ ν X‖ ^ 2 ∂ν ≤ 8 * B ^ 2)
    (F : (Fin n → Euc d) → ℝ) (hF : AEStronglyMeasurable F ν) :
    evariance F (ν.tilted (wl5_logW b μ Ψ ν)) ≤
      ENNReal.ofReal (Real.exp (4 * b * B ^ 2)) * evariance F ν := by
  haveI hQp : IsProbabilityMeasure (ν.tilted (wl5_logW b μ Ψ ν)) := wl5_isProb_tilted hΨ hb
  by_cases hmem : MemLp F 2 ν
  · have hle := wl5_tilted_le_smul hΨ hb hn htr
    have hmemQ : MemLp F 2 (ν.tilted (wl5_logW b μ Ψ ν)) :=
      (hmem.smul_measure ENNReal.ofReal_ne_top).mono_measure hle
    rw [← ofReal_variance hmem, ← ofReal_variance hmemQ,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (wl5_variance_transfer_real hΨ hb hn htr F hmem)
  · have htop : evariance F ν = ⊤ := by
      by_contra hne
      exact hmem ((evariance_lt_top_iff_memLp hF).1 (lt_top_iff_ne_top.2 hne))
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne']
    exact le_top

end Transfer

/-! ### The calibrated reference `ν = wl4_RN`: `P` is a tilt of `ν` -/

section Calibrated

variable [CompleteSpace H] {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Ψ : Euc d → H} {B : ℝ}
  {n : ℕ} {P0 : Measure (Fin n → Euc d)} [IsProbabilityMeasure P0] {b : ℝ}

/-- The completed square: `-(b/2) ‖S_n‖² = ⟪t, ∑ Ξ⟫ + logW + (b n/2) ‖Ξ̄‖²` for `t = wl4_tN`
(`t = -b Ξ̄`). -/
lemma wl5_logQ_eq (hΨ : CalFeat Ψ B) (hb : 0 < b) (hn : 0 < n) (X : Fin n → Euc d) :
    -(b / 2) * ‖wr11b_Sstat μ Ψ X‖ ^ 2 =
      Yf μ Ψ (wl4_tN (1 / (n : ℝ)) b μ Ψ P0) X +
        wl5_logW b μ Ψ (wl4_RN (1 / (n : ℝ)) b μ Ψ P0) X +
        (b * n / 2) * ‖∫ Y, empXi μ Ψ Y ∂(wl4_RN (1 / (n : ℝ)) b μ Ψ P0)‖ ^ 2 := by
  unfold wl5_logW wl5_D
  rw [Yf_eq_inner hn, wl4_tN_eq_empXi_inv hΨ hn hb]
  set Xb := ∫ Y, empXi μ Ψ Y ∂(wl4_RN (1 / (n : ℝ)) b μ Ψ P0) with hXb
  have key : ‖wr11b_Sstat μ Ψ X - Real.sqrt n • Xb‖ ^ 2 =
      n * (‖empXi μ Ψ X‖ ^ 2 - 2 * inner ℝ (empXi μ Ψ X) Xb + ‖Xb‖ ^ 2) := by
    unfold wr11b_Sstat
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg n),
      norm_sub_sq_real]
  have hS := wr11b_sq_norm_Sstat (μ := μ) (Ψ := Ψ) X
  rw [key, hS, inner_smul_left, real_inner_comm Xb (empXi μ Ψ X)]
  simp only [conj_trivial]
  ring

/-- **Exact density** (`A:eq:bounded-transfer`): if `P` is `P0` tilted by `-(b/2) ‖S_n‖²`, then `P` is `ν`
tilted by `-(b/2) ‖S_n - √n Ξ̄‖²`. -/
theorem wl5_P_eq_RN_tilted (hΨ : CalFeat Ψ B) (hb : 0 < b) (hn : 0 < n)
    {P : Measure (Fin n → Euc d)}
    (hP : P = P0.tilted (fun X => -(b / 2) * ‖wr11b_Sstat μ Ψ X‖ ^ 2)) :
    P = (wl4_RN (1 / (n : ℝ)) b μ Ψ P0).tilted (wl5_logW b μ Ψ (wl4_RN (1 / (n : ℝ)) b μ Ψ P0)) := by
  set t := wl4_tN (1 / (n : ℝ)) b μ Ψ P0 with ht
  set c : ℝ := (b * n / 2) * ‖∫ Y, empXi μ Ψ Y ∂(wl4_RN (1 / (n : ℝ)) b μ Ψ P0)‖ ^ 2 with hc
  have hfun : (fun X : Fin n → Euc d => -(b / 2) * ‖wr11b_Sstat μ Ψ X‖ ^ 2) =
      fun X => (Yf μ Ψ t X + wl5_logW b μ Ψ (wl4_RN (1 / (n : ℝ)) b μ Ψ P0) X) + c := by
    funext X
    rw [wl5_logQ_eq (P0 := P0) hΨ hb hn X]
  have hint : Integrable (fun X : Fin n → Euc d => Real.exp (Yf μ Ψ t X)) P0 := by
    have := hΨ.integrable_exp_Yf (μ := μ) P0 t 1
    simpa only [one_mul] using this
  rw [hP, hfun, wr11b_tilted_add_const P0 (fun X => Yf μ Ψ t X + wl5_logW b μ Ψ (wl4_RN (1 / (n : ℝ)) b μ Ψ P0) X) c]
  show _ = (P0.tilted (Yf μ Ψ t)).tilted _
  rw [tilted_tilted hint]
  rfl

end Calibrated

end HRS.MS.Wl
