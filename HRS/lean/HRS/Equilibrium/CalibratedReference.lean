/-
# HRS.Equilibrium.CalibratedReference -- the weak calibrated reference `R_N` and the bounded transfer (EXT-4, E6 + E8)

Source: main paper `A:eq:split` ... `A:eq:variance-transfer` (TeX lines 3405-3545) and
`Q:eq:reference-law`, `Q:eq:reference-input`, `Q:eq:calibration` (lines 4449-4488).
Plan: `docs/external/variance-plan.md`, rows E6, E8.

Setting.  `μ` is a probability measure on `𝕋^d`, `q ≥ 0` an even measurable kernel with row bound
`sup_x ∫ q(x - y) dμ(y) ≤ γ` (the `q` of the heat split), `Ψ : 𝕋^d → ℝ^M` features with
`g_L(x - y) = ⟪Ψ x, Ψ y⟫` (`RefHyp`; all of these are conclusions of `HeatSplit.weakSplit_spec`),
`Ξ = Ψ - μ(Ψ)`, `0 < β`, `N ≥ 1`.

* `R0`    : `R_N^0 ∝ exp(∑_i β (q*μ)(x_i) - (β/N) ∑_{i<j} q(x_i - x_j)) dμ^{⊗N}` (`Q^q_{N,β}(μ)`);
* `calibF`: `f_N(t) = N⁻¹ log E_{R0}[exp ∑_i t·Ξ(x_i)]`; `calibObj t = f_N(t) + |t|²/(2β)`;
* `tN`    : a minimizer of `calibObj` (`Classical.choose`; existence `exists_calib_min`);
* `RN`    : `R_N = R0` tilted by `∑_i t_N·Ξ(x_i)`.

The smallness `‖t_N·Ξ‖_∞ ≤ 1` is never assumed in a structure: the theorems that need it take it as the
explicit hypothesis `hsmall : ∀ x, |∑ m, tN m * Ξ x m| ≤ 1` (proved elsewhere, EXT-5).
-/
import HRS.Equilibrium.HeatSplit
import HRS.External.WeakSpec

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.External

namespace Calib

open HRS

variable {d M : ℕ}

/-- Standing hypotheses on the weak split (all are conclusions of `HeatSplit.weakSplit_spec`, except
that `μ` is the background, a probability measure): the kernel `q` is a nonnegative even measurable
function with row bound `γ`, and `g_L(x - y) = ⟪Ψ x, Ψ y⟫`. -/
structure RefHyp (μ : Measure (Torus d)) (q gL : Torus d → ℝ)
    (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) (γ : ℝ) : Prop where
  q_meas : Measurable q
  q_nonneg : ∀ x, 0 ≤ q x
  q_even : ∀ x, q (-x) = q x
  q_int : ∀ x, Integrable (fun y => q (x - y)) μ
  q_row : ∀ x, ∫ y, q (x - y) ∂μ ≤ γ
  Ψ_meas : Measurable Ψ
  gL_eq : ∀ x y, gL (x - y) = inner ℝ (Ψ x) (Ψ y)

/-! ### Definitions -/

/-- The centered features `Ξ = Ψ - μ(Ψ)`. -/
def Xi (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) (x : Torus d) :
    EuclideanSpace ℝ (Fin M) := Ψ x - ∫ y, Ψ y ∂μ

/-- The linear statistic `∑_i t·Ξ(x_i)`. -/
def Yf (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) {N : ℕ}
    (t : EuclideanSpace ℝ (Fin M)) (X : Config d N) : ℝ :=
  ∑ i, inner ℝ t (Xi μ Ψ (X i))

/-- The empirical average `μ_N(Ξ) = N⁻¹ ∑_i Ξ(x_i)`. -/
def empXi (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) {N : ℕ}
    (X : Config d N) : EuclideanSpace ℝ (Fin M) :=
  (1 / (N : ℝ)) • ∑ i, Xi μ Ψ (X i)

/-- The rescaled statistic `S_N = √N μ_N(Ξ)`. -/
def Sstat (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) {N : ℕ}
    (X : Config d N) : EuclideanSpace ℝ (Fin M) :=
  Real.sqrt N • empXi μ Ψ X

/-- Log-density of `R_N^0` w.r.t. `μ^{⊗N}` (`Q:eq:reference-law` with `h = 0`):
`∑_i β (q*μ)(x_i) - (β/N) ∑_{i<j} q(x_i - x_j)`, the pair sum written as `½ ∑_{i≠j}`. -/
def E0 (q : Torus d → ℝ) (μ : Measure (Torus d)) (β : ℝ) (N : ℕ) (X : Config d N) : ℝ :=
  ∑ i, β * convMeasure q μ (X i) -
    (β / N) * ((1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i - X j))

/-- The weak reference `R_N^0` (`= Q^q_{N,β}(μ)`, see `R0_eq_modulatedGibbs`). -/
def R0 (q : Torus d → ℝ) (μ : Measure (Torus d)) (β : ℝ) (N : ℕ) : Measure (Config d N) :=
  (Measure.pi fun _ : Fin N => μ).tilted (E0 q μ β N)

/-- The calibration function `f_N(t) = N⁻¹ log E_{R0}[exp ∑_i t·Ξ(x_i)]` (`A:eq:calibration`). -/
def calibF (q : Torus d → ℝ) (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (β : ℝ) (N : ℕ) (t : EuclideanSpace ℝ (Fin M)) : ℝ :=
  (1 / (N : ℝ)) * Real.log (∫ X, Real.exp (Yf μ Ψ t X) ∂(R0 q μ β N))

/-- The calibration objective `f_N(t) + |t|²/(2β)`. -/
def calibObj (q : Torus d → ℝ) (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (β : ℝ) (N : ℕ) (t : EuclideanSpace ℝ (Fin M)) : ℝ :=
  calibF q μ Ψ β N t + ‖t‖ ^ 2 / (2 * β)

open Classical in
/-- The calibration parameter `t_N`: a minimizer of `calibObj` (`0` if there is none; existence is
`exists_calib_min`). -/
def tN (q : Torus d → ℝ) (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (β : ℝ) (N : ℕ) : EuclideanSpace ℝ (Fin M) :=
  if h : ∃ t, ∀ s, calibObj q μ Ψ β N t ≤ calibObj q μ Ψ β N s then h.choose else 0

/-- The calibrated weak reference `R_N = R_{N, t_N·Ξ}`: `R0` tilted by `∑_i t_N·Ξ(x_i)`. -/
def RN (q : Torus d → ℝ) (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (β : ℝ) (N : ℕ) : Measure (Config d N) :=
  (R0 q μ β N).tilted (Yf μ Ψ (tN q μ Ψ β N))

/-- `Ξ̄_N = E_{R_N}[μ_N(Ξ)]`. -/
def Xibar (q : Torus d → ℝ) (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (β : ℝ) (N : ℕ) : EuclideanSpace ℝ (Fin M) :=
  ∫ X, empXi μ Ψ X ∂(RN q μ Ψ β N)

/-! ### Basic bounds -/

section Basic

variable {μ : Measure (Torus d)} {q gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)}
  {γ : ℝ}

theorem RefHyp.gL_zero (h : RefHyp μ q gL Ψ γ) (x : Torus d) : gL 0 = ‖Ψ x‖ ^ 2 := by
  have := h.gL_eq x x
  rw [sub_self, real_inner_self_eq_norm_sq] at this
  exact this

theorem RefHyp.gL_zero_nonneg (h : RefHyp μ q gL Ψ γ) : 0 ≤ gL 0 := by
  rw [h.gL_zero 0]; positivity

theorem RefHyp.norm_Ψ_le (h : RefHyp μ q gL Ψ γ) (x : Torus d) : ‖Ψ x‖ ≤ Real.sqrt (gL 0) := by
  rw [h.gL_zero x]; rw [Real.sqrt_sq (norm_nonneg _)]

theorem RefHyp.gamma_nonneg [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) : 0 ≤ γ := by
  refine le_trans ?_ (h.q_row 0)
  exact integral_nonneg fun y => h.q_nonneg _

theorem RefHyp.integrable_Ψ [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) : Integrable Ψ μ :=
  Integrable.of_bound h.Ψ_meas.aestronglyMeasurable (Real.sqrt (gL 0))
    (Filter.Eventually.of_forall h.norm_Ψ_le)

theorem RefHyp.norm_int_Ψ_le [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) :
    ‖∫ y, Ψ y ∂μ‖ ≤ Real.sqrt (gL 0) := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := Ψ) (C := Real.sqrt (gL 0))
    (Filter.Eventually.of_forall h.norm_Ψ_le)
  simpa using this

theorem RefHyp.measurable_Xi (h : RefHyp μ q gL Ψ γ) : Measurable (Xi μ Ψ) :=
  h.Ψ_meas.sub measurable_const

theorem RefHyp.norm_Xi_le [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) (x : Torus d) :
    ‖Xi μ Ψ x‖ ≤ 2 * Real.sqrt (gL 0) := by
  unfold Xi
  calc ‖Ψ x - ∫ y, Ψ y ∂μ‖ ≤ ‖Ψ x‖ + ‖∫ y, Ψ y ∂μ‖ := norm_sub_le _ _
    _ ≤ Real.sqrt (gL 0) + Real.sqrt (gL 0) := add_le_add (h.norm_Ψ_le x) h.norm_int_Ψ_le
    _ = _ := by ring

theorem RefHyp.integrable_Xi [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) :
    Integrable (Xi μ Ψ) μ :=
  Integrable.of_bound h.measurable_Xi.aestronglyMeasurable (2 * Real.sqrt (gL 0))
    (Filter.Eventually.of_forall h.norm_Xi_le)

theorem RefHyp.integral_Xi [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) :
    ∫ x, Xi μ Ψ x ∂μ = 0 := by
  unfold Xi
  rw [integral_sub h.integrable_Ψ (integrable_const _)]
  simp

theorem RefHyp.measurable_conv [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) :
    Measurable (convMeasure q μ) := by
  unfold convMeasure
  have : Measurable (fun p : Torus d × Torus d => q (p.1 - p.2)) :=
    h.q_meas.comp (measurable_fst.sub measurable_snd)
  exact (this.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem RefHyp.conv_nonneg (h : RefHyp μ q gL Ψ γ) (x : Torus d) : 0 ≤ convMeasure q μ x :=
  integral_nonneg fun y => h.q_nonneg _

theorem RefHyp.conv_le (h : RefHyp μ q gL Ψ γ) (x : Torus d) : convMeasure q μ x ≤ γ :=
  h.q_row x


theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P]
    {f : α → ℝ} (hm : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) : Integrable f P :=
  Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem RefHyp.measurable_E0 [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) (β : ℝ) (N : ℕ) :
    Measurable (E0 q μ β N) := by
  unfold E0
  refine (Finset.measurable_sum _ fun i _ => ?_).sub (Measurable.const_mul ?_ _)
  · exact (h.measurable_conv.comp (measurable_pi_apply i)).const_mul _
  · refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
    exact h.q_meas.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem RefHyp.E0_le [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 ≤ β) (N : ℕ)
    (X : Config d N) : E0 q μ β N X ≤ β * N * γ := by
  unfold E0
  have h1 : ∑ i, β * convMeasure q μ (X i) ≤ ∑ _i : Fin N, β * γ :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h.conv_le _) hβ
  have h2 : 0 ≤ (β / N) * ((1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i - X j)) := by
    refine mul_nonneg (div_nonneg hβ (Nat.cast_nonneg N)) (mul_nonneg (by norm_num) ?_)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => h.q_nonneg _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  nlinarith

theorem RefHyp.integrable_exp_E0 [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 ≤ β)
    (N : ℕ) : Integrable (fun X => Real.exp (E0 q μ β N X)) (Measure.pi fun _ : Fin N => μ) := by
  refine integrable_of_abs_le (Real.measurable_exp.comp (h.measurable_E0 β N)) (Real.exp (β * N * γ))
    fun X => ?_
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (h.E0_le hβ N X)

theorem RefHyp.isProb_R0 [IsProbabilityMeasure μ] (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 ≤ β)
    (N : ℕ) : IsProbabilityMeasure (R0 q μ β N) :=
  isProbabilityMeasure_tilted (h.integrable_exp_E0 hβ N)

/-! ### The linear statistic -/

theorem Yf_add (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) {N : ℕ}
    (t v : EuclideanSpace ℝ (Fin M)) (s : ℝ) (X : Config d N) :
    Yf μ Ψ (t + s • v) X = Yf μ Ψ t X + s * Yf μ Ψ v X := by
  unfold Yf
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_add_left, inner_smul_left]
  simp

theorem Yf_smul (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) {N : ℕ}
    (t : EuclideanSpace ℝ (Fin M)) (s : ℝ) (X : Config d N) :
    Yf μ Ψ (s • t) X = s * Yf μ Ψ t X := by
  have := Yf_add μ Ψ (0 : EuclideanSpace ℝ (Fin M)) t s X
  simpa [Yf] using this

theorem Yf_zero (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) {N : ℕ}
    (X : Config d N) : Yf μ Ψ 0 X = 0 := by simp [Yf]

theorem Yf_eq_inner (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) {N : ℕ}
    (hN : 0 < N) (t : EuclideanSpace ℝ (Fin M)) (X : Config d N) :
    Yf μ Ψ t X = N * inner ℝ t (empXi μ Ψ X) := by
  unfold Yf empXi
  rw [inner_smul_right, inner_sum]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

section Lin

variable [IsProbabilityMeasure μ]

theorem RefHyp.measurable_Yf (h : RefHyp μ q gL Ψ γ) {N : ℕ} (t : EuclideanSpace ℝ (Fin M)) :
    Measurable (Yf μ Ψ (N := N) t) := by
  unfold Yf
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_const.inner (h.measurable_Xi.comp (measurable_pi_apply i)))

theorem RefHyp.abs_Yf_le (h : RefHyp μ q gL Ψ γ) {N : ℕ} (t : EuclideanSpace ℝ (Fin M))
    (X : Config d N) : |Yf μ Ψ t X| ≤ N * (‖t‖ * (2 * Real.sqrt (gL 0))) := by
  unfold Yf
  calc |∑ i, inner ℝ t (Xi μ Ψ (X i))| ≤ ∑ i, |inner ℝ t (Xi μ Ψ (X i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ‖t‖ * (2 * Real.sqrt (gL 0)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc |inner ℝ t (Xi μ Ψ (X i))| ≤ ‖t‖ * ‖Xi μ Ψ (X i)‖ := abs_real_inner_le_norm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (h.norm_Xi_le _) (norm_nonneg _)
    _ = _ := by simp

theorem RefHyp.integrable_exp_Yf (h : RefHyp μ q gL Ψ γ) {N : ℕ} (P : Measure (Config d N))
    [IsFiniteMeasure P] (t : EuclideanSpace ℝ (Fin M)) (s : ℝ) :
    Integrable (fun X => Real.exp (s * Yf μ Ψ t X)) P := by
  refine integrable_of_abs_le (Real.measurable_exp.comp ((h.measurable_Yf t).const_mul s))
    (Real.exp (|s| * (N * (‖t‖ * (2 * Real.sqrt (gL 0)))))) fun X => ?_
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  calc s * Yf μ Ψ t X ≤ |s * Yf μ Ψ t X| := le_abs_self _
    _ = |s| * |Yf μ Ψ t X| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (h.abs_Yf_le t X) (abs_nonneg _)

theorem RefHyp.integrable_Yf (h : RefHyp μ q gL Ψ γ) {N : ℕ} (P : Measure (Config d N))
    [IsFiniteMeasure P] (t : EuclideanSpace ℝ (Fin M)) : Integrable (Yf μ Ψ t) P :=
  integrable_of_abs_le (h.measurable_Yf t) _ (h.abs_Yf_le t)

theorem RefHyp.measurable_empXi (h : RefHyp μ q gL Ψ γ) {N : ℕ} :
    Measurable (empXi μ Ψ (N := N)) := by
  unfold empXi
  exact Measurable.const_smul (Finset.measurable_sum _ fun i _ => h.measurable_Xi.comp (measurable_pi_apply i)) (1 / (N : ℝ))

theorem RefHyp.norm_empXi_le (h : RefHyp μ q gL Ψ γ) {N : ℕ} (hN : 0 < N) (X : Config d N) :
    ‖empXi μ Ψ X‖ ≤ 2 * Real.sqrt (gL 0) := by
  unfold empXi
  rw [norm_smul, Real.norm_eq_abs]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  calc |1 / (N : ℝ)| * ‖∑ i, Xi μ Ψ (X i)‖
      ≤ |1 / (N : ℝ)| * ∑ i, ‖Xi μ Ψ (X i)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)
    _ ≤ |1 / (N : ℝ)| * ∑ _i : Fin N, 2 * Real.sqrt (gL 0) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h.norm_Xi_le _) (abs_nonneg _)
    _ = 2 * Real.sqrt (gL 0) := by
        rw [abs_of_pos (by positivity)]
        simp
        field_simp

theorem RefHyp.integrable_empXi (h : RefHyp μ q gL Ψ γ) {N : ℕ} (hN : 0 < N)
    (P : Measure (Config d N)) [IsFiniteMeasure P] : Integrable (empXi μ Ψ) P :=
  Integrable.of_bound h.measurable_empXi.aestronglyMeasurable (2 * Real.sqrt (gL 0))
    (Filter.Eventually.of_forall (h.norm_empXi_le hN))

end Lin



/-! ### Existence of the minimizer `t_N` -/

section Min

variable [IsProbabilityMeasure μ] {β : ℝ} {N : ℕ}

theorem RefHyp.Z_pos (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (t : EuclideanSpace ℝ (Fin M)) :
    0 < ∫ X, Real.exp (Yf μ Ψ t X) ∂(R0 q μ β N) := by
  haveI := h.isProb_R0 hβ N
  have := h.integrable_exp_Yf (R0 q μ β N) t 1
  simp only [one_mul] at this
  exact integral_exp_pos this

theorem RefHyp.Z_zero (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) :
    ∫ X, Real.exp (Yf μ Ψ (0 : EuclideanSpace ℝ (Fin M)) X) ∂(R0 q μ β N) = 1 := by
  haveI := h.isProb_R0 hβ N
  simp [Yf_zero]

theorem RefHyp.continuous_Z (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) :
    Continuous fun t : EuclideanSpace ℝ (Fin M) => ∫ X, Real.exp (Yf μ Ψ t X) ∂(R0 q μ β N) := by
  haveI := h.isProb_R0 hβ N
  rw [continuous_iff_continuousAt]
  intro t₀
  refine continuousAt_of_dominated (bound := fun _ => Real.exp (N * ((‖t₀‖ + 1) * (2 * Real.sqrt (gL 0)))))
    (Filter.Eventually.of_forall fun t => ?_) ?_ (integrable_const _) (Filter.Eventually.of_forall fun X => ?_)
  · have := h.integrable_exp_Yf (R0 q μ β N) t 1
    simp only [one_mul] at this
    exact this.aestronglyMeasurable
  · have hn : ∀ᶠ t in 𝓝 t₀, ‖t‖ ≤ ‖t₀‖ + 1 := by
      have : Metric.ball t₀ 1 ∈ 𝓝 t₀ := Metric.ball_mem_nhds _ one_pos
      filter_upwards [this] with t ht
      have := norm_le_norm_add_norm_sub' t t₀
      rw [Metric.mem_ball, dist_eq_norm] at ht
      linarith [norm_sub_rev t t₀]
    filter_upwards [hn] with t ht
    refine Filter.Eventually.of_forall fun X => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    calc Yf μ Ψ t X ≤ |Yf μ Ψ t X| := le_abs_self _
      _ ≤ N * (‖t‖ * (2 * Real.sqrt (gL 0))) := h.abs_Yf_le t X
      _ ≤ _ := by
        gcongr
  · -- continuity in `t` of `exp (∑_i ⟪t, Ξ(x_i)⟫)`
    have : Continuous fun t : EuclideanSpace ℝ (Fin M) => Yf μ Ψ t X := by
      unfold Yf
      exact continuous_finset_sum _ fun i _ => continuous_id.inner continuous_const
    exact (Real.continuous_exp.comp this).continuousAt

theorem RefHyp.continuous_calibObj (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) :
    Continuous (calibObj q μ Ψ β N) := by
  unfold calibObj calibF
  refine Continuous.add (Continuous.mul continuous_const ?_) ?_
  · exact Continuous.log (h.continuous_Z hβ) fun t => (h.Z_pos hβ t).ne'
  · fun_prop

theorem RefHyp.calibObj_zero (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) :
    calibObj q μ Ψ β N 0 = 0 := by
  unfold calibObj calibF
  rw [h.Z_zero hβ]
  simp

theorem RefHyp.integral_Yf (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (hN : 0 < N)
    (P : Measure (Config d N)) [IsProbabilityMeasure P] (t : EuclideanSpace ℝ (Fin M)) :
    ∫ X, Yf μ Ψ t X ∂P = N * inner ℝ t (∫ X, empXi μ Ψ X ∂P) := by
  simp_rw [Yf_eq_inner μ Ψ hN]
  rw [integral_const_mul, integral_inner (h.integrable_empXi hN P)]

/-- Jensen: `log E[exp Y] ≥ E[Y]`. -/
theorem log_integral_exp_ge {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {Y : α → ℝ} (hY : Integrable Y P) (hE : Integrable (fun x => Real.exp (Y x)) P) :
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

theorem RefHyp.exists_calib_min (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N) :
    ∃ t, ∀ s, calibObj q μ Ψ β N t ≤ calibObj q μ Ψ β N s := by
  haveI := h.isProb_R0 hβ.le N
  set Xi0 : EuclideanSpace ℝ (Fin M) := ∫ X, empXi μ Ψ X ∂(R0 q μ β N)
  refine (h.continuous_calibObj hβ.le).exists_forall_le' 0 ?_
  rw [h.calibObj_zero hβ.le]
  have hev : ∀ᶠ t : EuclideanSpace ℝ (Fin M) in cocompact _, 2 * β * ‖Xi0‖ ≤ ‖t‖ :=
    (tendsto_norm_cocompact_atTop).eventually_ge_atTop _
  filter_upwards [hev] with t ht
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) * inner ℝ t Xi0 ≤ Real.log (∫ X, Real.exp (Yf μ Ψ t X) ∂(R0 q μ β N)) := by
    have := log_integral_exp_ge (h.integrable_Yf (R0 q μ β N) t)
      (by simpa using h.integrable_exp_Yf (R0 q μ β N) t 1)
    rwa [h.integral_Yf hβ.le hN] at this
  unfold calibObj calibF
  have h2 : inner ℝ t Xi0 ≥ -(‖t‖ * ‖Xi0‖) := by
    have := abs_real_inner_le_norm t Xi0
    linarith [neg_abs_le (inner ℝ t Xi0)]
  have h3 : (1 / (N : ℝ)) * (N * inner ℝ t Xi0) ≤
      (1 / (N : ℝ)) * Real.log (∫ X, Real.exp (Yf μ Ψ t X) ∂(R0 q μ β N)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : (1 / (N : ℝ)) * (N * inner ℝ t Xi0) = inner ℝ t Xi0 := by field_simp
  have h5 : 0 ≤ ‖t‖ ^ 2 / (2 * β) - ‖t‖ * ‖Xi0‖ := by
    have : ‖t‖ * ‖Xi0‖ ≤ ‖t‖ ^ 2 / (2 * β) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [norm_nonneg t, norm_nonneg Xi0]
    linarith
  linarith

end Min

section TNspec

variable [IsProbabilityMeasure μ] {β : ℝ} {N : ℕ}

theorem RefHyp.tN_spec (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N)
    (s : EuclideanSpace ℝ (Fin M)) :
    calibObj q μ Ψ β N (tN q μ Ψ β N) ≤ calibObj q μ Ψ β N s := by
  have hex := h.exists_calib_min hβ hN
  unfold tN
  rw [dif_pos hex]
  exact hex.choose_spec s

end TNspec


/-! ### Stationarity `t_N = -β Ξ̄_N` -/

section Stat

variable [IsProbabilityMeasure μ] {β : ℝ} {N : ℕ}

theorem RefHyp.integrableExpSet_Yf (h : RefHyp μ q gL Ψ γ) (P : Measure (Config d N))
    [IsFiniteMeasure P] (v : EuclideanSpace ℝ (Fin M)) :
    integrableExpSet (Yf μ Ψ v) P = Set.univ := by
  ext s
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact h.integrable_exp_Yf P v s

theorem RefHyp.isProb_tilted_Yf (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (t : EuclideanSpace ℝ (Fin M)) :
    IsProbabilityMeasure ((R0 q μ β N).tilted (Yf μ Ψ t)) := by
  haveI := h.isProb_R0 hβ N
  have := h.integrable_exp_Yf (R0 q μ β N) t 1
  simp only [one_mul] at this
  exact isProbabilityMeasure_tilted this

theorem RefHyp.calibF_add (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (t v : EuclideanSpace ℝ (Fin M))
    (s : ℝ) :
    calibF q μ Ψ β N (t + s • v) = calibF q μ Ψ β N t +
      (1 / (N : ℝ)) * cgf (Yf μ Ψ v) ((R0 q μ β N).tilted (Yf μ Ψ t)) s := by
  have hZ := h.Z_pos hβ (N := N) t
  have hZ' := h.Z_pos hβ (N := N) (t + s • v)
  have hmgf : mgf (Yf μ Ψ v) ((R0 q μ β N).tilted (Yf μ Ψ t)) s =
      (∫ X, Real.exp (Yf μ Ψ (t + s • v) X) ∂(R0 q μ β N)) /
        ∫ X, Real.exp (Yf μ Ψ t X) ∂(R0 q μ β N) := by
    unfold mgf
    rw [integral_exp_tilted (Yf μ Ψ t) (fun X => s * Yf μ Ψ v X)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp [Yf_add]
  unfold calibF cgf
  rw [hmgf, Real.log_div hZ'.ne' hZ.ne']
  ring

theorem RefHyp.hasDerivAt_calibObj (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β)
    (t v : EuclideanSpace ℝ (Fin M)) :
    HasDerivAt (fun s : ℝ => calibObj q μ Ψ β N (t + s • v))
      ((1 / (N : ℝ)) * ∫ X, Yf μ Ψ v X ∂((R0 q μ β N).tilted (Yf μ Ψ t)) +
        inner ℝ t v / β) 0 := by
  haveI := h.isProb_tilted_Yf hβ.le (N := N) t
  have hmem : (0 : ℝ) ∈ interior (integrableExpSet (Yf μ Ψ v) ((R0 q μ β N).tilted (Yf μ Ψ t))) := by
    rw [h.integrableExpSet_Yf]; simp
  have hc : HasDerivAt (cgf (Yf μ Ψ v) ((R0 q μ β N).tilted (Yf μ Ψ t)))
      (∫ X, Yf μ Ψ v X ∂((R0 q μ β N).tilted (Yf μ Ψ t))) 0 := by
    have := (analyticAt_cgf hmem).differentiableAt.hasDerivAt
    rwa [deriv_cgf_zero hmem, probReal_univ, div_one] at this
  have hf : HasDerivAt (fun s : ℝ => t + s • v) v 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add t
    simpa using this
  have hn := hf.norm_sq
  have hall := (hasDerivAt_const (0 : ℝ) (calibF q μ Ψ β N t)).add (hc.const_mul (1 / (N : ℝ)))
    |>.add (hn.div_const (2 * β))
  have e : (fun s : ℝ => calibObj q μ Ψ β N (t + s • v)) =
      fun s => (fun _ => calibF q μ Ψ β N t) s + (1 / (N : ℝ)) * cgf (Yf μ Ψ v)
        ((R0 q μ β N).tilted (Yf μ Ψ t)) s + ‖t + s • v‖ ^ 2 / (2 * β) := by
    funext s
    unfold calibObj
    rw [h.calibF_add hβ.le]
  rw [e]
  convert hall using 1
  simp
  field_simp

theorem RefHyp.tN_eq (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N) :
    tN q μ Ψ β N = -β • Xibar q μ Ψ β N := by
  set t := tN q μ Ψ β N with ht
  haveI := h.isProb_tilted_Yf hβ.le (N := N) t
  have hR : RN q μ Ψ β N = (R0 q μ β N).tilted (Yf μ Ψ t) := rfl
  have hstat : ∀ v : EuclideanSpace ℝ (Fin M),
      inner ℝ v (Xibar q μ Ψ β N + (1 / β) • t) = 0 := by
    intro v
    have hd := h.hasDerivAt_calibObj hβ (N := N) t v
    have hmin : IsLocalMin (fun s : ℝ => calibObj q μ Ψ β N (t + s • v)) 0 :=
      Filter.Eventually.of_forall fun s => by
        simpa using h.tN_spec hβ hN (t + s • v)
    have h0 := hmin.hasDerivAt_eq_zero hd
    rw [h.integral_Yf hβ.le hN] at h0
    have hX : Xibar q μ Ψ β N = ∫ X, empXi μ Ψ X ∂((R0 q μ β N).tilted (Yf μ Ψ t)) := rfl
    rw [← hX] at h0
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [inner_add_right, inner_smul_right, real_inner_comm t v]
    have : (1 / (N : ℝ)) * ((N : ℝ) * inner ℝ v (Xibar q μ Ψ β N)) = inner ℝ v (Xibar q μ Ψ β N) := by
      field_simp
    rw [this] at h0
    rw [one_div, inv_mul_eq_div]
    linarith [h0, show (inner ℝ v t) / β = β⁻¹ * inner ℝ v t by ring]
  have h0 := hstat (Xibar q μ Ψ β N + (1 / β) • t)
  rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at h0
  have : t = -β • Xibar q μ Ψ β N := by
    have h1 : (1 / β) • t = -Xibar q μ Ψ β N := eq_neg_of_add_eq_zero_right h0
    calc t = β • ((1 / β) • t) := by rw [smul_smul, mul_one_div_cancel hβ.ne', one_smul]
      _ = β • (-Xibar q μ Ψ β N) := by rw [h1]
      _ = _ := by rw [smul_neg, neg_smul]
  exact this

end Stat


/-! ### The bound `|t_N| ≤ β |E_{R0}[μ_N Ξ]|` -/

section Mono

variable [IsProbabilityMeasure μ] {β : ℝ} {N : ℕ}

/-- Monotonicity of the derivative of the cumulant generating function of a bounded statistic. -/
theorem RefHyp.deriv_cgf_mono (h : RefHyp μ q gL Ψ γ) (P : Measure (Config d N))
    [IsProbabilityMeasure P] (v : EuclideanSpace ℝ (Fin M)) :
    deriv (cgf (Yf μ Ψ v) P) 0 ≤ deriv (cgf (Yf μ Ψ v) P) 1 := by
  have hint : ∀ s : ℝ, s ∈ interior (integrableExpSet (Yf μ Ψ v) P) := by
    intro s; rw [h.integrableExpSet_Yf]; simp
  have hdiff : Differentiable ℝ (deriv (cgf (Yf μ Ψ v) P)) := fun s =>
    (analyticAt_cgf (hint s)).deriv.differentiableAt
  have hmono : MonotoneOn (deriv (cgf (Yf μ Ψ v) P)) Set.univ := by
    refine monotoneOn_of_deriv_nonneg convex_univ hdiff.continuous.continuousOn
      hdiff.differentiableOn fun s _ => ?_
    have h2 : deriv (deriv (cgf (Yf μ Ψ v) P)) s = iteratedDeriv 2 (cgf (Yf μ Ψ v) P) s := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2, ← variance_tilted_mul (hint s)]
    exact variance_nonneg _ _
  exact hmono (Set.mem_univ _) (Set.mem_univ _) zero_le_one

theorem RefHyp.calibF_smul (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (t : EuclideanSpace ℝ (Fin M))
    (s : ℝ) :
    calibF q μ Ψ β N (s • t) = (1 / (N : ℝ)) * cgf (Yf μ Ψ t) (R0 q μ β N) s := by
  unfold calibF cgf mgf
  simp_rw [Yf_smul]

theorem RefHyp.tN_norm_le (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N) :
    ‖tN q μ Ψ β N‖ ≤ β * ‖∫ X, empXi μ Ψ X ∂(R0 q μ β N)‖ := by
  set t := tN q μ Ψ β N with ht
  haveI := h.isProb_R0 hβ.le N
  haveI := h.isProb_tilted_Yf hβ.le (N := N) t
  have hmono := h.deriv_cgf_mono (R0 q μ β N) t
  have hint : ∀ s : ℝ, s ∈ interior (integrableExpSet (Yf μ Ψ t) (R0 q μ β N)) := by
    intro s; rw [h.integrableExpSet_Yf]; simp
  have d0 : deriv (cgf (Yf μ Ψ t) (R0 q μ β N)) 0 = ∫ X, Yf μ Ψ t X ∂(R0 q μ β N) := by
    rw [deriv_cgf_zero (hint 0), probReal_univ, div_one]
  have d1 : deriv (cgf (Yf μ Ψ t) (R0 q μ β N)) 1 =
      ∫ X, Yf μ Ψ t X ∂((R0 q μ β N).tilted (Yf μ Ψ t)) := by
    rw [← integral_tilted_mul_self (hint 1)]
    simp only [one_mul]
  rw [d0, d1, h.integral_Yf hβ.le hN, h.integral_Yf hβ.le hN] at hmono
  have hX : Xibar q μ Ψ β N = ∫ X, empXi μ Ψ X ∂((R0 q μ β N).tilted (Yf μ Ψ t)) := rfl
  rw [← hX] at hmono
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : inner ℝ t (∫ X, empXi μ Ψ X ∂(R0 q μ β N)) ≤ inner ℝ t (Xibar q μ Ψ β N) := by
    have := (mul_le_mul_iff_of_pos_left hN').1 hmono
    exact this
  have hteq := h.tN_eq hβ hN
  rw [← ht] at hteq
  have hXi : Xibar q μ Ψ β N = -(1 / β) • t := by
    rw [hteq, smul_smul]
    have : -(1 / β) * (-β) = 1 := by field_simp
    rw [this, one_smul]
  rw [hXi, inner_smul_right, real_inner_self_eq_norm_sq] at hm
  have h2 := abs_real_inner_le_norm t (∫ X, empXi μ Ψ X ∂(R0 q μ β N))
  have h3 : ‖t‖ ^ 2 ≤ β * (‖t‖ * ‖∫ X, empXi μ Ψ X ∂(R0 q μ β N)‖) := by
    have hneg := neg_abs_le (inner ℝ t (∫ X, empXi μ Ψ X ∂(R0 q μ β N)))
    have : -(1 / β) * ‖t‖ ^ 2 ≥ -(‖t‖ * ‖∫ X, empXi μ Ψ X ∂(R0 q μ β N)‖) := by linarith
    have h4 : (1 / β) * ‖t‖ ^ 2 ≤ ‖t‖ * ‖∫ X, empXi μ Ψ X ∂(R0 q μ β N)‖ := by linarith
    calc ‖t‖ ^ 2 = β * ((1 / β) * ‖t‖ ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 hβ.le
  by_cases h0 : ‖t‖ = 0
  · rw [h0]; positivity
  · have hpos : 0 < ‖t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

end Mono


/-! ### The modulated energy of the split kernel (`A:eq:finite-block-diagonal`) -/

section Energy

variable [IsProbabilityMeasure μ] {β : ℝ} {N : ℕ}

theorem RefHyp.empXi_eq (h : RefHyp μ q gL Ψ γ) (hN : 0 < N) (X : Config d N) :
    empXi μ Ψ X = (1 / (N : ℝ)) • ∑ i, Ψ (X i) - ∫ y, Ψ y ∂μ := by
  unfold empXi Xi
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have : (1 / (N : ℝ)) • (N • ∫ y, Ψ y ∂μ) = ∫ y, Ψ y ∂μ := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    field_simp
    simp
  rw [smul_sub, this]

/-- `A:eq:finite-block-diagonal`: `F_N^{g_L}(X_N, μ) = ½|μ_N(Ξ)|² - g_L(0)/(2N)`. -/
theorem RefHyp.modEnergy_gL (h : RefHyp μ q gL Ψ γ) (hN : 0 < N) (X : Config d N) :
    modulatedEnergyKernel gL X μ = (1 / 2) * ‖empXi μ Ψ X‖ ^ 2 - gL 0 / (2 * N) := by
  set m : EuclideanSpace ℝ (Fin M) := ∫ y, Ψ y ∂μ with hm
  set P : EuclideanSpace ℝ (Fin M) := ∑ i, Ψ (X i) with hP
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : ∑ i, ∑ j ∈ Finset.univ.erase i, gL (X i - X j) = ‖P‖ ^ 2 - N * gL 0 := by
    have e1 : ∀ i j, gL (X i - X j) = inner ℝ (Ψ (X i)) (Ψ (X j)) := fun i j => h.gL_eq _ _
    simp_rw [e1]
    have e2 : ∀ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Ψ (X i)) (Ψ (X j)) =
        ∑ j, inner ℝ (Ψ (X i)) (Ψ (X j)) - ‖Ψ (X i)‖ ^ 2 := by
      intro i
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), real_inner_self_eq_norm_sq]
    simp_rw [e2]
    rw [Finset.sum_sub_distrib]
    have e3 : ∑ i, ∑ j, inner ℝ (Ψ (X i)) (Ψ (X j)) = ‖P‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hP, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_sum]
    have e4 : ∑ i : Fin N, ‖Ψ (X i)‖ ^ 2 = N * gL 0 := by
      simp_rw [← h.gL_zero (X _)]
      simp
    rw [e3, e4]
  have h2 : ∀ x, ∫ y, gL (x - y) ∂μ = inner ℝ (Ψ x) m := by
    intro x
    simp_rw [h.gL_eq]
    exact integral_inner h.integrable_Ψ (Ψ x)
  have h3 : ∫ x, ∫ y, gL (x - y) ∂μ ∂μ = ‖m‖ ^ 2 := by
    simp_rw [h2]
    have : ∀ x, inner ℝ (Ψ x) m = inner ℝ m (Ψ x) := fun x => real_inner_comm _ _
    simp_rw [this]
    rw [integral_inner h.integrable_Ψ, ← hm, real_inner_self_eq_norm_sq]
  have h4 : empXi μ Ψ X = (1 / (N : ℝ)) • P - m := h.empXi_eq hN X
  unfold modulatedEnergyKernel modulatedEnergy
  simp only []
  rw [h1, h3]
  simp_rw [h2]
  rw [h4, norm_sub_sq_real, norm_smul, inner_smul_left]
  have : ∑ i, inner ℝ (Ψ (X i)) m = inner ℝ P m := by
    rw [hP, sum_inner]
  simp only [conj_trivial, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [this]
  field_simp
  ring

/-- The split kernel `g_L + q - c` (as a function; equal to `g` off the origin). -/
def gTot (gL q : Torus d → ℝ) (c : ℝ) : Torus d → ℝ := fun x => gL x + q x - c

/-- The modulated energy of a constant kernel: `F_N^c = -c/(2N)`. -/
theorem modEnergy_const (hN : 0 < N) (c : ℝ) (X : Config d N) :
    modulatedEnergyKernel (fun _ : Torus d => c) X μ = -c / (2 * N) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold modulatedEnergyKernel modulatedEnergy
  simp only [integral_const, probReal_univ, one_smul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hc : ∀ i : Fin N, ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hN]
    simp
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem modEnergy_add_sub {f1 f2 f3 : Torus d → ℝ}
    (hi1 : ∀ x, Integrable (fun y => f1 (x - y)) μ) (hi2 : ∀ x, Integrable (fun y => f2 (x - y)) μ)
    (hi3 : ∀ x, Integrable (fun y => f3 (x - y)) μ)
    (hii1 : Integrable (fun x => ∫ y, f1 (x - y) ∂μ) μ)
    (hii2 : Integrable (fun x => ∫ y, f2 (x - y) ∂μ) μ)
    (hii3 : Integrable (fun x => ∫ y, f3 (x - y) ∂μ) μ) (X : Config d N) :
    modulatedEnergyKernel (fun x => f1 x + f2 x - f3 x) X μ =
      modulatedEnergyKernel f1 X μ + modulatedEnergyKernel f2 X μ - modulatedEnergyKernel f3 X μ := by
  unfold modulatedEnergyKernel modulatedEnergy
  have e2 : ∀ x, ∫ y, (f1 (x - y) + f2 (x - y) - f3 (x - y)) ∂μ =
      ∫ y, f1 (x - y) ∂μ + ∫ y, f2 (x - y) ∂μ - ∫ y, f3 (x - y) ∂μ := fun x =>
    (integral_sub ((hi1 x).add (hi2 x)) (hi3 x)).trans
      (by simp only [Pi.add_apply]; rw [integral_add (hi1 x) (hi2 x)])
  have e3 : ∫ x, (∫ y, f1 (x - y) ∂μ + ∫ y, f2 (x - y) ∂μ - ∫ y, f3 (x - y) ∂μ) ∂μ =
      ∫ x, ∫ y, f1 (x - y) ∂μ ∂μ + ∫ x, ∫ y, f2 (x - y) ∂μ ∂μ - ∫ x, ∫ y, f3 (x - y) ∂μ ∂μ :=
    (integral_sub (hii1.add hii2) hii3).trans
      (by simp only [Pi.add_apply]; rw [integral_add hii1 hii2])
  simp only [e2, e3, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem RefHyp.integrable_gL_section (h : RefHyp μ q gL Ψ γ) (x : Torus d) :
    Integrable (fun y => gL (x - y)) μ := by
  have e : (fun y => gL (x - y)) = fun y => inner ℝ (Ψ x) (Ψ y) := funext fun y => h.gL_eq x y
  rw [e]
  refine integrable_of_abs_le (measurable_const.inner h.Ψ_meas) (Real.sqrt (gL 0) * Real.sqrt (gL 0))
    fun y => ?_
  calc |inner ℝ (Ψ x) (Ψ y)| ≤ ‖Ψ x‖ * ‖Ψ y‖ := abs_real_inner_le_norm _ _
    _ ≤ _ := mul_le_mul (h.norm_Ψ_le x) (h.norm_Ψ_le y) (norm_nonneg _) (Real.sqrt_nonneg _)

theorem RefHyp.integrable_gL_conv (h : RefHyp μ q gL Ψ γ) :
    Integrable (fun x => ∫ y, gL (x - y) ∂μ) μ := by
  have e : (fun x => ∫ y, gL (x - y) ∂μ) = fun x => inner ℝ (Ψ x) (∫ y, Ψ y ∂μ) := by
    funext x
    simp_rw [h.gL_eq]
    exact integral_inner h.integrable_Ψ (Ψ x)
  rw [e]
  refine integrable_of_abs_le (h.Ψ_meas.inner measurable_const) (Real.sqrt (gL 0) * Real.sqrt (gL 0))
    fun x => ?_
  calc |inner ℝ (Ψ x) (∫ y, Ψ y ∂μ)| ≤ ‖Ψ x‖ * ‖∫ y, Ψ y ∂μ‖ := abs_real_inner_le_norm _ _
    _ ≤ _ := mul_le_mul (h.norm_Ψ_le x) h.norm_int_Ψ_le (norm_nonneg _) (Real.sqrt_nonneg _)

theorem RefHyp.integrable_q_conv (h : RefHyp μ q gL Ψ γ) :
    Integrable (fun x => ∫ y, q (x - y) ∂μ) μ := by
  refine integrable_of_abs_le (f := fun x => ∫ y, q (x - y) ∂μ) h.measurable_conv γ fun x => ?_
  exact (abs_of_nonneg (h.conv_nonneg x)).trans_le (h.conv_le x)

/-- Linearity: `F_N^{g_L + q - c} = F_N^{g_L} + F_N^q - F_N^c`, hence
`F_N^{g_L+q-c} = ½|μ_N(Ξ)|² - g_L(0)/(2N) + F_N^q + c/(2N)`. -/
theorem RefHyp.modEnergy_total (h : RefHyp μ q gL Ψ γ) (hN : 0 < N) (c : ℝ) (X : Config d N) :
    modulatedEnergyKernel (gTot gL q c) X μ =
      (1 / 2) * ‖empXi μ Ψ X‖ ^ 2 - gL 0 / (2 * N) + modulatedEnergyKernel q X μ + c / (2 * N) := by
  unfold gTot
  rw [modEnergy_add_sub (f3 := fun _ => c) h.integrable_gL_section h.q_int
    (fun _ => integrable_const _) h.integrable_gL_conv h.integrable_q_conv
    (by simp) X, h.modEnergy_gL hN, modEnergy_const hN]
  ring

end Energy

/-! ### The exact density `dQ/dR_N` (`A:eq:bounded-transfer`) -/

section Density

/-- Adding a constant to the log-density does not change the tilted measure. -/
theorem tilted_add_const {α : Type*} [MeasurableSpace α] (P : Measure α) (f : α → ℝ) (k : ℝ) :
    P.tilted (fun x => f x + k) = P.tilted f := by
  unfold Measure.tilted
  have hZ : ∫ x, Real.exp (f x + k) ∂P = (∫ x, Real.exp (f x) ∂P) * Real.exp k := by
    simp_rw [Real.exp_add]
    exact integral_mul_const _ _
  congr 1
  funext x
  rw [hZ, Real.exp_add, mul_div_mul_right _ _ (Real.exp_pos k).ne']

theorem modulatedGibbs_eq_tilted [IsProbabilityMeasure μ] {g : Torus d → ℝ} {β : ℝ} {N : ℕ}
    (hint : Integrable (fun X : Config d N => Real.exp (-β * N * modulatedEnergyKernel g X μ))
      (Measure.pi fun _ : Fin N => μ)) :
    modulatedGibbs g N β μ =
      (Measure.pi fun _ : Fin N => μ).tilted (fun X => -β * N * modulatedEnergyKernel g X μ) := by
  have hZ := integral_exp_pos (μ := Measure.pi fun _ : Fin N => μ)
    (f := fun X : Config d N => -β * N * modulatedEnergyKernel g X μ) hint
  unfold modulatedGibbs gibbsNormalizer Measure.tilted
  have hr : (ENNReal.ofReal (∫ X : Config d N, Real.exp (-β * N * modulatedEnergyKernel g X μ)
      ∂(Measure.pi fun _ : Fin N => μ)))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne'
  rw [← withDensity_smul' _ _ hr]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm]

variable [IsProbabilityMeasure μ] {q gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)}
  {γ : ℝ} {β : ℝ} {N : ℕ}

/-- `K_q = ½ ∬ q dμ dμ`. -/
def Kq (q : Torus d → ℝ) (μ : Measure (Torus d)) : ℝ := (1 / 2) * ∫ x, ∫ y, q (x - y) ∂μ ∂μ

theorem modEnergy_q_eq (hN : 0 < N) (β : ℝ) (X : Config d N) :
    -β * N * modulatedEnergyKernel q X μ = E0 q μ β N X - β * N * Kq q μ := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold modulatedEnergyKernel modulatedEnergy E0 Kq convMeasure
  simp only [← Finset.mul_sum]
  field_simp
  ring

omit [IsProbabilityMeasure μ] in
theorem sq_norm_Sstat (N : ℕ) (X : Config d N) :
    ‖Sstat μ Ψ X‖ ^ 2 = N * ‖empXi μ Ψ X‖ ^ 2 := by
  unfold Sstat
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg N)]

theorem RefHyp.measurable_Sstat (h : RefHyp μ q gL Ψ γ) : Measurable (Sstat μ Ψ (N := N)) :=
  Measurable.const_smul h.measurable_empXi (Real.sqrt N)

/-- The log-density of `Q_{N,β}` w.r.t. `μ^{⊗N}` in terms of `R_N^0`:
`-βN F_N^{g_L+q-c} = log(dR_N^0/dμ^N) - (β/2)|S_N|² + const`. -/
theorem RefHyp.logQ_eq (h : RefHyp μ q gL Ψ γ) (hN : 0 < N) (β c : ℝ) (X : Config d N) :
    -β * N * modulatedEnergyKernel (gTot gL q c) X μ =
      E0 q μ β N X - (β / 2) * ‖Sstat μ Ψ X‖ ^ 2 + (β * (gL 0 - c) / 2 - β * N * Kq q μ) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have := modEnergy_q_eq (μ := μ) (q := q) hN β X
  rw [h.modEnergy_total hN c X, sq_norm_Sstat (μ := μ) (Ψ := Ψ) N X]
  have e : -β * N * (1 / 2 * ‖empXi μ Ψ X‖ ^ 2 - gL 0 / (2 * N) + modulatedEnergyKernel q X μ +
      c / (2 * N)) = -(β * N / 2) * ‖empXi μ Ψ X‖ ^ 2 + β * gL 0 / 2 - β * c / 2 +
      (-β * N * modulatedEnergyKernel q X μ) := by
    field_simp
    ring
  rw [e, this]
  ring

theorem RefHyp.integrable_exp_logQ (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (hN : 0 < N) (c : ℝ) :
    Integrable (fun X : Config d N => Real.exp (-β * N * modulatedEnergyKernel (gTot gL q c) X μ))
      (Measure.pi fun _ : Fin N => μ) := by
  have hm : Measurable (fun X : Config d N => -β * N * modulatedEnergyKernel (gTot gL q c) X μ) := by
    have : (fun X : Config d N => -β * N * modulatedEnergyKernel (gTot gL q c) X μ) =
        fun X => E0 q μ β N X - (β / 2) * ‖Sstat μ Ψ X‖ ^ 2 +
          (β * (gL 0 - c) / 2 - β * N * Kq q μ) := funext fun X => h.logQ_eq hN β c X
    rw [this]
    exact ((h.measurable_E0 β N).sub (((h.measurable_Sstat (N := N)).norm.pow_const 2).const_mul _)).add_const _
  refine integrable_of_abs_le (Real.measurable_exp.comp hm)
    (Real.exp (β * N * γ + (β * (gL 0 - c) / 2 - β * N * Kq q μ))) fun X => ?_
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  rw [h.logQ_eq hN β c X]
  have := h.E0_le hβ N X
  have : 0 ≤ (β / 2) * ‖Sstat μ Ψ X‖ ^ 2 := by positivity
  linarith

/-- `Q_{N,β}(μ)` (with the split kernel) as a tilt of `μ^{⊗N}`. -/
theorem RefHyp.Q_eq_tilted (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (hN : 0 < N) (c : ℝ) :
    modulatedGibbs (gTot gL q c) N β μ =
      (Measure.pi fun _ : Fin N => μ).tilted (fun X => -β * N * modulatedEnergyKernel (gTot gL q c) X μ) :=
  modulatedGibbs_eq_tilted (h.integrable_exp_logQ hβ hN c)

/-- `R_N^0 = Q^q_{N,β}(μ)`. -/
theorem RefHyp.R0_eq_modulatedGibbs (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (hN : 0 < N) :
    R0 q μ β N = modulatedGibbs q N β μ := by
  have hint : Integrable (fun X : Config d N => Real.exp (-β * N * modulatedEnergyKernel q X μ))
      (Measure.pi fun _ : Fin N => μ) := by
    have : (fun X : Config d N => Real.exp (-β * N * modulatedEnergyKernel q X μ)) =
        fun X => Real.exp (E0 q μ β N X) * Real.exp (-(β * N * Kq q μ)) := by
      funext X
      rw [← Real.exp_add, modEnergy_q_eq hN β X]
      ring_nf
    rw [this]
    exact (h.integrable_exp_E0 hβ N).mul_const _
  rw [modulatedGibbs_eq_tilted hint]
  unfold R0
  rw [← tilted_add_const _ (E0 q μ β N) (-(β * N * Kq q μ))]
  congr 1
  funext X
  rw [modEnergy_q_eq hN β X]
  ring

theorem RefHyp.RN_eq_tilted (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) :
    RN q μ Ψ β N = (Measure.pi fun _ : Fin N => μ).tilted
      (fun X => E0 q μ β N X + Yf μ Ψ (tN q μ Ψ β N) X) := by
  unfold RN R0
  rw [tilted_tilted (h.integrable_exp_E0 hβ N)]
  rfl

theorem RefHyp.integrable_exp_E0_Yf (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (N : ℕ)
    (t : EuclideanSpace ℝ (Fin M)) :
    Integrable (fun X : Config d N => Real.exp (E0 q μ β N X + Yf μ Ψ t X))
      (Measure.pi fun _ : Fin N => μ) := by
  refine integrable_of_abs_le (Real.measurable_exp.comp
    ((h.measurable_E0 β N).add (h.measurable_Yf _)))
    (Real.exp (β * N * γ + N * (‖t‖ * (2 * Real.sqrt (gL 0))))) fun X => ?_
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  have h1 := h.E0_le hβ N X
  have h2 := (le_abs_self _).trans (h.abs_Yf_le t X)
  linarith

/-- The Gaussian weight `exp(-(β/2)|S_N - √N Ξ̄_N|²)` of `A:eq:bounded-transfer` (log form). -/
def logW (q : Torus d → ℝ) (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (β : ℝ) (N : ℕ) (X : Config d N) : ℝ :=
  -(β / 2) * ‖Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N‖ ^ 2

theorem RefHyp.logQ_eq_RN (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N) (c : ℝ)
    (X : Config d N) :
    -β * N * modulatedEnergyKernel (gTot gL q c) X μ =
      (E0 q μ β N X + Yf μ Ψ (tN q μ Ψ β N) X) + logW q μ Ψ β N X +
        (β * (gL 0 - c) / 2 - β * N * Kq q μ + (β * N / 2) * ‖Xibar q μ Ψ β N‖ ^ 2) := by
  have key : ‖Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N‖ ^ 2 =
      N * (‖empXi μ Ψ X‖ ^ 2 - 2 * inner ℝ (empXi μ Ψ X) (Xibar q μ Ψ β N) +
        ‖Xibar q μ Ψ β N‖ ^ 2) := by
    unfold Sstat
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg N),
      norm_sub_sq_real]
  rw [h.logQ_eq hN β c X, Yf_eq_inner μ Ψ hN, h.tN_eq hβ hN]
  unfold logW
  rw [key, sq_norm_Sstat (μ := μ) (Ψ := Ψ) N X, inner_smul_left, real_inner_comm (Xibar q μ Ψ β N) (empXi μ Ψ X)]
  simp only [conj_trivial]
  ring

/-- **`A:eq:bounded-transfer`** (exact density): `Q_{N,β}(μ) = R_N` tilted by
`-(β/2)|S_N - √N Ξ̄_N|²`, i.e. `dQ/dR_N = e^{-β|S_N-√NΞ̄_N|²/2} / E_{R_N}[e^{-β|S_N-√NΞ̄_N|²/2}]`. -/
theorem RefHyp.Q_eq_RN_tilted (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N) (c : ℝ) :
    modulatedGibbs (gTot gL q c) N β μ = (RN q μ Ψ β N).tilted (logW q μ Ψ β N) := by
  rw [h.Q_eq_tilted hβ.le hN c, h.RN_eq_tilted hβ.le]
  have hint := h.integrable_exp_E0_Yf hβ.le N (tN q μ Ψ β N)
  rw [tilted_tilted hint]
  have : (fun X : Config d N => -β * N * modulatedEnergyKernel (gTot gL q c) X μ) =
      fun X => ((fun X => E0 q μ β N X + Yf μ Ψ (tN q μ Ψ β N) X) + logW q μ Ψ β N) X +
        (β * (gL 0 - c) / 2 - β * N * Kq q μ + (β * N / 2) * ‖Xibar q μ Ψ β N‖ ^ 2) := by
    funext X
    rw [h.logQ_eq_RN hβ hN c X]
    simp only [Pi.add_apply]
  rw [this, tilted_add_const]

/-- The density of `Q_{N,β}(μ)` w.r.t. `R_N` in `withDensity` form. -/
theorem RefHyp.Q_eq_RN_withDensity (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N) (c : ℝ) :
    modulatedGibbs (gTot gL q c) N β μ = (RN q μ Ψ β N).withDensity
      (fun X => ENNReal.ofReal (Real.exp (logW q μ Ψ β N X) /
        ∫ Y, Real.exp (logW q μ Ψ β N Y) ∂(RN q μ Ψ β N))) :=
  h.Q_eq_RN_tilted hβ hN c

end Density

/-! ### Wu's inequality for `R_N` (`A:eq:weak-linear`) -/

section WuApp

variable [IsProbabilityMeasure μ] {q gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)}
  {γ : ℝ} {β : ℝ} {N : ℕ}

theorem inner_eq_sum (t v : EuclideanSpace ℝ (Fin M)) :
    inner ℝ t v = ∑ m, t.ofLp m * v.ofLp m := by
  simp [PiLp.inner_apply, mul_comm]

/-- The weak potential of `R_{N, t·Ξ}`: `φ = β q*μ + t·Ξ`, pair kernel `q(x - y)`, `M = βγ + 1`,
`M' = 0`, provided `|t·Ξ| ≤ 1`. -/
def weakPot (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 ≤ β) (t : EuclideanSpace ℝ (Fin M))
    (ht : ∀ x, |inner ℝ t (Xi μ Ψ x)| ≤ 1) : WeakPotential μ where
  φ := fun x => β * convMeasure q μ x + inner ℝ t (Xi μ Ψ x)
  q := fun x y => q (x - y)
  M := β * γ + 1
  M' := 0
  γ := γ
  measurable_φ := (h.measurable_conv.const_mul β).add (measurable_const.inner h.measurable_Xi)
  measurable_q := h.q_meas.comp (measurable_fst.sub measurable_snd)
  q_nonneg := fun x y => h.q_nonneg _
  q_symm := fun x y => by rw [← h.q_even (x - y), neg_sub]
  γ_nonneg := h.gamma_nonneg
  φ_le := fun x => by
    have h1 : β * convMeasure q μ x ≤ β * γ := mul_le_mul_of_nonneg_left (h.conv_le x) hβ
    have h2 := (le_abs_self _).trans (ht x)
    linarith
  integrable_φ := by
    refine integrable_of_abs_le ((h.measurable_conv.const_mul β).add (measurable_const.inner h.measurable_Xi))
      (β * γ + 1) fun x => ?_
    have h1 : 0 ≤ β * convMeasure q μ x := mul_nonneg hβ (h.conv_nonneg x)
    have h1' : β * convMeasure q μ x ≤ β * γ := mul_le_mul_of_nonneg_left (h.conv_le x) hβ
    have h2 := ht x
    rw [abs_le] at h2 ⊢
    constructor <;> linarith [h2.1, h2.2]
  neg_le_integral_φ := by
    have hi1 : Integrable (fun x => β * convMeasure q μ x) μ :=
      integrable_of_abs_le (h.measurable_conv.const_mul β) (β * γ) fun x => by
        rw [abs_of_nonneg (mul_nonneg hβ (h.conv_nonneg x))]
        exact mul_le_mul_of_nonneg_left (h.conv_le x) hβ
    have hi2 : Integrable (fun x => inner ℝ t (Xi μ Ψ x)) μ :=
      integrable_of_abs_le (measurable_const.inner h.measurable_Xi) 1 ht
    rw [integral_add hi1 hi2, integral_inner h.integrable_Xi t, h.integral_Xi]
    have : 0 ≤ ∫ x, β * convMeasure q μ x ∂μ :=
      integral_nonneg fun x => mul_nonneg hβ (h.conv_nonneg x)
    simpa using this
  integrable_q := h.q_int
  row_le := h.q_row

theorem fieldLaw_eq_tilted {V : WeakPotential μ} {ψ : Torus d → ℝ} {lam : ℝ} {n : ℕ}
    (hint : Integrable (fun y : Fin n → Torus d => Real.exp (∑ i, ψ (y i) - lam * pairEnergy V y))
      (Measure.pi fun _ : Fin n => μ)) :
    fieldLaw V ψ lam n = (Measure.pi fun _ : Fin n => μ).tilted
      (fun y => ∑ i, ψ (y i) - lam * pairEnergy V y) := by
  have hZ : ENNReal.ofReal (∫ y, Real.exp (∑ i, ψ (y i) - lam * pairEnergy V y)
      ∂(Measure.pi fun _ : Fin n => μ)) = fieldNorm V ψ lam n := by
    unfold fieldNorm fieldWeight
    exact ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have hZpos := integral_exp_pos (μ := Measure.pi fun _ : Fin n => μ)
    (f := fun y : Fin n → Torus d => ∑ i, ψ (y i) - lam * pairEnergy V y) hint
  unfold fieldLaw Measure.tilted
  congr 1
  funext y
  unfold fieldDensity fieldWeight
  rw [ENNReal.ofReal_div_of_pos hZpos, hZ, div_eq_mul_inv]

theorem RefHyp.RN_eq_fieldLaw (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β)
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1) :
    RN q μ Ψ β N = fieldLaw (weakPot h hβ (tN q μ Ψ β N) ht) (weakPot h hβ (tN q μ Ψ β N) ht).φ
      (β / N) N := by
  rw [h.RN_eq_tilted hβ, fieldLaw_eq_tilted]
  · congr 1
    funext X
    simp only [E0, Yf, weakPot, pairEnergy, Finset.sum_add_distrib]
    ring
  · have := h.integrable_exp_E0_Yf hβ N (tN q μ Ψ β N)
    convert this using 2 with X
    simp only [E0, Yf, weakPot, pairEnergy, Finset.sum_add_distrib]
    ring_nf

/-- Smallness hypothesis of Wu's inequality for `R_N`: `κ = 4 e^{M+M'+βγ} βγ ≤ 1/2` with `M = βγ + 1`,
`M' = 0` (this is `A:eq:weak-dobrushin`, the "choose `τ` then `L`" step). -/
def KappaSmall (β γ : ℝ) : Prop := 4 * Real.exp (2 * (β * γ) + 1) * (β * γ) ≤ 1 / 2

/-- **`A:eq:weak-linear` for `R_N`**: `Var_{R_N}(∑_i f(x_i)) ≤ 2N Var_π(f)`, `π` the one-point marginal. -/
theorem RefHyp.var_sum_le (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N)
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β γ)
    [NeZero N] (f : Torus d → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    variance (fun X : Config d N => ∑ i, f (X i)) (RN q μ Ψ β N) ≤
      2 * N * variance f ((RN q μ Ψ β N).map (fun X => X 0)) := by
  obtain ⟨V, hV⟩ : ∃ V : WeakPotential μ, V = weakPot h hβ.le (tN q μ Ψ β N) ht := ⟨_, rfl⟩
  have hRN := h.RN_eq_fieldLaw hβ.le ht
  rw [← hV] at hRN
  haveI : IsProbabilityMeasure (RN q μ Ψ β N) := by
    unfold RN
    haveI := h.isProb_R0 hβ.le N
    exact h.isProb_tilted_Yf hβ.le _
  have hpin : pinnedLaw V (β / N) N (fun e : Empty => e.elim) = RN q μ Ψ β N := by
    rw [hRN]
    unfold pinnedLaw
    congr 1
    funext z
    simp [pinField]
  have hκ' : weakKappa V β ≤ 1 / 2 := by
    have e : weakKappa V β = 4 * Real.exp ((β * γ + 1) + 0 + β * γ) * (β * γ) := by
      rw [hV]; rfl
    rw [e]
    have : (β * γ + 1) + 0 + β * γ = 2 * (β * γ) + 1 := by ring
    rw [this]
    exact hκ
  have key := weak_linear_variance_symm (B := Empty) (n := N) V hβ.le hN (by simp)
    (fun e => e.elim) hκ' f hf
  rw [hpin] at key
  have hF : Measurable fun X : Config d N => ∑ i, f (X i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have hm0 : Measurable (fun X : Config d N => X 0) := measurable_pi_apply 0
  have hf2 : MemLp f 2 ((RN q μ Ψ β N).map (fun X => X 0)) :=
    MemLp.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hF2 : MemLp (fun X : Config d N => ∑ i, f (X i)) 2 (RN q μ Ψ β N) :=
    MemLp.of_bound hF.aestronglyMeasurable (N * B)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        calc |∑ i, f (X i)| ≤ ∑ i, |f (X i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hB _
          _ = N * B := by simp)
  rw [← ofReal_variance hf2, ← ofReal_variance hF2] at key
  have h0 : 0 ≤ 2 * (N : ℝ) * variance f ((RN q μ Ψ β N).map (fun X => X 0)) :=
    mul_nonneg (by positivity) (variance_nonneg _ _)
  have e : (2 : ℝ≥0∞) * N * ENNReal.ofReal (variance f ((RN q μ Ψ β N).map (fun X => X 0))) =
      ENNReal.ofReal (2 * N * variance f ((RN q μ Ψ β N).map (fun X => X 0))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [e, ENNReal.ofReal_le_ofReal_iff h0] at key
  exact key

/-! ### The trace bound `∫ |S_N - √N Ξ̄_N|² dR_N ≤ 8 g_L(0)` -/

theorem coord_empXi (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) {N : ℕ}
    (X : Config d N) (m : Fin M) :
    (empXi μ Ψ X).ofLp m = (1 / (N : ℝ)) * ∑ i, (Xi μ Ψ (X i)).ofLp m := by
  simp [empXi]

theorem RefHyp.coord_Xibar (h : RefHyp μ q gL Ψ γ) (hN : 0 < N) {P : Measure (Config d N)}
    [IsProbabilityMeasure P] (m : Fin M) :
    (∫ X, empXi μ Ψ X ∂P).ofLp m = ∫ X, (empXi μ Ψ X).ofLp m ∂P := by
  have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) m)
    (h.integrable_empXi hN P)
  simpa using this.symm

theorem RefHyp.norm_Dv_le (h : RefHyp μ q gL Ψ γ) (hN : 0 < N) (v : EuclideanSpace ℝ (Fin M))
    (X : Config d N) :
    ‖Sstat μ Ψ X - Real.sqrt N • v‖ ≤ Real.sqrt N * (2 * Real.sqrt (gL 0) + ‖v‖) := by
  unfold Sstat
  calc ‖Real.sqrt N • empXi μ Ψ X - Real.sqrt N • v‖ ≤
      ‖Real.sqrt N • empXi μ Ψ X‖ + ‖Real.sqrt N • v‖ := norm_sub_le _ _
    _ = Real.sqrt N * ‖empXi μ Ψ X‖ + Real.sqrt N * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt N * (2 * Real.sqrt (gL 0)) + Real.sqrt N * ‖v‖ := by
        gcongr
        exact h.norm_empXi_le hN X
    _ = _ := by ring

section Trace

variable [NeZero N]

theorem RefHyp.integral_coord_sq_le (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N)
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β γ) (m : Fin M) :
    ∫ X, ((Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N).ofLp m) ^ 2 ∂(RN q μ Ψ β N) ≤
      2 * ∫ X, ((Xi μ Ψ (X 0)).ofLp m) ^ 2 ∂(RN q μ Ψ β N) := by
  haveI : IsProbabilityMeasure (RN q μ Ψ β N) := by
    unfold RN
    haveI := h.isProb_R0 hβ.le N
    exact h.isProb_tilted_Yf hβ.le _
  set Pn := RN q μ Ψ β N with hR
  set g : Torus d → ℝ := fun x => (Xi μ Ψ x).ofLp m with hg
  have hgm : Measurable g := (EuclideanSpace.proj (𝕜 := ℝ) m).continuous.measurable.comp h.measurable_Xi
  have hgb : ∀ x, |g x| ≤ 2 * Real.sqrt (gL 0) := fun x =>
    (PiLp.norm_apply_le (Xi μ Ψ x) m).trans (h.norm_Xi_le x)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set G : Config d N → ℝ := fun X => ∑ i, g (X i) with hG
  have hGm : Measurable G := Finset.measurable_sum _ fun j _ => hgm.comp (measurable_pi_apply j)
  have hGb : ∀ X, |G X| ≤ N * (2 * Real.sqrt (gL 0)) := fun X =>
    (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc ∑ i, |g (X i)| ≤ ∑ _i : Fin N, 2 * Real.sqrt (gL 0) := Finset.sum_le_sum fun i _ => hgb _
        _ = _ := by simp)
  have hE : ∀ X, ((Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N).ofLp m) =
      Real.sqrt N * ((1 / (N : ℝ)) * G X - ∫ Y, (1 / (N : ℝ)) * G Y ∂Pn) := by
    intro X
    have e1 : (Xibar q μ Ψ β N).ofLp m = ∫ Y, (1 / (N : ℝ)) * G Y ∂Pn := by
      unfold Xibar
      rw [h.coord_Xibar hN]
      refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
      simp only [coord_empXi, hG, hg]
    unfold Sstat
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, coord_empXi, hG, hg] at e1 ⊢
    rw [e1]
    ring
  have hvar := h.var_sum_le hβ hN ht hκ g hgm _ hgb
  have hint1 : ∫ X, ((Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N).ofLp m) ^ 2 ∂Pn =
      N * variance (fun X => (1 / (N : ℝ)) * G X) Pn := by
    rw [variance_eq_integral ((hGm.const_mul _).aemeasurable)]
    simp_rw [hE, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    rw [integral_const_mul]
  have hvar2 : variance (fun X => (1 / (N : ℝ)) * G X) Pn = (1 / (N : ℝ)) ^ 2 * variance G Pn :=
    variance_const_mul _ _ _
  have hπ : variance g (Pn.map (fun X => X 0)) ≤ ∫ X, (g (X 0)) ^ 2 ∂Pn := by
    have := variance_le_expectation_sq (μ := Pn.map (fun X : Config d N => X 0)) (X := g)
      hgm.aestronglyMeasurable
    refine this.trans (le_of_eq ?_)
    rw [integral_map (measurable_pi_apply 0).aemeasurable (hgm.pow_const 2).aestronglyMeasurable]
    rfl
  rw [hint1, hvar2]
  have hv0 : 0 ≤ variance g (Pn.map (fun X => X 0)) := variance_nonneg _ _
  calc (N : ℝ) * ((1 / (N : ℝ)) ^ 2 * variance G Pn) ≤
      (N : ℝ) * ((1 / (N : ℝ)) ^ 2 * (2 * N * variance g (Pn.map (fun X => X 0)))) := by
        gcongr
    _ = 2 * variance g (Pn.map (fun X => X 0)) := by field_simp
    _ ≤ 2 * ∫ X, (g (X 0)) ^ 2 ∂Pn := by linarith

theorem RefHyp.trace_le (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N)
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β γ) :
    ∫ X, ‖Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N‖ ^ 2 ∂(RN q μ Ψ β N) ≤ 8 * gL 0 := by
  haveI : IsProbabilityMeasure (RN q μ Ψ β N) := by
    unfold RN
    haveI := h.isProb_R0 hβ.le N
    exact h.isProb_tilted_Yf hβ.le _
  set Pn := RN q μ Ψ β N with hR
  set C := Real.sqrt N * (2 * Real.sqrt (gL 0) + ‖Xibar q μ Ψ β N‖) with hC
  have hDm : ∀ m : Fin M, Measurable fun X : Config d N =>
      ((Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N).ofLp m) ^ 2 := fun m =>
    (((EuclideanSpace.proj (𝕜 := ℝ) m).continuous.measurable.comp
      ((h.measurable_Sstat (N := N)).sub measurable_const))).pow_const 2
  have hDi : ∀ m : Fin M, Integrable (fun X : Config d N =>
      ((Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N).ofLp m) ^ 2) Pn := fun m =>
    integrable_of_abs_le (hDm m) (C ^ 2) fun X => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have h1 := (PiLp.norm_apply_le (Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N) m).trans
        (h.norm_Dv_le hN (Xibar q μ Ψ β N) X)
      have h2 : |(Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N).ofLp m| ≤ C := by
        simpa using h1
      exact sq_le_sq' (by linarith [abs_le.1 h2]) (by linarith [abs_le.1 h2])
  have hgi : ∀ m : Fin M, Integrable (fun X : Config d N => ((Xi μ Ψ (X 0)).ofLp m) ^ 2) Pn := fun m =>
    integrable_of_abs_le ((((EuclideanSpace.proj (𝕜 := ℝ) m).continuous.measurable.comp
      (h.measurable_Xi.comp (measurable_pi_apply 0))).pow_const 2)) ((2 * Real.sqrt (gL 0)) ^ 2) fun X => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have h1 := (PiLp.norm_apply_le (Xi μ Ψ (X 0)) m).trans (h.norm_Xi_le (X 0))
      have h0 := norm_nonneg ((Xi μ Ψ (X 0)).ofLp m)
      simp only [Real.norm_eq_abs] at h1
      calc ((Xi μ Ψ (X 0)).ofLp m) ^ 2 = |(Xi μ Ψ (X 0)).ofLp m| ^ 2 := (sq_abs _).symm
        _ ≤ _ := by gcongr
  have e1 : ∀ X : Config d N, ‖Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N‖ ^ 2 =
      ∑ m, ((Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N).ofLp m) ^ 2 := by
    intro X
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have e2 : ∀ X : Config d N, ‖Xi μ Ψ (X 0)‖ ^ 2 = ∑ m, ((Xi μ Ψ (X 0)).ofLp m) ^ 2 := by
    intro X
    rw [EuclideanSpace.norm_sq_eq]
    simp
  simp_rw [e1]
  rw [integral_finsetSum _ fun m _ => hDi m]
  have h3 : ∑ m : Fin M, ∫ X, ((Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N).ofLp m) ^ 2 ∂Pn ≤
      ∑ m : Fin M, 2 * ∫ X, ((Xi μ Ψ (X 0)).ofLp m) ^ 2 ∂Pn :=
    Finset.sum_le_sum fun m _ => h.integral_coord_sq_le hβ hN ht hκ m
  refine h3.trans ?_
  rw [← Finset.mul_sum, ← integral_finsetSum _ fun m _ => hgi m]
  simp_rw [← e2]
  have h4 : ∫ X, ‖Xi μ Ψ (X 0)‖ ^ 2 ∂Pn ≤ 4 * gL 0 := by
    have : ∀ X : Config d N, ‖Xi μ Ψ (X 0)‖ ^ 2 ≤ 4 * gL 0 := fun X => by
      have h1 := h.norm_Xi_le (X 0)
      have h0 := norm_nonneg (Xi μ Ψ (X 0))
      calc ‖Xi μ Ψ (X 0)‖ ^ 2 ≤ (2 * Real.sqrt (gL 0)) ^ 2 := by gcongr
        _ = 4 * gL 0 := by rw [mul_pow, Real.sq_sqrt h.gL_zero_nonneg]; ring
    calc ∫ X, ‖Xi μ Ψ (X 0)‖ ^ 2 ∂Pn ≤ ∫ _X, 4 * gL 0 ∂Pn := by
          refine integral_mono (by simpa [e2] using integrable_finset_sum _ fun m _ => hgi m)
            (integrable_const _) this
      _ = 4 * gL 0 := by simp
  linarith

end Trace

end WuApp


/-! ### The bounded transfer and the variance transfer (`A:eq:bounded-transfer`, `A:eq:variance-transfer`) -/

section Transfer

variable [IsProbabilityMeasure μ] {q gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)}
  {γ : ℝ} {β : ℝ} {N : ℕ}

/-- The smallness hypothesis `‖t_N·Ξ‖_∞ ≤ 1`, in coordinates, gives the form used above. -/
theorem abs_inner_le_of_sum {t : EuclideanSpace ℝ (Fin M)} {x : Torus d}
    (hs : |∑ m, t.ofLp m * (Xi μ Ψ x).ofLp m| ≤ 1) : |inner ℝ t (Xi μ Ψ x)| ≤ 1 := by
  rwa [inner_eq_sum]

theorem RefHyp.isProb_RN (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (RN q μ Ψ β N) := by
  unfold RN
  haveI := h.isProb_R0 hβ N
  exact h.isProb_tilted_Yf hβ _

theorem RefHyp.measurable_logW (h : RefHyp μ q gL Ψ γ) :
    Measurable (logW q μ Ψ β N) := by
  unfold logW
  exact (((h.measurable_Sstat (N := N)).sub measurable_const).norm.pow_const 2).const_mul _

theorem RefHyp.logW_nonpos (hβ : 0 < β) (X : Config d N) : logW q μ Ψ β N X ≤ 0 := by
  unfold logW
  have : 0 ≤ (β / 2) * ‖Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N‖ ^ 2 := by positivity
  linarith

theorem RefHyp.integrable_logW (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N)
    {P : Measure (Config d N)} [IsFiniteMeasure P] :
    Integrable (logW q μ Ψ β N) P := by
  set C := Real.sqrt N * (2 * Real.sqrt (gL 0) + ‖Xibar q μ Ψ β N‖) with hC
  refine integrable_of_abs_le h.measurable_logW ((β / 2) * C ^ 2) fun X => ?_
  have h1 := h.norm_Dv_le hN (Xibar q μ Ψ β N) X
  have h0 := norm_nonneg (Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N)
  unfold logW
  rw [abs_of_nonpos (by have : 0 ≤ (β / 2) * ‖Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N‖ ^ 2 := by positivity
                        linarith)]
  have : ‖Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N‖ ^ 2 ≤ C ^ 2 := by gcongr
  nlinarith

theorem RefHyp.integrable_exp_logW (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β)
    {P : Measure (Config d N)} [IsFiniteMeasure P] :
    Integrable (fun X => Real.exp (logW q μ Ψ β N X)) P :=
  integrable_of_abs_le (Real.measurable_exp.comp h.measurable_logW) 1 fun X => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (RefHyp.logW_nonpos hβ X)

/-- **Denominator bound** (Jensen + Wu): `E_{R_N}[e^{-β|S_N-√NΞ̄_N|²/2}] ≥ e^{-4β g_L(0)}`. -/
theorem RefHyp.exp_le_integral_exp_logW (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N)
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β γ) :
    Real.exp (-(4 * β * gL 0)) ≤ ∫ X, Real.exp (logW q μ Ψ β N X) ∂(RN q μ Ψ β N) := by
  haveI := h.isProb_RN (N := N) hβ.le
  haveI : NeZero N := ⟨hN.ne'⟩
  have hJ := log_integral_exp_ge (h.integrable_logW hβ hN (P := RN q μ Ψ β N))
    (h.integrable_exp_logW hβ (P := RN q μ Ψ β N))
  have hpos := integral_exp_pos (μ := RN q μ Ψ β N) (f := logW q μ Ψ β N)
    (h.integrable_exp_logW hβ)
  have htr := h.trace_le hβ hN ht hκ
  have hint : ∫ X, logW q μ Ψ β N X ∂(RN q μ Ψ β N) =
      -(β / 2) * ∫ X, ‖Sstat μ Ψ X - Real.sqrt N • Xibar q μ Ψ β N‖ ^ 2 ∂(RN q μ Ψ β N) := by
    unfold logW
    rw [integral_const_mul]
  have : -(4 * β * gL 0) ≤ ∫ X, logW q μ Ψ β N X ∂(RN q μ Ψ β N) := by
    rw [hint]
    nlinarith
  exact (Real.le_log_iff_exp_le hpos).1 (this.trans hJ)

/-- **`A:eq:bounded-transfer`, pointwise**: the density `e^{ψ}/E_{R_N}[e^{ψ}]` is `≤ e^{4β g_L(0)}`. -/
theorem RefHyp.density_le (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N)
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β γ) (X : Config d N) :
    Real.exp (logW q μ Ψ β N X) / ∫ Y, Real.exp (logW q μ Ψ β N Y) ∂(RN q μ Ψ β N) ≤
      Real.exp (4 * β * gL 0) := by
  have hlow := h.exp_le_integral_exp_logW hβ hN ht hκ
  have hpos : 0 < Real.exp (-(4 * β * gL 0)) := Real.exp_pos _
  have h1 : Real.exp (logW q μ Ψ β N X) ≤ 1 := Real.exp_le_one_iff.2 (RefHyp.logW_nonpos hβ X)
  rw [div_le_iff₀ (hpos.trans_le hlow)]
  calc Real.exp (logW q μ Ψ β N X) ≤ 1 := h1
    _ = Real.exp (4 * β * gL 0) * Real.exp (-(4 * β * gL 0)) := by rw [← Real.exp_add]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le

/-- **`A:eq:bounded-transfer`** (`dQ/dR_N ≤ C`), with `C = e^{4β g_L(0)}`; `Q_{N,β}(μ)` is the modulated
Gibbs measure of the split kernel `g_L + q - c`. Hypothesis `hsmall`: `‖t_N·Ξ‖_∞ ≤ 1`. -/
theorem RefHyp.Q_le_smul_RN (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N) (c : ℝ)
    (hsmall : ∀ x, |∑ m, (tN q μ Ψ β N).ofLp m * (Xi μ Ψ x).ofLp m| ≤ 1) (hκ : KappaSmall β γ) :
    modulatedGibbs (gTot gL q c) N β μ ≤
      ENNReal.ofReal (Real.exp (4 * β * gL 0)) • RN q μ Ψ β N := by
  have ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1 := fun x => abs_inner_le_of_sum (hsmall x)
  haveI := h.isProb_RN (N := N) hβ.le
  rw [h.Q_eq_RN_withDensity hβ hN c]
  intro s
  rw [withDensity_apply' _ s, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in s, ENNReal.ofReal (Real.exp (logW q μ Ψ β N x) /
        ∫ Y, Real.exp (logW q μ Ψ β N Y) ∂(RN q μ Ψ β N)) ∂(RN q μ Ψ β N)
      ≤ ∫⁻ _x in s, ENNReal.ofReal (Real.exp (4 * β * gL 0)) ∂(RN q μ Ψ β N) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (h.density_le hβ hN ht hκ x)
    _ = _ := by rw [setLIntegral_const]

/-- **`A:eq:variance-transfer`**: `Var_{Q_{N,β}(μ)}(F) ≤ C Var_{R_N}(F)`, `C = e^{4β g_L(0)}`
(for `F ∈ L²(R_N)`; the reference mean is used as the trial centering).  Hypothesis `hsmall`:
`‖t_N·Ξ‖_∞ ≤ 1`; `hκ`: `βγ` small (`KappaSmall`). -/
theorem RefHyp.variance_transfer (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N) (c : ℝ)
    (hsmall : ∀ x, |∑ m, (tN q μ Ψ β N).ofLp m * (Xi μ Ψ x).ofLp m| ≤ 1) (hκ : KappaSmall β γ)
    (F : Config d N → ℝ) (hF : MemLp F 2 (RN q μ Ψ β N)) :
    variance F (modulatedGibbs (gTot gL q c) N β μ) ≤
      Real.exp (4 * β * gL 0) * variance F (RN q μ Ψ β N) := by
  haveI := h.isProb_RN (N := N) hβ.le
  have hQ := h.Q_eq_RN_tilted hβ hN c
  have hle := h.Q_le_smul_RN hβ hN c hsmall hκ
  haveI hQp : IsProbabilityMeasure (modulatedGibbs (gTot gL q c) N β μ) := by
    rw [hQ]
    exact isProbabilityMeasure_tilted (h.integrable_exp_logW hβ)
  set P := RN q μ Ψ β N with hP
  set Q := modulatedGibbs (gTot gL q c) N β μ with hQdef
  set a := ∫ X, F X ∂P with ha
  have hac : Q ≪ P := by rw [hQ]; exact tilted_absolutelyContinuous _ _
  have hFQ : AEStronglyMeasurable F Q := hF.aestronglyMeasurable.mono_ac hac
  have h1 : variance F Q = variance (fun X => F X + (-a)) Q := (variance_add_const hFQ _).symm
  have h2 : variance (fun X => F X + (-a)) Q ≤ ∫ X, (F X + (-a)) ^ 2 ∂Q := by
    have := variance_le_expectation_sq (μ := Q) (X := fun X => F X + (-a))
      (hFQ.add aestronglyMeasurable_const)
    simpa using this
  have hsq : Integrable (fun X => (F X + (-a)) ^ 2) P := by
    have := (hF.sub (memLp_const a)).integrable_sq
    simpa [sub_eq_add_neg] using this
  have h3 : ∫ X, (F X + (-a)) ^ 2 ∂Q ≤ Real.exp (4 * β * gL 0) * ∫ X, (F X + (-a)) ^ 2 ∂P := by
    have hsq' : Integrable (fun X => (F X + (-a)) ^ 2) (ENNReal.ofReal (Real.exp (4 * β * gL 0)) • P) :=
      hsq.smul_measure ENNReal.ofReal_ne_top
    calc ∫ X, (F X + (-a)) ^ 2 ∂Q ≤ ∫ X, (F X + (-a)) ^ 2 ∂(ENNReal.ofReal (Real.exp (4 * β * gL 0)) • P) :=
          integral_mono_measure hle (Filter.Eventually.of_forall fun X => sq_nonneg _) hsq'
      _ = _ := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have h4 : ∫ X, (F X + (-a)) ^ 2 ∂P = variance F P := by
    rw [variance_eq_integral hF.aemeasurable]
    simp [sub_eq_add_neg, ha]
  rw [h1]
  refine h2.trans (h3.trans ?_)
  rw [h4]

end Transfer

/-! ### Bridge to the heat split and to the Riesz kernel -/

section Bridge

/-- For an atomless probability `μ`, the coordinates of `μ^{⊗N}` are a.s. pairwise distinct. -/
theorem ae_distinct_pi [IsProbabilityMeasure μ] (hatom : ∀ x : Torus d, μ {x} = 0) (N : ℕ) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ i j : Fin N, i ≠ j → X i ≠ X j := by
  have hm : ∀ k : Fin N,
      (Measure.pi fun _ : Fin N => μ).map (fun X : Fin N → Torus d => X k) = μ := fun k =>
    (measurePreserving_eval (fun _ : Fin N => μ) k).map_eq
  have hpair : ∀ i j : Fin N, i ≠ j → ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), X i ≠ X j := by
    intro i j hij
    have hind : ProbabilityTheory.IndepFun (fun X : Fin N → Torus d => X i) (fun X : Fin N → Torus d => X j)
        (Measure.pi fun _ : Fin N => μ) :=
      (ProbabilityTheory.iIndepFun_pi (X := fun _ : Fin N => (id : Torus d → Torus d))
        (μ := fun _ : Fin N => μ) (fun _ => aemeasurable_id)).indepFun hij
    have hmap : (Measure.pi fun _ : Fin N => μ).map
        (fun X : Fin N → Torus d => (X i, X j)) = μ.prod μ := by
      have hEq := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable).mp hind
      rw [hEq, hm i, hm j]
    have hD : MeasurableSet {p : Torus d × Torus d | p.1 = p.2} :=
      isClosed_diagonal.measurableSet
    have hnull : (μ.prod μ) {p : Torus d × Torus d | p.1 = p.2} = 0 := by
      rw [Measure.measure_prod_null hD]
      refine ae_of_all _ fun x => ?_
      have hx : Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 = p.2} = {x} := by
        ext y
        exact eq_comm
      show μ (Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 = p.2}) = 0
      rw [hx]
      exact hatom x
    have hnull' : (Measure.pi fun _ : Fin N => μ)
        ((fun X : Fin N → Torus d => (X i, X j)) ⁻¹' {p : Torus d × Torus d | p.1 = p.2}) = 0 := by
      rw [← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hD,
        hmap, hnull]
    rw [ae_iff]
    exact measure_mono_null (fun X hX => not_not.mp hX) hnull'
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · exact ae_of_all _ fun X h => absurd hij h
  · exact (hpair i j hij).mono fun X hX _ => hX

/-- The modulated Gibbs measure depends only on the values of the kernel off the origin
(for an atomless background). -/
theorem modulatedGibbs_congr [IsProbabilityMeasure μ] (hatom : ∀ x : Torus d, μ {x} = 0)
    {g₁ g₂ : Torus d → ℝ} (hg : ∀ x, x ≠ 0 → g₁ x = g₂ x) (N : ℕ) (β : ℝ) :
    modulatedGibbs g₁ N β μ = modulatedGibbs g₂ N β μ := by
  have hint : ∀ x : Torus d, ∫ y, g₁ (x - y) ∂μ = ∫ y, g₂ (x - y) ∂μ := by
    intro x
    refine integral_congr_ae ?_
    have : ∀ᵐ y ∂μ, y ≠ x := by
      rw [ae_iff]
      simpa using hatom x
    filter_upwards [this] with y hy
    exact hg _ (sub_ne_zero.2 (Ne.symm hy))
  have hF : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ),
      modulatedEnergyKernel g₁ X μ = modulatedEnergyKernel g₂ X μ := by
    filter_upwards [ae_distinct_pi hatom N] with X hX
    unfold modulatedEnergyKernel modulatedEnergy
    have e1 : ∑ i, ∑ j ∈ Finset.univ.erase i, g₁ (X i - X j) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, g₂ (X i - X j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      exact hg _ (sub_ne_zero.2 (hX i j (Finset.ne_of_mem_erase hj).symm))
    simp only [hint, e1]
  have hZ : gibbsNormalizer g₁ N β μ = gibbsNormalizer g₂ N β μ := by
    unfold gibbsNormalizer
    refine integral_congr_ae ?_
    filter_upwards [hF] with X hX
    rw [hX]
  unfold modulatedGibbs
  rw [hZ]
  congr 1
  refine withDensity_congr_ae ?_
  filter_upwards [hF] with X hX
  rw [hX]

open HeatSplit in
theorem hQ_even {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (τ : ℝ) (L : ℕ) (x : Torus d) :
    hQ d s τ L (-x) = hQ d s τ L x := by
  unfold hQ hNear hRest
  simp only [Repulsive.psiFn_neg, StaticLimitAux.cosMode_neg_arg]

theorem continuous_features {gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)}
    (hc : Continuous gL) (hΨ : ∀ x y, gL (x - y) = inner ℝ (Ψ x) (Ψ y)) : Continuous Ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hn : ∀ y, ‖Ψ y‖ ^ 2 = gL 0 := fun y => by
    have := hΨ y y
    rw [sub_self, real_inner_self_eq_norm_sq] at this
    exact this.symm
  have e : (fun y => ‖Ψ y - Ψ x‖) = fun y => Real.sqrt (2 * (gL 0 - gL (y - x))) := by
    funext y
    rw [← Real.sqrt_sq (norm_nonneg (Ψ y - Ψ x)), norm_sub_sq_real, hn, hn, ← hΨ y x]
    congr 1
    ring
  rw [e]
  have hcont : Continuous fun y => Real.sqrt (2 * (gL 0 - gL (y - x))) := by
    have : Continuous fun y : Torus d => gL (y - x) := hc.comp (continuous_id.sub continuous_const)
    fun_prop
  have := hcont.tendsto x
  have h0 : Real.sqrt (2 * (gL 0 - gL (x - x))) = 0 := by simp
  rwa [h0] at this

open HeatSplit in
/-- The weak split of `HeatSplit` satisfies the standing hypotheses `RefHyp` for `μ = ρ dx`
(`ρ` a probability density bounded by `Λ`), with row bound `γ = Λ c`; the features `Ψ` are any
features of `g_L` (`g_L(x - y) = ⟪Ψ x, Ψ y⟫`, e.g. those of `weakSplit_spec`). -/
theorem refHyp_weakSplit {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ}
    (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    RefHyp (withDensityReal ρ) (weakSplit d s τ L).q (weakSplit d s τ L).gL Ψ
      (Λ * (weakSplit d s τ L).c) := by
  obtain ⟨-, -, -, -, h5, h6, h7, h8, -, -, -, -, h13, -, -, h16, h17⟩ :=
    weakSplit_spec hd hs0 hsd hτ hτ1 L
  haveI : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  have hqint : ∀ x : Torus d, Integrable (fun y : Torus d => (weakSplit d s τ L).q (x - y)) volume :=
    fun x => h7.comp_sub_left x
  have hΛ0 : 0 ≤ Λ := (hρ.nonneg 0).trans (hρΛ 0)
  refine ⟨h5, h6, fun x => hQ_even hd hs0 hsd τ L x, ?_, ?_,
    (continuous_features h13 hΨ).measurable, hΨ⟩
  · intro x
    have hmeas : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρ.measurable
    unfold withDensityReal
    rw [integrable_withDensity_iff_integrable_smul' hmeas (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
    have e : (fun y => (ENNReal.ofReal (ρ y)).toReal • (weakSplit d s τ L).q (x - y)) =
        fun y => ρ y * (weakSplit d s τ L).q (x - y) := by
      funext y
      simp [ENNReal.toReal_ofReal (hρ.nonneg y)]
    rw [e]
    refine Integrable.mono' ((hqint x).mul_const Λ)
      ((hρ.measurable.mul (h5.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    have h1 := mul_le_mul_of_nonneg_left (hρΛ y) (h6 (x - y))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg y) (h6 (x - y)))]
    linarith [mul_comm (ρ y) ((weakSplit d s τ L).q (x - y))]
  · intro x
    rw [integral_withDensityReal_eq ρ hρ.measurable hρ.nonneg]
    have := h17 ρ Λ hρ.measurable hρ.nonneg hρΛ x
    simpa [mul_comm] using this

open HeatSplit in
theorem atomless_withDensityReal (hd : 1 ≤ d) (ρ : Torus d → ℝ) (x : Torus d) :
    withDensityReal ρ {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (volume_singleton_torus hd x)

open HeatSplit in
/-- `Q_{N,β}(μ)` for the periodic Riesz kernel equals the modulated Gibbs measure of the split kernel
`g_L + q - c` (they differ only at the origin, a null set). -/
theorem modulatedGibbs_riesz_eq_split {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (N : ℕ) (β : ℝ) :
    modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) =
      modulatedGibbs (gTot (weakSplit d s τ L).gL (weakSplit d s τ L).q (weakSplit d s τ L).c) N β
        (withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  refine modulatedGibbs_congr (atomless_withDensityReal (by omega) ρ) (fun x hx => ?_) N β
  obtain ⟨-, -, h3, -⟩ := weakSplit_spec hd hs0 hsd hτ hτ1 L
  exact h3 x hx

end Bridge

section Final

open HeatSplit

/-- **`A:eq:bounded-transfer` for the Riesz kernel**: `dQ_{N,β}(μ)/dR_N ≤ e^{4β g_L(0)}` for the modulated
Gibbs measure `Q_{N,β}(μ)` of `g = periodicRiesz d s` and the calibrated weak reference `R_N`
built from the heat split at `(τ, L)`.  Hypotheses: `hκ` (smallness of `βγ`, `γ = Λ c`) and
`hsmall : ‖t_N·Ξ‖_∞ ≤ 1` (the smallness fact of EXT-5). -/
theorem riesz_Q_le_smul_RN {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ}
    (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y))
    {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N)
    (hκ : KappaSmall β (Λ * (weakSplit d s τ L).c))
    (hsmall : ∀ x, |∑ m, (tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N).ofLp m *
      (Xi (withDensityReal ρ) Ψ x).ofLp m| ≤ 1) :
    modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) ≤
      ENNReal.ofReal (Real.exp (4 * β * (weakSplit d s τ L).gL 0)) •
        RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N := by
  haveI := isProb_withDensityReal hρ
  rw [modulatedGibbs_riesz_eq_split hd hs0 hsd hτ hτ1 L hρ]
  exact (refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ).Q_le_smul_RN hβ hN _ hsmall hκ

/-- **`A:eq:bounded-transfer`, exact density** for the Riesz kernel:
`Q_{N,β}(μ)` is `R_N` tilted by `-(β/2)|S_N - √N Ξ̄_N|²`. -/
theorem riesz_Q_eq_RN_tilted {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ}
    (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y))
    {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) =
      (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N).tilted
        (logW (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) := by
  haveI := isProb_withDensityReal hρ
  rw [modulatedGibbs_riesz_eq_split hd hs0 hsd hτ hτ1 L hρ]
  exact (refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ).Q_eq_RN_tilted hβ hN _

/-- **`A:eq:variance-transfer` for the Riesz kernel**: `Var_Q(F) ≤ e^{4β g_L(0)} Var_{R_N}(F)`. -/
theorem riesz_variance_transfer {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ}
    (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y))
    {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N)
    (hκ : KappaSmall β (Λ * (weakSplit d s τ L).c))
    (hsmall : ∀ x, |∑ m, (tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N).ofLp m *
      (Xi (withDensityReal ρ) Ψ x).ofLp m| ≤ 1)
    (F : Config d N → ℝ) (hF : MemLp F 2 (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)) :
    variance F (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
      Real.exp (4 * β * (weakSplit d s τ L).gL 0) *
        variance F (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) := by
  haveI := isProb_withDensityReal hρ
  rw [modulatedGibbs_riesz_eq_split hd hs0 hsd hτ hτ1 L hρ]
  exact (refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ).variance_transfer hβ hN _ hsmall hκ F hF

end Final

end Basic

end Calib

end HRS.External

end
