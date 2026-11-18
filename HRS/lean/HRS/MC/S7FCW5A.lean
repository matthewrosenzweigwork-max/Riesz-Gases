import HRS.MC.QRPWickLimAux2
import HRS.Sections.Q41Aux12

/-!
# S7FCW5 (auxiliary): finite-section estimates and joint measurability for the Wick limit (FC-C2)

Helpers for `HRS/MC/S7FCW5.lean` (the relocated proof of `s7_FC_C2_wick_param`).
* `S7FCW5_tail_nonneg`, `S7FCW5_tail_anti`: monotonicity of the Hilbert-Schmidt tail `tailHS` in the index set.
* `S7FCW5_sq_diff`: `L²` bound for `b - a` from `L²` bounds on `a` and `b`.
* `S7FCW5_pair`: for ANY two finite sets `S, S'`, `E (W_S - W_{S'})² ≤ K² (tail S + tail S')`, from
  `HRS.MC.QRSpec.Wick.qrpw_sect` applied to `S ⊆ S ∪ S'` and `S' ⊆ S ∪ S'`.
* joint measurability in `(t, ω)` of the finite sections `wickSection P (X t) (μ t) h S ω`.
* `S7FCW5_eLp_of_sq`: an `eLpNorm` bound from a bound on the second moment.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.S7FCW5

open HRS HRS.Sec7 HRS.MC.QRSpec

variable {d : ℕ}

lemma S7FCW5_enorm_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

lemma S7FCW5_half_pow_sq (N n : ℕ) (h : N ≤ n) : ((1 / 2 : ℝ) ^ n) ^ 2 ≤ ((1 / 2 : ℝ) ^ N) ^ 2 := by
  have h1 : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have h0 : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  nlinarith

open Classical in
lemma S7FCW5_tail_nonneg {ι : Type*} (a : ι → ι → ℝ) (F : Finset ι) : 0 ≤ tailHS a F := by
  unfold tailHS
  refine tsum_nonneg fun p => ?_
  split_ifs <;> positivity

/-- The Hilbert-Schmidt tail decreases when the index set grows (no `open Classical`: the `if`s of `tailHS`
are elaborated with its own decidability instances, so the proof works on the goal after `unfold`). -/
lemma S7FCW5_tail_anti (a : NonzeroLattice d → NonzeroLattice d → ℝ)
    (hs : Summable fun p : NonzeroLattice d × NonzeroLattice d => a p.1 p.2 ^ 2)
    {F S : Finset (NonzeroLattice d)} (hFS : F ⊆ S) : tailHS a S ≤ tailHS a F := by
  have key : ∀ p : NonzeroLattice d × NonzeroLattice d, p.1 ∈ F ∧ p.2 ∈ F → p.1 ∈ S ∧ p.2 ∈ S :=
    fun p hp => ⟨hFS hp.1, hFS hp.2⟩
  unfold tailHS
  refine Summable.tsum_le_tsum (fun p => ?_) ?_ ?_
  · split_ifs <;> first | exact le_rfl | positivity | exact absurd (key p ‹_›) ‹_›
  · exact Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity)
      (fun p => by split_ifs <;> first | positivity | exact le_rfl) hs
  · exact Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity)
      (fun p => by split_ifs <;> first | positivity | exact le_rfl) hs

lemma S7FCW5_sq_diff {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (a b : Ω → ℝ) (ha : MemLp a 2 P) (hb : MemLp b 2 P) (cA cB : ℝ)
    (hA : ∫ ω, a ω ^ 2 ∂P ≤ cA) (hB : ∫ ω, b ω ^ 2 ∂P ≤ cB) :
    MemLp (fun ω => b ω - a ω) 2 P ∧ ∫ ω, (b ω - a ω) ^ 2 ∂P ≤ 2 * cA + 2 * cB := by
  refine ⟨hb.sub ha, ?_⟩
  have hpt : ∀ ω, (b ω - a ω) ^ 2 ≤ 2 * a ω ^ 2 + 2 * b ω ^ 2 := fun ω => by
    nlinarith [sq_nonneg (a ω + b ω)]
  have e : ∫ ω, (2 * a ω ^ 2 + 2 * b ω ^ 2) ∂P = 2 * ∫ ω, a ω ^ 2 ∂P + 2 * ∫ ω, b ω ^ 2 ∂P := by
    rw [integral_add (ha.integrable_sq.const_mul 2) (hb.integrable_sq.const_mul 2),
      integral_const_mul, integral_const_mul]
  have hmono : ∫ ω, (b ω - a ω) ^ 2 ∂P ≤ ∫ ω, (2 * a ω ^ 2 + 2 * b ω ^ 2) ∂P :=
    integral_mono (hb.sub ha).integrable_sq ((ha.integrable_sq.const_mul 2).add
      (hb.integrable_sq.const_mul 2)) hpt
  linarith

open Classical in
/-- Two finite sections: `E (W_S - W_{S'})² ≤ K² (tail S + tail S')`, for ANY finite `S, S'`. -/
lemma S7FCW5_pair {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    {η : Ω → NegSobolev d r} (hη : HasFiniteGaussianCoeffs P η) {K : ℝ}
    (hK : ModeCovBound P η K) (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ)
    (hHS : Summable fun p : NonzeroLattice d × NonzeroLattice d => wickCoeff μ h p.1 p.2 ^ 2)
    (S S' : Finset (NonzeroLattice d)) :
    MemLp (fun ω => wickSection P η μ h S ω - wickSection P η μ h S' ω) 2 P ∧
    ∫ ω, (wickSection P η μ h S ω - wickSection P η μ h S' ω) ^ 2 ∂P ≤
      K ^ 2 * (tailHS (wickCoeff μ h) S + tailHS (wickCoeff μ h) S') := by
  obtain ⟨ha, hai⟩ := HRS.MC.QRSpec.Wick.qrpw_sect hη hK μ h hHS S (S ∪ S') Finset.subset_union_left
  obtain ⟨hb, hbi⟩ := HRS.MC.QRSpec.Wick.qrpw_sect hη hK μ h hHS S' (S ∪ S') Finset.subset_union_right
  have hfun : (fun ω => wickSection P η μ h S ω - wickSection P η μ h S' ω) =
      fun ω => (wickSection P η μ h (S ∪ S') ω - wickSection P η μ h S' ω) -
        (wickSection P η μ h (S ∪ S') ω - wickSection P η μ h S ω) := by
    funext ω; ring
  obtain ⟨h1, h2⟩ := S7FCW5_sq_diff (fun ω => wickSection P η μ h (S ∪ S') ω - wickSection P η μ h S ω)
    (fun ω => wickSection P η μ h (S ∪ S') ω - wickSection P η μ h S' ω) ha hb
    ((1 / 2) * K ^ 2 * tailHS (wickCoeff μ h) S) ((1 / 2) * K ^ 2 * tailHS (wickCoeff μ h) S') hai hbi
  have h2' : ∫ ω, ((wickSection P η μ h (S ∪ S') ω - wickSection P η μ h S' ω) -
      (wickSection P η μ h (S ∪ S') ω - wickSection P η μ h S ω)) ^ 2 ∂P ≤
      2 * ((1 / 2) * K ^ 2 * tailHS (wickCoeff μ h) S) +
        2 * ((1 / 2) * K ^ 2 * tailHS (wickCoeff μ h) S') := h2
  rw [hfun]
  refine ⟨h1, ?_⟩
  calc ∫ ω, (wickSection P η μ h S ω - wickSection P η μ h S' ω) ^ 2 ∂P
      = ∫ ω, ((wickSection P η μ h (S ∪ S') ω - wickSection P η μ h S' ω) -
          (wickSection P η μ h (S ∪ S') ω - wickSection P η μ h S ω)) ^ 2 ∂P := by
        congr 1; funext ω; ring
    _ ≤ 2 * ((1 / 2) * K ^ 2 * tailHS (wickCoeff μ h) S) +
        2 * ((1 / 2) * K ^ 2 * tailHS (wickCoeff μ h) S') := h2'
    _ = K ^ 2 * (tailHS (wickCoeff μ h) S + tailHS (wickCoeff μ h) S') := by ring

section Meas

variable {Ω : Type} [MeasurableSpace Ω] {r : ℝ}

lemma S7FCW5_coef_meas {X : ℝ → Ω → NegSobolev d r} (hXm : Measurable (Function.uncurry X))
    (k : NonzeroLattice d) :
    Measurable fun p : ℝ × Ω => NegSobolev.fourierCoeff (X p.1 p.2) k :=
  (HRS.Q41.q41_continuous_fourierCoeff r k).measurable.comp hXm

lemma S7FCW5_mean_meas (P : Measure Ω) [IsProbabilityMeasure P] {X : ℝ → Ω → NegSobolev d r}
    (hXm : Measurable (Function.uncurry X)) (k l : NonzeroLattice d) :
    Measurable fun t : ℝ => ∫ ω, NegSobolev.fourierCoeff (X t ω) k *
      NegSobolev.fourierCoeff (X t ω) l ∂P := by
  have hf : StronglyMeasurable fun p : ℝ × Ω =>
      NegSobolev.fourierCoeff (X p.1 p.2) k * NegSobolev.fourierCoeff (X p.1 p.2) l :=
    ((S7FCW5_coef_meas hXm k).mul (S7FCW5_coef_meas hXm l)).stronglyMeasurable
  exact (hf.integral_prod_right').measurable

lemma S7FCW5_sec_meas (P : Measure Ω) [IsProbabilityMeasure P] {X : ℝ → Ω → NegSobolev d r}
    (hXm : Measurable (Function.uncurry X)) (μ : ℝ → Measure (Torus d)) (h : Torus d → Torus d → ℝ)
    (hcm : ∀ k l : NonzeroLattice d, Measurable fun t => wickCoeff (μ t) h k l)
    (S : Finset (NonzeroLattice d)) :
    Measurable fun p : ℝ × Ω => wickSection P (X p.1) (μ p.1) h S p.2 := by
  unfold wickSection
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_)
  exact ((hcm k l).comp measurable_fst).mul
    (((S7FCW5_coef_meas hXm k).mul (S7FCW5_coef_meas hXm l)).sub
      ((S7FCW5_mean_meas P hXm k l).comp measurable_fst))

end Meas

lemma S7FCW5_eLp_of_sq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (g : Ω → ℝ) (hg : MemLp g 2 P) (c : ℝ) (hc : 0 < c) (hI : ∫ ω, g ω ^ 2 ∂P < c ^ 2) :
    eLpNorm g 2 P < ENNReal.ofReal c := by
  have hp : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), hp,
    ENNReal.ofReal_lt_ofReal_iff hc]
  have e : ∫ ω, ‖g ω‖ ^ (2 : ℝ) ∂P = ∫ ω, g ω ^ 2 ∂P := by
    congr 1; funext ω; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [e, show ((2 : ℝ))⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_lt' hc]
  exact hI

end HRS.MC.Sec7.S7FCW5

end
