import HRS.MS.ThCorrUAux2

/-!
# TC-U1 (part 3): uniform a priori thermal bounds for `s = 0`

Namespace `HRS.MS.TcU`; helper lemmas carry the prefix `tcu3_`.

With `ThCorrUAux2` (uniform Gaussian bound for `γ̄`, explicit (K1) constant `B = tcuB0 d S c₁`) the bound
`thermalDensity d 0 a β ≤ M γ̄`, `M = max 1 (exp (β B)) ≤ Mu := max 1 (exp (βp B))` gives, for
`a ∈ [am, ap]`, `β ∈ [βm, βp]`:

* `ρ ≤ M₀ exp (-c ‖x‖²)`, `c = βm am / 4`, `M₀ = Mu S₀`;
* `∫ ‖x‖² ρ ≤ m₂`, `∫ (log (1 + ‖x‖²))² ρ ≤ L2` (both integrable);
* `|g * μ + ½ log (1 + ‖x‖²)| ≤ UB` (from `0 ≤ K̃ * ρ ≤ M B`, `K̃ * ρ = g * ρ + ½ l + ½ ∫ l ρ + ½ log 2`);
* `z₀ ≤ Z`, the normaliser of the thermal equation, from the thermal equation at `x = 0` and `g * μ (0) ≤ M B`.

Main export: `tcu_apriori_zero`.  No existing file is edited.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.TcU

open HRS.Whole HRS.MS.Thm

variable {d : ℕ}

/-- Moment of a Gaussian-dominated probability density against a measurable `f ≥ 0`. -/
lemma tcu3_moment {ρ f W : Euc d → ℝ} {M₀ c : ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hM₀ : 0 ≤ M₀)
    (hg : ∀ x, ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hW : Integrable W) (hfW : ∀ x, f x * Real.exp (-c * ‖x‖ ^ 2) ≤ W x) :
    Integrable (fun x => f x * ρ x) ∧ (∫ x, f x * ρ x) ≤ M₀ * ∫ x, W x := by
  have hmaj : Integrable (fun x => M₀ * W x) := hW.const_mul M₀
  have hpt : ∀ x, f x * ρ x ≤ M₀ * W x := fun x => by
    calc f x * ρ x ≤ f x * (M₀ * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hg x) (hf0 x)
      _ = M₀ * (f x * Real.exp (-c * ‖x‖ ^ 2)) := by ring
      _ ≤ M₀ * W x := mul_le_mul_of_nonneg_left (hfW x) hM₀
  have hint : Integrable (fun x => f x * ρ x) := by
    refine Integrable.mono' hmaj (hf.mul hρ.measurable).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (hρ.nonneg x))]
    exact hpt x
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint hmaj hpt

/-- **TC-U1 (`s = 0`).**  Uniform a priori bounds for the logarithmic thermal density, for `a ∈ [am, ap]`,
`β ∈ [βm, βp]`. -/
theorem tcu_apriori_zero (hd : 1 ≤ d) {am ap βm βp : ℝ}
    (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) :
    ∃ c M₀ z₀ m₂ L2 UB : ℝ, 0 < c ∧ 0 < M₀ ∧ 0 < z₀ ∧
      ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
        z₀ ≤ tcuZ d 0 a β ∧
        (∀ x : Euc d, thermalDensity d 0 a β x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) ∧
        Integrable (fun x : Euc d => ‖x‖ ^ 2 * thermalDensity d 0 a β x) ∧
        (∫ x : Euc d, ‖x‖ ^ 2 * thermalDensity d 0 a β x) ≤ m₂ ∧
        Integrable (fun x : Euc d => Real.log (1 + ‖x‖ ^ 2) ^ 2 * thermalDensity d 0 a β x) ∧
        (∫ x : Euc d, Real.log (1 + ‖x‖ ^ 2) ^ 2 * thermalDensity d 0 a β x) ≤ L2 ∧
        ∀ x : Euc d, |HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) x +
          (1 / 2) * Real.log (1 + ‖x‖ ^ 2)| ≤ UB := by
  have hap0 : 0 < ap := ham.trans_le hap
  have hβp0 : 0 < βp := hβm.trans_le hβp
  set S : ℝ := tcuS0 d am ap βp with hSdef
  have hSpos : 0 < S := tcuS0_pos hap0 hβp0
  set c : ℝ := βm * am / 4 with hcdef
  have hcpos : 0 < c := by positivity
  set B0 : ℝ := tcuB0 d S c with hB0def
  have hB0 : 0 ≤ B0 := tcuB0_nonneg d hSpos.le
  set Mu : ℝ := max 1 (Real.exp (βp * B0)) with hMu
  have hMu1 : 1 ≤ Mu := le_max_left _ _
  set M₀ : ℝ := Mu * S with hM₀def
  have hM₀pos : 0 < M₀ := by positivity
  set m₂ : ℝ := M₀ * ∫ x : Euc d, ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2) with hm₂def
  set L2 : ℝ := M₀ * ∫ x : Euc d, 4 * (Real.exp (-c * ‖x‖ ^ 2) + ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2))
    with hL2def
  have hm₂0 : 0 ≤ m₂ := by
    rw [hm₂def]
    exact mul_nonneg hM₀pos.le (integral_nonneg fun x => by positivity)
  have hint1 : Integrable (fun x : Euc d => ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2)) :=
    t012_integrable_sq_mul_exp hcpos
  have hint2 : Integrable (fun x : Euc d =>
      4 * (Real.exp (-c * ‖x‖ ^ 2) + ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2))) :=
    ((t012_integrable_exp_neg_sq hcpos).add hint1).const_mul 4
  refine ⟨c, M₀, Real.exp (-(βp * (Mu * B0))) / M₀, m₂, L2,
    Mu * B0 + m₂ / 2 + Real.log 2 / 2, hcpos, hM₀pos, by positivity, fun a β ha1 ha2 hβ1 hβ2 => ?_⟩
  have ha : 0 < a := ham.trans_le ha1
  have hβ : 0 < β := hβm.trans_le hβ1
  have hγ : ∀ y : Euc d, t67gammaBar d a β y ≤ S * Real.exp (-c * ‖y‖ ^ 2) :=
    fun y => tcu2_gamma_le ham hβm ha1 ha2 hβ1 hβ2 y
  obtain ⟨hτ, hρC⟩ := tcu2_rep hd ha hβ hSpos.le hcpos hγ
  have hS := tcu2_setting hd ha hβ hSpos.le hcpos hγ
  have hρ : HRS.Whole.IsProbDensity (thermalDensity d 0 a β) := hτ.1.1
  have hMle : max 1 (Real.exp (β * B0)) ≤ Mu := by
    refine max_le_max le_rfl (Real.exp_le_exp.2 ?_)
    exact mul_le_mul_of_nonneg_right hβ2 hB0
  have hM1 : 1 ≤ max 1 (Real.exp (β * B0)) := le_max_left _ _
  have hM0' : (0 : ℝ) ≤ max 1 (Real.exp (β * B0)) := zero_le_one.trans hM1
  -- Gaussian bound
  have hgauss : ∀ x : Euc d, thermalDensity d 0 a β x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2) := by
    intro x
    refine (hρC.2 x).trans ?_
    calc max 1 (Real.exp (β * B0)) * t67gammaBar d a β x
        ≤ Mu * (S * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul hMle (hγ x) (t67gammaBar_pos ha hβ x).le (by positivity)
      _ = M₀ * Real.exp (-c * ‖x‖ ^ 2) := by rw [hM₀def]; ring
  -- moments
  have hmom2 := tcu3_moment (f := fun x : Euc d => ‖x‖ ^ 2) (W := fun x : Euc d => ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2))
    hρ hM₀pos.le hgauss (measurable_norm.pow_const 2) (fun x => by positivity) hint1 (fun x => le_rfl)
  have hmomL := tcu3_moment (f := fun x : Euc d => Real.log (1 + ‖x‖ ^ 2) ^ 2)
    (W := fun x : Euc d => 4 * (Real.exp (-c * ‖x‖ ^ 2) + ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2)))
    hρ hM₀pos.le hgauss
    ((Real.measurable_log.comp (measurable_const.add (measurable_norm.pow_const 2))).pow_const 2)
    (fun x => by positivity) hint2 (fun x => by
      have h := tcu2_l_sq_le x
      have he := (Real.exp_pos (-c * ‖x‖ ^ 2)).le
      unfold t67l at h
      nlinarith [mul_le_mul_of_nonneg_right h he])
  have hmoml := tcu3_moment (f := fun x : Euc d => t67l x) (W := fun x : Euc d => ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2))
    hρ hM₀pos.le hgauss t67l_measurable t67l_nonneg hint1 (fun x =>
      mul_le_mul_of_nonneg_right (t67l_le_sq x) (Real.exp_pos _).le)
  have hlρ0 : 0 ≤ ∫ x : Euc d, t67l x * thermalDensity d 0 a β x :=
    integral_nonneg fun x => mul_nonneg (t67l_nonneg x) (hρ.nonneg x)
  have hlρ1 : (∫ x : Euc d, t67l x * thermalDensity d 0 a β x) ≤ m₂ := hmoml.2
  -- the interaction potential
  have hU : ∀ x : Euc d,
      -(m₂ / 2 + Real.log 2 / 2) ≤ HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) x +
        (1 / 2) * Real.log (1 + ‖x‖ ^ 2) ∧
      HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) x +
        (1 / 2) * Real.log (1 + ‖x‖ ^ 2) ≤ Mu * B0 := by
    intro x
    have hconv := (t67_conv_eq hS ha hβ hM1 hρC x).2
    obtain ⟨-, hK0, hK1⟩ := conv_bound_of_le hS.meas hS.nonneg hS.k1 hρ.measurable hρ.nonneg hM0'
      hρC.2 x
    have e : HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) x =
        ∫ y, rieszKernel d 0 (x - y) * thermalDensity d 0 a β y :=
      convMeasure_withDensityReal _ hρ.measurable hρ.nonneg x
    have hl : t67l x = Real.log (1 + ‖x‖ ^ 2) := rfl
    have hMB : max 1 (Real.exp (β * B0)) * B0 ≤ Mu * B0 := mul_le_mul_of_nonneg_right hMle hB0
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [e, ← hl]
    constructor <;> linarith
  have hU0 : (0 : ℝ) ≤ Mu * B0 := by positivity
  refine ⟨?_, hgauss, hmom2.1, hmom2.2, hmomL.1, hmomL.2, fun x => ?_⟩
  · -- normaliser
    obtain ⟨hZpos, heq⟩ := tcu1_eq hτ (0 : Euc d)
    have hV0 : confinement a (0 : Euc d) = 0 := by simp [confinement]
    rw [hV0, zero_add] at heq
    have h0 : thermalDensity d 0 a β 0 ≤ M₀ := by
      have := hgauss 0
      simpa using this
    have hUx := (hU 0).2
    have hl0 : Real.log (1 + ‖(0 : Euc d)‖ ^ 2) = 0 := by simp
    rw [hl0, mul_zero, add_zero] at hUx
    have hexp : Real.exp (-(βp * (Mu * B0))) ≤
        Real.exp (-β * HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) 0) := by
      apply Real.exp_le_exp.2
      have h1 : β * HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) 0 ≤ β * (Mu * B0) :=
        mul_le_mul_of_nonneg_left hUx hβ.le
      have h2 : β * (Mu * B0) ≤ βp * (Mu * B0) := mul_le_mul_of_nonneg_right hβ2 hU0
      linarith
    rw [div_le_iff₀ hM₀pos]
    calc Real.exp (-(βp * (Mu * B0))) ≤
          Real.exp (-β * HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) 0) := hexp
      _ = thermalDensity d 0 a β 0 * tcuZ d 0 a β := heq.symm
      _ ≤ M₀ * tcuZ d 0 a β := mul_le_mul_of_nonneg_right h0 hZpos.le
      _ = tcuZ d 0 a β * M₀ := mul_comm _ _
  · obtain ⟨h1, h2⟩ := hU x
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    constructor <;> nlinarith

end HRS.MS.TcU

end
