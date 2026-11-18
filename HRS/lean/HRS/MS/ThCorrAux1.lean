import HRS.MS.ThCorrSmAux2
import HRS.MS.ThCorrDriftAux1
import HRS.MS.ThCorrUDAux2
import HRS.MS.ThCorrUDAux4
import HRS.MS.ThCorrSAux2

/-!
# TC-6, part 1: assembly lemmas for the thermal corrector (S4.4, step 10)

Namespace `HRS.MS.Tc6`, helper prefix `tc6_`.

* `tc6_kop_congr_ae`: `Kop g μ f x` depends on the `μ`-class of `f` only (for every `x`).
* `tc6_unif`: the uniform thermal data (`TcRef` for every order `N`, `TcDrift` for every order `m`) for all `0 ≤ s < d`,
  constants quantified before `a, β` (the three regimes of `tcu_uniform_*`).
* `tc6_memLp_log`: a function with a log growth bound is in `L²(μ)` when `‖x‖²` is `μ`-integrable.
* `tc6_corrector_of_data`: the six conjuncts of `IsThermalCorrector` from the Poisson solution `χ` of `thermalGen χ = r`
  and the resolvent representative `r =ᵐ r₀`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
open HRS.Whole

noncomputable section

namespace HRS.MS.Tc6

variable {d : ℕ}

/-- `Kop g μ f x` depends only on the `μ`-a.e. class of `f` (for every `x`). -/
theorem tc6_kop_congr_ae (g : Euc d → ℝ) (μ : Measure (Euc d)) {f f' : Euc d → ℝ} (h : f =ᵐ[μ] f')
    (x : Euc d) : HRS.Whole.Kop g μ f x = HRS.Whole.Kop g μ f' x := by
  have e : (fun x => ∫ y, g (x - y) * f y ∂μ) = fun x => ∫ y, g (x - y) * f' y ∂μ := by
    funext x
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  unfold HRS.Whole.Kop
  rw [e]

/-- the uniform thermal data for every `0 ≤ s < d`. -/
theorem tc6_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {am ap βm βp : ℝ} (ham : 0 < am)
    (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) :
    ∃ c M₀ m₂ : ℝ, 0 < c ∧ 0 < M₀ ∧
      (∀ N : ℕ, ∃ S : ℝ, 0 ≤ S ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
        HRS.MS.TcDefs.TcRef d (thermalDensity d s a β) M₀ c S N) ∧
      (∀ m : ℕ, ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
        HRS.MS.TcDefs.TcDrift d (thermalDensity d s a β) (β * a) Mb m₂ m) := by
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    exact HRS.MS.TcU.tcu_uniform_zero hd ham hβm hap hβp
  · by_cases h1 : s < (d : ℝ) - 1
    · exact HRS.MS.TcU.tcu_uniform_easy hd h0 h1 ham hβm hap hβp
    · exact HRS.MS.TcU.tcu_uniform_hard hd h0 hsd (not_lt.1 h1) ham hβm hap hβp

/-- a function with a logarithmic growth bound is in `L²(μ)` (finite measure, second moment). -/
theorem tc6_memLp_log {μ : Measure (Euc d)} [IsFiniteMeasure μ]
    (hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ) {χ : Euc d → ℝ} (hχ : Continuous χ) {A : ℝ}
    (hA : 0 ≤ A) (hlog : ∀ x, |χ x| ≤ A * (1 + Real.log (2 + ‖x‖))) : MemLp χ 2 μ := by
  rw [memLp_two_iff_integrable_sq hχ.aestronglyMeasurable]
  have hb : Integrable (fun x : Euc d => 2 * A ^ 2 * (9 + ‖x‖ ^ 2)) μ :=
    (((integrable_const (9 : ℝ)).add hint2).const_mul (2 * A ^ 2))
  refine hb.mono' (hχ.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hl : Real.log (2 + ‖x‖) ≤ 2 + ‖x‖ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖x‖ by positivity)
    linarith
  have hl0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
  have h1 : |χ x| ≤ A * (3 + ‖x‖) := (hlog x).trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  have h2 : ‖χ x ^ 2‖ = |χ x| ^ 2 := by rw [Real.norm_eq_abs, abs_pow]
  rw [h2]
  calc |χ x| ^ 2 ≤ (A * (3 + ‖x‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = A ^ 2 * (3 + ‖x‖) ^ 2 := by ring
    _ ≤ 2 * A ^ 2 * (9 + ‖x‖ ^ 2) := by
      have : (3 + ‖x‖) ^ 2 ≤ 2 * (9 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (3 - ‖x‖)]
      nlinarith [sq_nonneg A]

/-- **Assembly of the six conjuncts of `IsThermalCorrector`.**  Data: `χ` solves `thermalGen χ = r` with the Poisson
bounds (constants `C1`, `Cm` in terms of `cbNorm 2 r`, `cbNorm (k+1) r`), `r ∈ C_b^{k+1}` is a representative of the
resolvent solution `r₀` and `cbNorm (k+1) r ≤ C2 * normφ`. -/
theorem tc6_corrector_of_data {s a β γ : ℝ} {k : ℕ} (hk : 1 ≤ k) {φ : Euc d → ℝ} {normφ : ℝ}
    (hnorm : 0 ≤ normφ) (hγ : 0 < γ) (hprob : IsProbabilityMeasure (thermalMeasure d s a β))
    (hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) (thermalMeasure d s a β))
    {r r₀ χ : Euc d → ℝ} {C1 Cm C2 : ℝ} (hC2 : 0 ≤ C2) (hr : HRS.MemCb (k + 1) r)
    (hrr : r =ᵐ[thermalMeasure d s a β] r₀)
    (heq : ∀ᵐ x ∂(thermalMeasure d s a β),
      r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (thermalMeasure d s a β) r₀ x =
        γ * HRS.Whole.projMean (thermalMeasure d s a β) φ x)
    (hχc : ContDiff ℝ (k + 1) χ)
    (hχ0 : ∫ x, χ x ∂(thermalMeasure d s a β) = 0) (hgen : ∀ x, thermalGen d s a β χ x = r x)
    (hlog : ∀ x, |χ x| ≤ C1 * HRS.cbNorm 2 r * (1 + Real.log (2 + ‖x‖)))
    (hder : ∀ x : Fin (k + 1) → Euc d,
      ∑ j : Fin (k + 1), ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (x j)‖ ≤ Cm * HRS.cbNorm (k + 1) r)
    (hbd : HRS.cbNorm (k + 1) r ≤ C2 * normφ) :
    IsThermalCorrector d s a β γ k φ normφ (|C1| * C2 + |Cm| * C2) χ := by
  have hgenf : thermalGen d s a β χ = r := funext hgen
  obtain ⟨hr2m, hr2n⟩ := HRS.MS.Tc5.tc5_cb_mono (m := 2) (J := k + 1) (by omega) hr
  have hcb2 : 0 ≤ HRS.cbNorm 2 r := HRS.MS.Tc5.tc5_cb_nonneg (d := d) 2 r
  have hcbm : 0 ≤ HRS.cbNorm (k + 1) r := hcb2.trans hr2n
  have hlogpos : ∀ x : Euc d, 0 ≤ 1 + Real.log (2 + ‖x‖) := fun x => by
    have : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
    linarith
  have hlog' : ∀ x, |χ x| ≤ (|C1| * C2 + |Cm| * C2) * normφ * (1 + Real.log (2 + ‖x‖)) := by
    intro x
    refine (hlog x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hlogpos x)
    calc C1 * HRS.cbNorm 2 r ≤ |C1| * HRS.cbNorm 2 r :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hcb2
      _ ≤ |C1| * (C2 * normφ) := mul_le_mul_of_nonneg_left (hr2n.trans hbd) (abs_nonneg _)
      _ ≤ (|C1| * C2 + |Cm| * C2) * normφ := by
          have : 0 ≤ |Cm| * C2 * normφ := by positivity
          nlinarith
  have hder' : ∀ x : Fin (k + 1) → Euc d,
      ∑ j : Fin (k + 1), ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (x j)‖ ≤ (|C1| * C2 + |Cm| * C2) * normφ := by
    intro x
    refine (hder x).trans ?_
    calc Cm * HRS.cbNorm (k + 1) r ≤ |Cm| * HRS.cbNorm (k + 1) r :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hcbm
      _ ≤ |Cm| * (C2 * normφ) := mul_le_mul_of_nonneg_left hbd (abs_nonneg _)
      _ ≤ (|C1| * C2 + |Cm| * C2) * normφ := by
          have : 0 ≤ |C1| * C2 * normφ := by positivity
          nlinarith
  have hA : 0 ≤ (|C1| * C2 + |Cm| * C2) * normφ := by positivity
  refine ⟨⟨?_, hχ0⟩, hχc, ?_, ?_, hlog', hder'⟩
  · exact tc6_memLp_log hint2 (hχc.continuous) hA hlog'
  · rw [hgenf]
    exact HRS.MS.Tc5.tc5_memLp_of_cb hr
  · filter_upwards [hrr, heq] with x hx1 hx2
    unfold susceptibilityOp
    rw [hgenf, tc6_kop_congr_ae (rieszKernel d s) (thermalMeasure d s a β) hrr x, hx1]
    refine mul_left_cancel₀ hγ.ne' ?_
    rw [← hx2, mul_add, ← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul]

end HRS.MS.Tc6

end
