import HRS.MS.MovInterpAux2
import HRS.PDE.ToolboxRd.Defs

/-!
# MOVA3 (spike): sanity instance, analytic lemma for the Fourier-side variants, A3b signatures

1. `mo_interp_gauss_mult`: first instance of `mo_interp_osc`, `T f = exp(-‖x‖²) f` between integer
   endpoints (the endpoint bounds are hypotheses; they are not proved here).
2. `mova3_hasDerivAt_weighted` / `mova3_differentiable_weighted`: the analytic lemma needed
   for the Fourier-side variants (A3b): for a weight `w ≥ 1` and `g` with `∫ w^R ‖g‖ < ∞` for all
   real `R`, the map `z ↦ ∫ w(x)^z g(x) dμ` is entire (complex-differentiable), proved from
   Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (instantiated at the field `ℂ`).
   Use in A3b: `w(ξ) = (1 + 4π²‖ξ‖²)^{1/2}`, `g = â · b̂` with `â ∈ L²` (Fourier transform of `T h_α`)
   and `b̂` a Schwartz function (Fourier transform of a finite Hermite combination, or of a Schwartz
   test function): `∫ w^R |â||b̂| ≤ ‖â‖₂ ‖w^R b̂‖₂ < ∞` for every `R`.
3. `mo_interp_osc_H_stmt`, `mo_interp_H_osc_stmt`: signatures only (as `Prop`-valued definitions,
   not asserted) of the Fourier-side variants `Σ → H` and `H → Σ` planned for A3b.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS.Whole
open HRS.MS.MovInterp

namespace HRS.MS.MovOsc

variable {d : ℕ}

/-! ### 1. Sanity instance: multiplication by `exp(-‖x‖²)` -/

/-- Multiplication by the Gaussian `exp(-‖x‖²)`. -/
def mova3_gaussMul (d : ℕ) (f : Euc d → ℝ) : Euc d → ℝ := fun x => Real.exp (-‖x‖ ^ 2) * f x

lemma mova3_hspan_memLp {f : Euc d → ℝ} (hf : f ∈ mo_Hspan d) :
    MemLp f 2 (volume : Measure (Euc d)) := by
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨α, rfl⟩ := hx; exact memLp_hermiteFunD α
  | zero => exact MemLp.zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

lemma mova3_gaussMul_memLp {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    MemLp (mova3_gaussMul d f) 2 (volume : Measure (Euc d)) := by
  refine hf.of_le ?_ (ae_of_all _ fun x => ?_)
  · exact ((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul hf.aestronglyMeasurable
  · simp only [mova3_gaussMul, norm_mul]
    have h1 : ‖Real.exp (-‖x‖ ^ 2)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])
    exact mul_le_of_le_one_left (norm_nonneg _) h1

lemma mova3_gaussMul_linear (f g : Euc d → ℝ) (a : ℝ) :
    mova3_gaussMul d (a • f + g) = a • mova3_gaussMul d f + mova3_gaussMul d g := by
  funext x; simp [mova3_gaussMul]; ring

/-- Interpolation for `f ↦ exp(-‖x‖²) f` between the integer indices `n0, n1`
(endpoint bounds as hypotheses). -/
theorem mo_interp_gauss_mult {n0 n1 : ℤ} {M0 M1 : ℝ}
    (h0 : ∀ f ∈ mo_Hspan d, MemOsc (n0 : ℝ) (mova3_gaussMul d f) ∧
      oscNorm (n0 : ℝ) (mova3_gaussMul d f) ≤ M0 * oscNorm (n0 : ℝ) f)
    (h1 : ∀ f ∈ mo_Hspan d, MemOsc (n1 : ℝ) (mova3_gaussMul d f) ∧
      oscNorm (n1 : ℝ) (mova3_gaussMul d f) ≤ M1 * oscNorm (n1 : ℝ) f)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ f ∈ mo_Hspan d,
      MemOsc ((1 - θ) * n0 + θ * n1) (mova3_gaussMul d f) ∧
        oscNorm ((1 - θ) * n0 + θ * n1) (mova3_gaussMul d f) ≤
          M0 ^ (1 - θ) * M1 ^ θ * oscNorm ((1 - θ) * n0 + θ * n1) f :=
  mo_interp_osc (T := mova3_gaussMul d)
    (fun f _ g _ a => mova3_gaussMul_linear f g a)
    (fun f hf => mova3_gaussMul_memLp (mova3_hspan_memLp hf)) h0 h1 hθ

/-! ### 2. Analyticity of `z ↦ ∫ w^z g` -/

section Analytic

variable {α : Type*} [MeasurableSpace α]

/-- Complex derivative of `z ↦ ∫ w(x)^z g(x) dμ` at any `z₀` (weight `w ≥ 1`, `g` with
`∫ w^R ‖g‖ < ∞` for every real `R`). -/
lemma mova3_hasDerivAt_weighted (μ : Measure α) (w : α → ℝ) (hw1 : ∀ x, 1 ≤ w x)
    (hwm : Measurable w) (g : α → ℂ) (hg : AEStronglyMeasurable g μ)
    (hint : ∀ R : ℝ, Integrable (fun x => w x ^ R * ‖g x‖) μ) (z₀ : ℂ) :
    HasDerivAt (fun z : ℂ => ∫ x, (w x : ℂ) ^ z * g x ∂μ)
      (∫ x, (w x : ℂ) ^ z₀ * Complex.log (w x : ℂ) * g x ∂μ) z₀ := by
  have hwpos : ∀ x, 0 < w x := fun x => lt_of_lt_of_le zero_lt_one (hw1 x)
  have hwc : Measurable fun x => (w x : ℂ) := Complex.measurable_ofReal.comp hwm
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun x => (w x : ℂ) ^ z * g x) μ := fun z =>
    ((hwc.pow_const z).aestronglyMeasurable).mul hg
  have hnorm : ∀ (z : ℂ) x, ‖(w x : ℂ) ^ z * g x‖ = w x ^ z.re * ‖g x‖ := fun z x => by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hwpos x)]
  set R : ℝ := |z₀.re| + 1 with hR
  have hbound : ∀ x, ∀ z ∈ Metric.ball z₀ 1,
      ‖(w x : ℂ) ^ z * Complex.log (w x : ℂ) * g x‖ ≤ w x ^ (R + 1) * ‖g x‖ := by
    intro x z hz
    have hzre : z.re ≤ R := by
      have h1 : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
        simpa using Complex.abs_re_le_norm (z - z₀)
      have h2 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      have h3 := abs_le.1 (h1.trans h2.le)
      have h4 := le_abs_self z₀.re
      linarith [h3.2]
    have hlog : ‖Complex.log (w x : ℂ)‖ ≤ w x := by
      rw [← Complex.ofReal_log (hwpos x).le, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (hw1 x))]
      exact (Real.log_le_sub_one_of_pos (hwpos x)).trans (by linarith)
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hwpos x)]
    have hpow : w x ^ z.re ≤ w x ^ R := Real.rpow_le_rpow_of_exponent_le (hw1 x) hzre
    have e : w x ^ (R + 1) = w x ^ R * w x := by
      rw [Real.rpow_add (hwpos x), Real.rpow_one]
    rw [e]
    have : w x ^ z.re * ‖Complex.log (w x : ℂ)‖ ≤ w x ^ R * w x :=
      mul_le_mul hpow hlog (norm_nonneg _) (Real.rpow_nonneg (hwpos x).le _)
    calc w x ^ z.re * ‖Complex.log (w x : ℂ)‖ * ‖g x‖ ≤ w x ^ R * w x * ‖g x‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := by ring
  have hF'meas : AEStronglyMeasurable (fun x => (w x : ℂ) ^ z₀ * Complex.log (w x : ℂ) * g x) μ :=
    (((hwc.pow_const z₀).mul (Complex.measurable_log.comp hwc)).aestronglyMeasurable).mul hg
  have hFint : Integrable (fun x => (w x : ℂ) ^ z₀ * g x) μ :=
    (hint z₀.re).mono' (hmeas z₀) (ae_of_all _ fun x => (hnorm z₀ x).le)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun z x => (w x : ℂ) ^ z * g x)
    (F' := fun z x => (w x : ℂ) ^ z * Complex.log (w x : ℂ) * g x)
    (bound := fun x => w x ^ (R + 1) * ‖g x‖) (s := Metric.ball z₀ 1) (Metric.ball_mem_nhds _
      one_pos) (Eventually.of_forall hmeas) hFint hF'meas
    (ae_of_all _ hbound) (hint (R + 1)) (ae_of_all _ fun x z _ => ?_)).2
  have hne : (w x : ℂ) ≠ 0 := by exact_mod_cast (hwpos x).ne'
  exact ((Complex.hasStrictDerivAt_const_cpow (Or.inl hne)).hasDerivAt).mul_const (g x)

/-- Entire dependence on `z` (complex-differentiability) of `z ↦ ∫ w^z g`. -/
theorem mova3_differentiable_weighted (μ : Measure α) (w : α → ℝ) (hw1 : ∀ x, 1 ≤ w x)
    (hwm : Measurable w) (g : α → ℂ) (hg : AEStronglyMeasurable g μ)
    (hint : ∀ R : ℝ, Integrable (fun x => w x ^ R * ‖g x‖) μ) :
    Differentiable ℂ (fun z : ℂ => ∫ x, (w x : ℂ) ^ z * g x ∂μ) := fun z₀ =>
  (mova3_hasDerivAt_weighted μ w hw1 hwm g hg hint z₀).differentiableAt

end Analytic

/-! ### 3. Signatures of the Fourier-side variants (A3b), as `Prop`s -/

/-- Signature of `Σ → H` interpolation: `T` linear on the Hermite span with values in `L²`,
`‖T f‖_{H^{s_i}} ≤ M_i ‖f‖_{Σ^{r_i}}`; conclusion at `θ`. -/
def mo_interp_osc_H_stmt (d : ℕ) : Prop :=
  ∀ (T : (Euc d → ℝ) → (Euc d → ℝ)),
    (∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g) →
    (∀ f ∈ mo_Hspan d, MemLp (T f) 2 (volume : Measure (Euc d))) →
    ∀ {r0 r1 s0 s1 M0 M1 : ℝ}, 0 ≤ M0 → 0 ≤ M1 →
      (∀ f ∈ mo_Hspan d, HRS.PDE.ToolboxRd.MemSobolev s0 (T f) ∧
        Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s0 (T f)) ≤ M0 * oscNorm r0 f) →
      (∀ f ∈ mo_Hspan d, HRS.PDE.ToolboxRd.MemSobolev s1 (T f) ∧
        Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s1 (T f)) ≤ M1 * oscNorm r1 f) →
      ∀ {θ : ℝ}, θ ∈ Set.Icc (0 : ℝ) 1 →
        ∀ f ∈ mo_Hspan d,
          HRS.PDE.ToolboxRd.MemSobolev ((1 - θ) * s0 + θ * s1) (T f) ∧
            Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ((1 - θ) * s0 + θ * s1) (T f)) ≤
              M0 ^ (1 - θ) * M1 ^ θ * oscNorm ((1 - θ) * r0 + θ * r1) f

/-- Signature of `H → Σ` interpolation on Schwartz inputs (the rotated inputs `⟨D⟩^{-z} f` are
Schwartz, not Hermite combinations, so the natural domain is the Schwartz space): `T` linear on
Schwartz functions, `‖T f‖_{Σ^{s_i}} ≤ M_i ‖f‖_{H^{r_i}}`; conclusion at `θ`. -/
def mo_interp_H_osc_stmt (d : ℕ) : Prop :=
  ∀ (T : SchwartzMap (Euc d) ℝ → (Euc d → ℝ)),
    (∀ f g : SchwartzMap (Euc d) ℝ, ∀ a : ℝ, T (a • f + g) = a • T f + T g) →
    (∀ f, MemLp (T f) 2 (volume : Measure (Euc d))) →
    ∀ {r0 r1 s0 s1 M0 M1 : ℝ}, 0 ≤ M0 → 0 ≤ M1 →
      (∀ f : SchwartzMap (Euc d) ℝ, MemOsc s0 (T f) ∧
        oscNorm s0 (T f) ≤ M0 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r0 f)) →
      (∀ f : SchwartzMap (Euc d) ℝ, MemOsc s1 (T f) ∧
        oscNorm s1 (T f) ≤ M1 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r1 f)) →
      ∀ {θ : ℝ}, θ ∈ Set.Icc (0 : ℝ) 1 →
        ∀ f : SchwartzMap (Euc d) ℝ,
          MemOsc ((1 - θ) * s0 + θ * s1) (T f) ∧
            oscNorm ((1 - θ) * s0 + θ * s1) (T f) ≤
              M0 ^ (1 - θ) * M1 ^ θ *
                Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ((1 - θ) * r0 + θ * r1) f)

end HRS.MS.MovOsc
