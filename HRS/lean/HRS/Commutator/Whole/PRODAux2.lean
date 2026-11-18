import HRS.Commutator.Whole.PRODAux1

/-!
# CMX-PROD helper file 2: even Schwartz mollifiers and the `L^p` approximate identity
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.PROD

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

/-- Hölder: `t ↦ K t * h (y - t)` is integrable for Schwartz `K` and `h ∈ L^p`. -/
lemma prod_integrable_conv (K : SchwartzMap (Euc d) ℂ) {p : ℝ} (hp : 1 < p) {h : Euc d → ℂ}
    (hh : MemLp h (ENNReal.ofReal p) volume) (y : Euc d) :
    Integrable (fun t => K t * h (y - t)) := by
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hH : (ENNReal.ofReal p).HolderConjugate (ENNReal.conjExponent (ENNReal.ofReal p)) :=
    ENNReal.HolderConjugate.conjExponent hP1
  have h1 : MemLp (fun t => h (y - t)) (ENNReal.ofReal p) volume :=
    hh.comp_measurePreserving (Measure.measurePreserving_sub_left volume y)
  have := hH.symm
  exact (K.memLp (ENNReal.conjExponent (ENNReal.ofReal p))).integrable_mul h1

/-- Linearity of the convolution in the function. -/
lemma prod_conv_sub (K : SchwartzMap (Euc d) ℂ) {p : ℝ} (hp : 1 < p) {h₁ h₂ : Euc d → ℂ}
    (h1 : MemLp h₁ (ENNReal.ofReal p) volume) (h2 : MemLp h₂ (ENNReal.ofReal p) volume) :
    prod_conv K (h₁ - h₂) = fun y => prod_conv K h₁ y - prod_conv K h₂ y := by
  funext y
  unfold prod_conv
  rw [← integral_sub (prod_integrable_conv K hp h1 y) (prod_integrable_conv K hp h2 y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [mul_sub, Pi.sub_apply]

/-! ### The mollifier -/

/-- The bump with radii `1/(n+2) < 1/(n+1)`. -/
def prod_bump (d n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity, by
    rw [one_div_lt_one_div (by positivity) (by positivity)]; linarith⟩

/-- The normalised bump, a smooth nonnegative even function of integral one. -/
def prod_kerR (d n : ℕ) : Euc d → ℝ := (prod_bump d n).normed volume

lemma prod_kerR_nonneg (n : ℕ) (x : Euc d) : 0 ≤ prod_kerR d n x := (prod_bump d n).nonneg_normed x

lemma prod_kerR_integral (n : ℕ) : ∫ x, prod_kerR d n x = 1 := (prod_bump d n).integral_normed

lemma prod_kerR_neg (n : ℕ) (x : Euc d) : prod_kerR d n (-x) = prod_kerR d n x :=
  (prod_bump d n).normed_neg (μ := volume) x

lemma prod_kerR_contDiff (n : ℕ) : ContDiff ℝ ∞ (prod_kerR d n) := (prod_bump d n).contDiff_normed

lemma prod_kerR_compact (n : ℕ) : HasCompactSupport (prod_kerR d n) :=
  (prod_bump d n).hasCompactSupport_normed

lemma prod_kerR_zero {n : ℕ} {x : Euc d} (hx : 1 / ((n : ℝ) + 1) ≤ ‖x‖) : prod_kerR d n x = 0 := by
  have h1 : x ∉ Function.support (prod_kerR d n) := by
    unfold prod_kerR
    rw [ContDiffBump.support_normed_eq]
    simpa [prod_bump] using hx
  simpa using h1

lemma prod_kerR_integrable (n : ℕ) : Integrable (prod_kerR d n) := (prod_bump d n).integrable_normed

/-- The mollifier as a Schwartz function. -/
def prod_ker (d n : ℕ) : SchwartzMap (Euc d) ℂ :=
  (show HasCompactSupport (fun x : Euc d => ((prod_kerR d n x : ℝ) : ℂ)) from
    (prod_kerR_compact n).comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (prod_kerR_contDiff n))

lemma prod_ker_apply (n : ℕ) (x : Euc d) : prod_ker d n x = ((prod_kerR d n x : ℝ) : ℂ) := rfl

lemma prod_ker_neg (n : ℕ) (x : Euc d) : prod_ker d n (-x) = prod_ker d n x := by
  simp [prod_ker_apply, prod_kerR_neg]

lemma prod_ker_norm_integral (n : ℕ) : ∫ t, ‖prod_ker d n t‖ = 1 := by
  have : ∀ t, ‖prod_ker d n t‖ = prod_kerR d n t := fun t => by
    rw [prod_ker_apply, Complex.norm_real, Real.norm_of_nonneg (prod_kerR_nonneg n t)]
  simp_rw [this]
  exact prod_kerR_integral n

lemma prod_conv_ker_tendsto {g : Euc d → ℂ} (hg : Continuous g) (y : Euc d) :
    Tendsto (fun n => prod_conv (prod_ker d n) g y) atTop (𝓝 (g y)) := by
  have hφ : Tendsto (fun n : ℕ => (prod_bump d n).rOut) atTop (𝓝 0) := by
    simpa [prod_bump] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
    (φ := fun n => prod_bump d n) (l := atTop) (g := g) hφ hg y
  refine this.congr (fun n => ?_)
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, prod_conv, prod_ker_apply,
    prod_kerR, Complex.real_smul]

end HRS.Commutator.Whole.PROD
