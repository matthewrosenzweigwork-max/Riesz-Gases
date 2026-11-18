import HRS.MS.WrKerAux3

/-!
# HRS.MS.WrCalAux1 -- exponential family of a bounded `H`-valued statistic (WR-11a, part 1)

Packet WR-11a of `docs/WR_B_PLAN.md` (T4, calibration).  This file is the abstract probabilistic
half of the calibration: for a probability space `(Ω, P)`, a real inner product space `H`, and a
bounded strongly measurable `S : Ω → H` it studies `t ↦ log E_P[exp ⟪t, S⟫]` on `H`.

Nothing here refers to the Riesz gas.  The torus template is `HRS/Equilibrium/CalibratedReference.lean`
(lines 259-330, 474-575), where `H = EuclideanSpace ℝ (Fin M)`; here `H` is arbitrary, so the
coordinate derivatives are replaced by derivatives along lines `s ↦ t + s • v`.

* `Wr11Bdd S C`: `S` strongly measurable with `‖S ω‖ ≤ C`, `0 ≤ C`.
* `wr11_Ya S t ω = ⟪t, S ω⟫`, `wr11_Z P S t = E_P exp ⟪t,S⟫`, `wr11_cF P S t = log (wr11_Z P S t)`.
* integrability of `exp (s * ⟪t,S⟫)`, `0 < Z`, `Z 0 = 1`, continuity of `Z` and of `cF`;
* `cF (t + s v) = cF t + cgf_{⟪v,S⟫}^{P tilted by ⟪t,S⟫} (s)`, the derivative along every line,
  convexity of `cF`, Jensen `⟪t, E S⟫ ≤ cF t`, and monotonicity of the gradient along `t`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {Ω : Type*} [MeasurableSpace Ω]

/-- The linear statistic `ω ↦ ⟪t, S ω⟫`. -/
def wr11_Ya (S : Ω → H) (t : H) (ω : Ω) : ℝ := inner ℝ t (S ω)

/-- `S` is strongly measurable and bounded by `C ≥ 0`. -/
structure Wr11Bdd (S : Ω → H) (C : ℝ) : Prop where
  meas : StronglyMeasurable S
  bound : ∀ ω, ‖S ω‖ ≤ C
  C_nonneg : 0 ≤ C

lemma wr11_Ya_add (S : Ω → H) (t v : H) (s : ℝ) (ω : Ω) :
    wr11_Ya S (t + s • v) ω = wr11_Ya S t ω + s * wr11_Ya S v ω := by
  simp [wr11_Ya, inner_add_left, real_inner_smul_left]

lemma wr11_Ya_zero (S : Ω → H) (ω : Ω) : wr11_Ya S 0 ω = 0 := by simp [wr11_Ya]

lemma wr11_Ya_smul (S : Ω → H) (t : H) (s : ℝ) (ω : Ω) :
    wr11_Ya S (s • t) ω = s * wr11_Ya S t ω := by
  simp [wr11_Ya, real_inner_smul_left]

variable {P : Measure Ω} {S : Ω → H} {C : ℝ}

lemma wr11_measurable_Ya (hS : StronglyMeasurable S) (t : H) : Measurable (wr11_Ya S t) := by
  unfold wr11_Ya
  exact (stronglyMeasurable_const.inner hS).measurable

lemma wr11_abs_Ya_le (h : Wr11Bdd S C) (t : H) (ω : Ω) : |wr11_Ya S t ω| ≤ ‖t‖ * C :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (h.bound ω) (norm_nonneg _))

lemma wr11_integrable_of_abs_le [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) (c : ℝ)
    (h : ∀ ω, |f ω| ≤ c) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable c
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using h ω)

lemma wr11_integrable_exp_Ya [IsFiniteMeasure P] (h : Wr11Bdd S C) (t : H) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * wr11_Ya S t ω)) P := by
  refine wr11_integrable_of_abs_le
    (Real.measurable_exp.comp ((wr11_measurable_Ya h.meas t).const_mul s))
    (Real.exp (|s| * (‖t‖ * C))) fun ω => ?_
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  calc s * wr11_Ya S t ω ≤ |s * wr11_Ya S t ω| := le_abs_self _
    _ = |s| * |wr11_Ya S t ω| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (wr11_abs_Ya_le h t ω) (abs_nonneg _)

lemma wr11_integrable_Ya [IsFiniteMeasure P] (h : Wr11Bdd S C) (t : H) :
    Integrable (wr11_Ya S t) P :=
  wr11_integrable_of_abs_le (wr11_measurable_Ya h.meas t) _ (wr11_abs_Ya_le h t)

/-- The partition function `Z(t) = E_P exp ⟪t, S⟫`. -/
def wr11_Z (P : Measure Ω) (S : Ω → H) (t : H) : ℝ := ∫ ω, Real.exp (wr11_Ya S t ω) ∂P

/-- The log partition function `cF(t) = log Z(t)`. -/
def wr11_cF (P : Measure Ω) (S : Ω → H) (t : H) : ℝ := Real.log (wr11_Z P S t)

lemma wr11_integrable_exp_Ya_one [IsFiniteMeasure P] (h : Wr11Bdd S C) (t : H) :
    Integrable (fun ω => Real.exp (wr11_Ya S t ω)) P := by
  simpa using wr11_integrable_exp_Ya (P := P) h t 1

lemma wr11_Z_pos [IsProbabilityMeasure P] (h : Wr11Bdd S C) (t : H) : 0 < wr11_Z P S t :=
  integral_exp_pos (wr11_integrable_exp_Ya_one (P := P) h t)

lemma wr11_Z_zero [IsProbabilityMeasure P] : wr11_Z P S 0 = 1 := by
  simp [wr11_Z, wr11_Ya_zero]

lemma wr11_cF_zero [IsProbabilityMeasure P] : wr11_cF P S 0 = 0 := by
  simp [wr11_cF, wr11_Z_zero]

lemma wr11_continuous_Z [IsProbabilityMeasure P] (h : Wr11Bdd S C) :
    Continuous (wr11_Z P S) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  refine continuousAt_of_dominated
    (bound := fun _ => Real.exp ((‖t₀‖ + 1) * C))
    (Eventually.of_forall fun t => (wr11_integrable_exp_Ya_one (P := P) h t).aestronglyMeasurable)
    ?_ (integrable_const _) (Eventually.of_forall fun ω => ?_)
  · have hn : ∀ᶠ t in 𝓝 t₀, ‖t‖ ≤ ‖t₀‖ + 1 := by
      have : Metric.ball t₀ 1 ∈ 𝓝 t₀ := Metric.ball_mem_nhds _ one_pos
      filter_upwards [this] with t ht
      have := norm_le_norm_add_norm_sub' t t₀
      rw [Metric.mem_ball, dist_eq_norm] at ht
      linarith [norm_sub_rev t t₀]
    filter_upwards [hn] with t ht
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    calc wr11_Ya S t ω ≤ |wr11_Ya S t ω| := le_abs_self _
      _ ≤ ‖t‖ * C := wr11_abs_Ya_le h t ω
      _ ≤ _ := mul_le_mul_of_nonneg_right ht h.C_nonneg
  · have : Continuous fun t : H => wr11_Ya S t ω := by
      unfold wr11_Ya
      exact continuous_id.inner continuous_const
    exact (Real.continuous_exp.comp this).continuousAt

lemma wr11_continuous_cF [IsProbabilityMeasure P] (h : Wr11Bdd S C) :
    Continuous (wr11_cF P S) :=
  Continuous.log (wr11_continuous_Z h) fun t => (wr11_Z_pos h t).ne'

/-- Jensen: `log E[exp Y] ≥ E[Y]`. -/
lemma wr11_log_integral_exp_ge {Y : Ω → ℝ} [IsProbabilityMeasure P] (hY : Integrable Y P)
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
    rw [integral_const_mul, integral_add hi (integrable_const _),
      integral_sub hY (integrable_const _)]
    simp [a]
  rw [← h2]
  exact integral_mono ((hY.sub (integrable_const _)).add (integrable_const _) |>.const_mul _) hE h1

/-- `E_P ⟪t, S⟫ ≤ cF(t)`. -/
lemma wr11_integral_Ya_le_cF [IsProbabilityMeasure P] (h : Wr11Bdd S C) (t : H) :
    ∫ ω, wr11_Ya S t ω ∂P ≤ wr11_cF P S t :=
  wr11_log_integral_exp_ge (wr11_integrable_Ya h t) (wr11_integrable_exp_Ya_one h t)

/-- Tilting by `⟪t,S⟫` gives a probability measure. -/
lemma wr11_isProb_tilted [IsProbabilityMeasure P] (h : Wr11Bdd S C) (t : H) :
    IsProbabilityMeasure (P.tilted (wr11_Ya S t)) :=
  isProbabilityMeasure_tilted (wr11_integrable_exp_Ya_one h t)

lemma wr11_integrableExpSet [IsFiniteMeasure P] (h : Wr11Bdd S C) (v : H) :
    integrableExpSet (wr11_Ya S v) P = Set.univ := by
  ext s
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact wr11_integrable_exp_Ya h v s

/-- Shifting `t` by a multiple of `v` changes `cF` by the cumulant generating function of `⟪v,S⟫`
under the tilted law. -/
lemma wr11_cF_add [IsProbabilityMeasure P] (h : Wr11Bdd S C) (t v : H) (s : ℝ) :
    wr11_cF P S (t + s • v) =
      wr11_cF P S t + cgf (wr11_Ya S v) (P.tilted (wr11_Ya S t)) s := by
  have hZ := wr11_Z_pos (P := P) h t
  have hZ' := wr11_Z_pos (P := P) h (t + s • v)
  have hmgf : mgf (wr11_Ya S v) (P.tilted (wr11_Ya S t)) s =
      wr11_Z P S (t + s • v) / wr11_Z P S t := by
    unfold mgf
    rw [integral_exp_tilted (wr11_Ya S t) (fun X => s * wr11_Ya S v X)]
    unfold wr11_Z
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [Pi.add_apply, wr11_Ya_add]
  unfold wr11_cF cgf
  rw [hmgf, Real.log_div hZ'.ne' hZ.ne']
  ring

/-- Derivative of `cF` along the line `s ↦ t + s v` at `s = 0`. -/
lemma wr11_hasDerivAt_cF [IsProbabilityMeasure P] (h : Wr11Bdd S C) (t v : H) :
    HasDerivAt (fun s : ℝ => wr11_cF P S (t + s • v))
      (∫ ω, wr11_Ya S v ω ∂(P.tilted (wr11_Ya S t))) 0 := by
  have := wr11_isProb_tilted (P := P) h t
  have hmem : (0 : ℝ) ∈ interior (integrableExpSet (wr11_Ya S v) (P.tilted (wr11_Ya S t))) := by
    rw [wr11_integrableExpSet h]; simp
  have hc : HasDerivAt (cgf (wr11_Ya S v) (P.tilted (wr11_Ya S t)))
      (∫ ω, wr11_Ya S v ω ∂(P.tilted (wr11_Ya S t))) 0 := by
    have := (analyticAt_cgf hmem).differentiableAt.hasDerivAt
    rwa [deriv_cgf_zero hmem, probReal_univ, div_one] at this
  have e : (fun s : ℝ => wr11_cF P S (t + s • v)) =
      fun s => wr11_cF P S t + cgf (wr11_Ya S v) (P.tilted (wr11_Ya S t)) s := by
    funext s; exact wr11_cF_add h t v s
  rw [e]
  exact HasDerivAt.const_add (wr11_cF P S t) hc

/-- The cumulant generating function of a bounded statistic is convex on `ℝ` (derivative monotone). -/
lemma wr11_monotoneOn_deriv_cgf (h : Wr11Bdd S C) (P' : Measure Ω) [IsProbabilityMeasure P']
    (v : H) : MonotoneOn (deriv (cgf (wr11_Ya S v) P')) Set.univ := by
  have hint : ∀ s : ℝ, s ∈ interior (integrableExpSet (wr11_Ya S v) P') := by
    intro s; rw [wr11_integrableExpSet h]; simp
  have hdiff : Differentiable ℝ (deriv (cgf (wr11_Ya S v) P')) := fun s =>
    (analyticAt_cgf (hint s)).deriv.differentiableAt
  refine monotoneOn_of_deriv_nonneg convex_univ hdiff.continuous.continuousOn
    hdiff.differentiableOn fun s _ => ?_
  have h2 : deriv (deriv (cgf (wr11_Ya S v) P')) s = iteratedDeriv 2 (cgf (wr11_Ya S v) P') s := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, ← variance_tilted_mul (hint s)]
  exact variance_nonneg _ _

lemma wr11_convexOn_cgf (h : Wr11Bdd S C) (P' : Measure Ω) [IsProbabilityMeasure P'] (v : H) :
    ConvexOn ℝ Set.univ (cgf (wr11_Ya S v) P') := by
  have hint : ∀ s : ℝ, s ∈ interior (integrableExpSet (wr11_Ya S v) P') := by
    intro s; rw [wr11_integrableExpSet h]; simp
  have hdiff : Differentiable ℝ (cgf (wr11_Ya S v) P') := fun s =>
    (analyticAt_cgf (hint s)).differentiableAt
  exact MonotoneOn.convexOn_of_deriv convex_univ hdiff.continuous.continuousOn
    hdiff.differentiableOn (by simpa using wr11_monotoneOn_deriv_cgf h P' v)

/-- `cF` is convex on `H`. -/
lemma wr11_convexOn_cF [IsProbabilityMeasure P] (h : Wr11Bdd S C) :
    ConvexOn ℝ Set.univ (wr11_cF P S) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  set v := y - x with hv
  have := wr11_isProb_tilted (P := P) h x
  have hconv := wr11_convexOn_cgf h (P.tilted (wr11_Ya S x)) v
  have hg0 : cgf (wr11_Ya S v) (P.tilted (wr11_Ya S x)) 0 = 0 := by simp
  have hx : a • x + b • y = x + b • v := by
    rw [hv, show a = 1 - b by linarith]; module
  have hy : y = x + (1 : ℝ) • v := by rw [one_smul, hv]; abel
  have h1 := wr11_cF_add (P := P) h x v b
  have h2 := wr11_cF_add (P := P) h x v 1
  rw [← hy] at h2
  have hc := hconv.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) ha hb hab
  simp only [smul_eq_mul, hg0, mul_zero, zero_add, mul_one] at hc
  have ha' : a * wr11_cF P S x = wr11_cF P S x - b * wr11_cF P S x := by
    rw [show a = 1 - b by linarith]; ring
  rw [hx, h1, smul_eq_mul, smul_eq_mul, h2]
  nlinarith [hc, ha']

/-- Monotonicity of the gradient: `E_P ⟪v, S⟫ ≤ E_{P tilted by ⟪v,S⟫} ⟪v, S⟫`. -/
lemma wr11_integral_Ya_le_tilted_self [IsProbabilityMeasure P] (h : Wr11Bdd S C) (v : H) :
    ∫ ω, wr11_Ya S v ω ∂P ≤ ∫ ω, wr11_Ya S v ω ∂(P.tilted (wr11_Ya S v)) := by
  have hint : ∀ s : ℝ, s ∈ interior (integrableExpSet (wr11_Ya S v) P) := by
    intro s; rw [wr11_integrableExpSet h]; simp
  have hmono := wr11_monotoneOn_deriv_cgf h P v (Set.mem_univ 0) (Set.mem_univ 1) zero_le_one
  have d0 : deriv (cgf (wr11_Ya S v) P) 0 = ∫ ω, wr11_Ya S v ω ∂P := by
    rw [deriv_cgf_zero (hint 0), probReal_univ, div_one]
  have d1 : deriv (cgf (wr11_Ya S v) P) 1 =
      ∫ ω, wr11_Ya S v ω ∂(P.tilted (wr11_Ya S v)) := by
    rw [← integral_tilted_mul_self (hint 1)]
    simp only [one_mul]
  rwa [d0, d1] at hmono

end Abstract

end HRS.MS.Wr
