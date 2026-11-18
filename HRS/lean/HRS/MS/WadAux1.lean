import HRS.Whole.Adjoint
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# S8.3, packet D1 (part 1): weights and the Gaussian-average (Mehler) operator

Infrastructure for `HRS.Whole.weighted_adjoint_decay` (S8.3); not a manuscript row.  Namespace
`HRS.MS.Wad`, helper prefix `s83_`.

* `Wt M C f` : `‖f x‖ ≤ C ⟨x⟩^M` for all `x` (a *pointwise* weighted bound, the form used throughout;
  `s83_wsup0_le_iff` translates it into `weightedSupE 0 (-M)`).
* `s83_G c σ f x = ∫ f(c x + σ z) dγ(z)`, `γ = stdGaussian (Euc d)`: the Gaussian-average operator.
  The Mehler semigroup of `L_0 = νΔ - a x·∇` is `P_t = G (e^{-at}) (σ_t)`, `σ_t² = ν(1-e^{-2at})/a`
  (`s83_mc`, `s83_ms`).  The operator is defined for functions with values in any real Banach space `E`.
* Bounds: `⟨x+y⟩^M ≤ 2^M ⟨x⟩^M ⟨y⟩^M` (Peetre), Gaussian moments of `⟨σ z⟩^M`, and the uniform weighted bound
  `‖G c σ f‖_{M} ≤ C 2^M mom ‖f‖_M` for `|c| ≤ 1`, `|σ| ≤ σ₀`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-! ### The weight `⟨x⟩` -/

theorem s83_jb_pos (x : Euc d) : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)

theorem s83_jb_sq (x : Euc d) : jbracket x ^ 2 = 1 + ‖x‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem s83_one_le_jb (x : Euc d) : 1 ≤ jbracket x := by
  have h := s83_jb_sq x
  have h0 := s83_jb_pos x
  by_contra hlt
  push Not at hlt
  nlinarith [sq_nonneg ‖x‖]

theorem s83_norm_le_jb (x : Euc d) : ‖x‖ ≤ jbracket x := by
  have h := s83_jb_sq x
  have h0 := s83_jb_pos x
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg x]

theorem s83_jb_le_one_add (x : Euc d) : jbracket x ≤ 1 + ‖x‖ := by
  have h := s83_jb_sq x
  have h0 := s83_jb_pos x
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg x]

theorem s83_le_of_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  (le_abs_self a).trans (abs_le_of_sq_le_sq h hb)

/-- Peetre's inequality (with constant `2`): `⟨x+y⟩ ≤ 2⟨x⟩⟨y⟩`. -/
theorem s83_jb_add (x y : Euc d) : jbracket (x + y) ≤ 2 * (jbracket x * jbracket y) := by
  have h1 := s83_jb_sq (x + y)
  have h2 := s83_jb_sq x
  have h3 := s83_jb_sq y
  have hn : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
  have hn0 := norm_nonneg (x + y)
  have hx0 := norm_nonneg x
  have hy0 := norm_nonneg y
  refine s83_le_of_sq_le (by have := s83_jb_pos x; have := s83_jb_pos y; positivity) ?_
  have e : (2 * (jbracket x * jbracket y)) ^ 2 = 4 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := by
    rw [mul_pow, mul_pow, h2, h3]; ring
  rw [h1, e]
  have : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ hn0 hn 2
  nlinarith [mul_nonneg hx0 hy0, sq_nonneg ‖x‖, sq_nonneg ‖y‖, sq_nonneg (‖x‖ * ‖y‖)]

theorem s83_jb_add_rpow {M : ℝ} (hM : 0 ≤ M) (x y : Euc d) :
    jbracket (x + y) ^ M ≤ 2 ^ M * (jbracket x ^ M * jbracket y ^ M) := by
  calc jbracket (x + y) ^ M ≤ (2 * (jbracket x * jbracket y)) ^ M :=
        Real.rpow_le_rpow (s83_jb_pos _).le (s83_jb_add x y) hM
    _ = 2 ^ M * (jbracket x ^ M * jbracket y ^ M) := by
        rw [Real.mul_rpow (by norm_num) (mul_nonneg (s83_jb_pos x).le (s83_jb_pos y).le),
          Real.mul_rpow (s83_jb_pos x).le (s83_jb_pos y).le]

theorem s83_jb_smul_le {c : ℝ} (hc : |c| ≤ 1) (x : Euc d) : jbracket (c • x) ≤ jbracket x := by
  unfold jbracket
  refine Real.sqrt_le_sqrt ?_
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have : c ^ 2 ≤ 1 := by
    have := sq_le_one_iff_abs_le_one c |>.2 hc
    exact this
  nlinarith [sq_nonneg ‖x‖]

theorem s83_jb_smul_le_rpow {M c : ℝ} (hM : 0 ≤ M) (hc : |c| ≤ 1) (x : Euc d) :
    jbracket (c • x) ^ M ≤ jbracket x ^ M :=
  Real.rpow_le_rpow (s83_jb_pos _).le (s83_jb_smul_le hc x) hM

/-! ### Pointwise weighted bounds -/

/-- `‖f x‖ ≤ C ⟨x⟩^M` for all `x`. -/
def Wt {E : Type*} [Norm E] (M C : ℝ) (f : Euc d → E) : Prop :=
  ∀ x, ‖f x‖ ≤ C * jbracket x ^ M

theorem Wt.mono {E : Type*} [Norm E] {M C C' : ℝ} {f : Euc d → E} (h : Wt M C f) (hC : C ≤ C') :
    Wt M C' f := fun x =>
  (h x).trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (s83_jb_pos x).le _))

theorem Wt.nonneg {E : Type*} [SeminormedAddCommGroup E] {M C : ℝ} {f : Euc d → E} (h : Wt M C f) :
    0 ≤ C := by
  have h0 := (norm_nonneg (f 0)).trans (h 0)
  have : 0 < jbracket (0 : Euc d) ^ M := Real.rpow_pos_of_pos (s83_jb_pos _) _
  by_contra hC
  push Not at hC
  nlinarith

/-- `weightedSupE 0 (-M) f = ⨆ x, ofReal(⟨x⟩^{-M} |f x|)`. -/
theorem s83_wsup0_eq (M : ℝ) (f : Euc d → ℝ) :
    weightedSupE 0 (-M) f = ⨆ x : Euc d, ENNReal.ofReal (jbracket x ^ (-M) * |f x|) := by
  unfold weightedSupE derivSupE
  apply le_antisymm
  · refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ?_
    have hj : (j : ℕ) = 0 := by
      have := j.2; omega
    have : partialDeriv i f x = f x := by
      unfold partialDeriv
      have hj' : ∀ k (hk : k = 0) (i' : Fin k → Fin d), iteratedFDeriv ℝ k f x
          (fun l => EuclideanSpace.single (i' l) 1) = f x := by
        intro k hk; subst hk; intro i'
        simp [iteratedFDeriv_zero_apply]
      exact hj' _ hj i
    rw [this]
    exact le_iSup (fun x : Euc d => ENNReal.ofReal (jbracket x ^ (-M) * |f x|)) x
  · refine iSup_le fun x => ?_
    refine le_iSup_of_le ⟨0, by omega⟩ ?_
    refine le_iSup_of_le (fun l => l.elim0) ?_
    refine le_iSup_of_le x ?_
    have : partialDeriv (j := ((⟨0, by omega⟩ : Fin 1) : ℕ)) (fun l => l.elim0) f x = f x := by
      unfold partialDeriv
      simp [iteratedFDeriv_zero_apply]
    simp only [this]
    exact le_rfl

/-- The weighted sup norm is `≤ ofReal C` iff the pointwise bound holds. -/
theorem s83_wsup0_le_iff {M C : ℝ} (hC : 0 ≤ C) (f : Euc d → ℝ) :
    weightedSupE 0 (-M) f ≤ ENNReal.ofReal C ↔ Wt M C f := by
  rw [s83_wsup0_eq, iSup_le_iff]
  constructor
  · intro h x
    have := h x
    rw [ENNReal.ofReal_le_ofReal_iff hC] at this
    have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
    have e : jbracket x ^ (-M) = (jbracket x ^ M)⁻¹ := Real.rpow_neg (s83_jb_pos x).le _
    rw [e, inv_mul_le_iff₀ hp] at this
    rw [Real.norm_eq_abs]
    linarith
  · intro h x
    refine ENNReal.ofReal_le_ofReal ?_
    have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
    have e : jbracket x ^ (-M) = (jbracket x ^ M)⁻¹ := Real.rpow_neg (s83_jb_pos x).le _
    rw [e, inv_mul_le_iff₀ hp]
    have := h x
    rwa [Real.norm_eq_abs, mul_comm] at this

/-- A finite weighted sup norm gives a pointwise bound. -/
theorem s83_wt_of_wsup_ne_top {M : ℝ} {f : Euc d → ℝ} (h : weightedSupE 0 (-M) f ≠ ⊤) :
    Wt M (weightedSupE 0 (-M) f).toReal f := by
  have := (s83_wsup0_le_iff (M := M) (ENNReal.toReal_nonneg) f).1
    (by rw [ENNReal.ofReal_toReal h])
  exact this

/-! ### Gaussian moments -/

theorem s83_int_pow (p : ℕ) :
    Integrable (fun z : Euc d => (1 + ‖z‖) ^ p) (stdGaussian (Euc d)) := by
  by_cases hp : p = 0
  · subst hp; simp
  have h1 := IsGaussian.memLp_id (stdGaussian (Euc d)) (p : ℝ≥0∞) (ENNReal.natCast_ne_top p)
  have h1' : MemLp (fun z : Euc d => ‖z‖) (p : ℝ≥0∞) (stdGaussian (Euc d)) := h1.norm
  have h2 : MemLp (fun z : Euc d => 1 + ‖z‖) (p : ℝ≥0∞) (stdGaussian (Euc d)) :=
    (memLp_const (1 : ℝ)).add h1'
  have := h2.integrable_norm_pow hp
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖z‖)]

theorem s83_int_of_poly {E : Type*} [NormedAddCommGroup E] {F : Euc d → E}
    (hF : AEStronglyMeasurable F (stdGaussian (Euc d))) {C : ℝ} {p : ℕ}
    (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ p) : Integrable F (stdGaussian (Euc d)) :=
  ((s83_int_pow p).const_mul C).mono' hF (Eventually.of_forall hb)

/-- The Gaussian moment constant `∫ (1 + σ₀‖z‖)^⌈M⌉ dγ`. -/
def mom (d : ℕ) (M σ₀ : ℝ) : ℝ := ∫ z : Euc d, (1 + σ₀ * ‖z‖) ^ ⌈M⌉₊ ∂(stdGaussian (Euc d))

theorem s83_int_one_add_mul {σ₀ : ℝ} (hσ : 0 ≤ σ₀) (p : ℕ) :
    Integrable (fun z : Euc d => (1 + σ₀ * ‖z‖) ^ p) (stdGaussian (Euc d)) := by
  refine s83_int_of_poly (C := (1 + σ₀) ^ p) (p := p) (by fun_prop) fun z => ?_
  have h0 : 0 ≤ 1 + σ₀ * ‖z‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _), ← mul_pow]
  refine pow_le_pow_left₀ h0 ?_ p
  nlinarith [norm_nonneg z]

theorem s83_mom_nonneg (M σ₀ : ℝ) (hσ : 0 ≤ σ₀) : 0 ≤ mom d M σ₀ := by
  unfold mom
  exact integral_nonneg fun z => pow_nonneg (by positivity) _

/-- `⟨σ z⟩^M ≤ (1 + σ₀‖z‖)^⌈M⌉` for `|σ| ≤ σ₀`, `M ≥ 0`. -/
theorem s83_jb_smul_poly {M σ σ₀ : ℝ} (hM : 0 ≤ M) (hσ : |σ| ≤ σ₀) (z : Euc d) :
    jbracket (σ • z) ^ M ≤ (1 + σ₀ * ‖z‖) ^ ⌈M⌉₊ := by
  have h1 : jbracket (σ • z) ≤ 1 + σ₀ * ‖z‖ := by
    refine (s83_jb_le_one_add _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [norm_nonneg z]
  have h0 : 0 ≤ jbracket (σ • z) := (s83_jb_pos _).le
  have hb : 1 ≤ 1 + σ₀ * ‖z‖ := by
    have : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
    nlinarith [norm_nonneg z]
  calc jbracket (σ • z) ^ M ≤ (1 + σ₀ * ‖z‖) ^ M := Real.rpow_le_rpow h0 h1 hM
    _ ≤ (1 + σ₀ * ‖z‖) ^ (⌈M⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb (Nat.le_ceil M)
    _ = (1 + σ₀ * ‖z‖) ^ ⌈M⌉₊ := Real.rpow_natCast _ _

theorem s83_int_jb_smul {M σ σ₀ : ℝ} (hM : 0 ≤ M) (hσ : |σ| ≤ σ₀) :
    Integrable (fun z : Euc d => jbracket (σ • z) ^ M) (stdGaussian (Euc d)) := by
  have hσ0 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  refine (s83_int_one_add_mul hσ0 ⌈M⌉₊).mono' ?_ (Eventually.of_forall fun z => ?_)
  · have : Continuous fun z : Euc d => jbracket (σ • z) ^ M := by
      unfold jbracket
      refine Continuous.rpow_const (by fun_prop) fun z => Or.inl ?_
      have := (s83_jb_pos (σ • z)).ne'
      unfold jbracket at this
      exact this
    exact this.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _)]
    exact s83_jb_smul_poly hM hσ z

theorem s83_int_jb_smul_le {M σ σ₀ : ℝ} (hM : 0 ≤ M) (hσ : |σ| ≤ σ₀) :
    ∫ z : Euc d, jbracket (σ • z) ^ M ∂(stdGaussian (Euc d)) ≤ mom d M σ₀ := by
  have hσ0 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  exact integral_mono (s83_int_jb_smul hM hσ) (s83_int_one_add_mul hσ0 ⌈M⌉₊)
    fun z => s83_jb_smul_poly hM hσ z

/-! ### The Gaussian-average operator -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Gaussian average `G_{c,σ} f (x) = ∫ f(c x + σ z) dγ(z)`. -/
def s83_G (c σ : ℝ) (f : Euc d → E) (x : Euc d) : E :=
  ∫ z, f (c • x + σ • z) ∂(stdGaussian (Euc d))

theorem s83_cont_shift {f : Euc d → E} (hf : Continuous f) (c σ : ℝ) (x : Euc d) :
    Continuous fun z : Euc d => f (c • x + σ • z) :=
  hf.comp (by fun_prop)

/-- Integrability of `z ↦ f(cx+σz)` for a continuous `f` of weighted growth, `M ≥ 0`. -/
theorem s83_int_shift {f : Euc d → E} (hf : Continuous f) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C f)
    {c σ σ₀ : ℝ} (hσ : |σ| ≤ σ₀) (x : Euc d) :
    Integrable (fun z : Euc d => f (c • x + σ • z)) (stdGaussian (Euc d)) := by
  have hC := hw.nonneg
  refine ((s83_int_jb_smul (M := M) hM hσ).const_mul (C * 2 ^ M * jbracket (c • x) ^ M)).mono'
    (s83_cont_shift hf c σ x).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  refine ((hw _).trans ?_)
  have := s83_jb_add_rpow hM (c • x) (σ • z)
  have hCn : 0 ≤ C := hC
  calc C * jbracket (c • x + σ • z) ^ M ≤ C * (2 ^ M * (jbracket (c • x) ^ M * jbracket (σ • z) ^ M)) :=
        mul_le_mul_of_nonneg_left this hCn
    _ = C * 2 ^ M * jbracket (c • x) ^ M * jbracket (σ • z) ^ M := by ring

/-- **Uniform weighted bound** for the Gaussian average: for `|c| ≤ 1`, `|σ| ≤ σ₀`,
`‖G_{c,σ} f (x)‖ ≤ C 2^M mom(M,σ₀) ⟨x⟩^M`. -/
theorem s83_G_wt [CompleteSpace E] {f : Euc d → E} (hf : Continuous f) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C f)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) :
    Wt M (C * 2 ^ M * mom d M σ₀) (s83_G c σ f) := by
  intro x
  have hC := hw.nonneg
  have hint := s83_int_shift hf hM hw hσ (c := c) x
  have h1 : ‖s83_G c σ f x‖ ≤ ∫ z : Euc d, C * 2 ^ M * jbracket (c • x) ^ M *
      jbracket (σ • z) ^ M ∂(stdGaussian (Euc d)) := by
    refine norm_integral_le_of_norm_le
      ((s83_int_jb_smul (M := M) hM hσ).const_mul (C * 2 ^ M * jbracket (c • x) ^ M))
      (Eventually.of_forall fun z => ?_)
    refine ((hw _).trans ?_)
    have := s83_jb_add_rpow hM (c • x) (σ • z)
    calc C * jbracket (c • x + σ • z) ^ M ≤ C * (2 ^ M * (jbracket (c • x) ^ M * jbracket (σ • z) ^ M)) :=
          mul_le_mul_of_nonneg_left this hC
      _ = C * 2 ^ M * jbracket (c • x) ^ M * jbracket (σ • z) ^ M := by ring
  refine h1.trans ?_
  rw [integral_const_mul]
  have h2 := s83_int_jb_smul_le (d := d) hM hσ
  have h3 : jbracket (c • x) ^ M ≤ jbracket x ^ M := s83_jb_smul_le_rpow hM hc x
  have hpos : 0 ≤ C * 2 ^ M := mul_nonneg hC (by positivity)
  calc C * 2 ^ M * jbracket (c • x) ^ M * ∫ z : Euc d, jbracket (σ • z) ^ M ∂(stdGaussian (Euc d))
      ≤ C * 2 ^ M * jbracket x ^ M * mom d M σ₀ := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h3 hpos) h2
          (integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos _).le _)
          (mul_nonneg hpos (Real.rpow_nonneg (s83_jb_pos x).le _))
    _ = C * 2 ^ M * mom d M σ₀ * jbracket x ^ M := by ring

theorem s83_G_add {f g : Euc d → E} (hf : Continuous f) (hg : Continuous g) {M C C' : ℝ} (hM : 0 ≤ M)
    (hwf : Wt M C f) (hwg : Wt M C' g) {σ σ₀ : ℝ} (c : ℝ) (hσ : |σ| ≤ σ₀) :
    s83_G c σ (f + g) = s83_G c σ f + s83_G c σ g := by
  funext x
  simp only [s83_G, Pi.add_apply]
  exact integral_add (s83_int_shift hf hM hwf hσ x) (s83_int_shift hg hM hwg hσ x)

theorem s83_G_smul (c σ : ℝ) (r : ℝ) (f : Euc d → E) :
    s83_G c σ (r • f) = r • s83_G c σ f := by
  funext x
  simp only [s83_G, Pi.smul_apply]
  exact integral_smul r _

theorem s83_int_const [CompleteSpace E] (v : E) : ∫ _ : Euc d, v ∂(stdGaussian (Euc d)) = v := by
  rw [integral_const]; simp

theorem s83_G_zero_scale [CompleteSpace E] (f : Euc d → E) (x : Euc d) : s83_G 1 0 f x = f x := by
  simp [s83_G, s83_int_const]

end Operator

/-! ### The Mehler parameters -/

/-- `e^{-at}`. -/
def s83_mc (a t : ℝ) : ℝ := Real.exp (-a * t)

/-- `σ_t = sqrt(ν (1 - e^{-2at}) / a)`. -/
def s83_ms (a ν t : ℝ) : ℝ := Real.sqrt (ν * (1 - Real.exp (-2 * a * t)) / a)

theorem s83_mc_pos (a t : ℝ) : 0 < s83_mc a t := Real.exp_pos _

theorem s83_mc_le_one {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) : s83_mc a t ≤ 1 := by
  unfold s83_mc
  rw [Real.exp_le_one_iff]
  nlinarith

theorem s83_abs_mc_le_one {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) : |s83_mc a t| ≤ 1 := by
  rw [abs_of_pos (s83_mc_pos a t)]; exact s83_mc_le_one ha ht

theorem s83_mc_add (a t s : ℝ) : s83_mc a (t + s) = s83_mc a t * s83_mc a s := by
  unfold s83_mc; rw [← Real.exp_add]; congr 1; ring

theorem s83_mc_zero (a : ℝ) : s83_mc a 0 = 1 := by simp [s83_mc]

theorem s83_ms_zero (a ν : ℝ) : s83_ms a ν 0 = 0 := by simp [s83_ms]

/-- `σ_t² = ν (1 - e^{-2at}) / a`. -/
theorem s83_ms_sq {a ν t : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    s83_ms a ν t ^ 2 = ν * (1 - Real.exp (-2 * a * t)) / a := by
  unfold s83_ms
  refine Real.sq_sqrt ?_
  have : Real.exp (-2 * a * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have : 0 ≤ 1 - Real.exp (-2 * a * t) := by linarith
  positivity

theorem s83_ms_nonneg (a ν t : ℝ) : 0 ≤ s83_ms a ν t := Real.sqrt_nonneg _

/-- `σ_t ≤ sqrt(ν / a)` for all `t ≥ 0`. -/
theorem s83_ms_le {a ν t : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    s83_ms a ν t ≤ Real.sqrt (ν / a) := by
  unfold s83_ms
  refine Real.sqrt_le_sqrt ?_
  have : 0 ≤ Real.exp (-2 * a * t) := (Real.exp_pos _).le
  rw [div_le_div_iff_of_pos_right ha]
  nlinarith

theorem s83_abs_ms_le {a ν t : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    |s83_ms a ν t| ≤ Real.sqrt (ν / a) := by
  rw [abs_of_nonneg (s83_ms_nonneg _ _ _)]; exact s83_ms_le ha hν ht

/-- The Mehler semigroup `P_t = G_{e^{-at}, σ_t}` of `νΔ - a x·∇`. -/
def s83_P {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a ν t : ℝ) (f : Euc d → E) :
    Euc d → E := s83_G (s83_mc a t) (s83_ms a ν t) f

theorem s83_P_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (a ν : ℝ) (f : Euc d → E) :
    s83_P a ν 0 f = f := by
  funext x
  simp [s83_P, s83_G, s83_mc_zero, s83_ms_zero, s83_int_const]

/-- The uniform weighted bound for the Mehler semigroup (`D1`, boundedness): for `M ≥ 0`, `a, ν > 0`,
`t ≥ 0`: `‖P_t f‖_M ≤ K_M ‖f‖_M` with `K_M = 2^M mom(M, sqrt(ν/a))` independent of `t`. -/
theorem s83_P_wt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : Euc d → E} (hf : Continuous f) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C f) {a ν t : ℝ}
    (ha : 0 < a) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    Wt M (C * 2 ^ M * mom d M (Real.sqrt (ν / a))) (s83_P a ν t f) :=
  s83_G_wt hf hM hw (s83_abs_mc_le_one ha.le ht) (s83_abs_ms_le ha hν ht)

end HRS.MS.Wad
