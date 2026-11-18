import HRS.Stochastic.BDG

/-!
# Lévy's characterisation and the Dambis–Dubins–Schwarz theorem

Package SI-01, part 8 (last packets).  Stated for the abstract predicates of
`HRS/Prob/CLT.lean` (`IsContSqMartingale`, `IsQuadraticVariation`), which is what `dds_coupling`
(Lemma A.19, M L10520-10534) consumes.

* `levy_characterization`: a continuous adapted `ι`-family `β` with `β_0 = 0` such that `β^k` and
  `β^k β^l - δ_{kl} t` are martingales is Brownian relative to its filtration
  (M L2148, L2430, S L2724).
* `brownian_stopped_L2_bound`: for a Brownian filtration and a finite stopping time `S ≥ 0` with
  `E S < ∞`, `E|β_S - β_v|² ≤ E|S - v|` (the computation of M L10529-10533).  Route: the two
  terms are `E (∫ 1_{(v, S ∨ v]} dβ)² = E[(S - v)⁺]` and `E (∫ 1_{(S ∧ v, v]} dβ)² = E[(v - S)⁺]`
  by the Itô isometry for stopping-time indicator integrands and the stopping identity; this
  avoids the strong Markov property used in the source.
* `dambis_dubins_schwarz`: for a continuous `L²` martingale `M` on `[0, t]` with quadratic
  variation `A` and `E A_t < ∞`, on an enlargement there are a Brownian filtration `(ℱ', β)`,
  copies `(M', A')` with the same finite-dimensional laws, with `A'_τ` an `ℱ'`-stopping time and
  `M'_τ = β_{A'_τ}` for all `τ ≤ t`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

section LevyPointwise

open Complex in
/-- Third-order Taylor bound for the factor `exp(i x + δ/2)` of the exponential martingale. -/
theorem norm_levy_remainder_le {x δ X : ℝ} (hx : |x| ≤ X) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ‖Complex.exp (Complex.I * x + δ / 2) - 1 - Complex.I * x - ((δ : ℂ) - (x : ℂ) ^ 2) / 2‖ ≤
      (4 * Real.exp (X + 1) + 1) * (|x| ^ 3 + |x| * δ + δ ^ 2) := by
  set w : ℂ := Complex.I * x + δ / 2 with hw
  have hwn : ‖w‖ ≤ |x| + δ / 2 := by
    calc ‖w‖ ≤ ‖Complex.I * (x : ℂ)‖ + ‖(δ : ℂ) / 2‖ := norm_add_le _ _
      _ = |x| + δ / 2 := by
        simp [abs_of_nonneg hδ0]
  have h1 := Complex.norm_exp_sub_sum_le_norm_mul_exp w 3
  have e1 : ∑ m ∈ Finset.range 3, w ^ m / (m.factorial : ℂ) = 1 + w + w ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [e1] at h1
  have e2 : Complex.exp w - 1 - Complex.I * x - ((δ : ℂ) - (x : ℂ) ^ 2) / 2 =
      (Complex.exp w - (1 + w + w ^ 2 / 2)) + (Complex.I * x * δ / 2 + (δ : ℂ) ^ 2 / 8) := by
    rw [hw]; ring_nf; simp [Complex.I_sq]; ring
  rw [e2]
  have hX : 0 ≤ X := (abs_nonneg x).trans hx
  have h3 : ‖w‖ ^ 3 * Real.exp ‖w‖ ≤ 4 * (|x| ^ 3 + δ ^ 2) * Real.exp (X + 1) := by
    have h4 : ‖w‖ ≤ |x| + δ := by linarith
    have h5 : ‖w‖ ^ 3 ≤ 4 * (|x| ^ 3 + δ ^ 2) := by
      have : (|x| + δ) ^ 3 ≤ 4 * (|x| ^ 3 + δ ^ 3) := by
        nlinarith [sq_nonneg (|x| - δ), abs_nonneg x, mul_nonneg (abs_nonneg x) hδ0,
          mul_nonneg (mul_nonneg (abs_nonneg x) hδ0) (sq_nonneg (|x| - δ))]
      have h6 : δ ^ 3 ≤ δ ^ 2 := by nlinarith [sq_nonneg δ]
      calc ‖w‖ ^ 3 ≤ (|x| + δ) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h4 3
        _ ≤ _ := by linarith
    have h7 : Real.exp ‖w‖ ≤ Real.exp (X + 1) := Real.exp_le_exp.2 (by linarith)
    calc ‖w‖ ^ 3 * Real.exp ‖w‖ ≤ (4 * (|x| ^ 3 + δ ^ 2)) * Real.exp (X + 1) :=
          mul_le_mul h5 h7 (Real.exp_pos _).le (by positivity)
      _ = _ := rfl
  have h8 : ‖Complex.I * (x : ℂ) * (δ : ℂ) / 2 + (δ : ℂ) ^ 2 / 8‖ ≤ |x| * δ + δ ^ 2 := by
    calc _ ≤ ‖Complex.I * (x : ℂ) * (δ : ℂ) / 2‖ + ‖(δ : ℂ) ^ 2 / 8‖ := norm_add_le _ _
      _ = |x| * δ / 2 + δ ^ 2 / 8 := by simp [abs_of_nonneg hδ0]
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg x) hδ0, sq_nonneg δ]
  calc _ ≤ ‖Complex.exp w - (1 + w + w ^ 2 / 2)‖ + ‖Complex.I * (x : ℂ) * (δ : ℂ) / 2 + (δ : ℂ) ^ 2 / 8‖ :=
        norm_add_le _ _
    _ ≤ 4 * (|x| ^ 3 + δ ^ 2) * Real.exp (X + 1) + (|x| * δ + δ ^ 2) := add_le_add (h1.trans h3) h8
    _ ≤ _ := by
        have : 0 ≤ Real.exp (X + 1) := (Real.exp_pos _).le
        have h9 : 1 ≤ Real.exp (X + 1) := Real.one_le_exp (by linarith)
        nlinarith [pow_nonneg (abs_nonneg x) 3, sq_nonneg δ, mul_nonneg (abs_nonneg x) hδ0]

end LevyPointwise


set_option linter.unusedSectionVars false

section LevyTest

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}

/-- Martingale property against a bounded `ℱ s`-measurable test function. -/
theorem integral_mul_martingale {M : ℝ → Ω → ℝ} (hM : Martingale M ℱ P) {s t : ℝ} (hst : s ≤ t)
    {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ s] g) {C : ℝ} (hgC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * M t ω ∂P = ∫ ω, g ω * M s ω ∂P := by
  have hgm : StronglyMeasurable g := hg.mono (ℱ.le s)
  have hgi : Integrable (g * M t) P := by
    refine (hM.integrable t).bdd_mul (c := C) hgm.aestronglyMeasurable ?_
    exact Eventually.of_forall fun ω => by simpa using hgC ω
  have hc : P[g * M t | ℱ s] =ᵐ[P] g * P[M t | ℱ s] :=
    condExp_mul_of_stronglyMeasurable_left hg hgi (hM.integrable t)
  have h1 := integral_condExp (μ := P) (m := ℱ s) (f := g * M t) (ℱ.le s)
  calc ∫ ω, g ω * M t ω ∂P = ∫ ω, (P[g * M t | ℱ s]) ω ∂P := h1.symm
    _ = ∫ ω, g ω * M s ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hc, hM.2 s t hst] with ω h1 h2
        rw [h1]; simp [h2]


/-- Complex test functions against a real martingale. -/
theorem integral_cmul_martingale {M : ℝ → Ω → ℝ} (hM : Martingale M ℱ P) {s t : ℝ} (hst : s ≤ t)
    {g : Ω → ℂ} (hg : StronglyMeasurable[ℱ s] g) {C : ℝ} (hgC : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, g ω * (M t ω : ℂ) ∂P = ∫ ω, g ω * (M s ω : ℂ) ∂P := by
  have hgm : StronglyMeasurable g := hg.mono (ℱ.le s)
  have hi : ∀ u, Integrable (fun ω => g ω * (M u ω : ℂ)) P := fun u =>
    (hM.integrable u).ofReal.bdd_mul (c := C) hgm.aestronglyMeasurable
      (Eventually.of_forall hgC)
  have hre : StronglyMeasurable[ℱ s] fun ω => (g ω).re := Complex.continuous_re.comp_stronglyMeasurable hg
  have him : StronglyMeasurable[ℱ s] fun ω => (g ω).im := Complex.continuous_im.comp_stronglyMeasurable hg
  have hreC : ∀ ω, |(g ω).re| ≤ C := fun ω => (Complex.abs_re_le_norm _).trans (hgC ω)
  have himC : ∀ ω, |(g ω).im| ≤ C := fun ω => (Complex.abs_im_le_norm _).trans (hgC ω)
  have key : ∀ u, (∫ ω, g ω * (M u ω : ℂ) ∂P).re = ∫ ω, (g ω).re * M u ω ∂P := fun u => by
    rw [← RCLike.re_eq_complex_re, ← integral_re (hi u)]
    simp
  have key' : ∀ u, (∫ ω, g ω * (M u ω : ℂ) ∂P).im = ∫ ω, (g ω).im * M u ω ∂P := fun u => by
    rw [← RCLike.im_eq_complex_im, ← integral_im (hi u)]
    simp
  apply Complex.ext
  · rw [key, key]; exact integral_mul_martingale hM hst hre hreC
  · rw [key', key']; exact integral_mul_martingale hM hst him himC


theorem measurable_bdd_integrable {f : Ω → ℝ} (hf : Measurable f) (K : ℝ) (hK : ∀ ω, |f ω| ≤ K) :
    Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable K (Eventually.of_forall fun ω => by simpa using hK ω)

/-- Running maximum of the absolute values `|f 0|, …, |f (k-1)|`. -/
def runMax (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun ω => max (runMax f k ω) |f k ω|

theorem runMax_nonneg (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : 0 ≤ runMax f k ω := by
  induction k with
  | zero => simp [runMax]
  | succ k ih => exact ih.trans (le_max_left _ _)

theorem abs_le_runMax (f : ℕ → Ω → ℝ) {j k : ℕ} (hjk : j < k) (ω : Ω) : |f j ω| ≤ runMax f k ω := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with h | h
    · exact (ih h).trans (le_max_left _ _)
    · subst h; exact le_max_right _ _

theorem runMax_le (f : ℕ → Ω → ℝ) {B : ℝ} (hB : 0 ≤ B) (hf : ∀ j ω, |f j ω| ≤ B) (k : ℕ) (ω : Ω) :
    runMax f k ω ≤ B := by
  induction k with
  | zero => simpa [runMax] using hB
  | succ k ih => exact max_le ih (hf k ω)

theorem runMax_le_of (f : ℕ → Ω → ℝ) {B : ℝ} (k : ℕ) (ω : Ω) (hf : ∀ j < k, |f j ω| ≤ B)
    (hB : 0 ≤ B) : runMax f k ω ≤ B := by
  induction k with
  | zero => simpa [runMax] using hB
  | succ k ih =>
    exact max_le (ih fun j hj => hf j (Nat.lt_succ_of_lt hj)) (hf k (Nat.lt_succ_self k))

theorem measurable_runMax {f : ℕ → Ω → ℝ} (hf : ∀ j, Measurable (f j)) (k : ℕ) :
    Measurable (runMax f k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact ih.max (hf k).abs

/-- The data of the bounded exponential-martingale lemma: a bounded continuous martingale `N`
with `N² - A` a martingale for a monotone `a`-Lipschitz clock `A`. -/
structure LevyData (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (N A : ℝ → Ω → ℝ) (R a : ℝ) : Prop where
  ha : 0 ≤ a
  hR : 0 ≤ R
  mart : Martingale N ℱ P
  cont : ∀ ω, Continuous fun t => N t ω
  bdd : ∀ t ω, |N t ω| ≤ R
  adaptedA : StronglyAdapted ℱ A
  contA : ∀ ω, Continuous fun t => A t ω
  monoA : ∀ ω u v, u ≤ v → A u ω ≤ A v ω
  lipA : ∀ ω u v, u ≤ v → A v ω - A u ω ≤ a * (v - u)
  nonnegA : ∀ t ω, 0 ≤ A t ω
  boundA : ∀ t ω, A t ω ≤ a * max t 0
  qv : Martingale (fun t ω => N t ω ^ 2 - A t ω) ℱ P

namespace LevyData

variable {N A : ℝ → Ω → ℝ} {R a : ℝ} (hD : LevyData P ℱ N A R a)
include hD

theorem measurable_N (t : ℝ) : Measurable (N t) := ((hD.mart.1 t).mono (ℱ.le t)).measurable

theorem measurable_A (t : ℝ) : Measurable (A t) := ((hD.adaptedA t).mono (ℱ.le t)).measurable

theorem integrable_N (t : ℝ) : Integrable (N t) P := hD.mart.integrable t

theorem integrable_A (t : ℝ) : Integrable (A t) P :=
  Integrable.of_bound (hD.measurable_A t).aestronglyMeasurable (a * max t 0)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hD.nonnegA t ω)]; exact hD.boundA t ω)


theorem integral_real_incr (u v : ℝ) (huv : u ≤ v) {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ u] g)
    {C : ℝ} (hgC : ∀ ω, |g ω| ≤ C) : ∫ ω, g ω * (N v ω - N u ω) ∂P = 0 := by
  have hgm : Measurable g := (hg.mono (ℱ.le u)).measurable
  have hi : ∀ w, Integrable (fun ω => g ω * N w ω) P := fun w =>
    (hD.integrable_N w).bdd_mul (c := C) hgm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa using hgC ω)
  simp_rw [mul_sub]
  rw [integral_sub (hi v) (hi u), integral_mul_martingale hD.mart huv hg hgC, sub_self]

theorem integral_real_sq_incr (u v : ℝ) (huv : u ≤ v) {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ u] g)
    {C : ℝ} (hgC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * ((N v ω - N u ω) ^ 2 - (A v ω - A u ω)) ∂P = 0 := by
  have hgm : Measurable g := (hg.mono (ℱ.le u)).measurable
  have hR := hD.hR
  have hNb : ∀ w ω, |N w ω| ≤ R := hD.bdd
  -- test function `g * N u`
  have hgN : StronglyMeasurable[ℱ u] fun ω => g ω * N u ω := hg.mul (hD.mart.1 u)
  have hgNC : ∀ ω, |g ω * N u ω| ≤ C * R := fun ω => by
    rw [abs_mul]; exact mul_le_mul (hgC ω) (hNb u ω) (abs_nonneg _) ((abs_nonneg _).trans (hgC ω))
  have hgb : ∀ f : Ω → ℝ, Measurable f → ∀ K, (∀ ω, |f ω| ≤ K) → Integrable f P :=
    fun f hf K hK => Integrable.of_bound hf.aestronglyMeasurable K
      (Eventually.of_forall fun ω => by simpa using hK ω)
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgC (Classical.arbitrary Ω))
  have hQ := integral_mul_martingale hD.qv huv hg hgC
  have hGN := integral_mul_martingale hD.mart huv hgN hgNC
  have e : (fun ω => g ω * ((N v ω - N u ω) ^ 2 - (A v ω - A u ω))) = fun ω =>
      g ω * (N v ω ^ 2 - A v ω) - 2 * ((g ω * N u ω) * N v ω) + g ω * N u ω ^ 2 + g ω * A u ω := by
    funext ω; ring
  rw [e]
  have i1 : Integrable (fun ω => g ω * (N v ω ^ 2 - A v ω)) P :=
    hgb _ (hgm.mul (((hD.measurable_N v).pow_const 2).sub (hD.measurable_A v))) (C * (R ^ 2 + a * max v 0))
      (fun ω => by
        rw [abs_mul]
        refine mul_le_mul (hgC ω) ?_ (abs_nonneg _) hC
        have := hD.bdd v ω
        have h2 : |N v ω ^ 2| ≤ R ^ 2 := by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
        have h3 := hD.boundA v ω
        have h4 := hD.nonnegA v ω
        calc |N v ω ^ 2 - A v ω| ≤ |N v ω ^ 2| + |A v ω| := abs_sub _ _
          _ ≤ _ := by rw [abs_of_nonneg h4]; linarith)
  have i2 : Integrable (fun ω => (g ω * N u ω) * N v ω) P :=
    hgb _ ((hgm.mul (hD.measurable_N u)).mul (hD.measurable_N v)) (C * R * R) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (hgNC ω) (hNb v ω) (abs_nonneg _) (by positivity))
  have i3 : Integrable (fun ω => g ω * N u ω ^ 2) P :=
    hgb _ (hgm.mul ((hD.measurable_N u).pow_const 2)) (C * R ^ 2) (fun ω => by
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hgC ω) (pow_le_pow_left₀ (abs_nonneg _) (hNb u ω) 2) (by positivity) hC)
  have i4 : Integrable (fun ω => g ω * A u ω) P :=
    hgb _ (hgm.mul (hD.measurable_A u)) (C * (a * max u 0)) (fun ω => by
      rw [abs_mul, abs_of_nonneg (hD.nonnegA u ω)]
      exact mul_le_mul (hgC ω) (hD.boundA u ω) (hD.nonnegA u ω) hC)
  have j1 : Integrable (fun ω => g ω * (N v ω ^ 2 - A v ω) - 2 * (g ω * N u ω * N v ω)) P :=
    i1.sub (i2.const_mul 2)
  have j2 : Integrable (fun ω => g ω * (N v ω ^ 2 - A v ω) - 2 * (g ω * N u ω * N v ω) +
      g ω * N u ω ^ 2) P := j1.add i3
  rw [integral_add j2 i4, integral_add j1 i3, integral_sub i1 (i2.const_mul 2), integral_const_mul]
  have hQ' : ∫ ω, g ω * (N v ω ^ 2 - A v ω) ∂P = ∫ ω, g ω * (N u ω ^ 2 - A u ω) ∂P := hQ
  have hQ'' : ∫ ω, g ω * (N u ω ^ 2 - A u ω) ∂P =
      ∫ ω, g ω * N u ω ^ 2 ∂P - ∫ ω, g ω * A u ω ∂P := by
    simp_rw [mul_sub]; exact integral_sub i3 i4
  have hGN' : ∫ ω, (g ω * N u ω) * N v ω ∂P = ∫ ω, g ω * N u ω ^ 2 ∂P := by
    rw [hGN]; simp_rw [mul_assoc, ← sq]
  rw [hQ', hQ'', hGN']
  ring



end LevyData

theorem integral_cmul_eq_zero_of_real {F : Ω → ℝ} (hF : Integrable F P) {u : ℝ}
    (h : ∀ g : Ω → ℝ, StronglyMeasurable[ℱ u] g → ∀ C : ℝ, (∀ ω, |g ω| ≤ C) →
      ∫ ω, g ω * F ω ∂P = 0)
    {g : Ω → ℂ} (hg : StronglyMeasurable[ℱ u] g) {C : ℝ} (hgC : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, g ω * (F ω : ℂ) ∂P = 0 := by
  have hgm : StronglyMeasurable g := hg.mono (ℱ.le u)
  have hi : Integrable (fun ω => g ω * (F ω : ℂ)) P :=
    hF.ofReal.bdd_mul (c := C) hgm.aestronglyMeasurable (Eventually.of_forall hgC)
  have hre : StronglyMeasurable[ℱ u] fun ω => (g ω).re :=
    Complex.continuous_re.comp_stronglyMeasurable hg
  have him : StronglyMeasurable[ℱ u] fun ω => (g ω).im :=
    Complex.continuous_im.comp_stronglyMeasurable hg
  have hreC : ∀ ω, |(g ω).re| ≤ C := fun ω => (Complex.abs_re_le_norm _).trans (hgC ω)
  have himC : ∀ ω, |(g ω).im| ≤ C := fun ω => (Complex.abs_im_le_norm _).trans (hgC ω)
  apply Complex.ext
  · have : (∫ ω, g ω * (F ω : ℂ) ∂P).re = ∫ ω, (g ω).re * F ω ∂P := by
      rw [← RCLike.re_eq_complex_re, ← integral_re hi]; simp
    rw [this, h _ hre C hreC]; simp
  · have : (∫ ω, g ω * (F ω : ℂ) ∂P).im = ∫ ω, (g ω).im * F ω ∂P := by
      rw [← RCLike.im_eq_complex_im, ← integral_im hi]; simp
    rw [this, h _ him C himC]; simp

namespace LevyData

variable {N A : ℝ → Ω → ℝ} {R a : ℝ} (hD : LevyData P ℱ N A R a)
include hD

theorem integral_cmul_incr (u v : ℝ) (huv : u ≤ v) {g : Ω → ℂ} (hg : StronglyMeasurable[ℱ u] g)
    {C : ℝ} (hgC : ∀ ω, ‖g ω‖ ≤ C) : ∫ ω, g ω * ((N v ω - N u ω : ℝ) : ℂ) ∂P = 0 :=
  integral_cmul_eq_zero_of_real ((hD.integrable_N v).sub (hD.integrable_N u))
    (fun g' hg' C' hC' => hD.integral_real_incr u v huv hg' hC') hg hgC

theorem integral_cmul_sq_incr (u v : ℝ) (huv : u ≤ v) {g : Ω → ℂ} (hg : StronglyMeasurable[ℱ u] g)
    {C : ℝ} (hgC : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, g ω * (((N v ω - N u ω) ^ 2 - (A v ω - A u ω) : ℝ) : ℂ) ∂P = 0 := by
  refine integral_cmul_eq_zero_of_real ?_
    (fun g' hg' C' hC' => hD.integral_real_sq_incr u v huv hg' hC') hg hgC
  have hb : ∀ w ω, |N w ω| ≤ R := hD.bdd
  have h1 : Integrable (fun ω => (N v ω - N u ω) ^ 2) P :=
    Integrable.of_bound (((hD.measurable_N v).sub (hD.measurable_N u)).pow_const 2).aestronglyMeasurable
      ((2 * R) ^ 2) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        calc |N v ω - N u ω| ≤ |N v ω| + |N u ω| := abs_sub _ _
          _ ≤ 2 * R := by linarith [hb v ω, hb u ω])
  exact h1.sub ((hD.integrable_A v).sub (hD.integrable_A u))

/-- The exponential martingale `exp(i N + A/2)` of the data. -/
def expMart (N A : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * (N t ω : ℂ) + (A t ω : ℂ) / 2)

theorem measurable_expMart (t : ℝ) : Measurable (expMart N A t) := by
  have := hD.measurable_N t
  have := hD.measurable_A t
  unfold expMart
  fun_prop

theorem norm_expMart (t : ℝ) (ω : Ω) : ‖expMart N A t ω‖ = Real.exp (A t ω / 2) := by
  unfold expMart
  rw [Complex.norm_exp]
  simp

theorem norm_expMart_le {t T : ℝ} (ht : max t 0 ≤ T) (ω : Ω) :
    ‖expMart N A t ω‖ ≤ Real.exp (a * T / 2) := by
  rw [hD.norm_expMart]
  refine Real.exp_le_exp.2 ?_
  have := hD.boundA t ω
  have h2 : a * max t 0 ≤ a * T := mul_le_mul_of_nonneg_left ht hD.ha
  linarith

theorem expMart_step (u v : ℝ) (ω : Ω) :
    expMart N A v ω - expMart N A u ω = expMart N A u ω *
      (Complex.exp (Complex.I * ((N v ω - N u ω : ℝ) : ℂ) + ((A v ω - A u ω : ℝ) : ℂ) / 2) - 1) := by
  unfold expMart
  rw [mul_sub, ← Complex.exp_add]
  push_cast
  ring_nf


theorem stronglyMeasurable_expMart (u : ℝ) : StronglyMeasurable[ℱ u] (expMart N A u) := by
  unfold expMart
  refine Complex.continuous_exp.comp_stronglyMeasurable ?_
  exact (stronglyMeasurable_const.mul (Complex.continuous_ofReal.comp_stronglyMeasurable
    (hD.mart.1 u))).add 
    ((continuous_id.div_const (2 : ℂ)).comp_stronglyMeasurable
      (Complex.continuous_ofReal.comp_stronglyMeasurable (hD.adaptedA u)))

theorem step_bound (u v T : ℝ) (huv : u ≤ v) (hvT : max u 0 ≤ T) (hδ : a * (v - u) ≤ 1)
    {g : Ω → ℂ} (hg : StronglyMeasurable[ℱ u] g) {C : ℝ} (hgC : ∀ ω, ‖g ω‖ ≤ C) :
    ‖∫ ω, g ω * (expMart N A v ω - expMart N A u ω) ∂P‖ ≤
      C * Real.exp (a * T / 2) * (4 * Real.exp (2 * R + 1) + 1) *
        ∫ ω, (|N v ω - N u ω| ^ 3 + |N v ω - N u ω| * (A v ω - A u ω) +
          (A v ω - A u ω) ^ 2) ∂P := by
  have hC : 0 ≤ C := by
    have : Nonempty Ω := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hgC (Classical.arbitrary Ω))
  set G : Ω → ℂ := fun ω => g ω * expMart N A u ω with hG
  set B : ℝ := C * Real.exp (a * T / 2) with hB
  have hGm : StronglyMeasurable[ℱ u] G := hg.mul (hD.stronglyMeasurable_expMart u)
  have hGC : ∀ ω, ‖G ω‖ ≤ B := fun ω => by
    rw [hG, norm_mul]
    exact mul_le_mul (hgC ω) (hD.norm_expMart_le hvT ω) (norm_nonneg _) hC
  clear_value G
  have hB0 : 0 ≤ B := by positivity
  -- pointwise decomposition
  set x : Ω → ℝ := fun ω => N v ω - N u ω with hx
  set δ : Ω → ℝ := fun ω => A v ω - A u ω with hδdef
  have hxm : Measurable x := (hD.measurable_N v).sub (hD.measurable_N u)
  have hδm : Measurable δ := (hD.measurable_A v).sub (hD.measurable_A u)
  have hxb : ∀ ω, |x ω| ≤ 2 * R := fun ω => by
    calc |x ω| ≤ |N v ω| + |N u ω| := abs_sub _ _
      _ ≤ 2 * R := by linarith [hD.bdd v ω, hD.bdd u ω]
  have hδ0 : ∀ ω, 0 ≤ δ ω := fun ω => sub_nonneg.2 (hD.monoA ω u v huv)
  have hδ1 : ∀ ω, δ ω ≤ 1 := fun ω => (hD.lipA ω u v huv).trans hδ
  set E : Ω → ℂ := fun ω => Complex.exp (Complex.I * (x ω : ℂ) + (δ ω : ℂ) / 2) with hE
  set ε : Ω → ℂ := fun ω => E ω - 1 - Complex.I * (x ω : ℂ) - ((δ ω : ℂ) - (x ω : ℂ) ^ 2) / 2 with hε
  have hEm : Measurable E := by
    simp only [hE]; fun_prop
  have hεm : Measurable ε := by
    simp only [hε]; fun_prop
  have hεb : ∀ ω, ‖ε ω‖ ≤ (4 * Real.exp (2 * R + 1) + 1) *
      (|x ω| ^ 3 + |x ω| * δ ω + δ ω ^ 2) := fun ω =>
    norm_levy_remainder_le (hxb ω) (hδ0 ω) (hδ1 ω)
  set K : ℝ := 4 * Real.exp (2 * R + 1) + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  have hGmeas : Measurable G := (hGm.mono (ℱ.le u)).measurable
  set bd : Ω → ℝ := fun ω => |x ω| ^ 3 + |x ω| * δ ω + δ ω ^ 2 with hbd
  have hbdm : Measurable bd := by simp only [hbd]; fun_prop
  have hbd0 : ∀ ω, 0 ≤ bd ω := fun ω => by
    simp only [hbd]; have := hδ0 ω; positivity
  have hbdb : ∀ ω, bd ω ≤ (2 * R) ^ 3 + 2 * R + 1 := fun ω => by
    simp only [hbd]
    have h1 := hxb ω
    have h2 := hδ0 ω
    have h3 := hδ1 ω
    have h4 : |x ω| ^ 3 ≤ (2 * R) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
    have h5 : |x ω| * δ ω ≤ 2 * R * 1 := mul_le_mul h1 h3 h2 (by linarith [abs_nonneg (x ω)])
    nlinarith
  have hbdi : Integrable bd P :=
    Integrable.of_bound hbdm.aestronglyMeasurable ((2 * R) ^ 3 + 2 * R + 1)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbd0 ω)]; exact hbdb ω)
  have hint : ∀ f : Ω → ℂ, Measurable f → ∀ M : ℝ, (∀ ω, ‖f ω‖ ≤ M) → Integrable f P :=
    fun f hf M hM => Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall hM)
  have hxC : Measurable fun ω => (x ω : ℂ) := Complex.measurable_ofReal.comp hxm
  have hδC : Measurable fun ω => (δ ω : ℂ) := Complex.measurable_ofReal.comp hδm
  have hxCb : ∀ ω, ‖(x ω : ℂ)‖ ≤ 2 * R := fun ω => by simpa using hxb ω
  have hδCb : ∀ ω, ‖(δ ω : ℂ)‖ ≤ 1 := fun ω => by
    simpa [abs_of_nonneg (hδ0 ω)] using hδ1 ω
  -- the three pieces
  have iA : Integrable (fun ω => G ω * ε ω) P :=
    Integrable.mono' (hbdi.const_mul (B * K)) (hGmeas.mul hεm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [norm_mul]
        calc ‖G ω‖ * ‖ε ω‖ ≤ B * (K * bd ω) :=
              mul_le_mul (hGC ω) (hεb ω) (norm_nonneg _) hB0
          _ = B * K * bd ω := by ring)
  have iB : Integrable (fun ω => G ω * (Complex.I * (x ω : ℂ))) P :=
    hint _ (hGmeas.mul (measurable_const.mul hxC)) (B * (1 * (2 * R))) (fun ω => by
      rw [norm_mul, norm_mul, Complex.norm_I]
      exact mul_le_mul (hGC ω) (mul_le_mul_of_nonneg_left (hxCb ω) zero_le_one) (by positivity) hB0)
  have iC : Integrable (fun ω => G ω * (((δ ω : ℂ) - (x ω : ℂ) ^ 2) / 2)) P :=
    hint _ (hGmeas.mul ((hδC.sub (hxC.pow_const 2)).div_const 2)) (B * ((1 + (2 * R) ^ 2) / 2))
      (fun ω => by
        rw [norm_mul, norm_div]
        refine mul_le_mul (hGC ω) ?_ (by positivity) hB0
        have h1 : ‖(δ ω : ℂ) - (x ω : ℂ) ^ 2‖ ≤ 1 + (2 * R) ^ 2 := by
          calc _ ≤ ‖(δ ω : ℂ)‖ + ‖(x ω : ℂ) ^ 2‖ := norm_sub_le _ _
            _ ≤ 1 + (2 * R) ^ 2 := by
              rw [norm_pow]
              exact add_le_add (hδCb ω) (pow_le_pow_left₀ (norm_nonneg _) (hxCb ω) 2)
        have : ‖(2 : ℂ)‖ = 2 := by simp
        rw [this]
        exact div_le_div_of_nonneg_right h1 (by norm_num))
  have hz1 : ∫ ω, G ω * (Complex.I * (x ω : ℂ)) ∂P = 0 := by
    have := hD.integral_cmul_incr u v huv (g := fun ω => G ω * Complex.I) (hGm.mul stronglyMeasurable_const)
      (C := B * 1) (fun ω => by rw [norm_mul, Complex.norm_I]; exact mul_le_mul (hGC ω) le_rfl zero_le_one hB0)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hx]; ring
  have hz2 : ∫ ω, G ω * (((δ ω : ℂ) - (x ω : ℂ) ^ 2) / 2) ∂P = 0 := by
    have := hD.integral_cmul_sq_incr u v huv (g := fun ω => G ω * (-(1 / 2 : ℂ)))
      (hGm.mul stronglyMeasurable_const) (C := B * 1) (fun ω => by
        rw [norm_mul]
        refine mul_le_mul (hGC ω) ?_ (norm_nonneg _) hB0
        norm_num)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hx, hδdef]; push_cast; ring
  have hsplit : ∫ ω, g ω * (expMart N A v ω - expMart N A u ω) ∂P =
      ∫ ω, G ω * ε ω ∂P := by
    have e : ∀ ω, g ω * (expMart N A v ω - expMart N A u ω) =
        G ω * ε ω + G ω * (Complex.I * (x ω : ℂ)) + G ω * (((δ ω : ℂ) - (x ω : ℂ) ^ 2) / 2) :=
      fun ω => by
        rw [hD.expMart_step u v ω]
        simp only [hG, hε, hE]
        ring
    simp_rw [e]
    have j1 : Integrable (fun ω => G ω * ε ω + G ω * (Complex.I * (x ω : ℂ))) P := iA.add iB
    rw [integral_add j1 iC, integral_add iA iB, hz1, hz2]
    simp
  rw [hsplit]
  calc ‖∫ ω, G ω * ε ω ∂P‖ ≤ ∫ ω, B * K * bd ω ∂P := by
        refine norm_integral_le_of_norm_le (hbdi.const_mul (B * K)) (Eventually.of_forall fun ω => ?_)
        rw [norm_mul]
        calc ‖G ω‖ * ‖ε ω‖ ≤ B * (K * bd ω) := mul_le_mul (hGC ω) (hεb ω) (norm_nonneg _) hB0
          _ = B * K * bd ω := by ring
    _ = C * Real.exp (a * T / 2) * (4 * Real.exp (2 * R + 1) + 1) *
        ∫ ω, (|N v ω - N u ω| ^ 3 + |N v ω - N u ω| * (A v ω - A u ω) +
          (A v ω - A u ω) ^ 2) ∂P := by
        rw [integral_const_mul]


theorem abs_incr_le (u v : ℝ) (ω : Ω) : |N v ω - N u ω| ≤ 2 * R := by
  calc |N v ω - N u ω| ≤ |N v ω| + |N u ω| := abs_sub _ _
    _ ≤ 2 * R := by linarith [hD.bdd v ω, hD.bdd u ω]

theorem integral_mul_sq_incr_le (u v : ℝ) (huv : u ≤ v) {g : Ω → ℝ}
    (hg : StronglyMeasurable[ℱ u] g) {C : ℝ} (hgC : ∀ ω, |g ω| ≤ C) (hg0 : ∀ ω, 0 ≤ g ω) :
    ∫ ω, g ω * (N v ω - N u ω) ^ 2 ∂P ≤ a * (v - u) * ∫ ω, g ω ∂P := by
  have hgm : Measurable g := (hg.mono (ℱ.le u)).measurable
  have h0 := hD.integral_real_sq_incr u v huv hg hgC
  have i1 : Integrable (fun ω => g ω * (N v ω - N u ω) ^ 2) P :=
    measurable_bdd_integrable (hgm.mul (((hD.measurable_N v).sub (hD.measurable_N u)).pow_const 2))
      (C * (2 * R) ^ 2) (fun ω => by
        rw [abs_mul, abs_pow]
        exact mul_le_mul (hgC ω) (pow_le_pow_left₀ (abs_nonneg _) (hD.abs_incr_le u v ω) 2)
          (by positivity) ((abs_nonneg _).trans (hgC ω)))
  have i2 : Integrable (fun ω => g ω * (A v ω - A u ω)) P :=
    measurable_bdd_integrable (hgm.mul ((hD.measurable_A v).sub (hD.measurable_A u)))
      (C * (a * max v 0)) (fun ω => by
        rw [abs_mul]
        have h1 := hD.nonnegA u ω
        have h2 := hD.boundA v ω
        have h3 := hD.monoA ω u v huv
        rw [abs_of_nonneg (sub_nonneg.2 h3)]
        exact mul_le_mul (hgC ω) (by linarith) (sub_nonneg.2 h3) ((abs_nonneg _).trans (hgC ω)))
  have e : ∫ ω, g ω * (N v ω - N u ω) ^ 2 ∂P = ∫ ω, g ω * (A v ω - A u ω) ∂P := by
    have := h0
    have e0 : ∀ ω, g ω * ((N v ω - N u ω) ^ 2 - (A v ω - A u ω)) =
        g ω * (N v ω - N u ω) ^ 2 - g ω * (A v ω - A u ω) := fun ω => by ring
    simp_rw [e0] at this
    rw [integral_sub i1 i2] at this
    linarith
  rw [e, ← integral_const_mul]
  refine integral_mono i2 ((measurable_bdd_integrable hgm C hgC).const_mul _) (fun ω => ?_)
  have := hD.lipA ω u v huv
  have h4 := hg0 ω
  show g ω * (A v ω - A u ω) ≤ a * (v - u) * g ω
  nlinarith


/-- Sum of squared increments along the grid `s + j h`. -/
def sqSum (N : ℝ → Ω → ℝ) (s h : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range k, (N (s + ((j + 1 : ℕ) : ℝ) * h) ω - N (s + (j : ℝ) * h) ω) ^ 2

theorem sqSum_succ (s h : ℝ) (k : ℕ) (ω : Ω) :
    sqSum N s h (k + 1) ω = sqSum N s h k ω +
      (N (s + ((k + 1 : ℕ) : ℝ) * h) ω - N (s + (k : ℝ) * h) ω) ^ 2 := by
  unfold sqSum; rw [Finset.sum_range_succ]

theorem measurable_sqSum (s h : ℝ) (k : ℕ) : Measurable (sqSum N s h k) := by
  unfold sqSum
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((hD.measurable_N _).sub (hD.measurable_N _)).pow_const 2

theorem stronglyMeasurable_sqSum {s h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    StronglyMeasurable[ℱ (s + (k : ℝ) * h)] (sqSum N s h k) := by
  unfold sqSum
  refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
  have hjk : j < k := Finset.mem_range.1 hj
  have h1 : s + (j : ℝ) * h ≤ s + (k : ℝ) * h := by
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk.le
    nlinarith
  have h2 : s + ((j + 1 : ℕ) : ℝ) * h ≤ s + (k : ℝ) * h := by
    have : ((j + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hjk
    nlinarith
  exact (((hD.mart.1 _).mono (ℱ.mono h2)).sub ((hD.mart.1 _).mono (ℱ.mono h1))).pow 2

theorem sqSum_nonneg (s h : ℝ) (k : ℕ) (ω : Ω) : 0 ≤ sqSum N s h k ω :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

theorem sqSum_le (s h : ℝ) (k : ℕ) (ω : Ω) : sqSum N s h k ω ≤ k * (2 * R) ^ 2 := by
  unfold sqSum
  calc _ ≤ ∑ j ∈ Finset.range k, (2 * R) ^ 2 := Finset.sum_le_sum fun j _ => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hD.abs_incr_le _ _ ω) 2
    _ = _ := by simp

theorem sqSum_moment {s h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    ∫ ω, sqSum N s h k ω ∂P ≤ a * h * k ∧
      ∫ ω, sqSum N s h k ω ^ 2 ∂P ≤ (a * h * k) ^ 2 + 4 * R ^ 2 * (a * h * k) := by
  have hR := hD.hR
  have ha := hD.ha
  induction k with
  | zero => simp [sqSum]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set u : ℝ := s + (k : ℝ) * h with hu
    set v : ℝ := s + ((k + 1 : ℕ) : ℝ) * h with hv
    have huv : u ≤ v := by
      simp only [hu, hv]; push_cast; nlinarith
    have hvu : v - u = h := by simp only [hu, hv]; push_cast; ring
    set x : Ω → ℝ := fun ω => N v ω - N u ω with hx
    have hxm : Measurable x := (hD.measurable_N v).sub (hD.measurable_N u)
    have hxb : ∀ ω, |x ω| ≤ 2 * R := fun ω => hD.abs_incr_le u v ω
    have hx2 : Integrable (fun ω => x ω ^ 2) P :=
      measurable_bdd_integrable (hxm.pow_const 2) ((2 * R) ^ 2) (fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hxb ω) 2)
    have hT : Integrable (sqSum N s h k) P :=
      measurable_bdd_integrable (hD.measurable_sqSum s h k) (k * (2 * R) ^ 2) (fun ω => by
        rw [abs_of_nonneg (hD.sqSum_nonneg s h k ω)]; exact hD.sqSum_le s h k ω)
    have hT2 : Integrable (fun ω => sqSum N s h k ω ^ 2) P :=
      measurable_bdd_integrable ((hD.measurable_sqSum s h k).pow_const 2) ((k * (2 * R) ^ 2) ^ 2)
        (fun ω => by
          rw [abs_pow, abs_of_nonneg (hD.sqSum_nonneg s h k ω)]
          exact pow_le_pow_left₀ (hD.sqSum_nonneg s h k ω) (hD.sqSum_le s h k ω) 2)
    -- ∫ x² ≤ a h
    have hx2le : ∫ ω, x ω ^ 2 ∂P ≤ a * h := by
      have := hD.integral_mul_sq_incr_le u v huv (g := fun _ => 1)
        (stronglyMeasurable_const) (C := 1) (fun ω => by simp) (fun ω => zero_le_one)
      simpa [hvu, hx] using this
    -- ∫ T x² ≤ a h ∫ T
    have hTx : ∫ ω, sqSum N s h k ω * x ω ^ 2 ∂P ≤ a * h * (a * h * k) := by
      have := hD.integral_mul_sq_incr_le u v huv (g := sqSum N s h k)
        (hD.stronglyMeasurable_sqSum hh k) (C := k * (2 * R) ^ 2) (fun ω => by
          rw [abs_of_nonneg (hD.sqSum_nonneg s h k ω)]; exact hD.sqSum_le s h k ω)
        (hD.sqSum_nonneg s h k)
      rw [hvu] at this
      calc _ ≤ a * h * ∫ ω, sqSum N s h k ω ∂P := this
        _ ≤ a * h * (a * h * k) := mul_le_mul_of_nonneg_left ih1 (mul_nonneg ha hh)
    -- ∫ x⁴ ≤ 4R² a h
    have hx4 : ∫ ω, x ω ^ 2 * x ω ^ 2 ∂P ≤ 4 * R ^ 2 * (a * h) := by
      calc ∫ ω, x ω ^ 2 * x ω ^ 2 ∂P ≤ ∫ ω, (2 * R) ^ 2 * x ω ^ 2 ∂P := by
            refine integral_mono ?_ (hx2.const_mul _) (fun ω => ?_)
            · exact measurable_bdd_integrable ((hxm.pow_const 2).mul (hxm.pow_const 2))
                ((2 * R) ^ 2 * (2 * R) ^ 2) (fun ω => by
                  rw [abs_mul, abs_pow]
                  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hxb ω) 2)
                    (pow_le_pow_left₀ (abs_nonneg _) (hxb ω) 2) (by positivity) (by positivity))
            · show x ω ^ 2 * x ω ^ 2 ≤ (2 * R) ^ 2 * x ω ^ 2
              have : x ω ^ 2 ≤ (2 * R) ^ 2 := by
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hxb ω) 2
              nlinarith [sq_nonneg (x ω)]
        _ = (2 * R) ^ 2 * ∫ ω, x ω ^ 2 ∂P := integral_const_mul _ _
        _ ≤ (2 * R) ^ 2 * (a * h) := mul_le_mul_of_nonneg_left hx2le (by positivity)
        _ = _ := by ring
    have e1 : ∀ ω, sqSum N s h (k + 1) ω = sqSum N s h k ω + x ω ^ 2 := fun ω =>
      hD.sqSum_succ s h k ω
    constructor
    · simp_rw [e1]
      rw [integral_add hT hx2]
      push_cast
      nlinarith
    · simp_rw [e1]
      have e2 : ∀ ω, (sqSum N s h k ω + x ω ^ 2) ^ 2 =
          sqSum N s h k ω ^ 2 + 2 * (sqSum N s h k ω * x ω ^ 2) + x ω ^ 2 * x ω ^ 2 := fun ω => by ring
      simp_rw [e2]
      have iTx : Integrable (fun ω => sqSum N s h k ω * x ω ^ 2) P :=
        measurable_bdd_integrable ((hD.measurable_sqSum s h k).mul (hxm.pow_const 2))
          ((k * (2 * R) ^ 2) * (2 * R) ^ 2) (fun ω => by
            rw [abs_mul, abs_of_nonneg (hD.sqSum_nonneg s h k ω), abs_pow]
            exact mul_le_mul (hD.sqSum_le s h k ω) (pow_le_pow_left₀ (abs_nonneg _) (hxb ω) 2)
              (by positivity) (by positivity))
      have ix4 : Integrable (fun ω => x ω ^ 2 * x ω ^ 2) P :=
        measurable_bdd_integrable ((hxm.pow_const 2).mul (hxm.pow_const 2))
          ((2 * R) ^ 2 * (2 * R) ^ 2) (fun ω => by
            rw [abs_mul, abs_pow]
            exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hxb ω) 2)
              (pow_le_pow_left₀ (abs_nonneg _) (hxb ω) 2) (by positivity) (by positivity))
      have j1 : Integrable (fun ω => sqSum N s h k ω ^ 2 + 2 * (sqSum N s h k ω * x ω ^ 2)) P :=
        hT2.add (iTx.const_mul 2)
      rw [integral_add j1 ix4, integral_add hT2 (iTx.const_mul 2), integral_const_mul]
      push_cast
      nlinarith [mul_nonneg ha hh, mul_nonneg (mul_nonneg ha hh) (Nat.cast_nonneg k : (0:ℝ) ≤ k),
        sq_nonneg R]


/-- Increments of `N` along the grid with `n` steps on `[s, t]`. -/
def gridIncr (N : ℝ → Ω → ℝ) (s t : ℝ) (n : ℕ) (j : ℕ) (ω : Ω) : ℝ :=
  N (s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n)) ω - N (s + (j : ℝ) * ((t - s) / n)) ω

theorem tendsto_runMax_gridIncr {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
    Tendsto (fun n : ℕ => runMax (gridIncr N s t n) n ω) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc : ContinuousOn (fun u => N u ω) (Set.Icc s t) := (hD.cont ω).continuousOn
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hc
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hηc⟩ := huc (ε / 2) (by positivity)
  obtain ⟨n0, hn0⟩ := exists_nat_gt ((t - s) / η)
  refine ⟨n0 + 1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hh : (t - s) / n < η := by
    rw [div_lt_iff₀ hnpos]
    have : (t - s) / η < n := lt_of_lt_of_le hn0 (by exact_mod_cast (by omega : n0 ≤ n))
    rw [div_lt_iff₀ hη] at this
    linarith
  have hh0 : 0 ≤ (t - s) / n := div_nonneg (sub_nonneg.2 hst) hnpos.le
  have hbound : runMax (gridIncr N s t n) n ω ≤ ε / 2 := by
    refine runMax_le_of _ n ω (fun j hj => ?_) (by positivity)
    have hj1 : ((j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hnh : (n : ℝ) * ((t - s) / n) = t - s := by field_simp
    have hm1 : s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n) ∈ Set.Icc s t := by
      constructor
      · nlinarith [mul_nonneg (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ)) hh0]
      · nlinarith [mul_le_mul_of_nonneg_right hj1 hh0]
    have hm0 : s + (j : ℝ) * ((t - s) / n) ∈ Set.Icc s t := by
      constructor
      · nlinarith [mul_nonneg hj0 hh0]
      · have : (j : ℝ) ≤ n := by exact_mod_cast hj.le
        nlinarith [mul_le_mul_of_nonneg_right this hh0]
    have hd : dist (s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n)) (s + (j : ℝ) * ((t - s) / n)) < η := by
      rw [Real.dist_eq]
      have : s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n) - (s + (j : ℝ) * ((t - s) / n)) = (t - s) / n := by
        push_cast; ring
      rw [this, abs_of_nonneg hh0]; exact hh
    have := hηc _ hm1 _ hm0 hd
    rw [Real.dist_eq] at this
    exact this.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (runMax_nonneg _ _ _)]
  linarith [hε]


theorem telescoping_bound {s t : ℝ} (hst : s ≤ t) (n : ℕ) (hn : 0 < n)
    (hah : a * ((t - s) / n) ≤ 1) {g : Ω → ℂ} (hg : StronglyMeasurable[ℱ s] g) {C : ℝ}
    (hgC : ∀ ω, ‖g ω‖ ≤ C) :
    ‖∫ ω, g ω * (expMart N A t ω - expMart N A s ω) ∂P‖ ≤
      C * Real.exp (a * max t 0 / 2) * (4 * Real.exp (2 * R + 1) + 1) *
        ∑ j ∈ Finset.range n, ∫ ω, (|gridIncr N s t n j ω| ^ 3 + |gridIncr N s t n j ω| *
          (A (s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n)) ω - A (s + (j : ℝ) * ((t - s) / n)) ω) +
          (A (s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n)) ω - A (s + (j : ℝ) * ((t - s) / n)) ω) ^ 2) ∂P := by
  have hC : 0 ≤ C := by
    have : Nonempty Ω := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hgC (Classical.arbitrary Ω))
  set h : ℝ := (t - s) / n with hh
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.2 hst) hnpos.le
  set r : ℕ → ℝ := fun j => s + (j : ℝ) * h with hr
  have hr0 : r 0 = s := by simp [hr]
  have hrn : r n = t := by simp only [hr, hh]; field_simp; ring
  have hrle : ∀ j, j ≤ n → r j ≤ t := fun j hj => by
    rw [← hrn]; simp only [hr]
    have : (j : ℝ) ≤ n := by exact_mod_cast hj
    nlinarith
  have hrs : ∀ j, s ≤ r j := fun j => by
    simp only [hr]; nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hh0]
  have hrsucc : ∀ j, r (j + 1) = s + ((j + 1 : ℕ) : ℝ) * h := fun j => rfl
  have hmono : ∀ j, r j ≤ r (j + 1) := fun j => by
    simp only [hr]; push_cast; nlinarith
  have hT : ∀ j, j ≤ n → max (r j) 0 ≤ max t 0 := fun j hj => max_le_max (hrle j hj) le_rfl
  set Z : ℝ → Ω → ℂ := expMart N A with hZ
  have hZb : ∀ j, j ≤ n → ∀ ω, ‖Z (r j) ω‖ ≤ Real.exp (a * max t 0 / 2) := fun j hj ω =>
    hD.norm_expMart_le (hT j hj) ω
  have hint : ∀ j, j < n → Integrable (fun ω => g ω * (Z (r (j + 1)) ω - Z (r j) ω)) P := by
    intro j hj
    have hgm : Measurable g := (hg.mono (ℱ.le s)).measurable
    refine Integrable.of_bound ((hgm.mul ((hD.measurable_expMart _).sub
      (hD.measurable_expMart _))).aestronglyMeasurable) (C * (Real.exp (a * max t 0 / 2) +
        Real.exp (a * max t 0 / 2))) (Eventually.of_forall fun ω => ?_)
    rw [norm_mul]
    exact mul_le_mul (hgC ω) ((norm_sub_le _ _).trans (add_le_add (hZb (j + 1) hj ω)
      (hZb j hj.le ω))) (norm_nonneg _) hC
  have hsum : ∫ ω, g ω * (Z t ω - Z s ω) ∂P =
      ∑ j ∈ Finset.range n, ∫ ω, g ω * (Z (r (j + 1)) ω - Z (r j) ω) ∂P := by
    rw [← integral_finset_sum _ (fun j hj => hint j (Finset.mem_range.1 hj))]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show g ω * (Z t ω - Z s ω) = ∑ i ∈ Finset.range n, g ω * (Z (r (i + 1)) ω - Z (r i) ω)
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun j => Z (r j) ω) n, hrn, hr0]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjn : j < n := Finset.mem_range.1 hj
  have := hD.step_bound (r j) (r (j + 1)) (max t 0) (hmono j) (hT j hjn.le)
    (by have : r (j + 1) - r j = h := by simp only [hr]; push_cast; ring
        rw [this]; exact hah) (g := g) (hg.mono (ℱ.mono (hrs j))) hgC
  exact this


theorem sum_bd_le {s t : ℝ} (hst : s ≤ t) (n : ℕ) (hn : 0 < n)
    (hah : a * ((t - s) / n) ≤ 1) :
    ∑ j ∈ Finset.range n, ∫ ω, (|gridIncr N s t n j ω| ^ 3 + |gridIncr N s t n j ω| *
          (A (s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n)) ω - A (s + (j : ℝ) * ((t - s) / n)) ω) +
          (A (s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n)) ω - A (s + (j : ℝ) * ((t - s) / n)) ω) ^ 2) ∂P ≤
      ∫ ω, runMax (gridIncr N s t n) n ω * sqSum N s ((t - s) / n) n ω ∂P +
        a * (t - s) * ∫ ω, runMax (gridIncr N s t n) n ω ∂P + a * ((t - s) / n) * (a * (t - s)) := by
  have hR := hD.hR
  have ha := hD.ha
  set h : ℝ := (t - s) / n with hh
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.2 hst) hnpos.le
  have hrn : s + (n : ℝ) * h = t := by simp only [hh]; field_simp; ring
  set M : Ω → ℝ := runMax (gridIncr N s t n) n with hM
  set δ : ℕ → Ω → ℝ := fun j ω => A (s + ((j + 1 : ℕ) : ℝ) * h) ω - A (s + (j : ℝ) * h) ω with hδ
  have hxm : ∀ j, Measurable (gridIncr N s t n j) := fun j =>
    (hD.measurable_N _).sub (hD.measurable_N _)
  have hδm : ∀ j, Measurable (δ j) := fun j => (hD.measurable_A _).sub (hD.measurable_A _)
  have hmono : ∀ j ω, 0 ≤ δ j ω := fun j ω => sub_nonneg.2 (hD.monoA ω _ _ (by
    push_cast; nlinarith))
  have hlip : ∀ j ω, δ j ω ≤ a * h := fun j ω => by
    have := hD.lipA ω (s + (j : ℝ) * h) (s + ((j + 1 : ℕ) : ℝ) * h) (by push_cast; nlinarith)
    have e : s + ((j + 1 : ℕ) : ℝ) * h - (s + (j : ℝ) * h) = h := by push_cast; ring
    rw [e] at this; exact this
  have hxb : ∀ j ω, |gridIncr N s t n j ω| ≤ 2 * R := fun j ω => hD.abs_incr_le _ _ ω
  have hMm : Measurable M := measurable_runMax hxm n
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => runMax_nonneg _ _ ω
  have hMb : ∀ ω, M ω ≤ 2 * R := fun ω => runMax_le _ (by positivity) hxb n ω
  have hδsum : ∀ ω, ∑ j ∈ Finset.range n, δ j ω = A t ω - A s ω := fun ω => by
    have := Finset.sum_range_sub (fun j => A (s + (j : ℝ) * h) ω) n
    rw [hrn] at this
    simpa [hδ] using this
  have hδsum_le : ∀ ω, ∑ j ∈ Finset.range n, δ j ω ≤ a * (t - s) := fun ω => by
    rw [hδsum]; exact hD.lipA ω s t hst
  -- the pointwise bound
  have hpt : ∀ ω, ∑ j ∈ Finset.range n, (|gridIncr N s t n j ω| ^ 3 + |gridIncr N s t n j ω| * δ j ω +
      δ j ω ^ 2) ≤ M ω * sqSum N s h n ω + a * (t - s) * M ω + a * h * (a * (t - s)) := by
    intro ω
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 : ∑ j ∈ Finset.range n, |gridIncr N s t n j ω| ^ 3 ≤ M ω * sqSum N s h n ω := by
      unfold sqSum
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have := abs_le_runMax (gridIncr N s t n) (Finset.mem_range.1 hj) ω
      have e : (N (s + ((j + 1 : ℕ) : ℝ) * h) ω - N (s + (j : ℝ) * h) ω) ^ 2 =
          |gridIncr N s t n j ω| ^ 2 := by rw [sq_abs]; rfl
      rw [e]
      calc |gridIncr N s t n j ω| ^ 3 = |gridIncr N s t n j ω| * |gridIncr N s t n j ω| ^ 2 := by ring
        _ ≤ M ω * |gridIncr N s t n j ω| ^ 2 :=
            mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have h2 : ∑ j ∈ Finset.range n, |gridIncr N s t n j ω| * δ j ω ≤ a * (t - s) * M ω := by
      calc _ ≤ ∑ j ∈ Finset.range n, M ω * δ j ω := Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_right (abs_le_runMax (gridIncr N s t n) (Finset.mem_range.1 hj) ω)
              (hmono j ω)
        _ = M ω * ∑ j ∈ Finset.range n, δ j ω := (Finset.mul_sum _ _ _).symm
        _ ≤ M ω * (a * (t - s)) := mul_le_mul_of_nonneg_left (hδsum_le ω) (hM0 ω)
        _ = _ := by ring
    have h3 : ∑ j ∈ Finset.range n, δ j ω ^ 2 ≤ a * h * (a * (t - s)) := by
      calc _ ≤ ∑ j ∈ Finset.range n, (a * h) * δ j ω := Finset.sum_le_sum fun j hj => by
            rw [sq]; exact mul_le_mul_of_nonneg_right (hlip j ω) (hmono j ω)
        _ = (a * h) * ∑ j ∈ Finset.range n, δ j ω := (Finset.mul_sum _ _ _).symm
        _ ≤ (a * h) * (a * (t - s)) :=
            mul_le_mul_of_nonneg_left (hδsum_le ω) (mul_nonneg ha hh0)
    linarith
  -- integrability
  have hbd : ∀ j ∈ Finset.range n, Integrable (fun ω => |gridIncr N s t n j ω| ^ 3 +
      |gridIncr N s t n j ω| * δ j ω + δ j ω ^ 2) P := by
    intro j _
    refine measurable_bdd_integrable (by have := hxm j; have := hδm j; fun_prop)
      ((2 * R) ^ 3 + 2 * R * 1 + 1 ^ 2) (fun ω => ?_)
    have h1 := hxb j ω
    have h2 := hmono j ω
    have h3 : δ j ω ≤ 1 := (hlip j ω).trans hah
    have h4 : |gridIncr N s t n j ω| ^ 3 ≤ (2 * R) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
    have h5 : |gridIncr N s t n j ω| * δ j ω ≤ 2 * R * 1 :=
      mul_le_mul h1 h3 h2 (by positivity)
    have h6 : δ j ω ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h2 h3 2
    have : 0 ≤ |gridIncr N s t n j ω| ^ 3 + |gridIncr N s t n j ω| * δ j ω + δ j ω ^ 2 := by positivity
    rw [abs_of_nonneg this]; linarith
  have hSm : Measurable (sqSum N s h n) := hD.measurable_sqSum s h n
  have hSb : ∀ ω, sqSum N s h n ω ≤ n * (2 * R) ^ 2 := hD.sqSum_le s h n
  have hS0 : ∀ ω, 0 ≤ sqSum N s h n ω := hD.sqSum_nonneg s h n
  have iMS : Integrable (fun ω => M ω * sqSum N s h n ω) P :=
    measurable_bdd_integrable (hMm.mul hSm) ((2 * R) * (n * (2 * R) ^ 2)) (fun ω => by
      rw [abs_of_nonneg (mul_nonneg (hM0 ω) (hS0 ω))]
      exact mul_le_mul (hMb ω) (hSb ω) (hS0 ω) (by positivity))
  have iM : Integrable M P := measurable_bdd_integrable hMm (2 * R) (fun ω => by
    rw [abs_of_nonneg (hM0 ω)]; exact hMb ω)
  rw [← integral_finset_sum _ hbd]
  calc ∫ ω, ∑ j ∈ Finset.range n, (|gridIncr N s t n j ω| ^ 3 + |gridIncr N s t n j ω| * δ j ω +
        δ j ω ^ 2) ∂P ≤ ∫ ω, (M ω * sqSum N s h n ω + a * (t - s) * M ω + a * h * (a * (t - s))) ∂P :=
        integral_mono (integrable_finset_sum _ hbd)
          (((iMS.add (iM.const_mul _)).add (integrable_const _)) : Integrable (fun ω =>
            M ω * sqSum N s h n ω + a * (t - s) * M ω + a * h * (a * (t - s))) P) hpt
    _ = _ := by
        have j1 : Integrable (fun ω => M ω * sqSum N s h n ω + a * (t - s) * M ω) P :=
          iMS.add (iM.const_mul _)
        rw [integral_add j1 (integrable_const _), integral_add iMS (iM.const_mul _),
          integral_const_mul]
        simp


theorem tendsto_integral_runMax {s t : ℝ} (hst : s ≤ t) :
    Tendsto (fun n : ℕ => ∫ ω, runMax (gridIncr N s t n) n ω ∂P) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ ω, runMax (gridIncr N s t n) n ω ^ 2 ∂P) atTop (𝓝 0) := by
  have hR := hD.hR
  have hxm : ∀ n j, Measurable (gridIncr N s t n j) := fun n j =>
    (hD.measurable_N _).sub (hD.measurable_N _)
  have hMm : ∀ n, Measurable (runMax (gridIncr N s t n) n) := fun n => measurable_runMax (hxm n) n
  have hxb : ∀ n j ω, |gridIncr N s t n j ω| ≤ 2 * R := fun n j ω => hD.abs_incr_le _ _ ω
  have hMb : ∀ n ω, runMax (gridIncr N s t n) n ω ≤ 2 * R := fun n ω =>
    runMax_le _ (by positivity) (hxb n) n ω
  have hlim : ∀ ω, Tendsto (fun n : ℕ => runMax (gridIncr N s t n) n ω) atTop (𝓝 0) :=
    fun ω => hD.tendsto_runMax_gridIncr hst ω
  constructor
  · have := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun n ω => runMax (gridIncr N s t n) n ω) (f := fun _ => (0 : ℝ))
      (fun _ => 2 * R) (fun n => (hMm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (runMax_nonneg _ _ _)]; exact hMb n ω)
      (Eventually.of_forall hlim)
    simpa using this
  · have := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun n ω => runMax (gridIncr N s t n) n ω ^ 2) (f := fun _ => (0 : ℝ))
      (fun _ => (2 * R) ^ 2) (fun n => ((hMm n).pow_const 2).aestronglyMeasurable)
      (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (runMax_nonneg _ _ _) (hMb n ω) 2)
      (Eventually.of_forall fun ω => by
        simpa using (hlim ω).pow 2)
    simpa using this

/-- **Exponential martingale for a bounded continuous martingale with Lipschitz clock.** -/
theorem exp_martingale_bounded {s t : ℝ} (hst : s ≤ t) {g : Ω → ℂ}
    (hg : StronglyMeasurable[ℱ s] g) {C : ℝ} (hgC : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, g ω * (expMart N A t ω - expMart N A s ω) ∂P = 0 := by
  have hR := hD.hR
  have ha := hD.ha
  have hC : 0 ≤ C := by
    have : Nonempty Ω := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hgC (Classical.arbitrary Ω))
  set L : ℝ := t - s with hL
  have hL0 : 0 ≤ L := sub_nonneg.2 hst
  set c1 : ℝ := C * Real.exp (a * max t 0 / 2) * (4 * Real.exp (2 * R + 1) + 1) with hc1
  have hc10 : 0 ≤ c1 := by positivity
  set Cb : ℝ := (a * L) ^ 2 + 4 * R ^ 2 * (a * L) with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set Q : ℝ := ‖∫ ω, g ω * (expMart N A t ω - expMart N A s ω) ∂P‖ with hQ
  obtain ⟨hI1, hI2⟩ := hD.tendsto_integral_runMax hst
  have key : ∀ η : ℝ, 0 < η → Q ≤ c1 * (η * Cb / 2) := by
    intro η hη
    set e : ℕ → ℝ := fun n => (∫ ω, runMax (gridIncr N s t n) n ω ^ 2 ∂P) / (2 * η) +
      a * L * ∫ ω, runMax (gridIncr N s t n) n ω ∂P + a * (L / n) * (a * L) with he
    have hlim : Tendsto (fun n : ℕ => c1 * (η * Cb / 2 + e n)) atTop (𝓝 (c1 * (η * Cb / 2 + 0))) := by
      have h1 : Tendsto (fun n : ℕ => (∫ ω, runMax (gridIncr N s t n) n ω ^ 2 ∂P) / (2 * η))
          atTop (𝓝 (0 / (2 * η))) := hI2.div_const _
      have h2 : Tendsto (fun n : ℕ => a * L * ∫ ω, runMax (gridIncr N s t n) n ω ∂P) atTop
          (𝓝 (a * L * 0)) := hI1.const_mul _
      have h3 : Tendsto (fun n : ℕ => a * (L / n) * (a * L)) atTop (𝓝 (a * 0 * (a * L))) := by
        have : Tendsto (fun n : ℕ => L / (n : ℝ)) atTop (𝓝 0) :=
          tendsto_const_div_atTop_nhds_zero_nat L
        exact (this.const_mul a).mul_const _
      have h4 := (h1.add h2).add h3
      simp only [zero_div, mul_zero, zero_mul, add_zero] at h4
      exact (tendsto_const_nhds.add h4).const_mul c1 |>.congr (fun n => rfl)
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ a * L ≤ n := by
      filter_upwards [eventually_ge_atTop 1, tendsto_natCast_atTop_atTop.eventually_ge_atTop (a * L)]
        with n h1 h2 using ⟨h1, h2⟩
    filter_upwards [hev] with n ⟨hn1, hn2⟩
    have hn : 0 < n := hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hah : a * ((t - s) / n) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hnpos]; exact hn2
    have h1 := hD.telescoping_bound hst n hn hah hg hgC
    have h2 := hD.sum_bd_le hst n hn hah
    -- bound `∫ M S`
    set M : Ω → ℝ := runMax (gridIncr N s t n) n with hM
    set S : Ω → ℝ := sqSum N s ((t - s) / n) n with hS
    have hh0 : 0 ≤ (t - s) / n := div_nonneg hL0 hnpos.le
    have hmom := (hD.sqSum_moment (s := s) hh0 n).2
    have hhn : a * ((t - s) / n) * n = a * L := by rw [hL]; field_simp
    rw [hhn] at hmom
    have hxm : ∀ j, Measurable (gridIncr N s t n j) := fun j =>
      (hD.measurable_N _).sub (hD.measurable_N _)
    have hMm : Measurable M := measurable_runMax hxm n
    have hM0 : ∀ ω, 0 ≤ M ω := fun ω => runMax_nonneg _ _ ω
    have hMb : ∀ ω, M ω ≤ 2 * R := fun ω => runMax_le _ (by positivity)
      (fun j ω => hD.abs_incr_le _ _ ω) n ω
    have hSm : Measurable S := hD.measurable_sqSum s _ n
    have hSb : ∀ ω, S ω ≤ n * (2 * R) ^ 2 := hD.sqSum_le s _ n
    have hS0 : ∀ ω, 0 ≤ S ω := hD.sqSum_nonneg s _ n
    have iM2 : Integrable (fun ω => M ω ^ 2) P :=
      measurable_bdd_integrable (hMm.pow_const 2) ((2 * R) ^ 2) (fun ω => by
        rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (hM0 ω) (hMb ω) 2)
    have iS2 : Integrable (fun ω => S ω ^ 2) P :=
      measurable_bdd_integrable (hSm.pow_const 2) ((n * (2 * R) ^ 2) ^ 2) (fun ω => by
        rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (hS0 ω) (hSb ω) 2)
    have iMS : Integrable (fun ω => M ω * S ω) P :=
      measurable_bdd_integrable (hMm.mul hSm) ((2 * R) * (n * (2 * R) ^ 2)) (fun ω => by
        rw [abs_of_nonneg (mul_nonneg (hM0 ω) (hS0 ω))]
        exact mul_le_mul (hMb ω) (hSb ω) (hS0 ω) (by positivity))
    have hamgm : ∫ ω, M ω * S ω ∂P ≤ η * Cb / 2 + (∫ ω, M ω ^ 2 ∂P) / (2 * η) := by
      have hpt : ∀ ω, M ω * S ω ≤ (η / 2) * S ω ^ 2 + (1 / (2 * η)) * M ω ^ 2 := fun ω => by
        have : 0 ≤ (η * S ω - M ω) ^ 2 := sq_nonneg _
        have h2η : 0 < 2 * η := by positivity
        rw [show (η / 2) * S ω ^ 2 + (1 / (2 * η)) * M ω ^ 2 =
          ((η * S ω - M ω) ^ 2 + 2 * η * (M ω * S ω)) / (2 * η) by field_simp; ring]
        rw [le_div_iff₀ h2η]; nlinarith
      calc ∫ ω, M ω * S ω ∂P ≤ ∫ ω, ((η / 2) * S ω ^ 2 + (1 / (2 * η)) * M ω ^ 2) ∂P :=
            integral_mono iMS ((iS2.const_mul _).add (iM2.const_mul _)) hpt
        _ = (η / 2) * ∫ ω, S ω ^ 2 ∂P + (1 / (2 * η)) * ∫ ω, M ω ^ 2 ∂P := by
            rw [integral_add (iS2.const_mul _) (iM2.const_mul _), integral_const_mul,
              integral_const_mul]
        _ ≤ (η / 2) * Cb + (1 / (2 * η)) * ∫ ω, M ω ^ 2 ∂P := by
            have : ∫ ω, S ω ^ 2 ∂P ≤ Cb := hmom
            nlinarith
        _ = _ := by ring
    have hsum : ∑ j ∈ Finset.range n, ∫ ω, (|gridIncr N s t n j ω| ^ 3 + |gridIncr N s t n j ω| *
          (A (s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n)) ω - A (s + (j : ℝ) * ((t - s) / n)) ω) +
          (A (s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n)) ω - A (s + (j : ℝ) * ((t - s) / n)) ω) ^ 2) ∂P
        ≤ η * Cb / 2 + e n := by
      refine h2.trans ?_
      simp only [he]
      have : (∫ ω, M ω ^ 2 ∂P) / (2 * η) = (∫ ω, M ω ^ 2 ∂P) / (2 * η) := rfl
      linarith
    calc Q ≤ c1 * ∑ j ∈ Finset.range n, ∫ ω, (|gridIncr N s t n j ω| ^ 3 +
          |gridIncr N s t n j ω| *
          (A (s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n)) ω - A (s + (j : ℝ) * ((t - s) / n)) ω) +
          (A (s + ((j + 1 : ℕ) : ℝ) * ((t - s) / n)) ω - A (s + (j : ℝ) * ((t - s) / n)) ω) ^ 2) ∂P :=
          h1
      _ ≤ c1 * (η * Cb / 2 + e n) := mul_le_mul_of_nonneg_left hsum hc10
  have hQ0 : Q ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hc : c1 * (Cb / 2) = 0
    · have := key 1 one_pos
      have : Q ≤ 0 := by simpa [mul_div_assoc, hc] using this
      linarith
    · have hpos : 0 < c1 * (Cb / 2) := lt_of_le_of_ne (by positivity) (Ne.symm hc)
      have := key (ε / (c1 * (Cb / 2))) (div_pos hε hpos)
      have hne : c1 * Cb ≠ 0 := fun h => hc (by rw [show c1 * (Cb / 2) = c1 * Cb / 2 by ring, h]; simp)
      have e : c1 * (ε / (c1 * (Cb / 2)) * Cb / 2) = ε := by
        field_simp
        exact div_self hne
      linarith
  have : ‖∫ ω, g ω * (expMart N A t ω - expMart N A s ω) ∂P‖ ≤ 0 := hQ0
  exact norm_le_zero_iff.1 this

end LevyData

end LevyTest


section LevyLocalize

theorem phi_cases (τ : WithTop ℝ) : (∀ t : ℝ, (min (t : WithTop ℝ) τ).untopA = t) ∨
    ∃ c : ℝ, ∀ t : ℝ, (min (t : WithTop ℝ) τ).untopA = min t c := by
  induction τ using WithTop.recTopCoe with
  | top => left; intro t; simp
  | coe c =>
    right; refine ⟨c, fun t => ?_⟩
    have : min (t : WithTop ℝ) (c : WithTop ℝ) = ((min t c : ℝ) : WithTop ℝ) :=
      (WithTop.coe_min t c).symm
    rw [this]; rfl

/-- The localising time: first time `|N| ≥ R`. -/
def locTimeAbs (N : ℝ → Ω → ℝ) (R : ℝ) : Ω → WithTop ℝ :=
  hittingAfter (fun t ω => |N t ω|) (Set.Ici R) 0

theorem abs_stoppedProcess_le {N : ℝ → Ω → ℝ} (hc : ∀ ω, Continuous fun t => N t ω)
    (hneg : ∀ t, t ≤ 0 → ∀ ω, N t ω = 0) {R : ℝ} (hR : 0 < R) (ω : Ω) (t : ℝ) :
    |stoppedProcess N (locTimeAbs N R) t ω| ≤ R := by
  have hcont : Continuous fun t => |N t ω| := (hc ω).abs
  have hσ' : ∀ k : ℝ, 0 ≤ k → (k : WithTop ℝ) < locTimeAbs N R ω → |N k ω| < R := by
    intro k hk hlt
    have := notMem_of_lt_hittingAfter (u := fun t ω => |N t ω|) (s := Set.Ici R) (n := 0) (ω := ω)
      hlt hk
    simpa using this
  rcases hσ : locTimeAbs N R ω with _ | c
  · rw [stoppedProcess_apply_top hσ t]
    rcases le_or_gt t 0 with ht | ht
    · rw [hneg t ht ω]; simp [hR.le]
    · have := hσ' t ht.le (by rw [hσ]; exact WithTop.coe_lt_top t)
      exact this.le
  · rw [stoppedProcess_apply_coe hσ t]
    have hmem := mem_of_hittingAfter_eq_of_isClosed (fun t ω => |N t ω|) ω hcont isClosed_Ici 0 c hσ
    have hc0 : 0 ≤ c := by
      have : (0 : WithTop ℝ) ≤ locTimeAbs N R ω := le_hittingAfter ω
      rw [hσ] at this; exact WithTop.coe_le_coe.1 this
    have hcne : c ≠ 0 := by
      rintro rfl
      have : R ≤ |N 0 ω| := hmem
      rw [hneg 0 le_rfl ω] at this
      simp at this; linarith
    have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne)
    have hclosed : IsClosed {u : ℝ | |N u ω| ≤ R} := isClosed_le hcont continuous_const
    have hsub : Set.Ico 0 c ⊆ {u : ℝ | |N u ω| ≤ R} := fun u hu =>
      (hσ' u hu.1 (by rw [hσ]; exact WithTop.coe_lt_coe.2 hu.2)).le
    have hcle : |N c ω| ≤ R := by
      have : c ∈ closure (Set.Ico 0 c) := by
        rw [closure_Ico hcpos.ne]; exact ⟨hc0, le_rfl⟩
      exact (closure_minimal hsub hclosed) this
    rcases le_or_gt (min t c) 0 with hu | hu
    · rw [hneg _ hu ω]; simp [hR.le]
    · rcases lt_or_eq_of_le (min_le_right t c) with h | h
      · exact (hσ' _ hu.le (by rw [hσ]; exact WithTop.coe_lt_coe.2 h)).le
      · rw [h]; exact hcle

theorem exists_clock (τ : WithTop ℝ) : ∃ φ : ℝ → ℝ, Continuous φ ∧ Monotone φ ∧
    (∀ u v, u ≤ v → φ v - φ u ≤ v - u) ∧ (∀ t, φ t ≤ t) ∧
    ∀ t : ℝ, (min (t : WithTop ℝ) τ).untopA = φ t := by
  rcases phi_cases τ with h | ⟨c, h⟩
  · exact ⟨id, continuous_id, monotone_id, fun u v _ => le_rfl, fun t => le_rfl, h⟩
  · refine ⟨fun t => min t c, continuous_id.min continuous_const, fun u v huv => min_le_min_right _ huv,
      fun u v huv => ?_, fun t => min_le_left _ _, h⟩
    show min v c - min u c ≤ v - u
    rcases le_total v c with h1 | h1
    · rw [min_eq_left h1, min_eq_left (huv.trans h1)]
    · rcases le_total u c with h2 | h2
      · rw [min_eq_right h1, min_eq_left h2]; linarith
      · rw [min_eq_right h1, min_eq_right h2]; linarith

theorem levyData_stopped {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {N : ℝ → Ω → ℝ} (hN : Martingale N ℱ P) (hc : ∀ ω, Continuous fun t => N t ω)
    (hneg : ∀ t, t ≤ 0 → ∀ ω, N t ω = 0) {a : ℝ} (ha : 0 ≤ a)
    (hQ : Martingale (fun t ω => N t ω ^ 2 - a * max t 0) ℱ P) {R : ℝ} (hR : 0 < R) :
    LevyData P ℱ (stoppedProcess N (locTimeAbs N R))
      (stoppedProcess (fun t (_ : Ω) => a * max t 0) (locTimeAbs N R)) R a := by
  have hσ : IsStoppingTime ℱ (locTimeAbs N R) :=
    isStoppingTime_hittingAfter_Ici ℱ (fun t ω => |N t ω|)
      (fun t => continuous_abs.measurable.comp (hN.1 t).measurable) (fun ω => (hc ω).abs) R
  have hAad : StronglyAdapted ℱ (fun t (_ : Ω) => a * max t 0) := fun t => by
    show StronglyMeasurable[ℱ t] fun _ : Ω => a * max t 0
    exact stronglyMeasurable_const
  have hAc : ∀ ω : Ω, Continuous fun t : ℝ => a * max t 0 := fun ω =>
    continuous_const.mul (continuous_id.max continuous_const)
  have hclock := fun ω => exists_clock (locTimeAbs N R ω)
  refine ⟨ha, hR.le, Martingale.stoppedProcess_of_continuous P ℱ N hN hc hσ, ?_,
    fun t ω => abs_stoppedProcess_le hc hneg hR ω t, hAad.stoppedProcess hAc hσ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    obtain ⟨φ, hφc, -, -, -, hφ⟩ := hclock ω
    have : (fun t => stoppedProcess N (locTimeAbs N R) t ω) = fun t => N (φ t) ω := by
      funext t; exact congrArg (fun x => N x ω) (hφ t)
    rw [this]; exact (hc ω).comp hφc
  · intro ω
    obtain ⟨φ, hφc, -, -, -, hφ⟩ := hclock ω
    have : (fun t => stoppedProcess (fun t (_ : Ω) => a * max t 0) (locTimeAbs N R) t ω) =
        fun t => a * max (φ t) 0 := by
      funext t; exact congrArg (fun x => a * max x 0) (hφ t)
    rw [this]; exact continuous_const.mul (hφc.max continuous_const)
  · intro ω u v huv
    obtain ⟨φ, -, hφm, -, -, hφ⟩ := hclock ω
    show a * max ((min (u : WithTop ℝ) (locTimeAbs N R ω)).untopA) 0 ≤
      a * max ((min (v : WithTop ℝ) (locTimeAbs N R ω)).untopA) 0
    rw [hφ, hφ]
    exact mul_le_mul_of_nonneg_left (max_le_max (hφm huv) le_rfl) ha
  · intro ω u v huv
    obtain ⟨φ, -, hφm, hφl, -, hφ⟩ := hclock ω
    show a * max ((min (v : WithTop ℝ) (locTimeAbs N R ω)).untopA) 0 -
      a * max ((min (u : WithTop ℝ) (locTimeAbs N R ω)).untopA) 0 ≤ a * (v - u)
    rw [hφ, hφ, ← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ ha
    have h1 := hφl u v huv
    have h2 := hφm huv
    rcases le_total (φ u) 0 with h3 | h3
    · rw [max_eq_right h3]
      rcases le_total (φ v) 0 with h4 | h4
      · rw [max_eq_right h4]; linarith
      · rw [max_eq_left h4]; linarith
    · rw [max_eq_left h3, max_eq_left (h3.trans h2)]; linarith
  · intro t ω
    exact mul_nonneg ha (le_max_right _ _)
  · intro t ω
    obtain ⟨φ, -, -, -, hφt, hφ⟩ := hclock ω
    show a * max ((min (t : WithTop ℝ) (locTimeAbs N R ω)).untopA) 0 ≤ a * max t 0
    rw [hφ]
    exact mul_le_mul_of_nonneg_left (max_le_max (hφt t) le_rfl) ha
  · have hQc : ∀ ω : Ω, Continuous fun t : ℝ => N t ω ^ 2 - a * max t 0 := fun ω =>
      ((hc ω).pow 2).sub (continuous_const.mul (continuous_id.max continuous_const))
    exact Martingale.stoppedProcess_of_continuous P ℱ _ hQ hQc hσ

theorem eventually_le_locTimeAbs {N : ℝ → Ω → ℝ} (hc : ∀ ω, Continuous fun t => N t ω) (ω : Ω)
    (u : ℝ) : ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → (u : WithTop ℝ) ≤ locTimeAbs N ((m : ℝ) + 1) ω := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := u)).exists_bound_of_continuousOn
    (f := fun v => N v ω) (hc ω).continuousOn
  obtain ⟨m0, hm0⟩ := exists_nat_gt C
  refine ⟨m0, fun m hm => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hne : locTimeAbs N ((m : ℝ) + 1) ω ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨c, hcdef⟩ := WithTop.ne_top_iff_exists.1 hne
  have hσ : locTimeAbs N ((m : ℝ) + 1) ω = (c : WithTop ℝ) := hcdef.symm
  have hmem := mem_of_hittingAfter_eq_of_isClosed (fun t ω => |N t ω|) ω (hc ω).abs isClosed_Ici
    0 c hσ
  have hc0 : 0 ≤ c := by
    have : (0 : WithTop ℝ) ≤ locTimeAbs N ((m : ℝ) + 1) ω := le_hittingAfter ω
    rw [hσ] at this; exact WithTop.coe_le_coe.1 this
  have hcu : c < u := by
    rw [hσ] at hlt; exact WithTop.coe_lt_coe.1 hlt
  have h1 := hC c ⟨hc0, hcu.le⟩
  have h2 : (m : ℝ) + 1 ≤ |N c ω| := hmem
  have h3 : (m0 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Real.norm_eq_abs] at h1
  linarith

theorem stoppedProcess_eq_of_le_locTimeAbs {N : ℝ → Ω → ℝ} {R : ℝ} {ω : Ω} {u : ℝ}
    (h : (u : WithTop ℝ) ≤ locTimeAbs N R ω) {M : ℝ → Ω → ℝ} :
    stoppedProcess M (locTimeAbs N R) u ω = M u ω := by
  show M (min (u : WithTop ℝ) (locTimeAbs N R ω)).untopA ω = M u ω
  rw [min_eq_left h]; rfl

/-- **Exponential martingale** for a continuous martingale `N` (with `N_t = 0` for `t ≤ 0`) such
that `N² - a t⁺` is a martingale. -/
theorem exp_martingale {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {N : ℝ → Ω → ℝ} (hN : Martingale N ℱ P) (hc : ∀ ω, Continuous fun t => N t ω)
    (hneg : ∀ t, t ≤ 0 → ∀ ω, N t ω = 0) {a : ℝ} (ha : 0 ≤ a)
    (hQ : Martingale (fun t ω => N t ω ^ 2 - a * max t 0) ℱ P) {s t : ℝ} (hst : s ≤ t)
    {g : Ω → ℂ} (hg : StronglyMeasurable[ℱ s] g) {C : ℝ} (hgC : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, g ω * (LevyData.expMart N (fun t (_ : Ω) => a * max t 0) t ω -
      LevyData.expMart N (fun t (_ : Ω) => a * max t 0) s ω) ∂P = 0 := by
  set Ad : ℝ → Ω → ℝ := fun t _ => a * max t 0 with hAd
  have hD : ∀ m : ℕ, LevyData P ℱ (stoppedProcess N (locTimeAbs N ((m : ℝ) + 1)))
      (stoppedProcess Ad (locTimeAbs N ((m : ℝ) + 1))) ((m : ℝ) + 1) a := fun m =>
    levyData_stopped hN hc hneg ha hQ (by positivity)
  have hC : 0 ≤ C := by
    have : Nonempty Ω := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hgC (Classical.arbitrary Ω))
  have hgm : Measurable g := (hg.mono (ℱ.le s)).measurable
  set F : ℕ → Ω → ℂ := fun m ω => g ω *
    (LevyData.expMart (stoppedProcess N (locTimeAbs N ((m : ℝ) + 1)))
      (stoppedProcess Ad (locTimeAbs N ((m : ℝ) + 1))) t ω -
     LevyData.expMart (stoppedProcess N (locTimeAbs N ((m : ℝ) + 1)))
      (stoppedProcess Ad (locTimeAbs N ((m : ℝ) + 1))) s ω) with hF
  set FI : Ω → ℂ := fun ω => g ω * (LevyData.expMart N Ad t ω - LevyData.expMart N Ad s ω) with hFI
  have hF0 : ∀ m, ∫ ω, F m ω ∂P = 0 := fun m =>
    (hD m).exp_martingale_bounded hst hg hgC
  have hFm : ∀ m, Measurable (F m) := fun m =>
    hgm.mul (((hD m).measurable_expMart t).sub ((hD m).measurable_expMart s))
  have hB : ∀ m ω, ‖F m ω‖ ≤ C * (Real.exp (a * max t 0 / 2) + Real.exp (a * max t 0 / 2)) :=
    fun m ω => by
      rw [hF, norm_mul]
      refine mul_le_mul (hgC ω) ((norm_sub_le _ _).trans (add_le_add
        ((hD m).norm_expMart_le (T := max t 0) le_rfl ω)
        ((hD m).norm_expMart_le (T := max t 0) (max_le_max hst le_rfl) ω))) (norm_nonneg _) hC
  have hlim : ∀ ω, Tendsto (fun m => F m ω) atTop (𝓝 (FI ω)) := by
    intro ω
    obtain ⟨m1, hm1⟩ := eventually_le_locTimeAbs hc ω t
    obtain ⟨m2, hm2⟩ := eventually_le_locTimeAbs hc ω s
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (max m1 m2)] with m hm
    have e1 := stoppedProcess_eq_of_le_locTimeAbs (hm1 m (le_trans (le_max_left _ _) hm)) (M := N)
    have e2 := stoppedProcess_eq_of_le_locTimeAbs (hm2 m (le_trans (le_max_right _ _) hm)) (M := N)
    have e3 := stoppedProcess_eq_of_le_locTimeAbs (hm1 m (le_trans (le_max_left _ _) hm)) (M := Ad)
    have e4 := stoppedProcess_eq_of_le_locTimeAbs (hm2 m (le_trans (le_max_right _ _) hm)) (M := Ad)
    simp only [hF, hFI, LevyData.expMart, e1, e2, e3, e4]
  have hdct := tendsto_integral_of_dominated_convergence (μ := P) (F := F) (f := FI)
    (fun _ => C * (Real.exp (a * max t 0 / 2) + Real.exp (a * max t 0 / 2)))
    (fun m => (hFm m).aestronglyMeasurable) (integrable_const _)
    (fun m => Eventually.of_forall (hB m)) (Eventually.of_forall hlim)
  simp_rw [hF0] at hdct
  exact tendsto_nhds_unique hdct tendsto_const_nhds

end LevyLocalize

section LevyVector

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {β : ℝ≥0 → Ω → ι → ℝ}

theorem martingale_finset_sum {κ : Type*} (S : Finset κ) (f : κ → ℝ → Ω → ℝ)
    (hf : ∀ i ∈ S, Martingale (f i) ℱ P) : Martingale (fun t ω => ∑ i ∈ S, f i t ω) ℱ P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact martingale_zero ℝ ℱ P
  | insert i S hi ih =>
    have h1 := (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    convert h1 using 2 with t
    funext ω
    simp [Finset.sum_insert hi]

theorem martingale_smul_fun (c : ℝ) {f : ℝ → Ω → ℝ} (hf : Martingale f ℱ P) :
    Martingale (fun t ω => c * f t ω) ℱ P := by
  have := hf.smul c
  convert this using 1

/-- The one-dimensional projection `θ · β` and its compensator. -/
theorem levy_projection [DecidableEq ι] (θ : ι → ℝ)
    (hmart : ∀ k, Martingale (fun (t : ℝ) ω => ofNNRealTime β t ω k) ℱ P)
    (hqv : ∀ k l, Martingale (fun (t : ℝ) ω =>
      ofNNRealTime β t ω k * ofNNRealTime β t ω l - if k = l then max t 0 else 0) ℱ P) :
    Martingale (fun t ω => ∑ k, θ k * ofNNRealTime β t ω k) ℱ P ∧
    Martingale (fun t ω => (∑ k, θ k * ofNNRealTime β t ω k) ^ 2 - (∑ k, θ k ^ 2) * max t 0) ℱ P := by
  refine ⟨martingale_finset_sum _ _ fun k _ => martingale_smul_fun _ (hmart k), ?_⟩
  have h := martingale_finset_sum (Finset.univ : Finset ι) (fun k t ω =>
    ∑ l, θ k * θ l * (ofNNRealTime β t ω k * ofNNRealTime β t ω l - if k = l then max t 0 else 0))
    (fun k _ => martingale_finset_sum _ _ fun l _ => martingale_smul_fun _ (hqv k l))
  convert h using 2 with t
  funext ω
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sq, Finset.sum_mul_sum]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have : ∑ x : ι, θ x * θ x * max t 0 = (∑ k, θ k ^ 2) * max t 0 := by
    rw [Finset.sum_mul]; simp [sq]
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end LevyVector


section LevyIndep

theorem charFunDual_gaussianReal_zero (v : ℝ≥0) (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 v) L = Complex.exp (-((L 1 : ℝ) ^ 2 * (v : ℝ) / 2 : ℝ)) := by
  have hL : ∀ x : ℝ, L x = L 1 * x := fun x => by
    have := L.map_smul x (1 : ℝ)
    simpa [mul_comm] using this
  rw [charFunDual_apply]
  have : ∀ x : ℝ, Complex.exp ((L x : ℂ) * Complex.I) = Complex.exp (((L 1 * x : ℝ) : ℂ) * Complex.I) :=
    fun x => by rw [hL x]
  simp_rw [this]
  have h2 := charFun_gaussianReal (μ := 0) (v := v) (L 1)
  rw [charFun_apply_real] at h2
  simp only [Complex.ofReal_mul] at h2 ⊢
  rw [h2]
  congr 1
  push_cast
  ring

theorem strongDual_pi_apply [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (y : ι → ℝ) :
    L y = ∑ k, L (Pi.single k 1) * y k := by
  conv_lhs => rw [pi_eq_sum_univ y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  congr 2
  funext j
  by_cases h : k = j <;> simp [Pi.single_apply, h, eq_comm]

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- If conditionally on every `ℱ s`-measurable `A` the characteristic function of `Y` is the
Gaussian one, then `Y` is Gaussian and independent of `ℱ s`. -/
theorem indep_and_law_of_charFun [DecidableEq ι] {ℱ : Filtration ℝ mΩ} (s : ℝ) {Y : Ω → ι → ℝ}
    (hY : Measurable Y) (v : ℝ≥0)
    (h : ∀ A : Set Ω, MeasurableSet[ℱ s] A → ∀ θ : ι → ℝ,
      ∫ ω in A, Complex.exp (Complex.I * ((∑ k, θ k * Y ω k : ℝ) : ℂ)) ∂P =
        (P.real A : ℂ) * Complex.exp (-((∑ k, θ k ^ 2) * (v : ℝ) / 2 : ℝ))) :
    Indep (MeasurableSpace.comap Y inferInstance) (ℱ s) P ∧
      HasLaw Y (Measure.pi fun _ : ι => gaussianReal 0 v) P := by
  set γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 v with hγ
  have hγp : IsProbabilityMeasure γ := by rw [hγ]; infer_instance
  have key : ∀ A : Set Ω, MeasurableSet[ℱ s] A → (P.restrict A).map Y = P A • γ := by
    intro A hA
    have hAm : MeasurableSet A := ℱ.le s A hA
    have : IsFiniteMeasure (P A • γ) := Measure.smul_finite γ (measure_ne_top P A)
    refine Measure.ext_of_charFunDual ?_
    funext L
    have hLY : ∀ y : ι → ℝ, Complex.exp ((L y : ℂ) * Complex.I) =
        Complex.exp (Complex.I * ((∑ k, L (Pi.single k 1) * y k : ℝ) : ℂ)) := fun y => by
      rw [strongDual_pi_apply L y, mul_comm]
    have hlhs : charFunDual ((P.restrict A).map Y) L =
        ∫ ω in A, Complex.exp (Complex.I * ((∑ k, L (Pi.single k 1) * Y ω k : ℝ) : ℂ)) ∂P := by
      rw [charFunDual_apply, integral_map hY.aemeasurable]
      · simp_rw [hLY]
      · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    have hrhs : charFunDual (P A • γ) L = (P.real A : ℂ) *
        Complex.exp (-((∑ k, L (Pi.single k 1) ^ 2) * (v : ℝ) / 2 : ℝ)) := by
      rw [charFunDual_apply, integral_smul_measure, ← charFunDual_apply, hγ,
        charFunDual_pi (E := fun _ : ι => ℝ) (μ := fun _ : ι => gaussianReal 0 v) L]
      have : ∀ i : ι, charFunDual (gaussianReal 0 v) (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) =
          Complex.exp (-((L (Pi.single i 1)) ^ 2 * (v : ℝ) / 2 : ℝ)) := fun i => by
        rw [charFunDual_gaussianReal_zero]
        rfl
      simp_rw [this]
      rw [← Complex.exp_sum]
      simp only [Measure.real, Complex.real_smul]
      congr 2
      push_cast
      rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    rw [hlhs, hrhs]
    exact h A hA _
  have hlaw : P.map Y = γ := by
    have := key Set.univ MeasurableSet.univ
    simpa using this
  refine ⟨?_, ⟨hY.aemeasurable, hlaw⟩⟩
  rw [Indep_iff]
  rintro _ t2 ⟨B, hB, rfl⟩ ht2
  have h1 := key t2 ht2
  have h2 := congrArg (fun m => m B) h1
  simp only [Measure.map_apply hY hB, Measure.smul_apply, smul_eq_mul] at h2
  rw [Measure.restrict_apply (hY hB)] at h2
  have h3 : P (Y ⁻¹' B) = γ B := by rw [← hlaw, Measure.map_apply hY hB]
  rw [h2, h3, mul_comm]

end LevyIndep

section LevyBeta

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {β : ℝ≥0 → Ω → ι → ℝ}

/-- Conditional characteristic function of an increment of `β`. -/
theorem levy_incr_charFun [DecidableEq ι] (h0 : ∀ ω, β 0 ω = 0)
    (hcont : ∀ ω, Continuous fun t => β t ω)
    (hmart : ∀ k, Martingale (fun (t : ℝ) ω => ofNNRealTime β t ω k) ℱ P)
    (hqv : ∀ k l, Martingale (fun (t : ℝ) ω =>
      ofNNRealTime β t ω k * ofNNRealTime β t ω l - if k = l then max t 0 else 0) ℱ P)
    (s t : ℝ≥0) (hst : s ≤ t) (A : Set Ω) (hA : MeasurableSet[ℱ (s : ℝ)] A) (θ : ι → ℝ) :
    ∫ ω in A, Complex.exp (Complex.I * ((∑ k, θ k * (β t ω k - β s ω k) : ℝ) : ℂ)) ∂P =
      (P.real A : ℂ) * Complex.exp (-((∑ k, θ k ^ 2) * ((t - s : ℝ≥0) : ℝ) / 2 : ℝ)) := by
  obtain ⟨hN, hQ⟩ := levy_projection (P := P) (ℱ := ℱ) (β := β) θ hmart hqv
  set N : ℝ → Ω → ℝ := fun t ω => ∑ k, θ k * ofNNRealTime β t ω k with hNdef
  set a : ℝ := ∑ k, θ k ^ 2 with hadef
  have ha : 0 ≤ a := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hc : ∀ ω, Continuous fun t => N t ω := fun ω => by
    refine continuous_finset_sum _ fun k _ => continuous_const.mul ?_
    exact (continuous_apply k).comp (continuous_ofNNRealTime β ω (hcont ω))
  have hneg : ∀ t, t ≤ 0 → ∀ ω, N t ω = 0 := fun t ht ω => by
    simp [hNdef, ofNNRealTime_apply, Real.toNNReal_of_nonpos ht, h0]
  have hAm : MeasurableSet A := ℱ.le _ _ hA
  have hNm : ∀ u, Measurable[ℱ u] (N u) := fun u => (hN.1 u).measurable
  set g : Ω → ℂ := fun ω => A.indicator (fun _ => (1 : ℂ)) ω *
    Complex.exp (-(Complex.I * (N s ω : ℂ)) - (a * max (s : ℝ) 0 / 2 : ℝ)) with hg
  have hgm : StronglyMeasurable[ℱ (s : ℝ)] g := by
    refine Measurable.stronglyMeasurable ?_
    refine (measurable_const.indicator hA).mul (Complex.measurable_exp.comp ?_)
    exact ((measurable_const.mul (Complex.measurable_ofReal.comp (hNm s))).neg).sub measurable_const
  have hgC : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    rw [hg]; simp only [norm_mul, Complex.norm_exp]
    have h1 : ‖A.indicator (fun _ => (1 : ℂ)) ω‖ ≤ 1 := by
      by_cases hω : ω ∈ A <;> simp [hω]
    have h2 : Real.exp (-(Complex.I * (N s ω : ℂ)) - (a * max (s : ℝ) 0 / 2 : ℝ)).re ≤ 1 := by
      rw [Real.exp_le_one_iff]
      simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero, neg_zero]
      have : 0 ≤ a * max (s : ℝ) 0 / 2 := by positivity
      linarith
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  have hE := exp_martingale hN hc hneg ha hQ (s := (s : ℝ)) (t := (t : ℝ)) (by exact_mod_cast hst) hgm hgC
  set Δ : Ω → ℝ := fun ω => ∑ k, θ k * (β t ω k - β s ω k) with hΔ
  have hΔN : ∀ ω, Δ ω = N t ω - N s ω := fun ω => by
    simp only [hΔ, hNdef, ofNNRealTime_apply, Real.toNNReal_coe, mul_sub, Finset.sum_sub_distrib]
  have hΔm : Measurable Δ := by
    have : Measurable (fun ω => N t ω - N s ω) :=
      ((hNm t).mono (ℱ.le _) le_rfl).sub ((hNm s).mono (ℱ.le _) le_rfl)
    simpa [funext hΔN] using this
  set c : ℂ := Complex.exp ((a * ((t : ℝ) - s) / 2 : ℝ)) with hcdef
  have hpt : ∀ ω, g ω * (LevyData.expMart N (fun t (_ : Ω) => a * max t 0) t ω -
      LevyData.expMart N (fun t (_ : Ω) => a * max t 0) s ω) =
      A.indicator (fun ω => c * Complex.exp (Complex.I * (Δ ω : ℂ)) - 1) ω := fun ω => by
    by_cases hω : ω ∈ A
    · simp only [hg, Set.indicator_of_mem hω, one_mul, LevyData.expMart, mul_sub, ← Complex.exp_add]
      have e1 : Complex.exp (-(Complex.I * (N s ω : ℂ)) - ((a * max (s : ℝ) 0 / 2 : ℝ) : ℂ) +
          (Complex.I * (N t ω : ℂ) + ((a * max (t : ℝ) 0 : ℝ) : ℂ) / 2)) =
          c * Complex.exp (Complex.I * (Δ ω : ℂ)) := by
        rw [hcdef, ← Complex.exp_add]
        congr 1
        rw [hΔN, max_eq_left (NNReal.coe_nonneg t), max_eq_left (NNReal.coe_nonneg s)]
        push_cast; ring
      have e2 : Complex.exp (-(Complex.I * (N s ω : ℂ)) - ((a * max (s : ℝ) 0 / 2 : ℝ) : ℂ) +
          (Complex.I * (N s ω : ℂ) + ((a * max (s : ℝ) 0 : ℝ) : ℂ) / 2)) = 1 := by
        rw [← Complex.exp_zero]; congr 1
        push_cast; ring
      rw [e1, e2]
    · simp [hg, Set.indicator_of_notMem hω]
  simp_rw [hpt] at hE
  rw [integral_indicator hAm] at hE
  have hint1 : Integrable (fun ω => Complex.exp (Complex.I * (Δ ω : ℂ))) (P.restrict A) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun ω => ?_)
    · exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp hΔm))).aestronglyMeasurable
    · rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [integral_sub (hint1.const_mul c) (integrable_const _), integral_const_mul, setIntegral_const] at hE
  have hcx : Complex.exp (-((a * ((t - s : ℝ≥0) : ℝ) / 2 : ℝ))) * c = 1 := by
    rw [hcdef, ← Complex.exp_add, ← Complex.exp_zero]; congr 1
    rw [NNReal.coe_sub hst]; push_cast; ring
  have hJ : c * ∫ ω in A, Complex.exp (Complex.I * (Δ ω : ℂ)) ∂P = (P.real A : ℂ) := by
    simpa [sub_eq_zero] using hE
  calc ∫ ω in A, Complex.exp (Complex.I * ((∑ k, θ k * (β t ω k - β s ω k) : ℝ) : ℂ)) ∂P
      = (Complex.exp (-((a * ((t - s : ℝ≥0) : ℝ) / 2 : ℝ))) * c) *
        ∫ ω in A, Complex.exp (Complex.I * (Δ ω : ℂ)) ∂P := by rw [hcx, one_mul]
    _ = Complex.exp (-((a * ((t - s : ℝ≥0) : ℝ) / 2 : ℝ))) * (c * ∫ ω in A, Complex.exp (Complex.I * (Δ ω : ℂ)) ∂P) := by
        rw [mul_assoc]
    _ = _ := by rw [hJ, mul_comm]

end LevyBeta

/-- **Lévy's characterisation.** `β : ℝ≥0 → Ω → ι → ℝ` adapted to a complete filtration `ℱ`,
with everywhere continuous paths, `β_0 = 0`, each `β^k` a martingale and each
`β^k_t β^l_t - δ_{kl} t` a martingale (over real time, `β` frozen on `(-∞,0]`): then `β` is a
Brownian family relative to `ℱ`. -/
theorem levy_characterization [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (hℱ : IsCompleteFiltration P ℱ) (β : ℝ≥0 → Ω → ι → ℝ)
    (hadapted : ∀ t : ℝ≥0, Measurable[ℱ t] (β t)) (h0 : ∀ ω, β 0 ω = 0)
    (hcont : ∀ ω, Continuous fun t => β t ω)
    (hmart : ∀ k, Martingale (fun (t : ℝ) ω => ofNNRealTime β t ω k) ℱ P)
    (hqv : ∀ k l, Martingale (fun (t : ℝ) ω =>
      ofNNRealTime β t ω k * ofNNRealTime β t ω l - if k = l then max t 0 else 0) ℱ P) :
    IsBrownianFiltration P ℱ β := by
  have hmeas : ∀ t : ℝ≥0, Measurable (β t) := fun t => (hadapted t).mono (ℱ.le _) le_rfl
  have key : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => β t ω - β s ω) inferInstance) (ℱ s) P ∧
      HasLaw (fun ω => β t ω - β s ω) (Measure.pi fun _ : ι => gaussianReal 0 (t - s)) P :=
    fun s t hst => indep_and_law_of_charFun (P := P) (ℱ := ℱ) (s : ℝ)
      ((hmeas t).sub (hmeas s)) (t - s)
      (fun A hA θ => levy_incr_charFun h0 hcont hmart hqv s t hst A hA θ)
  exact ⟨hℱ, hadapted, h0, hcont, fun s t hst => (key s t hst).1, fun s t hst => (key s t hst).2⟩

/-! ### The stopped Brownian `L²` bound -/

theorem integral_sq_sub_condExp {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, (f ω - (P[f | m]) ω) ^ 2 ∂P = ∫ ω, f ω ^ 2 ∂P - ∫ ω, ((P[f | m]) ω) ^ 2 ∂P := by
  have hg : MemLp (P[f | m]) 2 P := hf.condExp (by norm_num)
  have hgsm : StronglyMeasurable[m] (P[f | m]) := stronglyMeasurable_condExp
  have hgf : Integrable (P[f | m] * f) P := hg.integrable_mul hf
  have hc : P[P[f | m] * f | m] =ᵐ[P] P[f | m] * P[f | m] :=
    condExp_mul_of_stronglyMeasurable_left hgsm hgf (hf.integrable one_le_two)
  have h1 : ∫ ω, (P[f | m]) ω * f ω ∂P = ∫ ω, ((P[f | m]) ω) ^ 2 ∂P := by
    have := integral_condExp (μ := P) (m := m) (f := P[f | m] * f) hm
    have h2 : ∫ ω, (P[f | m] * f) ω ∂P = ∫ ω, (P[f | m]) ω * f ω ∂P := rfl
    rw [← h2, ← this]
    refine integral_congr_ae ?_
    filter_upwards [hc] with ω hω
    simp only [Pi.mul_apply] at hω
    rw [hω]; ring
  have e : ∀ ω, (f ω - (P[f | m]) ω) ^ 2 =
      f ω ^ 2 - 2 * ((P[f | m]) ω * f ω) + ((P[f | m]) ω) ^ 2 := fun ω => by ring
  simp_rw [e]
  rw [integral_add, integral_sub, integral_const_mul, h1]
  · ring
  · exact hf.integrable_sq
  · exact hgf.const_mul 2
  · exact hf.integrable_sq.sub (hgf.const_mul 2)
  · exact hg.integrable_sq


section StoppedL2

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {β : ℝ≥0 → Ω → ι → ℝ}

theorem countable_range_coe_real {S : Ω → ℝ} (hc : (Set.range S).Countable) :
    (Set.range fun ω => ((S ω : ℝ) : WithTop ℝ)).Countable :=
  (hc.image (fun x : ℝ => (x : WithTop ℝ))).mono (by
    rintro _ ⟨ω, rfl⟩; exact ⟨S ω, ⟨ω, rfl⟩, rfl⟩)

theorem memLp_stopped_coord (hβ : IsBrownianFiltration P ℱ β) (k : ι)
    {S : Ω → ℝ} (hS : IsStoppingTime ℱ fun ω => ((S ω : ℝ) : WithTop ℝ))
    (hc : (Set.range S).Countable) {N : ℝ} (hN : ∀ ω, S ω ≤ N) :
    MemLp (fun ω => ofNNRealTime β (S ω) ω k) 2 P := by
  have hX := hβ.martingale k
  have hle : ∀ ω, ((S ω : ℝ) : WithTop ℝ) ≤ (N : WithTop ℝ) := fun ω => by exact_mod_cast hN ω
  have hcond := hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hS hle
    (countable_range_coe_real hc)
  exact ((hβ.memLp_two_coord_real N k).condExp (by norm_num)).ae_eq hcond.symm

theorem integrable_max_stopped (hβ : IsBrownianFiltration P ℱ β) (k : ι)
    {S : Ω → ℝ} (hS : IsStoppingTime ℱ fun ω => ((S ω : ℝ) : WithTop ℝ))
    (hc : (Set.range S).Countable) {N : ℝ} (hN : ∀ ω, S ω ≤ N) :
    Integrable (fun ω => max (S ω) 0) P := by
  have hQ := hβ.martingale_sq_sub k
  have hle : ∀ ω, ((S ω : ℝ) : WithTop ℝ) ≤ (N : WithTop ℝ) := fun ω => by exact_mod_cast hN ω
  have hcond := hQ.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hS hle
    (countable_range_coe_real hc)
  have hint1 : Integrable (fun ω => ofNNRealTime β (S ω) ω k ^ 2 - max (S ω) 0) P :=
    integrable_condExp.congr hcond.symm
  have hint2 : Integrable (fun ω => ofNNRealTime β (S ω) ω k ^ 2) P :=
    (memLp_stopped_coord hβ k hS hc hN).integrable_sq
  have := hint2.sub hint1
  refine this.congr (Eventually.of_forall fun ω => ?_)
  simp

/-- For a bounded stopping time with countable range, `E X_S² = E S⁺` for the Brownian
coordinate `X = β^k`. -/
theorem integral_sq_stopped_coord (hβ : IsBrownianFiltration P ℱ β) (k : ι)
    {S : Ω → ℝ} (hS : IsStoppingTime ℱ fun ω => ((S ω : ℝ) : WithTop ℝ))
    (hc : (Set.range S).Countable) {N : ℝ} (hN0 : 0 ≤ N) (hN : ∀ ω, S ω ≤ N) :
    ∫ ω, (ofNNRealTime β (S ω) ω k) ^ 2 ∂P = ∫ ω, max (S ω) 0 ∂P := by
  have hQ := hβ.martingale_sq_sub k
  have hle : ∀ ω, ((S ω : ℝ) : WithTop ℝ) ≤ (N : WithTop ℝ) := fun ω => by exact_mod_cast hN ω
  have hcond := hQ.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hS hle
    (countable_range_coe_real hc)
  have h1 : ∫ ω, stoppedValue (fun (t : ℝ) ω => ofNNRealTime β t ω k ^ 2 - max t 0)
      (fun ω => ((S ω : ℝ) : WithTop ℝ)) ω ∂P =
      ∫ ω, (ofNNRealTime β N ω k ^ 2 - max N 0) ∂P := by
    rw [integral_congr_ae hcond, integral_condExp (hS.measurableSpace_le_of_le hle)]
  have h2 : ∫ ω, (ofNNRealTime β N ω k ^ 2 - max N 0) ∂P = 0 := by
    have h4 := integral_condExp (μ := P) (m := ℱ 0) (f := fun ω => ofNNRealTime β N ω k ^ 2 - max N 0)
      (ℱ.le 0)
    rw [← h4, integral_congr_ae (hQ.2 0 N hN0)]
    simp [ofNNRealTime, hβ.zero]
  have h5 : ∫ ω, stoppedValue (fun (t : ℝ) ω => ofNNRealTime β t ω k ^ 2 - max t 0)
      (fun ω => ((S ω : ℝ) : WithTop ℝ)) ω ∂P =
      ∫ ω, (ofNNRealTime β (S ω) ω k ^ 2 - max (S ω) 0) ∂P := rfl
  have hint1 : Integrable (fun ω => ofNNRealTime β (S ω) ω k ^ 2 - max (S ω) 0) P :=
    integrable_condExp.congr hcond.symm
  have hint2 : Integrable (fun ω => ofNNRealTime β (S ω) ω k ^ 2) P :=
    (memLp_stopped_coord hβ k hS hc hN).integrable_sq
  have hint3 : Integrable (fun ω => max (S ω) 0) P := integrable_max_stopped hβ k hS hc hN
  rw [h5, h2] at h1
  rw [integral_sub hint2 hint3] at h1
  linarith

/-- Orthogonality of martingale increments between two ordered bounded stopping times with
countable range: `E (X_T - X_S)² = E (T⁺ - S⁺)`. -/
theorem integral_sq_stopped_incr (hβ : IsBrownianFiltration P ℱ β) (k : ι)
    {S T : Ω → ℝ} (hS : IsStoppingTime ℱ fun ω => ((S ω : ℝ) : WithTop ℝ))
    (hT : IsStoppingTime ℱ fun ω => ((T ω : ℝ) : WithTop ℝ))
    (hSc : (Set.range S).Countable) (hTc : (Set.range T).Countable) (hST : ∀ ω, S ω ≤ T ω)
    {N : ℝ} (hN0 : 0 ≤ N) (hN : ∀ ω, T ω ≤ N) :
    ∫ ω, (ofNNRealTime β (T ω) ω k - ofNNRealTime β (S ω) ω k) ^ 2 ∂P =
      ∫ ω, (max (T ω) 0 - max (S ω) 0) ∂P := by
  have hX := hβ.martingale k
  have hleT : ∀ ω, ((T ω : ℝ) : WithTop ℝ) ≤ (N : WithTop ℝ) := fun ω => by exact_mod_cast hN ω
  have hSTle : (fun ω => ((S ω : ℝ) : WithTop ℝ)) ≤ fun ω => ((T ω : ℝ) : WithTop ℝ) :=
    fun ω => WithTop.coe_le_coe.2 (hST ω)
  have hcond := hX.stoppedValue_ae_eq_condExp_of_le_of_countable_range hT hS hSTle hleT
    (countable_range_coe_real hTc) (countable_range_coe_real hSc)
  have hmT : MemLp (fun ω => ofNNRealTime β (T ω) ω k) 2 P := memLp_stopped_coord hβ k hT hTc hN
  have hmS : MemLp (fun ω => ofNNRealTime β (S ω) ω k) 2 P :=
    memLp_stopped_coord hβ k hS hSc (fun ω => (hST ω).trans (hN ω))
  have hsq := integral_sq_sub_condExp (P := P) (hS.measurableSpace_le_of_le
    (fun ω => by exact_mod_cast (hST ω).trans (hN ω))) hmT
  have e1 : ∀ᵐ ω ∂P, (ofNNRealTime β (T ω) ω k - ofNNRealTime β (S ω) ω k) ^ 2 =
      (ofNNRealTime β (T ω) ω k - (P[fun ω => ofNNRealTime β (T ω) ω k |
        hS.measurableSpace]) ω) ^ 2 := by
    filter_upwards [hcond] with ω hω
    have hω' : ofNNRealTime β (S ω) ω k =
        (P[fun ω => ofNNRealTime β (T ω) ω k | hS.measurableSpace]) ω := hω
    rw [hω']
  have e2 : ∀ᵐ ω ∂P, ((P[fun ω => ofNNRealTime β (T ω) ω k | hS.measurableSpace]) ω) ^ 2 =
      (ofNNRealTime β (S ω) ω k) ^ 2 := by
    filter_upwards [hcond] with ω hω
    have hω' : ofNNRealTime β (S ω) ω k =
        (P[fun ω => ofNNRealTime β (T ω) ω k | hS.measurableSpace]) ω := hω
    rw [hω']
  have hTT := integral_sq_stopped_coord hβ k hT hTc hN0 hN
  have hSS := integral_sq_stopped_coord hβ k hS hSc hN0 (fun ω => (hST ω).trans (hN ω))
  have hmaxT : Integrable (fun ω => max (T ω) 0) P := integrable_max_stopped hβ k hT hTc hN
  have hmaxS : Integrable (fun ω => max (S ω) 0) P :=
    integrable_max_stopped hβ k hS hSc (fun ω => (hST ω).trans (hN ω))
  rw [integral_congr_ae e1, hsq, integral_congr_ae e2, hTT, hSS, integral_sub hmaxT hmaxS]

theorem isStoppingTime_max_const {S : Ω → ℝ} (hS : IsStoppingTime ℱ fun ω => ((S ω : ℝ) : WithTop ℝ))
    (v : ℝ) : IsStoppingTime ℱ fun ω => ((max (S ω) v : ℝ) : WithTop ℝ) := by
  have := hS.max (isStoppingTime_const ℱ v)
  convert this using 2 with ω
  simp

theorem isStoppingTime_min_const {S : Ω → ℝ} (hS : IsStoppingTime ℱ fun ω => ((S ω : ℝ) : WithTop ℝ))
    (v : ℝ) : IsStoppingTime ℱ fun ω => ((min (S ω) v : ℝ) : WithTop ℝ) := by
  have := hS.min (isStoppingTime_const ℱ v)
  convert this using 2 with ω

theorem isStoppingTime_const_real (v : ℝ) :
    IsStoppingTime ℱ fun _ : Ω => ((v : ℝ) : WithTop ℝ) := isStoppingTime_const ℱ v

/-- `E (X_S - X_v)² = E |S - v|` for a bounded stopping time `S ≥ 0` with countable range. -/
theorem integral_sq_stopped_sub_const (hβ : IsBrownianFiltration P ℱ β) (k : ι)
    {S : Ω → ℝ} (hS : IsStoppingTime ℱ fun ω => ((S ω : ℝ) : WithTop ℝ))
    (hc : (Set.range S).Countable) (hS0 : ∀ ω, 0 ≤ S ω) {N : ℝ} (hN : ∀ ω, S ω ≤ N)
    {v : ℝ} (hv : 0 ≤ v) (hvN : v ≤ N) :
    ∫ ω, (ofNNRealTime β (S ω) ω k - ofNNRealTime β v ω k) ^ 2 ∂P = ∫ ω, |S ω - v| ∂P := by
  have hρ := isStoppingTime_max_const hS v
  have hμ := isStoppingTime_min_const hS v
  have hvst : IsStoppingTime ℱ fun _ : Ω => ((v : ℝ) : WithTop ℝ) := isStoppingTime_const ℱ v
  have hρc : (Set.range fun ω => max (S ω) v).Countable :=
    (hc.image (fun x => max x v)).mono (by rintro _ ⟨ω, rfl⟩; exact ⟨S ω, ⟨ω, rfl⟩, rfl⟩)
  have hμc : (Set.range fun ω => min (S ω) v).Countable :=
    (hc.image (fun x => min x v)).mono (by rintro _ ⟨ω, rfl⟩; exact ⟨S ω, ⟨ω, rfl⟩, rfl⟩)
  have hvc : (Set.range fun _ : Ω => v).Countable := by
    refine (Set.countable_singleton v).mono ?_
    rintro _ ⟨ω, rfl⟩; rfl
  have hN0 : 0 ≤ N := hv.trans hvN
  have h1 := integral_sq_stopped_incr hβ k hvst hρ hvc hρc (fun ω => le_max_right _ _) hN0
    (N := N) (fun ω => max_le (hN ω) hvN)
  have h2 := integral_sq_stopped_incr hβ k hμ hvst hμc hvc (fun ω => min_le_right _ _) hN0
    (N := N) (fun _ => hvN)
  have hmρ := memLp_stopped_coord hβ k hρ hρc (N := N) (fun ω => max_le (hN ω) hvN)
  have hmμ := memLp_stopped_coord hβ k hμ hμc (N := N) (fun ω => (min_le_right _ _).trans hvN)
  have hmv := memLp_stopped_coord hβ k hvst hvc (N := N) (fun _ => hvN)
  have hi1 : Integrable (fun ω => (ofNNRealTime β (max (S ω) v) ω k - ofNNRealTime β v ω k) ^ 2) P :=
    (hmρ.sub hmv).integrable_sq
  have hi2 : Integrable (fun ω => (ofNNRealTime β v ω k - ofNNRealTime β (min (S ω) v) ω k) ^ 2) P :=
    (hmv.sub hmμ).integrable_sq
  have hxρ := integrable_max_stopped hβ k hρ hρc (N := N) (fun ω => max_le (hN ω) hvN)
  have hxμ := integrable_max_stopped hβ k hμ hμc (N := N) (fun ω => (min_le_right _ _).trans hvN)
  have hpt : ∀ ω, (ofNNRealTime β (S ω) ω k - ofNNRealTime β v ω k) ^ 2 =
      (ofNNRealTime β (max (S ω) v) ω k - ofNNRealTime β v ω k) ^ 2 +
      (ofNNRealTime β v ω k - ofNNRealTime β (min (S ω) v) ω k) ^ 2 := fun ω => by
    rcases le_total (S ω) v with h | h
    · simp [max_eq_right h, min_eq_left h]; ring
    · simp [max_eq_left h, min_eq_right h]
  simp_rw [hpt]
  rw [integral_add hi1 hi2, h1, h2, ← integral_add (f := fun ω => max (max (S ω) v) 0 - max v 0)
    (g := fun ω => max v 0 - max (min (S ω) v) 0) (hxρ.sub (integrable_const _))
    ((integrable_const _).sub hxμ)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have := hS0 ω
  rcases le_total (S ω) v with h | h
  · simp [max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.2 h), max_eq_left hv,
      max_eq_left this]
  · simp [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.2 h), max_eq_left hv,
      max_eq_left this]

/-- Dyadic truncated approximation of a stopping time. -/
def dyadicTrunc (m : ℕ) (S : Ω → ℝ) : Ω → ℝ :=
  fun ω => min ((⌈(2 : ℝ) ^ m * S ω⌉ : ℝ) / 2 ^ m) m

theorem isStoppingTime_dyadicTrunc {S : Ω → ℝ}
    (hS : IsStoppingTime ℱ fun ω => ((S ω : ℝ) : WithTop ℝ)) (m : ℕ) :
    IsStoppingTime ℱ fun ω => ((dyadicTrunc m S ω : ℝ) : WithTop ℝ) := by
  have h1 := isStoppingTime_dyadicUp ℱ hS m
  have h2 : dyadicUp m (fun ω => ((S ω : ℝ) : WithTop ℝ)) =
      fun ω => (((⌈(2 : ℝ) ^ m * S ω⌉ : ℝ) / 2 ^ m : ℝ) : WithTop ℝ) := by
    funext ω; simp [dyadicUp]
  rw [h2] at h1
  exact isStoppingTime_min_const h1 m

theorem countable_range_dyadicTrunc (m : ℕ) (S : Ω → ℝ) :
    (Set.range (dyadicTrunc m S)).Countable := by
  have : Set.range (dyadicTrunc m S) ⊆ Set.range fun k : ℤ => min ((k : ℝ) / 2 ^ m) m := by
    rintro _ ⟨ω, rfl⟩
    exact ⟨⌈(2 : ℝ) ^ m * S ω⌉, rfl⟩
  exact (Set.countable_range _).mono this

theorem dyadicTrunc_nonneg {S : Ω → ℝ} (hS0 : ∀ ω, 0 ≤ S ω) (m : ℕ) (ω : Ω) :
    0 ≤ dyadicTrunc m S ω := by
  unfold dyadicTrunc
  refine le_min ?_ (Nat.cast_nonneg m)
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  refine div_nonneg ?_ hpos.le
  exact_mod_cast Int.ceil_nonneg (mul_nonneg hpos.le (hS0 ω))

theorem dyadicTrunc_le (S : Ω → ℝ) (m : ℕ) (ω : Ω) : dyadicTrunc m S ω ≤ m := min_le_right _ _

theorem dyadicTrunc_bounds (S : Ω → ℝ) (m : ℕ) (ω : Ω) :
    S ω ≤ (⌈(2 : ℝ) ^ m * S ω⌉ : ℝ) / 2 ^ m ∧
      (⌈(2 : ℝ) ^ m * S ω⌉ : ℝ) / 2 ^ m < S ω + (1 / 2) ^ m := by
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  constructor
  · rw [le_div_iff₀ hpos, mul_comm]; exact Int.le_ceil _
  · rw [div_lt_iff₀ hpos]
    have := Int.ceil_lt_add_one ((2 : ℝ) ^ m * S ω)
    have e : (S ω + (1 / 2) ^ m) * 2 ^ m = 2 ^ m * S ω + 1 := by
      rw [add_mul, one_div, inv_pow, inv_mul_cancel₀ hpos.ne']; ring
    rw [e]; exact this

theorem abs_dyadicTrunc_sub_le (S : Ω → ℝ) (m : ℕ) (ω : Ω) {v : ℝ}
    (hvm : v ≤ m) : |dyadicTrunc m S ω - v| ≤ |S ω - v| + (1 / 2) ^ m := by
  set D : ℝ := (⌈(2 : ℝ) ^ m * S ω⌉ : ℝ) / 2 ^ m with hD
  have hD1 : S ω ≤ D := (dyadicTrunc_bounds S m ω).1
  have hD2 : D < S ω + (1 / 2) ^ m := (dyadicTrunc_bounds S m ω).2
  have hpe : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
  show |min D m - v| ≤ _
  rcases le_total D m with h | h
  · rw [min_eq_left h]
    have : |D - v| ≤ |D - S ω| + |S ω - v| := abs_sub_le _ _ _
    rw [abs_of_nonneg (sub_nonneg.2 hD1)] at this
    linarith
  · rw [min_eq_right h]
    rcases le_total (m : ℝ) (S ω) with h' | h'
    · rw [abs_of_nonneg (sub_nonneg.2 hvm), abs_of_nonneg (sub_nonneg.2 (hvm.trans h'))]
      linarith
    · have : |(m : ℝ) - v| ≤ |(m : ℝ) - S ω| + |S ω - v| := abs_sub_le _ _ _
      rw [abs_of_nonneg (sub_nonneg.2 h')] at this
      linarith

theorem tendsto_dyadicTrunc (S : Ω → ℝ) (ω : Ω) :
    Tendsto (fun m => dyadicTrunc m S ω) atTop (𝓝 (S ω)) := by
  have hD : Tendsto (fun m : ℕ => (⌈(2 : ℝ) ^ m * S ω⌉ : ℝ) / 2 ^ m) atTop (𝓝 (S ω)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun m => (dyadicTrunc_bounds S m ω).1) (fun m => (dyadicTrunc_bounds S m ω).2.le)
    have : Tendsto (fun m : ℕ => S ω + (1 / 2 : ℝ) ^ m) atTop (𝓝 (S ω + 0)) :=
      tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    simpa using this
  refine hD.congr' ?_
  have hev : ∀ᶠ m : ℕ in atTop, S ω + 1 ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hev] with m hm
  have h1 := (dyadicTrunc_bounds S m ω).2
  have h2 : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold dyadicTrunc
  rw [min_eq_left (by linarith)]

theorem brownian_stopped_L2_bound_aux (hβ : IsBrownianFiltration P ℱ β) (k : ι) (S : Ω → ℝ)
    (hS0 : ∀ ω, 0 ≤ S ω) (hS : IsStoppingTime ℱ fun ω => ((S ω : ℝ) : WithTop ℝ))
    (hSint : Integrable S P) (v : ℝ) (hv : 0 ≤ v) :
    ∫⁻ ω, ‖β (Real.toNNReal (S ω)) ω k - β (Real.toNNReal v) ω k‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (∫ ω, |S ω - v| ∂P) := by
  set f : ℕ → Ω → ℝ≥0∞ := fun m ω =>
    ‖ofNNRealTime β (dyadicTrunc m S ω) ω k - ofNNRealTime β v ω k‖ₑ ^ 2 with hf
  have hSv : Integrable (fun ω => |S ω - v|) P := (hSint.sub (integrable_const v)).abs
  set c : ℝ := ∫ ω, |S ω - v| ∂P with hc
  have hmeas : ∀ m, AEMeasurable (f m) P := by
    intro m
    have h1 := memLp_stopped_coord hβ k (isStoppingTime_dyadicTrunc hS m)
      (countable_range_dyadicTrunc m S) (dyadicTrunc_le S m)
    have h2 := hβ.memLp_two_coord_real v k
    have := (h1.sub h2).aestronglyMeasurable.aemeasurable
    exact (this.enorm).pow_const 2
  have hbound : ∀ m : ℕ, v ≤ m → ∫⁻ ω, f m ω ∂P ≤ ENNReal.ofReal (c + (1 / 2) ^ m) := by
    intro m hvm
    have hvm0 : (0 : ℝ) ≤ m := hv.trans hvm
    have h1 := integral_sq_stopped_sub_const hβ k (isStoppingTime_dyadicTrunc hS m)
      (countable_range_dyadicTrunc m S) (dyadicTrunc_nonneg hS0 m) (dyadicTrunc_le S m) hv hvm
    have hi : Integrable (fun ω => (ofNNRealTime β (dyadicTrunc m S ω) ω k -
        ofNNRealTime β v ω k) ^ 2) P :=
      ((memLp_stopped_coord hβ k (isStoppingTime_dyadicTrunc hS m)
        (countable_range_dyadicTrunc m S) (dyadicTrunc_le S m)).sub
        (hβ.memLp_two_coord_real v k)).integrable_sq
    have h2 : ∫⁻ ω, f m ω ∂P = ENNReal.ofReal (∫ ω, |dyadicTrunc m S ω - v| ∂P) := by
      rw [← h1, ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ω => sq_nonneg _)]
      exact lintegral_congr fun ω => enorm_sq_eq_ofReal _
    rw [h2]
    refine ENNReal.ofReal_le_ofReal ?_
    have hint : Integrable (fun ω => |dyadicTrunc m S ω - v|) P := by
      have h3 := integrable_max_stopped hβ k (isStoppingTime_dyadicTrunc hS m)
        (countable_range_dyadicTrunc m S) (dyadicTrunc_le S m)
      have h4 : Integrable (dyadicTrunc m S) P :=
        h3.congr (Eventually.of_forall fun ω => max_eq_left (dyadicTrunc_nonneg hS0 m ω))
      exact (h4.sub (integrable_const v)).abs
    calc ∫ ω, |dyadicTrunc m S ω - v| ∂P ≤ ∫ ω, (|S ω - v| + (1 / 2) ^ m) ∂P :=
          integral_mono hint (hSv.add (integrable_const _))
            (fun ω => abs_dyadicTrunc_sub_le S m ω hvm)
      _ = c + (1 / 2) ^ m := by
          rw [integral_add hSv (integrable_const _)]; simp [hc]
  have hlim : ∀ ω, Tendsto (fun m => f m ω) atTop
      (𝓝 (‖β (Real.toNNReal (S ω)) ω k - β (Real.toNNReal v) ω k‖ₑ ^ 2)) := by
    intro ω
    have hc1 : Continuous fun t : ℝ => ofNNRealTime β t ω k - ofNNRealTime β v ω k :=
      ((continuous_apply k).comp (continuous_ofNNRealTime β ω (hβ.cont ω))).sub continuous_const
    have h3 := ((hc1.tendsto (S ω)).comp (tendsto_dyadicTrunc S ω)).enorm
    exact ((ENNReal.continuous_pow 2).tendsto _).comp h3
  calc ∫⁻ ω, ‖β (Real.toNNReal (S ω)) ω k - β (Real.toNNReal v) ω k‖ₑ ^ 2 ∂P
      = ∫⁻ ω, liminf (fun m => f m ω) atTop ∂P := by
        refine lintegral_congr fun ω => ?_
        exact ((hlim ω).liminf_eq).symm
    _ ≤ liminf (fun m => ∫⁻ ω, f m ω ∂P) atTop := lintegral_liminf_le' hmeas
    _ ≤ liminf (fun m : ℕ => ENNReal.ofReal (c + (1 / 2) ^ m)) atTop := by
        refine liminf_le_liminf ?_
        filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop v] with m hm
        exact hbound m hm
    _ = ENNReal.ofReal c := by
        refine Tendsto.liminf_eq ?_
        have : Tendsto (fun m : ℕ => c + (1 / 2 : ℝ) ^ m) atTop (𝓝 (c + 0)) :=
          tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
        rw [add_zero] at this
        exact (ENNReal.tendsto_ofReal this)

end StoppedL2


/-- `E|β_S - β_v|² ≤ E|S - v|` for a finite integrable stopping time `S ≥ 0` of a Brownian
filtration (one coordinate `k`), `v ≥ 0` deterministic.  The left side is a `lintegral`, so the
statement asserts finiteness of the second moment, matching the `lintegral` form of
`dds_coupling` in `HRS/Prob/CLT.lean` (`docs/SPEC_AUDIT.md` B12). -/
theorem brownian_stopped_L2_bound {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {β : ℝ≥0 → Ω → ι → ℝ} (hβ : IsBrownianFiltration P ℱ β) (k : ι) (S : Ω → ℝ)
    (hS0 : ∀ ω, 0 ≤ S ω) (hS : IsStoppingTime ℱ fun ω => ((S ω : ℝ) : WithTop ℝ))
    (hSint : Integrable S P) (v : ℝ) (hv : 0 ≤ v) :
    ∫⁻ ω, ‖β (Real.toNNReal (S ω)) ω k - β (Real.toNNReal v) ω k‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (∫ ω, |S ω - v| ∂P) :=
  brownian_stopped_L2_bound_aux hβ k S hS0 hS hSint v hv

/-! ### Continuous modifications and optional sampling -/

section Modification

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}

omit [IsProbabilityMeasure P] in
/-- A martingale started at `0` vanishes (a.s.) at negative times. -/
theorem martingale_ae_eq_zero_of_nonpos {M : ℝ → Ω → ℝ} (hM : Martingale M ℱ P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) {s : ℝ} (hs : s ≤ 0) : M s =ᵐ[P] 0 := by
  have h1 := hM.2 s 0 hs
  have h2 : P[M 0 | ℱ s] =ᵐ[P] P[(0 : Ω → ℝ) | ℱ s] := condExp_congr_ae h0
  filter_upwards [h1, h2] with ω h1 h2
  rw [← h1, h2]
  simp

/-- Clamping a martingale at time `t ≥ 0` gives a martingale. -/
theorem martingale_clamp {M : ℝ → Ω → ℝ} (hM : Martingale M ℱ P) {t : ℝ} :
    Martingale (fun s => M (min s t)) ℱ P := by
  refine ⟨fun s => ?_, fun s r hsr => ?_⟩
  · exact (hM.1 (min s t)).mono (ℱ.mono (min_le_left _ _))
  · rcases le_total s t with hst | hts
    · show P[M (min r t) | ℱ s] =ᵐ[P] M (min s t)
      rw [min_eq_left hst]
      exact hM.2 s (min r t) (le_min hsr hst)
    · show P[M (min r t) | ℱ s] =ᵐ[P] M (min s t)
      rw [min_eq_right hts, min_eq_right (hts.trans hsr)]
      exact (condExp_of_stronglyMeasurable (ℱ.le s) ((hM.1 t).mono (ℱ.mono hts))
        (hM.integrable t)).eventuallyEq

end Modification

theorem martingale_stoppedProcess_aux (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (hℱ : IsCompleteFiltration P ℱ) (t : ℝ) (ht : 0 ≤ t) (M : ℝ → Ω → ℝ)
    (hM : IsContSqMartingale P ℱ t M) {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    (hτt : ∀ ω, τ ω ≤ (t : WithTop ℝ)) :
    ∃ M₁ : ℝ → Ω → ℝ, (∀ s, M₁ s =ᵐ[P] M s) ∧ Martingale (stoppedProcess M₁ τ) ℱ P := by
  classical
  obtain ⟨N, hNsub, hNm, hN0⟩ : ∃ N : Set Ω,
      {ω | ¬ (ContinuousOn (fun τ => M τ ω) (Set.Icc 0 t) ∧ M 0 ω = 0)} ⊆ N ∧
        MeasurableSet N ∧ P N = 0 := by
    have h0 : P {ω | ¬ (ContinuousOn (fun τ => M τ ω) (Set.Icc 0 t) ∧ M 0 ω = 0)} = 0 :=
      ae_iff.1 (hM.cont.and hM.zero)
    exact ⟨toMeasurable P _, subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
      by rw [measure_toMeasurable]; exact h0⟩
  have hgood : ∀ ω, ω ∉ N → ContinuousOn (fun τ => M τ ω) (Set.Icc 0 t) ∧ M 0 ω = 0 := by
    intro ω hω
    by_contra h
    exact hω (hNsub h)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]; simpa using hN0
  set Mt : ℝ → Ω → ℝ := fun s ω => if ω ∈ N then 0 else M (min (max s 0) t) ω with hMt
  set M₁ : ℝ → Ω → ℝ := fun s ω => if s ≤ t then Mt s ω else M s ω with hM₁
  have hMt_cont : ∀ ω, Continuous fun s => Mt s ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [hMt, hω, ite_true]; exact continuous_const
    · simp only [hMt, hω, ite_false]
      refine (hgood ω hω).1.comp_continuous (by fun_prop) (fun s => ⟨?_, min_le_right _ _⟩)
      exact le_min (le_max_right _ _) ht
  have hMt_ae : ∀ s, Mt s =ᵐ[P] fun ω => M (min s t) ω := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · filter_upwards [hNae] with ω hω
      simp only [hMt, hω, ite_false, max_eq_left hs]
    · filter_upwards [hNae, martingale_ae_eq_zero_of_nonpos hM.martingale hM.zero hs.le] with ω hω h2
      have h3 : M 0 ω = 0 := (hgood ω hω).2
      simp only [hMt, hω, ite_false, max_eq_right hs.le, min_eq_left ht, min_eq_left (hs.le.trans ht)]
      rw [h3]; simpa using h2.symm
  have hMt_adapt : StronglyAdapted ℱ Mt := by
    have hX : Adapted ℱ (fun s ω => M (min s t) ω) :=
      fun s => ((martingale_clamp hM.martingale (t := t)).1 s).measurable
    have hY : ∀ s, Measurable (Mt s) := fun s =>
      Measurable.ite hNm measurable_const
        (((hM.martingale.1 _).measurable).mono (ℱ.le _) le_rfl)
    exact fun s => (hℱ.adapted_of_ae_eq hX hY (fun s => (hMt_ae s).symm) s).stronglyMeasurable
  have hMt_mart : Martingale Mt ℱ P := martingale_congr_ae (martingale_clamp hM.martingale (t := t)) hMt_adapt hMt_ae
  have hstop := Martingale.stoppedProcess_of_continuous P ℱ Mt hMt_mart hMt_cont hτ
  refine ⟨M₁, fun s => ?_, ?_⟩
  · by_cases hs : s ≤ t
    · simp only [hM₁, hs, ite_true]
      refine (hMt_ae s).trans ?_
      rw [min_eq_left hs]
    · simp only [hM₁, hs, ite_false]; exact Filter.EventuallyEq.rfl
  · convert hstop using 1
    funext s ω
    have hne : τ ω ≠ ⊤ := ((hτt ω).trans_lt (WithTop.coe_lt_top t)).ne
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hne
    have hct : c ≤ t := by
      have := hτt ω
      rw [← hc] at this
      exact_mod_cast this
    rw [stoppedProcess_apply_coe hc.symm, stoppedProcess_apply_coe hc.symm]
    have : min s c ≤ t := (min_le_right _ _).trans hct
    simp only [hM₁, this, ite_true]



theorem isContSqMartingale_max_zero (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (t : ℝ) (M : ℝ → Ω → ℝ) (hM : IsContSqMartingale P ℱ t M) :
    IsContSqMartingale P ℱ (max t 0) M := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht]; exact hM
  · rw [max_eq_right ht.le]
    refine ⟨hM.martingale, hM.zero, ?_, ?_⟩
    · exact Eventually.of_forall fun ω => by
        simp only [Set.Icc_self]; exact continuousOn_singleton _ _
    · intro τ hτ
      have : τ = 0 := le_antisymm hτ.2 hτ.1
      subst this
      exact (memLp_congr_ae (show M 0 =ᵐ[P] 0 from hM.zero)).2 MemLp.zero

/-- Continuous-time optional sampling for the abstract class: the stopped process of an
`IsContSqMartingale` (made everywhere continuous by modification on a null set of a complete
filtration) is a martingale; used in the DDS proof for `M` and `M² - A`. -/
theorem IsContSqMartingale.martingale_stoppedProcess (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (hℱ : IsCompleteFiltration P ℱ) (t : ℝ) (M : ℝ → Ω → ℝ)
    (hM : IsContSqMartingale P ℱ t M) {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    (hτt : ∀ ω, τ ω ≤ (t : WithTop ℝ)) :
    ∃ M₁ : ℝ → Ω → ℝ, (∀ s, M₁ s =ᵐ[P] M s) ∧ Martingale (stoppedProcess M₁ τ) ℱ P :=
  martingale_stoppedProcess_aux P ℱ hℱ (max t 0) (le_max_right _ _) M
    (isContSqMartingale_max_zero P ℱ t M hM) hτ (fun ω => (hτt ω).trans (by exact_mod_cast le_max_left _ _))

end HRS
