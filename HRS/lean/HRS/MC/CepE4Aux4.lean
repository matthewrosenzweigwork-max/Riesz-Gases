import HRS.MC.CepE4Aux3

/-!
# Packet CEPE4, auxiliary 4: integrability on `(0,t] × Ω` for the solution paths

The setup `E4Setup`: noise `w` (an `E4Noise`), a continuous adapted path `Z`, and an `L²` random variable `A` with
`‖Z_s‖ ≤ A + |σ'| ‖w_s‖` on `[0,T]` (a.s.).  Every continuous function of `Z_s` of quadratic growth is then integrable
on the product `(0,t] × Ω` (`t ≤ T`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE4

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- The setup. -/
structure E4Setup (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (N : ℕ) (T σ' : ℝ) (w Z : ℝ → Ω → Ch N)
    (A : Ω → ℝ) : Prop where
  hw : E4Noise P ℱ N w
  Zc : ∀ ω, Continuous fun t => Z t ω
  Zm : ∀ t, Measurable (Z t)
  ZF : ∀ t, 0 ≤ t → Measurable[ℱ t] (Z t)
  hA : MemLp A 2 P
  hAb : ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ‖Z s ω‖ ≤ A ω + |σ'| * ‖w s ω‖

/-- The time measure. -/
abbrev e4_mu (t : ℝ) : Measure ℝ := (volume : Measure ℝ).restrict (Ioc 0 t)

theorem e4_Z_joint {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N} {A : Ω → ℝ}
    (h : E4Setup P ℱ N T σ' w Z A) : Measurable fun p : ℝ × Ω => Z p.1 p.2 :=
  measurable_uncurry_of_continuous_of_measurable h.Zc h.Zm

theorem e4_w_joint {ℱ : Filtration ℝ mΩ} {w : ℝ → Ω → Ch N} (h : E4Noise P ℱ N w) :
    Measurable fun p : ℝ × Ω => w p.1 p.2 :=
  measurable_uncurry_of_continuous_of_measurable h.cont h.meas

/-- Integrability of `‖w_s ω‖²` on the product. -/
theorem e4_wsq_integrable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {w : ℝ → Ω → Ch N}
    (h : E4Noise P ℱ N w) (t : ℝ) :
    Integrable (fun p : ℝ × Ω => ‖w p.1 p.2‖ ^ 2) ((e4_mu t).prod P) := by
  have hm : Measurable fun p : ℝ × Ω => ‖w p.1 p.2‖ ^ 2 := (e4_w_joint h).norm.pow_const 2
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun s => (h.memLp s).integrable_sq, ?_⟩
  have hc : Integrable (fun s : ℝ => (N : ℝ) * s) (e4_mu t) :=
    (continuous_const.mul continuous_id).integrableOn_Ioc
  refine hc.congr ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => hs.1)] with s hs
  have hs' : 0 ≤ s := hs.le
  have := h.sq s hs'
  simp only [norm_pow, norm_norm]
  exact this.symm

/-- The dominating function. -/
def e4_D (A : Ω → ℝ) (w : ℝ → Ω → Ch N) (t : ℝ) (p : ℝ × Ω) : ℝ :=
  1 + A p.2 ^ 2 + ‖w p.1 p.2‖ ^ 2 + ‖w t p.2‖ ^ 2

theorem e4_D_integrable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {w : ℝ → Ω → Ch N}
    (h : E4Noise P ℱ N w) {A : Ω → ℝ} (hA : MemLp A 2 P) (t : ℝ) :
    Integrable (e4_D A w t) ((e4_mu t).prod P) := by
  unfold e4_D
  refine (((integrable_const (1 : ℝ)).add ?_).add (e4_wsq_integrable h t)).add ?_
  · exact hA.integrable_sq.comp_snd (e4_mu t)
  · exact ((h.memLp t).integrable_sq).comp_snd (e4_mu t)

theorem e4_integrable_dom [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {w : ℝ → Ω → Ch N}
    (h : E4Noise P ℱ N w) {A : Ω → ℝ} (hA : MemLp A 2 P) {t : ℝ} {f : ℝ × Ω → ℝ}
    (hf : AEStronglyMeasurable f ((e4_mu t).prod P)) {c : ℝ}
    (hdom : ∀ᵐ ω ∂P, ∀ s ∈ Ioc 0 t, |f (s, ω)| ≤ c * e4_D A w t (s, ω)) :
    Integrable f ((e4_mu t).prod P) := by
  refine ((e4_D_integrable h hA t).const_mul c).mono' hf ?_
  have h1 : ∀ᵐ p ∂((e4_mu t).prod P), p.1 ∈ Ioc 0 t :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  have h2 : ∀ᵐ p ∂((e4_mu t).prod P), ∀ s ∈ Ioc 0 t, |f (s, p.2)| ≤ c * e4_D A w t (s, p.2) :=
    Measure.quasiMeasurePreserving_snd.ae hdom
  filter_upwards [h1, h2] with p hp1 hp2
  have := hp2 p.1 hp1
  simpa [Real.norm_eq_abs, e4_D] using this

theorem e4_Zsq_le {A a w : ℝ} {σ' : ℝ} (h : a ≤ A + |σ'| * w) (ha : 0 ≤ a) (hw : 0 ≤ w) :
    a ^ 2 ≤ 2 * A ^ 2 + 2 * σ' ^ 2 * w ^ 2 := by
  have h1 : a ^ 2 ≤ (A + |σ'| * w) ^ 2 := pow_le_pow_left₀ ha h 2
  have h2 : (A + |σ'| * w) ^ 2 ≤ 2 * A ^ 2 + 2 * (|σ'| * w) ^ 2 := by nlinarith [sq_nonneg (A - |σ'| * w)]
  have h3 : (|σ'| * w) ^ 2 = σ' ^ 2 * w ^ 2 := by rw [mul_pow, sq_abs]
  nlinarith

theorem e4_g_integrable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N}
    {A : Ω → ℝ} (S : E4Setup P ℱ N T σ' w Z A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {g : Ch N → ℝ}
    (hg : Continuous g) {c0 c1 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hgb : ∀ z, |g z| ≤ c0 + c1 * ‖z‖ ^ 2) :
    Integrable (fun p : ℝ × Ω => g (Z p.1 p.2)) ((e4_mu t).prod P) := by
  refine e4_integrable_dom S.hw S.hA (hg.measurable.comp (e4_Z_joint S)).aestronglyMeasurable
    (c := c0 + 2 * c1 * (1 + σ' ^ 2)) ?_
  filter_upwards [S.hAb] with ω hω s hs
  have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans htT⟩
  have h1 := hω s hs'
  have h2 := e4_Zsq_le h1 (norm_nonneg _) (norm_nonneg _)
  have h3 := (hgb (Z s ω))
  simp only [e4_D]
  have hw1 := sq_nonneg ‖w s ω‖
  have hw2 := sq_nonneg ‖w t ω‖
  have hA2 := sq_nonneg (A ω)
  have hσ := sq_nonneg σ'
  nlinarith [mul_nonneg hc1 hw1, mul_nonneg hc1 hw2, mul_nonneg hc1 hA2, mul_nonneg (mul_nonneg hc1 hσ) hw1,
    mul_nonneg hc1 hA2, mul_nonneg hc1 hw1]

theorem e4_quad_le_J {β0 Lb σ' u x y Zn : ℝ} (hβ0 : 0 ≤ β0) (hLb : 0 ≤ Lb) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hZ : 0 ≤ Zn) (hZsq : Zn ^ 2 ≤ 2 * u ^ 2 + 2 * σ' ^ 2 * x ^ 2) :
    (β0 + Lb * Zn) * (x + y) ≤ (β0 + Lb * (1 + σ' ^ 2) * 2) * (1 + u ^ 2 + x ^ 2 + y ^ 2) := by
  have h1 : β0 * (x + y) ≤ β0 * (1 + u ^ 2 + x ^ 2 + y ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hβ0
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg u]
  have h2 : Zn * (x + y) ≤ (1 + σ' ^ 2) * 2 * (1 + u ^ 2 + x ^ 2 + y ^ 2) := by
    have hσ := sq_nonneg σ'
    have e1 : Zn * (x + y) ≤ (Zn ^ 2 + (x + y) ^ 2) / 2 := by nlinarith [sq_nonneg (Zn - (x + y))]
    have e2 : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - y)]
    have e3 : 0 ≤ u ^ 2 := sq_nonneg u
    have e4 : 0 ≤ σ' ^ 2 * x ^ 2 := by positivity
    nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg hσ (sq_nonneg x), mul_nonneg hσ (sq_nonneg y),
      mul_nonneg hσ e3]
  have h3 : Lb * (Zn * (x + y)) ≤ Lb * ((1 + σ' ^ 2) * 2 * (1 + u ^ 2 + x ^ 2 + y ^ 2)) :=
    mul_le_mul_of_nonneg_left h2 hLb
  nlinarith

/-- Linear growth bound gives an `L²` bound along the path. -/
theorem e4_Bf_memLp [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N}
    {A : Ω → ℝ} (S : E4Setup P ℱ N T σ' w Z A) {Bf : Ch N → Ch N} (hBc : Continuous Bf) {β0 Lb : ℝ}
    (hβ0 : 0 ≤ β0) (hLb : 0 ≤ Lb) (hBb : ∀ z, ‖Bf z‖ ≤ β0 + Lb * ‖z‖) {s : ℝ} (hs : s ∈ Icc 0 T) :
    MemLp (fun ω => ‖Bf (Z s ω)‖) 2 P := by
  have hmajor : MemLp (fun ω => β0 + Lb * (A ω + |σ'| * ‖w s ω‖)) 2 P := by
    have h1 : MemLp (fun _ : Ω => β0) 2 P := memLp_const _
    have h2 : MemLp (fun ω => A ω + |σ'| * ‖w s ω‖) 2 P := S.hA.add ((S.hw.memLp s).const_mul _)
    exact h1.add (h2.const_mul Lb)
  refine hmajor.mono ?_ ?_
  · exact ((hBc.measurable.comp (S.Zm s)).norm).aestronglyMeasurable
  · filter_upwards [S.hAb] with ω hω
    have := hω s hs
    have h3 := hBb (Z s ω)
    have h4 : Lb * ‖Z s ω‖ ≤ Lb * (A ω + |σ'| * ‖w s ω‖) := mul_le_mul_of_nonneg_left this hLb
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (by linarith : ‖Bf (Z s ω)‖ ≤ β0 + Lb * (A ω + |σ'| * ‖w s ω‖)).trans (le_abs_self _)

theorem e4_J_integrable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N}
    {A : Ω → ℝ} (S : E4Setup P ℱ N T σ' w Z A) {Bf : Ch N → Ch N} (hBc : Continuous Bf) {β0 Lb : ℝ}
    (hβ0 : 0 ≤ β0) (hLb : 0 ≤ Lb) (hBb : ∀ z, ‖Bf z‖ ≤ β0 + Lb * ‖z‖) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) :
    Integrable (fun p : ℝ × Ω => inner ℝ (Bf (Z p.1 p.2)) (w t p.2 - w p.1 p.2)) ((e4_mu t).prod P) := by
  have hmeas : Measurable fun p : ℝ × Ω => inner ℝ (Bf (Z p.1 p.2)) (w t p.2 - w p.1 p.2) := by
    refine Measurable.inner (hBc.measurable.comp (e4_Z_joint S)) ?_
    exact ((S.hw.meas t).comp measurable_snd).sub (e4_w_joint S.hw)
  refine e4_integrable_dom S.hw S.hA hmeas.aestronglyMeasurable (c := β0 + Lb * (1 + σ' ^ 2) * 2) ?_
  filter_upwards [S.hAb] with ω hω s hs
  have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans htT⟩
  have h1 := hω s hs'
  have h2 := e4_Zsq_le h1 (norm_nonneg _) (norm_nonneg _)
  have h3 : |inner ℝ (Bf (Z s ω)) (w t ω - w s ω)| ≤ ‖Bf (Z s ω)‖ * ‖w t ω - w s ω‖ := abs_real_inner_le_norm _ _
  have h4 : ‖w t ω - w s ω‖ ≤ ‖w s ω‖ + ‖w t ω‖ := by
    have := norm_sub_le (w t ω) (w s ω); linarith
  have h5 := hBb (Z s ω)
  have h6 : ‖Bf (Z s ω)‖ * ‖w t ω - w s ω‖ ≤ (β0 + Lb * ‖Z s ω‖) * (‖w s ω‖ + ‖w t ω‖) :=
    mul_le_mul h5 h4 (norm_nonneg _) (by positivity)
  have h7 := e4_quad_le_J (β0 := β0) (Lb := Lb) (σ' := σ') (u := A ω) hβ0 hLb (norm_nonneg (w s ω))
    (norm_nonneg (w t ω)) (norm_nonneg (Z s ω)) h2
  simp only [e4_D]
  calc |inner ℝ (Bf (Z s ω)) (w t ω - w s ω)| ≤ _ := h3
    _ ≤ _ := h6
    _ ≤ _ := h7

theorem e4_J_zero [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N}
    {A : Ω → ℝ} (S : E4Setup P ℱ N T σ' w Z A) {Bf : Ch N → Ch N} (hBc : Continuous Bf) {β0 Lb : ℝ}
    (hβ0 : 0 ≤ β0) (hLb : 0 ≤ Lb) (hBb : ∀ z, ‖Bf z‖ ≤ β0 + Lb * ‖z‖) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) :
    ∫ ω, (∫ s in (0 : ℝ)..t, inner ℝ (Bf (Z s ω)) (w t ω - w s ω)) ∂P = 0 := by
  have hint := e4_J_integrable S hBc hβ0 hLb hBb ht0 htT
  simp_rw [intervalIntegral.integral_of_le ht0]
  have hswap := integral_integral_swap (μ := e4_mu t) (ν := P)
    (f := fun s ω => inner ℝ (Bf (Z s ω)) (w t ω - w s ω)) hint
  have hs0 : ∀ s ∈ Ioc (0 : ℝ) t, ∫ ω, inner ℝ (Bf (Z s ω)) (w t ω - w s ω) ∂P = 0 := by
    intro s hs
    refine S.hw.incr s t hs.1.le hs.2 (fun ω => Bf (Z s ω)) ?_ ?_
    · exact hBc.measurable.comp (S.ZF s hs.1.le)
    · exact e4_Bf_memLp S hBc hβ0 hLb hBb ⟨hs.1.le, hs.2.trans htT⟩
  rw [← hswap]
  refine (setIntegral_congr_fun measurableSet_Ioc hs0).trans ?_
  simp

theorem e4_inner_cont {Bf : Ch N → Ch N} (hBc : Continuous Bf) (ρ : Ch N) :
    Continuous fun z : Ch N => inner ℝ (z - ρ) (Bf z) :=
  (continuous_id.sub continuous_const).inner hBc

theorem e4_inner_bound {Bf : Ch N → Ch N} {β0 Lb : ℝ} (hβ0 : 0 ≤ β0) (hLb : 0 ≤ Lb)
    (hBb : ∀ z, ‖Bf z‖ ≤ β0 + Lb * ‖z‖) (ρ z : Ch N) :
    |inner ℝ (z - ρ) (Bf z)| ≤ (β0 * (1 + ‖ρ‖ ^ 2) + Lb * ‖ρ‖ ^ 2 + Lb) + (β0 + Lb * (1 + ‖ρ‖ ^ 2) + Lb) * ‖z‖ ^ 2 := by
  have h1 := abs_real_inner_le_norm (z - ρ) (Bf z)
  have h2 : ‖z - ρ‖ ≤ ‖z‖ + ‖ρ‖ := norm_sub_le _ _
  have h3 := hBb z
  have h4 : ‖z - ρ‖ * ‖Bf z‖ ≤ (‖z‖ + ‖ρ‖) * (β0 + Lb * ‖z‖) :=
    mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
  have hz := norm_nonneg z
  have hr := norm_nonneg ρ
  nlinarith [sq_nonneg (‖z‖ - 1), sq_nonneg (‖z‖ - ‖ρ‖), sq_nonneg (‖ρ‖ - 1), mul_nonneg hLb hz, mul_nonneg hLb hr,
    mul_nonneg hβ0 hz, mul_nonneg hβ0 hr, mul_nonneg hLb (sq_nonneg (‖z‖ - ‖ρ‖)), mul_nonneg hβ0 (sq_nonneg (‖z‖ - 1)),
    mul_nonneg hLb (sq_nonneg (‖z‖ - 1)), mul_nonneg hLb (sq_nonneg (‖ρ‖ - 1))]

/-- **Second-moment identity** (the expectation of Itô's formula for `½|Z - ρ|²`, by elementary means). -/
theorem e4_second_moment [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N}
    {A : Ω → ℝ} (S : E4Setup P ℱ N T σ' w Z A) {z0 : Ω → Ch N} (hz0 : Measurable[ℱ 0] z0) {R : ℝ}
    (hR : ∀ ω, ‖z0 ω‖ ≤ R) (ρ : Ch N) {Bf : Ch N → Ch N} (hBc : Continuous Bf) {β0 Lb : ℝ}
    (hβ0 : 0 ≤ β0) (hLb : 0 ≤ Lb) (hBb : ∀ z, ‖Bf z‖ ≤ β0 + Lb * ‖z‖)
    (heq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Z t ω = z0 ω + (∫ s in (0 : ℝ)..t, Bf (Z s ω)) + σ' • w t ω)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Integrable (fun ω => ‖Z t ω - ρ‖ ^ 2) P ∧
    ∫ ω, (1 / 2) * ‖Z t ω - ρ‖ ^ 2 ∂P =
      ∫ ω, (1 / 2) * ‖z0 ω - ρ‖ ^ 2 ∂P +
        (∫ ω, (∫ s in (0 : ℝ)..t, inner ℝ (Z s ω - ρ) (Bf (Z s ω))) ∂P) +
        (1 / 2) * σ' ^ 2 * (N * t) := by
  have hz0m : Measurable (z0) := hz0.mono (ℱ.le 0) le_rfl
  -- the five terms
  set T1 : Ω → ℝ := fun ω => (1 / 2) * ‖z0 ω - ρ‖ ^ 2 with hT1
  set T2 : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..t, inner ℝ (Z s ω - ρ) (Bf (Z s ω)) with hT2
  set T3 : Ω → ℝ := fun ω => (1 / 2) * σ' ^ 2 * ‖w t ω‖ ^ 2 with hT3
  set T4 : Ω → ℝ := fun ω => σ' * inner ℝ (z0 ω - ρ) (w t ω) with hT4
  set T5 : Ω → ℝ := fun ω => σ' * ∫ s in (0 : ℝ)..t, inner ℝ (Bf (Z s ω)) (w t ω - w s ω) with hT5
  have hz0L : MemLp (fun ω => ‖z0 ω - ρ‖) 2 P := by
    refine MemLp.of_bound ((hz0m.sub_const ρ).norm).aestronglyMeasurable (R + ‖ρ‖) ?_
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (by linarith [hR ω])
  have hi1 : Integrable T1 P := (hz0L.integrable_sq.const_mul (1 / 2)).congr (Filter.Eventually.of_forall fun ω => by simp [hT1])
  have hi3 : Integrable T3 P := ((S.hw.memLp t).integrable_sq).const_mul ((1 / 2) * σ' ^ 2)
  have hi4 : Integrable T4 P := by
    refine (((hz0L.integrable_mul (S.hw.memLp t))).const_mul |σ'|).mono' ?_ ?_
    · exact ((hz0m.sub_const ρ).inner (S.hw.meas t)).const_mul σ' |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        simp only [hT4, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
  -- T2, T5 integrable via the product
  have hg2 : Integrable (fun p : ℝ × Ω => inner ℝ (Z p.1 p.2 - ρ) (Bf (Z p.1 p.2))) ((e4_mu t).prod P) :=
    e4_g_integrable S ht0 htT (e4_inner_cont hBc ρ)
      (c0 := β0 * (1 + ‖ρ‖ ^ 2) + Lb * ‖ρ‖ ^ 2 + Lb) (c1 := β0 + Lb * (1 + ‖ρ‖ ^ 2) + Lb)
      (by positivity) (by positivity) (e4_inner_bound hβ0 hLb hBb ρ)
  have hi2 : Integrable T2 P := by
    have := hg2.integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hT2]
    rw [intervalIntegral.integral_of_le ht0]
  have hJ := e4_J_integrable S hBc hβ0 hLb hBb ht0 htT
  have hi5 : Integrable T5 P := by
    have := hJ.integral_prod_right.const_mul σ'
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hT5]
    rw [intervalIntegral.integral_of_le ht0]
  -- pathwise identity
  have hpath : ∀ᵐ ω ∂P, (1 / 2) * ‖Z t ω - ρ‖ ^ 2 = T1 ω + T2 ω + T3 ω + T4 ω + T5 ω := by
    filter_upwards [heq] with ω hω
    have hb : Continuous fun s => Bf (Z s ω) := hBc.comp (S.Zc ω)
    have hwc : Continuous fun s => w s ω := S.hw.cont ω
    have := e4_path_ident (fun s => Bf (Z s ω)) (fun s => w s ω) hb hwc (z0 ω) ρ σ' t
    have hZt := hω t ht0
    have hint : (∫ s in (0 : ℝ)..t, inner ℝ ((z0 ω + ∫ r in (0 : ℝ)..s, Bf (Z r ω)) + σ' • w s ω - ρ)
        (Bf (Z s ω))) = T2 ω := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le ht0] at hs
      rw [← hω s hs.1]
    rw [hint] at this
    rw [hZt]
    simp only [hT1, hT3, hT4, hT5]
    rw [this]
  refine ⟨?_, ?_⟩
  · -- integrability of `‖Z_t - ρ‖²`
    have hi : Integrable (fun ω => (1 / 2) * ‖Z t ω - ρ‖ ^ 2) P :=
      (((((hi1.add hi2).add hi3).add hi4).add hi5)).congr (hpath.mono fun ω h => h.symm)
    have := hi.const_mul 2
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    ring
  · have hi : Integrable (fun ω => (1 / 2) * ‖Z t ω - ρ‖ ^ 2) P :=
      (((((hi1.add hi2).add hi3).add hi4).add hi5)).congr (hpath.mono fun ω h => h.symm)
    rw [integral_congr_ae hpath]
    have hA2 : Integrable (fun ω => T1 ω + T2 ω) P := hi1.add hi2
    have hA3 : Integrable (fun ω => T1 ω + T2 ω + T3 ω) P := hA2.add hi3
    have hA4 : Integrable (fun ω => T1 ω + T2 ω + T3 ω + T4 ω) P := hA3.add hi4
    rw [integral_add hA4 hi5, integral_add hA3 hi4, integral_add hA2 hi3, integral_add hi1 hi2]
    -- the means of `T4` and `T5`
    have h4 : ∫ ω, T4 ω ∂P = 0 := by
      have := S.hw.incr 0 t le_rfl ht0 (fun ω => z0 ω - ρ) (hz0.sub_const ρ) hz0L
      simp only [hT4]
      rw [integral_const_mul]
      have e : (fun ω => inner ℝ (z0 ω - ρ) (w t ω - w 0 ω)) = fun ω => inner ℝ (z0 ω - ρ) (w t ω) := by
        funext ω; rw [S.hw.zero ω, sub_zero]
      rw [e] at this
      rw [this, mul_zero]
    have h5 : ∫ ω, T5 ω ∂P = 0 := by
      simp only [hT5]
      rw [integral_const_mul, e4_J_zero S hBc hβ0 hLb hBb ht0 htT, mul_zero]
    have h3 : ∫ ω, T3 ω ∂P = (1 / 2) * σ' ^ 2 * (N * t) := by
      simp only [hT3]
      rw [integral_const_mul, S.hw.sq t ht0]
    rw [h4, h5, h3]
    simp only [hT1, hT2]
    ring

end HRS.MC.CepE4
