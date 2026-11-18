import Mathlib
import HRS.MS.PoisLipAux2

open Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace NNReal

/-!
# POIS-LIPDEC (part 3): Lipschitz decay of the semigroup

Main theorem `HRS.MS.PoisLip.pois_lipdecay`.  Let `q > 0`, `HasCbBound m Mb B` (`2 ≤ m`), `IsBrownianFiltration`,
and `g ∈ C²` with `‖g‖ ≤ M0`, `‖Dg‖ ≤ M1`, `‖D²g‖ ≤ M2`.  Then for `t ≥ 0`
`|P_t g(x) - P_t g(y)| ≤ κ⁻¹ e^{-c0 t} M1 |x - y|`,
with `κ = pm_kappa q Mb`, `c0 = pm_c0 q Mb` the constants of `pm_ffun` (PoisMaxAux2).

Proof: doubling of variables.  With `f` from `pm_ffun` and `A = M1/κ`, `G(t,x,y) = P_t g(x) - P_t g(y)
- A e^{-c0 t} f(|x-y|)` on `[0,T] × (ℝ^d × ℝ^d)` (with the Euclidean product norm, so that the penalty
`ε(1+|x|²+|y|²)e^{λt}` is smooth) satisfies `G(0,·) ≤ 0` (`f(r) ≥ κ r`), is bounded above, is `C¹` in time with
`∂_t P_t g = L P_t g` (`ld_L_commute`), and at a positive penalised maximum the differential inequality
fails (`ld_step` together with `4f'' + c f' ≤ -c0 f`).  `pm_penalized_max` gives `G ≤ 0`; then `f(r) ≤ r`.

Statement adjustments relative to the packet sketch (documented, harmless):
* `Lip g` is replaced by any bound `M1 ≥ ‖Dg‖` (for `g ∈ C¹` they coincide for the best `M1`);
* `g` is assumed bounded (`‖g‖ ≤ M0`), which is what `sg_contDiff`, the Markov property and the
  commutation `P_t L = L P_t` need; the downstream use (`pois_centered_decay`, the resolvent `∫ P_t r dt`)
  has `r` bounded.  The bound `M0` does not enter the conclusion;
* the constants `κ, c0` are those of `pm_ffun` (`pm_kappa`, `pm_c0`), not the sketch's `exp(-(Kc+1)R²/8)`;
* `pois_centered_decay` takes the invariance fact as the hypothesis `hinv : ∫ P_t r dμ = ∫ r dμ` (to be
  supplied by the invariance packet) together with `∫ r dμ = 0`, `μ` a probability measure with
  `Integrable |y|²` and `∫ |y|² dμ ≤ m2`; `Lip r` is a bound `M1 ≥ ‖Dr‖`, `‖r‖∞` a bound `M0`;
* `pois_logbound` is stated for `a > 0`, `A ≥ 0`, `c0 > 0` with `log⁺ = Real.posLog`, and also asserts
  integrability of the integrand on `(0,∞)` (so that the Bochner integral is not a junk value);
* `d = 1` needs no separate treatment (the orthonormal basis extension of `{e}` is uniform in `d ≥ 1`);
  `d = 0` is trivial.
-/

namespace HRS.MS.PoisLip

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisMax

universe u

variable {d : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

theorem ld_sg_bound [IsProbabilityMeasure P] {q : ℝ} {B : Euc d → Euc d} {h : Euc d → ℝ} {M0 : ℝ}
    (hM0 : ∀ y, ‖h y‖ ≤ M0) (t : ℝ) (x : Euc d) : ‖sg P W q B t h x‖ ≤ M0 := by
  unfold sg
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun ω => h (flowMap q B (fun s => W s ω) t x)) (C := M0)
    (Filter.Eventually.of_forall fun ω => hM0 _)
  simpa using this

theorem ld_lip_of_fderiv {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) {M1 : ℝ}
    (hM1 : ∀ y, ‖fderiv ℝ g y‖ ≤ M1) (x y : Euc d) : |g x - g y| ≤ M1 * ‖x - y‖ := by
  have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := g) (C := M1) (fun z _ => (hg.differentiable (by norm_num)) z) (fun z _ => hM1 z)
    (mem_univ y) (mem_univ x)
  rwa [Real.norm_eq_abs] at this

set_option maxHeartbeats 1600000 in
/-- **POIS-LIPDEC, Lipschitz decay.** -/
theorem pois_lipdecay {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) {M0 M1 M2 : ℝ} (hM0 : ∀ y, ‖g y‖ ≤ M0)
    (hM1 : ∀ y, ‖fderiv ℝ g y‖ ≤ M1) (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 g y‖ ≤ M2)
    {t : ℝ} (ht : 0 ≤ t) (x y : Euc d) :
    |sg P W q B t g x - sg P W q B t g y| ≤
      (pm_kappa q Mb)⁻¹ * Real.exp (-(pm_c0 q Mb) * t) * M1 * ‖x - y‖ := by
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero, norm_zero, mul_zero]
    exact le_rfl
  have hM1nn : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (by simpa using hB.2 0 (Nat.zero_le _) 0)
  have hm1 : 1 ≤ m := by omega
  have hn := sgNoise_of_brownian hW
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      exact absurd (Subsingleton.elim x y) hxy
    · exact h0
  obtain ⟨f, hfc, hf0, hfd, hfb, hfine⟩ := pm_ffun hq hMb
  have hκ : 0 < pm_kappa q Mb := Real.exp_pos _
  have hc0 : 0 < pm_c0 q Mb := by
    unfold pm_c0
    exact mul_pos hκ (lt_min one_pos (by linarith))
  set κ : ℝ := pm_kappa q Mb with hκdef
  set c0 : ℝ := pm_c0 q Mb with hc0def
  set A : ℝ := M1 / κ with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hAκ : A * κ = M1 := by rw [hAdef]; field_simp
  set T : ℝ := t + 1 with hTdef
  have hT : 0 < T := by rw [hTdef]; linarith
  have htT : t ∈ Icc (0:ℝ) T := ⟨ht, by rw [hTdef]; linarith⟩
  set M : ℝ := max (max M0 M1) M2 with hMdef
  have hMi : ∀ i ≤ 2, ∀ z, ‖iteratedFDeriv ℝ i g z‖ ≤ M := by
    intro i hi z
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]; exact (hM0 z).trans ((le_max_left _ _).trans (le_max_left _ _))
    · rw [norm_iteratedFDeriv_one]; exact (hM1 z).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hM2 z).trans (le_max_right _ _)
  obtain ⟨C, hC1, hC⟩ := sg_contDiff (d := d) q Mb hq m hm T hT.le 2 hm
  have hu : ∀ s ∈ Icc (0:ℝ) T, ContDiff ℝ 2 (sg P W q B s g) := fun s hs => by
    have := (hC P W hn B hB g (by exact_mod_cast hg) M hMi s hs).1
    exact_mod_cast this
  have hK := pois_kolmogorov hq hm hB hW hg hM1 hM2
  have hC12 : IsC12On T Set.univ (fun s z => sg P W q B s g z) := hK.2.2.2 T hT
  have hderiv : ∀ (z : Euc d) (s : ℝ), 0 ≤ s → HasDerivWithinAt (fun r => sg P W q B r g z)
      (sg P W q B s (kolmL q B g) z) (Ici 0) s := hK.2.1
  have hfcont : Continuous f := hfc.continuous
  -- the doubled function
  set G : ℝ → WithLp 2 (Euc d × Euc d) → ℝ := fun s z =>
    sg P W q B s g z.fst - sg P W q B s g z.snd - A * Real.exp (-c0 * s) * f ‖z.fst - z.snd‖ with hG
  set Gt : ℝ → WithLp 2 (Euc d × Euc d) → ℝ := fun s z =>
    sg P W q B s (kolmL q B g) z.fst - sg P W q B s (kolmL q B g) z.snd +
      c0 * (A * Real.exp (-c0 * s) * f ‖z.fst - z.snd‖) with hGt
  have hcont : ContinuousOn (fun p : ℝ × WithLp 2 (Euc d × Euc d) => G p.1 p.2)
      (Icc 0 T ×ˢ univ) := by
    have h1 : ContinuousOn (fun p : ℝ × WithLp 2 (Euc d × Euc d) =>
        sg P W q B p.1 g p.2.fst) (Icc 0 T ×ˢ univ) := by
      have hmp : Set.MapsTo (fun p : ℝ × WithLp 2 (Euc d × Euc d) => (p.1, p.2.fst))
          (Icc 0 T ×ˢ univ) (Icc 0 T ×ˢ univ) := fun p hp => ⟨hp.1, mem_univ _⟩
      exact ContinuousOn.comp (g := Function.uncurry fun s z => sg P W q B s g z) hC12.cont
        (by fun_prop : Continuous fun p : ℝ × WithLp 2 (Euc d × Euc d) => (p.1, p.2.fst)).continuousOn hmp
    have h2 : ContinuousOn (fun p : ℝ × WithLp 2 (Euc d × Euc d) =>
        sg P W q B p.1 g p.2.snd) (Icc 0 T ×ˢ univ) := by
      have hmp : Set.MapsTo (fun p : ℝ × WithLp 2 (Euc d × Euc d) => (p.1, p.2.snd))
          (Icc 0 T ×ˢ univ) (Icc 0 T ×ˢ univ) := fun p hp => ⟨hp.1, mem_univ _⟩
      exact ContinuousOn.comp (g := Function.uncurry fun s z => sg P W q B s g z) hC12.cont
        (by fun_prop : Continuous fun p : ℝ × WithLp 2 (Euc d × Euc d) => (p.1, p.2.snd)).continuousOn hmp
    have h3 : Continuous (fun p : ℝ × WithLp 2 (Euc d × Euc d) =>
        A * Real.exp (-c0 * p.1) * f ‖p.2.fst - p.2.snd‖) := by fun_prop
    exact (h1.sub h2).sub h3.continuousOn
  have hf2 : ContDiffOn ℝ 2 f (Set.Ioi 0) :=
    (by exact_mod_cast (contDiff_infty.1 hfc) 2 : ContDiff ℝ 2 f).contDiffOn
  have hfnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ f r := fun r hr =>
    le_trans (mul_nonneg hκ.le hr) (hfb r hr).1
  have hder : ∀ s ∈ Icc (0:ℝ) T, ∀ z : WithLp 2 (Euc d × Euc d),
      HasDerivWithinAt (fun r => G r z) (Gt s z) (Icc 0 T) s := by
    intro s hs z
    have h1 := (hderiv z.fst s hs.1).mono (fun r (hr : r ∈ Icc (0:ℝ) T) => (hr.1 : r ∈ Ici (0:ℝ)))
    have h2 := (hderiv z.snd s hs.1).mono (fun r (hr : r ∈ Icc (0:ℝ) T) => (hr.1 : r ∈ Ici (0:ℝ)))
    have h4 : HasDerivAt (fun r : ℝ => -c0 * r) (-c0) s := by
      simpa using (hasDerivAt_id s).const_mul (-c0)
    have h3 : HasDerivAt (fun r : ℝ => A * Real.exp (-c0 * r) * f ‖z.fst - z.snd‖)
        (A * (Real.exp (-c0 * s) * (-c0)) * f ‖z.fst - z.snd‖) s :=
      ((h4.exp).const_mul A).mul_const _
    refine ((h1.sub h2).sub h3.hasDerivWithinAt).congr_deriv ?_
    simp only [hGt]
    ring
  have h0 : ∀ z : WithLp 2 (Euc d × Euc d), G 0 z ≤ 0 := by
    intro z
    simp only [hG, ld_sg_zero hn hq.le hm1 hB, mul_zero, Real.exp_zero, mul_one]
    have h1 := ld_lip_of_fderiv hg hM1 z.fst z.snd
    have h2 := (hfb ‖z.fst - z.snd‖ (norm_nonneg _)).1
    have h3 : A * (κ * ‖z.fst - z.snd‖) ≤ A * f ‖z.fst - z.snd‖ :=
      mul_le_mul_of_nonneg_left h2 hA0
    have h4 : A * (κ * ‖z.fst - z.snd‖) = M1 * ‖z.fst - z.snd‖ := by rw [← hAκ]; ring
    have h5 := le_abs_self (g z.fst - g z.snd)
    linarith
  have hgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ s ∈ Icc (0:ℝ) T, ∀ z : WithLp 2 (Euc d × Euc d),
      G s z ≤ C + δ * ‖z‖ ^ 2 := by
    intro δ hδ
    refine ⟨2 * M0, fun s hs z => ?_⟩
    have h1 := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ ld_sg_bound (P := P) (W := W) (q := q)
      (B := B) hM0 s z.fst)
    have h2 := neg_le_of_abs_le ((Real.norm_eq_abs _ ▸ ld_sg_bound (P := P) (W := W) (q := q)
      (B := B) hM0 s z.snd) : |sg P W q B s g z.snd| ≤ M0)
    have h3 : 0 ≤ A * Real.exp (-c0 * s) * f ‖z.fst - z.snd‖ :=
      mul_nonneg (mul_nonneg hA0 (Real.exp_pos _).le) (hfnn _ (norm_nonneg _))
    have h4 : 0 ≤ δ * ‖z‖ ^ 2 := by positivity
    simp only [hG]
    linarith
  have hfail : ∃ lam : ℝ, ∀ ε : ℝ, 0 < ε → ∀ s ∈ Ioc (0:ℝ) T, ∀ z : WithLp 2 (Euc d × Euc d),
      0 < G s z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * s) →
      (∀ z' : WithLp 2 (Euc d × Euc d), G s z' - ε * (1 + ‖z'‖ ^ 2) * Real.exp (lam * s) ≤
        G s z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * s)) →
      Gt s z < ε * lam * (1 + ‖z‖ ^ 2) * Real.exp (lam * s) := by
    refine ⟨4 * d + 2 * Mb + 1, fun ε hε s hs z hpos hmax => ?_⟩
    have hsT : s ∈ Icc (0:ℝ) T := ⟨hs.1.le, hs.2⟩
    have hpen : ∀ z' : WithLp 2 (Euc d × Euc d),
        ε * (1 + ‖z'‖ ^ 2) * Real.exp ((4 * d + 2 * Mb + 1) * s) =
          ε * Real.exp ((4 * d + 2 * Mb + 1) * s) * ‖z'.fst‖ ^ 2 +
          ε * Real.exp ((4 * d + 2 * Mb + 1) * s) * ‖z'.snd‖ ^ 2 +
          ε * Real.exp ((4 * d + 2 * Mb + 1) * s) := fun z' => by
      rw [WithLp.prod_norm_sq_eq_of_L2]; ring
    have hexp : 0 < Real.exp ((4 * d + 2 * Mb + 1) * s) := Real.exp_pos _
    have hε' : 0 ≤ ε * Real.exp ((4 * d + 2 * Mb + 1) * s) := by positivity
    have hxy' : z.fst ≠ z.snd := by
      intro hxy0
      have h1 : G s z = 0 := by simp [hG, hxy0, hf0]
      rw [h1] at hpos
      have : 0 < ε * (1 + ‖z‖ ^ 2) * Real.exp ((4 * d + 2 * Mb + 1) * s) := by positivity
      linarith
    have hA' : 0 ≤ A * Real.exp (-c0 * s) := mul_nonneg hA0 (Real.exp_pos _).le
    have hmax' : ∀ x' y' : Euc d,
        sg P W q B s g x' - sg P W q B s g y' - A * Real.exp (-c0 * s) * f ‖x' - y'‖
          - ε * Real.exp ((4 * d + 2 * Mb + 1) * s) * ‖x'‖ ^ 2
          - ε * Real.exp ((4 * d + 2 * Mb + 1) * s) * ‖y'‖ ^ 2
          + (-(ε * Real.exp ((4 * d + 2 * Mb + 1) * s))) ≤
        sg P W q B s g z.fst - sg P W q B s g z.snd
          - A * Real.exp (-c0 * s) * f ‖z.fst - z.snd‖
          - ε * Real.exp ((4 * d + 2 * Mb + 1) * s) * ‖z.fst‖ ^ 2
          - ε * Real.exp ((4 * d + 2 * Mb + 1) * s) * ‖z.snd‖ ^ 2
          + (-(ε * Real.exp ((4 * d + 2 * Mb + 1) * s))) := by
      intro x' y'
      have h1 := hmax (WithLp.toLp 2 (x', y'))
      have e1 := hpen (WithLp.toLp 2 (x', y'))
      have e2 := hpen z
      simp only [hG, WithLp.toLp_fst, WithLp.toLp_snd] at h1 e1
      linarith
    have hr0 : 0 ≤ ‖z.fst - z.snd‖ := norm_nonneg _
    have hfp : 0 ≤ deriv f ‖z.fst - z.snd‖ := le_trans hκ.le (hfd _ hr0).1
    have hstep := ld_step hq hm hB hd (hu s hsT) hf2 hA' hε' hfp hxy' hmax'
    have hfi := hfine _ hr0
    have hAfi : A * Real.exp (-c0 * s) * (4 * deriv (deriv f) ‖z.fst - z.snd‖ +
        pm_c q Mb ‖z.fst - z.snd‖ * deriv f ‖z.fst - z.snd‖) ≤
        A * Real.exp (-c0 * s) * (-(c0 * f ‖z.fst - z.snd‖)) :=
      mul_le_mul_of_nonneg_left hfi hA'
    have hc1 := ld_L_commute hq hm hB hW hg hMi hs.1.le z.fst
    have hc2 := ld_L_commute hq hm hB hW hg hMi hs.1.le z.snd
    have hGt' : Gt s z = kolmL q B (sg P W q B s g) z.fst - kolmL q B (sg P W q B s g) z.snd +
        c0 * (A * Real.exp (-c0 * s) * f ‖z.fst - z.snd‖) := by
      simp only [hGt, hc1, hc2]
    rw [hGt']
    have hS : 0 < ε * Real.exp ((4 * d + 2 * Mb + 1) * s) *
        (1 + ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2) := by positivity
    have hz : ε * (4 * d + 2 * Mb + 1) * (1 + ‖z‖ ^ 2) * Real.exp ((4 * d + 2 * Mb + 1) * s) =
        ε * Real.exp ((4 * d + 2 * Mb + 1) * s) * (4 * d + 2 * Mb) *
          (1 + ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2) +
        ε * Real.exp ((4 * d + 2 * Mb + 1) * s) * (1 + ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2) := by
      rw [WithLp.prod_norm_sq_eq_of_L2]; ring
    rw [hz]
    have e3 : A * Real.exp (-c0 * s) * (-(c0 * f ‖z.fst - z.snd‖)) =
        -(c0 * (A * Real.exp (-c0 * s) * f ‖z.fst - z.snd‖)) := by ring
    linarith
  have key := pm_penalized_max (E := WithLp 2 (Euc d × Euc d)) G Gt T hcont hder h0 hgrow hfail
  have hbound : ∀ a b : Euc d, sg P W q B t g a - sg P W q B t g b ≤
      A * Real.exp (-c0 * t) * ‖a - b‖ := by
    intro a b
    have h1 : sg P W q B t g a - sg P W q B t g b - A * Real.exp (-c0 * t) * f ‖a - b‖ ≤ 0 :=
      key t htT (WithLp.toLp 2 (a, b))
    have h2 : A * Real.exp (-c0 * t) * f ‖a - b‖ ≤ A * Real.exp (-c0 * t) * ‖a - b‖ :=
      mul_le_mul_of_nonneg_left (hfb _ (norm_nonneg _)).2 (mul_nonneg hA0 (Real.exp_pos _).le)
    linarith
  have e : κ⁻¹ * Real.exp (-c0 * t) * M1 * ‖x - y‖ = A * Real.exp (-c0 * t) * ‖x - y‖ := by
    rw [hAdef]; field_simp
  rw [e, abs_le]
  constructor
  · have := hbound y x
    rw [norm_sub_rev] at this
    linarith
  · exact hbound x y

/-! ### Centered decay -/

theorem ld_first_moment {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (hμ2 : Integrable (fun y : Euc d => ‖y‖ ^ 2) μ) {m2 : ℝ} (hm2 : ∫ y, ‖y‖ ^ 2 ∂μ ≤ m2) :
    Integrable (fun y : Euc d => ‖y‖) μ ∧ ∫ y, ‖y‖ ∂μ ≤ Real.sqrt m2 := by
  have hmeas : AEStronglyMeasurable (fun y : Euc d => ‖y‖) μ := continuous_norm.aestronglyMeasurable
  have hL2 : MemLp (fun y : Euc d => ‖y‖) 2 μ := (memLp_two_iff_integrable_sq hmeas).2 hμ2
  have hint : Integrable (fun y : Euc d => ‖y‖) μ := hL2.integrable (by norm_num)
  refine ⟨hint, ?_⟩
  have hv := ProbabilityTheory.variance_nonneg (fun y : Euc d => ‖y‖) μ
  rw [ProbabilityTheory.variance_eq_sub hL2] at hv
  have h1 : (∫ y, ‖y‖ ∂μ) ^ 2 ≤ m2 := by
    have e : ∫ x, ((fun y : Euc d => ‖y‖) ^ 2) x ∂μ = ∫ y, ‖y‖ ^ 2 ∂μ := rfl
    rw [e] at hv
    linarith
  exact Real.le_sqrt_of_sq_le h1

/-- **POIS-LIPDEC, centered decay.**  If `μ` is a probability measure with `∫ |y|² dμ ≤ m2` for which
`P_t r` has the same mean as `r` (`hinv`, the invariance `∫ P_t r dμ = ∫ r dμ`, to be supplied by the
invariance packet) and `∫ r dμ = 0`, then `|P_t r (x)| ≤ min{‖r‖∞, κ⁻¹ e^{-c0 t} Lip r (|x| + √m2)}`. -/
theorem pois_centered_decay {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {r : Euc d → ℝ} (hr : ContDiff ℝ 2 r) {M0 M1 M2 : ℝ} (hM0 : ∀ y, ‖r y‖ ≤ M0)
    (hM1 : ∀ y, ‖fderiv ℝ r y‖ ≤ M1) (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 r y‖ ≤ M2)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (hμ2 : Integrable (fun y : Euc d => ‖y‖ ^ 2) μ) {m2 : ℝ} (hm2 : ∫ y, ‖y‖ ^ 2 ∂μ ≤ m2)
    (hcen : ∫ y, r y ∂μ = 0) {t : ℝ} (ht : 0 ≤ t)
    (hinv : ∫ y, sg P W q B t r y ∂μ = ∫ y, r y ∂μ) (x : Euc d) :
    |sg P W q B t r x| ≤ min M0
      ((pm_kappa q Mb)⁻¹ * Real.exp (-(pm_c0 q Mb) * t) * M1 * (‖x‖ + Real.sqrt m2)) := by
  refine le_min ?_ ?_
  · have := ld_sg_bound (P := P) (W := W) (q := q) (B := B) hM0 t x
    rwa [Real.norm_eq_abs] at this
  set Lt : ℝ := (pm_kappa q Mb)⁻¹ * Real.exp (-(pm_c0 q Mb) * t) * M1 with hLt
  have hM1nn : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hLt0 : 0 ≤ Lt := by
    have : 0 < (pm_kappa q Mb)⁻¹ := inv_pos.2 (Real.exp_pos _)
    positivity
  obtain ⟨hi1, hmom⟩ := ld_first_moment hμ2 hm2
  -- continuity and integrability of `y ↦ P_t r y`
  have hn := sgNoise_of_brownian hW
  have hm1 : 1 ≤ m := by omega
  have hMi : ∀ i ≤ 2, ∀ z, ‖iteratedFDeriv ℝ i r z‖ ≤ max (max M0 M1) M2 := by
    intro i hi z
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]; exact (hM0 z).trans ((le_max_left _ _).trans (le_max_left _ _))
    · rw [norm_iteratedFDeriv_one]; exact (hM1 z).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hM2 z).trans (le_max_right _ _)
  obtain ⟨C, hC1, hC⟩ := sg_contDiff (d := d) q Mb hq m hm t ht 2 hm
  have hcont : Continuous (sg P W q B t r) := by
    have := (hC P W hn B hB r (by exact_mod_cast hr) _ hMi t ⟨ht, le_rfl⟩).1
    exact (this.continuous)
  have hint : Integrable (sg P W q B t r) μ :=
    Integrable.of_bound hcont.aestronglyMeasurable M0
      (Filter.Eventually.of_forall fun y => ld_sg_bound (P := P) (W := W) (q := q) (B := B) hM0 t y)
  have hconst : Integrable (fun _ : Euc d => sg P W q B t r x) μ := integrable_const _
  have hzero : ∫ y, sg P W q B t r y ∂μ = 0 := by rw [hinv, hcen]
  have hdiff : sg P W q B t r x = ∫ y, (sg P W q B t r x - sg P W q B t r y) ∂μ := by
    rw [integral_sub hconst hint, hzero]; simp
  have hbd : Integrable (fun y : Euc d => Lt * (‖x‖ + ‖y‖)) μ :=
    (integrable_const (‖x‖)).add hi1 |>.const_mul Lt
  have hle : ‖∫ y, (sg P W q B t r x - sg P W q B t r y) ∂μ‖ ≤ ∫ y, Lt * (‖x‖ + ‖y‖) ∂μ := by
    refine norm_integral_le_of_norm_le hbd (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (pois_lipdecay hq hm hB hW hr hM0 hM1 hM2 ht x y).trans ?_
    have : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    rw [hLt]
    exact mul_le_mul_of_nonneg_left this hLt0
  have hint2 : ∫ y, Lt * (‖x‖ + ‖y‖) ∂μ ≤ Lt * (‖x‖ + Real.sqrt m2) := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hLt0
    rw [integral_add (integrable_const _) hi1]
    simp only [integral_const, probReal_univ, one_smul]
    linarith
  rw [hdiff, ← Real.norm_eq_abs]
  exact hle.trans hint2

/-! ### The logarithmic bound -/

/-- **POIS-LIPDEC, log bound.**  `∫_0^∞ min{a, A e^{-c0 t}} dt ≤ (a/c0)(1 + log⁺(A/a))`
(`log⁺ = Real.posLog`), together with integrability of the integrand on `(0,∞)`. -/
theorem pois_logbound {a A c0 : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hc : 0 < c0) :
    IntegrableOn (fun t : ℝ => min a (A * Real.exp (-(c0 * t)))) (Set.Ioi 0) ∧
    ∫ t in Set.Ioi (0 : ℝ), min a (A * Real.exp (-(c0 * t))) ≤
      a / c0 * (1 + Real.posLog (A / a)) := by
  set F : ℝ → ℝ := fun t => min a (A * Real.exp (-(c0 * t))) with hF
  have hFc : Continuous F := by
    refine continuous_const.min ?_
    fun_prop
  have hexp : ∀ s : ℝ, IntegrableOn (fun t : ℝ => A * Real.exp (-(c0 * t))) (Set.Ioi s) := fun s => by
    have := (integrableOn_exp_mul_Ioi (show -c0 < 0 by linarith) s).const_mul A
    have e : (fun t : ℝ => A * Real.exp (-(c0 * t))) = fun t => A * Real.exp (-c0 * t) := by
      funext t; rw [neg_mul]
    rw [e]
    exact this
  have hFi : ∀ s : ℝ, IntegrableOn F (Set.Ioi s) := fun s =>
    (hexp s).mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min ha.le (by positivity))]
      exact min_le_right _ _)
  refine ⟨hFi 0, ?_⟩
  set L : ℝ := Real.posLog (A / a) with hL
  have hL0 : 0 ≤ L := Real.posLog_nonneg
  set T0 : ℝ := L / c0 with hT0
  have hT00 : 0 ≤ T0 := by positivity
  have hsplit : ∫ t in Set.Ioi (0 : ℝ), F t =
      (∫ t in Set.Ioc (0 : ℝ) T0, F t) + ∫ t in Set.Ioi T0, F t := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hFc.integrableOn_Ioc) (hFi T0), Set.Ioc_union_Ioi_eq_Ioi hT00]
  have h1 : ∫ t in Set.Ioc (0 : ℝ) T0, F t ≤ a * T0 := by
    have := setIntegral_mono_on (μ := volume) (hFc.integrableOn_Ioc (a := 0) (b := T0))
      (integrableOn_const (μ := volume) (s := Set.Ioc (0 : ℝ) T0) (C := a)
        (by simp)) measurableSet_Ioc (fun t _ => min_le_left _ _)
    rw [setIntegral_const] at this
    simpa [Real.volume_real_Ioc, hT00, mul_comm] using this
  have h2 : ∫ t in Set.Ioi T0, F t ≤ A * (Real.exp (-(c0 * T0)) / c0) := by
    have := setIntegral_mono_on (μ := volume) (hFi T0) (hexp T0) measurableSet_Ioi
      (fun t _ => min_le_right _ _)
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul]
    have h3 := integral_exp_mul_Ioi (show -c0 < 0 by linarith) T0
    simp only [neg_mul] at h3 ⊢
    rw [h3]
    field_simp
  have hAe : A * Real.exp (-(c0 * T0)) ≤ a := by
    have hcT : c0 * T0 = L := by rw [hT0]; field_simp
    rw [hcT]
    rcases le_or_gt A a with hAa | hAa
    · have : L = 0 := by
        rw [hL, Real.posLog_eq_zero_iff, abs_of_nonneg (by positivity), div_le_one ha]
        exact hAa
      rw [this]; simpa using hAa
    · have hr : 1 < A / a := by rwa [one_lt_div ha]
      have hLl : L = Real.log (A / a) := by
        rw [hL, Real.posLog]
        exact max_eq_right (Real.log_nonneg hr.le)
      have hA0 : A ≠ 0 := by have : 0 < A := ha.trans hAa; exact this.ne'
      rw [hLl, Real.exp_neg, Real.exp_log (by positivity), inv_div]
      have e : A * (a / A) = a := by field_simp
      rw [e]
  calc ∫ t in Set.Ioi (0 : ℝ), F t = _ := hsplit
    _ ≤ a * T0 + A * (Real.exp (-(c0 * T0)) / c0) := add_le_add h1 h2
    _ ≤ a * T0 + a / c0 := by
        have : A * (Real.exp (-(c0 * T0)) / c0) = (A * Real.exp (-(c0 * T0))) / c0 := by ring
        rw [this]
        have := div_le_div_of_nonneg_right hAe hc.le
        linarith
    _ = a / c0 * (1 + L) := by rw [hT0]; field_simp; ring

end HRS.MS.PoisLip
