/-
# HRS.External.WuResampling -- Wu's conditional-variance inequality (EXT-1, E2)

Formalization from scratch of L. Wu, Ann. Probab. 34 (2006), Thm 2.1 (discrete metric), as used
in the main manuscript as `A:eq:resampling`, `N:eq:weak-pi`, `A:eq:weak-linear`, for the law
`(μ^n).withDensity W` on `Fin n → E` with `W` bounded and positive (abstract setting, no torus).

The proof replaces Wu's semigroup argument by a discrete-time one: the random-scan operator
`P = n⁻¹ ∑ᵢ G_i` is a self-adjoint contraction on centered bounded functions with norm
`≤ ρ = 1 - (1 - r)/n` (oscillation contraction of `Dobrushin.lean` plus log-convexity of
`‖P^m g‖²`), which gives the Poincaré inequality for bounded `g`
(`poincare_bounded`, `wu_bounded`); truncation `clip` and Fatou on the pair integral
`∬ (F a - F b)²` extend it to all measurable `F` (`wu_evariance`, `ℝ≥0∞` form, no integrability
hypothesis), and to `L²` (`wu_resampling_spec_real`). Public statements: `wu_resampling`,
`wu_resampling_half`, `wu_resampling_uniform`, `wu_resampling_half_real`,
`wu_resampling_uniform_real`, `wu_linear`, `wu_linear_real`, `wu_linear_symm`, `wu_linear_pinned`.
-/
import HRS.External.Dobrushin

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.External

section Real

/-- A log-convex nonnegative sequence with geometric upper bound `K s^k` has `b₁ ≤ s b₀`. -/
lemma ratio_le_of_logconvex {b : ℕ → ℝ} {K s : ℝ} (hb0 : ∀ k, 0 ≤ b k)
    (hlc : ∀ k, b (k + 1) ^ 2 ≤ b k * b (k + 2)) (hs : 0 ≤ s) (hdec : ∀ k, b k ≤ K * s ^ k) :
    b 1 ≤ s * b 0 := by
  by_contra hcon
  have hcon := not_le.mp hcon
  have hb1 : 0 < b 1 := lt_of_le_of_lt (mul_nonneg hs (hb0 0)) hcon
  have hb0pos : 0 < b 0 := by
    rcases (hb0 0).eq_or_lt with h | h
    · exfalso
      have := hlc 0
      rw [← h] at this
      simp at this
      linarith
    · exact h
  set q := b 1 / b 0 with hq
  have hqs : s < q := by
    rw [hq, lt_div_iff₀ hb0pos]; linarith
  have hq0 : 0 < q := lt_of_le_of_lt hs hqs
  have key : ∀ k, 0 < b k ∧ q * b k ≤ b (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨hb0pos, by rw [hq]; field_simp; simp⟩
    | succ k ih =>
      obtain ⟨hpos, hge⟩ := ih
      have hpos1 : 0 < b (k + 1) := lt_of_lt_of_le (mul_pos hq0 hpos) hge
      refine ⟨hpos1, ?_⟩
      have h1 := hlc k
      -- b(k+1)^2 ≤ b k * b (k+2), and b(k+1) ≥ q b k
      have : q * b (k + 1) * b k ≤ b k * b (k + 2) := by
        calc q * b (k + 1) * b k = b (k + 1) * (q * b k) := by ring
          _ ≤ b (k + 1) * b (k + 1) := mul_le_mul_of_nonneg_left hge hpos1.le
          _ = b (k + 1) ^ 2 := by ring
          _ ≤ b k * b (k + 2) := h1
      have h2 : q * b (k + 1) ≤ b (k + 2) := by
        by_contra hh
        have hh := not_le.mp hh
        nlinarith [mul_lt_mul_of_pos_left hh hpos]
      exact h2
  have hpow : ∀ k, q ^ k * b 0 ≤ b k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc q ^ (k + 1) * b 0 = q * (q ^ k * b 0) := by ring
        _ ≤ q * b k := mul_le_mul_of_nonneg_left ih hq0.le
        _ ≤ b (k + 1) := (key k).2
  set t := s / q with ht
  have ht0 : 0 ≤ t := div_nonneg hs hq0.le
  have ht1 : t < 1 := by rw [ht, div_lt_one hq0]; exact hqs
  have hle : ∀ k, b 0 ≤ K * t ^ k := by
    intro k
    have h1 := (hpow k).trans (hdec k)
    have h2 : q ^ k * b 0 ≤ K * s ^ k := h1
    have hqk : 0 < q ^ k := pow_pos hq0 k
    have : s ^ k = t ^ k * q ^ k := by rw [ht, div_pow]; field_simp
    rw [this] at h2
    nlinarith
  have hlim : Filter.Tendsto (fun k : ℕ => K * t ^ k) Filter.atTop (nhds (K * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).const_mul K
  rw [mul_zero] at hlim
  have := (hlim.eventually (gt_mem_nhds hb0pos)).exists
  obtain ⟨k, hk⟩ := this
  linarith [hle k]

/-- Cauchy-Schwarz for bounded measurable functions on a finite measure. -/
lemma integral_mul_sq_le {α : Type*} [MeasurableSpace α] {ρ : Measure α} [IsFiniteMeasure ρ]
    {f g : α → ℝ} {M : ℝ} (hf : Measurable f) (hg : Measurable g) (hfb : ∀ x, |f x| ≤ M)
    (hgb : ∀ x, |g x| ≤ M) :
    (∫ x, f x * g x ∂ρ) ^ 2 ≤ (∫ x, f x ^ 2 ∂ρ) * ∫ x, g x ^ 2 ∂ρ := by
  have hint : ∀ {u v : α → ℝ}, Measurable u → Measurable v → (∀ x, |u x| ≤ M) → (∀ x, |v x| ≤ M) →
      Integrable (fun x => u x * v x) ρ := by
    intro u v hu hv hub hvb
    refine Integrable.of_bound (hu.mul hv).aestronglyMeasurable (M * M)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hub x) (hvb x) (abs_nonneg _) ((abs_nonneg _).trans (hub x))
  have hff := hint hf hf hfb hfb
  have hgg := hint hg hg hgb hgb
  have hfg := hint hf hg hfb hgb
  have hff2 : Integrable (fun x => f x ^ 2) ρ := by simpa [sq] using hff
  have hgg2 : Integrable (fun x => g x ^ 2) ρ := by simpa [sq] using hgg
  have hq : ∀ t : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂ρ) * (t * t) + (2 * ∫ x, f x * g x ∂ρ) * t
      + ∫ x, g x ^ 2 ∂ρ := by
    intro t
    have h0 : 0 ≤ ∫ x, (t * f x + g x) ^ 2 ∂ρ := integral_nonneg fun x => sq_nonneg _
    have e : ∫ x, (t * f x + g x) ^ 2 ∂ρ
        = t * t * ∫ x, f x ^ 2 ∂ρ + 2 * t * ∫ x, f x * g x ∂ρ + ∫ x, g x ^ 2 ∂ρ := by
      have : ∀ x, (t * f x + g x) ^ 2 = t * t * (f x ^ 2) + 2 * t * (f x * g x) + g x ^ 2 :=
        fun x => by ring
      simp_rw [this]
      have h1 : Integrable (fun x => t * t * (f x ^ 2)) ρ := hff2.const_mul _
      have h2 : Integrable (fun x => 2 * t * (f x * g x)) ρ := hfg.const_mul _
      rw [integral_add (f := fun x => t * t * (f x ^ 2) + 2 * t * (f x * g x))
        (g := fun x => g x ^ 2) (h1.add h2) hgg2,
        integral_add (f := fun x => t * t * (f x ^ 2)) (g := fun x => 2 * t * (f x * g x)) h1 h2,
        integral_const_mul, integral_const_mul]
    rw [e] at h0
    linarith
  have := discrim_le_zero hq
  rw [discrim] at this
  nlinarith

end Real

section Core

open Spec

variable {E : Type*} [MeasurableSpace E] {n : ℕ} {S : Spec E n} {c : Fin n → Fin n → ℝ}

/-- Contraction `‖P h‖₂ ≤ ρ ‖h‖₂` for centered bounded `h` (log-convexity of `‖P^m h‖₂²`). -/
lemma integral_sq_scan_le [NeZero n] (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {M : ℝ} {h : (Fin n → E) → ℝ}
    (hm : Measurable h) (hb : ∀ x, |h x| ≤ M) (h0 : ∫ x, h x ∂S.P = 0) :
    ∫ x, S.scan h x ^ 2 ∂S.P ≤ (1 - (1 - r) / n) ^ 2 * ∫ x, h x ^ 2 ∂S.P := by
  have hρ := rho_nonneg hc hrow
  set ρ : ℝ := 1 - (1 - r) / n with hρdef
  set u : ℕ → (Fin n → E) → ℝ := fun k => S.scan^[k] h with hu
  have hum : ∀ k, Measurable (u k) := fun k => (integral_scan_iterate (S := S) hm hb k).1
  have hub : ∀ k x, |u k x| ≤ M := fun k => (integral_scan_iterate (S := S) hm hb k).2.1
  set b : ℕ → ℝ := fun k => ∫ x, u k x ^ 2 ∂S.P with hbdef
  have hsucc : ∀ k, u (k + 1) = S.scan (u k) := fun k => by
    simp only [hu]; rw [Function.iterate_succ_apply']
  have hb0 : ∀ k, 0 ≤ b k := fun k => integral_nonneg fun x => sq_nonneg _
  have hlc : ∀ k, b (k + 1) ^ 2 ≤ b k * b (k + 2) := by
    intro k
    have e : b (k + 1) = ∫ x, u (k + 2) x * u k x ∂S.P := by
      have h1 : b (k + 1) = ∫ x, u (k + 1) x * S.scan (u k) x ∂S.P := by
        simp only [hbdef]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        rw [← hsucc k]; ring
      rw [h1, integral_mul_scan_comm (hum (k + 1)) (hum k) (hub (k + 1)) (hub k), ← hsucc (k + 1)]
    rw [e]
    have := integral_mul_sq_le (ρ := S.P) (hum (k + 2)) (hum k) (hub (k + 2)) (hub k)
    rw [mul_comm (b k)]
    exact this
  have hdec : ∀ k, b k ≤ (n * (2 * M)) ^ 2 * (ρ ^ 2) ^ k := by
    intro k
    have hpt : ∀ x, u k x ^ 2 ≤ (ρ ^ k * (n * (2 * M))) ^ 2 := fun x => by
      have := abs_scan_iterate_sub_integral_le hc hrow hm hb k x
      rw [h0, sub_zero] at this
      exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
    have : b k ≤ ∫ _x, (ρ ^ k * (n * (2 * M))) ^ 2 ∂S.P :=
      integral_mono (integrable_of_bdd ((hum k).pow_const 2) (M := M ^ 2) (fun x => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hub k x) 2))
        (integrable_const _) hpt
    simpa [mul_pow, ← pow_mul, mul_comm, mul_left_comm, mul_assoc] using this
  have := ratio_le_of_logconvex hb0 hlc (sq_nonneg ρ) hdec
  simpa [hbdef, hu] using this

lemma integral_mul_scan_eq [NeZero n] {M : ℝ} {h : (Fin n → E) → ℝ} (hm : Measurable h)
    (hb : ∀ x, |h x| ≤ M) :
    ∫ x, h x * S.scan h x ∂S.P = (1 / (n : ℝ)) * ∑ i, ∫ x, h x * S.site i h x ∂S.P := by
  unfold scan
  have e1 : ∀ x, h x * ((1 / (n : ℝ)) * ∑ i, S.site i h x)
      = (1 / (n : ℝ)) * ∑ i, h x * S.site i h x := fun x => by
    rw [mul_left_comm, Finset.mul_sum]
  simp_rw [e1]
  rw [integral_const_mul]
  congr 1
  exact integral_finsetSum _ fun i _ => integrable_of_bdd (hm.mul (measurable_site hm i))
    (M := |M| * |M|) (fun x => by
      rw [abs_mul]
      exact mul_le_mul ((hb x).trans (le_abs_self _)) ((abs_site_le hb i x).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _))

/-- Sum of the expected conditional variances, in operator form. -/
lemma sum_integral_siteVar_real [NeZero n] {M : ℝ} {h : (Fin n → E) → ℝ} (hm : Measurable h)
    (hb : ∀ x, |h x| ≤ M) :
    ∑ i, ∫ x, (S.site i (fun y => h y ^ 2) x - S.site i h x ^ 2) ∂S.P
      = n * (∫ x, h x ^ 2 ∂S.P - ∫ x, h x * S.scan h x ∂S.P) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hsq : Measurable fun y => h y ^ 2 := hm.pow_const 2
  have hsqb : ∀ x, |h x ^ 2| ≤ M ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
  have hi : ∀ i, ∫ x, (S.site i (fun y => h y ^ 2) x - S.site i h x ^ 2) ∂S.P
      = ∫ x, h x ^ 2 ∂S.P - ∫ x, h x * S.site i h x ∂S.P := by
    intro i
    have i1 : Integrable (S.site i fun y => h y ^ 2) S.P :=
      integrable_of_bdd (measurable_site hsq i) (abs_site_le hsqb i)
    have i2 : Integrable (fun x => S.site i h x ^ 2) S.P :=
      integrable_of_bdd ((measurable_site hm i).pow_const 2) (M := M ^ 2) (fun x => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_site_le hb i x) 2)
    rw [integral_sub i1 i2, integral_site hsq hsqb i]
    have := integral_mul_site (S := S) hm hm hb hb i
    rw [this]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, integral_mul_scan_eq hm hb]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The Poincaré inequality for centered bounded measurable functions, in operator form. -/
lemma poincare_centered [NeZero n] (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {M : ℝ} {h : (Fin n → E) → ℝ}
    (hm : Measurable h) (hb : ∀ x, |h x| ≤ M) (h0 : ∫ x, h x ∂S.P = 0) :
    (1 - r) * ∫ x, h x ^ 2 ∂S.P
      ≤ ∑ i, ∫ x, (S.site i (fun y => h y ^ 2) x - S.site i h x ^ 2) ∂S.P := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hρ := rho_nonneg hc hrow
  set ρ : ℝ := 1 - (1 - r) / n with hρdef
  have hcs : (∫ x, h x * S.scan h x ∂S.P) ^ 2 ≤ (∫ x, h x ^ 2 ∂S.P) * ∫ x, S.scan h x ^ 2 ∂S.P :=
    integral_mul_sq_le (ρ := S.P) hm (measurable_scan hm) hb (abs_scan_le hb)
  have hcon := integral_sq_scan_le hc hrow hm hb h0
  have hb0 : 0 ≤ ∫ x, h x ^ 2 ∂S.P := integral_nonneg fun x => sq_nonneg _
  have hle : ∫ x, h x * S.scan h x ∂S.P ≤ ρ * ∫ x, h x ^ 2 ∂S.P := by
    have h1 : (∫ x, h x * S.scan h x ∂S.P) ^ 2 ≤ (ρ * ∫ x, h x ^ 2 ∂S.P) ^ 2 := by
      calc _ ≤ _ := hcs
        _ ≤ (∫ x, h x ^ 2 ∂S.P) * (ρ ^ 2 * ∫ x, h x ^ 2 ∂S.P) :=
            mul_le_mul_of_nonneg_left hcon hb0
        _ = _ := by ring
    exact (le_abs_self _).trans (abs_le_of_sq_le_sq h1 (mul_nonneg hρ hb0))
  rw [sum_integral_siteVar_real hm hb]
  have : (n : ℝ) * (1 - ρ) = 1 - r := by rw [hρdef]; field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left hle hn.le]

lemma memLp_section {M : ℝ} {g : (Fin n → E) → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ M)
    (i : Fin n) (x : Fin n → E) : MemLp (fun z => g (update x i z)) 2 (S.G i x) :=
  MemLp.of_bound (measurable_section g hg i x).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb _)

/-- Conditional variance of a bounded function in operator form. -/
lemma variance_section_eq {M : ℝ} {g : (Fin n → E) → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ M) (i : Fin n) (x : Fin n → E) :
    variance (fun z => g (update x i z)) (S.G i x)
      = S.site i (fun y => g y ^ 2) x - S.site i g x ^ 2 := by
  rw [variance_eq_sub (memLp_section hg hb i x)]
  simp [Spec.site, Pi.pow_apply]

/-- Poincaré inequality for bounded measurable functions (real form). -/
theorem poincare_bounded [NeZero n] (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {M : ℝ} {g : (Fin n → E) → ℝ}
    (hg : Measurable g) (hb : ∀ x, |g x| ≤ M) :
    (1 - r) * variance g S.P
      ≤ ∑ i, ∫ x, variance (fun z => g (update x i z)) (S.G i x) ∂S.P := by
  set m : ℝ := ∫ x, g x ∂S.P with hmdef
  set h : (Fin n → E) → ℝ := fun x => g x - m with hhdef
  have hhm : Measurable h := hg.sub_const m
  have hmM : |m| ≤ M := by
    have := norm_integral_le_of_norm_le_const (μ := S.P) (f := g) (C := M)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
    simpa [hmdef] using this
  have hhb : ∀ x, |h x| ≤ M + M := fun x => by
    have := abs_sub (g x) m
    simp only [hhdef]
    linarith [hb x]
  have h0 : ∫ x, h x ∂S.P = 0 := by
    simp only [hhdef]
    rw [integral_sub (integrable_of_bdd hg hb) (integrable_const _)]
    simp [hmdef]
  have hvar : variance g S.P = ∫ x, h x ^ 2 ∂S.P := by
    rw [variance_eq_integral hg.aemeasurable]
  have hsec : ∀ i x, variance (fun z => g (update x i z)) (S.G i x)
      = S.site i (fun y => h y ^ 2) x - S.site i h x ^ 2 := by
    intro i x
    rw [← variance_section_eq hhm hhb i x]
    have := variance_sub_const (μ := S.G i x) (X := fun z => g (update x i z))
      (measurable_section g hg i x).aestronglyMeasurable m
    simpa [hhdef] using this.symm
  simp_rw [hsec, hvar]
  exact poincare_centered hc hrow hhm hhb h0

end Core

section Pair

variable {α : Type*} [MeasurableSpace α]

/-- The variance is at most the second moment about any constant (in `ℝ≥0∞`). -/
lemma evariance_le_lintegral_sub (ν : Measure α) [IsProbabilityMeasure ν] {X : α → ℝ}
    (hX : AEStronglyMeasurable X ν) (c : ℝ) :
    evariance X ν ≤ ∫⁻ z, ‖X z - c‖ₑ ^ 2 ∂ν := by
  by_cases h : ∫⁻ z, ‖X z - c‖ₑ ^ 2 ∂ν = ⊤
  · simp [h]
  have hm : AEStronglyMeasurable (fun z => X z - c) ν := hX.sub aestronglyMeasurable_const
  have hint : Integrable (fun z => (X z - c) ^ 2) ν := by
    refine ⟨(hm.pow 2 : _), ?_⟩
    simp only [HasFiniteIntegral, enorm_pow]
    exact lt_top_iff_ne_top.mpr h
  have hmem : MemLp (fun z => X z - c) 2 ν := (memLp_two_iff_integrable_sq hm).2 hint
  have hXmem : MemLp X 2 ν := by
    have := hmem.add (memLp_const c)
    convert this using 1
    funext z
    simp
  rw [← ofReal_variance hXmem]
  have h1 : variance X ν = variance (fun z => X z - c) ν := (variance_sub_const hX c).symm
  have h2 : variance (fun z => X z - c) ν ≤ ∫ z, (X z - c) ^ 2 ∂ν := by
    have := variance_le_expectation_sq (μ := ν) hm
    simpa using this
  calc ENNReal.ofReal (variance X ν) ≤ ENNReal.ofReal (∫ z, (X z - c) ^ 2 ∂ν) := by
        rw [h1]; exact ENNReal.ofReal_le_ofReal h2
    _ = ∫⁻ z, ENNReal.ofReal ((X z - c) ^ 2) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => sq_nonneg _)
    _ = ∫⁻ z, ‖X z - c‖ₑ ^ 2 ∂ν := by
        refine lintegral_congr fun z => ?_
        rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

/-- Truncation of a real number to `[-M, M]`. -/
def clip (M t : ℝ) : ℝ := max (-M) (min M t)

lemma abs_clip_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : |clip M t| ≤ M := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clip_of_abs_le {M t : ℝ} (h : |t| ≤ M) : clip M t = t := by
  unfold clip
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

lemma abs_clip_sub_clip_le (M a b : ℝ) : |clip M a - clip M b| ≤ |a - b| := by
  unfold clip
  have h3 : |min M a - min M b| ≤ |a - b| := by
    refine (abs_min_sub_min_le_max M a M b).trans ?_
    simp
  rw [max_comm (-M), max_comm (-M)]
  exact (abs_max_sub_max_le_abs _ _ _).trans h3

lemma measurable_clip (M : ℝ) : Measurable (clip M) := by
  unfold clip
  fun_prop

/-- Truncation does not increase the variance. -/
lemma evariance_clip_le (ν : Measure α) [IsProbabilityMeasure ν] {X : α → ℝ}
    (hX : AEStronglyMeasurable X ν) (M : ℝ) :
    evariance (fun z => clip M (X z)) ν ≤ evariance X ν := by
  have hm : AEStronglyMeasurable (fun z => clip M (X z)) ν :=
    ((measurable_clip M).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
  refine (evariance_le_lintegral_sub ν hm (clip M (∫ z, X z ∂ν))).trans ?_
  unfold evariance
  refine lintegral_mono fun z => ?_
  gcongr
  rw [enorm_le_iff_norm_le]
  simpa [Real.norm_eq_abs] using abs_clip_sub_clip_le M (X z) (∫ z, X z ∂ν)

/-- Pair formula for the variance of an `L²` function. -/
lemma pair_eq_two_evariance (ν : Measure α) [IsProbabilityMeasure ν] {X : α → ℝ}
    (hX : MemLp X 2 ν) :
    ∫⁻ p, ‖X p.1 - X p.2‖ₑ ^ 2 ∂(ν.prod ν) = 2 * evariance X ν := by
  set Z : α × α → ℝ := fun p => X p.1 + (fun b => -X b) p.2 with hZ
  have hY : MemLp (fun b => -X b) 2 ν := hX.neg
  have hZm : MemLp Z 2 (ν.prod ν) := (hX.comp_fst ν).add (hY.comp_snd ν)
  have hint : Integrable X ν := hX.integrable one_le_two
  have hmean : ∫ p, Z p ∂(ν.prod ν) = 0 := by
    rw [integral_prod _ (hZm.integrable one_le_two)]
    have : ∀ a, ∫ b, Z (a, b) ∂ν = X a - ∫ b, X b ∂ν := fun a => by
      simp only [hZ]
      have hneg : Integrable (fun b => -X b) ν := hint.neg
      rw [integral_add (f := fun _ => X a) (g := fun b => -X b) (integrable_const _) hneg,
        integral_const, integral_neg]
      simp [sub_eq_add_neg]
    simp_rw [this]
    rw [integral_sub hint (integrable_const _)]
    simp
  have e1 : ∫⁻ p, ‖X p.1 - X p.2‖ₑ ^ 2 ∂(ν.prod ν) = evariance Z (ν.prod ν) := by
    unfold evariance
    rw [hmean]
    refine lintegral_congr fun p => ?_
    simp [hZ, sub_eq_add_neg]
  rw [e1, ← ofReal_variance hZm, variance_add_prod hX hY, variance_fun_neg,
    ← ofReal_variance hX, ← two_mul, ENNReal.ofReal_mul (by norm_num)]
  simp

lemma memLp_two_of_lintegral_lt_top (ν : Measure α) {f : α → ℝ}
    (hf : AEStronglyMeasurable f ν) (h : ∫⁻ z, ‖f z‖ₑ ^ 2 ∂ν < ⊤) : MemLp f 2 ν := by
  refine (memLp_two_iff_integrable_sq hf).2 ⟨(hf.pow 2 : _), ?_⟩
  simp only [HasFiniteIntegral, enorm_pow]
  exact h

/-- If the pair integral is finite, the function is in `L²`. -/
lemma memLp_of_pair_lt_top (ν : Measure α) [IsProbabilityMeasure ν] {X : α → ℝ}
    (hX : Measurable X) (h : ∫⁻ p, ‖X p.1 - X p.2‖ₑ ^ 2 ∂(ν.prod ν) < ⊤) : MemLp X 2 ν := by
  have hm2 : Measurable fun p : α × α => ‖X p.1 - X p.2‖ₑ ^ 2 :=
    ((hX.comp measurable_fst).sub (hX.comp measurable_snd)).enorm.pow_const 2
  rw [lintegral_prod _ hm2.aemeasurable] at h
  have hmeas : Measurable fun a => ∫⁻ b, ‖X a - X b‖ₑ ^ 2 ∂ν :=
    Measurable.lintegral_prod_right' (f := fun p : α × α => ‖X p.1 - X p.2‖ₑ ^ 2) (ν := ν) hm2
  have hae : ∀ᵐ a ∂ν, ∫⁻ b, ‖X a - X b‖ₑ ^ 2 ∂ν < ⊤ := ae_lt_top hmeas h.ne
  obtain ⟨a0, ha0⟩ := hae.exists
  have h1 : MemLp (fun b => X a0 - X b) 2 ν :=
    memLp_two_of_lintegral_lt_top ν (aestronglyMeasurable_const.sub hX.aestronglyMeasurable) ha0
  have := (memLp_const (X a0)).sub h1
  convert this using 1
  funext b
  simp

end Pair

section Main

open Spec

variable {E : Type*} [MeasurableSpace E] {n : ℕ} {S : Spec E n} {c : Fin n → Fin n → ℝ}

/-- Wu's inequality for bounded measurable functions in `ℝ≥0∞` form. -/
theorem wu_bounded [NeZero n] (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {M : ℝ} {g : (Fin n → E) → ℝ}
    (hg : Measurable g) (hb : ∀ x, |g x| ≤ M) :
    ENNReal.ofReal (1 - r) * evariance g S.P
      ≤ ∑ i, ∫⁻ x, S.siteVar i g x ∂S.P := by
  by_cases hr : 1 - r < 0
  · rw [ENNReal.ofReal_of_nonpos hr.le]; simp
  have hr : 0 ≤ 1 - r := not_lt.mp hr
  have hgm : MemLp g 2 S.P := MemLp.of_bound hg.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have hsq : Measurable fun y => g y ^ 2 := hg.pow_const 2
  have hsqb : ∀ x, |g x ^ 2| ≤ M ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
  have hint : ∀ i, Integrable (fun x => variance (fun z => g (update x i z)) (S.G i x)) S.P := by
    intro i
    have : (fun x => variance (fun z => g (update x i z)) (S.G i x))
        = fun x => S.site i (fun y => g y ^ 2) x - S.site i g x ^ 2 :=
      funext fun x => variance_section_eq hg hb i x
    rw [this]
    exact (integrable_of_bdd (measurable_site hsq i) (abs_site_le hsqb i)).sub
      (integrable_of_bdd ((measurable_site hg i).pow_const 2) (M := M ^ 2) (fun x => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_site_le hb i x) 2))
  have hsv : ∀ i x, S.siteVar i g x
      = ENNReal.ofReal (variance (fun z => g (update x i z)) (S.G i x)) := fun i x =>
    (ofReal_variance (memLp_section hg hb i x)).symm
  have hlin : ∀ i, ∫⁻ x, S.siteVar i g x ∂S.P
      = ENNReal.ofReal (∫ x, variance (fun z => g (update x i z)) (S.G i x) ∂S.P) := by
    intro i
    rw [ofReal_integral_eq_lintegral_ofReal (hint i)
      (Filter.Eventually.of_forall fun x => variance_nonneg _ _)]
    exact lintegral_congr fun x => hsv i x
  simp_rw [hlin]
  rw [← ofReal_variance hgm, ← ENNReal.ofReal_mul hr,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg fun x => variance_nonneg _ _)]
  exact ENNReal.ofReal_le_ofReal (poincare_bounded hc hrow hg hb)

/-- **Wu's conditional-variance inequality** (`ℝ≥0∞` form, all measurable `F`):
`(1 - r) Var_P(F) ≤ ∑ᵢ E_P[Var_i F]`. -/
theorem wu_evariance [NeZero n] (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {F : (Fin n → E) → ℝ}
    (hF : Measurable F) :
    ENNReal.ofReal (1 - r) * evariance F S.P ≤ ∑ i, ∫⁻ x, S.siteVar i F x ∂S.P := by
  set T : ℝ≥0∞ := ∑ i, ∫⁻ x, S.siteVar i F x ∂S.P with hT
  set cc : ℝ≥0∞ := ENNReal.ofReal (1 - r) with hcc
  -- truncations
  set Fk : ℕ → (Fin n → E) → ℝ := fun k x => clip k (F x) with hFk
  have hFkm : ∀ k, Measurable (Fk k) := fun k => (measurable_clip k).comp hF
  have hFkb : ∀ k x, |Fk k x| ≤ k := fun k x => abs_clip_le (Nat.cast_nonneg k) _
  have hk : ∀ k, cc * evariance (Fk k) S.P ≤ T := by
    intro k
    refine (wu_bounded hc hrow (hFkm k) (hFkb k)).trans ?_
    refine Finset.sum_le_sum fun i _ => lintegral_mono fun x => ?_
    exact evariance_clip_le (S.G i x) (measurable_section F hF i x).aestronglyMeasurable k
  -- Fatou for the pair integral
  set D : ((Fin n → E) → ℝ) → ℝ≥0∞ := fun X => ∫⁻ p, ‖X p.1 - X p.2‖ₑ ^ 2 ∂(S.P.prod S.P) with hD
  have hDk : ∀ k, cc * D (Fk k) ≤ 2 * T := by
    intro k
    have := pair_eq_two_evariance S.P (X := Fk k)
      (MemLp.of_bound (hFkm k).aestronglyMeasurable k
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFkb k x))
    simp only [hD]
    rw [this, mul_left_comm]
    exact mul_le_mul' le_rfl (hk k)
  have hmD : ∀ X : (Fin n → E) → ℝ, Measurable X →
      Measurable fun p : (Fin n → E) × (Fin n → E) => ‖X p.1 - X p.2‖ₑ ^ 2 := fun X hX =>
    ((hX.comp measurable_fst).sub (hX.comp measurable_snd)).enorm.pow_const 2
  have hfat : cc * D F ≤ 2 * T := by
    have hmeas : ∀ (X : (Fin n → E) → ℝ), Measurable X →
        Measurable fun p : (Fin n → E) × (Fin n → E) => cc * ‖X p.1 - X p.2‖ₑ ^ 2 := fun X hX =>
      (hmD X hX).const_mul cc
    have h1 := lintegral_liminf_le (μ := S.P.prod S.P) (u := Filter.atTop)
      (f := fun k p => cc * ‖Fk k p.1 - Fk k p.2‖ₑ ^ 2) (fun k => hmeas (Fk k) (hFkm k))
    have h2 : ∀ p : (Fin n → E) × (Fin n → E), Filter.liminf
        (fun k => cc * ‖Fk k p.1 - Fk k p.2‖ₑ ^ 2) Filter.atTop = cc * ‖F p.1 - F p.2‖ₑ ^ 2 := by
      intro p
      have hev : ∀ᶠ k : ℕ in Filter.atTop, cc * ‖Fk k p.1 - Fk k p.2‖ₑ ^ 2 = cc * ‖F p.1 - F p.2‖ₑ ^ 2 := by
        obtain ⟨K, hK⟩ := exists_nat_ge (max |F p.1| |F p.2|)
        filter_upwards [Filter.eventually_ge_atTop K] with k hk'
        have hk'' : (K : ℝ) ≤ k := by exact_mod_cast hk'
        have a1 : |F p.1| ≤ k := (le_max_left _ _).trans (hK.trans hk'')
        have a2 : |F p.2| ≤ k := (le_max_right _ _).trans (hK.trans hk'')
        simp only [hFk, clip_of_abs_le a1, clip_of_abs_le a2]
      rw [Filter.liminf_congr hev, Filter.liminf_const]
    simp_rw [h2] at h1
    have h3 : ∫⁻ p, cc * ‖F p.1 - F p.2‖ₑ ^ 2 ∂(S.P.prod S.P) = cc * D F := by
      exact lintegral_const_mul cc (hmD F hF)
    rw [h3] at h1
    refine h1.trans ?_
    refine Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun k => ?_)
    rw [lintegral_const_mul cc (hmD (Fk k) (hFkm k))]
    exact hDk k
  by_cases hDt : D F < ⊤
  · have hmem : MemLp F 2 S.P := memLp_of_pair_lt_top S.P hF hDt
    have := pair_eq_two_evariance S.P hmem
    have hDF : D F = 2 * evariance F S.P := this
    rw [hDF, mul_left_comm] at hfat
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hfat
  · have hDtop : D F = ⊤ := not_lt_top_iff.mp hDt
    by_cases hc0 : cc = 0
    · rw [hc0]; simp
    · rw [hDtop, ENNReal.mul_top hc0] at hfat
      have : T = ⊤ := by
        by_contra hne
        exact absurd hfat (by simp [ENNReal.mul_eq_top, hne])
      rw [this]; exact le_top

/-- Over an empty set of coordinates every function has zero variance. -/
lemma evariance_eq_zero_of_card_zero (hn : n = 0) (S : Spec E n) (F : (Fin n → E) → ℝ) :
    evariance F S.P = 0 := by
  subst hn
  have hsub : ∀ x y : Fin 0 → E, x = y := fun x y => Subsingleton.elim x y
  obtain ⟨x0⟩ := Measure.nonempty_of_neZero S.P
  have hconst : F = fun _ => F x0 := funext fun x => by rw [hsub x x0]
  rw [hconst]
  unfold evariance
  simp

/-- **Wu's inequality** for an abstract specification, `ℝ≥0∞` form, for every measurable `F`. -/
theorem wu_resampling_spec (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {F : (Fin n → E) → ℝ}
    (hF : Measurable F) :
    ENNReal.ofReal (1 - r) * evariance F S.P ≤ ∑ i, ∫⁻ x, S.siteVar i F x ∂S.P := by
  by_cases hn : n = 0
  · rw [evariance_eq_zero_of_card_zero hn S F]; simp
  · have : NeZero n := ⟨hn⟩
    exact wu_evariance hc hrow hF

lemma measurable_variance_section {F : (Fin n → E) → ℝ} (hF : Measurable F) (i : Fin n) :
    Measurable fun x => variance (fun z => F (update x i z)) (S.G i x) := by
  have e : ∀ x, variance (fun z => F (update x i z)) (S.G i x)
      = ∫ z, (F (update x i z) - S.site i F x) ^ 2 ∂(S.G i x) := fun x => by
    rw [variance_eq_integral (measurable_section F hF i x).aemeasurable]
    rfl
  simp_rw [e]
  have h : Measurable fun p : (Fin n → E) × E => (F (update p.1 i p.2) - S.site i F p.1) ^ 2 :=
    ((hF.comp measurable_update').sub ((measurable_site hF i).comp measurable_fst)).pow_const 2
  exact (h.stronglyMeasurable.integral_kernel_prod_right' (κ := S.G i)).measurable

/-- The `ℝ≥0∞` second moment of the sections is the second moment of `F`. -/
lemma lintegral_lintegral_sq_section {F : (Fin n → E) → ℝ} (hF : Measurable F) (i : Fin n) :
    ∫⁻ x, ∫⁻ z, ‖F (update x i z)‖ₑ ^ 2 ∂(S.G i x) ∂S.P = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂S.P :=
  S.invariant i (fun x => ‖F x‖ₑ ^ 2) (hF.enorm.pow_const 2)

/-- **Wu's inequality**, real form for `F ∈ L²(P)`:
`(1 - r) Var_P(F) ≤ ∑ᵢ E_P[Var_i F]`. -/
theorem wu_resampling_spec_real (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {F : (Fin n → E) → ℝ}
    (hF : Measurable F) (hL2 : MemLp F 2 S.P) :
    (1 - r) * variance F S.P
      ≤ ∑ i, ∫ x, variance (fun z => F (update x i z)) (S.G i x) ∂S.P := by
  have hV0 : ∀ i x, 0 ≤ variance (fun z => F (update x i z)) (S.G i x) :=
    fun i x => variance_nonneg _ _
  have hI : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂S.P < ⊤ := by
    have := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).1 hL2
    have h2 := this.hasFiniteIntegral
    simpa [HasFiniteIntegral, enorm_pow] using h2
  have hfin : ∀ i, Integrable (fun x => variance (fun z => F (update x i z)) (S.G i x)) S.P := by
    intro i
    have hmeas := measurable_variance_section (S := S) hF i
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hΦm : Measurable fun x => ∫⁻ z, ‖F (update x i z)‖ₑ ^ 2 ∂(S.G i x) :=
      ((hF.comp measurable_update').enorm.pow_const 2).lintegral_kernel_prod_right'
    have hle : ∀ x, ENNReal.ofReal (variance (fun z => F (update x i z)) (S.G i x))
        ≤ ∫⁻ z, ‖F (update x i z)‖ₑ ^ 2 ∂(S.G i x) := by
      intro x
      by_cases hm : MemLp (fun z => F (update x i z)) 2 (S.G i x)
      · rw [ofReal_variance hm]
        simpa using evariance_le_lintegral_sub (S.G i x)
          (measurable_section F hF i x).aestronglyMeasurable 0
      · rw [variance_of_not_memLp (measurable_section F hF i x).aestronglyMeasurable hm]
        simp
    have : ∫⁻ x, ENNReal.ofReal (variance (fun z => F (update x i z)) (S.G i x)) ∂S.P < ⊤ :=
      lt_of_le_of_lt (lintegral_mono hle) (by rw [lintegral_lintegral_sq_section hF i]; exact hI)
    simp only [HasFiniteIntegral, Real.enorm_eq_ofReal (hV0 i _)]
    exact this
  have hsv : ∀ i, ∫⁻ x, S.siteVar i F x ∂S.P
      = ENNReal.ofReal (∫ x, variance (fun z => F (update x i z)) (S.G i x) ∂S.P) := by
    intro i
    rw [ofReal_integral_eq_lintegral_ofReal (hfin i) (Filter.Eventually.of_forall (hV0 i))]
    refine lintegral_congr_ae ?_
    have hΦm : Measurable fun x => ∫⁻ z, ‖F (update x i z)‖ₑ ^ 2 ∂(S.G i x) :=
      ((hF.comp measurable_update').enorm.pow_const 2).lintegral_kernel_prod_right'
    have hΦ : ∀ᵐ x ∂S.P, ∫⁻ z, ‖F (update x i z)‖ₑ ^ 2 ∂(S.G i x) < ⊤ := by
      refine ae_lt_top hΦm ?_
      rw [lintegral_lintegral_sq_section hF i]; exact hI.ne
    filter_upwards [hΦ] with x hx
    have hm : MemLp (fun z => F (update x i z)) 2 (S.G i x) :=
      memLp_two_of_lintegral_lt_top (S.G i x) (measurable_section F hF i x).aestronglyMeasurable
        (by simpa using hx)
    exact (ofReal_variance hm).symm
  have key := wu_resampling_spec hc hrow hF
  simp_rw [hsv] at key
  have hsum0 : 0 ≤ ∑ i, ∫ x, variance (fun z => F (update x i z)) (S.G i x) ∂S.P :=
    Finset.sum_nonneg fun i _ => integral_nonneg (hV0 i)
  by_cases hr : 1 - r < 0
  · have := variance_nonneg F S.P
    nlinarith
  have hr : 0 ≤ 1 - r := not_lt.mp hr
  rw [← ofReal_variance hL2, ← ENNReal.ofReal_mul hr,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg (hV0 i)),
    ENNReal.ofReal_le_ofReal_iff hsum0] at key
  exact key

/-- The variance is invariant under adding a constant. -/
lemma evariance_add_const' {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {X : α → ℝ} (hX : AEStronglyMeasurable X ν) (a : ℝ) :
    evariance (fun z => X z + a) ν = evariance X ν := by
  have hXa : AEStronglyMeasurable (fun z => X z + a) ν := hX.add_const a
  by_cases hm : MemLp X 2 ν
  · have hm' : MemLp (fun z => X z + a) 2 ν := hm.add (memLp_const a)
    rw [← ofReal_variance hm, ← ofReal_variance hm', variance_add_const hX a]
  · have hm' : ¬ MemLp (fun z => X z + a) 2 ν := fun h => hm (by
      have := h.sub (memLp_const a)
      convert this using 1
      funext z; simp)
    rw [evariance_eq_top hX hm, evariance_eq_top hXa hm']

/-- The conditional variance of a sum of one-body functions only sees the `i`-th term. -/
lemma siteVar_sum {f : E → ℝ} (hf : Measurable f) (i : Fin n) (x : Fin n → E) :
    S.siteVar i (fun y => ∑ j, f (y j)) x = evariance f (S.G i x) := by
  unfold siteVar
  have : (fun z => ∑ j, f (update x i z j)) = fun z => f z + ∑ j ∈ Finset.univ.erase i, f (x j) := by
    funext z
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp [Finset.ne_of_mem_erase hj]
  rw [this]
  exact evariance_add_const' (S.G i x) hf.aestronglyMeasurable _

/-- Averaging the conditional variance of a one-body function gives at most its marginal
variance. -/
lemma lintegral_evariance_site_le {f : E → ℝ} (hf : Measurable f) (i : Fin n) :
    ∫⁻ x, evariance f (S.G i x) ∂S.P ≤ evariance f (S.P.map fun x => x i) := by
  set c : ℝ := ∫ y, f y ∂(S.P.map fun x => x i) with hc
  have h1 : ∀ x, evariance f (S.G i x) ≤ ∫⁻ z, ‖f z - c‖ₑ ^ 2 ∂(S.G i x) := fun x =>
    evariance_le_lintegral_sub (S.G i x) hf.aestronglyMeasurable c
  refine (lintegral_mono h1).trans ?_
  have hm : Measurable fun x : Fin n → E => ‖f (x i) - c‖ₑ ^ 2 :=
    ((hf.comp (measurable_pi_apply i)).sub_const c).enorm.pow_const 2
  have := S.invariant i (fun x => ‖f (x i) - c‖ₑ ^ 2) hm
  simp only [update_self] at this
  rw [this]
  unfold evariance
  rw [lintegral_map (((hf.sub_const c).enorm).pow_const 2) (measurable_pi_apply i)]

/-- **Linear form** (`A:eq:weak-linear`) for an abstract specification, `ℝ≥0∞` form: for every
measurable `f`, `(1 - r) Var_P(∑ᵢ f(yᵢ)) ≤ ∑ᵢ Var_{πᵢ}(f)` with `πᵢ` the `i`-th marginal. -/
theorem wu_linear_spec (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {f : E → ℝ} (hf : Measurable f) :
    ENNReal.ofReal (1 - r) * evariance (fun y => ∑ j, f (y j)) S.P
      ≤ ∑ i, evariance f (S.P.map fun x => x i) := by
  have hF : Measurable fun y : Fin n → E => ∑ j, f (y j) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  refine (wu_resampling_spec hc hrow hF).trans (Finset.sum_le_sum fun i _ => ?_)
  simp_rw [siteVar_sum hf i]
  exact lintegral_evariance_site_le hf i

end Main

section Statements

open Spec

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

/-- **Wu's conditional-variance inequality** (L. Wu, Ann. Probab. 34 (2006), Thm 2.1, discrete
metric), in the form used as `A:eq:resampling` / `N:eq:weak-pi`.

Setting: `μ` a probability measure on the measurable space `E`, `W` a measurable, strictly
positive, bounded density with `∫ W d(μ^n) = 1`; `P = (μ^n).withDensity W` is a law on
`Fin n → E`, and `siteKernel μ W i x` is the one-site conditional law of coordinate `i` given the
other coordinates of `x`, with density `z ↦ W(x^{i ← z}) / ∫ W(x^{i ← z'}) μ(dz')` with respect to
`μ`. The numbers `c i j ≥ 0` are Dobrushin interdependence coefficients: for `i ≠ j` and
configurations `x, y` differing only in coordinate `j`,
`sup_A |G_i(x, A) - G_i(y, A)| ≤ c i j` (the Wasserstein distance for the discrete metric); `r`
bounds the row sums `∑_{j ≠ i} c i j`. Then for every measurable `F`
`(1 - r) Var_P(F) ≤ ∑ᵢ E_P[Var_i F]`, where `Var_i F (x)` is the variance of `z ↦ F(x^{i ← z})`
under `G_i(x, ·)`. Variances are `evariance` (`ℝ≥0∞`); no integrability of `F` is assumed. -/
theorem wu_resampling (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)
    (hW : Measurable W) (hpos : ∀ x, 0 < W x) (K : ℝ≥0) (hbd : ∀ x, W x ≤ K)
    (hnorm : ∫⁻ x, W x ∂(Measure.pi fun _ : Fin n => μ) = 1)
    (c : Fin n → Fin n → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hc : ∀ i j, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
      MeasurableSet A →
      |(siteKernel μ W i x).real A - (siteKernel μ W i y).real A| ≤ c i j)
    (r : ℝ) (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r)
    (F : (Fin n → E) → ℝ) (hF : Measurable F) :
    ENNReal.ofReal (1 - r) * evariance F ((Measure.pi fun _ : Fin n => μ).withDensity W)
      ≤ ∑ i, ∫⁻ x, evariance (fun z => F (update x i z)) (siteKernel μ W i x)
          ∂((Measure.pi fun _ : Fin n => μ).withDensity W) :=
  wu_resampling_spec (S := Spec.ofDensity μ W hW hpos K hbd hnorm) ⟨hc0, hc⟩ hrow hF


lemma le_two_mul_of_half {a T : ℝ≥0∞} {r : ℝ} (hr : r ≤ 1 / 2)
    (h : ENNReal.ofReal (1 - r) * a ≤ T) : a ≤ 2 * T := by
  have h1 : (2 : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (1 - r) := by
    have : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (1 - r) := ENNReal.ofReal_le_ofReal (by linarith)
    simpa [ENNReal.ofReal_div_of_pos, one_div] using this
  have h2 : (2 : ℝ≥0∞)⁻¹ * a ≤ T := (mul_le_mul_left h1 a).trans h
  calc a = 2 * (2⁻¹ * a) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * T := mul_le_mul' le_rfl h2

lemma row_sum_le_of_uniform {N : ℕ} (hN : 0 < N) (hnN : n ≤ N) {κ : ℝ} (hκ : 0 ≤ κ) (i : Fin n) :
    ∑ _j ∈ Finset.univ.erase i, κ / N ≤ κ := by
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ((n - 1 : ℕ) : ℝ) ≤ N := by
    have : n - 1 ≤ N := (Nat.sub_le n 1).trans hnN
    exact_mod_cast this
  calc ((n - 1 : ℕ) : ℝ) * (κ / N) = (((n - 1 : ℕ) : ℝ) / N) * κ := by ring
    _ ≤ 1 * κ := mul_le_mul_of_nonneg_right ((div_le_one hN').2 h1) hκ
    _ = κ := one_mul κ

/-- `A:eq:resampling` with the constant `2`: if the Dobrushin row sums are at most `1/2`, then
`Var_P(F) ≤ 2 ∑ᵢ E_P[Var_i F]` for every measurable `F`. -/
theorem wu_resampling_half (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)
    (hW : Measurable W) (hpos : ∀ x, 0 < W x) (K : ℝ≥0) (hbd : ∀ x, W x ≤ K)
    (hnorm : ∫⁻ x, W x ∂(Measure.pi fun _ : Fin n => μ) = 1)
    (c : Fin n → Fin n → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hc : ∀ i j, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
      MeasurableSet A →
      |(siteKernel μ W i x).real A - (siteKernel μ W i y).real A| ≤ c i j)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ 1 / 2)
    (F : (Fin n → E) → ℝ) (hF : Measurable F) :
    evariance F ((Measure.pi fun _ : Fin n => μ).withDensity W)
      ≤ 2 * ∑ i, ∫⁻ x, evariance (fun z => F (update x i z)) (siteKernel μ W i x)
          ∂((Measure.pi fun _ : Fin n => μ).withDensity W) :=
  le_two_mul_of_half (r := 1 / 2) le_rfl (wu_resampling μ W hW hpos K hbd hnorm c hc0 hc (1 / 2) hrow F hF)


/-- `A:eq:resampling` in the form of the manuscript: if `G_i(x, ·)` and `G_i(y, ·)` differ in total
variation by at most `κ / N` whenever `x, y` differ only in a coordinate `j ≠ i` (`A:eq:weak-dobrushin`),
with `0 ≤ κ ≤ 1/2` and `n ≤ N` coordinates, then `Var_P(F) ≤ 2 ∑ᵢ E_P[Var_i F]`. -/
theorem wu_resampling_uniform (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)
    (hW : Measurable W) (hpos : ∀ x, 0 < W x) (K : ℝ≥0) (hbd : ∀ x, W x ≤ K)
    (hnorm : ∫⁻ x, W x ∂(Measure.pi fun _ : Fin n => μ) = 1)
    (N : ℕ) (hN : 0 < N) (hnN : n ≤ N) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 2)
    (hdob : ∀ i j, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
      MeasurableSet A →
      |(siteKernel μ W i x).real A - (siteKernel μ W i y).real A| ≤ κ / N)
    (F : (Fin n → E) → ℝ) (hF : Measurable F) :
    evariance F ((Measure.pi fun _ : Fin n => μ).withDensity W)
      ≤ 2 * ∑ i, ∫⁻ x, evariance (fun z => F (update x i z)) (siteKernel μ W i x)
          ∂((Measure.pi fun _ : Fin n => μ).withDensity W) :=
  wu_resampling_half μ W hW hpos K hbd hnorm (fun _ _ => κ / N)
    (fun _ _ => div_nonneg hκ0 (Nat.cast_nonneg N)) hdob
    (fun i => (row_sum_le_of_uniform hN hnN hκ0 i).trans hκ) F hF

/-- Real form of `wu_resampling_half`, for `F ∈ L²(P)`:
`Var_P(F) ≤ 2 ∑ᵢ E_P[Var_i F]`. -/
theorem wu_resampling_half_real (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)
    (hW : Measurable W) (hpos : ∀ x, 0 < W x) (K : ℝ≥0) (hbd : ∀ x, W x ≤ K)
    (hnorm : ∫⁻ x, W x ∂(Measure.pi fun _ : Fin n => μ) = 1)
    (c : Fin n → Fin n → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hc : ∀ i j, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
      MeasurableSet A →
      |(siteKernel μ W i x).real A - (siteKernel μ W i y).real A| ≤ c i j)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ 1 / 2)
    (F : (Fin n → E) → ℝ) (hF : Measurable F) (hL2 : MemLp F 2 ((Measure.pi fun _ : Fin n => μ).withDensity W)) :
    variance F ((Measure.pi fun _ : Fin n => μ).withDensity W)
      ≤ 2 * ∑ i, ∫ x, variance (fun z => F (update x i z)) (siteKernel μ W i x) ∂((Measure.pi fun _ : Fin n => μ).withDensity W) := by
  have h := wu_resampling_spec_real (S := Spec.ofDensity μ W hW hpos K hbd hnorm)
    ⟨hc0, hc⟩ hrow hF hL2
  have hv := variance_nonneg F (Spec.ofDensity μ W hW hpos K hbd hnorm).P
  have hs : 0 ≤ ∑ i, ∫ x, variance (fun z => F (update x i z)) (siteKernel μ W i x) ∂((Measure.pi fun _ : Fin n => μ).withDensity W) :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun x => variance_nonneg _ _
  have h' : (1 - 1 / 2) * variance F ((Measure.pi fun _ : Fin n => μ).withDensity W)
      ≤ ∑ i, ∫ x, variance (fun z => F (update x i z)) (siteKernel μ W i x)
          ∂((Measure.pi fun _ : Fin n => μ).withDensity W) := h
  linarith

/-- Real form of `wu_resampling_uniform` (the statement `N:eq:weak-pi` for `F ∈ L²`). -/
theorem wu_resampling_uniform_real (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)
    (hW : Measurable W) (hpos : ∀ x, 0 < W x) (K : ℝ≥0) (hbd : ∀ x, W x ≤ K)
    (hnorm : ∫⁻ x, W x ∂(Measure.pi fun _ : Fin n => μ) = 1)
    (N : ℕ) (hN : 0 < N) (hnN : n ≤ N) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 2)
    (hdob : ∀ i j, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
      MeasurableSet A →
      |(siteKernel μ W i x).real A - (siteKernel μ W i y).real A| ≤ κ / N)
    (F : (Fin n → E) → ℝ) (hF : Measurable F) (hL2 : MemLp F 2 ((Measure.pi fun _ : Fin n => μ).withDensity W)) :
    variance F ((Measure.pi fun _ : Fin n => μ).withDensity W)
      ≤ 2 * ∑ i, ∫ x, variance (fun z => F (update x i z)) (siteKernel μ W i x) ∂((Measure.pi fun _ : Fin n => μ).withDensity W) :=
  wu_resampling_half_real μ W hW hpos K hbd hnorm (fun _ _ => κ / N)
    (fun _ _ => div_nonneg hκ0 (Nat.cast_nonneg N)) hdob
    (fun i => (row_sum_le_of_uniform hN hnN hκ0 i).trans hκ) F hF hL2

/-- **Linear form** (`A:eq:weak-linear`): if every one-coordinate marginal of `P` equals `π`, then
`Var_P(∑ᵢ f(yᵢ)) ≤ 2 n Var_π(f)` for every measurable `f`. -/
theorem wu_linear (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)
    (hW : Measurable W) (hpos : ∀ x, 0 < W x) (K : ℝ≥0) (hbd : ∀ x, W x ≤ K)
    (hnorm : ∫⁻ x, W x ∂(Measure.pi fun _ : Fin n => μ) = 1)
    (c : Fin n → Fin n → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hc : ∀ i j, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
      MeasurableSet A →
      |(siteKernel μ W i x).real A - (siteKernel μ W i y).real A| ≤ c i j)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ 1 / 2)
    (π : Measure E) (hπ : ∀ i, ((Measure.pi fun _ : Fin n => μ).withDensity W).map (fun x => x i) = π)
    (f : E → ℝ) (hf : Measurable f) :
    evariance (fun y : Fin n → E => ∑ i, f (y i)) ((Measure.pi fun _ : Fin n => μ).withDensity W) ≤ 2 * n * evariance f π := by
  have h := wu_linear_spec (S := Spec.ofDensity μ W hW hpos K hbd hnorm) ⟨hc0, hc⟩ hrow hf
  have h2 := le_two_mul_of_half (r := 1 / 2) le_rfl (by simpa using h)
  refine h2.trans ?_
  have : ∑ i : Fin n, evariance f (((Measure.pi fun _ : Fin n => μ).withDensity W).map fun x => x i) = n * evariance f π := by
    simp [hπ]
  change 2 * (∑ i : Fin n, evariance f (((Measure.pi fun _ : Fin n => μ).withDensity W).map fun x => x i)) ≤ _
  rw [this, mul_assoc]

/-- Real form of `wu_linear` (`A:eq:weak-linear`): for `f ∈ L²(π)`,
`Var_P(∑ᵢ f(yᵢ)) ≤ 2 n Var_π(f)`. -/
theorem wu_linear_real (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)
    (hW : Measurable W) (hpos : ∀ x, 0 < W x) (K : ℝ≥0) (hbd : ∀ x, W x ≤ K)
    (hnorm : ∫⁻ x, W x ∂(Measure.pi fun _ : Fin n => μ) = 1)
    (c : Fin n → Fin n → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hc : ∀ i j, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
      MeasurableSet A →
      |(siteKernel μ W i x).real A - (siteKernel μ W i y).real A| ≤ c i j)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ 1 / 2)
    (π : Measure E) [IsProbabilityMeasure π] (hπ : ∀ i, ((Measure.pi fun _ : Fin n => μ).withDensity W).map (fun x => x i) = π)
    (f : E → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 π) :
    variance (fun y : Fin n → E => ∑ i, f (y i)) ((Measure.pi fun _ : Fin n => μ).withDensity W) ≤ 2 * n * variance f π := by
  have h := wu_linear μ W hW hpos K hbd hnorm c hc0 hc hrow π hπ f hf
  have hF : Measurable fun y : Fin n → E => ∑ i, f (y i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have : IsProbabilityMeasure ((Measure.pi fun _ : Fin n => μ).withDensity W) := (Spec.ofDensity μ W hW hpos K hbd hnorm).isProb
  rw [← ofReal_variance hf2] at h
  have hlt : evariance (fun y : Fin n → E => ∑ i, f (y i)) ((Measure.pi fun _ : Fin n => μ).withDensity W) < ⊤ := by
    refine lt_of_le_of_lt h ?_
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (by simp)) ENNReal.ofReal_lt_top
  have hmem : MemLp (fun y : Fin n → E => ∑ i, f (y i)) 2 ((Measure.pi fun _ : Fin n => μ).withDensity W) :=
    (evariance_lt_top_iff_memLp hF.aestronglyMeasurable).1 hlt
  rw [← ofReal_variance hmem] at h
  have h0 : 0 ≤ 2 * (n : ℝ) * variance f π := mul_nonneg (by positivity) (variance_nonneg _ _)
  have : (2 : ℝ≥0∞) * n * ENNReal.ofReal (variance f π) = ENNReal.ofReal (2 * n * variance f π) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [this, ENNReal.ofReal_le_ofReal_iff h0] at h
  exact h

/-- **Pinned variant.** A pinned ensemble with pin configuration `a : B → E` is the law
`(μ^n).withDensity (Wp a)` whose density `Wp a` contains the pair factors with the pins; its
conditional one-site kernels retain the pin factors, and `π` is its own one-coordinate marginal.
The linear form `A:eq:weak-linear` holds for it with the Dobrushin coefficients of the pinned
kernels. -/
theorem wu_linear_pinned {B : Type*} (μ : Measure E) [IsProbabilityMeasure μ]
    (Wp : (B → E) → (Fin n → E) → ℝ≥0∞) (a : B → E)
    (hW : Measurable (Wp a)) (hpos : ∀ x, 0 < Wp a x) (K : ℝ≥0) (hbd : ∀ x, Wp a x ≤ K)
    (hnorm : ∫⁻ x, Wp a x ∂(Measure.pi fun _ : Fin n => μ) = 1)
    (c : Fin n → Fin n → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hc : ∀ i j, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
      MeasurableSet A →
      |(siteKernel μ (Wp a) i x).real A - (siteKernel μ (Wp a) i y).real A| ≤ c i j)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ 1 / 2)
    (π : Measure E)
    (hπ : ∀ i, ((Measure.pi fun _ : Fin n => μ).withDensity (Wp a)).map (fun x => x i) = π)
    (f : E → ℝ) (hf : Measurable f) :
    evariance (fun y : Fin n → E => ∑ i, f (y i))
        ((Measure.pi fun _ : Fin n => μ).withDensity (Wp a)) ≤ 2 * n * evariance f π :=
  wu_linear μ (Wp a) hW hpos K hbd hnorm c hc0 hc hrow π hπ f hf


/-- Permuting the coordinates preserves the product measure. -/
lemma measurePreserving_comp_perm (μ : Measure E) [IsProbabilityMeasure μ] (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → E => x ∘ σ) (Measure.pi fun _ : Fin n => μ)
      (Measure.pi fun _ : Fin n => μ) := by
  have hm : Measurable fun x : Fin n → E => x ∘ σ :=
    measurable_pi_iff.2 fun k => measurable_pi_apply (σ k)
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun x : Fin n → E => x ∘ σ) ⁻¹' (Set.univ.pi s) = Set.univ.pi fun m => s (σ.symm m) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Function.comp]
    constructor
    · intro h m; simpa using h (σ.symm m)
    · intro h k; simpa using h (σ k)
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp σ.symm (fun k => μ (s k))

/-- If the density is invariant under all coordinate permutations, all one-coordinate marginals of
`(μ^n).withDensity W` coincide. -/
lemma map_eval_eq_of_symm (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)
    (hW : Measurable W) (hsymm : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → E), W (x ∘ σ) = W x)
    (i j : Fin n) :
    ((Measure.pi fun _ : Fin n => μ).withDensity W).map (fun x => x i)
      = ((Measure.pi fun _ : Fin n => μ).withDensity W).map (fun x => x j) := by
  ext A hA
  rw [Measure.map_apply (measurable_pi_apply i) hA, Measure.map_apply (measurable_pi_apply j) hA,
    withDensity_apply _ (measurable_pi_apply i hA), withDensity_apply _ (measurable_pi_apply j hA),
    ← lintegral_indicator (measurable_pi_apply i hA), ← lintegral_indicator (measurable_pi_apply j hA)]
  have hg : Measurable fun y : Fin n → E => ({y : Fin n → E | y i ∈ A}).indicator W y :=
    hW.indicator (measurable_pi_apply i hA)
  have := (measurePreserving_comp_perm μ (Equiv.swap i j)).lintegral_comp hg
  refine this.symm.trans (lintegral_congr fun x => ?_)
  have e : (Equiv.swap i j) i = j := Equiv.swap_apply_left i j
  have h1 : x ∘ ⇑(Equiv.swap i j) ∈ {y : Fin n → E | y i ∈ A} ↔ x ∈ (fun f : Fin n → E => f j) ⁻¹' A := by
    show x (Equiv.swap i j i) ∈ A ↔ x j ∈ A
    rw [e]
  simp only [Set.indicator, hsymm (Equiv.swap i j) x]
  by_cases h : x ∈ (fun f : Fin n → E => f j) ⁻¹' A
  · rw [if_pos h, if_pos (h1.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (h1.1 h'))]


/-- Linear form for an exchangeable law (`W` invariant under coordinate permutations), with `π` the
common one-coordinate marginal. -/
theorem wu_linear_symm [NeZero n] (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)
    (hW : Measurable W) (hpos : ∀ x, 0 < W x) (K : ℝ≥0) (hbd : ∀ x, W x ≤ K)
    (hnorm : ∫⁻ x, W x ∂(Measure.pi fun _ : Fin n => μ) = 1)
    (c : Fin n → Fin n → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hc : ∀ i j, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
      MeasurableSet A →
      |(siteKernel μ W i x).real A - (siteKernel μ W i y).real A| ≤ c i j)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ 1 / 2)
    (hsymm : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → E), W (x ∘ σ) = W x)
    (f : E → ℝ) (hf : Measurable f) :
    evariance (fun y : Fin n → E => ∑ i, f (y i)) ((Measure.pi fun _ : Fin n => μ).withDensity W)
      ≤ 2 * n * evariance f
          (((Measure.pi fun _ : Fin n => μ).withDensity W).map (fun x => x 0)) :=
  wu_linear μ W hW hpos K hbd hnorm c hc0 hc hrow _
    (fun i => map_eval_eq_of_symm μ W hW hsymm i 0) f hf

end Statements

end HRS.External
