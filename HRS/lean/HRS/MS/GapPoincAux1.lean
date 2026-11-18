import HRS.MS.GapRevAux1

/-!
# GAP-3: the doubling lemma and the Poincare inequality for smooth bounded functions

Supplement foundation packet GAP-3 (`docs/S4_PLAN.md`, section 2.4, steps 4 and 5; row S4.9).  Namespace
`HRS.MS.Gap`, helper prefix `gap234_`.

* `gap_doubling` (pure real analysis): if `u ≥ 0` on `[0,∞)`, `u(t)² ≤ u(2t) u(0)`, `u(t) ≤ A e^{-2ct}` and
  `u(0) > 0`, then `u(t) ≤ e^{-2ct} u(0)` for all `t ≥ 0`.  (Iterate `u(t)^{2^n} ≤ u(0)^{2^n - 1} u(2^n t)`.)
* `gap_smooth`: for `GapRef d ρ q B` (`μ = ρ dx`), `q > 0`, `B ∈ C_b^2`, a Brownian filtration, and `f` in the
  bounded `C²` class `gap234_Sm M` with `∫ f dμ = 0`:
  `c0 · ∫ f² dμ ≤ ∫ ‖∇f‖² dμ`, `c0 = pm_c0 q Mb` (so `c0 > 0` depends on `(q, Mb)` only).
  Proof: `u(t) = ‖P_t f‖² = ⟨f, P_{2t} f⟩` (reversibility `gap_reversible` and Markov), Cauchy-Schwarz gives
  `u(t)² ≤ u(0) u(2t)`, `pois_centered_decay` gives `u(t) ≤ A e^{-2 c0 t}`, the doubling lemma upgrades this to
  `u(t) ≤ e^{-2 c0 t} u(0)`, and the right derivative at `0` (`pois_kolmogorov`, dominated convergence with the
  linear growth of `kolmL f`, `gap_dirichlet`) gives `-∫‖∇f‖² ≤ -c0 ∫ f²`.
* `gap_smooth_const`: the same with the probability space chosen by `exists_isBrownianFiltration_type`, i.e.
  `∃ c > 0, ∀ M f, gap234_Sm M f → ∫ f dμ = 0 → c ∫ f² ≤ ∫ ‖∇f‖²`.

Statement adjustments relative to the plan sketch (documented, harmless): `‖∇f‖²` is `‖gradient f x‖ ^ 2`; the
right-hand side of the decay estimate is `A e^{-2 c0 t}` with the explicit `A = 4 m₂ (M/κ)²`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal Interval
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisInv HRS.MS.PoisLip HRS.MS.PoisMax
open HRS.MS.FlowB (clampT continuous_clampT clampT_mem clampT_of_mem)

noncomputable section

namespace HRS.MS.Gap

universe u

variable {d : ℕ}

/-! ### The doubling lemma -/

theorem gap234_dbl_iter {u : ℝ → ℝ} (hu0 : ∀ t, 0 ≤ t → 0 ≤ u t)
    (hdbl : ∀ t, 0 ≤ t → u t ^ 2 ≤ u (2 * t) * u 0) (hpos : 0 < u 0) :
    ∀ n : ℕ, ∀ t, 0 ≤ t → (u t / u 0) ^ (2 ^ n) ≤ u (2 ^ n * t) / u 0 := by
  intro n
  induction n with
  | zero => intro t _; simp
  | succ n ih =>
    intro t ht
    have h1 := ih t ht
    have h2 : 0 ≤ (u t / u 0) ^ (2 ^ n) := pow_nonneg (div_nonneg (hu0 t ht) hpos.le) _
    have h3 : ((u t / u 0) ^ (2 ^ n)) ^ 2 ≤ (u (2 ^ n * t) / u 0) ^ 2 := pow_le_pow_left₀ h2 h1 2
    have ht' : 0 ≤ 2 ^ n * t := by positivity
    have h4 := hdbl _ ht'
    have h5 : (u (2 ^ n * t) / u 0) ^ 2 ≤ u (2 * (2 ^ n * t)) / u 0 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) hpos]
      nlinarith [h4, hpos]
    have e1 : (u t / u 0) ^ (2 ^ (n + 1)) = ((u t / u 0) ^ (2 ^ n)) ^ 2 := by
      rw [pow_succ, pow_mul]
    have e2 : 2 * (2 ^ n * t) = 2 ^ (n + 1) * t := by ring
    rw [e1]
    rw [e2] at h5
    exact h3.trans h5

/-- **GAP-3 (doubling lemma).**  `u(t)² ≤ u(2t) u(0)`, `u(t) ≤ A e^{-2ct}` and `u(0) > 0` imply
`u(t) ≤ e^{-2ct} u(0)`. -/
theorem gap_doubling {u : ℝ → ℝ} (hu0 : ∀ t, 0 ≤ t → 0 ≤ u t)
    (hdbl : ∀ t, 0 ≤ t → u t ^ 2 ≤ u (2 * t) * u 0) {A c : ℝ}
    (hbd : ∀ t, 0 ≤ t → u t ≤ A * Real.exp (-(2 * c * t))) (hpos : 0 < u 0) :
    ∀ t, 0 ≤ t → u t ≤ Real.exp (-(2 * c * t)) * u 0 := by
  intro t ht
  set e : ℝ := Real.exp (-(2 * c * t)) with he
  have he0 : 0 < e := Real.exp_pos _
  set r : ℝ := u t / u 0 / e with hr
  have hr0 : 0 ≤ r := div_nonneg (div_nonneg (hu0 t ht) hpos.le) he0.le
  have hbound : ∀ n : ℕ, r ^ (2 ^ n) ≤ A / u 0 := by
    intro n
    have h1 := gap234_dbl_iter hu0 hdbl hpos n t ht
    have ht' : 0 ≤ 2 ^ n * t := by positivity
    have h2 := hbd _ ht'
    have h3 : Real.exp (-(2 * c * (2 ^ n * t))) = e ^ (2 ^ n) := by
      rw [he, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h3] at h2
    have h4 : (u t / u 0) ^ (2 ^ n) ≤ A / u 0 * e ^ (2 ^ n) := by
      refine h1.trans ?_
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpos]
      exact h2
    rw [hr, div_pow]
    rw [div_le_iff₀ (pow_pos he0 _)]
    exact h4
  have hr1 : r ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (A / u 0) hcon
    have : r ^ n ≤ r ^ (2 ^ n) := pow_le_pow_right₀ hcon.le (Nat.lt_two_pow_self).le
    linarith [hbound n]
  have : u t / u 0 ≤ e := by
    have := mul_le_mul_of_nonneg_right hr1 he0.le
    rwa [hr, div_mul_cancel₀ _ he0.ne', one_mul] at this
  rw [div_le_iff₀ hpos] at this
  linarith

/-! ### Cauchy-Schwarz for bounded continuous functions -/

theorem gap234_cs {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f k : Euc d → ℝ}
    (hf : Continuous f) (hk : Continuous k) {Mf Mk : ℝ} (hMf : ∀ x, ‖f x‖ ≤ Mf)
    (hMk : ∀ x, ‖k x‖ ≤ Mk) :
    (∫ x, f x * k x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, k x ^ 2 ∂μ := by
  have ib : ∀ {g : Euc d → ℝ} {M : ℝ}, Continuous g → (∀ x, ‖g x‖ ≤ M) → Integrable g μ :=
    fun hg hM => (integrable_const _).mono' hg.aestronglyMeasurable (ae_of_all _ hM)
  have i1 : Integrable (fun x => f x ^ 2) μ :=
    ib (hf.pow 2) (M := Mf ^ 2) (fun x => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hMf x) 2)
  have i2 : Integrable (fun x => k x ^ 2) μ :=
    ib (hk.pow 2) (M := Mk ^ 2) (fun x => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hMk x) 2)
  have i3 : Integrable (fun x => f x * k x) μ :=
    ib (hf.mul hk) (M := Mf * Mk) (fun x => by
      rw [norm_mul]; exact mul_le_mul (hMf x) (hMk x) (norm_nonneg _) ((norm_nonneg _).trans (hMf x)))
  have key : ∀ l : ℝ, 0 ≤ (∫ x, k x ^ 2 ∂μ) * (l * l) + (2 * ∫ x, f x * k x ∂μ) * l +
      ∫ x, f x ^ 2 ∂μ := by
    intro l
    have h0 : 0 ≤ ∫ x, (f x + l * k x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have e : ∫ x, (f x + l * k x) ^ 2 ∂μ =
        (∫ x, k x ^ 2 ∂μ) * (l * l) + (2 * ∫ x, f x * k x ∂μ) * l + ∫ x, f x ^ 2 ∂μ := by
      have : ∀ x, (f x + l * k x) ^ 2 = f x ^ 2 + (2 * l) * (f x * k x) + (l * l) * k x ^ 2 :=
        fun x => by ring
      simp_rw [this]
      have ia : Integrable (fun x => f x ^ 2 + (2 * l) * (f x * k x)) μ := i1.add (i3.const_mul _)
      rw [integral_add ia (i2.const_mul _), integral_add i1 (i3.const_mul _),
        integral_const_mul, integral_const_mul]
      ring
    rw [← e]; exact h0
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-! ### The smooth Poincare inequality -/

section Smooth

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

theorem gap234_c0_pos {q : ℝ} (hq : 0 < q) (Mb : ℝ) : 0 < pm_c0 q Mb := by
  unfold pm_c0 pm_kappa
  exact mul_pos (Real.exp_pos _) (lt_min one_pos (by linarith))

/-- `u(t) = ∫ (P_t f)² dμ = ∫ f · P_{2t} f dμ` (reversibility and the Markov property). -/
theorem gap234_u_eq [IsProbabilityMeasure P] {q Mb : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ}
    (hR : GapRef d ρ q B) (hq : 0 < q) (hB : HasCbBound 2 Mb B)
    (hW : IsBrownianFiltration P ℱ W) {f : Euc d → ℝ} {M : ℝ} (hf : gap234_Sm M f) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ x, sg P W q B t f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) =
      ∫ x, f x * sg P W q B (t + t) f x ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, hC1, hC⟩ := gap234_sg_sm hW hq hB ht
  have hst := hC hf t ⟨ht, le_rfl⟩
  have := (gap_reversible hR hq hB hW hf hst ht).2.2
  have e1 : ∀ x, sg P W q B t f x ^ 2 = sg P W q B t f x * sg P W q B t f x := fun x => sq _
  simp_rw [e1]
  rw [this]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show f x * sg P W q B t (sg P W q B t f) x = f x * sg P W q B (t + t) f x
  rw [← sg_markov_C2 hW hq.le (by norm_num) hB hf.1 hf.2 ht ht x]

/-- Exponential decay of `u(t) = ‖P_t f‖²_{L²(μ)}` for centered `f` (`pois_centered_decay`). -/
theorem gap234_decay [IsProbabilityMeasure P] {q Mb : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ}
    (hR : GapRef d ρ q B) (hq : 0 < q) (hB : HasCbBound 2 Mb B)
    (hW : IsBrownianFiltration P ℱ W) {f : Euc d → ℝ} {M : ℝ} (hf : gap234_Sm M f)
    (hcen : ∫ x, f x ∂(HRS.Whole.withDensityReal ρ) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, sg P W q B t f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
      (4 * (∫ x, ‖x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ)) * (M / pm_kappa q Mb) ^ 2) *
        Real.exp (-(2 * pm_c0 q Mb * t)) := by
  have : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := gap1_isProb hR
  have hm2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) (HRS.Whole.withDensityReal ρ) := (gap_moment hR).2.1
  set m2 : ℝ := ∫ x, ‖x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) with hm2def
  have hm20 : 0 ≤ m2 := integral_nonneg fun x => sq_nonneg _
  have hinv := ((pois_inv hq le_rfl hB hW (gap_invariant hR) hm2 hf.1 (gap234_sm_one hf)
    (hf.2 2 le_rfl)).2 t ht).2.2
  have hdec := fun x => pois_centered_decay hq le_rfl hB hW hf.1 (gap234_sm_zero hf)
    (gap234_sm_one hf) (hf.2 2 le_rfl) (HRS.Whole.withDensityReal ρ) hm2 (m2 := m2) le_rfl hcen ht
    hinv x
  have hκ : 0 < pm_kappa q Mb := Real.exp_pos _
  set E : ℝ := (pm_kappa q Mb)⁻¹ * Real.exp (-(pm_c0 q Mb) * t) * M with hE
  have hpt : ∀ x, sg P W q B t f x ^ 2 ≤ E ^ 2 * (2 * (‖x‖ ^ 2 + m2)) := fun x => by
    have h1 := (hdec x).trans (min_le_right _ _)
    rw [← sq_abs]
    have h2 : |sg P W q B t f x| ≤ E * (‖x‖ + Real.sqrt m2) := by
      refine h1.trans (le_of_eq ?_)
      rw [hE]
    have hE0 : 0 ≤ E := by
      have := gap234_sm_nonneg hf
      rw [hE]; positivity
    calc |sg P W q B t f x| ^ 2 ≤ (E * (‖x‖ + Real.sqrt m2)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = E ^ 2 * (‖x‖ + Real.sqrt m2) ^ 2 := by ring
      _ ≤ E ^ 2 * (2 * (‖x‖ ^ 2 + m2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have := Real.sq_sqrt hm20
          nlinarith [sq_nonneg (‖x‖ - Real.sqrt m2)]
  obtain ⟨C, hC1, hC⟩ := gap234_sg_sm hW hq hB ht
  have hst := hC hf t ⟨ht, le_rfl⟩
  have hint : Integrable (fun x => sg P W q B t f x ^ 2) (HRS.Whole.withDensityReal ρ) :=
    (integrable_const ((C * M) ^ 2)).mono' (hst.1.continuous.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (gap234_sm_zero hst x) 2)
  have hint2 : Integrable (fun x : Euc d => E ^ 2 * (2 * (‖x‖ ^ 2 + m2))) (HRS.Whole.withDensityReal ρ) :=
    ((hm2.add (integrable_const m2)).const_mul 2).const_mul _
  refine (integral_mono hint hint2 hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_const_mul, integral_add hm2 (integrable_const m2)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have e1 : E ^ 2 = (M / pm_kappa q Mb) ^ 2 * Real.exp (-(2 * pm_c0 q Mb * t)) := by
    rw [hE]
    have : Real.exp (-(pm_c0 q Mb) * t) ^ 2 = Real.exp (-(2 * pm_c0 q Mb * t)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [← this]; field_simp
  rw [e1]
  ring

/-- The right derivative of `s ↦ ∫ f (P_s f - f)/s dμ` at `0` is `-∫ ‖∇f‖² dμ`. -/
theorem gap234_deriv [IsProbabilityMeasure P] {q Mb : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ}
    (hR : GapRef d ρ q B) (hq : 0 < q) (hB : HasCbBound 2 Mb B)
    (hW : IsBrownianFiltration P ℱ W) {f : Euc d → ℝ} {M : ℝ} (hf : gap234_Sm M f) :
    Tendsto (fun s : ℝ => ∫ x, f x * ((sg P W q B s f x - f x) / s) ∂(HRS.Whole.withDensityReal ρ))
      (𝓝[>] 0) (𝓝 (-∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ))) := by
  have : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := gap1_isProb hR
  have hm2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) (HRS.Whole.withDensityReal ρ) := (gap_moment hR).2.1
  have hn := sgNoise_of_brownian hW
  have hBc : Continuous B := hB.1.continuous
  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hB.2 0 (Nat.zero_le _) y
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (hBb 0)
  have hM0 := gap234_sm_nonneg hf
  obtain ⟨Cm, hCm, hmom⟩ := sg_second_moment (d := d) q Mb hq 1 zero_le_one
  have hmom' := fun s hs x => hmom P ℱ W hW 2 (by norm_num) B hB s hs x
  obtain ⟨C, hC1, hC⟩ := gap234_sg_sm hW hq hB zero_le_one
  set a : ℝ := (d : ℝ) * M + M * Mb with ha
  set a' : ℝ := M * |q| with ha'
  have ha0 : 0 ≤ a := by positivity
  have ha'0 : 0 ≤ a' := by positivity
  have hLf : ∀ y, |kolmL q B f y| ≤ a + a' * ‖y‖ := gap234_L_growth hBb hf
  have hLc : Continuous (kolmL q B f) := kl_L_continuous q hBc hf.1
  have hbnd : ∀ r ∈ Icc (0 : ℝ) 1, ∀ x, |sg P W q B r (kolmL q B f) x| ≤
      a + a' * (1 + Cm * (1 + ‖x‖ ^ 2)) := fun r hr x =>
    (inv_sg_bound hW hq.le (m := 2) (by norm_num) hB hr.1 (fun y => hmom' r hr y) hLc ha'0 hLf x).2
  have hkol := pois_kolmogorov hq le_rfl hB hW hf.1 (gap234_sm_one hf) (hf.2 2 le_rfl)
  -- the difference quotient is dominated
  have hquot : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ x, |(sg P W q B s f x - f x) / s| ≤
      a + a' * (1 + Cm * (1 + ‖x‖ ^ 2)) := by
    intro s hs x
    have h1 := hkol.1 s hs.1.le x
    have h2 : sg P W q B s f x - f x = ∫ r in (0 : ℝ)..s, sg P W q B r (kolmL q B f) x := by
      rw [h1]; ring
    have h3 : ‖∫ r in (0 : ℝ)..s, sg P W q B r (kolmL q B f) x‖ ≤
        (a + a' * (1 + Cm * (1 + ‖x‖ ^ 2))) * |s - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => ?_)
      rw [Set.uIoc_of_le hs.1.le] at hr
      rw [Real.norm_eq_abs]
      exact hbnd r ⟨hr.1.le, hr.2.trans hs.2⟩ x
    rw [h2, abs_div, abs_of_pos hs.1, div_le_iff₀ hs.1]
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hs.1] at h3
    exact h3
  -- pointwise limit
  have hlim : ∀ x, Tendsto (fun s : ℝ => (sg P W q B s f x - f x) / s) (𝓝[>] 0)
      (𝓝 (kolmL q B f x)) := by
    intro x
    have h1 := hkol.2.1 x 0 le_rfl
    rw [ld_sg_zero hn hq.le (m := 2) (by norm_num) hB (kolmL q B f) x] at h1
    have h2 := (hasDerivWithinAt_iff_tendsto_slope.1 h1)
    have hI : Ici (0 : ℝ) \ {0} = Ioi 0 := by
      ext y
      simp only [mem_diff, mem_Ici, mem_singleton_iff, mem_Ioi]
      exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
    rw [hI] at h2
    refine h2.congr (fun s => ?_)
    rw [slope_def_field, ld_sg_zero hn hq.le (m := 2) (by norm_num) hB f x, sub_zero]
  have hconv : Tendsto (fun s : ℝ => ∫ x, f x * ((sg P W q B s f x - f x) / s)
      ∂(HRS.Whole.withDensityReal ρ)) (𝓝[>] 0)
      (𝓝 (∫ x, f x * kolmL q B f x ∂(HRS.Whole.withDensityReal ρ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => M * (a + a' * (1 + Cm * (1 + ‖x‖ ^ 2)))) ?_ ?_ ?_ ?_
    · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with s hs
      have hs' := hC hf s ⟨hs.1.le, hs.2⟩
      exact (hf.1.continuous.mul ((hs'.1.continuous.sub hf.1.continuous).div_const s)).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with s hs
      refine ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using gap234_sm_zero hf x) (hquot s hs x)
        (abs_nonneg _) hM0
    · have : Integrable (fun x : Euc d => a + a' * (1 + Cm * (1 + ‖x‖ ^ 2)))
          (HRS.Whole.withDensityReal ρ) :=
        (integrable_const a).add (((integrable_const (1 : ℝ)).add
          (((integrable_const (1 : ℝ)).add hm2).const_mul Cm)).const_mul a')
      exact this.const_mul M
    · exact ae_of_all _ fun x => (hlim x).const_mul (f x)
  have hdir := (gap_dirichlet hR hf.1 (gap234_sm_one hf) (gap234_sm_two hf)
    (hf.1.of_le (by norm_num)) (Cψ := M)
    (fun x => by have := gap234_sm_zero hf x; rwa [Real.norm_eq_abs] at this)
    (gap234_sm_one hf)).2.2
  have e1 : ∫ x, f x * kolmL q B f x ∂(HRS.Whole.withDensityReal ρ) =
      -∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
    have : ∀ x, f x * kolmL q B f x = kolmL q B f x * f x := fun x => mul_comm _ _
    simp_rw [this]
    rw [hdir]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact real_inner_self_eq_norm_sq _
  rw [← e1]
  exact hconv

set_option maxHeartbeats 1600000 in
/-- **GAP-3 (smooth Poincare inequality).**  For `GapRef d ρ q B`, `q > 0`, `B ∈ C_b^2`, a Brownian
filtration and `f` in the bounded `C²` class with `∫ f dμ = 0` (`μ = ρ dx`):
`c0 ∫ f² dμ ≤ ∫ ‖∇f‖² dμ` with `c0 = pm_c0 q Mb > 0`. -/
theorem gap_smooth [IsProbabilityMeasure P] {q Mb : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ}
    (hR : GapRef d ρ q B) (hq : 0 < q) (hB : HasCbBound 2 Mb B)
    (hW : IsBrownianFiltration P ℱ W) {f : Euc d → ℝ} {M : ℝ} (hf : gap234_Sm M f)
    (hcen : ∫ x, f x ∂(HRS.Whole.withDensityReal ρ) = 0) :
    pm_c0 q Mb * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
      ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  have hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := gap1_isProb hR
  have hn := sgNoise_of_brownian hW
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set c0 : ℝ := pm_c0 q Mb with hc0
  have hc00 : 0 < c0 := gap234_c0_pos hq Mb
  set u : ℝ → ℝ := fun t => ∫ x, sg P W q B t f x ^ 2 ∂μ with hu
  have hu0 : u 0 = ∫ x, f x ^ 2 ∂μ := by
    simp only [hu]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ld_sg_zero hn hq.le (m := 2) (by norm_num) hB f x]
  have hnn : ∀ t, 0 ≤ t → 0 ≤ u t := fun t _ => integral_nonneg fun x => sq_nonneg _
  have hgrad_nn : 0 ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rcases (hnn 0 le_rfl).eq_or_lt with hz | hpos
  · rw [← hu0, ← hz]
    simpa using hgrad_nn
  have hMf := gap234_sm_nonneg hf
  -- Cauchy-Schwarz: `u(t)² ≤ u(2t) u(0)`
  have hdbl : ∀ t, 0 ≤ t → u t ^ 2 ≤ u (2 * t) * u 0 := by
    intro t ht
    obtain ⟨C, hC1, hC⟩ := gap234_sg_sm hW hq hB (show 0 ≤ 2 * t by linarith)
    have hs2 := hC hf (2 * t) ⟨by linarith, le_rfl⟩
    have h1 : u t = ∫ x, f x * sg P W q B (2 * t) f x ∂μ := by
      simp only [hu]
      rw [gap234_u_eq hR hq hB hW hf ht]
      have : t + t = 2 * t := by ring
      rw [this]
    have h2 := gap234_cs (μ := μ) hf.1.continuous hs2.1.continuous (gap234_sm_zero hf)
      (gap234_sm_zero hs2)
    rw [h1, hu0]
    simpa [hu, mul_comm] using h2
  -- exponential decay
  have hbd : ∀ t, 0 ≤ t → u t ≤ (4 * (∫ x, ‖x‖ ^ 2 ∂μ) * (M / pm_kappa q Mb) ^ 2) *
      Real.exp (-(2 * c0 * t)) := fun t ht => gap234_decay hR hq hB hW hf hcen ht
  have hmain := gap_doubling hnn hdbl hbd hpos
  -- the derivative at 0
  have hlimL := gap234_deriv hR hq hB hW hf
  have hlimR : Tendsto (fun s : ℝ => (Real.exp (-(c0 * s)) - 1) / s * u 0) (𝓝[>] 0)
      (𝓝 (-c0 * u 0)) := by
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(c0 * s))) (-c0) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_mul c0).neg.exp
      simpa using this
    have h2 := h1.tendsto_slope_zero_right
    have h3 := h2.mul_const (u 0)
    refine h3.congr (fun s => ?_)
    simp [smul_eq_mul, div_eq_inv_mul]
  have hle : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫ x, f x * ((sg P W q B s f x - f x) / s) ∂μ ≤
      (Real.exp (-(c0 * s)) - 1) / s * u 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : 0 < s := hs
    obtain ⟨C, hC1, hC⟩ := gap234_sg_sm hW hq hB hs0.le
    have hss := hC hf s ⟨hs0.le, le_rfl⟩
    have iA : Integrable (fun x => f x * sg P W q B s f x) μ :=
      (integrable_const (M * (C * M))).mono' (hf.1.continuous.mul hss.1.continuous).aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [norm_mul]
          exact mul_le_mul (gap234_sm_zero hf x) (gap234_sm_zero hss x) (norm_nonneg _) hMf)
    have iB : Integrable (fun x => f x ^ 2) μ :=
      (integrable_const (M ^ 2)).mono' (hf.1.continuous.pow 2).aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (gap234_sm_zero hf x) 2)
    have e1 : ∫ x, f x * ((sg P W q B s f x - f x) / s) ∂μ =
        ((∫ x, f x * sg P W q B s f x ∂μ) - ∫ x, f x ^ 2 ∂μ) / s := by
      have : ∀ x, f x * ((sg P W q B s f x - f x) / s) =
          (f x * sg P W q B s f x - f x ^ 2) / s := fun x => by ring
      simp_rw [this]
      rw [integral_div, integral_sub iA iB]
    have e2 : ∫ x, f x * sg P W q B s f x ∂μ = u (s / 2) := by
      simp only [hu]
      rw [gap234_u_eq hR hq hB hW hf (show 0 ≤ s / 2 by linarith)]
      have : s / 2 + s / 2 = s := by ring
      rw [this]
    have h3 := hmain (s / 2) (by linarith)
    have e3 : -(2 * c0 * (s / 2)) = -(c0 * s) := by ring
    rw [e3] at h3
    rw [e1, e2, ← hu0, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hs0.le
    nlinarith [h3]
  have hfin := le_of_tendsto_of_tendsto hlimL hlimR hle
  rw [hu0] at hfin
  nlinarith [hfin]

end Smooth

/-- **GAP-3 (smooth Poincare inequality, probability space chosen).**  The constant `pm_c0 q Mb` works for
every bounded `C²` function of mean zero. -/
theorem gap_smooth_const {q Mb : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B)
    (hq : 0 < q) (hB : HasCbBound 2 Mb B) :
    ∃ c : ℝ, 0 < c ∧ ∀ {f : Euc d → ℝ} {M : ℝ}, gap234_Sm M f →
      ∫ x, f x ∂(HRS.Whole.withDensityReal ρ) = 0 →
      c * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  exact ⟨pm_c0 q Mb, gap234_c0_pos hq Mb, fun {f M} hf hcen => gap_smooth hR hq hB hW hf hcen⟩

end HRS.MS.Gap

end
