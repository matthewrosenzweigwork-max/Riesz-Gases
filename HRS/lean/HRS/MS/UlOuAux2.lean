import HRS.MS.UlOuAux1
import HRS.MS.LcEngAux1

/-!
# UL-2, part 2: the Gaussian law of the OU shift `lcU`

Setting.  `W` is a Brownian filtration, `ν ≥ 0` a constant viscosity, `G v = lcNoiseE W (fun _ => ν) v`
(a path in `Euc d`, `G_0 = 0`, independent Gaussian increments `G_v - G_u ~ N(0, 2ν(v-u) I)`), and
`lcU Q G 0 τ = G_τ - ∫_0^τ e^{-(τ-u)Q} Q G_u du` the pathwise Riemann-Stieltjes integral
`∫_0^τ e^{-(τ-u)Q} dG_u`.

Main result `ou_law`: `lcU Q G 0 τ` has law `ouLaw Q ν τ = N(0, Σ_τ)` (`0 ≤ τ`).

Route (no path-space Gaussian-process machinery).  Fix `ξ` and `ψ(u) = e^{-(τ-u)Qᵀ} ξ`, `χ = ψ'`.
Pathwise `⟨ξ, lcU⟩ = ⟨ξ, G_τ⟩ - ∫_0^τ ⟨χ(u), G_u⟩ du` (integration by parts, `ul2_pair_lcU`).  With
`h = τ/n`, `u_i = i h`, the right Riemann sums `Y_n = ⟨ξ, G_τ⟩ - h ∑_{i<n} ⟨χ(u_{i+1}), G_{u_{i+1}}⟩` converge
pathwise to `⟨ξ, lcU⟩` (`ul2_cell`, `ul2_tail`) and, by Abel summation (`ul2_abel`),
`Y_n = ∑_{j<n} ⟨b_j, G_{u_{j+1}} - G_{u_j}⟩` with `b_j = ξ - h ∑_{i=j}^{n-1} χ(u_{i+1})`.  The summands are
independent Gaussians (`lc_noise_indepFun`, `lc_noise_law`), so
`E exp(i Y_n) = exp(-ν h ∑_j |b_j|²)` (`ul2_ch_sum`); `b_j → ψ(u_j)` uniformly, hence
`E exp(i Y_n) → exp(-ν ∫_0^τ |ψ|²)` while dominated convergence gives `E exp(i Y_n) → E exp(i ⟨ξ,lcU⟩)`.
The identification of the characteristic function with that of `ouLaw` (`ou_charFun_integral`) and
`Measure.ext_of_charFun` conclude.

Helper lemmas carry the prefix `ul2_`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped InnerProduct ENNReal NNReal Matrix

noncomputable section

namespace HRS.MS.Ul

open HRS HRS.MS.Lc

variable {d : ℕ}

/-! ### Riemann sums with tags (uniform grids) -/

section Riemann

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- One cell of the grid `i τ/n`: for large `n`, `|∫_cell f - (τ/n) f(s)| ≤ (τ/n) ε` for every tag `s`
in the cell. -/
theorem ul2_cell {f : ℝ → F} (hf : Continuous f) {τ : ℝ} (hτ : 0 ≤ τ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, j < n → ∀ s ∈ Icc ((j : ℝ) * (τ / n)) (((j : ℝ) + 1) * (τ / n)),
      ‖(∫ u in ((j : ℝ) * (τ / n))..(((j : ℝ) + 1) * (τ / n)), f u) - (τ / n) • f s‖ ≤
        (τ / n) * ε := by
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := τ)).uniformContinuousOn_of_continuous hf.continuousOn) ε hε
  have hev : ∀ᶠ n : ℕ in atTop, τ / n < δ :=
    (tendsto_const_div_atTop_nhds_zero_nat τ).eventually (gt_mem_nhds hδ)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  intro j hj s hs
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set h := τ / n with hh
  have hh0 : 0 ≤ h := div_nonneg hτ hn0.le
  have hjn : ((j : ℝ) + 1) * h ≤ τ := by
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    calc ((j : ℝ) + 1) * h ≤ n * h := mul_le_mul_of_nonneg_right this hh0
      _ = τ := by rw [hh]; field_simp
  have hj0 : 0 ≤ (j : ℝ) * h := by positivity
  have hab : (j : ℝ) * h ≤ ((j : ℝ) + 1) * h := by nlinarith
  have hint := hf.intervalIntegrable (μ := volume) ((j : ℝ) * h) (((j : ℝ) + 1) * h)
  have e : (∫ u in ((j : ℝ) * h)..(((j : ℝ) + 1) * h), f u) - h • f s =
      ∫ u in ((j : ℝ) * h)..(((j : ℝ) + 1) * h), (f u - f s) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    congr 2
    ring
  rw [e]
  have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := (j : ℝ) * h)
    (b := ((j : ℝ) + 1) * h) (C := ε) (f := fun u => f u - f s) ?_
  · calc _ ≤ ε * |((j : ℝ) + 1) * h - (j : ℝ) * h| := key
      _ = h * ε := by rw [abs_of_nonneg (by nlinarith)]; ring
  · intro u hu
    rw [uIoc_of_le hab] at hu
    have hu' : u ∈ Icc 0 τ := ⟨hj0.trans hu.1.le, hu.2.trans hjn⟩
    have hs' : s ∈ Icc 0 τ := ⟨hj0.trans hs.1, hs.2.trans hjn⟩
    have hd : dist u s < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> nlinarith [hs.1, hs.2, hu.1, hu.2]
    have := hU u hu' s hs' hd
    rw [dist_eq_norm] at this
    exact this.le

/-- Tagged Riemann sums over `j ≤ i < n` approximate `∫_{j h}^{τ} f` up to `τ ε`, for every choice of
tags. -/
theorem ul2_tail {f : ℝ → F} (hf : Continuous f) {τ : ℝ} (hτ : 0 ≤ τ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ → ℝ,
      (∀ i < n, t i ∈ Icc ((i : ℝ) * (τ / n)) (((i : ℝ) + 1) * (τ / n))) →
      ∀ j ≤ n, ‖(∑ i ∈ Finset.Ico j n, (τ / n) • f (t i)) -
        ∫ u in ((j : ℝ) * (τ / n))..((n : ℝ) * (τ / n)), f u‖ ≤ τ * ε := by
  filter_upwards [ul2_cell hf hτ hε, eventually_ge_atTop 1] with n hn hn1 t ht j hj
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals_Ico (f := f) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) * (τ / n)) hj (fun k _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_add, Nat.cast_one] at hsplit
  rw [← hsplit, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ Finset.Ico j n, ‖(τ / n) • f (t i) -
      ∫ u in ((i : ℝ) * (τ / n))..(((i : ℝ) + 1) * (τ / n)), f u‖ ≤ (τ / n) * ε := by
    intro i hi
    rw [norm_sub_rev]
    exact hn i (Finset.mem_Ico.1 hi).2 (t i) (ht i (Finset.mem_Ico.1 hi).2)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have h1 : ((n - j : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n j
  have h2 : 0 ≤ (τ / n) * ε := by positivity
  calc ((n - j : ℕ) : ℝ) * ((τ / n) * ε) ≤ n * ((τ / n) * ε) := mul_le_mul_of_nonneg_right h1 h2
    _ = τ * ε := by field_simp

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- A sequence is eventually `ε`-close to `L` for every `ε` iff it converges. -/
theorem ul2_tendsto_of_eps {a : ℕ → F} {L : F} (h : ∀ ε > 0, ∀ᶠ n in atTop, ‖a n - L‖ ≤ ε) :
    Tendsto a atTop (𝓝 L) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [h (ε / 2) (half_pos hε)] with n hn
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hn (half_lt_self hε)

end Riemann

/-! ### Characteristic functions of the Gaussian increments of the noise -/

section Noise

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ} {ν : ℝ}

/-- The OU noise path `G v = W_{2νv}` as a path in `Euc d`. -/
abbrev ulG (W : ℝ≥0 → Ω → Fin d → ℝ) (ν : ℝ) (v : ℝ) (ω : Ω) : Euc d :=
  lcNoiseE W (fun _ => ν) v ω

theorem ul2_lcTau (ν v : ℝ) : lcTau (fun _ => ν) v = 2 * ν * v := by
  simp only [lcTau, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

theorem ul2_inner_toLp (b : Euc d) (z : Fin d → ℝ) :
    inner ℝ b (WithLp.toLp 2 z) = ∑ k, b k * z k := by
  simp [PiLp.inner_apply, mul_comm]

theorem ul2_ch_incr [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (hν : 0 ≤ ν)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (b : Euc d) :
    ∫ ω, Complex.exp (((inner ℝ b (ulG W ν v ω - ulG W ν u ω) : ℝ) : ℂ) * Complex.I) ∂P =
      Complex.exp (-(((2 * ν * (v - u) * ‖b‖ ^ 2 : ℝ) : ℂ) / 2)) := by
  have hc : Continuous fun _ : ℝ => ν := continuous_const
  obtain ⟨hlaw, -, -, -⟩ := lc_noise_law hW hc (fun _ => hν) hu huv
  have hsub : ∀ ω, ulG W ν v ω - ulG W ν u ω = WithLp.toLp 2
      (lcNoise W (fun _ => ν) v ω - lcNoise W (fun _ => ν) u ω) := fun ω => rfl
  simp_rw [hsub, ul2_inner_toLp]
  have hmeas : AEStronglyMeasurable (fun z : Fin d → ℝ =>
      Complex.exp (((∑ k, b k * z k : ℝ) : ℂ) * Complex.I))
      (Measure.pi fun _ : Fin d => gaussianReal 0 (lcTau (fun _ => ν) v -
        lcTau (fun _ => ν) u).toNNReal) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have h1 := hlaw.integral_comp hmeas
  simp only [Function.comp_def] at h1
  rw [h1]
  have hprod : ∀ z : Fin d → ℝ, Complex.exp (((∑ k, b k * z k : ℝ) : ℂ) * Complex.I) =
      ∏ k, Complex.exp (((b k * z k : ℝ) : ℂ) * Complex.I) := by
    intro z
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod (f := fun k (z : ℝ) => Complex.exp (((b k * z : ℝ) : ℂ) * Complex.I))]
  have hσ : ((lcTau (fun _ => ν) v - lcTau (fun _ => ν) u).toNNReal : ℝ) = 2 * ν * (v - u) := by
    rw [Real.coe_toNNReal _ (by rw [ul2_lcTau, ul2_lcTau]; nlinarith)]
    rw [ul2_lcTau, ul2_lcTau]; ring
  have hk : ∀ k, ∫ z, Complex.exp (((b k * z : ℝ) : ℂ) * Complex.I) ∂(gaussianReal 0
      (lcTau (fun _ => ν) v - lcTau (fun _ => ν) u).toNNReal) =
      Complex.exp (-(((2 * ν * (v - u) * (b k) ^ 2 : ℝ) : ℂ) / 2)) := by
    intro k
    have := charFun_gaussianReal (μ := 0) (v := (lcTau (fun _ => ν) v - lcTau (fun _ => ν) u).toNNReal) (b k)
    rw [charFun_apply_real] at this
    push_cast at this ⊢
    rw [hσ] at this
    rw [this]
    congr 1
    push_cast
    ring
  simp_rw [hk]
  rw [← Complex.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← Complex.ofReal_sum,
    ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]

theorem ul2_G_measurable (hW : IsBrownianFiltration P ℱ W) (s : ℝ) :
    Measurable (ulG W ν s) :=
  lc_noiseE_measurable hW s

theorem ul2_G_adapted (hW : IsBrownianFiltration P ℱ W) (hν : 0 ≤ ν) {s w : ℝ} (hsw : s ≤ w) :
    Measurable[ℱ (((lcTau (fun _ => ν) w).toNNReal : ℝ≥0) : ℝ)] (ulG W ν s) := by
  have h := lc_noise_adapted hW (continuous_const : Continuous fun _ : ℝ => ν) (fun _ => hν) hsw
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp h

/-- The partial sums `S_m = ∑_{j<m} ⟨b_j, G_{u_{j+1}} - G_{u_j}⟩`. -/
def ulS (W : ℝ≥0 → Ω → Fin d → ℝ) (ν : ℝ) (u : ℕ → ℝ) (b : ℕ → Euc d) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range m, inner ℝ (b j) (ulG W ν (u (j + 1)) ω - ulG W ν (u j) ω)

theorem ul2_S_measurable (hW : IsBrownianFiltration P ℱ W) (u : ℕ → ℝ) (b : ℕ → Euc d) (m : ℕ) :
    Measurable (ulS W ν u b m) := by
  unfold ulS
  refine Finset.measurable_sum _ fun j _ => ?_
  exact measurable_const.inner ((ul2_G_measurable hW _).sub (ul2_G_measurable hW _))

theorem ul2_S_adapted (hW : IsBrownianFiltration P ℱ W) (hν : 0 ≤ ν) {u : ℕ → ℝ}
    (hu : Monotone u) (b : ℕ → Euc d) (m : ℕ) :
    Measurable[ℱ (((lcTau (fun _ => ν) (u m)).toNNReal : ℝ≥0) : ℝ)] (ulS W ν u b m) := by
  unfold ulS
  refine Finset.measurable_sum _ fun j hj => ?_
  have hj' : j < m := Finset.mem_range.1 hj
  exact measurable_const.inner
    ((ul2_G_adapted hW hν (hu (Nat.succ_le_of_lt hj'))).sub (ul2_G_adapted hW hν (hu hj'.le)))

/-- **Characteristic function of the discrete stochastic integral.** -/
theorem ul2_ch_sum [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (hν : 0 ≤ ν)
    {u : ℕ → ℝ} (hu0 : 0 ≤ u 0) (hu : Monotone u) (b : ℕ → Euc d) (m : ℕ) :
    ∫ ω, Complex.exp ((ulS W ν u b m ω : ℂ) * Complex.I) ∂P =
      Complex.exp (-(((∑ j ∈ Finset.range m, 2 * ν * (u (j + 1) - u j) * ‖b j‖ ^ 2 : ℝ) : ℂ) / 2)) := by
  induction m with
  | zero => simp [ulS]
  | succ m ih =>
    have hS : ∀ ω, ulS W ν u b (m + 1) ω = ulS W ν u b m ω +
        inner ℝ (b m) (ulG W ν (u (m + 1)) ω - ulG W ν (u m) ω) := fun ω => by
      simp [ulS, Finset.sum_range_succ]
    simp_rw [hS]
    have hc : Continuous fun _ : ℝ => ν := continuous_const
    have hind : IndepFun (fun ω => lcNoise W (fun _ => ν) (u (m + 1)) ω -
        lcNoise W (fun _ => ν) (u m) ω) (ulS W ν u b m) P :=
      lc_noise_indepFun hW hc (fun _ => hν) (hu (Nat.le_succ m)) (ul2_S_adapted hW hν hu b m)
    have hF : Measurable fun z : Fin d → ℝ => inner ℝ (b m) (WithLp.toLp 2 z : Euc d) := by
      fun_prop
    have hind2 := hind.comp hF measurable_id
    have hexp : Measurable fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I) := by fun_prop
    have hind3 := hind2.comp hexp hexp
    have hm1 : (fun ω => Complex.exp ((((ulS W ν u b m ω +
        inner ℝ (b m) (ulG W ν (u (m + 1)) ω - ulG W ν (u m) ω) : ℝ)) : ℂ) * Complex.I)) =
        fun ω => Complex.exp (((inner ℝ (b m) (ulG W ν (u (m + 1)) ω - ulG W ν (u m) ω) : ℝ) : ℂ)
          * Complex.I) * Complex.exp ((ulS W ν u b m ω : ℂ) * Complex.I) := by
      funext ω
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hm1]
    have hG : Measurable fun ω => ulG W ν (u (m + 1)) ω - ulG W ν (u m) ω :=
      (ul2_G_measurable hW _).sub (ul2_G_measurable hW _)
    have hI : Measurable fun ω => inner ℝ (b m) (ulG W ν (u (m + 1)) ω - ulG W ν (u m) ω) :=
      measurable_const.inner hG
    have hmX := hexp.comp hI
    have hmS := hexp.comp (ul2_S_measurable hW (ν := ν) u b m)
    have hind4 : IndepFun (fun ω => Complex.exp (((inner ℝ (b m)
        (ulG W ν (u (m + 1)) ω - ulG W ν (u m) ω) : ℝ) : ℂ) * Complex.I))
        (fun ω => Complex.exp ((ulS W ν u b m ω : ℂ) * Complex.I)) P := hind3
    rw [hind4.integral_fun_mul_eq_mul_integral hmX.aestronglyMeasurable hmS.aestronglyMeasurable]
    rw [ih, ul2_ch_incr hW hν (hu0.trans (hu (Nat.zero_le m))) (hu (Nat.le_succ m)) (b m),
      ← Complex.exp_add, Finset.sum_range_succ]
    congr 1
    push_cast
    ring

end Noise


/-! ### Abel summation -/

theorem ul2_abel (g : ℕ → Euc d) (hg0 : g 0 = 0) (c : ℕ → Euc d) (ξ : Euc d) (h : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, inner ℝ (ξ - ∑ i ∈ Finset.Ico j n, h • c (i + 1)) (g (j + 1) - g j) =
      inner ℝ ξ (g n) - ∑ i ∈ Finset.range n, h * inner ℝ (c (i + 1)) (g (i + 1)) := by
  have e1 : ∀ j, inner ℝ (ξ - ∑ i ∈ Finset.Ico j n, h • c (i + 1)) (g (j + 1) - g j) =
      inner ℝ ξ (g (j + 1) - g j) -
        ∑ i ∈ Finset.Ico j n, h * inner ℝ (c (i + 1)) (g (j + 1) - g j) := by
    intro j
    rw [inner_sub_left, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left]
  simp_rw [e1]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [← inner_sum, Finset.sum_range_sub, hg0, sub_zero]
  · rw [Finset.sum_comm' (t' := Finset.range n) (s' := fun i => Finset.range (i + 1))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_sum, ← inner_sum, Finset.sum_range_sub, hg0, sub_zero]
    · intro j i
      simp only [Finset.mem_range, Finset.mem_Ico]
      omega

/-! ### The dual function `ψ` and its derivative `χ` -/

section Psi

variable (Q : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (ξ : Euc d)

/-- `ψ(u) = e^{-(τ-u)Qᵀ} ξ`. -/
def ulψ (u : ℝ) : Euc d := ContinuousLinearMap.adjoint (ouExp Q (τ - u)) ξ

/-- `χ(u) = Qᵀ ψ(u) = ψ'(u)`. -/
def ulχ (u : ℝ) : Euc d := ContinuousLinearMap.adjoint (lcQ Q) (ulψ Q τ ξ u)

theorem ulψ_cont : Continuous (ulψ Q τ ξ) :=
  (ul2_adj_cont Q ξ).comp (continuous_const.sub continuous_id)

theorem ulχ_cont : Continuous (ulχ Q τ ξ) :=
  (ContinuousLinearMap.adjoint (lcQ Q)).continuous.comp (ulψ_cont Q τ ξ)

theorem ulψ_self : ulψ Q τ ξ τ = ξ := by
  simp [ulψ, ouExp_zero, ← ContinuousLinearMap.star_eq_adjoint]

theorem ulψ_hasDerivAt (u : ℝ) : HasDerivAt (ulψ Q τ ξ) (ulχ Q τ ξ u) u := by
  have hA : ∀ u, ulψ Q τ ξ u = (NormedSpace.exp ((u - τ) • star (lcQ Q))) ξ := by
    intro u
    unfold ulψ
    rw [ul2_adj_eq, neg_sub]
  have hfun : ulψ Q τ ξ = fun u => (NormedSpace.exp ((u - τ) • star (lcQ Q))) ξ := funext hA
  rw [hfun]
  have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (star (lcQ Q)) (u - τ)
  have h2 := h1.scomp u ((hasDerivAt_id u).sub_const τ)
  have h3 := h2.clm_apply (hasDerivAt_const u ξ)
  refine h3.congr_deriv ?_
  unfold ulχ
  rw [hA u, ContinuousLinearMap.star_eq_adjoint]
  simp

/-- `⟨ξ, e^{-(τ-u)Q} Q z⟩ = ⟨χ(u), z⟩`. -/
theorem ulχ_pair (u : ℝ) (z : Euc d) :
    inner ℝ ξ (ouExp Q (τ - u) (lcQ Q z)) = inner ℝ (ulχ Q τ ξ u) z := by
  unfold ulχ ulψ
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

theorem ul2_pair_lcU {g : ℝ → Euc d} (hg : Continuous g) (hg0 : g 0 = 0) :
    inner ℝ ξ (lcU Q g 0 τ) = inner ℝ ξ (g τ) - ∫ u in (0 : ℝ)..τ, inner ℝ (ulχ Q τ ξ u) (g u) := by
  unfold lcU
  rw [hg0, sub_zero, inner_sub_right]
  congr 1
  have hc : Continuous fun u : ℝ => (NormedSpace.exp ((-(τ - u)) • lcQ Q)) (lcQ Q (g u - 0)) := by
    have h1 : Continuous fun u : ℝ => NormedSpace.exp ((-(τ - u)) • lcQ Q) :=
      NormedSpace.exp_continuous.comp ((continuous_const.sub continuous_id).neg.smul continuous_const)
    exact h1.clm_apply ((lcQ Q).continuous.comp (hg.sub continuous_const))
  have := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ ξ) (hc.intervalIntegrable (μ := volume) 0 τ)
  simp only [innerSL_apply_apply] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [sub_zero]
  exact ulχ_pair Q τ ξ u (g u)

theorem ul2_psi_int : ∫ u in (0 : ℝ)..τ, ‖ulψ Q τ ξ u‖ ^ 2 =
    ∫ v in (0 : ℝ)..τ, ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2 := by
  have := intervalIntegral.integral_comp_sub_left
    (fun v => ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2) (a := 0) (b := τ) τ
  simpa [ulψ] using this

end Psi


/-! ### Pathwise limit and variance limit of the discretisation -/

section Limit

variable (Q : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (ξ : Euc d)

/-- The grid `u_i = i τ / n`. -/
def ulGrid (τ : ℝ) (n i : ℕ) : ℝ := (i : ℝ) * (τ / n)

/-- The coefficients `b_j = ξ - h ∑_{i=j}^{n-1} χ(u_{i+1})`, `h = τ/n`. -/
def ulB (n j : ℕ) : Euc d :=
  ξ - ∑ i ∈ Finset.Ico j n, (τ / n) • ulχ Q τ ξ (ulGrid τ n (i + 1))

theorem ulGrid_zero (n : ℕ) : ulGrid τ n 0 = 0 := by simp [ulGrid]

theorem ulGrid_mono (hτ : 0 ≤ τ) (n : ℕ) : Monotone (ulGrid τ n) := by
  intro i j hij
  unfold ulGrid
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

theorem ulGrid_top {n : ℕ} (hn : 1 ≤ n) : ulGrid τ n n = τ := by
  have : (n : ℝ) ≠ 0 := by positivity
  unfold ulGrid
  field_simp

theorem ulGrid_succ_sub (n j : ℕ) : ulGrid τ n (j + 1) - ulGrid τ n j = τ / n := by
  unfold ulGrid
  push_cast
  ring

theorem ulGrid_mem {n : ℕ} (hτ : 0 ≤ τ) (hn : 1 ≤ n) {j : ℕ} (hj : j ≤ n) :
    ulGrid τ n j ∈ Icc 0 τ := by
  refine ⟨by rw [← ulGrid_zero τ n]; exact ulGrid_mono τ hτ n (Nat.zero_le j), ?_⟩
  exact (ulGrid_mono τ hτ n hj).trans (ulGrid_top τ hn).le

/-- Right Riemann sums converge. -/
theorem ul2_RS_right {f : ℝ → ℝ} (hf : Continuous f) (hτ : 0 ≤ τ) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (τ / n) * f (ulGrid τ n (i + 1))) atTop
      (𝓝 (∫ u in (0 : ℝ)..τ, f u)) := by
  refine ul2_tendsto_of_eps fun ε hε => ?_
  have hε' : 0 < ε / (τ + 1) := by positivity
  filter_upwards [ul2_tail hf hτ hε', eventually_ge_atTop 1] with n hn hn1
  have h := hn (fun i => ulGrid τ n (i + 1)) (fun i _ => by
    unfold ulGrid
    push_cast
    exact ⟨by nlinarith [show (0:ℝ) ≤ τ / n by positivity], le_rfl⟩) 0 (Nat.zero_le n)
  have e : (n : ℝ) * (τ / n) = τ := by
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Nat.cast_zero, zero_mul, e, ← Finset.range_eq_Ico] at h
  simp only [smul_eq_mul, Real.norm_eq_abs] at h
  rw [Real.norm_eq_abs]
  refine h.trans ?_
  calc τ * (ε / (τ + 1)) = ε * (τ / (τ + 1)) := by ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) hε.le
    _ = ε := mul_one ε

/-- Left Riemann sums converge. -/
theorem ul2_RS_left {f : ℝ → ℝ} (hf : Continuous f) (hτ : 0 ≤ τ) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (τ / n) * f (ulGrid τ n i)) atTop
      (𝓝 (∫ u in (0 : ℝ)..τ, f u)) := by
  refine ul2_tendsto_of_eps fun ε hε => ?_
  have hε' : 0 < ε / (τ + 1) := by positivity
  filter_upwards [ul2_tail hf hτ hε', eventually_ge_atTop 1] with n hn hn1
  have h := hn (fun i => ulGrid τ n i) (fun i _ => by
    unfold ulGrid
    exact ⟨le_rfl, by nlinarith [show (0:ℝ) ≤ τ / n by positivity]⟩) 0 (Nat.zero_le n)
  have e : (n : ℝ) * (τ / n) = τ := by
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Nat.cast_zero, zero_mul, e, ← Finset.range_eq_Ico] at h
  simp only [smul_eq_mul, Real.norm_eq_abs] at h
  rw [Real.norm_eq_abs]
  refine h.trans ?_
  calc τ * (ε / (τ + 1)) = ε * (τ / (τ + 1)) := by ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) hε.le
    _ = ε := mul_one ε

/-- **Pathwise limit.**  For a continuous path with `g 0 = 0` the discrete stochastic integrals
converge to `⟨ξ, lcU Q g 0 τ⟩`. -/
theorem ul2_path_limit {g : ℝ → Euc d} (hg : Continuous g) (hg0 : g 0 = 0) (hτ : 0 ≤ τ) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n,
      inner ℝ (ulB Q τ ξ n j) (g (ulGrid τ n (j + 1)) - g (ulGrid τ n j))) atTop
      (𝓝 (inner ℝ ξ (lcU Q g 0 τ))) := by
  have hf : Continuous fun u => inner ℝ (ulχ Q τ ξ u) (g u) := (ulχ_cont Q τ ξ).inner hg
  have hR := (tendsto_const_nhds (x := inner ℝ ξ (g τ))).sub (ul2_RS_right τ hf hτ)
  rw [ul2_pair_lcU Q τ ξ hg hg0]
  refine hR.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have := ul2_abel (fun k => g (ulGrid τ n k)) (by simp [ulGrid_zero, hg0])
    (fun k => ulχ Q τ ξ (ulGrid τ n k)) ξ (τ / n) n
  simp only [ulGrid_top τ hn] at this
  unfold ulB
  rw [this]

/-- The coefficients `b_j` are uniformly close to `ψ(u_j)`. -/
theorem ul2_B_close (hτ : 0 ≤ τ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j ≤ n, ‖ulB Q τ ξ n j - ulψ Q τ ξ (ulGrid τ n j)‖ ≤ ε := by
  have hε' : 0 < ε / (τ + 1) := by positivity
  filter_upwards [ul2_tail (ulχ_cont Q τ ξ) hτ hε', eventually_ge_atTop 1] with n hn hn1 j hj
  have h := hn (fun i => ulGrid τ n (i + 1)) (fun i _ => by
    unfold ulGrid
    push_cast
    exact ⟨by nlinarith [show (0:ℝ) ≤ τ / n by positivity], le_rfl⟩) j hj
  have e : (n : ℝ) * (τ / n) = τ := by
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hF : ∫ u in ((j : ℝ) * (τ / n))..((n : ℝ) * (τ / n)), ulχ Q τ ξ u =
      ξ - ulψ Q τ ξ (ulGrid τ n j) := by
    rw [e]
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := ulψ Q τ ξ)
      (f' := ulχ Q τ ξ) (a := ((j : ℝ) * (τ / n))) (b := τ) (fun u _ => ulψ_hasDerivAt Q τ ξ u)
      ((ulχ_cont Q τ ξ).intervalIntegrable _ _)
    rw [this, ulψ_self]
    rfl
  rw [hF] at h
  have e2 : ulB Q τ ξ n j - ulψ Q τ ξ (ulGrid τ n j) =
      -((∑ i ∈ Finset.Ico j n, (τ / n) • ulχ Q τ ξ (ulGrid τ n (i + 1))) -
        (ξ - ulψ Q τ ξ (ulGrid τ n j))) := by
    unfold ulB
    abel
  rw [e2, norm_neg]
  refine h.trans ?_
  calc τ * (ε / (τ + 1)) = ε * (τ / (τ + 1)) := by ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) hε.le
    _ = ε := mul_one ε

theorem ul2_sq_close {x y : Euc d} {K ε : ℝ} (hK : ‖y‖ ≤ K) (hε : 0 ≤ ε) (hxy : ‖x - y‖ ≤ ε) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ ε * (2 * K + ε) := by
  have h1 : ‖x‖ ≤ ‖y‖ + ε := by
    have := norm_le_norm_add_norm_sub' x y
    linarith
  have h2 : ‖y‖ ≤ ‖x‖ + ε := by
    have := norm_sub_norm_le y x
    rw [norm_sub_rev] at this
    linarith
  have hx0 := norm_nonneg x
  have hy0 := norm_nonneg y
  rw [abs_le]
  constructor <;> nlinarith

/-- **Variance limit.**  `h ∑_j |b_j|² → ∫_0^τ |ψ|²`. -/
theorem ul2_V_limit (hτ : 0 ≤ τ) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, (τ / n) * ‖ulB Q τ ξ n j‖ ^ 2) atTop
      (𝓝 (∫ u in (0 : ℝ)..τ, ‖ulψ Q τ ξ u‖ ^ 2)) := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := τ)).exists_bound_of_continuousOn
    (ulψ_cont Q τ ξ).continuousOn
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hτ⟩)
  have hR := ul2_RS_left τ (f := fun u => ‖ulψ Q τ ξ u‖ ^ 2) ((ulψ_cont Q τ ξ).norm.pow 2) hτ
  refine ul2_tendsto_of_eps fun ε hε => ?_
  have hR' := (Metric.tendsto_nhds.1 hR) (ε / 2) (half_pos hε)
  have hpos : 0 < 2 * (τ * (2 * K + 1) + 1) := by positivity
  set ε' := min 1 (ε / (2 * (τ * (2 * K + 1) + 1))) with hε'
  have hε'0 : 0 < ε' := lt_min one_pos (by positivity)
  filter_upwards [hR', ul2_B_close Q τ ξ hτ hε'0, eventually_ge_atTop 1] with n hn1 hn2 hn3
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn3
  have hh : 0 ≤ τ / n := by positivity
  set a := ∑ j ∈ Finset.range n, (τ / n) * ‖ulB Q τ ξ n j‖ ^ 2 with ha
  set a' := ∑ j ∈ Finset.range n, (τ / n) * ‖ulψ Q τ ξ (ulGrid τ n j)‖ ^ 2 with ha'
  have hdiff : |a - a'| ≤ ε / 2 := by
    have : a - a' = ∑ j ∈ Finset.range n, (τ / n) *
        (‖ulB Q τ ξ n j‖ ^ 2 - ‖ulψ Q τ ξ (ulGrid τ n j)‖ ^ 2) := by
      rw [ha, ha', ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j ∈ Finset.range n, |(τ / n) * (‖ulB Q τ ξ n j‖ ^ 2 -
        ‖ulψ Q τ ξ (ulGrid τ n j)‖ ^ 2)| ≤ (τ / n) * (ε' * (2 * K + ε')) := by
      intro j hj
      have hj' : j ≤ n := (Finset.mem_range.1 hj).le
      rw [abs_mul, abs_of_nonneg hh]
      refine mul_le_mul_of_nonneg_left (ul2_sq_close ?_ hε'0.le (hn2 j hj')) hh
      exact hK _ (ulGrid_mem τ hτ hn3 hj')
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e : (n : ℝ) * (τ / n) = τ := by field_simp
    have hε1 : ε' ≤ 1 := min_le_left _ _
    have hε2 : ε' ≤ ε / (2 * (τ * (2 * K + 1) + 1)) := min_le_right _ _
    calc (n : ℝ) * ((τ / n) * (ε' * (2 * K + ε'))) = τ * (ε' * (2 * K + ε')) := by
          rw [← mul_assoc, e]
      _ ≤ τ * (ε' * (2 * K + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hτ
          exact mul_le_mul_of_nonneg_left (by linarith) hε'0.le
      _ = (τ * (2 * K + 1)) * ε' := by ring
      _ ≤ (τ * (2 * K + 1)) * (ε / (2 * (τ * (2 * K + 1) + 1))) :=
          mul_le_mul_of_nonneg_left hε2 (by positivity)
      _ ≤ ε / 2 := by
          rw [← mul_div_assoc, div_le_div_iff₀ hpos two_pos]
          nlinarith [mul_nonneg hτ (by linarith : (0:ℝ) ≤ 2 * K + 1)]
  rw [dist_eq_norm, Real.norm_eq_abs] at hn1
  rw [Real.norm_eq_abs]
  calc |a - ∫ u in (0 : ℝ)..τ, ‖ulψ Q τ ξ u‖ ^ 2| ≤ |a - a'| + |a' - ∫ u in (0 : ℝ)..τ, ‖ulψ Q τ ξ u‖ ^ 2| :=
        abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hdiff hn1.le
    _ = ε := by ring

end Limit


/-! ### The law of `lcU` -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ} {ν : ℝ} (Q : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (ξ : Euc d)

/-- Characteristic function of `⟨ξ, lcU Q G 0 τ⟩`. -/
theorem ul2_charFun_lcU [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ) :
    ∫ ω, Complex.exp (((inner ℝ ξ (lcU Q (fun v => ulG W ν v ω) 0 τ) : ℝ) : ℂ) * Complex.I) ∂P =
      Complex.exp (-(((ν * ∫ v in (0 : ℝ)..τ,
        ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2 : ℝ) : ℂ))) := by
  have hc : Continuous fun _ : ℝ => ν := continuous_const
  have hexp : Measurable fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I) := by fun_prop
  have hGc : ∀ ω, Continuous fun v => ulG W ν v ω := fun ω => lc_noiseE_cont hW hc ω
  have h1 : ∀ n : ℕ, ∫ ω, Complex.exp ((ulS W ν (ulGrid τ n) (ulB Q τ ξ n) n ω : ℂ) * Complex.I) ∂P =
      Complex.exp (-(((2 * ν * ∑ j ∈ Finset.range n, (τ / n) * ‖ulB Q τ ξ n j‖ ^ 2 : ℝ) : ℂ) / 2)) := by
    intro n
    rw [ul2_ch_sum hW hν (by rw [ulGrid_zero]) (ulGrid_mono τ hτ n) (ulB Q τ ξ n) n]
    have : ∑ j ∈ Finset.range n, 2 * ν * (ulGrid τ n (j + 1) - ulGrid τ n j) *
        ‖ulB Q τ ξ n j‖ ^ 2 = 2 * ν * ∑ j ∈ Finset.range n, (τ / n) * ‖ulB Q τ ξ n j‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ulGrid_succ_sub]
      ring
    rw [this]
  have h2 : Tendsto (fun n : ℕ => ∫ ω, Complex.exp
      ((ulS W ν (ulGrid τ n) (ulB Q τ ξ n) n ω : ℂ) * Complex.I) ∂P) atTop
      (𝓝 (∫ ω, Complex.exp (((inner ℝ ξ (lcU Q (fun v => ulG W ν v ω) 0 τ) : ℝ) : ℂ) *
        Complex.I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (hexp.comp (ul2_S_measurable hW _ _ n)).aestronglyMeasurable)
      (integrable_const 1) (fun n => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => ?_)
    · rw [Complex.norm_exp_ofReal_mul_I]
    · have hlim0 := ul2_path_limit Q τ ξ (hGc ω) (lc_noiseE_zero (ν := fun _ => ν) hW ω) hτ
      have hlim : Tendsto (fun n : ℕ => ulS W ν (ulGrid τ n) (ulB Q τ ξ n) n ω) atTop
          (𝓝 (inner ℝ ξ (lcU Q (fun v => ulG W ν v ω) 0 τ))) := by
        unfold ulS
        exact hlim0
      have hcont : Continuous fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I) := by fun_prop
      exact (hcont.tendsto _).comp hlim
  have h3 : Tendsto (fun n : ℕ => Complex.exp (-(((2 * ν * ∑ j ∈ Finset.range n,
      (τ / n) * ‖ulB Q τ ξ n j‖ ^ 2 : ℝ) : ℂ) / 2))) atTop
      (𝓝 (Complex.exp (-(((ν * ∫ v in (0 : ℝ)..τ,
        ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2 : ℝ) : ℂ))))) := by
    have hV := ul2_V_limit Q τ ξ hτ
    rw [ul2_psi_int] at hV
    have hcont : Continuous fun r : ℝ => Complex.exp (-(((2 * ν * r : ℝ) : ℂ) / 2)) := by
      fun_prop
    have := (hcont.tendsto _).comp hV
    have e2 : Complex.exp (-(((2 * ν * ∫ v in (0 : ℝ)..τ,
        ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2 : ℝ) : ℂ) / 2)) =
        Complex.exp (-(((ν * ∫ v in (0 : ℝ)..τ,
        ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2 : ℝ) : ℂ))) := by
      congr 1
      push_cast
      ring
    rw [← e2]
    exact this
  simp_rw [h1] at h2
  exact tendsto_nhds_unique h3 h2 |>.symm

/-- **`ou_law`.**  For `ν ≥ 0`, `τ ≥ 0` the OU shift `lcU Q G 0 τ`, `G = lcNoiseE W (fun _ => ν)`,
has law `ouLaw Q ν τ = N(0, 2ν ∫_0^τ e^{-vQ} e^{-vQᵀ} dv)`. -/
theorem ou_law [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ) :
    HasLaw (fun ω => lcU Q (fun v => lcNoiseE W (fun _ => ν) v ω) 0 τ) (ouLaw Q ν τ) P := by
  have hc : Continuous fun _ : ℝ => ν := continuous_const
  have hGm : ∀ v, Measurable fun ω => ulG W ν v ω := fun v => ul2_G_measurable hW v
  have hGc : ∀ ω, Continuous fun v => ulG W ν v ω := fun ω => lc_noiseE_cont hW hc ω
  have hm : Measurable fun ω => lcU Q (fun v => ulG W ν v ω) 0 τ := lc4_meas_lcU_fixed Q hGm hGc 0 τ
  refine ⟨hm.aemeasurable, ?_⟩
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [ou_charFun_integral Q hν hτ, charFun_apply, integral_map hm.aemeasurable
    (by fun_prop : AEStronglyMeasurable _ _)]
  simp_rw [real_inner_comm ξ]
  exact ul2_charFun_lcU Q τ ξ hW hν hτ

end Main

end HRS.MS.Ul
