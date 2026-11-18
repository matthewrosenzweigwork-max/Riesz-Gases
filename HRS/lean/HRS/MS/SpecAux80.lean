import HRS.MS.SpecAux79

/-!
# S8L: Gaussian log-Sobolev inequality for `C²` functions in `H¹(γ)` (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_gauss_lsi_cs0` (no shift), cut-off lemmas, and
`s8p_gauss_lsi`: for `u ∈ C²` with `u² gd` and `‖Du‖² gd` integrable, `u² log u² gd` is integrable and
`Ent_γ(u²) ≤ 2 ∫ ‖Du‖² dγ` (cut-off `χ(x/R) u`, then Fatou).
-/

noncomputable section

open MeasureTheory Real Filter Topology

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem s8p_gauss_lsi_cs0 {u : V → ℝ} (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) :
    (∫ x, (u x ^ 2 * Real.log (u x ^ 2)) * s8p_gd x) -
        (∫ x, u x ^ 2 * s8p_gd x) * Real.log (∫ x, u x ^ 2 * s8p_gd x) ≤
      2 * ∫ x, ‖fderiv ℝ u x‖ ^ 2 * s8p_gd x := by
  obtain ⟨B, hB⟩ := hu.continuous.bounded_above_of_compact_support hcs
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεn
  have hεn0 : ∀ n, 0 < εn n := fun n => by simp only [hεn]; positivity
  have hεn1 : Tendsto εn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- bound for t log t on [0, B^2 + 1]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := B ^ 2 + 1)).exists_bound_of_continuousOn
    (Real.continuous_mul_log.continuousOn)
  have hu2 : ∀ x, u x ^ 2 ≤ B ^ 2 := fun x => by
    have := hB x; rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (u x), sq_abs (u x)]
  have hu2c : Continuous fun x => u x ^ 2 := hu.continuous.pow 2
  -- the left integral converges
  have h1 : Tendsto (fun n => ∫ x, ((u x ^ 2 + εn n) * Real.log (u x ^ 2 + εn n)) * s8p_gd x) atTop
      (𝓝 (∫ x, (u x ^ 2 * Real.log (u x ^ 2)) * s8p_gd x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => C * s8p_gd x) ?_ ?_ ?_ ?_
    · intro n
      exact ((Real.continuous_mul_log.comp (hu2c.add continuous_const)).mul s8p_gd_continuous).aestronglyMeasurable
    · exact s8p_gd_integrable.const_mul C
    · intro n
      refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le]
      refine mul_le_mul_of_nonneg_right ?_ (s8p_gd_pos x).le
      have hn : εn n ≤ 1 := by
        simp only [hεn]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have := hC (u x ^ 2 + εn n) ⟨by have := hεn0 n; positivity, by have := hu2 x; linarith⟩
      simpa using this
    · refine Filter.Eventually.of_forall fun x => ?_
      have : Tendsto (fun n => u x ^ 2 + εn n) atTop (𝓝 (u x ^ 2)) := by
        simpa using tendsto_const_nhds.add hεn1
      have := (Real.continuous_mul_log.tendsto (u x ^ 2)).comp this
      exact this.mul_const _
  have h2 : Tendsto (fun n => (∫ x, (u x ^ 2 + εn n) * s8p_gd x) *
      Real.log (∫ x, (u x ^ 2 + εn n) * s8p_gd x)) atTop
      (𝓝 ((∫ x, u x ^ 2 * s8p_gd x) * Real.log (∫ x, u x ^ 2 * s8p_gd x))) := by
    have hm : ∀ n, ∫ x, (u x ^ 2 + εn n) * s8p_gd x = (∫ x, u x ^ 2 * s8p_gd x) + εn n := fun n => by
      have hint : Integrable (fun x => u x ^ 2 * s8p_gd x) := by
        refine Integrable.mono' (s8p_gd_integrable.const_mul (B ^ 2))
          (hu2c.mul s8p_gd_continuous).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
        rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_right (hu2 x) (s8p_gd_pos x).le
      simp_rw [add_mul]
      rw [integral_add hint (s8p_gd_integrable.const_mul _) |> fun h => h, integral_const_mul,
        s8p_gd_integral]
      ring
    simp_rw [hm]
    have : Tendsto (fun n => (∫ x, u x ^ 2 * s8p_gd x) + εn n) atTop (𝓝 (∫ x, u x ^ 2 * s8p_gd x)) := by
      simpa using tendsto_const_nhds.add hεn1
    exact (Real.continuous_mul_log.tendsto _).comp this
  have key : ∀ n, (∫ x, ((u x ^ 2 + εn n) * Real.log (u x ^ 2 + εn n)) * s8p_gd x) -
      (∫ x, (u x ^ 2 + εn n) * s8p_gd x) * Real.log (∫ x, (u x ^ 2 + εn n) * s8p_gd x) ≤
      2 * ∫ x, ‖fderiv ℝ u x‖ ^ 2 * s8p_gd x := fun n => s8p_gauss_lsi_cs hu hcs (hεn0 n)
  exact le_of_tendsto_of_tendsto (h1.sub h2) tendsto_const_nhds (Filter.Eventually.of_forall key)


/-- A smooth cutoff. -/
theorem s8p_cutoff : ∃ χ : V → ℝ, ContDiff ℝ 2 χ ∧ (∃ R0 : ℝ, ∀ x, R0 < ‖x‖ → χ x = 0) ∧
    (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
    (∀ x, ‖x‖ ≤ 1 → χ x = 1) ∧ ∃ Bχ : ℝ, 0 ≤ Bχ ∧ ∀ x, ‖fderiv ℝ χ x‖ ≤ Bχ := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have hcs : HasCompactSupport (fun x => b x) := b.hasCompactSupport
  have hcd : ContDiff ℝ 2 (fun x => b x) := b.contDiff
  obtain ⟨B, hB⟩ := ((hcd.continuous_fderiv (by norm_num))).bounded_above_of_compact_support (hcs.fderiv ℝ)
  refine ⟨fun x => b x, hcd, ⟨2, fun x hx => ?_⟩, fun x => ⟨b.nonneg, b.le_one⟩, fun x hx => ?_,
    max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩
  · exact b.zero_of_le_dist (by simpa [dist_eq_norm] using hx.le)
  · exact b.one_of_mem_closedBall (by simpa using hx)

/-- Cut-off functions `u_R = χ(x/R) u`. -/
theorem s8p_cutoff_u {u : V → ℝ} (hu : ContDiff ℝ 2 u) {χ : V → ℝ} (hχ : ContDiff ℝ 2 χ)
    {R0 : ℝ} (hR0 : ∀ x, R0 < ‖x‖ → χ x = 0) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ 2 (fun x => χ (R⁻¹ • x) * u x) ∧ HasCompactSupport (fun x => χ (R⁻¹ • x) * u x) := by
  refine ⟨(hχ.comp (contDiff_const.smul contDiff_id)).mul hu, ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (0 : V) (R * |R0| + R * 0 + R)) (fun x hx => ?_)
  have hx' : R * |R0| + R * 0 + R < ‖x‖ := by simpa using hx
  have : R0 < ‖R⁻¹ • x‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
    rw [lt_inv_mul_iff₀ hR]
    nlinarith [le_abs_self R0]
  simp [hR0 _ this]


theorem s8p_cutoff_grad {u : V → ℝ} (hu : ContDiff ℝ 2 u) {χ : V → ℝ} (hχ : ContDiff ℝ 2 χ)
    (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {Bχ : ℝ} (hB : ∀ x, ‖fderiv ℝ χ x‖ ≤ Bχ) {R : ℝ} (hR : 0 < R) (x : V) :
    ‖fderiv ℝ (fun x => χ (R⁻¹ • x) * u x) x‖ ≤ ‖fderiv ℝ u x‖ + |u x| * (Bχ / R) := by
  have h1 : HasFDerivAt (fun x : V => R⁻¹ • x) (R⁻¹ • ContinuousLinearMap.id ℝ V) x := by
    exact (hasFDerivAt_id x).const_smul R⁻¹
  have h2 : HasFDerivAt (fun x : V => χ (R⁻¹ • x)) (R⁻¹ • fderiv ℝ χ (R⁻¹ • x)) x := by
    have := (hχ.differentiable (by norm_num) (R⁻¹ • x)).hasFDerivAt.comp x h1
    refine this.congr_fderiv ?_
    ext v; simp
  have h3 := h2.mul ((hu.differentiable (by norm_num)) x).hasFDerivAt
  have h4 : fderiv ℝ (fun x => χ (R⁻¹ • x) * u x) x = _ := h3.fderiv
  rw [h4]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
  have a1 := h01 (R⁻¹ • x)
  have a2 : ‖fderiv ℝ χ (R⁻¹ • x)‖ ≤ Bχ := hB _
  have a3 : |χ (R⁻¹ • x)| ≤ 1 := by rw [abs_of_nonneg a1.1]; exact a1.2
  calc |χ (R⁻¹ • x)| * ‖fderiv ℝ u x‖ + |u x| * (R⁻¹ * ‖fderiv ℝ χ (R⁻¹ • x)‖)
      ≤ 1 * ‖fderiv ℝ u x‖ + |u x| * (R⁻¹ * Bχ) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right a3 (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a2 (by positivity)) (abs_nonneg _)
    _ = _ := by ring


theorem s8p_mul_log_ge (t : ℝ) (ht : 0 ≤ t) : t - 1 ≤ t * Real.log t := by
  rcases ht.eq_or_lt with h | h
  · rw [← h]; simp
  · have := Real.one_sub_inv_le_log_of_pos h
    have h2 : t * (1 - t⁻¹) ≤ t * Real.log t := mul_le_mul_of_nonneg_left this h.le
    have : t * (1 - t⁻¹) = t - 1 := by field_simp
    linarith

/-- **Gaussian log-Sobolev inequality** for `C²` functions with `u ∈ L²(γ)`, `‖Du‖ ∈ L²(γ)`. -/
theorem s8p_gauss_lsi {u : V → ℝ} (hu : ContDiff ℝ 2 u)
    (hL2 : Integrable (fun x => u x ^ 2 * s8p_gd x))
    (hD : Integrable (fun x => ‖fderiv ℝ u x‖ ^ 2 * s8p_gd x)) :
    Integrable (fun x => (u x ^ 2 * Real.log (u x ^ 2)) * s8p_gd x) ∧
    (∫ x, (u x ^ 2 * Real.log (u x ^ 2)) * s8p_gd x) -
        (∫ x, u x ^ 2 * s8p_gd x) * Real.log (∫ x, u x ^ 2 * s8p_gd x) ≤
      2 * ∫ x, ‖fderiv ℝ u x‖ ^ 2 * s8p_gd x := by
  obtain ⟨χ, hχ, ⟨R0, hR0⟩, h01, h1, Bχ, hBχ0, hBχ⟩ := s8p_cutoff (V := V)
  set Rn : ℕ → ℝ := fun n => (n : ℝ) + 1 with hRn
  have hRpos : ∀ n, 0 < Rn n := fun n => by simp only [hRn]; positivity
  set un : ℕ → V → ℝ := fun n x => χ ((Rn n)⁻¹ • x) * u x with hun
  have hun_cd : ∀ n, ContDiff ℝ 2 (un n) := fun n => (s8p_cutoff_u hu hχ hR0 (hRpos n)).1
  have hun_cs : ∀ n, HasCompactSupport (un n) := fun n => (s8p_cutoff_u hu hχ hR0 (hRpos n)).2
  set Ea := ∫ x, ‖fderiv ℝ u x‖ ^ 2 * s8p_gd x with hEa
  set m := ∫ x, u x ^ 2 * s8p_gd x with hm
  -- pointwise eventual equality
  have hev : ∀ x, ∀ᶠ n in Filter.atTop, un n x = u x := fun x => by
    have : ∀ᶠ n : ℕ in Filter.atTop, ‖x‖ ≤ Rn n := by
      filter_upwards [Filter.eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
      simp only [hRn]
      have := Nat.le_ceil ‖x‖
      have : (⌈‖x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    filter_upwards [this] with n hn
    have : χ ((Rn n)⁻¹ • x) = 1 := h1 _ (by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (hRpos n).le, inv_mul_le_iff₀ (hRpos n)]
      simpa using hn)
    simp [hun, this]
  -- m_n
  have hmn : Tendsto (fun n => ∫ x, un n x ^ 2 * s8p_gd x) atTop (𝓝 m) := by
    refine tendsto_integral_of_dominated_convergence (fun x => u x ^ 2 * s8p_gd x) ?_ hL2 ?_ ?_
    · intro n
      exact (((hun_cd n).continuous.pow 2).mul s8p_gd_continuous).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_of_nonneg (sq_nonneg _)]
      refine mul_le_mul_of_nonneg_right ?_ (s8p_gd_pos x).le
      have a1 := h01 ((Rn n)⁻¹ • x)
      simp only [hun]
      rw [mul_pow]
      nlinarith [sq_nonneg (u x), mul_nonneg (sq_nonneg (u x)) (sq_nonneg (χ ((Rn n)⁻¹ • x))),
        pow_le_one₀ a1.1 a1.2 (n := 2), sq_nonneg (χ ((Rn n)⁻¹ • x))]
    · refine Filter.Eventually.of_forall fun x => ?_
      refine (tendsto_const_nhds.congr' ?_).mul_const _
      filter_upwards [hev x] with n hn
      rw [hn]
  -- gradient estimate
  have hgrad : ∀ n, ∫ x, ‖fderiv ℝ (un n) x‖ ^ 2 * s8p_gd x ≤
      (1 + 1 / Rn n) * Ea + (1 / Rn n + 1 / Rn n ^ 2) * (Bχ ^ 2 * m) := fun n => by
    have hR := hRpos n
    have hpt : ∀ x, ‖fderiv ℝ (un n) x‖ ^ 2 * s8p_gd x ≤
        ((1 + 1 / Rn n) * (‖fderiv ℝ u x‖ ^ 2 * s8p_gd x) +
          (1 / Rn n + 1 / Rn n ^ 2) * (Bχ ^ 2 * (u x ^ 2 * s8p_gd x))) := fun x => by
      have h := s8p_cutoff_grad hu hχ h01 hBχ hR x
      have hb := norm_nonneg (fderiv ℝ (fun x => χ ((Rn n)⁻¹ • x) * u x) x)
      have hg := (s8p_gd_pos x).le
      set a := ‖fderiv ℝ u x‖
      set b := |u x| * Bχ
      have e : |u x| * (Bχ / Rn n) = b / Rn n := by ring
      rw [e] at h
      have h2 : ‖fderiv ℝ (un n) x‖ ^ 2 ≤ (a + b / Rn n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      have h3 : (a + b / Rn n) ^ 2 ≤ (1 + 1 / Rn n) * a ^ 2 + (1 / Rn n + 1 / Rn n ^ 2) * b ^ 2 := by
        have : 2 * a * (b / Rn n) ≤ (a ^ 2 + b ^ 2) / Rn n := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hR]; nlinarith [sq_nonneg (a - b)]
        have e2 : (a + b / Rn n) ^ 2 = a ^ 2 + 2 * a * (b / Rn n) + b ^ 2 / Rn n ^ 2 := by
          field_simp; ring
        rw [e2]
        have e3 : (1 + 1 / Rn n) * a ^ 2 + (1 / Rn n + 1 / Rn n ^ 2) * b ^ 2 =
            a ^ 2 + (a ^ 2 + b ^ 2) / Rn n + b ^ 2 / Rn n ^ 2 := by field_simp; ring
        rw [e3]; linarith
      have hb2 : b ^ 2 = Bχ ^ 2 * u x ^ 2 := by simp only [b]; rw [mul_pow, sq_abs]; ring
      have := mul_le_mul_of_nonneg_right (h2.trans h3) hg
      rw [hb2] at this
      nlinarith [this]
    have hint1 : Integrable (fun x => ‖fderiv ℝ (un n) x‖ ^ 2 * s8p_gd x) := by
      have hd : HasCompactSupport (fderiv ℝ (un n)) := (hun_cs n).fderiv ℝ
      obtain ⟨B, hB⟩ := ((hun_cd n).continuous_fderiv (by norm_num)).bounded_above_of_compact_support hd
      refine Integrable.mono' (s8p_gd_integrable.const_mul (B ^ 2))
        ((((hun_cd n).continuous_fderiv (by norm_num)).norm.pow 2).mul s8p_gd_continuous).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB x) 2) (s8p_gd_pos x).le
    have hs1 : Integrable (fun x => (1 + 1 / Rn n) * (‖fderiv ℝ u x‖ ^ 2 * s8p_gd x)) := hD.const_mul _
    have hs2 : Integrable (fun x => (1 / Rn n + 1 / Rn n ^ 2) * (Bχ ^ 2 * (u x ^ 2 * s8p_gd x))) :=
      (hL2.const_mul _).const_mul _
    have : ∫ x, ‖fderiv ℝ (un n) x‖ ^ 2 * s8p_gd x ≤ ∫ x, ((1 + 1 / Rn n) * (‖fderiv ℝ u x‖ ^ 2 * s8p_gd x) +
        (1 / Rn n + 1 / Rn n ^ 2) * (Bχ ^ 2 * (u x ^ 2 * s8p_gd x))) := integral_mono hint1 (hs1.add hs2) hpt
    rw [integral_add hs1 hs2, integral_const_mul, integral_const_mul, integral_const_mul] at this
    exact this
  -- the bounds U_n
  set mn : ℕ → ℝ := fun n => ∫ x, un n x ^ 2 * s8p_gd x with hmn_def
  set Un : ℕ → ℝ := fun n => 2 * ((1 + 1 / Rn n) * Ea + (1 / Rn n + 1 / Rn n ^ 2) * (Bχ ^ 2 * m)) +
    mn n * Real.log (mn n) with hUn
  have hR1 : Tendsto (fun n => 1 / Rn n) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hUn_lim : Tendsto Un atTop (𝓝 (2 * Ea + m * Real.log m)) := by
    have h1 : Tendsto (fun n => 2 * ((1 + 1 / Rn n) * Ea + (1 / Rn n + 1 / Rn n ^ 2) * (Bχ ^ 2 * m))) atTop
        (𝓝 (2 * ((1 + 0) * Ea + (0 + 0 ^ 2) * (Bχ ^ 2 * m)))) := by
      refine Tendsto.const_mul _ (Tendsto.add (Tendsto.mul_const _ (tendsto_const_nhds.add hR1))
        (Tendsto.mul_const _ (hR1.add ((hR1.pow 2).congr (fun n => by ring)))))
    have h2 : Tendsto (fun n => mn n * Real.log (mn n)) atTop (𝓝 (m * Real.log m)) :=
      (Real.continuous_mul_log.tendsto m).comp hmn
    have e : 2 * ((1 + 0) * Ea + (0 + 0 ^ 2) * (Bχ ^ 2 * m)) + m * Real.log m = 2 * Ea + m * Real.log m := by ring
    rw [← e]
    exact h1.add h2
  have hFn_int : ∀ n, Integrable (fun x => (un n x ^ 2 * Real.log (un n x ^ 2)) * s8p_gd x) := fun n => by
    have hc : Continuous fun x => un n x ^ 2 * Real.log (un n x ^ 2) :=
      Real.continuous_mul_log.comp ((hun_cd n).continuous.pow 2)
    have hcs : HasCompactSupport fun x => un n x ^ 2 * Real.log (un n x ^ 2) :=
      HasCompactSupport.intro (hun_cs n) (fun x hx => by
        have : un n x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [this])
    obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hcs
    refine Integrable.mono' (s8p_gd_integrable.const_mul B) (hc.mul s8p_gd_continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le]
    exact mul_le_mul_of_nonneg_right (hB x) (s8p_gd_pos x).le
  have hFn_le : ∀ n, ∫ x, (un n x ^ 2 * Real.log (un n x ^ 2)) * s8p_gd x ≤ Un n := fun n => by
    have h1 := s8p_gauss_lsi_cs0 (hun_cd n) (hun_cs n)
    have h2 := hgrad n
    simp only [hUn, hmn_def]
    nlinarith [h1, h2]
  -- Fatou
  set f : ℕ → V → ENNReal := fun n x =>
    ENNReal.ofReal (((un n x ^ 2 * Real.log (un n x ^ 2)) + 1) * s8p_gd x) with hf
  have hfm : ∀ n, Measurable (f n) := fun n => by
    simp only [hf]
    exact ENNReal.measurable_ofReal.comp ((((Real.continuous_mul_log.comp ((hun_cd n).continuous.pow 2)).add
      continuous_const).mul s8p_gd_continuous).measurable)
  have hfl := lintegral_liminf_le (μ := (volume : Measure V)) (u := (atTop : Filter ℕ)) hfm
  have hlim_pt : ∀ x, Filter.liminf (fun n => f n x) (atTop : Filter ℕ) =
      ENNReal.ofReal (((u x ^ 2 * Real.log (u x ^ 2)) + 1) * s8p_gd x) := fun x => by
    refine Filter.Tendsto.liminf_eq (f := (atTop : Filter ℕ)) ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev x] with n hn
    simp only [hf, hn]
  have hint_n : ∀ n, ∫⁻ x, f n x ≤ ENNReal.ofReal (Un n + 1) := fun n => by
    simp only [hf]
    rw [← ofReal_integral_eq_lintegral_ofReal ((hFn_int n).add s8p_gd_integrable |>.congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring))
      (Filter.Eventually.of_forall fun x => mul_nonneg (by
        have := s8p_mul_log_ge (un n x ^ 2) (sq_nonneg _); have := sq_nonneg (un n x); linarith) (s8p_gd_pos x).le)]
    apply ENNReal.ofReal_le_ofReal
    have : ∫ x, ((un n x ^ 2 * Real.log (un n x ^ 2)) + 1) * s8p_gd x =
        (∫ x, (un n x ^ 2 * Real.log (un n x ^ 2)) * s8p_gd x) + 1 := by
      simp_rw [add_mul, one_mul]
      rw [integral_add (hFn_int n) s8p_gd_integrable, s8p_gd_integral]
    rw [this]
    linarith [hFn_le n]
  have hlimU : Tendsto (fun n => ENNReal.ofReal (Un n + 1)) atTop
      (𝓝 (ENNReal.ofReal (2 * Ea + m * Real.log m + 1))) := ENNReal.tendsto_ofReal (hUn_lim.add_const 1)
  have h3 : Filter.liminf (fun n => ∫⁻ x, f n x) (atTop : Filter ℕ) ≤
      Filter.liminf (fun n => ENNReal.ofReal (Un n + 1)) (atTop : Filter ℕ) :=
    Filter.liminf_le_liminf (Filter.Eventually.of_forall hint_n)
  rw [hlimU.liminf_eq] at h3
  simp_rw [hlim_pt] at hfl
  have hbound := hfl.trans h3
  -- conclusion
  have hFm : Measurable fun x => (u x ^ 2 * Real.log (u x ^ 2)) := 
    (Real.continuous_mul_log.comp (hu.continuous.pow 2)).measurable
  have hG0 : ∀ x, 0 ≤ ((u x ^ 2 * Real.log (u x ^ 2)) + 1) * s8p_gd x := fun x =>
    mul_nonneg (by have := s8p_mul_log_ge (u x ^ 2) (sq_nonneg _); have := sq_nonneg (u x); linarith) (s8p_gd_pos x).le
  have hGint : Integrable (fun x => ((u x ^ 2 * Real.log (u x ^ 2)) + 1) * s8p_gd x) := by
    refine ⟨((hFm.add_const 1).mul (s8p_gd_continuous.measurable)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hFint : Integrable (fun x => (u x ^ 2 * Real.log (u x ^ 2)) * s8p_gd x) := by
    refine (hGint.sub s8p_gd_integrable).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  refine ⟨hFint, ?_⟩
  have hval : ∫ x, ((u x ^ 2 * Real.log (u x ^ 2)) + 1) * s8p_gd x ≤ 2 * Ea + m * Real.log m + 1 := by
    have := hbound
    rw [← ofReal_integral_eq_lintegral_ofReal hGint (Filter.Eventually.of_forall hG0)] at this
    have hm0 : 0 ≤ m := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (s8p_gd_pos x).le
    have hEa0 : 0 ≤ Ea := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (s8p_gd_pos x).le
    have := (ENNReal.ofReal_le_ofReal_iff (by have := s8p_mul_log_ge m hm0; linarith)).1 this
    exact this
  have e : ∫ x, ((u x ^ 2 * Real.log (u x ^ 2)) + 1) * s8p_gd x =
      (∫ x, (u x ^ 2 * Real.log (u x ^ 2)) * s8p_gd x) + 1 := by
    simp_rw [add_mul, one_mul]
    rw [integral_add hFint s8p_gd_integrable, s8p_gd_integral]
  rw [e] at hval
  linarith

end HRS.MS.Spec
