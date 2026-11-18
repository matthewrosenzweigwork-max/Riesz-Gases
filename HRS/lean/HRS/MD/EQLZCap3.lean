import HRS.MD.EQLZCap2

/-!
# EQ-LZ packet CAP, helper 3: truncation (stage (i))

The soft truncation `capTr K y = K p(y / K)` with `p(x) = x ψ(x)`, `ψ` a bump function (`ψ = 1` on `[-1,1]`,
`ψ = 0` off `[-2,2]`).  Properties: `|capTr K y| ≤ min(|y|, 2K)`, `capTr K y = y` for `|y| ≤ K`, the derivative is
bounded by an absolute constant and equals `1` for `|y| < K`.  `trunc_approx`: for `Φ` with the hypotheses of
`IsLZTest` transported to the torus, `capTr K ∘ Φ → Φ` in `L²(ν)` and the energies converge.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology

namespace HRS.MD.EQLZ.Cap

variable {n : ℕ}

/-! ### The profile -/

def capBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

def capP (x : ℝ) : ℝ := x * capBump x

theorem capP_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) capP :=
  contDiff_id.mul (capBump.contDiff (n := ⊤))

theorem capP_c1 : ContDiff ℝ 1 capP := capP_smooth.of_le (by exact_mod_cast le_top)

theorem capP_abs_le (x : ℝ) : |capP x| ≤ |x| := by
  unfold capP
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_of_nonneg capBump.nonneg]; exact capBump.le_one)

theorem capP_eq (x : ℝ) (hx : |x| ≤ 1) : capP x = x := by
  have : capBump x = 1 := capBump.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, capBump] using hx)
  simp [capP, this]

theorem capP_zero (x : ℝ) (hx : 2 ≤ |x|) : capP x = 0 := by
  have : capBump x = 0 := capBump.zero_of_le_dist (by simpa [capBump, Real.dist_eq] using hx)
  simp [capP, this]

theorem capP_abs_le_two (x : ℝ) : |capP x| ≤ 2 := by
  by_cases hx : 2 ≤ |x|
  · rw [capP_zero x hx]; norm_num
  · exact (capP_abs_le x).trans (not_le.1 hx).le

theorem capP_hasCompactSupport : HasCompactSupport capP :=
  capBump.hasCompactSupport.mul_left (f := fun x : ℝ => x)

theorem exists_deriv_bound : ∃ A : ℝ, 1 ≤ A ∧ ∀ x, |deriv capP x| ≤ A := by
  obtain ⟨C, hC⟩ := (capP_c1.continuous_deriv le_rfl).bounded_above_of_compact_support
    capP_hasCompactSupport.deriv
  exact ⟨max C 1, le_max_right _ _, fun x => by simpa using (hC x).trans (le_max_left _ _)⟩

theorem capP_deriv_one (x : ℝ) (hx : |x| < 1) : deriv capP x = 1 := by
  have h : capP =ᶠ[𝓝 x] fun y => y := by
    have : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 x := Ioo_mem_nhds (by linarith [neg_abs_le x]) (by linarith [le_abs_self x])
    filter_upwards [this] with y hy
    exact capP_eq y (abs_le.2 ⟨hy.1.le, hy.2.le⟩)
  rw [h.deriv_eq]
  simp

/-! ### The truncation -/

def capTr (K y : ℝ) : ℝ := K * capP (y / K)

theorem capTr_hasDerivAt {K : ℝ} (hK : K ≠ 0) (y : ℝ) : HasDerivAt (capTr K) (deriv capP (y / K)) y := by
  have h1 : HasDerivAt (fun y : ℝ => y / K) (1 / K) y := (hasDerivAt_id y).div_const K
  have h2 : HasDerivAt capP (deriv capP (y / K)) (y / K) :=
    ((capP_c1.differentiable one_ne_zero) (y / K)).hasDerivAt
  have h3 := (h2.comp y h1).const_mul K
  have e : K * (deriv capP (y / K) * (1 / K)) = deriv capP (y / K) := by field_simp
  rw [e] at h3
  exact h3

theorem capTr_contDiff {K : ℝ} : ContDiff ℝ 1 (capTr K) :=
  contDiff_const.mul (capP_c1.comp (contDiff_id.div_const K))

theorem capTr_abs_le {K : ℝ} (hK : 0 < K) (y : ℝ) : |capTr K y| ≤ |y| := by
  unfold capTr
  rw [abs_mul, abs_of_pos hK]
  have := capP_abs_le (y / K)
  rw [abs_div, abs_of_pos hK] at this
  calc K * |capP (y / K)| ≤ K * (|y| / K) := by gcongr
    _ = |y| := by field_simp

theorem capTr_abs_le_two {K : ℝ} (hK : 0 < K) (y : ℝ) : |capTr K y| ≤ 2 * K := by
  unfold capTr
  rw [abs_mul, abs_of_pos hK]
  nlinarith [capP_abs_le_two (y / K)]

theorem capTr_eq {K : ℝ} (hK : 0 < K) {y : ℝ} (hy : |y| ≤ K) : capTr K y = y := by
  unfold capTr
  rw [capP_eq _ (by rw [abs_div, abs_of_pos hK]; exact (div_le_one hK).2 hy)]
  field_simp

theorem capTr_deriv {K : ℝ} (hK : 0 < K) {y : ℝ} (hy : |y| < K) : deriv capP (y / K) = 1 :=
  capP_deriv_one _ (by rw [abs_div, abs_of_pos hK]; exact (div_lt_one hK).2 hy)

/-! ### Energy of a truncation -/

section Trunc

variable (Bd : Set (Torus n))

theorem isOpen_notBd (hBd : IsClosed Bd) : IsOpen {y : Euc n | Torus.mk y ∉ Bd} :=
  hBd.isOpen_compl.preimage Torus.continuous_mk

theorem lift_rep (Φ : Torus n → ℝ) (x : Torus n) : Torus.lift Φ (Torus.rep x) = Φ x := by
  simp [Torus.lift, Torus.mk_rep]

theorem capG_trunc (hBd : IsClosed Bd) {Φ : Torus n → ℝ}
    (hc : ContDiffOn ℝ 1 (Torus.lift Φ) {y | Torus.mk y ∉ Bd}) {K : ℝ} (hK : K ≠ 0) {x : Torus n}
    (hx : x ∉ Bd) :
    capG (fun x => capTr K (Φ x)) x = (deriv capP (Φ x / K)) ^ 2 * capG Φ x := by
  have hy : Torus.rep x ∈ {y : Euc n | Torus.mk y ∉ Bd} := by simpa [Torus.mk_rep] using hx
  have hd : DifferentiableAt ℝ (Torus.lift Φ) (Torus.rep x) :=
    ((hc.contDiffAt ((isOpen_notBd Bd hBd).mem_nhds hy)).differentiableAt one_ne_zero)
  have hl : Torus.lift (fun x => capTr K (Φ x)) = capTr K ∘ Torus.lift Φ := rfl
  have h1 := (capTr_hasDerivAt hK (Torus.lift Φ (Torus.rep x))).comp_hasFDerivAt (Torus.rep x) hd.hasFDerivAt
  unfold capG
  rw [hl, h1.fderiv, norm_smul, lift_rep, mul_pow, Real.norm_eq_abs, sq_abs]

theorem capG_nonneg (Φ : Torus n → ℝ) (x : Torus n) : 0 ≤ capG Φ x := sq_nonneg _

variable (ν : Measure (Torus n)) [IsFiniteMeasure ν]

theorem trunc_props (hBd : IsClosed Bd) (hBd0 : ν Bd = 0) {Φ : Torus n → ℝ} (hm : Measurable Φ)
    (hc : ContDiffOn ℝ 1 (Torus.lift Φ) {y | Torus.mk y ∉ Bd}) (hE : Integrable (capG Φ) ν)
    {K : ℝ} (hK : 0 < K) :
    Measurable (fun x => capTr K (Φ x)) ∧ (∀ x, |capTr K (Φ x)| ≤ 2 * K) ∧
      ContDiffOn ℝ 1 (Torus.lift fun x => capTr K (Φ x)) {y | Torus.mk y ∉ Bd} ∧
      Integrable (capG (fun x => capTr K (Φ x))) ν := by
  obtain ⟨A, hA1, hA⟩ := exists_deriv_bound
  refine ⟨capTr_contDiff.continuous.measurable.comp hm, fun x => capTr_abs_le_two hK _, ?_, ?_⟩
  · exact capTr_contDiff.comp_contDiffOn hc
  · refine Integrable.mono' (hE.const_mul (A ^ 2)) (measurable_capG _).aestronglyMeasurable ?_
    have hae : ∀ᵐ x ∂ν, x ∉ Bd := measure_eq_zero_iff_ae_notMem.1 hBd0
    filter_upwards [hae] with x hx
    rw [capG_trunc Bd hBd hc hK.ne' hx, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (capG_nonneg _ _))]
    have : (deriv capP (Φ x / K)) ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hA _) 2
    exact mul_le_mul_of_nonneg_right this (capG_nonneg _ _)

theorem trunc_approx (hBd : IsClosed Bd) (hBd0 : ν Bd = 0) {Φ : Torus n → ℝ} (hm : Measurable Φ)
    (h2 : MemLp Φ 2 ν) (hc : ContDiffOn ℝ 1 (Torus.lift Φ) {y | Torus.mk y ∉ Bd})
    (hE : Integrable (capG Φ) ν) :
    ∀ ε > 0, ∃ K : ℝ, 0 < K ∧ ∫ x, (capTr K (Φ x) - Φ x) ^ 2 ∂ν < ε ∧
      |∫ x, capG (fun x => capTr K (Φ x)) x ∂ν - ∫ x, capG Φ x ∂ν| < ε := by
  intro ε hε
  obtain ⟨A, hA1, hA⟩ := exists_deriv_bound
  have hae : ∀ᵐ x ∂ν, x ∉ Bd := measure_eq_zero_iff_ae_notMem.1 hBd0
  have hKpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  -- values
  have t1 : Tendsto (fun k : ℕ => ∫ x, (capTr ((k : ℝ) + 1) (Φ x) - Φ x) ^ 2 ∂ν) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun (k : ℕ) x => (capTr ((k : ℝ) + 1) (Φ x) - Φ x) ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => 4 * Φ x ^ 2)
      (fun k => ((capTr_contDiff.continuous.measurable.comp hm).sub hm).pow_const 2 |>.aestronglyMeasurable)
      (h2.integrable_sq.const_mul 4)
      (fun k => ae_of_all _ fun x => by
        have h1 : |capTr ((k : ℝ) + 1) (Φ x) - Φ x| ≤ 2 * |Φ x| := by
          calc _ ≤ |capTr ((k : ℝ) + 1) (Φ x)| + |Φ x| := abs_sub _ _
            _ ≤ |Φ x| + |Φ x| := add_le_add_left (capTr_abs_le (hKpos k) _) _
            _ = 2 * |Φ x| := by ring
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        calc (capTr ((k : ℝ) + 1) (Φ x) - Φ x) ^ 2 = |capTr ((k : ℝ) + 1) (Φ x) - Φ x| ^ 2 :=
              (sq_abs _).symm
          _ ≤ (2 * |Φ x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ = 4 * Φ x ^ 2 := by rw [mul_pow, sq_abs]; norm_num)
      (ae_of_all _ fun x => by
        obtain ⟨k₀, hk₀⟩ := exists_nat_ge |Φ x|
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop k₀] with k hk
        have : |Φ x| ≤ (k : ℝ) + 1 := by
          have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
          linarith
        rw [capTr_eq (hKpos k) this]; simp)
    simpa using this
  -- energies
  have t2 : Tendsto (fun k : ℕ => ∫ x, capG (fun x => capTr ((k : ℝ) + 1) (Φ x)) x ∂ν) atTop
      (𝓝 (∫ x, capG Φ x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun (k : ℕ) x => capG (fun x => capTr ((k : ℝ) + 1) (Φ x)) x) (f := capG Φ)
      (fun x => A ^ 2 * capG Φ x) (fun k => (measurable_capG _).aestronglyMeasurable)
      (hE.const_mul (A ^ 2)) (fun k => ?_) ?_
    · filter_upwards [hae] with x hx
      rw [capG_trunc Bd hBd hc (hKpos k).ne' hx, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (capG_nonneg _ _))]
      have : (deriv capP (Φ x / ((k : ℝ) + 1))) ^ 2 ≤ A ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hA _) 2
      exact mul_le_mul_of_nonneg_right this (capG_nonneg _ _)
    · filter_upwards [hae] with x hx
      obtain ⟨k₀, hk₀⟩ := exists_nat_gt |Φ x|
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop k₀] with k hk
      have : |Φ x| < (k : ℝ) + 1 := by
        have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      rw [capG_trunc Bd hBd hc (hKpos k).ne' hx, capTr_deriv (hKpos k) this]
      simp
  have e1 := t1.eventually (gt_mem_nhds hε)
  have e2 := (tendsto_iff_norm_sub_tendsto_zero.1 t2).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk1, hk2⟩ := (e1.and e2).exists
  exact ⟨(k : ℝ) + 1, hKpos k, hk1, by simpa [Real.norm_eq_abs] using hk2⟩

end Trunc

end HRS.MD.EQLZ.Cap
