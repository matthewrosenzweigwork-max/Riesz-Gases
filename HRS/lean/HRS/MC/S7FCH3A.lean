import HRS.MC.S7FCW9Mom

/-!
# S7FCH3A: generic `L^p` helpers for the Gaussian-side approximation (H3), part A

Sorry-free helpers, no regime:

* `S7FCH3_lint_jensen`: finite weighted power-mean inequality integrated over `Ω`, with a per-index moment
  constant `Dm i` (generalising `S7FCW9_lint_jensen`);
* `S7FCH3_lint_jensen_tsum`: the same for an infinite sum over the nonzero lattice (monotone limit over the cubes);
* `S7FCH3_lint_holder_time`: `(∫⁻ f)^m ≤ μ(univ)^(m-1) ∫⁻ f^m` for a finite measure;
* `S7FCH3_time_jensen`: Jensen in time plus Tonelli: from a pointwise-in-time `L^m(Ω)` bound of `N t` to a bound of
  `(∫⁻_{[0,T]} N t ω dt)^m`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH3

open HRS HRS.Sec7 HRS.MC.QRSpec HRS.MC.Sec7.S7FCW9

variable {d : ℕ}

theorem S7FCH3_lint_jensen {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*} (U : Finset ι)
    (a σ Dm : ι → ℝ) (f : ι → Ω → ℝ) (A m : ℝ)
    (hf : ∀ i, Measurable (f i)) (ha : ∀ i, 0 ≤ a i) (hσ : ∀ i, 0 < σ i) (hDm : ∀ i, 0 ≤ Dm i)
    (hA : ∑ i ∈ U, a i ≤ A) (hA0 : 0 < A) (hm : 1 ≤ m)
    (hmom : ∀ i ∈ U, ∫⁻ ω, ENNReal.ofReal (|f i ω| ^ (2 * m)) ∂P ≤ ENNReal.ofReal (σ i ^ m * Dm i)) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i ∈ U, a i * (f i ω ^ 2 / σ i)) ^ m) ∂P ≤
      ENNReal.ofReal (A ^ (m - 1) * ∑ i ∈ U, a i * Dm i) := by
  have hAm1 : 0 ≤ A ^ (m - 1) := Real.rpow_nonneg hA0.le _
  have hcoef : ∀ i, 0 ≤ a i / σ i ^ m := fun i =>
    div_nonneg (ha i) (Real.rpow_nonneg (hσ i).le _)
  have hpt : ∀ ω, ENNReal.ofReal ((∑ i ∈ U, a i * (f i ω ^ 2 / σ i)) ^ m) ≤
      ∑ i ∈ U, ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)) * ENNReal.ofReal (|f i ω| ^ (2 * m)) := by
    intro ω
    have hz : ∀ i ∈ U, 0 ≤ f i ω ^ 2 / σ i := fun i _ => div_nonneg (sq_nonneg _) (hσ i).le
    have J := S7FCW9_jensen_fin U a (fun i => f i ω ^ 2 / σ i) A m (fun i _ => ha i) hz hA hm
    beta_reduce at J
    have e : ∀ i ∈ U, a i * (f i ω ^ 2 / σ i) ^ m = (a i / σ i ^ m) * |f i ω| ^ (2 * m) := by
      intro i _
      rw [Real.div_rpow (sq_nonneg _) (hσ i).le, S7FCW9_sq_rpow]
      ring
    rw [Finset.sum_congr rfl e] at J
    have hnn : ∀ i ∈ U, 0 ≤ A ^ (m - 1) * ((a i / σ i ^ m) * |f i ω| ^ (2 * m)) := fun i _ =>
      mul_nonneg hAm1 (mul_nonneg (hcoef i) (Real.rpow_nonneg (abs_nonneg _) _))
    calc ENNReal.ofReal ((∑ i ∈ U, a i * (f i ω ^ 2 / σ i)) ^ m)
        ≤ ENNReal.ofReal (A ^ (m - 1) * ∑ i ∈ U, (a i / σ i ^ m) * |f i ω| ^ (2 * m)) :=
          ENNReal.ofReal_le_ofReal J
      _ = ENNReal.ofReal (∑ i ∈ U, A ^ (m - 1) * ((a i / σ i ^ m) * |f i ω| ^ (2 * m))) := by
          rw [Finset.mul_sum]
      _ = ∑ i ∈ U, ENNReal.ofReal (A ^ (m - 1) * ((a i / σ i ^ m) * |f i ω| ^ (2 * m))) :=
          ENNReal.ofReal_sum_of_nonneg hnn
      _ = ∑ i ∈ U, ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)) *
            ENNReal.ofReal (|f i ω| ^ (2 * m)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hAm1 (hcoef i))]
  have hmeas : ∀ i, Measurable fun ω => ENNReal.ofReal (|f i ω| ^ (2 * m)) := fun i =>
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp (hf i)).pow_const _)
  calc ∫⁻ ω, ENNReal.ofReal ((∑ i ∈ U, a i * (f i ω ^ 2 / σ i)) ^ m) ∂P
      ≤ ∫⁻ ω, ∑ i ∈ U, ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)) *
          ENNReal.ofReal (|f i ω| ^ (2 * m)) ∂P := lintegral_mono hpt
    _ = ∑ i ∈ U, ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)) *
          ∫⁻ ω, ENNReal.ofReal (|f i ω| ^ (2 * m)) ∂P := by
          rw [lintegral_finset_sum' U fun i _ =>
            ((hmeas i).const_mul (ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)))).aemeasurable]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_const_mul _ (hmeas i)]
    _ ≤ ∑ i ∈ U, ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)) *
          ENNReal.ofReal (σ i ^ m * Dm i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact mul_le_mul_of_nonneg_left (hmom i hi) zero_le'
    _ = ∑ i ∈ U, ENNReal.ofReal (A ^ (m - 1) * (a i * Dm i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← ENNReal.ofReal_mul (mul_nonneg hAm1 (hcoef i))]
          congr 1
          have : σ i ^ m ≠ 0 := (Real.rpow_pos_of_pos (hσ i) _).ne'
          field_simp
    _ = ENNReal.ofReal (∑ i ∈ U, A ^ (m - 1) * (a i * Dm i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i _
          exact mul_nonneg hAm1 (mul_nonneg (ha i) (hDm i))
    _ = ENNReal.ofReal (A ^ (m - 1) * ∑ i ∈ U, a i * Dm i) := by
          rw [Finset.mul_sum]

/-- Infinite sum over the nonzero lattice, by monotone convergence along the cubes. -/
theorem S7FCH3_lint_jensen_tsum {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (a σ Dm : NonzeroLattice d → ℝ) (f : NonzeroLattice d → Ω → ℝ) (Nn : Ω → ℝ) (A m : ℝ)
    (hf : ∀ i, Measurable (f i)) (ha : ∀ i, 0 ≤ a i) (hσ : ∀ i, 0 < σ i) (hDm : ∀ i, 0 ≤ Dm i)
    (hsum : Summable a) (hA : ∑' i, a i ≤ A) (hA0 : 0 < A) (hm : 1 ≤ m)
    (hDs : Summable fun i => a i * Dm i)
    (hmom : ∀ i, ∫⁻ ω, ENNReal.ofReal (|f i ω| ^ (2 * m)) ∂P ≤ ENNReal.ofReal (σ i ^ m * Dm i))
    (hNn : ∀ ω, HasSum (fun i => a i * (f i ω ^ 2 / σ i)) (Nn ω)) :
    ∫⁻ ω, ENNReal.ofReal (Nn ω ^ m) ∂P ≤ ENNReal.ofReal (A ^ (m - 1) * ∑' i, a i * Dm i) := by
  have hm0 : 0 < m := by linarith
  have hnn : ∀ ω i, 0 ≤ a i * (f i ω ^ 2 / σ i) := fun ω i =>
    mul_nonneg (ha i) (div_nonneg (sq_nonneg _) (hσ i).le)
  set F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal ((∑ i ∈ S7FCW9_cube d n, a i * (f i ω ^ 2 / σ i)) ^ m) with hF
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.pow_const ?_ _
    exact Finset.measurable_sum _ fun i _ => ((hf i).pow_const 2).div_const (σ i) |>.const_mul (a i)
  have hmono : ∀ ω, Monotone fun n => F n ω := by
    intro ω n n' hnn'
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
      (Finset.sum_nonneg fun i _ => hnn ω i) ?_ hm0.le)
    exact Finset.sum_le_sum_of_subset_of_nonneg (S7FCW9_cube_mono hnn') fun i _ _ => hnn ω i
  have htend : ∀ ω, Tendsto (fun n => F n ω) atTop (𝓝 (ENNReal.ofReal (Nn ω ^ m))) := by
    intro ω
    have h1 := S7FCW9_tendsto_of_hasSum (hNn ω)
    have h2 : Tendsto (fun n => (∑ i ∈ S7FCW9_cube d n, a i * (f i ω ^ 2 / σ i)) ^ m) atTop
        (𝓝 (Nn ω ^ m)) :=
      (Real.continuousAt_rpow_const _ _ (Or.inr hm0.le)).tendsto.comp h1 |>.congr fun n => rfl
    exact (ENNReal.continuous_ofReal.tendsto _).comp h2
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := P) (fun n => (hFm n).aemeasurable)
    (Filter.Eventually.of_forall hmono) (Filter.Eventually.of_forall htend)
  refine le_of_tendsto' hlim fun n => ?_
  have hA' : ∑ i ∈ S7FCW9_cube d n, a i ≤ A :=
    (Summable.sum_le_tsum _ (fun i _ => ha i) hsum).trans hA
  refine (S7FCH3_lint_jensen P (S7FCW9_cube d n) a σ Dm f A m hf ha hσ hDm hA' hA0 hm
    (fun i _ => hmom i)).trans ?_
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hA0.le _))
  exact Summable.sum_le_tsum _ (fun i _ => mul_nonneg (ha i) (hDm i)) hDs

/-- `(∫⁻ f)^m ≤ μ(univ)^(m-1) ∫⁻ f^m` for a finite measure. -/
theorem S7FCH3_lint_holder_time {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ≥0∞) (hf : AEMeasurable f μ) (m : ℝ) (hm : 1 ≤ m) :
    (∫⁻ x, f x ∂μ) ^ m ≤ μ Set.univ ^ (m - 1) * ∫⁻ x, f x ^ m ∂μ := by
  rcases hm.eq_or_lt with h1 | h1
  · subst h1
    simp
  · have hm0 : 0 < m := by linarith
    set q : ℝ := m / (m - 1) with hq
    have hpq : m.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent h1).2 hq
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (g := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
    simp only [mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at hH
    have h2 := ENNReal.rpow_le_rpow hH hm0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hm0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
    have e1 : 1 / m * m = 1 := by field_simp
    have e2 : 1 / q * m = m - 1 := by rw [hq]; field_simp
    rw [e1, e2, ENNReal.rpow_one] at h2
    simpa [mul_comm] using h2

/-- Jensen in time followed by Tonelli: a pointwise-in-time `L^m(Ω)` bound for `N t` gives an `L^m(Ω)` bound for
the time integral over `[0,T]`. -/
theorem S7FCH3_time_jensen {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] (T : ℝ) (hT : 0 ≤ T)
    (N : ℝ → Ω → ℝ) (hN : Measurable (Function.uncurry N)) (hN0 : ∀ t ω, 0 ≤ N t ω) (m V : ℝ)
    (hm : 1 ≤ m)
    (hV : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫⁻ ω, ENNReal.ofReal (N t ω ^ m) ∂P ≤ ENNReal.ofReal V) :
    ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (N t ω)) ^ m ∂P ≤ ENNReal.ofReal (T ^ m * V) := by
  have hm0 : 0 < m := by linarith
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  haveI : IsFiniteMeasure μT := by
    rw [hμT]; exact Real.isFiniteMeasure_restrict_Icc 0 T
  have hμu : μT Set.univ = ENNReal.ofReal T := by
    rw [hμT, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]; simp
  have hgm : Measurable (fun p : ℝ × Ω => ENNReal.ofReal (N p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp hN
  have hpt : ∀ ω, (∫⁻ t, ENNReal.ofReal (N t ω) ∂μT) ^ m ≤
      ENNReal.ofReal T ^ (m - 1) * ∫⁻ t, ENNReal.ofReal (N t ω) ^ m ∂μT := by
    intro ω
    have hmω : Measurable (fun t => ENNReal.ofReal (N t ω)) :=
      hgm.comp (measurable_id.prodMk measurable_const)
    have := S7FCH3_lint_holder_time μT _ hmω.aemeasurable m hm
    rwa [hμu] at this
  have hswap : ∫⁻ ω, ∫⁻ t, ENNReal.ofReal (N t ω) ^ m ∂μT ∂P =
      ∫⁻ t, ∫⁻ ω, ENNReal.ofReal (N t ω) ^ m ∂P ∂μT := by
    refine lintegral_lintegral_swap ?_
    have : Measurable (fun p : Ω × ℝ => ENNReal.ofReal (N p.2 p.1) ^ m) :=
      (hgm.comp measurable_swap).pow_const m
    exact this.aemeasurable
  have hinner : ∫⁻ t, ∫⁻ ω, ENNReal.ofReal (N t ω) ^ m ∂P ∂μT ≤ ENNReal.ofReal T * ENNReal.ofReal V := by
    calc ∫⁻ t, ∫⁻ ω, ENNReal.ofReal (N t ω) ^ m ∂P ∂μT ≤ ∫⁻ t, ENNReal.ofReal V ∂μT := by
          refine lintegral_mono_ae ?_
          filter_upwards [hV] with t ht
          refine le_trans (le_of_eq ?_) ht
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_rpow_of_nonneg (hN0 t ω) hm0.le]
      _ = ENNReal.ofReal T * ENNReal.ofReal V := by rw [lintegral_const, hμu, mul_comm]
  calc ∫⁻ ω, (∫⁻ t, ENNReal.ofReal (N t ω) ∂μT) ^ m ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal T ^ (m - 1) * ∫⁻ t, ENNReal.ofReal (N t ω) ^ m ∂μT ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal T ^ (m - 1) * ∫⁻ ω, ∫⁻ t, ENNReal.ofReal (N t ω) ^ m ∂μT ∂P := by
        rw [lintegral_const_mul']
        exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal T ^ (m - 1) * (ENNReal.ofReal T * ENNReal.ofReal V) := by
        rw [hswap]; exact mul_le_mul_of_nonneg_left hinner zero_le'
    _ = ENNReal.ofReal T ^ m * ENNReal.ofReal V := by
        rw [← mul_assoc]
        congr 1
        conv_rhs => rw [show m = (m - 1) + 1 by ring, ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one,
          ENNReal.rpow_one]
    _ = ENNReal.ofReal (T ^ m * V) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT _), ENNReal.ofReal_rpow_of_nonneg hT hm0.le]

/-- Jensen weight `a_κ = ĵ_κ^{-(2r-(d+3))}`. -/
noncomputable def S7FCH3_wt (d : ℕ) (r : ℝ) (κ : NonzeroLattice d) : ℝ :=
  Lattice.jp κ.1 ^ (-(2 * r - ((d : ℝ) + 3)))

/-- Jensen scale `σ_κ = ĵ_κ^{d+3}`. -/
noncomputable def S7FCH3_sg (d : ℕ) (κ : NonzeroLattice d) : ℝ :=
  Lattice.jp κ.1 ^ ((d : ℝ) + 3)

theorem S7FCH3_wt_pos (r : ℝ) (κ : NonzeroLattice d) : 0 < S7FCH3_wt d r κ :=
  Real.rpow_pos_of_pos (Torus.jp_pos κ.1) _

theorem S7FCH3_sg_pos (κ : NonzeroLattice d) : 0 < S7FCH3_sg d κ :=
  Real.rpow_pos_of_pos (Torus.jp_pos κ.1) _

theorem S7FCH3_weight_eq (r j : ℝ) (hj : 0 < j) (x : ℝ) (d : ℕ) :
    j ^ (-(2 * r - ((d : ℝ) + 3))) * (x ^ 2 / j ^ ((d : ℝ) + 3)) = (j ^ (-r) * x) ^ 2 := by
  have hp : (j ^ (-r)) ^ 2 = j ^ (-(2 * r)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hj.le]
    congr 1
    push_cast
    ring
  have hs : j ^ (-(2 * r - ((d : ℝ) + 3))) = j ^ (-(2 * r)) * j ^ ((d : ℝ) + 3) := by
    rw [← Real.rpow_add hj]
    congr 1
    ring
  have hne : j ^ ((d : ℝ) + 3) ≠ 0 := (Real.rpow_pos_of_pos hj _).ne'
  rw [mul_pow, hp, hs]
  field_simp

end HRS.MC.Sec7.S7FCH3

end
