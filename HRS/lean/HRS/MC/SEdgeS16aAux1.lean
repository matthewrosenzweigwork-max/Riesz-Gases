import HRS.Torus.Sobolev
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# S16a, Aux1: weak convergence in `E_m` from finite-dimensional convergence and uniform coordinate tails

Abstract Hilbert-space step of the proof of `sed_S16a_field_clt` (see `SEdgeS16a.lean` for the plan).
No Gibbs measure appears here.  Let `ν n` and `G` be probability measures on `E_m = ℓ²(ℤ^d∖{0})`
(`NegSobolev d m`), `coord y k` the `k`-th coordinate, `proj S` the coordinate projection onto a finite set
`S`.  If `∫ coord_k² dν_n ≤ w k` with `w` summable (uniform tails), and the finite-dimensional
marginals `proj S` converge against bounded continuous test functions, then `ν n → G` weakly.
The limit also satisfies the tail bound (by a monotone-truncation argument), and the proof tests against
bounded Lipschitz functions (Mathlib: `tendsto_iff_forall_lipschitz_integral_tendsto`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.S16a

variable {d : ℕ} {m : ℝ}

open Classical in
/-- Coordinate projection of `E_m` onto the finitely many coordinates in `S`. -/
def s16a_proj (S : Finset (NonzeroLattice d)) (y : NegSobolev d m) : NegSobolev d m :=
  ∑ k ∈ S, (show NegSobolev d m from
    lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (NegSobolev.coord y k))

open Classical in
theorem s16a_coord_proj (S : Finset (NonzeroLattice d)) (y : NegSobolev d m)
    (j : NonzeroLattice d) :
    NegSobolev.coord (s16a_proj S y) j = if j ∈ S then NegSobolev.coord y j else 0 := by
  unfold s16a_proj NegSobolev.coord
  show ((∑ k ∈ S, lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (NegSobolev.coord y k) :
    lp (fun _ : NonzeroLattice d => ℝ) 2) j) = _
  rw [lp.coeFn_sum]
  simp [Finset.sum_apply, lp.single_apply]
  rfl

theorem s16a_coord_sub (a b : NegSobolev d m) (j : NonzeroLattice d) :
    NegSobolev.coord (a - b) j = NegSobolev.coord a j - NegSobolev.coord b j := rfl

theorem s16a_continuous_coord (j : NonzeroLattice d) :
    Continuous (fun y : NegSobolev d m => NegSobolev.coord y j) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun y z => ?_).continuous
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from y - z) j
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
  have h2 : NegSobolev.coord y j - NegSobolev.coord z j =
      (show lp (fun _ : NonzeroLattice d => ℝ) 2 from y - z) j := rfl
  rw [h2]
  exact h

theorem s16a_continuous_proj (S : Finset (NonzeroLattice d)) :
    Continuous (fun y : NegSobolev d m => s16a_proj S y) := by
  classical
  unfold s16a_proj
  refine continuous_finsetSum _ fun k _ => ?_
  have hc : Continuous (fun a : ℝ => (show NegSobolev d m from
      lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k a)) :=
    (lp.isometry_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) k).continuous
  exact hc.comp (s16a_continuous_coord k)

/-- Tail sum of a weight outside `S`. -/
def s16a_tail (w : NonzeroLattice d → ℝ) (S : Finset (NonzeroLattice d)) : ℝ :=
  ∑' j, if j ∈ S then 0 else w j

theorem s16a_summable_ite {w : NonzeroLattice d → ℝ} (hw : Summable w) (hw0 : ∀ k, 0 ≤ w k)
    (S : Finset (NonzeroLattice d)) : Summable (fun j => if j ∈ S then 0 else w j) :=
  Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp [hw0]) (fun j => by
    split_ifs <;> simp [hw0]) hw

theorem s16a_tail_nonneg {w : NonzeroLattice d → ℝ} (hw0 : ∀ k, 0 ≤ w k)
    (S : Finset (NonzeroLattice d)) : 0 ≤ s16a_tail w S :=
  tsum_nonneg fun j => by split_ifs <;> simp [hw0]

theorem s16a_tail_tendsto {w : NonzeroLattice d → ℝ} (hw : Summable w) :
    Tendsto (fun S : Finset (NonzeroLattice d) => s16a_tail w S) atTop (𝓝 0) := by
  have h := tendsto_tsum_compl_atTop_zero w
  refine h.congr fun S => ?_
  unfold s16a_tail
  have := tsum_subtype ({x | x ∉ S} : Set (NonzeroLattice d)) w
  refine this.trans (tsum_congr fun j => ?_)
  by_cases hj : j ∈ S <;> simp [hj, Set.indicator]

theorem s16a_sub_proj_norm_sq (S : Finset (NonzeroLattice d)) (y : NegSobolev d m) :
    ‖y - s16a_proj S y‖ ^ 2 = ∑' j, (if j ∈ S then 0 else NegSobolev.coord y j ^ 2) := by
  classical
  obtain ⟨_, h⟩ := NegSobolev.coord_sq (y - s16a_proj S y)
  rw [h]
  refine tsum_congr fun j => ?_
  rw [s16a_coord_sub, s16a_coord_proj]
  by_cases hj : j ∈ S <;> simp [hj]

theorem s16a_summable_sub_proj (S : Finset (NonzeroLattice d)) (y : NegSobolev d m) :
    Summable (fun j => if j ∈ S then 0 else NegSobolev.coord y j ^ 2) := by
  obtain ⟨h, _⟩ := NegSobolev.coord_sq y
  exact Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity)
    (fun j => by split_ifs <;> simp [sq_nonneg]) h

/-- The lintegral tail bound outside `S`. -/
theorem s16a_lint_tail (μ : Measure (NegSobolev d m)) {w : NonzeroLattice d → ℝ}
    (hw : Summable w) (hw0 : ∀ k, 0 ≤ w k)
    (hμ : ∀ k, ∫⁻ y, ENNReal.ofReal (NegSobolev.coord y k ^ 2) ∂μ ≤ ENNReal.ofReal (w k))
    (S : Finset (NonzeroLattice d)) :
    ∫⁻ y, ENNReal.ofReal (‖y - s16a_proj S y‖ ^ 2) ∂μ ≤ ENNReal.ofReal (s16a_tail w S) := by
  classical
  have hnn : ∀ (y : NegSobolev d m) (j : NonzeroLattice d),
      0 ≤ (if j ∈ S then 0 else NegSobolev.coord y j ^ 2) := fun y j => by
    split_ifs <;> positivity
  calc ∫⁻ y, ENNReal.ofReal (‖y - s16a_proj S y‖ ^ 2) ∂μ
      = ∫⁻ y, ∑' j, ENNReal.ofReal (if j ∈ S then 0 else NegSobolev.coord y j ^ 2) ∂μ := by
        refine lintegral_congr fun y => ?_
        rw [s16a_sub_proj_norm_sq, ENNReal.ofReal_tsum_of_nonneg (hnn y)
          (s16a_summable_sub_proj S y)]
    _ = ∑' j, ∫⁻ y, ENNReal.ofReal (if j ∈ S then 0 else NegSobolev.coord y j ^ 2) ∂μ := by
        refine lintegral_tsum fun j => ?_
        refine (Measurable.ennreal_ofReal ?_).aemeasurable
        by_cases hj : j ∈ S
        · simp [hj]
        · simp only [hj, ite_false]
          exact ((s16a_continuous_coord j).pow 2).measurable
    _ ≤ ∑' j, ENNReal.ofReal (if j ∈ S then 0 else w j) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases hj : j ∈ S
        · simp [hj]
        · simpa [hj] using hμ j
    _ = ENNReal.ofReal (s16a_tail w S) := by
        unfold s16a_tail
        rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by split_ifs <;> simp [hw0])
          (s16a_summable_ite hw hw0 S)]

/-- A bounded Lipschitz function is `L`-close to its finite-dimensional truncation, in mean. -/
theorem s16a_close (μ : Measure (NegSobolev d m)) [IsProbabilityMeasure μ]
    {w : NonzeroLattice d → ℝ} (hw : Summable w) (hw0 : ∀ k, 0 ≤ w k)
    (hμ : ∀ k, ∫⁻ y, ENNReal.ofReal (NegSobolev.coord y k ^ 2) ∂μ ≤ ENNReal.ofReal (w k))
    {f : NegSobolev d m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L f) (hfb : ∃ M, ∀ x, |f x| ≤ M)
    (S : Finset (NonzeroLattice d)) {δ : ℝ} (hδ : 0 < δ) :
    |∫ y, f y ∂μ - ∫ y, f (s16a_proj S y) ∂μ| ≤
      (L : ℝ) * (δ / 2 + s16a_tail w S / (2 * δ)) := by
  obtain ⟨M, hM⟩ := hfb
  have hfc : Continuous f := hL.continuous
  have hfi : Integrable f μ := Integrable.of_bound hfc.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
  have hfpc : Continuous (fun y => f (s16a_proj S y)) := hfc.comp (s16a_continuous_proj S)
  have hfpi : Integrable (fun y => f (s16a_proj S y)) μ := Integrable.of_bound
    hfpc.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM _)
  set T : NegSobolev d m → ℝ := fun y => ‖y - s16a_proj S y‖ ^ 2 with hT
  have hTc : Continuous T := ((continuous_id.sub (s16a_continuous_proj S)).norm).pow 2
  have hTn : ∀ y, 0 ≤ T y := fun y => by positivity
  have hlt : ∫⁻ y, ENNReal.ofReal (T y) ∂μ ≤ ENNReal.ofReal (s16a_tail w S) :=
    s16a_lint_tail μ hw hw0 hμ S
  have hTi : Integrable T μ := by
    refine ⟨hTc.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ y, ‖T y‖ₑ ∂μ = ∫⁻ y, ENNReal.ofReal (T y) ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [Real.enorm_eq_ofReal (hTn y)]
      _ ≤ _ := hlt
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hTint : ∫ y, T y ∂μ ≤ s16a_tail w S := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hTn) hTc.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (s16a_tail_nonneg hw0 S) hlt
  have hpt : ∀ y, ‖f y - f (s16a_proj S y)‖ ≤ (L : ℝ) * (δ / 2 + T y / (2 * δ)) := by
    intro y
    have h1 : ‖f y - f (s16a_proj S y)‖ ≤ (L : ℝ) * ‖y - s16a_proj S y‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact hL.dist_le_mul _ _
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ L.2)
    have h2 : 0 ≤ (‖y - s16a_proj S y‖ - δ) ^ 2 := sq_nonneg _
    have : ‖y - s16a_proj S y‖ ≤ δ / 2 + ‖y - s16a_proj S y‖ ^ 2 / (2 * δ) := by
      rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
      nlinarith
    simpa [hT] using this
  rw [← integral_sub hfi hfpi, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (g := fun y => (L : ℝ) * (δ / 2 + T y / (2 * δ)))
    (((integrable_const (δ / 2)).add (hTi.div_const (2 * δ))).const_mul _)
    (Filter.Eventually.of_forall hpt)).trans ?_
  have hdiv : ∫ a, T a / (2 * δ) ∂μ = (∫ a, T a ∂μ) / (2 * δ) := integral_div _ _
  rw [integral_const_mul, integral_add (integrable_const _) (hTi.div_const _), hdiv]
  simp only [integral_const, probReal_univ, one_smul]
  refine mul_le_mul_of_nonneg_left ?_ L.2
  have : (∫ y, T y ∂μ) / (2 * δ) ≤ s16a_tail w S / (2 * δ) :=
    div_le_div_of_nonneg_right hTint (by positivity)
  linarith

/-- The finite-dimensional convergence hypothesis (against bounded continuous tests). -/
def S16aFdd (ν : ℕ → Measure (NegSobolev d m)) (G : Measure (NegSobolev d m)) : Prop :=
  ∀ (S : Finset (NonzeroLattice d)) (F : NegSobolev d m → ℝ), Continuous F →
    (∃ M, ∀ x, |F x| ≤ M) →
    Tendsto (fun n => ∫ y, F (s16a_proj S y) ∂(ν n)) atTop (𝓝 (∫ y, F (s16a_proj S y) ∂G))

/-- The tail bound passes to the limit measure. -/
theorem s16a_G_tail (ν : ℕ → Measure (NegSobolev d m)) [∀ n, IsProbabilityMeasure (ν n)]
    (G : Measure (NegSobolev d m)) [IsProbabilityMeasure G] {w : NonzeroLattice d → ℝ}
    (hw0 : ∀ k, 0 ≤ w k)
    (hν : ∀ n k, ∫⁻ y, ENNReal.ofReal (NegSobolev.coord y k ^ 2) ∂(ν n) ≤ ENNReal.ofReal (w k))
    (hfdd : S16aFdd ν G) (k : NonzeroLattice d) :
    ∫⁻ y, ENNReal.ofReal (NegSobolev.coord y k ^ 2) ∂G ≤ ENNReal.ofReal (w k) := by
  classical
  set c : NegSobolev d m → ℝ := fun y => NegSobolev.coord y k ^ 2 with hc
  have hcc : Continuous c := (s16a_continuous_coord k).pow 2
  have hcn : ∀ y, 0 ≤ c y := fun y => sq_nonneg _
  set F : ℕ → NegSobolev d m → ℝ := fun M y => min (c y) M with hF
  have hFc : ∀ M, Continuous (F M) := fun M => hcc.min continuous_const
  have hF0 : ∀ M y, 0 ≤ F M y := fun M y => le_min (hcn y) (Nat.cast_nonneg M)
  have hFb : ∀ M y, F M y ≤ M := fun M y => min_le_right _ _
  have hFproj : ∀ M y, F M (s16a_proj {k} y) = F M y := by
    intro M y
    simp only [hF, hc]
    rw [s16a_coord_proj]
    simp
  have hFint : ∀ (μ : Measure (NegSobolev d m)) [IsProbabilityMeasure μ] M,
      Integrable (F M) μ := fun μ _ M => Integrable.of_bound (hFc M).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 M y)]; exact hFb M y)
  have hle : ∀ M, ∫ y, F M y ∂G ≤ w k := by
    intro M
    have hlim := hfdd {k} (F M) (hFc M)
      ⟨M, fun y => by rw [abs_of_nonneg (hF0 M y)]; exact hFb M y⟩
    simp only [hFproj] at hlim
    refine le_of_tendsto' hlim fun n => ?_
    have h1 : ∫⁻ y, ENNReal.ofReal (F M y) ∂(ν n) ≤ ENNReal.ofReal (w k) :=
      (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (hν n k)
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint (ν n) M)
      (Filter.Eventually.of_forall (hF0 M))] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (hw0 k)).1 h1
  have hlim : Tendsto (fun M : ℕ => ∫⁻ y, ENNReal.ofReal (F M y) ∂G) atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (c y) ∂G)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun M => ?_) ?_ ?_
    · exact (Measurable.ennreal_ofReal (hFc M).measurable).aemeasurable
    · refine Filter.Eventually.of_forall fun y M M' hMM' => ?_
      exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hMM'))
    · refine Filter.Eventually.of_forall fun y => ?_
      refine ENNReal.tendsto_ofReal ?_
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨M0, hM0⟩ := exists_nat_ge (c y)
      filter_upwards [eventually_ge_atTop M0] with M hM
      simp only [hF]
      exact (min_eq_left (hM0.trans (by exact_mod_cast hM))).symm
  refine le_of_tendsto' hlim fun M => ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (hFint G M) (Filter.Eventually.of_forall (hF0 M))]
  exact ENNReal.ofReal_le_ofReal (hle M)

/-- **Weak convergence in `E_m`** from finite-dimensional convergence and uniform coordinate tails. -/
theorem s16a_weak_conv (ν : ℕ → Measure (NegSobolev d m)) [∀ n, IsProbabilityMeasure (ν n)]
    (G : Measure (NegSobolev d m)) [IsProbabilityMeasure G] {w : NonzeroLattice d → ℝ}
    (hw : Summable w) (hw0 : ∀ k, 0 ≤ w k)
    (hν : ∀ n k, ∫⁻ y, ENNReal.ofReal (NegSobolev.coord y k ^ 2) ∂(ν n) ≤ ENNReal.ofReal (w k))
    (hfdd : S16aFdd ν G) (F : NegSobolev d m → ℝ) (hFc : Continuous F) (hFb : ∃ M, ∀ x, |F x| ≤ M) :
    Tendsto (fun n => ∫ y, F y ∂(ν n)) atTop (𝓝 (∫ y, F y ∂G)) := by
  have hGt := s16a_G_tail ν G hw0 hν hfdd
  let P : ℕ → ProbabilityMeasure (NegSobolev d m) := fun n => ⟨ν n, inferInstance⟩
  let P0 : ProbabilityMeasure (NegSobolev d m) := ⟨G, inferInstance⟩
  have hP : Tendsto P atTop (𝓝 P0) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro f hfb hfL
    obtain ⟨L, hL⟩ := hfL
    obtain ⟨C, hC⟩ := hfb
    have hfb' : ∃ M, ∀ x, |f x| ≤ M := by
      refine ⟨|f 0| + C, fun x => ?_⟩
      have := hC x 0
      rw [Real.dist_eq] at this
      calc |f x| = |(f x - f 0) + f 0| := by ring_nf
        _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
        _ ≤ C + |f 0| := by linarith
        _ = _ := by ring
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ : ℝ := ε / (4 * ((L : ℝ) + 1)) with hδ
    have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
    have hδ0 : 0 < δ := by positivity
    set η : ℝ := ε ^ 2 / (16 * ((L : ℝ) + 1) ^ 2) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨S, hS⟩ := ((s16a_tail_tendsto hw).eventually (gt_mem_nhds hη0)).exists
    have hτ0 := s16a_tail_nonneg hw0 S
    -- the truncation error bound
    have hbound : (L : ℝ) * (δ / 2 + s16a_tail w S / (2 * δ)) ≤ ε / 4 := by
      have h1 : (L : ℝ) * (δ / 2) ≤ ε / 8 := by
        have : (L : ℝ) * δ ≤ ε / 4 := by
          rw [hδ, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hε]
        linarith
      have h2 : (L : ℝ) * (s16a_tail w S / (2 * δ)) ≤ ε / 8 := by
        have hτ' : s16a_tail w S ≤ ε ^ 2 / (16 * ((L : ℝ) + 1) ^ 2) := hS.le
        have hq : 0 ≤ s16a_tail w S / (2 * δ) := by positivity
        calc (L : ℝ) * (s16a_tail w S / (2 * δ))
            ≤ ((L : ℝ) + 1) * (s16a_tail w S / (2 * δ)) :=
              mul_le_mul_of_nonneg_right (by linarith) hq
          _ ≤ ((L : ℝ) + 1) * ((ε ^ 2 / (16 * ((L : ℝ) + 1) ^ 2)) / (2 * δ)) := by
              gcongr
          _ = ε / 8 := by rw [hδ]; field_simp; ring
      calc (L : ℝ) * (δ / 2 + s16a_tail w S / (2 * δ))
          = (L : ℝ) * (δ / 2) + (L : ℝ) * (s16a_tail w S / (2 * δ)) := by ring
        _ ≤ ε / 8 + ε / 8 := add_le_add h1 h2
        _ = ε / 4 := by ring
    have hmid := hfdd S f hL.continuous hfb'
    rw [Metric.tendsto_atTop] at hmid
    obtain ⟨N0, hN0⟩ := hmid (ε / 2) (by positivity)
    refine ⟨N0, fun n hn => ?_⟩
    have c1 := s16a_close (ν n) hw hw0 (hν n) hL hfb' S hδ0
    have c2 := s16a_close G hw hw0 hGt hL hfb' S hδ0
    have c3 := hN0 n hn
    rw [Real.dist_eq] at c3 ⊢
    show |∫ y, f y ∂(ν n) - ∫ y, f y ∂G| < ε
    calc |∫ y, f y ∂(ν n) - ∫ y, f y ∂G|
        = |(∫ y, f y ∂(ν n) - ∫ y, f (s16a_proj S y) ∂(ν n)) +
            (∫ y, f (s16a_proj S y) ∂(ν n) - ∫ y, f (s16a_proj S y) ∂G) -
            (∫ y, f y ∂G - ∫ y, f (s16a_proj S y) ∂G)| := by ring_nf
      _ ≤ |∫ y, f y ∂(ν n) - ∫ y, f (s16a_proj S y) ∂(ν n)| +
            |∫ y, f (s16a_proj S y) ∂(ν n) - ∫ y, f (s16a_proj S y) ∂G| +
            |∫ y, f y ∂G - ∫ y, f (s16a_proj S y) ∂G| := by
          refine (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ < ε := by linarith
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hP)
    ⟨⟨F, hFc⟩, by
      obtain ⟨M, hM⟩ := hFb
      refine ⟨2 * M, fun x y => ?_⟩
      show |F x - F y| ≤ 2 * M
      have h1 := hM x
      have h2 := hM y
      rw [abs_le] at h1 h2
      rw [abs_le]; constructor <;> linarith⟩
  simpa [P, P0] using this

end HRS.MC.SEdge.S16a

end
