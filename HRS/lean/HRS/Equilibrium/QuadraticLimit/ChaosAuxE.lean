import Mathlib
import HRS.Equilibrium.QuadraticLimit.ChaosAuxB

/-!
# Lemma 7.5: `L²` limits of the linear and quadratic forms (prefix `q08c_ch_`)

For a measurable family `G` with Gaussian marginals `N(0, C_n)` (`q08c_ch_Setup`): the partial
sums `∑_{i<L} w_i G_i` and `½ ∑_{i,j<L} H_ij (G_iG_j - C_ij)` are `L²`-Cauchy (second-moment bound
of `ChaosAuxB` plus summability tails), and `L²` is complete; measurable representatives of the
limits are taken in `Lp`.
-/
open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section
namespace HRS.Q08

/-- A measurable family `G` with Gaussian finite-dimensional marginals `N(0, C_n)`. -/
structure q08c_ch_Setup {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G : ℕ → Ω → ℝ)
    (C : ℕ → ℕ → ℝ) : Prop where
  meas : ∀ i, Measurable (G i)
  symm : ∀ i j, C i j = C j i
  psd : ∀ (n : ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j
  le_one : ∀ (n : ℕ) (v : ℕ → ℝ), ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j ≤
    ∑ i ∈ Finset.range n, v i ^ 2
  law : ∀ n : ℕ, P.map (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) =
    multivariateGaussian 0 (Matrix.of fun i j : Fin n => C i j)


theorem q08c_ch_l2_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → ℝ) (hS2 : ∀ L, MemLp (S L) 2 P)
    (hcauchy : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∫ ω, (S m ω - S n ω) ^ 2 ∂P < ε) :
    ∃ Q : Ω → ℝ, Measurable Q ∧
      Tendsto (fun L => ∫⁻ ω, ‖Q ω - S L ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  set f : ℕ → Lp ℝ 2 P := fun L => (hS2 L).toLp (S L) with hf
  have hnorm : ∀ m n, ‖f m - f n‖ ^ 2 = ∫ ω, (S m ω - S n ω) ^ 2 ∂P := by
    intro m n
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (f m) (f n), (hS2 m).coeFn_toLp, (hS2 n).coeFn_toLp] with ω h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply, hf] at h2 h3 ⊢
    rw [h2, h3]
    simp [sq]
  have hcs : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have := hN m hm n hn
    rw [← hnorm] at this
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨⇑F, (Lp.stronglyMeasurable F).measurable, ?_⟩
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' f F).1 hF
  have h2 : ∀ L, ∫⁻ ω, ‖F ω - S L ω‖ₑ ^ 2 ∂P = (eLpNorm (⇑(f L) - ⇑F) 2 P) ^ 2 := by
    intro L
    have hfL : eLpNorm (⇑(f L) - ⇑F) 2 P = eLpNorm (⇑F - S L) 2 P := by
      rw [← eLpNorm_neg]
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hS2 L).coeFn_toLp] with ω h
      simp only [Pi.neg_apply, Pi.sub_apply, hf, h]; ring
    rw [hfL]
    have := eLpNorm_nnreal_pow_eq_lintegral (μ := P) (f := ⇑F - S L) (p := 2) (by norm_num)
      ((Lp.aestronglyMeasurable F).sub (hS2 L).aestronglyMeasurable)
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two, Pi.sub_apply] at this
    exact this.symm
  simp_rw [h2]
  have := ((ENNReal.continuous_pow 2).tendsto 0).comp h1
  rw [show (0 : ℝ≥0∞) ^ 2 = 0 by simp] at this
  exact this


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {G : ℕ → Ω → ℝ} {C : ℕ → ℕ → ℝ}

omit [IsProbabilityMeasure P] in
theorem q08c_ch_Setup.vec_meas (h : q08c_ch_Setup P G C) (n : ℕ) :
    Measurable (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) := by
  have := h.meas
  fun_prop

/-- Linear functionals of the family are `L²`, with second moment `≤ ∑ w²`. -/
theorem q08c_ch_lin_facts (h : q08c_ch_Setup P G C) (n : ℕ) (w : Fin n → ℝ) :
    MemLp (fun ω => ∑ i : Fin n, w i * G i ω) 2 P ∧
      ∫ ω, (∑ i : Fin n, w i * G i ω) ^ 2 ∂P ≤ ∑ i : Fin n, w i ^ 2 := by
  obtain ⟨hS, hle'⟩ := q08c_ch_cov_fin C h.symm h.psd h.le_one n
  set X : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 fun i : Fin n => G i ω with hXdef
  have hXm : Measurable X := h.vec_meas n
  have hfe : (fun ω => ∑ i : Fin n, w i * G i ω) = fun ω => q08c_ch_lin w (X ω) := by
    funext ω; simp [q08c_ch_lin, hXdef]
  have hint : Integrable (fun ω => (q08c_ch_lin w (X ω)) ^ 2) P := by
    have h1 := q08c_ch_lin_int hS w 2
    rw [← h.law n] at h1
    exact (integrable_map_measure (g := fun z => q08c_ch_lin w z ^ 2) (f := X)
      (((q08c_ch_lin_meas w).pow_const 2).aestronglyMeasurable) hXm.aemeasurable).1 h1
  have hmeasf : Measurable (fun ω => q08c_ch_lin w (X ω)) := (q08c_ch_lin_meas w).comp hXm
  constructor
  · rw [hfe]
    exact (memLp_two_iff_integrable_sq hmeasf.aestronglyMeasurable).2 hint
  · have hfe' : ∀ ω, ∑ i : Fin n, w i * G i ω = q08c_ch_lin w (X ω) := fun ω => by
      simp [q08c_ch_lin, hXdef]
    simp_rw [hfe']
    have h2 := integral_map (μ := P) hXm.aemeasurable
      (f := fun z => q08c_ch_lin w z ^ 2) (((q08c_ch_lin_meas w).pow_const 2).aestronglyMeasurable)
    rw [h.law n, q08c_ch_second hS w] at h2
    rw [← h2]
    exact hle' w

theorem q08c_ch_pair_int_P (h : q08c_ch_Setup P G C) (n : ℕ) (u v : Fin n → ℝ) :
    Integrable (fun ω => (∑ i : Fin n, u i * G i ω) ^ 2 * (∑ i : Fin n, v i * G i ω) ^ 2) P := by
  obtain ⟨hS, hle'⟩ := q08c_ch_cov_fin C h.symm h.psd h.le_one n
  set X : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 fun i : Fin n => G i ω with hXdef
  have hXm : Measurable X := h.vec_meas n
  have h1 := q08c_ch_pair_int hS u v
  rw [← h.law n] at h1
  have := (integrable_map_measure (g := fun z => q08c_ch_lin u z ^ 2 * q08c_ch_lin v z ^ 2) (f := X)
    ((((q08c_ch_lin_meas u).pow_const 2).mul ((q08c_ch_lin_meas v).pow_const 2)).aestronglyMeasurable)
    hXm.aemeasurable).1 h1
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [q08c_ch_lin, hXdef]

theorem q08c_ch_prod_memLp (h : q08c_ch_Setup P G C) (i j : ℕ) :
    MemLp (fun ω => G i ω * G j ω) 2 P := by
  set n := max i j + 1 with hn
  have hi : i < n := by omega
  have hj : j < n := by omega
  have hmeas : Measurable (fun ω => G i ω * G j ω) := (h.meas i).mul (h.meas j)
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  have := q08c_ch_pair_int_P h n (Pi.single ⟨i, hi⟩ 1) (Pi.single ⟨j, hj⟩ 1)
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [Pi.single_apply, mul_pow]

theorem q08c_ch_tail {β : Type*} (f : β → ℝ) (hf : Summable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset β, ∀ t : Finset β, Disjoint t s → ∑ b ∈ t, f b < ε := by
  obtain ⟨s, hs⟩ := (summable_iff_vanishing.1 hf) (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)
  refine ⟨s, fun t ht => ?_⟩
  have := hs t ht
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
  exact lt_of_abs_lt this

theorem q08c_ch_sum_lt (m n : ℕ) (hmn : m ≤ n) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, (if i < m then f i else 0) = ∑ i ∈ Finset.range m, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega

theorem q08c_ch_lin_limit (h : q08c_ch_Setup P G C) (w : ℕ → ℝ) (hw : Summable fun i => w i ^ 2) :
    ∃ Lin : Ω → ℝ, Measurable Lin ∧
      Tendsto (fun L => ∫⁻ ω, ‖Lin ω - ∑ i ∈ Finset.range L, w i * G i ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  have hS2 : ∀ L, MemLp (fun ω => ∑ i ∈ Finset.range L, w i * G i ω) 2 P := by
    intro L
    have := (q08c_ch_lin_facts h L (fun i => w i)).1
    simpa [Finset.sum_range] using this
  refine q08c_ch_l2_limit P (fun L ω => ∑ i ∈ Finset.range L, w i * G i ω) hS2 ?_
  intro ε hε
  obtain ⟨s, hs⟩ := q08c_ch_tail _ hw ε hε
  set M := s.sup id + 1 with hM
  have hsM : ∀ i ∈ s, i < M := fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have key : ∀ m n, M ≤ m → m ≤ n →
      ∫ ω, (∑ i ∈ Finset.range m, w i * G i ω - ∑ i ∈ Finset.range n, w i * G i ω) ^ 2 ∂P < ε := by
    intro m n hMm hmn
    set w' : Fin n → ℝ := fun i => if (i : ℕ) < m then 0 else w i with hw'
    have hid : ∀ ω, ∑ i ∈ Finset.range m, w i * G i ω - ∑ i ∈ Finset.range n, w i * G i ω =
        - ∑ i : Fin n, w' i * G i ω := by
      intro ω
      have e1 := q08c_ch_sum_lt m n hmn (fun i => w i * G i ω)
      have e2 : ∑ i : Fin n, w' i * G i ω = ∑ i ∈ Finset.range n, (if i < m then 0 else w i) * G i ω := by
        rw [← Finset.sum_range (fun i => (if i < m then 0 else w i) * G i ω)]
      have e3 : ∑ i ∈ Finset.range n, w i * G i ω =
          ∑ i ∈ Finset.range n, (if i < m then w i * G i ω else 0) +
            ∑ i ∈ Finset.range n, (if i < m then 0 else w i) * G i ω := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      rw [e2, e3, e1]; ring
    simp_rw [hid, neg_sq]
    refine lt_of_le_of_lt (q08c_ch_lin_facts h n w').2 ?_
    have e4 : ∑ i : Fin n, w' i ^ 2 = ∑ i ∈ (Finset.range n).filter (fun i => ¬ i < m), w i ^ 2 := by
      rw [Finset.sum_filter, ← Finset.sum_range (fun i => (if i < m then 0 else w i) ^ 2)]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp_all
    rw [e4]
    refine hs _ ?_
    rw [Finset.disjoint_left]
    intro i hi his
    have := hsM i his
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    omega
  refine ⟨M, fun m hm n hn => ?_⟩
  rcases le_total m n with hmn | hmn
  · exact key m n hm hmn
  · have := key n m hn hmn
    simpa [sub_sq_comm] using this

theorem q08c_ch_quad_limit (h : q08c_ch_Setup P G C) (H : ℕ → ℕ → ℝ) (hHs : ∀ i j, H i j = H j i)
    (hH : Summable (fun ij : ℕ × ℕ => H ij.1 ij.2 ^ 2)) :
    ∃ Q : Ω → ℝ, Measurable Q ∧
      Tendsto (fun L => ∫⁻ ω, ‖Q ω - (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          H i j * (G i ω * G j ω - C i j)‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  have hS2 : ∀ L, MemLp (fun ω => (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      H i j * (G i ω * G j ω - C i j)) 2 P := by
    intro L
    have hin : ∀ i, MemLp (fun ω => ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω - C i j)) 2 P := by
      intro i
      refine memLp_finsetSum (f := fun j ω => H i j * (G i ω * G j ω - C i j)) _ fun j _ => ?_
      have h1 : MemLp (fun ω => G i ω * G j ω - C i j) 2 P :=
        (q08c_ch_prod_memLp h i j).sub (memLp_const (C i j))
      exact h1.const_mul (H i j)
    have hsum : MemLp (fun ω => ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
        H i j * (G i ω * G j ω - C i j)) 2 P :=
      memLp_finsetSum (f := fun i ω => ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω - C i j)) _
        fun i _ => hin i
    exact hsum.const_mul (1 / 2)
  refine q08c_ch_l2_limit P (fun L ω => (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    H i j * (G i ω * G j ω - C i j)) hS2 ?_
  intro ε hε
  obtain ⟨s, hs⟩ := q08c_ch_tail _ hH ε hε
  set M := s.sup (fun p => max p.1 p.2) + 1 with hM
  have hsM : ∀ p ∈ s, p.1 < M ∧ p.2 < M := fun p hp =>
    ⟨Nat.lt_succ_of_le ((le_max_left _ _).trans (Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp)),
     Nat.lt_succ_of_le ((le_max_right _ _).trans (Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp))⟩
  have key : ∀ m n, M ≤ m → m ≤ n →
      ∫ ω, ((1 / 2) * ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, H i j * (G i ω * G j ω - C i j) -
        (1 / 2) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, H i j * (G i ω * G j ω - C i j)) ^ 2 ∂P
        < ε := by
    intro m n hMm hmn
    set A : Fin n → Fin n → ℝ := fun i j => if (i : ℕ) < m ∧ (j : ℕ) < m then 0 else H i j with hA
    have hAs : ∀ i j, A i j = A j i := fun i j => by
      simp only [hA, hHs i j, and_comm]
    have hid : ∀ ω, (1 / 2) * ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, H i j * (G i ω * G j ω - C i j) -
        (1 / 2) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, H i j * (G i ω * G j ω - C i j) =
        - ((1 / 2) * ∑ i : Fin n, ∑ j : Fin n, A i j * (G i ω * G j ω - C i j)) := by
      intro ω
      set g : ℕ → ℕ → ℝ := fun i j => H i j * (G i ω * G j ω - C i j) with hg
      have e1 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < m ∧ j < m then g i j else 0) =
          ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, g i j := by
        have : ∀ i, ∑ j ∈ Finset.range n, (if i < m ∧ j < m then g i j else 0) =
            if i < m then ∑ j ∈ Finset.range m, g i j else 0 := by
          intro i
          by_cases hi : i < m
          · simp only [hi, true_and, if_true]
            exact q08c_ch_sum_lt m n hmn (g i)
          · simp [hi]
        simp_rw [this]
        exact q08c_ch_sum_lt m n hmn (fun i => ∑ j ∈ Finset.range m, g i j)
      have e2 : ∑ i : Fin n, ∑ j : Fin n, A i j * (G i ω * G j ω - C i j) =
          ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < m ∧ j < m then 0 else g i j) := by
        rw [Finset.sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hA, hg]
        split_ifs <;> simp
      have e3 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g i j =
          ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < m ∧ j < m then g i j else 0) +
            ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < m ∧ j < m then 0 else g i j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      rw [e2, e3, e1]; ring
    simp_rw [hid, neg_sq]
    have hb := q08c_ch_bound_raw P G h.meas C h.symm h.psd h.le_one n (h.law n) A hAs
    have e4 : ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 =
        ∑ p ∈ ((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => ¬ (p.1 < m ∧ p.2 < m)),
          H p.1 p.2 ^ 2 := by
      rw [Finset.sum_filter, Finset.sum_product, Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hA]
      split_ifs <;> simp_all
    have e5 : ∑ p ∈ ((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => ¬ (p.1 < m ∧ p.2 < m)),
        H p.1 p.2 ^ 2 < ε := by
      refine hs _ ?_
      rw [Finset.disjoint_left]
      intro p hp hps
      have := hsM p hps
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      omega
    rw [e4] at hb
    linarith
  refine ⟨M, fun m hm n hn => ?_⟩
  rcases le_total m n with hmn | hmn
  · exact key m n hm hmn
  · have := key n m hn hmn
    simpa [sub_sq_comm] using this

end HRS.Q08
