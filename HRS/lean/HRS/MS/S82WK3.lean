import HRS.MS.S82WK2

/-!
# S8.2 A04 (S82W), part 4: jets, support and eventual triviality of the cut-off `Θ_m`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

section theta3
variable {d N : ℕ}

def wT1 (X : EucConfig d N) : ℝ := ∑ p : Fin N × Fin N, wb1 p X

def wT2 (X : EucConfig d N) : ℝ := ∑ p : Fin N × Fin N, wb2 p X + wT1 X ^ 2

lemma wTheta_jets {m : ℝ} (hm : 1 ≤ m) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    ‖fderiv ℝ (wTheta d N m) X‖ ≤ wT1 X ∧ ‖fderiv ℝ (fderiv ℝ (wTheta d N m)) X‖ ≤ wT2 X := by
  have hX' : ∀ p : Fin N × Fin N, p.1 ≠ p.2 → X p.1 ≠ X p.2 := fun p hp h => hX ⟨p.1, p.2, hp, h⟩
  have := w_prod_finset (E := EucConfig d N) Finset.univ (fun p => wfac (d := d) m p) (wfac_contDiff m)
    (fun p y => wfac_01 m p y) (fun p => wb1 p X) (fun p => wb2 p X) X
    (fun p _ => (wfac_jets hm p (hX' p)).1) (fun p _ => (wfac_jets hm p (hX' p)).2)
  exact this

lemma wb1_tame (p : Fin N × Fin N) : u4Tame (fun X : EucConfig d N => wb1 p X) := by
  unfold wb1
  by_cases h : p.1 = p.2
  · simp only [h, ite_true]; exact u4Tame_const _
  · simp only [h, ite_false]
    exact u4Tame_const_mul _ (u4Tame_pole h (by norm_num))

lemma wb2_tame (p : Fin N × Fin N) : u4Tame (fun X : EucConfig d N => wb2 p X) := by
  unfold wb2
  by_cases h : p.1 = p.2
  · simp only [h, ite_true]; exact u4Tame_const _
  · simp only [h, ite_false]
    exact u4Tame_const_mul _ (u4Tame_pole h (by norm_num))

lemma wT1_tame : u4Tame (wT1 (d := d) (N := N)) := u4Tame_sum _ _ fun p _ => wb1_tame p

lemma wT2_tame : u4Tame (wT2 (d := d) (N := N)) := by
  have h1 := u4Tame_sum (Finset.univ : Finset (Fin N × Fin N)) (fun p (X : EucConfig d N) => wb2 p X)
    fun p _ => wb2_tame p
  have h2 := u4Tame_mul (wT1_tame (d := d) (N := N)) (wT1_tame (d := d) (N := N))
  have := u4Tame_add h1 h2
  convert this using 2 with X
  simp [wT2, sq]

lemma wT1_nonneg (hw : 0 ≤ wB) (X : EucConfig d N) (hX : X ∉ eucCollisionSet d N) : 0 ≤ wT1 X := by
  refine Finset.sum_nonneg fun p _ => ?_
  unfold wb1
  split_ifs with h
  · linarith
  · have hne : 0 < ‖X p.1 - X p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 (fun h' => hX ⟨p.1, p.2, h, h'⟩))
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hne.le _)

lemma wTheta_support {m : ℝ} {X : EucConfig d N} (h : wTheta d N m X ≠ 0) :
    (∀ i, (1 / m ^ 2) * ‖X i‖ ^ 2 < 2) ∧ ∀ i j, i ≠ j → 1 < m ^ 2 * ‖X i - X j‖ ^ 2 := by
  have h' := Finset.prod_ne_zero_iff.1 h
  constructor
  · intro i
    have := h' (i, i) (Finset.mem_univ _)
    simp only [wfac, ite_true] at this
    by_contra hc
    exact this (wc_zero (not_lt.1 hc))
  · intro i j hij
    have := h' (i, j) (Finset.mem_univ _)
    simp only [wfac, hij, ite_false] at this
    by_contra hc
    exact this (by rw [wc_one (not_lt.1 hc)]; norm_num)

/-- the closed set containing the support of `Θ_m` -/
def wS (d N : ℕ) (m : ℝ) : Set (EucConfig d N) :=
  {X | (∀ i, (1 / m ^ 2) * ‖X i‖ ^ 2 ≤ 2) ∧ ∀ i j, i ≠ j → 1 ≤ m ^ 2 * ‖X i - X j‖ ^ 2}

lemma wS_closed (m : ℝ) : IsClosed (wS d N m) := by
  unfold wS
  rw [Set.setOf_and]
  refine IsClosed.inter ?_ ?_
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  · rw [Set.setOf_forall]
    refine isClosed_iInter fun i => ?_
    rw [Set.setOf_forall]
    refine isClosed_iInter fun j => ?_
    by_cases h : i = j
    · simp [h]
    · simp only [h, ne_eq, not_false_eq_true, forall_const]
      exact isClosed_le continuous_const (by fun_prop)

lemma wS_compact {m : ℝ} (hm : 0 < m) : IsCompact (wS d N m) := by
  refine Metric.isCompact_of_isClosed_isBounded (wS_closed m) ?_
  refine (Metric.isBounded_closedBall (x := (0 : EucConfig d N)) (r := 2 * m)).subset fun X hX => ?_
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h2 := hX.1 i
  have : ‖X i‖ ^ 2 ≤ 2 * m ^ 2 := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)] at h2; linarith
  have : ‖X i‖ ^ 2 ≤ (2 * m) ^ 2 := by nlinarith
  exact le_of_sq_le_sq this (by positivity)

lemma wS_subset_compl {m : ℝ} : wS d N m ⊆ (eucCollisionSet d N)ᶜ := by
  intro X hX hc
  obtain ⟨i, j, hij, hXij⟩ := hc
  have := hX.2 i j hij
  rw [hXij, sub_self, norm_zero] at this
  norm_num at this

lemma wTheta_zero_off {m : ℝ} {X : EucConfig d N} (hX : X ∉ wS d N m) : wTheta d N m X = 0 := by
  by_contra h
  obtain ⟨a, b⟩ := wTheta_support h
  exact hX ⟨fun i => (a i).le, fun i j hij => (b i j hij).le⟩

lemma wTheta_tsupport {m : ℝ} : tsupport (wTheta d N m) ⊆ wS d N m := by
  refine closure_minimal ?_ (wS_closed m)
  intro X hX
  by_contra h
  exact hX (wTheta_zero_off h)

lemma wTheta_hasCompactSupport {m : ℝ} (hm : 0 < m) : HasCompactSupport (wTheta d N m) :=
  HasCompactSupport.intro (wS_compact hm) fun X hX => wTheta_zero_off hX

lemma wTheta_eventually_one {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ Y in 𝓝 X, wTheta d N ((n : ℝ) + 1) Y = 1 := by
  have hpos : ∀ i j, i ≠ j → 0 < ‖X i - X j‖ := fun i j h =>
    norm_pos_iff.2 (sub_ne_zero.2 (fun h' => hX ⟨i, j, h, h'⟩))
  have hY : ∀ᶠ Y in 𝓝 X, (∀ i, ‖Y i‖ < ‖X i‖ + 1) ∧
      ∀ i j, i ≠ j → ‖X i - X j‖ / 2 < ‖Y i - Y j‖ := by
    refine (Filter.eventually_all.2 fun i => ?_).and (Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun j => ?_)
    · exact ((continuous_norm.comp (continuous_apply i)).continuousAt).eventually_lt continuousAt_const
        (lt_add_one _)
    · by_cases h : i = j
      · exact Eventually.of_forall fun Y hij => absurd h hij
      · have h1 : ‖X i - X j‖ / 2 < ‖X i - X j‖ := by linarith [hpos i j h]
        have := (continuousAt_const (y := ‖X i - X j‖ / 2)).eventually_lt
          ((show Continuous fun Y : EucConfig d N => ‖Y i - Y j‖ by fun_prop).continuousAt) h1
        filter_upwards [this] with Y hY _ using hY
  have hn : ∀ᶠ n : ℕ in atTop, (∀ i, ‖X i‖ ≤ n) ∧ ∀ i j, i ≠ j → 8 / ‖X i - X j‖ ^ 2 ≤ n := by
    refine (Filter.eventually_all.2 fun i => ?_).and (Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun j => ?_)
    · exact tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    · by_cases h : i = j
      · exact Eventually.of_forall fun n hij => absurd h hij
      · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 / ‖X i - X j‖ ^ 2)] with n hn _ using hn
  filter_upwards [hn] with n hn
  filter_upwards [hY] with Y hY
  unfold wTheta
  refine Finset.prod_eq_one fun p _ => ?_
  obtain ⟨i, j⟩ := p
  have hm1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  by_cases h : i = j
  · subst h
    simp only [wfac, ite_true]
    refine wc_one ?_
    have h1 : ‖Y i‖ ≤ (n : ℝ) + 1 := by linarith [hY.1 i, hn.1 i]
    have h2 : ‖Y i‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    linarith
  · simp only [wfac, h, ite_false]
    have hr := hpos i j h
    have e : wc (((n : ℝ) + 1) ^ 2 * ‖Y i - Y j‖ ^ 2) = 0 := by
      refine wc_zero ?_
      have h1 := hn.2 i j h
      have h2 : 8 ≤ (n : ℝ) * ‖X i - X j‖ ^ 2 := by
        rw [div_le_iff₀ (by positivity)] at h1; linarith
      have h3 : (‖X i - X j‖ / 2) ^ 2 ≤ ‖Y i - Y j‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) (hY.2 i j h).le 2
      have h4 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      have h5 : (n : ℝ) * ‖X i - X j‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2 := by
        have : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by linarith
        exact mul_le_mul_of_nonneg_right this (by positivity)
      calc (2 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 * (‖X i - X j‖ / 2) ^ 2 := by nlinarith
        _ ≤ ((n : ℝ) + 1) ^ 2 * ‖Y i - Y j‖ ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    rw [e]; norm_num

end theta3

end HRS.MS.S82W
