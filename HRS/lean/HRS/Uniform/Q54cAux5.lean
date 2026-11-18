import HRS.Uniform.Q54cAux3
import HRS.Uniform.Q54cAux4

/-!
# Q54c, part 5: Itô sums

For a path `g` (continuous on `[0,T]`, `g 0 = 0`) with values in a Hilbert space `H` and a `C¹` path
`y : [0,t] → H`, the Itô sums `∑_i ⟨g(s_{i+1}) - g(s_i), y(s_i)⟩` along the uniform grid
`s_i = min (iT/(N+1)) t` converge to `⟨g_t, y_t⟩ - ∫_0^t ⟨g_σ, y'_σ⟩ dσ` (summation by parts).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The grid `τ_i = i T/(N+1)`. -/
def gridPt (T : ℝ) (N i : ℕ) : ℝ := (i : ℝ) * T / ((N : ℝ) + 1)

theorem gridPt_zero (T : ℝ) (N : ℕ) : gridPt T N 0 = 0 := by simp [gridPt]

theorem gridPt_last (T : ℝ) (N : ℕ) : gridPt T N (N + 1) = T := by
  unfold gridPt
  have : ((N : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem gridPt_mono {T : ℝ} (hT : 0 ≤ T) (N : ℕ) : Monotone (gridPt T N) := by
  intro i j hij
  unfold gridPt
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  have h1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [div_le_div_iff_of_pos_right h1]
  exact mul_le_mul_of_nonneg_right this hT

theorem gridPt_succ_sub (T : ℝ) (N i : ℕ) : gridPt T N (i + 1) - gridPt T N i = T / ((N : ℝ) + 1) := by
  unfold gridPt
  have : ((N : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem gridPt_le {T : ℝ} (hT : 0 ≤ T) (N : ℕ) {i : ℕ} (hi : i ≤ N + 1) : gridPt T N i ≤ T :=
  (gridPt_mono hT N hi).trans_eq (gridPt_last T N)

theorem gridPt_nonneg {T : ℝ} (hT : 0 ≤ T) (N i : ℕ) : 0 ≤ gridPt T N i := by
  unfold gridPt; positivity

/-- The Itô sum along the grid truncated at `t`. -/
def isum (G : ℝ → H) (y : ℝ → H) (T t : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), inner ℝ (G (min (gridPt T N (i + 1)) t) - G (min (gridPt T N i) t))
    (y (min (gridPt T N i) t))

section Conv

variable {g y y' : ℝ → H} {T t : ℝ}

/-- FTC for a `C¹` path on `[0,t]`. -/
theorem ftc_path (hy : ∀ σ ∈ Set.Icc 0 t, HasDerivWithinAt y (y' σ) (Set.Icc 0 t) σ)
    (hy' : ContinuousOn y' (Set.Icc 0 t)) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ t) :
    ∫ σ in u..v, y' σ = y v - y u := by
  have hsub : Set.Icc u v ⊆ Set.Icc 0 t := Set.Icc_subset_Icc hu hv
  have hcont : ContinuousOn y (Set.Icc u v) := by
    intro σ hσ
    exact (hy σ (hsub hσ)).continuousWithinAt.mono hsub
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le huv hcont ?_ ?_
  · intro σ hσ
    have hσ0 : σ ∈ Set.Ioo (0 : ℝ) t := ⟨hu.trans_lt hσ.1, hσ.2.trans_le hv⟩
    have := (hy σ ⟨hσ0.1.le, hσ0.2.le⟩).hasDerivAt (Icc_mem_nhds hσ0.1 hσ0.2)
    exact this.hasDerivWithinAt
  · exact (hy'.mono hsub).intervalIntegrable_of_Icc huv

theorem inner_intervalIntegral (c : H) {f : ℝ → H} {u v : ℝ} (hf : IntervalIntegrable f volume u v) :
    inner ℝ c (∫ σ in u..v, f σ) = ∫ σ in u..v, inner ℝ c (f σ) := by
  rcases le_total u v with h | h
  · rw [intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h]
    exact (integral_inner (hf.1) c).symm
  · rw [intervalIntegral.integral_of_ge h, intervalIntegral.integral_of_ge h, inner_neg_right]
    rw [integral_inner (hf.symm.1) c]

end Conv

section Abel

variable {g y y' : ℝ → H} {T t : ℝ}

/-- Summation by parts: the Itô sums converge to `⟨g_t, y_t⟩ - ∫_0^t ⟨g, y'⟩`. -/
theorem isum_tendsto (hT : 0 ≤ T) (ht : t ∈ Set.Icc 0 T) (hg : ContinuousOn g (Set.Icc 0 T))
    (hg0 : g 0 = 0) (hy : ∀ σ ∈ Set.Icc 0 t, HasDerivWithinAt y (y' σ) (Set.Icc 0 t) σ)
    (hy' : ContinuousOn y' (Set.Icc 0 t)) :
    Tendsto (fun N => isum g y T t N) atTop
      (𝓝 (inner ℝ (g t) (y t) - ∫ σ in Set.Icc 0 t, inner ℝ (g σ) (y' σ))) := by
  classical
  obtain ⟨Y, hY⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hy'
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans (hY 0 ⟨le_rfl, ht.1⟩)
  have hguc := isCompact_Icc.uniformContinuousOn_of_continuous hg
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / (2 * (Y * t + 1)) with hε'
  have hpos : 0 < Y * t + 1 := by have := ht.1; positivity
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.1 hguc ε' hε'0
  obtain ⟨N0, hN0⟩ := exists_nat_gt (T / δ)
  refine ⟨N0, fun N hN => ?_⟩
  set s : ℕ → ℝ := fun i => min (gridPt T N i) t with hs
  have hs0 : s 0 = 0 := by simp [hs, gridPt_zero, ht.1]
  have hsN : s (N + 1) = t := by simp [hs, gridPt_last, ht.2]
  have hsmono : Monotone s := fun i j hij => min_le_min_right _ (gridPt_mono hT N hij)
  have hst : ∀ i, s i ∈ Set.Icc 0 t := fun i =>
    ⟨le_min (gridPt_nonneg hT N i) ht.1, min_le_right _ _⟩
  have hcell : ∀ i, s (i + 1) - s i ≤ T / ((N : ℝ) + 1) := by
    intro i
    have hm := gridPt_mono hT N (Nat.le_succ i)
    have h1 : s (i + 1) - s i ≤ gridPt T N (i + 1) - gridPt T N i := by
      simp only [hs]
      rcases le_total (gridPt T N (i + 1)) t with h | h
      · rw [min_eq_left h, min_eq_left (hm.trans h)]
      · rcases le_total (gridPt T N i) t with h' | h'
        · rw [min_eq_right h, min_eq_left h']; linarith
        · rw [min_eq_right h, min_eq_right h']; linarith
    rw [gridPt_succ_sub] at h1; exact h1
  have hN1 : T / δ < (N : ℝ) + 1 := by
    have : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hdel : T / ((N : ℝ) + 1) < δ := by
    have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hNp]
    rw [div_lt_iff₀ hδ] at hN1
    linarith
  have hsub : ∀ i, Set.uIcc (s i) (s (i + 1)) ⊆ Set.uIcc 0 t := by
    intro i
    rw [Set.uIcc_of_le ht.1]
    exact Set.uIcc_subset_Icc (hst i) (hst (i + 1))
  have hc : ContinuousOn (fun σ => inner ℝ (g σ) (y' σ)) (Set.Icc 0 t) :=
    ContinuousOn.inner (hg.mono (Set.Icc_subset_Icc_right ht.2)) hy'
  have hint : ∀ i, IntervalIntegrable (fun σ => inner ℝ (g σ) (y' σ)) volume (s i) (s (i + 1)) :=
    fun i => (hc.intervalIntegrable_of_Icc ht.1).mono_set (hsub i)
  have hint' : ∀ i, IntervalIntegrable y' volume (s i) (s (i + 1)) :=
    fun i => (hy'.intervalIntegrable_of_Icc ht.1).mono_set (hsub i)
  have hint'' : ∀ (c : H) (i : ℕ), IntervalIntegrable (fun σ => inner ℝ c (y' σ)) volume (s i) (s (i + 1)) :=
    fun c i => ((continuousOn_const.inner hy').intervalIntegrable_of_Icc ht.1).mono_set (hsub i)
  have hftc : ∀ i, y (s (i + 1)) - y (s i) = ∫ σ in s i..s (i + 1), y' σ := fun i =>
    (ftc_path hy hy' (hst i).1 (hsmono (Nat.le_succ i)) (hst (i + 1)).2).symm
  have hsum1 : ∑ i ∈ Finset.range (N + 1), (inner ℝ (g (s (i + 1))) (y (s (i + 1))) -
      inner ℝ (g (s i)) (y (s i))) = inner ℝ (g t) (y t) := by
    rw [Finset.sum_range_sub (fun i => inner ℝ (g (s i)) (y (s i))), hsN, hs0, hg0]
    simp
  have hI : (∫ σ in Set.Icc 0 t, inner ℝ (g σ) (y' σ)) =
      ∑ i ∈ Finset.range (N + 1), ∫ σ in s i..s (i + 1), inner ℝ (g σ) (y' σ) := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun i _ => hint i), hs0, hsN,
      intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
  have hisum : isum g y T t N = ∑ i ∈ Finset.range (N + 1), (inner ℝ (g (s (i + 1))) (y (s (i + 1))) -
      inner ℝ (g (s i)) (y (s i)) - inner ℝ (g (s (i + 1))) (y (s (i + 1)) - y (s i))) := by
    unfold isum
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hs, inner_sub_left, inner_sub_right]
    ring
  have hBI : ∀ i, inner ℝ (g (s (i + 1))) (y (s (i + 1)) - y (s i)) -
      (∫ σ in s i..s (i + 1), inner ℝ (g σ) (y' σ)) =
      ∫ σ in s i..s (i + 1), inner ℝ (g (s (i + 1)) - g σ) (y' σ) := by
    intro i
    rw [hftc i, inner_intervalIntegral _ (hint' i), ← intervalIntegral.integral_sub (hint'' _ i) (hint i)]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [inner_sub_left]
  have hdiff : (inner ℝ (g t) (y t) - ∫ σ in Set.Icc 0 t, inner ℝ (g σ) (y' σ)) - isum g y T t N =
      ∑ i ∈ Finset.range (N + 1), ∫ σ in s i..s (i + 1), inner ℝ (g (s (i + 1)) - g σ) (y' σ) := by
    rw [hisum, Finset.sum_sub_distrib, hsum1, hI, ← Finset.sum_congr rfl fun i _ => hBI i,
      Finset.sum_sub_distrib]
    ring
  -- the bound
  have hbd : ∀ i, ‖∫ σ in s i..s (i + 1), inner ℝ (g (s (i + 1)) - g σ) (y' σ)‖ ≤
      (ε' * Y) * (s (i + 1) - s i) := by
    intro i
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s i) (b := s (i + 1))
      (f := fun σ => inner ℝ (g (s (i + 1)) - g σ) (y' σ)) (C := ε' * Y) fun σ hσ => by
        rw [Set.uIoc_of_le (hsmono (Nat.le_succ i))] at hσ
        have hσt : σ ∈ Set.Icc 0 t := ⟨(hst i).1.trans hσ.1.le, hσ.2.trans (hst (i + 1)).2⟩
        have hσT : σ ∈ Set.Icc 0 T := ⟨hσt.1, hσt.2.trans ht.2⟩
        have hsT : s (i + 1) ∈ Set.Icc 0 T :=
          ⟨(hst (i + 1)).1, (hst (i + 1)).2.trans ht.2⟩
        have hd : dist (s (i + 1)) σ < δ := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hσ.2])]
          linarith [hcell i, hσ.1]
        have hgd := hδg _ hsT _ hσT hd
        rw [dist_eq_norm] at hgd
        rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul hgd.le (hY σ hσt) (norm_nonneg _) hε'0.le
    rwa [abs_of_nonneg (sub_nonneg.2 (hsmono (Nat.le_succ i)))] at h
  have hsum2 : ∑ i ∈ Finset.range (N + 1), (s (i + 1) - s i) = t := by
    rw [Finset.sum_range_sub (fun i => s i), hsN, hs0]; ring
  rw [Real.dist_eq, abs_sub_comm, hdiff]
  calc |∑ i ∈ Finset.range (N + 1), ∫ σ in s i..s (i + 1), inner ℝ (g (s (i + 1)) - g σ) (y' σ)|
      = ‖∑ i ∈ Finset.range (N + 1), ∫ σ in s i..s (i + 1), inner ℝ (g (s (i + 1)) - g σ) (y' σ)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑ i ∈ Finset.range (N + 1), ‖∫ σ in s i..s (i + 1), inner ℝ (g (s (i + 1)) - g σ) (y' σ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (N + 1), (ε' * Y) * (s (i + 1) - s i) := Finset.sum_le_sum fun i _ => hbd i
    _ = (ε' * Y) * t := by rw [← Finset.mul_sum, hsum2]
    _ < ε := by
        have : ε' * Y * t ≤ ε / 2 := by
          have h1 : ε' * (Y * t) ≤ ε' * (Y * t + 1) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hε'0.le
          have h2 : ε' * (Y * t + 1) = ε / 2 := by
            rw [hε']; field_simp
          calc ε' * Y * t = ε' * (Y * t) := by ring
            _ ≤ ε / 2 := h1.trans h2.le
        linarith

end Abel

end HRS.Uniform.Q54c
