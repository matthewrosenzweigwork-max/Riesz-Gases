import HRS.MS.S104eC3D

/-!
# S104E route C, packet C3, file E: closure properties of the classes `VanB` and `s104c3_TC`

Joint continuity of jets from time continuity, linear combinations, uniform limits.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Interval

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

variable {d : ℕ}

theorem s104c3_jets_cont_of_TC {t : ℝ} {N : ℕ} {u : ℝ → Euc d → ℝ} (hTC : s104c3_TC t N u)
    (hC : ∀ r ∈ Icc 0 t, ContDiff ℝ (N : WithTop ℕ∞) (u r)) :
    ∀ i ≤ N, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (u p.1) p.2) (Icc 0 t ×ˢ univ) := by
  intro i hi p hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ1, hδ1, h1⟩ := hTC i hi (ε / 2) (by linarith)
  have hcont : Continuous (iteratedFDeriv ℝ i (u p.1)) :=
    (hC p.1 hp.1).continuous_iteratedFDeriv (by exact_mod_cast hi)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuous_iff.1 hcont p.2 (ε / 2) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun q hq hdist => ?_⟩
  rw [Prod.dist_eq, max_lt_iff] at hdist
  have hd1 : |q.1 - p.1| < δ1 := by
    have := hdist.1; rw [Real.dist_eq] at this; exact lt_of_lt_of_le this (min_le_left _ _)
  have hd2 : dist q.2 p.2 < δ2 := lt_of_lt_of_le hdist.2 (min_le_right _ _)
  have e1 := h1 q.1 hq.1 p.1 hp.1 hd1 q.2
  have e2 := h2 q.2 hd2
  rw [dist_eq_norm] at e2 ⊢
  calc ‖iteratedFDeriv ℝ i (u q.1) q.2 - iteratedFDeriv ℝ i (u p.1) p.2‖
      = ‖(iteratedFDeriv ℝ i (u q.1) q.2 - iteratedFDeriv ℝ i (u p.1) q.2) +
        (iteratedFDeriv ℝ i (u p.1) q.2 - iteratedFDeriv ℝ i (u p.1) p.2)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith

theorem s104c3_TC_lin {t : ℝ} {N : ℕ} {u u' : ℝ → Euc d → ℝ} (c : ℝ)
    (hu : ∀ r ∈ Icc 0 t, ContDiff ℝ (N : WithTop ℕ∞) (u r))
    (hu' : ∀ r ∈ Icc 0 t, ContDiff ℝ (N : WithTop ℕ∞) (u' r))
    (h : s104c3_TC t N u) (h' : s104c3_TC t N u') :
    s104c3_TC t N (fun r x => c * u r x + u' r x) := by
  intro i hi ε hε
  have hc : 0 < |c| + 1 := by positivity
  obtain ⟨δ1, hδ1, h1⟩ := h i hi (ε / (2 * (|c| + 1))) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := h' i hi (ε / 2) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun r hr r' hr' hrr x => ?_⟩
  have e1 := h1 r hr r' hr' (lt_of_lt_of_le hrr (min_le_left _ _)) x
  have e2 := h2 r hr r' hr' (lt_of_lt_of_le hrr (min_le_right _ _)) x
  simp only [s104c3_jets_lin_apply c (hu r hr) (hu' r hr) hi x,
    s104c3_jets_lin_apply c (hu r' hr') (hu' r' hr') hi x]
  have : c • iteratedFDeriv ℝ i (u r) x + iteratedFDeriv ℝ i (u' r) x -
      (c • iteratedFDeriv ℝ i (u r') x + iteratedFDeriv ℝ i (u' r') x) =
      c • (iteratedFDeriv ℝ i (u r) x - iteratedFDeriv ℝ i (u r') x) +
      (iteratedFDeriv ℝ i (u' r) x - iteratedFDeriv ℝ i (u' r') x) := by
    rw [smul_sub]; abel
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h3 : |c| * ‖iteratedFDeriv ℝ i (u r) x - iteratedFDeriv ℝ i (u r') x‖ ≤
      |c| * (ε / (2 * (|c| + 1))) := mul_le_mul_of_nonneg_left e1 (abs_nonneg c)
  have h4 : |c| * (ε / (2 * (|c| + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg c]
  linarith

theorem s104c3_VanB_lin {N : ℕ} {f g : Euc d → ℝ} (c : ℝ) (hf : ContDiff ℝ (N : WithTop ℕ∞) f)
    (hg : ContDiff ℝ (N : WithTop ℕ∞) g) (h1 : VanB N f) (h2 : VanB N g) :
    VanB N (fun x => c * f x + g x) := by
  intro i hi
  have h := ((h1 i hi).const_mul |c|).add (h2 i hi)
  rw [mul_zero, add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun x => norm_nonneg _) (fun x => ?_)
  simp only [s104c3_jets_lin_apply c hf hg hi x]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]

theorem s104c3_VanB_of_unif {N : ℕ} {f : Euc d → ℝ} {fn : ℕ → Euc d → ℝ} (hv : ∀ n, VanB N (fn n))
    (hu : ∀ i ≤ N, ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x, ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i (fn n) x‖ ≤ ε) :
    VanB N f := by
  intro i hi
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := hu i hi (ε / 2) (by linarith)
  have := (Metric.tendsto_nhds.1 (hv n i hi)) (ε / 2) (by linarith)
  filter_upwards [this] with x hx
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hx
  have := hn x
  have h3 : ‖iteratedFDeriv ℝ i f x‖ ≤ ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i (fn n) x‖ +
      ‖iteratedFDeriv ℝ i (fn n) x‖ := by
    have := norm_add_le (iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i (fn n) x) (iteratedFDeriv ℝ i (fn n) x)
    simpa using this
  linarith

theorem s104c3_TC_of_unif {t : ℝ} {N : ℕ} {f : ℝ → Euc d → ℝ} {fn : ℕ → ℝ → Euc d → ℝ}
    (hTC : ∀ n, s104c3_TC t N (fn n))
    (hu : ∀ i ≤ N, ∀ ε : ℝ, 0 < ε → ∃ n, ∀ r ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ i (f r) x - iteratedFDeriv ℝ i (fn n r) x‖ ≤ ε) :
    s104c3_TC t N f := by
  intro i hi ε hε
  obtain ⟨n, hn⟩ := hu i hi (ε / 3) (by linarith)
  obtain ⟨δ, hδ, h⟩ := hTC n i hi (ε / 3) (by linarith)
  refine ⟨δ, hδ, fun r hr r' hr' hrr x => ?_⟩
  have e1 := hn r hr x
  have e2 := hn r' hr' x
  have e3 := h r hr r' hr' hrr x
  have : iteratedFDeriv ℝ i (f r) x - iteratedFDeriv ℝ i (f r') x =
      (iteratedFDeriv ℝ i (f r) x - iteratedFDeriv ℝ i (fn n r) x) +
      (iteratedFDeriv ℝ i (fn n r) x - iteratedFDeriv ℝ i (fn n r') x) -
      (iteratedFDeriv ℝ i (f r') x - iteratedFDeriv ℝ i (fn n r') x) := by abel
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  have := norm_add_le (iteratedFDeriv ℝ i (f r) x - iteratedFDeriv ℝ i (fn n r) x)
    (iteratedFDeriv ℝ i (fn n r) x - iteratedFDeriv ℝ i (fn n r') x)
  linarith

end HRS.MS.S104e.C
