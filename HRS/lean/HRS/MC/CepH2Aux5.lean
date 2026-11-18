import HRS.MC.CepH2Aux4

/-!
# CEPH2, helper 5: periodisation along the diagonal

Summability and termwise differentiation of `x ↦ ∑' m : ℤ, φ (x + m d)` for Gaussian-bounded `φ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

theorem h2_norm_diag [NeZero N] : ‖cep_diag N‖ = Real.sqrt N := by
  rw [EuclideanSpace.norm_eq]
  simp [cep_diag_apply]

theorem h2_norm_smul_diag [NeZero N] (m : ℝ) : ‖m • cep_diag N‖ = |m| * Real.sqrt N := by
  rw [norm_smul, h2_norm_diag, Real.norm_eq_abs]

theorem h2_one_le_sqrt [NeZero N] : (1 : ℝ) ≤ Real.sqrt N := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N))

theorem h2_summable_exp_abs {κ : ℝ} (hκ : 0 < κ) : Summable (fun m : ℤ => Real.exp (-κ * |(m : ℝ)|)) := by
  have hg : Summable (fun n : ℕ => (Real.exp (-κ)) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith))
  have key : ∀ n : ℕ, Real.exp (-κ * |((n : ℤ) : ℝ)|) = (Real.exp (-κ)) ^ n := fun n => by
    rw [← Real.exp_nat_mul]; congr 1; simp [abs_of_nonneg]; ring
  apply Summable.of_nat_of_neg
  · exact hg.congr (fun n => (key n).symm)
  · refine hg.congr (fun n => ?_)
    rw [← key n]; simp

theorem h2_summable_lat [NeZero N] {c T : ℝ} (hc : 0 < c) :
    Summable (fun m : ℤ => Real.exp (-c * (max (|(m : ℝ)| * Real.sqrt N - T) 0) ^ 2)) := by
  have ha := h2_one_le_sqrt (N := N)
  refine (h2_summable_exp_abs (by positivity : 0 < c / 4)).of_norm_bounded_eventually ?_
  rw [Filter.eventually_cofinite]
  set K : ℤ := ⌈2 * |T|⌉ + 1 with hK
  refine (Set.finite_Icc (-K) K).subset ?_
  intro m hm
  simp only [Set.mem_ofPred_eq, not_le] at hm
  by_contra hmem
  simp only [Set.mem_Icc, not_and_or, not_le] at hmem
  apply (not_lt.2 _) hm
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hKr : 2 * |T| + 1 ≤ (K : ℝ) := by
    rw [hK]; push_cast; linarith [Int.le_ceil (2 * |T|)]
  have hm1 : (K : ℝ) < |(m : ℝ)| := by
    rcases hmem with h | h
    · have h' : (m : ℝ) < -(K : ℝ) := by exact_mod_cast h
      exact lt_abs.2 (Or.inr (by linarith))
    · have h' : (K : ℝ) < m := by exact_mod_cast h
      exact lt_abs.2 (Or.inl h')
  have hm2 : |T| ≤ |(m : ℝ)| / 2 := by linarith
  have hm3 : (1 : ℝ) ≤ |(m : ℝ)| := by linarith [abs_nonneg T]
  have h4 : |(m : ℝ)| / 2 ≤ max (|(m : ℝ)| * Real.sqrt N - T) 0 := by
    refine le_trans ?_ (le_max_left _ _)
    nlinarith [le_abs_self T, abs_nonneg T]
  rw [Real.exp_le_exp]
  have h5 : (|(m : ℝ)| / 2) ^ 2 ≤ (max (|(m : ℝ)| * Real.sqrt N - T) 0) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h4 2
  have h6 : |(m : ℝ)| / 4 ≤ (max (|(m : ℝ)| * Real.sqrt N - T) 0) ^ 2 := by nlinarith
  have h7 := mul_le_mul_of_nonneg_left h6 hc.le
  linarith

theorem h2_trans_bound [NeZero N] {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) {B : Ch N → ℝ}
    (hB : ∀ w, B w ≤ C * Real.exp (-c * ‖w‖ ^ 2)) (w0 x : Ch N) (hx : x ∈ Metric.ball w0 1) (m : ℤ) :
    B (x + (m : ℝ) • cep_diag N) ≤ C * Real.exp (-c * (max (|(m : ℝ)| * Real.sqrt N - (‖w0‖ + 1)) 0) ^ 2) := by
  refine (hB _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)
  have h1 : |(m : ℝ)| * Real.sqrt N - (‖w0‖ + 1) ≤ ‖x + (m : ℝ) • cep_diag N‖ := by
    have := norm_sub_norm_le ((m : ℝ) • cep_diag N) (-x)
    have h2 : ‖x‖ ≤ ‖w0‖ + 1 := by
      have := Metric.mem_ball.1 hx
      rw [dist_eq_norm] at this
      have := norm_le_norm_add_norm_sub' x w0
      linarith
    rw [h2_norm_smul_diag] at this
    rw [norm_neg] at this
    have e : (m : ℝ) • cep_diag N - -x = x + (m : ℝ) • cep_diag N := by abel
    rw [e] at this
    linarith
  have h2 : max (|(m : ℝ)| * Real.sqrt N - (‖w0‖ + 1)) 0 ≤ ‖x + (m : ℝ) • cep_diag N‖ :=
    max_le h1 (norm_nonneg _)
  have h3 := pow_le_pow_left₀ (le_max_right _ _) h2 2
  nlinarith

/-- Termwise differentiation of the periodisation of a Gaussian-bounded `C¹` function. -/
theorem h2_periodise_hasFDerivAt [NeZero N] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {φ : Ch N → F} {φ' : Ch N → Ch N →L[ℝ] F} (hφ : ∀ w, HasFDerivAt φ (φ' w) w)
    {C c : ℝ} (hc : 0 < c) (hφb : ∀ w, ‖φ w‖ ≤ C * Real.exp (-c * ‖w‖ ^ 2))
    (hφ'b : ∀ w, ‖φ' w‖ ≤ C * Real.exp (-c * ‖w‖ ^ 2)) (w : Ch N) :
    Summable (fun m : ℤ => φ (w + (m : ℝ) • cep_diag N)) ∧
    HasFDerivAt (fun x => ∑' m : ℤ, φ (x + (m : ℝ) • cep_diag N)) (∑' m : ℤ, φ' (w + (m : ℝ) • cep_diag N)) w := by
  have hC : 0 ≤ C := by
    have := hφb 0
    have h2 : 0 < Real.exp (-c * ‖(0 : Ch N)‖ ^ 2) := Real.exp_pos _
    by_contra h
    have h' : C < 0 := not_le.1 h
    nlinarith [norm_nonneg (φ 0)]
  have hu : Summable (fun m : ℤ => C * Real.exp (-c * (max (|(m : ℝ)| * Real.sqrt N - (‖w‖ + 1)) 0) ^ 2)) :=
    (h2_summable_lat hc).mul_left C
  have hw : w ∈ Metric.ball w 1 := Metric.mem_ball_self one_pos
  have hf : ∀ (m : ℤ) (x : Ch N), x ∈ Metric.ball w 1 →
      HasFDerivAt (fun y => φ (y + (m : ℝ) • cep_diag N)) (φ' (x + (m : ℝ) • cep_diag N)) x := by
    intro m x _
    have h1 : HasFDerivAt (fun y : Ch N => y + (m : ℝ) • cep_diag N) (ContinuousLinearMap.id ℝ (Ch N)) x :=
      (hasFDerivAt_id x).add_const _
    have h := (hφ (x + (m : ℝ) • cep_diag N)).comp x h1
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have hsum : Summable (fun m : ℤ => φ (w + (m : ℝ) • cep_diag N)) :=
    hu.of_norm_bounded (fun m => (hφb _).trans (by
      simpa using h2_trans_bound hC hc (B := fun z => C * Real.exp (-c * ‖z‖ ^ 2)) (fun w => le_rfl) w w hw m))
  refine ⟨hsum, ?_⟩
  exact hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball w 1).isPreconnected hf
    (fun m x hx => (hφ'b _).trans (by
      simpa using h2_trans_bound hC hc (B := fun z => C * Real.exp (-c * ‖z‖ ^ 2)) (fun w => le_rfl) w x hx m))
    hw hsum hw

/-- Continuity of the periodisation of a Gaussian-bounded continuous function. -/
theorem h2_periodise_continuous [NeZero N] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {φ : Ch N → F} (hφ : Continuous φ) {C c : ℝ} (hc : 0 < c) (hφb : ∀ w, ‖φ w‖ ≤ C * Real.exp (-c * ‖w‖ ^ 2)) :
    Continuous (fun x => ∑' m : ℤ, φ (x + (m : ℝ) • cep_diag N)) := by
  have hC : 0 ≤ C := by
    have := hφb 0
    have h2 : 0 < Real.exp (-c * ‖(0 : Ch N)‖ ^ 2) := Real.exp_pos _
    by_contra h
    have h' : C < 0 := not_le.1 h
    nlinarith [norm_nonneg (φ 0)]
  rw [continuous_iff_continuousAt]
  intro w
  have hu : Summable (fun m : ℤ => C * Real.exp (-c * (max (|(m : ℝ)| * Real.sqrt N - (‖w‖ + 1)) 0) ^ 2)) :=
    (h2_summable_lat hc).mul_left C
  have := continuousOn_tsum (f := fun (m : ℤ) (x : Ch N) => φ (x + (m : ℝ) • cep_diag N)) (s := Metric.ball w 1)
    (fun m => (hφ.comp (continuous_id.add continuous_const)).continuousOn) hu
    (fun m x hx => (hφb _).trans (by
      simpa using h2_trans_bound hC hc (B := fun z => C * Real.exp (-c * ‖z‖ ^ 2)) (fun w => le_rfl) w x hx m))
  exact this.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

end HRS.MC.CepH2
