import HRS.MS.R26T8AG01f
import HRS.MS.R26T8AG01c

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper g): the graph cutoff and its qualitative properties

`θ_n X = (∏_i (1 - ψ(m⁻² ‖X_i‖²))) · ∏_{i<j} ψ(m² ‖X_i - X_j‖²)` with `m = n + 1`.  It is smooth, takes values
in `[0, 1]`, has compact support in the sup-norm ball of radius `2m`, and its support stays a positive distance from
the collision set.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

/-- the graph cutoff at level `n` -/
def r26t8a_g01_theta (d N : ℕ) (n : ℕ) (X : EucConfig d N) : ℝ :=
  (∏ i : Fin N, (1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2))) *
    ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
      r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2)

theorem r26t8a_g01_theta_contDiff (d N n : ℕ) : ContDiff ℝ ∞ (r26t8a_g01_theta d N n) := by
  unfold r26t8a_g01_theta
  refine ContDiff.mul (contDiff_prod fun i _ => ?_) (contDiff_prod fun i _ => contDiff_prod fun j _ => ?_)
  · have hL : ContDiff ℝ ∞ (fun X : EucConfig d N => ‖X i‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).contDiff
    exact contDiff_const.sub (r26t8a_g01a_contDiff.comp (contDiff_const.mul hL))
  · have hL : ContDiff ℝ ∞ (fun X : EucConfig d N => ‖X i - X j‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j).contDiff)
    exact r26t8a_g01a_contDiff.comp (contDiff_const.mul hL)

theorem r26t8a_g01_theta_bounds (d N n : ℕ) (X : EucConfig d N) :
    0 ≤ r26t8a_g01_theta d N n X ∧ r26t8a_g01_theta d N n X ≤ 1 := by
  unfold r26t8a_g01_theta
  have hS : ∀ i : Fin N, 0 ≤ 1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2) ∧
      1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2) ≤ 1 := fun i =>
    ⟨by linarith [r26t8a_g01a_le_one (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2)],
      by linarith [r26t8a_g01a_nonneg (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2)]⟩
  have hP : ∀ i j : Fin N, 0 ≤ r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2) ∧
      r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2) ≤ 1 := fun i j =>
    ⟨r26t8a_g01a_nonneg _, r26t8a_g01a_le_one _⟩
  have hA0 : 0 ≤ ∏ i : Fin N, (1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2)) :=
    Finset.prod_nonneg fun i _ => (hS i).1
  have hA1 : ∏ i : Fin N, (1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (hS i).1) fun i _ => (hS i).2
  have hB0 : 0 ≤ ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
      r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2) :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => (hP i j).1
  have hB1 : ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
      r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => Finset.prod_nonneg fun j _ => (hP i j).1)
      fun i _ => Finset.prod_le_one₀ (fun j _ => (hP i j).1) fun j _ => (hP i j).2
  exact ⟨mul_nonneg hA0 hB0, mul_le_one₀ hA1 hB0 hB1⟩

theorem r26t8a_g01_theta_compact (d N n : ℕ) : HasCompactSupport (r26t8a_g01_theta d N n) := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine HasCompactSupport.intro (isCompact_closedBall (0 : EucConfig d N) (2 * ((n : ℝ) + 1))) ?_
  intro X hX
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hX
  obtain ⟨i, hi⟩ : ∃ i : Fin N, 2 * ((n : ℝ) + 1) < ‖X i‖ := by
    by_contra h
    push_neg at h
    have : ‖X‖ ≤ 2 * ((n : ℝ) + 1) :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => h i
    linarith
  have hsq : 4 * ((n : ℝ) + 1) ^ 2 ≤ ‖X i‖ ^ 2 := by nlinarith
  have hfac : (1 : ℝ) - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2) = 0 := by
    have h4 : 4 ≤ ((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2 := by
      rw [inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    rw [r26t8a_g01a_eq_one h4]
    norm_num
  unfold r26t8a_g01_theta
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hfac, zero_mul]

theorem r26t8a_g01_theta_tsupport (d N n : ℕ) :
    tsupport (r26t8a_g01_theta d N n) ⊆ (eucCollisionSet d N)ᶜ := by
  set S : Set (EucConfig d N) := ⋂ i : Fin N, ⋂ j : Fin N,
    {X | i < j → 1 ≤ ((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2} with hSdef
  have hSc : IsClosed S := by
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    by_cases hij : i < j
    · simp only [hij, true_implies, Set.setOf_forall]
      refine isClosed_le continuous_const ?_
      exact continuous_const.mul ((continuous_norm.comp
        ((continuous_apply i).sub (continuous_apply j))).pow 2)
    · simp [hij]
  have hsub : Function.support (r26t8a_g01_theta d N n) ⊆ S := by
    intro X hX
    have hB : (∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2)) ≠ 0 := by
      intro h0
      apply hX
      unfold r26t8a_g01_theta
      rw [h0, mul_zero]
    simp only [hSdef, Set.mem_iInter, Set.mem_setOf_eq]
    intro i j hij
    by_contra hlt
    push_neg at hlt
    have hmem : j ∈ Finset.univ.filter (fun j => i < j) := by simpa using hij
    have hz : r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2) = 0 :=
      r26t8a_g01a_eq_zero hlt.le
    apply hB
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero hmem hz)
  have hcl := closure_minimal hsub hSc
  intro X hX
  have hXS : X ∈ S := hcl hX
  rintro ⟨i, j, hij, heq⟩
  simp only [hSdef, Set.mem_iInter, Set.mem_setOf_eq] at hXS
  rcases lt_or_gt_of_ne hij with h | h
  · have := hXS i j h
    rw [heq, sub_self, norm_zero] at this
    norm_num at this
  · have := hXS j i h
    rw [heq, sub_self, norm_zero] at this
    norm_num at this

theorem r26t8a_g01_theta_eventually (d N : ℕ) (X : EucConfig d N) (hX : X ∉ eucCollisionSet d N) :
    ∀ᶠ n : ℕ in atTop, r26t8a_g01_theta d N n =ᶠ[𝓝 X] (fun _ => (1 : ℝ)) := by
  have hsp : ∀ i : Fin N, ∀ᶠ n : ℕ in atTop, ∀ᶠ X' in 𝓝 X,
      r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X' i‖ ^ 2) = 0 := by
    intro i
    have hc : Continuous fun X' : EucConfig d N => ‖X' i‖ :=
      continuous_norm.comp (continuous_apply i)
    have hlt : ∀ᶠ X' in 𝓝 X, ‖X' i‖ < ‖X i‖ + 1 :=
      (hc.tendsto X).eventually_lt_const (by linarith)
    filter_upwards [eventually_ge_atTop ⌈‖X i‖⌉₊] with n hn
    have hnR : ‖X i‖ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    filter_upwards [hlt] with X' hX'
    apply r26t8a_g01a_eq_zero
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : ‖X' i‖ / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hpos]
      linarith
    have key : ((n : ℝ) + 1)⁻¹ ^ 2 * ‖X' i‖ ^ 2 = (‖X' i‖ / ((n : ℝ) + 1)) ^ 2 := by ring
    rw [key]
    exact pow_le_one₀ (by positivity) hle
  have hpp : ∀ i j : Fin N, ∀ᶠ n : ℕ in atTop, ∀ᶠ X' in 𝓝 X,
      i < j → r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X' i - X' j‖ ^ 2) = 1 := by
    intro i j
    by_cases hij : i < j
    · have hr : 0 < ‖X i - X j‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hX ⟨i, j, hij.ne, h⟩)
      have hc : Continuous fun X' : EucConfig d N => ‖X' i - X' j‖ :=
        continuous_norm.comp ((continuous_apply i).sub (continuous_apply j))
      have hev : ∀ᶠ X' in 𝓝 X, ‖X i - X j‖ / 2 < ‖X' i - X' j‖ :=
        (hc.tendsto X).eventually_const_lt (by linarith)
      filter_upwards [eventually_ge_atTop ⌈4 / ‖X i - X j‖⌉₊] with n hn
      have hn' : 4 / ‖X i - X j‖ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
      rw [div_le_iff₀ hr] at hn'
      filter_upwards [hev] with X' hX' _
      apply r26t8a_g01a_eq_one
      have hpos : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have h2 : 2 ≤ ((n : ℝ) + 1) * ‖X' i - X' j‖ := by nlinarith
      nlinarith
    · exact Filter.Eventually.of_forall fun _ => Filter.Eventually.of_forall fun _ h' => absurd h' hij
  have A : ∀ᶠ n : ℕ in atTop, ∀ i : Fin N, ∀ᶠ X' in 𝓝 X,
      r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X' i‖ ^ 2) = 0 :=
    Filter.eventually_all.2 hsp
  have B : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin N, ∀ᶠ X' in 𝓝 X,
      i < j → r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X' i - X' j‖ ^ 2) = 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hpp i j
  filter_upwards [A, B] with n hA hB
  filter_upwards [Filter.eventually_all.2 hA,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hB i j] with X' h1 h2
  unfold r26t8a_g01_theta
  have hS : ∀ i : Fin N, 1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X' i‖ ^ 2) = 1 := fun i => by
    rw [h1 i, sub_zero]
  rw [Finset.prod_congr rfl (fun i _ => hS i), Finset.prod_const_one]
  rw [Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j hj =>
    h2 i j (Finset.mem_filter.1 hj).2))]
  simp

end HRS.MS.R26T8A

end
