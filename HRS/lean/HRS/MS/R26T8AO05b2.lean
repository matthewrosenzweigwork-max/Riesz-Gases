import HRS.MS.R26T8AG01

/-!
# S8.2 observed-time layer, packet T8A.O05b (helper 2): uniform eventual value one of the graph cutoff

For a compact set `K` of collision-free configurations, the graph cutoffs `r26t8a_g01_theta d N n` are eventually
equal to one on a neighbourhood of every point of `K`, uniformly in `K`.  The proof uses the explicit form of `θ_n`:
it equals one where `‖X_i‖ ≤ n+1` and `2/(n+1) ≤ ‖X_i - X_j‖` for all `i ≠ j`, and a compact `K` has a uniform lower
bound `δ` on the pair distances and a uniform bound `R` on the norms.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_o05b2_coll_closed (d N : ℕ) : IsClosed (eucCollisionSet d N) := by
  have h : eucCollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j), {X : EucConfig d N | X i = X j} := by
    ext X
    simp [eucCollisionSet]
  rw [h]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)

/-- one-value criterion: if all particles are within `n+1` of the origin and pairwise at distance at least `2/(n+1)`,
then the graph cutoff equals one -/
theorem r26t8a_o05b2_one {d N : ℕ} (n : ℕ) (Y : EucConfig d N) (hY : ∀ i, ‖Y i‖ ≤ (n : ℝ) + 1)
    (hpair : ∀ i j : Fin N, i ≠ j → 2 / ((n : ℝ) + 1) ≤ ‖Y i - Y j‖) :
    r26t8a_g01_theta d N n Y = 1 := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsp : ∀ i : Fin N, 1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖Y i‖ ^ 2) = 1 := by
    intro i
    have hu1 : ((n : ℝ) + 1)⁻¹ * ‖Y i‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ hm, mul_one]
      exact hY i
    have hu0 : 0 ≤ ((n : ℝ) + 1)⁻¹ * ‖Y i‖ := by positivity
    have hsq : ((n : ℝ) + 1)⁻¹ ^ 2 * ‖Y i‖ ^ 2 ≤ 1 := by
      have e : ((n : ℝ) + 1)⁻¹ ^ 2 * ‖Y i‖ ^ 2 = (((n : ℝ) + 1)⁻¹ * ‖Y i‖) ^ 2 := by ring
      rw [e]
      exact pow_le_one₀ hu0 hu1
    rw [r26t8a_g01a_eq_zero hsq, sub_zero]
  have hpr : ∀ i j : Fin N, i < j → r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖Y i - Y j‖ ^ 2) = 1 := by
    intro i j hij
    apply r26t8a_g01a_eq_one
    have h2 := hpair i j (ne_of_lt hij)
    have h3 : 2 ≤ ‖Y i - Y j‖ * ((n : ℝ) + 1) := by
      rwa [div_le_iff₀ hm] at h2
    nlinarith [norm_nonneg (Y i - Y j), mul_nonneg (norm_nonneg (Y i - Y j)) hm.le]
  unfold r26t8a_g01_theta
  rw [Finset.prod_eq_one (fun i _ => hsp i), one_mul]
  exact Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j hj => hpr i j (Finset.mem_filter.1 hj).2

theorem r26t8a_o05b2_eventually (d N : ℕ) (K : Set (EucConfig d N)) (hK : IsCompact K)
    (hKD : K ⊆ (eucCollisionSet d N)ᶜ) :
    ∀ᶠ n : ℕ in atTop, ∀ X ∈ K, r26t8a_g01_theta d N n =ᶠ[𝓝 X] (fun _ => (1 : ℝ)) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact Eventually.of_forall fun n X hX => by simp at hX
  -- uniform bound on the norms over K
  obtain ⟨R0, hR0⟩ := hK.exists_bound_of_continuousOn (continuous_norm.continuousOn)
  -- uniform lower bound on the pair distances over K
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ X ∈ K, ∀ i j : Fin N, i ≠ j → δ ≤ ‖X i - X j‖ := by
    rcases Nat.lt_or_ge N 2 with hN | hN
    · exact ⟨1, one_pos, fun X _ i j hij => absurd (Fin.ext (by
        have := i.isLt; have := j.isLt; omega)) hij⟩
    · let P : Finset (Fin N × Fin N) := (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 ≠ p.2)
      have hP : P.Nonempty := ⟨((⟨0, by omega⟩ : Fin N), (⟨1, by omega⟩ : Fin N)), by simp [P, Fin.ext_iff]⟩
      let Φ : EucConfig d N → ℝ := fun X => P.inf' hP (fun p => ‖X p.1 - X p.2‖)
      have hΦc : Continuous Φ :=
        Continuous.finset_inf'_apply hP fun p _ =>
          (continuous_norm.comp ((continuous_apply p.1).sub (continuous_apply p.2)))
      obtain ⟨X0, hX0K, hmin⟩ := hK.exists_isMinOn hne hΦc.continuousOn
      refine ⟨Φ X0, ?_, fun X hX i j hij => ?_⟩
      · show (0 : ℝ) < P.inf' hP (fun p => ‖X0 p.1 - X0 p.2‖)
        rw [Finset.lt_inf'_iff]
        intro p hp
        have hpne : p.1 ≠ p.2 := (Finset.mem_filter.1 hp).2
        exact norm_pos_iff.2 (sub_ne_zero.2 fun h => hKD hX0K ⟨p.1, p.2, hpne, h⟩)
      · have h1 : Φ X0 ≤ Φ X := isMinOn_iff.1 hmin X hX
        have hmem : (i, j) ∈ P := Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hij⟩
        have h2 : Φ X ≤ ‖X i - X j‖ := Finset.inf'_le _ hmem
        exact le_trans h1 h2
  -- the radius of the neighbourhoods
  set r : ℝ := min 1 (δ / 4) with hr
  have hr0 : 0 < r := lt_min one_pos (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hr2 : 2 * r ≤ δ / 2 := by
    have := min_le_right 1 (δ / 4)
    linarith
  obtain ⟨N0, hN0⟩ := exists_nat_ge (max (R0 + 1) (4 / δ))
  filter_upwards [eventually_ge_atTop N0] with n hn
  intro X hX
  have hnR : R0 + 1 ≤ (n : ℝ) + 1 ∧ 4 / δ ≤ (n : ℝ) + 1 := by
    have hnn : max (R0 + 1) (4 / δ) ≤ (n : ℝ) := le_trans hN0 (Nat.cast_le.2 hn)
    have := max_le_iff.1 hnn
    constructor <;> linarith [this.1, this.2]
  have hXR : ∀ i, ‖X i‖ ≤ R0 := fun i => by
    have h := hR0 X hX
    rw [norm_norm] at h
    exact le_trans (norm_le_pi_norm X i) h
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  filter_upwards [Metric.ball_mem_nhds X hr0] with Y hY
  have hd : ∀ i, ‖Y i - X i‖ < r := fun i => by
    rw [← dist_eq_norm]
    exact (dist_pi_lt_iff hr0).1 (Metric.mem_ball.1 hY) i
  have h4 : 4 ≤ ((n : ℝ) + 1) * δ := (div_le_iff₀ hδ0).1 hnR.2
  have h5 : 2 / ((n : ℝ) + 1) ≤ δ / 2 := by
    rw [div_le_iff₀ hm]
    nlinarith
  apply r26t8a_o05b2_one n Y
  · intro i
    have := norm_sub_norm_le (Y i) (X i)
    linarith [hXR i, hd i, hr1]
  · intro i j hij
    have e1 := norm_sub_norm_le (X i - X j) (Y i - Y j)
    have e2 : (X i - X j) - (Y i - Y j) = (X i - Y i) - (X j - Y j) := by abel
    have e3 := norm_sub_le (X i - Y i) (X j - Y j)
    rw [e2] at e1
    have f1 : ‖X i - Y i‖ = ‖Y i - X i‖ := norm_sub_rev _ _
    have f2 : ‖X j - Y j‖ = ‖Y j - X j‖ := norm_sub_rev _ _
    have hlow : δ ≤ ‖X i - X j‖ := hδ X hX i j hij
    have hlow2 : δ / 2 ≤ ‖Y i - Y j‖ := by
      linarith [e1, e3, f1, f2, hd i, hd j, hr2, hlow]
    linarith [h5, hlow2]

end HRS.MS.R26T8A

end
