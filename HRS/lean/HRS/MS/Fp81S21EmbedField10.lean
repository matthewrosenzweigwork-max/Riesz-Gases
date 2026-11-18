import HRS.MS.Fp81S21EmbedField9

/-! Compact operators are uniformly approximated on the unit ball by the
finite coordinate projections. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq
open Filter Topology
open scoped RealInnerProductSpace

/-- Postcomposition by the coordinate projections converges in operator norm
for any compact operator on the coefficient Hilbert space. -/
theorem fp81s21_projectField_comp_tendsto
    (T : r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (hT : IsCompactOperator T) :
    Tendsto (fun m => (fp81s21_projectField m).comp T) atTop (𝓝 T) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  let η : ℝ := ε / 8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C, hC, hTC⟩ :=
    (isCompactOperator_iff_image_closedBall_subset_compact
      (T : r26t6_Coeff →ₗ[ℝ] r26t6_Coeff) (r := 1) one_pos).1 hT
  obtain ⟨centers, hcentersFinite, hcentersCover⟩ :=
    Metric.totallyBounded_iff.1 hC.totallyBounded η hη
  have hcentersEventually : ∀ᶠ m : ℕ in atTop,
      ∀ y ∈ centers, dist y (fp81s21_projectField m y) < η := by
    refine (hcentersFinite.eventually_all).2 fun y hy => ?_
    have h := fp81s21_projectField_tendsto y
    have hball := h.eventually (Metric.ball_mem_nhds y hη)
    simpa [dist_comm] using hball
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hcentersEventually
  have hnormBound : ∀ m : ℕ, M ≤ m →
      ‖(fp81s21_projectField m).comp T - T‖ ≤ 3 * η := by
    intro m hm
    let A := (fp81s21_projectField m).comp T - T
    have hunit : ∀ u : r26t6_Coeff, ‖u‖ ≤ 1 → ‖A u‖ ≤ 3 * η := by
      intro u hu
      have huBall : u ∈ Metric.closedBall (0 : r26t6_Coeff) 1 := by
        simpa [Metric.mem_closedBall] using hu
      have hTuC : T u ∈ C := hTC ⟨u, huBall, rfl⟩
      have hcovered := hcentersCover hTuC
      simp only [Set.mem_iUnion] at hcovered
      obtain ⟨y, hyC, hTyBall⟩ := hcovered
      have hTy : dist (T u) y < η := by
        simpa [dist_comm] using hTyBall
      have hym := hM m hm y hyC
      have hcontract :
          dist (fp81s21_projectField m y)
            (fp81s21_projectField m (T u)) ≤ dist y (T u) := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact fp81s21_projectField_norm_le m (y - T u)
      have hcontract' :
          dist (fp81s21_projectField m y)
            (fp81s21_projectField m (T u)) ≤ dist (T u) y := by
        simpa [dist_comm] using hcontract
      have htri :
          dist (T u) (fp81s21_projectField m (T u)) ≤
            dist (T u) y + dist y (fp81s21_projectField m y) +
              dist (fp81s21_projectField m y)
                (fp81s21_projectField m (T u)) := by
        calc
          dist (T u) (fp81s21_projectField m (T u)) ≤
              dist (T u) y + dist y (fp81s21_projectField m (T u)) :=
            dist_triangle _ _ _
          _ ≤ dist (T u) y +
              (dist y (fp81s21_projectField m y) +
                dist (fp81s21_projectField m y)
                  (fp81s21_projectField m (T u))) :=
            add_le_add_right (dist_triangle _ _ _) _
          _ = dist (T u) y + dist y (fp81s21_projectField m y) +
                dist (fp81s21_projectField m y)
                  (fp81s21_projectField m (T u)) := by ring
      have hres : dist (T u) (fp81s21_projectField m (T u)) < 3 * η := by
        calc
          dist (T u) (fp81s21_projectField m (T u)) ≤
              dist (T u) y + dist y (fp81s21_projectField m y) +
                dist (fp81s21_projectField m y)
                  (fp81s21_projectField m (T u)) := htri
          _ < η + η + η := by linarith
          _ = 3 * η := by ring
      have hAeq : ‖A u‖ = dist (T u) (fp81s21_projectField m (T u)) := by
        change ‖fp81s21_projectField m (T u) - T u‖ =
          dist (T u) (fp81s21_projectField m (T u))
        rw [dist_comm, dist_eq_norm]
      exact le_of_lt (hAeq ▸ hres)
    have hscale : ∀ x : r26t6_Coeff, ‖A x‖ ≤ (3 * η) * ‖x‖ := by
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · let u : r26t6_Coeff := ‖x‖⁻¹ • x
        have hu : ‖u‖ = 1 := by
          dsimp [u]
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
        have hxscale : x = ‖x‖ • u := by
          dsimp [u]
          rw [smul_smul]
          simp [norm_ne_zero_iff.mpr hx]
        have hAx : A x = ‖x‖ • A u := by
          calc
            A x = A (‖x‖ • u) := congrArg A hxscale
            _ = ‖x‖ • A u := map_smul A ‖x‖ u
        calc
          ‖A x‖ = ‖‖x‖ • A u‖ := by rw [hAx]
          _ = ‖x‖ * ‖A u‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          _ ≤ ‖x‖ * (3 * η) :=
            mul_le_mul_of_nonneg_left (hunit u (by norm_num [hu]))
              (norm_nonneg _)
          _ = (3 * η) * ‖x‖ := by ring
    exact ContinuousLinearMap.opNorm_le_bound A (by positivity) hscale
  have hsmall : 3 * η < ε := by dsimp [η]; nlinarith
  refine Filter.eventually_atTop.2 ⟨M, fun m hm => ?_⟩
  have hb := hnormBound m hm
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using lt_of_le_of_lt hb hsmall

#print axioms HRS.Fp81.S21.fp81s21_projectField_comp_tendsto

end HRS.Fp81.S21
