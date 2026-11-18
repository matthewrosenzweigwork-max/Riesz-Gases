import HRS.MS.WsPrepAux13
import HRS.MS.WsStatAux14

/-!
# S2.1(iii) packet G7: a.e. measurability of the exactly centered window `ζ_N^{a₀+·}`

`s21e_zeta_cont_time`: along a.s. continuous particle paths the exactly centered field `t ↦ √N(μ_N^t - m_N^t)` (`zetaB`, `m_N^t = E μ_N^t` the law-mean,
a MOVING centering) is continuous in `B_m` (`m > d`): each coordinate is continuous (dominated convergence for `t ↦ E oscTestFun_α(X_i(t))`), and the
coordinates are bounded by a summable square sequence (`s56_osc_cont_of_coord`).  Unlike S2.1(i) (`s21_zeta_aemeas`) no stationarity of the law is used.
`s21e_zeta_window_aemeas`: `AEMeasurable (zetaPathW m T a₀ P X) P` for every window start `a₀ ≥ 0` (the first measurability conjunct of the frozen
`whole_space_edgeworth`; the junk value `0` of `windowPathOf` is never used).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole

variable {d : ℕ}

theorem s21e_zeta_cont_time (hd : 1 ≤ d) {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : (d : ℝ) < m)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) :
    ∀ᵐ ζ ∂P, Continuous fun t : ℝ =>
      zetaB m (P.map (X (Real.toNNReal t))) (X (Real.toNNReal t) ζ) := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.GenPath.s56_oscTestFun_bound (d := d) m
  -- continuity in time of the mean coordinates
  have hF : ∀ (α : MultiIndex d) (i : Fin N), Continuous fun t : ℝ =>
      ∫ ζ', oscTestFun m α (X (Real.toNNReal t) ζ' i) ∂P := by
    intro α i
    refine continuous_of_dominated (bound := fun _ => C * oscEigenvalue d α ^ (-(m / 2)))
      (fun t => ?_) (fun t => Filter.Eventually.of_forall fun ζ' => ?_) (integrable_const _) ?_
    · exact ((HRS.MS.GenPath.s56_oscTestFun_cont m α).measurable.comp
        ((measurable_pi_apply i).comp (hXm _))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hC α _
    · filter_upwards [hXc] with ζ' hζ'
      exact (HRS.MS.GenPath.s56_oscTestFun_cont m α).comp ((hζ' i).comp continuous_real_toNNReal)
  filter_upwards [hXc] with ζ hζ
  have hpath : ∀ i, Continuous fun t : ℝ => X (Real.toNNReal t) ζ i := fun i =>
    (hζ i).comp continuous_real_toNNReal
  have hprob : ∀ t : ℝ, IsProbabilityMeasure (P.map (X (Real.toNNReal t))) := fun t => inferInstance
  have hmean : ∀ t : ℝ, ∀ α : MultiIndex d,
      ∫ y, oscTestFun m α y ∂(meanEmpirical (P.map (X (Real.toNNReal t)))) =
        (N : ℝ)⁻¹ * ∑ i : Fin N, ∫ ζ', oscTestFun m α (X (Real.toNNReal t) ζ' i) ∂P := by
    intro t α
    rw [HRS.MS.S21.s21_integral_meanEmpirical (P.map (X (Real.toNNReal t)))
      (HRS.MS.GenPath.s56_oscTestFun_cont m α).measurable (B := C * oscEigenvalue d α ^ (-(m / 2))) (hC α)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_map (hXm _).aemeasurable
      ((HRS.MS.GenPath.s56_oscTestFun_cont m α).comp (continuous_apply i)).aestronglyMeasurable
  have hcoord : ∀ (t : ℝ) (α : MultiIndex d),
      OscDual.coord (zetaB m (P.map (X (Real.toNNReal t))) (X (Real.toNNReal t) ζ)) α =
        Real.sqrt N * ((N : ℝ)⁻¹ * ∑ i : Fin N, oscTestFun m α (X (Real.toNNReal t) ζ i) -
          (N : ℝ)⁻¹ * ∑ i : Fin N, ∫ ζ', oscTestFun m α (X (Real.toNNReal t) ζ' i) ∂P) := by
    intro t α
    have := hprob t
    have := meanEmpirical_isProbabilityMeasure (P.map (X (Real.toNNReal t))) (by omega : 1 ≤ N)
    have := empirical_isProbabilityMeasure hN (X (Real.toNNReal t) ζ)
    unfold zetaB
    rw [OscDual.coord_smul, HRS.MS.GenPath.s56_coord_ofMeasureDiff hm, hmean t α]
    congr 2
    exact pair_empirical hN _ (oscTestFun m α)
  refine HRS.MS.GenPath.s56_osc_cont_of_coord _
    (fun α => 2 * |Real.sqrt N| * (C * oscEigenvalue d α ^ (-(m / 2)))) ?_ (fun α => ?_) (fun t α => ?_)
  · simpa [mul_assoc] using
      (HRS.MS.GenPath.s56_summable_bound hd hm (2 * |Real.sqrt N| * C)).congr fun α => by ring
  · simp_rw [hcoord]
    refine continuous_const.mul (Continuous.sub (continuous_const.mul ?_) (continuous_const.mul ?_))
    · exact continuous_finsetSum _ fun i _ =>
        (HRS.MS.GenPath.s56_oscTestFun_cont m α).comp (hpath i)
    · exact continuous_finsetSum _ fun i _ => hF α i
  · have := hprob t
    have := meanEmpirical_isProbabilityMeasure (P.map (X (Real.toNNReal t))) (by omega : 1 ≤ N)
    have := empirical_isProbabilityMeasure hN (X (Real.toNNReal t) ζ)
    exact HRS.MS.GenPath.s56_xi_coord_bound (Real.sqrt N) C hC _ _ hm α

/-- **G7.**  The exactly centered window of a collision-free strong solution is a.e. measurable, for every window start `a₀ ≥ 0`. -/
theorem s21e_zeta_window_aemeas (hd : 1 ≤ d) {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : (d : ℝ) < m)
    {a₀ T : ℝ} (ha₀ : 0 ≤ a₀) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) :
    AEMeasurable (zetaPathW m T a₀ P X) P := by
  set Y : ℝ → Ω → OscDual d m := fun t ζ =>
    zetaB m (P.map (X (Real.toNNReal t))) (X (Real.toNNReal t) ζ) with hY
  have hmeas : ∀ u ∈ Icc (0 : ℝ) T, Measurable (fun ζ => Y (a₀ + u) ζ) := by
    intro u _
    have : IsProbabilityMeasure (P.map (X (Real.toNNReal (a₀ + u)))) :=
      inferInstance
    have := meanEmpirical_isProbabilityMeasure (P.map (X (Real.toNNReal (a₀ + u)))) (by omega : 1 ≤ N)
    exact (HRS.MS.GenPath.s56_xi_cont_config hd hm (Real.sqrt N) hN
      (meanEmpirical (P.map (X (Real.toNNReal (a₀ + u)))))).measurable.comp (hXm _)
  have hc : ∀ᵐ ζ ∂P, ContinuousOn (fun u => Y (a₀ + u) ζ) (Icc 0 T) := by
    filter_upwards [s21e_zeta_cont_time hd hN hm P X hXm hXc] with ζ hζ
    exact (hζ.comp (continuous_const.add continuous_id)).continuousOn
  have h := HRS.GF.gfb4_aemeasurable_windowPath P hT (fun u ζ => Y (a₀ + u) ζ) hmeas hc
  rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
  have e : zetaPathW m T a₀ P X = fun ζ => windowPathOf m T 0 (fun u => Y (a₀ + u) ζ) := by
    funext ζ
    unfold zetaPathW
    exact s21p_wpo_shift m T a₀ (fun t => Y t ζ)
  rw [e]
  exact h

end HRS.Whole
