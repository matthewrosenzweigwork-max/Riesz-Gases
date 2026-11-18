import HRS.MS.R2InterpAux12

/-!
# S10.2 (worker S102), part 13 (packet I3): the predicted path and the initial propagation are genuine paths

For a continuous path `w` and admissible functionals `z^u` matching `w(u)` (`V^{u,u}z^u = w(u)`), `r2Predicted C w z u` is not the junk zero path
of `windowPathOf`: its value at `t ∈ [0,T]` is `w(t)` for `t ≤ u` and `V^{t,u}z^u` for `t > u`.  Likewise `r2InitProp C m T z` has value
`V^{t,0}z` at `t`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

theorem s102_r2PathAt_of_mem (w : OscPath d m T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    r2PathAt w t = OscPath.at' w ⟨t, ht⟩ := by
  unfold r2PathAt
  rw [dif_pos ht]

theorem s102_windowPathOf_at {f : ℝ → OscDual d m} (hf : ContinuousOn f (Icc 0 T)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : r2PathAt (windowPathOf m T 0 f) t = f t := by
  have hc : Continuous fun s : Icc (0 : ℝ) T => f (0 + s) := by
    simp only [zero_add]
    exact hf.comp_continuous continuous_subtype_val (fun s => s.2)
  rw [s102_r2PathAt_of_mem _ ht]
  have : windowPathOf m T 0 f =
      (⟨fun t => f (0 + t), hc⟩ : C(Icc (0 : ℝ) T, OscDual d m)) := by
    unfold windowPathOf
    exact dif_pos hc
  rw [this]
  show f (0 + t) = f t
  rw [zero_add]

/-- `t ↦ V^{t,u}z` is continuous on `[u,T]`. -/
theorem s102_Vprop_continuousOn (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) {z : (Euc d → ℝ) → ℝ}
    (hz : S102Z r Pw z) (hlin : S102Lin C m T) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) :
    ContinuousOn (fun t => r2Vprop C m t u z) (Icc u T) := by
  obtain ⟨K, hK0, hK⟩ := s102_Vprop_lip hP hD hz hlin hu
  have : LipschitzOnWith (Real.toNNReal K) (fun t => r2Vprop C m t u z) (Icc u T) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ hK0]
    rcases le_total y x with h | h
    · have := hK hy hx h
      rw [abs_of_nonneg (sub_nonneg.2 h)]; exact this
    · have := hK hx hy h
      rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.2 h), neg_sub]; exact this
  exact this.continuousOn

/-- The predicted path at time `u`. -/
theorem s102_predicted_at (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (w : OscPath d m T) (zf : ℝ → (Euc d → ℝ) → ℝ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T)
    (hz : S102Z r Pw (zf u)) (hmatch : r2Vprop C m u u (zf u) = r2PathAt w u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    r2PathAt (r2Predicted C w zf u) t =
      if t ≤ u then r2PathAt w t else r2Vprop C m t u (zf u) := by
  unfold r2Predicted
  have hV := s102_Vprop_continuousOn hP hD hz hlin hu
  have hcont : ContinuousOn (fun t => if t ≤ u then r2PathAt w t else r2Vprop C m t u (zf u)) (Icc 0 T) := by
    have hg1 : Continuous fun s : Icc (0 : ℝ) T => OscPath.at' w s := by
      show Continuous fun s : Icc (0 : ℝ) T => (show C(Icc (0 : ℝ) T, OscDual d m) from w) s
      exact (show C(Icc (0 : ℝ) T, OscDual d m) from w).continuous
    have hg2 : Continuous fun s : Icc (0 : ℝ) T => r2Vprop C m (max (s : ℝ) u) u (zf u) :=
      hV.comp_continuous (continuous_subtype_val.max continuous_const)
        (fun s => ⟨le_max_right _ _, max_le s.2.2 hu.2⟩)
    have hsub : Continuous fun s : Icc (0 : ℝ) T =>
        if (s : ℝ) ≤ u then OscPath.at' w s else r2Vprop C m (max (s : ℝ) u) u (zf u) :=
      Continuous.if_le hg1 hg2 continuous_subtype_val continuous_const (fun s hs => by
        have hsu : (s : ℝ) = u := hs
        rw [max_eq_right hsu.le]
        have e1 : OscPath.at' w s = OscPath.at' w ⟨u, hu⟩ := by
          congr 1; exact Subtype.ext hsu
        rw [e1, ← s102_r2PathAt_of_mem w hu, ← hmatch])
    rw [continuousOn_iff_continuous_domRestrict]
    refine hsub.congr fun s => ?_
    by_cases h : (s : ℝ) ≤ u
    · simp [Set.domRestrict, h, s102_r2PathAt_of_mem w s.2]
    · simp [Set.domRestrict, h, max_eq_left (not_le.1 h).le]
  rw [s102_windowPathOf_at hcont ht]

/-- The initial propagation at time `t`. -/
theorem s102_initProp_at (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    {z : (Euc d → ℝ) → ℝ} (hz : S102Z r Pw z) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    r2PathAt (r2InitProp C m T z) t = r2Vprop C m t 0 z := by
  unfold r2InitProp
  have hu0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hV := s102_Vprop_continuousOn hP hD hz hlin hu0
  exact s102_windowPathOf_at (hV.mono (fun s hs => hs)) ht

end HRS.MS.R2Interp

end
