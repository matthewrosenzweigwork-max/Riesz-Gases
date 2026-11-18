import HRS.MS.SA12X4V2

/-!
# S.A.12 (SA12X4) V3: the continuous weighted jet energy is bounded by `varpiNormE` squared

`sa12x4_J_le_varpi`: `∫ ϖ Z_m(u) ≤ K ‖u‖²_{H^m(ϖ)}` for smooth `u`.  Cover `ℝ^d` by the unit balls `B(cellPt c, 1)`, on which
`χ(· - cellPt c) = 1` so that the jets of `χ(· - cellPt c) u` and of `u` agree, and use `ϖ(x) ≤ C ϖ(cellPt c)` there.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Near HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x4_J_le_varpi (hd : 1 ≤ d) (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : Euc d → ℝ}, ContDiff ℝ ∞ u → sa12x4_J m u ≤ ENNReal.ofReal K * varpiNormE m χ u ^ 2 := by
  classical
  set p : ℝ := (d : ℝ) + 3 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set Cw : ℝ := (Real.sqrt 2 * Real.sqrt (1 + (1 : ℝ) ^ 2)) ^ p with hCw
  have hCw0 : 0 ≤ Cw := Real.rpow_nonneg (by positivity) _
  refine ⟨2 ^ m * (Cw * ((m : ℝ) + 1)), by positivity, fun {u} hu => ?_⟩
  set f : (Fin d → ℤ) → Euc d → ℝ := fun c y => χ (y - cellPt d c) * u y with hf
  have hfC : ∀ c, ContDiff ℝ ∞ (f c) := fun c => (hχ.1.comp (contDiff_id.sub contDiff_const)).mul hu
  have hfc : ∀ c, HasCompactSupport (f c) := fun c => by
    have : HasCompactSupport (fun y => χ (y - cellPt d c)) := hχ.2.1.comp_homeomorph (Homeomorph.subRight _)
    exact this.mul_right
  have hYm : Measurable (sa12z3_Y m u) := by
    unfold sa12z3_Y
    refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun γ _ => ?_
    exact ((sa12z3_pd_contDiff_inf hu γ).continuous.measurable).pow_const 2
  have hsqi : ∀ c, ∀ {n : ℕ} (idx : Fin n → Fin d), Integrable (fun x => (partialDeriv idx (f c) x) ^ 2) := fun c n idx =>
    Continuous.integrable_of_hasCompactSupport (f := fun x => (partialDeriv idx (f c) x) ^ 2)
      ((sa12z3_pd_contDiff_inf (hfC c) idx).continuous.pow 2)
      ((sa12z3_pd_compact (hfc c) idx).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  -- the local bound on a unit ball
  have hball : ∀ c, ∫⁻ x in ball (cellPt d c) 1, ENNReal.ofReal (sa12z3_Y m u x) ≤
      ENNReal.ofReal ((m : ℝ) + 1) * sobolevNormE (m : ℝ) (f c) ^ 2 := by
    intro c
    have hEq : EqOn (f c) u (ball (cellPt d c) 1) := by
      intro y hy
      have h1 : χ (y - cellPt d c) = 1 := hχ.2.2.2.2 _ (by
        rw [mem_closedBall_zero_iff]; exact (mem_ball_iff_norm.1 hy).le)
      simp [hf, h1]
    have hY : ∀ x ∈ ball (cellPt d c) 1, sa12z3_Y m u x = sa12z3_Y m (f c) x := by
      intro x hx
      unfold sa12z3_Y
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun γ _ => ?_
      rw [sa12x3_pd_congr_open (isOpen_ball (x := cellPt d c) (ε := 1)) hEq γ hx]
    have hYf : Integrable (sa12z3_Y m (f c)) := by
      unfold sa12z3_Y
      exact integrable_finset_sum _ fun r _ => integrable_finset_sum _ fun γ _ => hsqi c γ
    have hint : ∫ x, sa12z3_Y m (f c) x = sa12x3_Jraw m (f c) := by
      unfold sa12z3_Y sa12x3_Jraw
      rw [integral_finset_sum _ fun r _ => integrable_finset_sum _ fun γ _ => hsqi c γ]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [integral_finset_sum _ fun γ _ => hsqi c γ]
    have hnn : ∀ x, 0 ≤ sa12z3_Y m (f c) x := fun x =>
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun γ _ => sq_nonneg _
    calc ∫⁻ x in ball (cellPt d c) 1, ENNReal.ofReal (sa12z3_Y m u x)
        = ∫⁻ x in ball (cellPt d c) 1, ENNReal.ofReal (sa12z3_Y m (f c) x) :=
          setLIntegral_congr_fun measurableSet_ball fun x hx => by rw [hY x hx]
      _ ≤ ∫⁻ x, ENNReal.ofReal (sa12z3_Y m (f c) x) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (sa12x3_Jraw m (f c)) := by
          rw [← hint, ofReal_integral_eq_lintegral_ofReal hYf (Filter.Eventually.of_forall hnn)]
      _ ≤ _ := (sa12x3_sob_jet m (sa12z3_cd_of_inf (hfC c) m) (hfc c)).2
  -- the covering
  have hcov : (⋃ c : Fin d → ℤ, ball (cellPt d c) 1) = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨c, hc⟩ := HRS.MS.UniqC3.exists_cellPt_near hd x
    exact mem_iUnion.2 ⟨c, by rw [mem_ball_iff_norm]; linarith⟩
  have hJY : sa12x4_J m u ≤ ENNReal.ofReal (2 ^ m) * ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-p)) * ENNReal.ofReal (sa12z3_Y m u x) := by
    rw [sa12x4_J, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    have h := sa12x4_Z_le_Y m u x
    calc ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3))) * ENNReal.ofReal (sa12x4_Z m u x)
        ≤ ENNReal.ofReal (jbracket x ^ (-p)) * ENNReal.ofReal (2 ^ m * sa12z3_Y m u x) := by
          rw [← hp]; gcongr
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]; ring
  refine hJY.trans ?_
  have hsplit : ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-p)) * ENNReal.ofReal (sa12z3_Y m u x) ≤
      ∑' c, ∫⁻ x in ball (cellPt d c) 1, ENNReal.ofReal (jbracket x ^ (-p)) * ENNReal.ofReal (sa12z3_Y m u x) := by
    have := lintegral_iUnion_le (μ := (volume : Measure (Euc d))) (fun c : Fin d → ℤ => ball (cellPt d c) 1)
      (fun x => ENNReal.ofReal (jbracket x ^ (-p)) * ENNReal.ofReal (sa12z3_Y m u x))
    rwa [hcov, Measure.restrict_univ] at this
  have hloc : ∀ c, ∫⁻ x in ball (cellPt d c) 1, ENNReal.ofReal (jbracket x ^ (-p)) * ENNReal.ofReal (sa12z3_Y m u x) ≤
      ENNReal.ofReal Cw * (ENNReal.ofReal (jbracket (cellPt d c) ^ (-p)) *
        (ENNReal.ofReal ((m : ℝ) + 1) * sobolevNormE (m : ℝ) (f c) ^ 2)) := by
    intro c
    calc ∫⁻ x in ball (cellPt d c) 1, ENNReal.ofReal (jbracket x ^ (-p)) * ENNReal.ofReal (sa12z3_Y m u x)
        ≤ ∫⁻ x in ball (cellPt d c) 1, ENNReal.ofReal Cw * ENNReal.ofReal (jbracket (cellPt d c) ^ (-p)) *
            ENNReal.ofReal (sa12z3_Y m u x) := by
          refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
          have hnear : ‖cellPt d c - x‖ ≤ 1 := by
            rw [mem_ball_iff_norm, norm_sub_rev] at hx; exact hx.le
          have hc := sa12x4_varpi_comp p hp0 1 (cellPt d c) x hnear
          gcongr
          rw [← ENNReal.ofReal_mul hCw0]
          exact ENNReal.ofReal_le_ofReal hc
      _ = ENNReal.ofReal Cw * ENNReal.ofReal (jbracket (cellPt d c) ^ (-p)) *
            ∫⁻ x in ball (cellPt d c) 1, ENNReal.ofReal (sa12z3_Y m u x) :=
          lintegral_const_mul _ hYm.ennreal_ofReal
      _ ≤ ENNReal.ofReal Cw * ENNReal.ofReal (jbracket (cellPt d c) ^ (-p)) *
            (ENNReal.ofReal ((m : ℝ) + 1) * sobolevNormE (m : ℝ) (f c) ^ 2) := by gcongr; exact hball c
      _ = _ := by ring
  rw [sa12x4_varpi_sq]
  calc ENNReal.ofReal (2 ^ m) * ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-p)) * ENNReal.ofReal (sa12z3_Y m u x)
      ≤ ENNReal.ofReal (2 ^ m) * ∑' c, ENNReal.ofReal Cw * (ENNReal.ofReal (jbracket (cellPt d c) ^ (-p)) *
        (ENNReal.ofReal ((m : ℝ) + 1) * sobolevNormE (m : ℝ) (f c) ^ 2)) := by
        gcongr
        exact hsplit.trans (ENNReal.tsum_le_tsum hloc)
    _ = ENNReal.ofReal (2 ^ m * (Cw * ((m : ℝ) + 1))) *
          ∑' c, ENNReal.ofReal (jbracket (cellPt d c) ^ (-((d : ℝ) + 3))) * sobolevNormE (m : ℝ) (f c) ^ 2 := by
        rw [ENNReal.tsum_mul_left, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCw0, ← hp]
        have : ∀ c, ENNReal.ofReal (jbracket (cellPt d c) ^ (-p)) *
            (ENNReal.ofReal ((m : ℝ) + 1) * sobolevNormE (m : ℝ) (f c) ^ 2) =
            ENNReal.ofReal ((m : ℝ) + 1) * (ENNReal.ofReal (jbracket (cellPt d c) ^ (-p)) *
              sobolevNormE (m : ℝ) (f c) ^ 2) := fun c => by ring
        simp_rw [this]
        rw [ENNReal.tsum_mul_left]
        ring

end HRS.MH.AdjointRd.Phase2SA12X4
