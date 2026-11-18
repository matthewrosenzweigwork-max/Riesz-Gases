import HRS.MS.MainRdPathAux10

/-!
# S.A.9, packet P3e: the weighted cell integrals of the tail function tend to `0`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit

variable {d : ℕ}

theorem sa9_wsum_lt_top :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) < ⊤ := by
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun z => ?_) (mri_lattice_sum (d := d))
  refine ENNReal.ofReal_le_ofReal ?_
  have hnn : 0 ≤ jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) := Real.rpow_nonneg (mri_jb_pos _).le _
  have h1 : 1 ≤ jbracket (cellPt d z) ^ 2 := by rw [mri_jb_sq]; nlinarith [sq_nonneg ‖cellPt d z‖]
  exact le_mul_of_one_le_right hnn h1

section Cell

variable {q m : ℕ} {T K : ℝ} {Cf : WholeCoeff d}

theorem sa9_cellsum_tendsto (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) Cf T K) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (Kc : ℝ) :
    Tendsto (fun Lc => ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
      (ENNReal.ofReal Kc * ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h Cf t m Lc x)) atTop (𝓝 0) := by
  set GB : ℝ≥0∞ := ENNReal.ofReal (sa9_Cdim d m * K ^ 2) with hGB
  have hinner : ∀ z : Fin d → ℤ, Tendsto (fun Lc => ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h Cf t m Lc x)
      atTop (𝓝 0) := by
    intro z
    have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Metric.ball (cellPt d z) 2))
      (F := fun Lc x => sa9_Gt h Cf t m Lc x) (f := fun _ => (0 : ℝ≥0∞)) (fun _ => GB)
      (fun Lc => sa9_Gt_meas hadj ht0 htT h Lc)
      (fun Lc => Eventually.of_forall fun x => sa9_Gt_le hadj h hP ht0 htT Lc x)
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (by rw [Measure.restrict_apply MeasurableSet.univ]; simp; exact measure_ball_lt_top.ne))
      (Eventually.of_forall fun x => sa9_Gt_tendsto hadj h hP ht0 htT x)
    simpa using this
  set V0 : ℝ≥0∞ := volume (Metric.ball (0 : Euc d) 2) with hV0
  have hV0top : V0 ≠ ⊤ := measure_ball_lt_top.ne
  set bnd : (Fin d → ℤ) → ℝ≥0∞ := fun z => ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
    (ENNReal.ofReal Kc * (GB * V0)) with hbnd
  have hfin : ∑' z, bnd z ≠ ⊤ := by
    simp only [hbnd]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top sa9_wsum_lt_top.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV0top))
  have hmain := tendsto_lintegral_of_dominated_convergence (μ := (Measure.count : Measure (Fin d → ℤ)))
    (F := fun Lc z => ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
      (ENNReal.ofReal Kc * ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h Cf t m Lc x))
    (f := fun _ => (0 : ℝ≥0∞)) bnd (fun Lc => measurable_of_countable _)
    (fun Lc => Eventually.of_forall fun z => by
      simp only [hbnd]
      refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
      calc ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h Cf t m Lc x
          ≤ ∫⁻ x in Metric.ball (cellPt d z) 2, GB := lintegral_mono fun x => sa9_Gt_le hadj h hP ht0 htT Lc x
        _ = GB * V0 := by
            rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
              Measure.addHaar_ball_center]
            )
    (by rw [lintegral_count]; exact hfin)
    (Eventually.of_forall fun z => by
      have h1 := ENNReal.Tendsto.const_mul (hinner z) (Or.inr (ENNReal.ofReal_ne_top (r := Kc)))
      have h2 := ENNReal.Tendsto.const_mul h1
        (Or.inr (ENNReal.ofReal_ne_top (r := jbracket (cellPt d z) ^ (-((d : ℝ) + 3)))))
      simpa using h2)
  simpa [lintegral_count] using hmain

end Cell

end HRS.MS.MainRdPath
