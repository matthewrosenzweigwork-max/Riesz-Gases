import HRS.MS.Fp81S21BlockValue10

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set Classical
namespace HRS.Fp81.S21

/-- Combine the four covariance entries over their clipped clock intervals. -/
theorem fp81s21_blockValue_four_sum
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (D : ℝ → K →L[ℝ] K →L[ℝ] ℝ) (Pa Qa Pb Qb : K)
    (ta tb : Icc (0 : ℝ) 1)
    (hPP : IntegrableOn (fun s => D s Pa Pb) (Icc (0 : ℝ) 1))
    (hPQ : IntegrableOn (fun s => D s Pa Qb) (Icc (0 : ℝ) 1))
    (hQP : IntegrableOn (fun s => D s Qa Pb) (Icc (0 : ℝ) 1))
    (hQQ : IntegrableOn (fun s => D s Qa Qb) (Icc (0 : ℝ) 1)) :
    (∫ s in Icc (0 : ℝ) 1, D s Pa Pb) +
    (∫ s in Icc (0 : ℝ) (tb : ℝ), D s Pa Qb) +
    (∫ s in Icc (0 : ℝ) (ta : ℝ), D s Qa Pb) +
    (∫ s in Icc (0 : ℝ) (min (ta : ℝ) (tb : ℝ)), D s Qa Qb) =
    ∫ s in Icc (0 : ℝ) 1,
      D s (Pa + if s ≤ (ta : ℝ) then Qa else 0)
        (Pb + if s ≤ (tb : ℝ) then Qb else 0) := by
  let A := Icc (0 : ℝ) (ta : ℝ)
  let B := Icc (0 : ℝ) (tb : ℝ)
  let AB := Icc (0 : ℝ) (min (ta : ℝ) (tb : ℝ))
  have hA : MeasurableSet A := measurableSet_Icc
  have hB : MeasurableSet B := measurableSet_Icc
  have hAB : MeasurableSet AB := measurableSet_Icc
  have hAsub : A ⊆ Icc (0 : ℝ) 1 := fun _ h => ⟨h.1, h.2.trans ta.property.2⟩
  have hBsub : B ⊆ Icc (0 : ℝ) 1 := fun _ h => ⟨h.1, h.2.trans tb.property.2⟩
  have hABsub : AB ⊆ Icc (0 : ℝ) 1 := fun _ h => ⟨h.1, h.2.trans ((min_le_left _ _).trans ta.property.2)⟩
  have hPQ' := hPQ.indicator hB
  have hQP' := hQP.indicator hA
  have hQQ' := hQQ.indicator hAB
  calc
    _ = ∫ s in Icc (0 : ℝ) 1,
        ((D s Pa Pb + B.indicator (fun s => D s Pa Qb) s) +
          A.indicator (fun s => D s Qa Pb) s) + AB.indicator (fun s => D s Qa Qb) s := by
      change _ = ∫ s in Icc (0 : ℝ) 1,
        (((fun s => D s Pa Pb) + B.indicator (fun s => D s Pa Qb)) +
          A.indicator (fun s => D s Qa Pb) + AB.indicator (fun s => D s Qa Qb)) s
      rw [integral_add' (hPP.add hPQ' |>.add hQP') hQQ',
        integral_add' (hPP.add hPQ') hQP', integral_add' hPP hPQ',
        setIntegral_indicator hB, setIntegral_indicator hA, setIntegral_indicator hAB,
        inter_eq_right.mpr hBsub, inter_eq_right.mpr hAsub, inter_eq_right.mpr hABsub]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      simp only [A, B, AB, Set.indicator, mem_Icc, hs.1, true_and, le_min_iff]
      by_cases ha : s ≤ (ta : ℝ) <;> by_cases hb : s ≤ (tb : ℝ) <;>
        simp [ha, hb, map_add, add_assoc, add_comm, add_left_comm]

#print axioms fp81s21_blockValue_four_sum
end HRS.Fp81.S21
end
