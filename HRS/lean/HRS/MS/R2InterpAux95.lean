import HRS.MS.R2InterpAux94

/-!
# S10.2 (worker S10R), part 95 (packet F5j): `Φc` is a progressive, locally square-integrable integrand
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

theorem s102_orb_classical (hs : S102Std C m T r c) (hT : 0 < T) (L : ℕ) (i : Fin (s102_q d L)) :
    IsClassicalAdjointW C (s102_tk hT L i) (oscTestFun m (s102_alk L i)) (s102_orb C m hT L i) :=
  s102_propagator_classical (hs.hcls (s102_alk L i) _ (s102_tauk hT L i).2)

theorem s102_PhicE_locL2 (hs : S102Std C m T r c) (hT : 0 < T) (L : ℕ) {N : ℕ} {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) {ℱ : Filtration ℝ mΩ} (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsProgressive ℱ (ofNNRealTime X)) : IsProgressiveLocL2E P ℱ (s102_PhicE C m hT L X) := by
  classical
  set K : ℝ := Real.sqrt N * (Real.sqrt (2 * C.ν) / N) with hK
  have hprog : IsProgressive ℱ (s102_PhicE C m hT L X) := by
    intro j
    refine (@measurable_pi_iff _ _ _ (Subtype.instMeasurableSpace.prod (ℱ j)) _).2 fun k => ?_
    have hcoord : ∀ i : Fin (s102_q d L), Measurable[Subtype.instMeasurableSpace.prod (ℱ j)]
        fun p : Set.Iic j × Ω => K * s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X p.1 p.2 k := fun i =>
      ((measurable_pi_apply k).comp (s102_Ig_progressive (s102_orb_classical hs hT L i) hX j)).const_mul K
    exact (EuclideanSpace.equiv (Fin (s102_q d L)) ℝ).symm.continuous.measurable.comp
      (@measurable_pi_iff _ _ _ (Subtype.instMeasurableSpace.prod (ℱ j)) _ |>.2 hcoord)
  choose Bg hBg using fun i : Fin (s102_q d L) => s102_Ig_bdd (s102_orb_classical hs hT L i) X
  set B : ℝ := |K| * ∑ i, max (Bg i) 0 with hB
  have hB0 : 0 ≤ B := by positivity
  have hnorm : ∀ u ζ k, ‖s102_PhicE C m hT L X u ζ k‖ ≤ Real.sqrt (s102_q d L) * B := by
    intro u ζ k
    refine s102_eucl_norm_le hB0 _ fun i => ?_
    rw [s102_PhicE_apply, abs_mul]
    have : |s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X u ζ k| ≤ ∑ i, max (Bg i) 0 :=
      (hBg i u ζ k).trans ((le_max_left _ _).trans
        (Finset.single_le_sum (f := fun i => max (Bg i) 0) (fun i _ => le_max_right _ _) (Finset.mem_univ i)))
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _) |>.trans (by rw [hB])
  refine ⟨hprog, fun T' => Eventually.of_forall fun ω => ?_⟩
  have hle : ∀ s, ∑ k : Fin N × Fin d, ‖s102_PhicE C m hT L X s ω k‖ₑ ^ 2 ≤
      ∑ _k : Fin N × Fin d, (ENNReal.ofReal (Real.sqrt (s102_q d L) * B)) ^ 2 := fun s =>
    Finset.sum_le_sum fun k _ => by
      gcongr
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hnorm s ω k)
  calc ∫⁻ s in Icc 0 T', ∑ k : Fin N × Fin d, ‖s102_PhicE C m hT L X s ω k‖ₑ ^ 2
      ≤ ∫⁻ _s in Icc 0 T', ∑ _k : Fin N × Fin d, (ENNReal.ofReal (Real.sqrt (s102_q d L) * B)) ^ 2 :=
        lintegral_mono hle
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top (ENNReal.sum_lt_top.2 fun _ _ => ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (by simp)

end HRS.MS.R2Interp

end
