import HRS.MS.MovEntAux21

/-!
# S6.6, packet P5 (part 5): the Itô integrand of `m = N⁻¹∑|x_i|²` is `L²` and the window estimate

`s66_Phi_form`, `s66_Phi_sqsum`, `s66_Phi_L2`: the explicit integrand and its `L²(dt⊗P)` norm (from a uniform second-moment bound).
`s66_window`: `E sup_{t ∈ [b,b+T]} m_t ≤ C_T`, with `C_T` independent of `b, N, ρ` (BDG `p = 2` for the increments).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole HRS.MH.DualityRd

variable {d : ℕ}

/-- The Itô integrand of `sumLift N |·|²`. -/
def s66Phi {Ω : Type*} {N : ℕ} (D : WholeDyn d) (T : ℝ) (X : ℝ≥0 → Ω → EucConfig d N) :
    ℝ → Ω → (Fin N × Fin d) → ℝ :=
  itoIntegrand T Set.univ (fun _ x => HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2) x) (ofNNRealTime X)
    (fun _ _ => noiseDir D)

theorem s66_Phi_form {Ω : Type*} {N : ℕ} (D : WholeDyn d) (T : ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (s' : ℝ) (ζ : Ω) (k : Fin N × Fin d) :
    s66Phi D T X s' ζ k =
      if s' ∈ Set.Icc (0 : ℝ) T then
        (N : ℝ)⁻¹ * (2 * (Real.sqrt (2 * D.invβ) * (X s'.toNNReal ζ k.1) k.2)) else 0 := by
  unfold s66Phi itoIntegrand
  by_cases hs : s' ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs, if_pos hs]
    simp only [Set.mem_univ, Set.setOf_true, Set.indicator_univ, ofNNRealTime_apply]
    rw [HRS.fderiv_sumLift_apply ((contDiff_norm_sq ℝ : ContDiff ℝ 1 (fun x : Euc d => ‖x‖ ^ 2)).differentiable one_ne_zero)]
    simp only [s66_fderiv_normsq]
    rw [← Finset.mul_sum]
    rw [da4_sum_inner_noiseDir D (fun i => X s'.toNNReal ζ i) k]
  · rw [Set.indicator_of_notMem hs, if_neg hs]

theorem s66_Phi_sqsum {Ω : Type*} {N : ℕ} (hN : 0 < N) (D : WholeDyn d) (hinv : 0 ≤ D.invβ) (T : ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (s' : ℝ) (ζ : Ω) :
    ∑ k, ‖s66Phi D T X s' ζ k‖ₑ ^ 2 =
      if s' ∈ Set.Icc (0 : ℝ) T then
        ENNReal.ofReal ((8 * D.invβ / N) * movSecondMoment (X s'.toNNReal ζ)) else 0 := by
  by_cases hs : s' ∈ Set.Icc (0 : ℝ) T
  · rw [if_pos hs]
    simp only [s66_Phi_form, if_pos hs, HRS.enorm_sq_eq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    congr 1
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hc : Real.sqrt (2 * D.invβ) ^ 2 = 2 * D.invβ := Real.sq_sqrt (by linarith)
    have e1 : ∀ k : Fin N × Fin d, ((N : ℝ)⁻¹ * (2 * (Real.sqrt (2 * D.invβ) * (X s'.toNNReal ζ k.1) k.2))) ^ 2 =
        (8 * D.invβ / (N : ℝ) ^ 2) * ((X s'.toNNReal ζ k.1) k.2) ^ 2 := by
      intro k
      calc _ = (N : ℝ)⁻¹ ^ 2 * 4 * (Real.sqrt (2 * D.invβ) ^ 2) * ((X s'.toNNReal ζ k.1) k.2) ^ 2 := by ring
        _ = _ := by rw [hc]; field_simp; ring
    simp only [e1]
    rw [← Finset.mul_sum, Fintype.sum_prod_type]
    have e2 : ∀ i : Fin N, ∑ l : Fin d, ((X s'.toNNReal ζ i) l) ^ 2 = ‖X s'.toNNReal ζ i‖ ^ 2 := by
      intro i
      rw [EuclideanSpace.real_norm_sq_eq]
    simp only [e2]
    unfold movSecondMoment
    field_simp
  · rw [if_neg hs]
    simp only [s66_Phi_form, if_neg hs, enorm_zero]
    simp

theorem s66_Phi_prog {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ} {N : ℕ} (D : WholeDyn d)
    (T : ℝ) {X : ℝ≥0 → Ω → EucConfig d N} (hX : IsProgressive ℱ (ofNNRealTime X)) :
    IsProgressive ℱ (s66Phi D T X) := by
  have hfun : s66Phi D T X = fun s' ζ k => (fun (r : ℝ) (Y : EucConfig d N) (k : Fin N × Fin d) =>
      if r ∈ Set.Icc (0 : ℝ) T then (N : ℝ)⁻¹ * (2 * (Real.sqrt (2 * D.invβ) * (Y k.1) k.2)) else 0)
        s' (ofNNRealTime X s' ζ) k := by
    funext s' ζ k
    rw [s66_Phi_form]
    rfl
  rw [hfun]
  have hg : Measurable (Function.uncurry fun (r : ℝ) (Y : EucConfig d N) (k : Fin N × Fin d) =>
      if r ∈ Set.Icc (0 : ℝ) T then (N : ℝ)⁻¹ * (2 * (Real.sqrt (2 * D.invβ) * (Y k.1) k.2)) else 0) := by
    refine measurable_pi_iff.2 fun k => ?_
    refine Measurable.ite (measurableSet_Icc.preimage measurable_fst) ?_ measurable_const
    have ha : Measurable (fun Y : EucConfig d N => Y k.1) := measurable_pi_apply k.1
    have hb : Measurable (fun x : Euc d => x k.2) :=
      (EuclideanSpace.proj (𝕜 := ℝ) k.2).continuous.measurable
    have h1 : Measurable (fun p : ℝ × EucConfig d N => (p.2 k.1) k.2) :=
      (hb.comp ha).comp measurable_snd
    exact measurable_const.mul (measurable_const.mul (measurable_const.mul h1))
  exact HRS.isProgressive_comp_measurable' (ofNNRealTime X) hX _ hg

theorem s66_Phi_L2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {N : ℕ} (hN : 0 < N) (D : WholeDyn d) (hinv : 0 ≤ D.invβ) (T : ℝ)
    {X : ℝ≥0 → Ω → EucConfig d N} (hX : IsProgressive ℱ (ofNNRealTime X)) {Cm : ℝ}
    (hmom : ∀ t : ℝ, 0 ≤ t → ∫⁻ ζ, ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal Cm) :
    IsProgressiveL2 P ℱ (s66Phi D T X) := by
  refine ⟨s66_Phi_prog D T hX, fun T'' => ?_⟩
  unfold sqIntegralOn
  set c : ℝ := 8 * D.invβ / N with hc
  have hc0 : 0 ≤ c := by positivity
  have hle : ∀ ζ, ∫⁻ s in Set.Icc (0 : ℝ) T'', ∑ k, ‖s66Phi D T X s ζ k‖ₑ ^ 2 ≤
      ∫⁻ s in Set.Icc (0 : ℝ) T'', ENNReal.ofReal (c * movSecondMoment (X s.toNNReal ζ)) := by
    intro ζ
    refine lintegral_mono fun s => ?_
    rw [s66_Phi_sqsum hN D hinv T X s ζ]
    split_ifs
    · exact le_rfl
    · exact zero_le
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  have hG : Measurable (fun Y : EucConfig d N => ENNReal.ofReal (c * movSecondMoment Y)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul s66_measurable_secondMoment)
  have hbound := s66_swap_bound hX (fun Y => ENNReal.ofReal (c * movSecondMoment Y)) hG 0 T''
    (ENNReal.ofReal c * ENNReal.ofReal Cm) (fun s hs => by
      have hs0 : 0 ≤ s := hs.1
      calc ∫⁻ ζ, ENNReal.ofReal (c * movSecondMoment (X s.toNNReal ζ)) ∂P
          = ∫⁻ ζ, ENNReal.ofReal c * ENNReal.ofReal (movSecondMoment (X s.toNNReal ζ)) ∂P := by
            refine lintegral_congr fun ζ => ?_
            rw [ENNReal.ofReal_mul hc0]
        _ = ENNReal.ofReal c * ∫⁻ ζ, ENNReal.ofReal (movSecondMoment (X s.toNNReal ζ)) ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal c * ENNReal.ofReal Cm := mul_le_mul' le_rfl (hmom s hs0))
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))

end HRS.MS.MovEnt

end
