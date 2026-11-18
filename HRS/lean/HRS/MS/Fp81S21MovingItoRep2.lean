import HRS.MS.Fp81S21MovingItoRep

/-!
# HRS S2.1(iii), packet 8.5: moving progressive noise coordinates

This file retains Aux94's exact `s102_PhicE` coefficient and Aux100's
simultaneous coordinate/stopping conclusion. The only change in the
progressive local-L² producer is replacing stationary `S102Std.hcls` by
`Fp81MovingStd.hcls`; the proof uses the classical-adjoint bounds, not the
stationary-density fields. Stochastic integration always uses the supplied
filtered path `X` and filtration `ℱ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- The existing Euclidean noise coefficient is progressive and locally
square-integrable under the moving classical-adjoint hypotheses. -/
theorem fp81s21_moving_PhicE_locL2
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (L : ℕ) {N : ℕ} {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) {ℱ : Filtration ℝ mΩ}
    (X : ℝ≥0 → Ω → EucConfig p.d N)
    (hX : IsProgressive ℱ (ofNNRealTime X))
    {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H r c hH) :
    IsProgressiveLocL2E P ℱ
      (s102_PhicE (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) hH L X) := by
  classical
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := wholeSpaceIndex p.d
  have hOrbit : ∀ i : Fin (s102_q p.d L),
      IsClassicalAdjointW C (s102_tk hH L i) (oscTestFun m (s102_alk L i))
        (s102_orb C m hH L i) := by
    intro i
    exact s102_propagator_classical
      (hstd.hcls (s102_alk L i) (s102_tk hH L i) (s102_tauk hH L i).2)
  set K : ℝ := Real.sqrt N * (Real.sqrt (2 * C.ν) / N) with hK
  have hprog : IsProgressive ℱ (s102_PhicE C m hH L X) := by
    intro j
    refine (@measurable_pi_iff _ _ _
      (Subtype.instMeasurableSpace.prod (ℱ j)) _).2 fun k => ?_
    have hcoord : ∀ i : Fin (s102_q p.d L),
        Measurable[Subtype.instMeasurableSpace.prod (ℱ j)]
          (fun q : Set.Iic j × Ω => K *
            s102_Ig (s102_orb C m hH L i) (s102_tk hH L i) X q.1 q.2 k) := by
      intro i
      exact ((measurable_pi_apply k).comp
        (s102_Ig_progressive (hOrbit i) hX j)).const_mul K
    exact (EuclideanSpace.equiv (Fin (s102_q p.d L)) ℝ).symm.continuous.measurable.comp
      ((@measurable_pi_iff _ _ _
        (Subtype.instMeasurableSpace.prod (ℱ j)) _).2 hcoord)
  choose Bg hBg using fun i : Fin (s102_q p.d L) =>
    s102_Ig_bdd (hOrbit i) X
  set B : ℝ := |K| * ∑ i, max (Bg i) 0 with hB
  have hB0 : 0 ≤ B := by positivity
  have hnorm : ∀ u ζ k,
      ‖s102_PhicE C m hH L X u ζ k‖ ≤
        Real.sqrt (s102_q p.d L) * B := by
    intro u ζ k
    refine s102_eucl_norm_le hB0 _ fun i => ?_
    rw [s102_PhicE_apply]
    rw [abs_mul]
    have hsum : |s102_Ig (s102_orb C m hH L i)
        (s102_tk hH L i) X u ζ k| ≤ ∑ i, max (Bg i) 0 := by
      exact (hBg i u ζ k).trans ((le_max_left _ _).trans
        (Finset.single_le_sum (f := fun i => max (Bg i) 0)
          (fun i _ => le_max_right _ _) (Finset.mem_univ i)))
    calc
      |Real.sqrt N * (Real.sqrt (2 * C.ν) / N)| *
          |s102_Ig (s102_orb C m hH L i)
            (s102_tk hH L i) X u ζ k|
          = |K| * |s102_Ig (s102_orb C m hH L i)
              (s102_tk hH L i) X u ζ k| := by rw [hK]
      _ ≤ |K| * ∑ i, max (Bg i) 0 :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = B := by rw [hB]
  refine ⟨hprog, fun T' => Eventually.of_forall fun ω => ?_⟩
  have hle : ∀ s, ∑ k : Fin N × Fin p.d,
      ‖s102_PhicE C m hH L X s ω k‖ₑ ^ 2 ≤
        ∑ _k : Fin N × Fin p.d,
          (ENNReal.ofReal (Real.sqrt (s102_q p.d L) * B)) ^ 2 := by
    intro s
    refine Finset.sum_le_sum fun k _ => ?_
    gcongr
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hnorm s ω k)
  calc
    ∫⁻ s in Icc 0 T', ∑ k : Fin N × Fin p.d,
        ‖s102_PhicE C m hH L X s ω k‖ₑ ^ 2
      ≤ ∫⁻ _s in Icc 0 T', ∑ _k : Fin N × Fin p.d,
          (ENNReal.ofReal (Real.sqrt (s102_q p.d L) * B)) ^ 2 :=
        lintegral_mono hle
    _ < ⊤ := by
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top
        (ENNReal.sum_lt_top.2 fun _ _ => ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
        (by simp)

/-- Coordinate form of the local Euclidean stochastic integral, including its
stopping at the corresponding observation time. The exceptional set is
simultaneous in every real time `u`. -/
theorem fp81s21_moving_loc_coord
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (L : ℕ) {N : ℕ} {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin p.d) → ℝ}
    (hW : IsBrownianFiltration P ℱ W')
    (X : ℝ≥0 → Ω → EucConfig p.d N)
    (hX : IsProgressive ℱ (ofNNRealTime X))
    {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H r c hH)
    (i : Fin (s102_q p.d L)) :
    ∀ᵐ ζ ∂P, ∀ u : ℝ,
      (localItoIntegralE P ℱ W'
        (s102_PhicE (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) hH L X)
        u ζ).ofLp i =
          (Real.sqrt N *
            (Real.sqrt (2 * (r26t3_coeff R).ν) / N)) *
            itoIntegral P ℱ W'
              (s102_Ig (s102_orb (r26t3_coeff R)
                (wholeSpaceIndex p.d : ℝ) hH L i)
                (s102_tk hH L i) X) u ζ ∧
      itoIntegral P ℱ W'
        (s102_Ig (s102_orb (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) hH L i)
          (s102_tk hH L i) X) u ζ =
        itoIntegral P ℱ W'
          (s102_Ig (s102_orb (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) hH L i)
            (s102_tk hH L i) X)
          (min u (s102_tk hH L i)) ζ := by
  set C : WholeCoeff p.d := r26t3_coeff R
  set m : ℝ := (wholeSpaceIndex p.d : ℝ)
  set K : ℝ := Real.sqrt N * (Real.sqrt (2 * C.ν) / N)
  have hf : IsClassicalAdjointW C (s102_tk hH L i)
      (oscTestFun m (s102_alk L i)) (s102_orb C m hH L i) := by
    exact s102_propagator_classical
      (hstd.hcls (s102_alk L i) (s102_tk hH L i)
        (s102_tauk hH L i).2)
  obtain ⟨Bg, hBg⟩ := s102_Ig_bdd hf X
  have hIg : IsProgressiveL2 P ℱ
      (s102_Ig (s102_orb C m hH L i) (s102_tk hH L i) X) :=
    IsProgressiveL2.of_bounded P
      (s102_Ig_progressive hf hX) Bg hBg
  have hPhi := fp81s21_moving_PhicE_locL2 p R hH L P X hX hstd
  have hsm : IsProgressiveL2 P ℱ
      (fun s ω => K • s102_Ig (s102_orb C m hH L i)
        (s102_tk hH L i) X s ω) := hIg.smul K
  have hco :
      (fun s ω k =>
        (s102_PhicE C m hH L X s ω k).ofLp i) =
      (fun s ω => K • s102_Ig (s102_orb C m hH L i)
        (s102_tk hH L i) X s ω) := by
    funext s ω k
    rw [show (s102_PhicE C m hH L X s ω k).ofLp i =
      s102_PhicE C m hH L X s ω k i from rfl, s102_PhicE_apply]
    rfl
  have h1 := localItoIntegralE_euclidean hW
    (s102_PhicE C m hH L X) hPhi i
  have h2 := localItoIntegral_eq_itoIntegral hW hsm
  have h3 := itoIntegral_smul hW hIg K
  have h4 := s102_ito_stop hW hIg (t := s102_tk hH L i)
    (s102_tauk hH L i).2.1
    (fun s ω k hs => by
      unfold s102_Ig
      rw [if_neg (fun h => absurd h.2 (not_le.2 hs))])
    (fun s ω k hs => by
      unfold s102_Ig
      rw [if_neg (fun h => absurd h.1 (not_le.2 hs))])
  filter_upwards [h1, h2, h3, h4] with ζ e1 e2 e3 e4 u
  refine ⟨?_, e4 u⟩
  rw [e1 u, hco, e2 u, e3 u]

#print axioms HRS.Fp81.S21.fp81s21_moving_PhicE_locL2
#print axioms HRS.Fp81.S21.fp81s21_moving_loc_coord

end HRS.Fp81.S21

end
