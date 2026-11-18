import HRS.MS.UniqN4bE

/-!
# N4b of `UniqPlan.md`, part F: `L²` bounds of `ψ = ς f` and its gradient on the ball `B̄(p, 8L)`

For `ς ∈ C²` with `0 ≤ ς ≤ 1`, `‖∇ς‖ ≤ K`, `tsupport ς ⊆ B̄(p, 2L)`, and `f ∈ C¹` with
`‖1_E f‖₂ ≤ m`, `‖1_E ∇f‖₂ ≤ G` on `E = B̄(p, 8L)`:
`‖ψ‖₂ ≤ m`, `‖∇ψ‖₂ ≤ G + K m` and `‖1_E ∂_j f‖₂ ≤ G`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN4b

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqN2b

variable {d : ℕ}

theorem n4b_enorm_le {x y : ℝ} (h : |x| ≤ |y|) : ‖x‖ₑ ≤ ‖y‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using h)

theorem n4b_D1_cont {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin d) : Continuous (D1 j f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem n4b_norms {p : Euc d} {L K : ℝ} (hK : 0 ≤ K) {ς f : Euc d → ℝ} (hς : ContDiff ℝ 2 ς)
    (hς01 : ∀ y, 0 ≤ ς y ∧ ς y ≤ 1) (hςK : ∀ y, ‖fderiv ℝ ς y‖ ≤ K)
    (hςs : tsupport ς ⊆ closedBall p (2 * L)) (hL : 0 ≤ L) (hf : ContDiff ℝ 1 f)
    {m G : ℝ} (hm : 0 ≤ m) (hG : 0 ≤ G)
    (hfm : eLpNorm ((closedBall p (8 * L)).indicator f) 2 volume ≤ ENNReal.ofReal m)
    (hGint : ∫ y in closedBall p (8 * L), ‖fderiv ℝ f y‖ ^ 2 ≤ G ^ 2) :
    eLpNorm (fun x => ‖fderiv ℝ (fun x => ς x * f x) x‖) 2 volume ≤ ENNReal.ofReal (G + K * m) ∧
    eLpNorm (fun x => ς x * f x) 2 volume ≤ ENNReal.ofReal m ∧
    ∀ j : Fin d, eLpNorm ((closedBall p (8 * L)).indicator (D1 j f)) 2 volume ≤ ENNReal.ofReal G := by
  set E : Set (Euc d) := closedBall p (8 * L) with hE
  have hEm : MeasurableSet E := measurableSet_closedBall
  have hEc : IsCompact E := isCompact_closedBall _ _
  have hς2E : closedBall p (2 * L) ⊆ E := closedBall_subset_closedBall (by linarith)
  have hςE : ∀ y, y ∉ E → ς y = 0 ∧ fderiv ℝ ς y = 0 := by
    intro y hy
    have hy' : y ∉ tsupport ς := fun h => hy (hς2E (hςs h))
    refine ⟨image_eq_zero_of_notMem_tsupport hy', ?_⟩
    by_contra h0
    exact hy' ((support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 h0))
  have hfdC : Continuous (fun y => ‖fderiv ℝ f y‖) := (hf.continuous_fderiv one_ne_zero).norm
  have hψC : ContDiff ℝ 1 (fun x => ς x * f x) := (hς.of_le (by norm_num)).mul hf
  -- second claim
  have h2 : eLpNorm (fun x => ς x * f x) 2 volume ≤ ENNReal.ofReal m := by
    refine le_trans (eLpNorm_mono_enorm hψC.continuous.aestronglyMeasurable (g := E.indicator f)
      (fun y => ?_)) hfm
    by_cases hy : y ∈ E
    · rw [Set.indicator_of_mem hy]
      refine n4b_enorm_le ?_
      rw [abs_mul]
      calc |ς y| * |f y| ≤ 1 * |f y| := by
            gcongr; rw [abs_of_nonneg (hς01 y).1]; exact (hς01 y).2
        _ = _ := one_mul _
    · rw [Set.indicator_of_notMem hy, (hςE y hy).1]; simp
  -- third claim
  have h3 : ∀ j : Fin d, eLpNorm (E.indicator (D1 j f)) 2 volume ≤ ENNReal.ofReal G := by
    intro j
    have hc := n4b_D1_cont hf j
    refine n4b_eLp_le hc.aestronglyMeasurable hEm
      ((hc.pow 2).continuousOn.integrableOn_compact hEc) hG ?_
    refine le_trans ?_ hGint
    refine setIntegral_mono_on ((hc.pow 2).continuousOn.integrableOn_compact hEc)
      ((hfdC.pow 2).continuousOn.integrableOn_compact hEc) hEm fun y _ => ?_
    have := n2b_D1_le j f y
    calc (D1 j f y) ^ 2 = |D1 j f y| ^ 2 := (sq_abs _).symm
      _ ≤ ‖fderiv ℝ f y‖ ^ 2 := by gcongr
  refine ⟨?_, h2, h3⟩
  -- first claim
  set W1 : Euc d → ℝ := E.indicator (fun y => ‖fderiv ℝ f y‖) with hW1
  set W2 : Euc d → ℝ := K • (fun y => ‖E.indicator f y‖) with hW2
  have hW1m : AEStronglyMeasurable W1 volume := hfdC.aestronglyMeasurable.indicator hEm
  have hW2m : AEStronglyMeasurable W2 volume :=
    ((hf.continuous.aestronglyMeasurable.indicator hEm).norm).const_smul K
  have hW1b : eLpNorm W1 2 volume ≤ ENNReal.ofReal G := by
    have := n4b_eLp_le (E := E) hfdC.aestronglyMeasurable hEm
      ((hfdC.pow 2).continuousOn.integrableOn_compact hEc) hG hGint
    exact this
  have hW2b : eLpNorm W2 2 volume ≤ ENNReal.ofReal (K * m) := by
    rw [hW2, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hK,
      ENNReal.ofReal_mul hK,
      eLpNorm_norm (E.indicator f)]
    exact mul_le_mul' le_rfl hfm
    exact hf.continuous.aestronglyMeasurable.indicator hEm
  have hsum : eLpNorm (W1 + W2) 2 volume ≤ ENNReal.ofReal (G + K * m) := by
    refine (eLpNorm_add_le one_le_two).trans ?_
    rw [ENNReal.ofReal_add hG (mul_nonneg hK hm)]
    exact add_le_add hW1b hW2b
  refine le_trans (eLpNorm_mono (g := W1 + W2) ?_ (fun x => ?_)) hsum
  · exact (((hψC.continuous_fderiv one_ne_zero).norm)).aestronglyMeasurable
  · by_cases hx : x ∈ E
    · have hd := fderiv_fun_mul ((hς.differentiable (by norm_num)) x) (hf.differentiable one_ne_zero x)
      simp only [Pi.add_apply, hW1, hW2, Set.indicator_of_mem hx, Pi.smul_apply, smul_eq_mul]
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      rw [hd]
      calc ‖ς x • fderiv ℝ f x + f x • fderiv ℝ ς x‖
          ≤ ‖ς x • fderiv ℝ f x‖ + ‖f x • fderiv ℝ ς x‖ := norm_add_le _ _
        _ = ς x * ‖fderiv ℝ f x‖ + ‖f x‖ * ‖fderiv ℝ ς x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs (ς x), abs_of_nonneg (hς01 x).1]
        _ ≤ ‖fderiv ℝ f x‖ + K * ‖f x‖ := by
            have h1 : ς x * ‖fderiv ℝ f x‖ ≤ 1 * ‖fderiv ℝ f x‖ :=
              mul_le_mul_of_nonneg_right (hς01 x).2 (norm_nonneg _)
            have h2 : ‖f x‖ * ‖fderiv ℝ ς x‖ ≤ ‖f x‖ * K :=
              mul_le_mul_of_nonneg_left (hςK x) (norm_nonneg _)
            nlinarith
    · have hd0 : fderiv ℝ (fun x => ς x * f x) x = 0 := by
        have hd := fderiv_fun_mul ((hς.differentiable (by norm_num)) x) (hf.differentiable one_ne_zero x)
        rw [hd, (hςE x hx).1, (hςE x hx).2]; simp
      simp only [Pi.add_apply, hW1, hW2, Set.indicator_of_notMem hx, Pi.smul_apply, smul_eq_mul]
      rw [hd0]
      simp

end HRS.MS.UniqN4b
