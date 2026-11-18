import HRS.MS.Fp81S21ShiftKernel
import HRS.MS.Fp81S21ShiftKernel2
import HRS.MS.Fp81S21ShiftKernel3
import HRS.MS.R2ChaosAux30
import HRS.MS.R2SeAux1

open MeasureTheory Filter Topology ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- A bounded shift interval admits one finite-rank list whose members approximate
the commutator kernels both in product-law `L¹` and in the actual-centered
quadratic statistic uniformly over all particle numbers. -/
theorem fp81s21_initial_shift_kernel_finite_cover
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    (F : fp81s21_CompatPotentialFamily R)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hdecay : ∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
      HasCbBound (fp81s21_k0 p.d)
        (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
        (gradient ((F a).χ j))) :
    ∀ M : ℝ, 0 ≤ M → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ B C₂ : ℝ, 0 ≤ B ∧ 0 ≤ C₂ ∧
        (∀ a : Set.Ici (0 : ℝ), (a : ℝ) ≤ M →
          IsBoundedPairKernel p.s B
            (fun x y => commutatorKernel p.d p.s (gradient ((F a).χ j)) x y)) ∧
        ∃ m : ℕ, ∃ D : Fin m → fp81s21_RankKernel p.d,
          (∀ i, IsBoundedPairKernel p.s (C₂ * B) (D i).kernel) ∧
          ∀ a : Set.Ici (0 : ℝ), (a : ℝ) ≤ M →
            ∃ i : Fin m,
              Integrable
                (fun z : Euc p.d × Euc p.d =>
                  |commutatorKernel p.d p.s (gradient ((F a).χ j)) z.1 z.2 -
                    (D i).kernel z.1 z.2|)
                ((r26t3_mu R 0).prod (r26t3_mu R 0)) ∧
              (∫ z : Euc p.d × Euc p.d,
                |commutatorKernel p.d p.s (gradient ((F a).χ j)) z.1 z.2 -
                  (D i).kernel z.1 z.2|
                ∂((r26t3_mu R 0).prod (r26t3_mu R 0))) ≤ ε ∧
              ∀ N : ℕ, 2 ≤ N →
                Integrable
                  (fun X : EucConfig p.d N =>
                    fp81s21_initial_Bh R N
                        (fun x y => commutatorKernel p.d p.s
                          (gradient ((F a).χ j)) x y) X -
                      fp81s21_initial_Bh R N (D i).kernel X)
                  (r26t3_Q R N) ∧
                (∫ X : EucConfig p.d N,
                  |fp81s21_initial_Bh R N
                        (fun x y => commutatorKernel p.d p.s
                          (gradient ((F a).χ j)) x y) X -
                      fp81s21_initial_Bh R N (D i).kernel X|
                  ∂(r26t3_Q R N)) ≤ ε := by
  intro M hM j ε hε
  classical
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let k : Set.Ici (0 : ℝ) → Euc p.d → Euc p.d → ℝ := fun a x y =>
    commutatorKernel p.d p.s (gradient ((F a).χ j)) x y
  have hμ : IsProbabilityMeasure μ :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  letI : IsProbabilityMeasure μ := hμ
  obtain ⟨B, C₂, hB, hC₂, hkernelBound, hnet⟩ :=
    fp81s21_compat_kernel_finite_L2_net hδ hδh R F hC hc hdecay M hM j
  let Bdiff : ℝ := B + C₂ * B
  have hBdiff : 0 ≤ Bdiff := by
    dsimp [Bdiff]
    exact add_nonneg hB (mul_nonneg hC₂ hB)
  obtain ⟨η₀, hη₀, hmod⟩ :=
    fp81s21_initial_Bh_small_of_L2 hδ hδh R E hγ Bdiff hBdiff ε hε
  let η : ℝ := min η₀ ε
  have hη : 0 < η := lt_min hη₀ hε
  have hη₀' : η ≤ η₀ := min_le_left _ _
  have hηε : η ≤ ε := min_le_right _ _
  obtain ⟨m, D, hDbound, hnetη⟩ := hnet η hη
  refine ⟨B, C₂, hB, hC₂, (by
    intro a haM
    exact hkernelBound a haM), m, D, hDbound, ?_⟩
  intro a haM
  obtain ⟨i, hL2⟩ := hnetη a haM
  let hdiff : Euc p.d → Euc p.d → ℝ := fun x y => k a x y - (D i).kernel x y
  have hdiffBound : IsBoundedPairKernel p.s Bdiff hdiff := by
    simpa [hdiff, Bdiff, k] using
      HRS.MS.R2Chaos.s94_sub_isBounded (hkernelBound a haM) (hDbound i)
  have huncurry : Function.uncurry hdiff = fun z : Euc p.d × Euc p.d =>
      k a z.1 z.2 - (D i).kernel z.1 z.2 := by
    funext z
    rfl
  have hL2net :
      eLpNorm (Function.uncurry hdiff) 2 (μ.prod μ) ≤ ENNReal.ofReal η := by
    rw [huncurry]
    simpa [μ] using hL2
  have hL2small :
      eLpNorm (Function.uncurry hdiff) 2 (μ.prod μ) ≤ ENNReal.ofReal η₀ :=
    hL2net.trans (ENNReal.ofReal_le_ofReal hη₀')
  have hstatSmall := hmod hdiff hdiffBound hL2small
  have hL1norm : eLpNorm (Function.uncurry hdiff) 1 (μ.prod μ) ≤ ENNReal.ofReal ε := by
    calc
      eLpNorm (Function.uncurry hdiff) 1 (μ.prod μ)
          ≤ eLpNorm (Function.uncurry hdiff) 2 (μ.prod μ) :=
            eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      _ ≤ ENNReal.ofReal η := hL2net
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hηε
  have hpairL1 := S99.s99_l1_bound hε.le
    hdiffBound.measurable.aestronglyMeasurable hL1norm
  have hpairAbsInt : Integrable
      (fun z : Euc p.d × Euc p.d => |hdiff z.1 z.2|) (μ.prod μ) := by
    simpa [Real.norm_eq_abs] using hpairL1.1.norm
  have hpairIntegralBound :
      (∫ z : Euc p.d × Euc p.d,
        |k a z.1 z.2 - (D i).kernel z.1 z.2| ∂(μ.prod μ)) ≤ ε := by
    simpa [hdiff, k, μ, Function.uncurry] using hpairL1.2
  refine ⟨i, hpairAbsInt, hpairIntegralBound, ?_⟩
  intro N hN
  have hstatSmallN := hstatSmall N hN
  have hstatEqN :
      (fun X : EucConfig p.d N =>
        fp81s21_initial_Bh R N (k a) X -
          fp81s21_initial_Bh R N (D i).kernel X) =
      fun X => fp81s21_initial_Bh R N hdiff X := by
    funext X
    simpa [hdiff, k] using
      fp81s21_initial_Bh_sub hδ hδh R E hγ (hkernelBound a haM) (hDbound i) hN X
  have hactualDiffIntN :
      Integrable
        (fun X : EucConfig p.d N =>
          fp81s21_initial_Bh R N (k a) X -
            fp81s21_initial_Bh R N (D i).kernel X)
        (r26t3_Q R N) := by
    rw [hstatEqN]
    exact hstatSmallN.1
  have hstatL1N := S99.s99_l1_bound hε.le
    hstatSmallN.1.aestronglyMeasurable hstatSmallN.2
  have hactualAbsIntEqN :
      (fun X : EucConfig p.d N =>
        |fp81s21_initial_Bh R N (k a) X -
          fp81s21_initial_Bh R N (D i).kernel X|) =
      fun X => |fp81s21_initial_Bh R N hdiff X| := by
    funext X
    exact congrArg abs (congrFun hstatEqN X)
  have hactualIntegralEqN :
      (∫ X : EucConfig p.d N,
        |fp81s21_initial_Bh R N (k a) X -
          fp81s21_initial_Bh R N (D i).kernel X|
        ∂(r26t3_Q R N)) =
      ∫ X : EucConfig p.d N, |fp81s21_initial_Bh R N hdiff X| ∂(r26t3_Q R N) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun X => congrFun hactualAbsIntEqN X
  exact ⟨hactualDiffIntN, by rw [hactualIntegralEqN]; exact hstatL1N.2⟩

#print axioms fp81s21_initial_shift_kernel_finite_cover

end HRS.Fp81.S21

end
