import HRS.MC.S7PIHC4Time

/-!
# Packet piH: `s7_PIH_heat_c12_proof'` (the `C^{1,2}` extension of the heat function piece)

The statement of `s7_PIH_heat_c12` in `HRS/MC/S7PIPlan.lean` is FALSE for `T = 0`: with `a = b = T = 0`
the set `Set.Icc 0 T` is a singleton, `derivWithin (fun s => f s c) {0} 0 = 0` (Mathlib convention), while the
right hand side is `-(1/2) ∑ A 0 i j * D²(gaussHeat S G 0) c (e_i,e_j)`, which is non-zero for, e.g.,
`q = 1`, `A 0 = 1`, `S 0 = 0`, `G = cos`, `c = 0`.  The repaired statement adds `(hT : 0 < T)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {q : ℕ}

/-- **H1b (`C^{1,2}` extension, for the Itô formula), REPAIRED: with `0 < T`.** -/
theorem s7_PIH_heat_c12_proof' {q : ℕ} (a b T : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (hT : 0 < T)
    (A S : ℝ → Matrix (Fin q) (Fin q) ℝ) (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (hApsd : ∀ v ∈ Set.Icc a b, (A v).PosSemidef) (hSb : (S b).PosSemidef)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 4 G) :
    ∃ f : ℝ → EuclideanSpace ℝ (Fin q) → ℝ, HRS.IsC12On T Set.univ f ∧
      (∀ r ∈ Set.Icc a b, f r = gaussHeat S G r) ∧
      ∀ r ∈ Set.Icc a b, ∀ c, derivWithin (fun s => f s c) (Set.Icc 0 T) r =
        -(1 / 2) * ∑ i, ∑ j, A r i j *
          iteratedFDeriv ℝ 2 (gaussHeat S G r) c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
  have hcit : ∀ {j : ℕ}, j ≤ 4 → ∀ m : Fin j → EuclideanSpace ℝ (Fin q),
      Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin q) =>
        iteratedFDeriv ℝ j (gaussHeat S G (S7PIH_rho a b p.1)) p.2 m) :=
    fun hj m => S7PIH_cont_iter hab hA hApsd hSb hS hG hj m
  have hcA : ∀ i j : Fin q, Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin q) =>
      A (S7PIH_rho a b p.1) i j) := fun i j =>
    (S7PIH_cont_A hab hA i j).comp continuous_fst
  have hcτ : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin q) => p.1 - S7PIH_rho a b p.1) :=
    continuous_fst.sub ((S7PIH_rho_cont a b).comp continuous_fst)
  have hF0 : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin q) =>
      gaussHeat S G (S7PIH_rho a b p.1) p.2) :=
    (hcit (j := 0) (by norm_num) default).congr (fun p => iteratedFDeriv_zero_apply _)
  have hWc : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin q) =>
      S7PIH_Wphi (fun i j => A (S7PIH_rho a b p.1) i j) (gaussHeat S G (S7PIH_rho a b p.1)) p.2) := by
    unfold S7PIH_Wphi
    exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (hcA i j).mul (hcit (j := 2) (by norm_num) _))
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ (Fin q),
      derivWithin (fun r => S7PIH_ext a b A S G r x) (Set.Icc 0 T) t =
        S7PIH_Wphi (fun i j => A (S7PIH_rho a b t) i j) (gaussHeat S G (S7PIH_rho a b t)) x :=
    fun t ht x => ((S7PIH_ext_hasDerivAt hab hA hApsd hSb hS hG x t).hasDerivWithinAt).derivWithin
      (uniqueDiffOn_Icc hT t ht)
  refine ⟨S7PIH_ext a b A S G, ?_, ?_, ?_⟩
  · refine
      { cont := ?_
        hasFDerivAt := fun t _ x _ =>
          ((S7PIH_ext_contDiff (a := a) (b := b) (A := A) (S := S) hG t).differentiable (by norm_num) x).hasFDerivAt
        hasFDerivAt_fderiv := fun t _ x _ =>
          (((S7PIH_ext_contDiff (a := a) (b := b) (A := A) (S := S) hG t).fderiv_right (m := 1)
            (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
        cont_fderiv := ?_
        cont_fderiv₂ := ?_
        hasDerivWithinAt := ?_
        cont_deriv := ?_ }
    · have : Continuous (Function.uncurry (S7PIH_ext a b A S G)) := by
        have h : Function.uncurry (S7PIH_ext a b A S G) = fun p : ℝ × EuclideanSpace ℝ (Fin q) =>
            gaussHeat S G (S7PIH_rho a b p.1) p.2 + (p.1 - S7PIH_rho a b p.1) *
              S7PIH_Wphi (fun i j => A (S7PIH_rho a b p.1) i j) (gaussHeat S G (S7PIH_rho a b p.1)) p.2 := by
          funext p; rfl
        rw [h]
        exact hF0.add (hcτ.mul hWc)
      exact this.continuousOn
    · refine continuousOn_clm_apply.2 fun u => Continuous.continuousOn ?_
      have : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin q) =>
          iteratedFDeriv ℝ 1 (gaussHeat S G (S7PIH_rho a b p.1)) p.2 ![u] +
          (p.1 - S7PIH_rho a b p.1) * (-(1 / 2) * ∑ i, ∑ j, A (S7PIH_rho a b p.1) i j *
            iteratedFDeriv ℝ 3 (gaussHeat S G (S7PIH_rho a b p.1)) p.2
              (Fin.cons u ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]))) :=
        (hcit (j := 1) (by norm_num) _).add (hcτ.mul (continuous_const.mul
          (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
            (hcA i j).mul (hcit (j := 3) (by norm_num) _))))
      exact this.congr (fun p => (S7PIH_ext_fderiv hG p.1 p.2 u).symm)
    · refine continuousOn_clm_apply.2 fun v => continuousOn_clm_apply.2 fun u => Continuous.continuousOn ?_
      have : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin q) =>
          iteratedFDeriv ℝ 2 (gaussHeat S G (S7PIH_rho a b p.1)) p.2 ![v, u] +
          (p.1 - S7PIH_rho a b p.1) * (-(1 / 2) * ∑ i, ∑ j, A (S7PIH_rho a b p.1) i j *
            iteratedFDeriv ℝ 4 (gaussHeat S G (S7PIH_rho a b p.1)) p.2
              (Fin.cons v (Fin.cons u ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])))) :=
        (hcit (j := 2) (by norm_num) _).add (hcτ.mul (continuous_const.mul
          (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
            (hcA i j).mul (hcit (j := 4) (by norm_num) _))))
      exact this.congr (fun p => (S7PIH_ext_fderiv2 hG p.1 p.2 v u).symm)
    · intro x _ t ht
      rw [hd t ht x]
      exact (S7PIH_ext_hasDerivAt hab hA hApsd hSb hS hG x t).hasDerivWithinAt
    · refine hWc.continuousOn.congr (fun p hp => ?_)
      exact hd p.1 hp.1 p.2
  · intro r hr
    funext c
    simp [S7PIH_ext, S7PIH_rho_of_mem hr]
  · intro r hr c
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hr.1, hr.2.trans hb⟩
    rw [hd r hrT c, S7PIH_rho_of_mem hr]
    rfl

end HRS.MC.Sec7.S7PIH

end
