import HRS.MS.SA12K22

/-!
# S.A.12 L8 (SA12X3): `sa12k_L8_of_nonlocal` with a free lower bound `Lmin` for the period
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MS.ToriConv

variable {d : ℕ}

set_option maxHeartbeats 4000000 in
theorem sa12x3n_L8_of_nonlocal (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (Λ' ΛV' Cb L₀ : ℝ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (γ : ℝ → Euc d → ℝ) (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ)
    (hA : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL) (Lmin : ℝ) (hLmin : max 1 L₀ ≤ Lmin)
    (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ)
    (N1 : ∃ c : ℝ, 0 ≤ c ∧ ∀ L : ℝ, Lmin ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 →
      ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d,
        |(centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x| ≤
          c * jbracket x ^ (-((d : ℝ) + 3)))
    (N2 : ∀ (R δ : ℝ), 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R →
        |(centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x -
          nonlocalTestRd (D.coeff μ) (t - σ) ψ x| ≤ δ) :
    (∃ K : ℝ, ∀ L : ℝ, Lmin ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 → ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (weakOpPer L (γ L) D.M D.invβ (μL L ε)
        (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ) ≤
          ENNReal.ofReal K) ∧
    ∀ δ : ℝ, 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (fun x => weakOpPer L (γ L) D.M D.invβ (μL L ε)
        (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ x -
          weakOp (D.coeff μ) t σ ψ x) ≤ ENNReal.ofReal δ := by
  obtain ⟨cN, hcN, hN1⟩ := N1
  have hν0 : 0 ≤ D.invβ ∧ D.invβ ≤ νbar := hD.hν
  have hνb : |D.invβ| ≤ νbar := by rw [abs_of_nonneg hν0.1]; exact hν0.2
  have hνbar : 0 ≤ νbar := hν0.1.trans hν0.2
  obtain ⟨R, A, hR, hA0, hjet, hvan⟩ := sa12k_psi_data hψ
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by simp)
  have hψd : ∀ x, DifferentiableAt ℝ ψ x := fun x => (hψ2.differentiable (by norm_num)) x
  have hσT : ∀ σ ∈ Icc (0 : ℝ) t, σ ∈ Icc (0 : ℝ) T := fun σ hσ => ⟨hσ.1, hσ.2.trans ht.2⟩
  -- properties of the periodic drifts
  have hbL : ∀ L : ℝ, Lmin ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 → ∀ σ ∈ Icc (0 : ℝ) t,
      ContDiff ℝ 1 (HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ) (VL L ε)) ∧
      (∀ x, ‖HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ) (VL L ε) x‖ ≤
        Cb * (1 + ‖x‖)) ∧
      (∀ x, ‖fderiv ℝ (HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ) (VL L ε)) x‖ ≤ Cb) := by
    intro L hL ε hε σ hσ
    have h := (hA.1 L (hLmin.trans hL) ε hε).b_drift
    refine ⟨(h.smooth σ (hσT σ hσ)).of_le (by exact_mod_cast (by omega : 1 ≤ m + 1)),
      h.growth σ (hσT σ hσ), fun x => ?_⟩
    have := h.deriv_bdd σ (hσT σ hσ) 1 le_rfl (by omega) x
    rwa [norm_iteratedFDeriv_one] at this
  have hCb : 0 ≤ Cb := by
    have := (hbL Lmin le_rfl 1 ⟨one_pos, le_rfl⟩ 0 ⟨le_rfl, ht.1.le⟩).2.1 0
    simp at this
    exact (norm_nonneg _).trans this
  obtain ⟨cl, hcl, hloc⟩ := sa12k_loc_decay hψ νbar Cb hνbar hCb
  obtain ⟨cL, hcL, hlim⟩ := sa12k_hldec hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD t ht ψ hψ
  refine sa12k_L8_of_pointwise hd t (Lmin)
    (fun L ε σ x => weakOpPer L (γ L) D.M D.invβ (μL L ε)
      (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ x)
    (fun σ x => weakOp (D.coeff μ) t σ ψ x) ⟨cl + cN, by positivity, ?_⟩ ⟨cL, hcL, hlim⟩ ?_
  · intro L hL ε hε σ hσ x
    obtain ⟨hb1, hb2, hb3⟩ := hbL L hL ε hε σ hσ
    have h1 := hloc hνb hb1 hb2 hb3 x
    have h2 := hN1 L hL ε hε σ hσ x
    show |D.invβ * Laplacian.laplacian ψ x -
      movDiv (fun y => ψ y • HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ) (VL L ε) y) x -
        (centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x| ≤ _
    calc _ ≤ |D.invβ * Laplacian.laplacian ψ x -
        movDiv (fun y => ψ y • HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ) (VL L ε) y) x| +
        |(centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x| := abs_sub _ _
      _ ≤ _ := by nlinarith
  · intro R δ hδ
    -- the drift part
    set δ' : ℝ := (δ / 2) / (2 * d * A + 1) with hδ'
    have hδ'pos : 0 < δ' := by positivity
    obtain ⟨L₁a, ε₀a, hε₀a, ha⟩ := hA.2 (Metric.closedBall (0 : Euc d) R) (isCompact_closedBall _ _) 0
      (by omega) δ' hδ'pos
    obtain ⟨L₁b, ε₀b, hε₀b, hb⟩ := hA.2 (Metric.closedBall (0 : Euc d) R) (isCompact_closedBall _ _) 1
      (by omega) δ' hδ'pos
    obtain ⟨L₁c, ε₀c, hε₀c, hc⟩ := N2 R (δ / 2) (by positivity)
    refine ⟨max (max L₁a L₁b) (max L₁c Lmin), min (min (min ε₀a ε₀b) ε₀c) 1,
      lt_min (lt_min (lt_min hε₀a hε₀b) hε₀c) one_pos, fun L hL ε hε hεle σ hσ x hx => ?_⟩
    have hLa : L₁a ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
    have hLb : L₁b ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
    have hLc : L₁c ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
    have hL1 : Lmin ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
    have hεa : ε ≤ ε₀a := hεle.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
    have hεb : ε ≤ ε₀b := hεle.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
    have hεc : ε ≤ ε₀c := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hεI : ε ∈ Ioc (0 : ℝ) 1 := ⟨hε, hεle.trans (min_le_right _ _)⟩
    have hmax : max (t - σ) 0 = t - σ := max_eq_left (by linarith [hσ.2])
    have hxK : x ∈ Metric.closedBall (0 : Euc d) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hx
    obtain ⟨hb1, hb2, hb3⟩ := hbL L hL1 ε hεI σ hσ
    have hbLd : DifferentiableAt ℝ
        (HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ) (VL L ε)) x :=
      (hb1.differentiable (by norm_num)) x
    have hbd : DifferentiableAt ℝ ((D.coeff μ).drift (t - σ)) x :=
      sa12k_limit_drift_diff hA hm ht hσ x
    have e0 := (ha L hLa ε hε hεa σ (hσT σ hσ) x hxK).1
    have e1 := (hb L hLb ε hε hεb σ (hσT σ hσ) x hxK).1
    rw [hmax] at e0 e1
    rw [tcv_iter_zero_sub_norm] at e0
    rw [sa12k_norm_one_sub] at e1
    have hdiff := sa12k_movDiv_diff (hψd x) hbLd hbd
    have j1 : ‖fderiv ℝ ψ x‖ ≤ A := by
      have := hjet 1 (by norm_num) x; rwa [norm_iteratedFDeriv_one] at this
    have j0 : |ψ x| ≤ A := by
      have := hjet 0 (by norm_num) x; rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have hmd : |movDiv (fun y => ψ y • HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ)
        (VL L ε) y) x - movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y) x| ≤ δ / 2 := by
      refine hdiff.trans ?_
      have h3 : ‖fderiv ℝ ψ x‖ * ‖HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ) (VL L ε) x -
          (D.coeff μ).drift (t - σ) x‖ + |ψ x| * ‖fderiv ℝ
            (HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ) (VL L ε)) x -
          fderiv ℝ ((D.coeff μ).drift (t - σ)) x‖ ≤ 2 * A * δ' := by
        have := add_le_add (mul_le_mul j1 e0 (norm_nonneg _) hA0) (mul_le_mul j0 e1 (norm_nonneg _) hA0)
        linarith
      calc (d : ℝ) * _ ≤ d * (2 * A * δ') := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d)
        _ ≤ δ / 2 := by
          rw [hδ']
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          rw [show (d : ℝ) * (2 * A * ((δ / 2) / (2 * d * A + 1))) =
            (δ / 2) * ((2 * d * A) / (2 * d * A + 1)) by field_simp]
          have : (2 * d * A) / (2 * d * A + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ δ / 2) (sub_nonneg.2 this)]
    have hnl := hc L hLc ε hε hεc σ hσ x hx
    show |D.invβ * Laplacian.laplacian ψ x -
      movDiv (fun y => ψ y • HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ) (VL L ε) y) x -
        (centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x -
      ((D.coeff μ).ν * Laplacian.laplacian ψ x -
        movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y) x -
          nonlocalTestRd (D.coeff μ) (t - σ) ψ x)| ≤ δ
    have hν : (D.coeff μ).ν = D.invβ := rfl
    rw [hν]
    calc _ = |-(movDiv (fun y => ψ y • HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ)
          (VL L ε) y) x - movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y) x) -
        ((centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x -
          nonlocalTestRd (D.coeff μ) (t - σ) ψ x)| := by congr 1; ring
      _ ≤ |movDiv (fun y => ψ y • HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε σ)
          (VL L ε) y) x - movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y) x| +
        |(centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x -
          nonlocalTestRd (D.coeff μ) (t - σ) ψ x| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_neg]
      _ ≤ δ := by linarith

end HRS.MH.AdjointRd.Phase2SA12Limit
