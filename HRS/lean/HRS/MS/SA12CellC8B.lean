import HRS.MS.SA12CellC8A
import HRS.MS.UniqT3
import HRS.MP.RdInit

/-!
# S.A.12 C8 (part B): local boundedness of the jets of a classical solution and of its time derivative
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12y_opnorm_le_sum {j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ) :
    ‖A‖ ≤ ∑ idx : Fin j → Fin d, |A (fun l => EuclideanSpace.single (idx l) (1 : ℝ))| := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun m => ?_
  have hexp : ∀ l, m l = ∑ i : Fin d, (m l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    intro l
    ext k
    simp [Pi.single_apply]
  have h1 : A m = ∑ r : Fin j → Fin d, (∏ l, m l (r l)) * A (fun l => EuclideanSpace.single (r l) (1 : ℝ)) := by
    have := A.toMultilinearMap.map_sum (fun l (i : Fin d) => (m l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d))
    calc A m = A (fun l => ∑ i : Fin d, (m l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d)) := by
          congr 1; funext l; exact hexp l
      _ = _ := by
          rw [show (A (fun l => ∑ i : Fin d, (m l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d))) =
            A.toMultilinearMap (fun l => ∑ i : Fin d, (m l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d)) from rfl,
            this]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [A.toMultilinearMap.map_smul_univ]
          simp
  rw [h1, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [abs_mul]
  have h2 : |∏ l, m l (r l)| ≤ ∏ l, ‖m l‖ := by
    rw [← Real.norm_eq_abs, norm_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => ?_
    rw [Real.norm_eq_abs]
    exact PiLp.norm_apply_le (m l) (r l)
  calc _ ≤ (∏ l, ‖m l‖) * |A (fun l => EuclideanSpace.single (r l) (1 : ℝ))| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    _ = _ := mul_comm _ _

/-- Local boundedness of the jets of a family with jointly continuous partial derivatives. -/
theorem sa12y_jet_bound {t : ℝ} {F : ℝ → Euc d → ℝ}
    (hcont : ∀ j : ℕ, ∀ idx : Fin j → Fin d,
      ContinuousOn (fun p : ℝ × Euc d => partialDeriv idx (F p.1) p.2) (Icc 0 t ×ˢ univ))
    (n : ℕ) (R : ℝ) :
    ∃ K : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R → ‖iteratedFDeriv ℝ n (F τ) x‖ ≤ K := by
  have hS : IsCompact (Icc (0 : ℝ) t ×ˢ Metric.closedBall (0 : Euc d) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hg : ContinuousOn (fun p : ℝ × Euc d => ∑ idx : Fin n → Fin d, |partialDeriv idx (F p.1) p.2|)
      (Icc (0 : ℝ) t ×ˢ Metric.closedBall (0 : Euc d) R) :=
    continuousOn_finset_sum _ fun idx _ => ((hcont n idx).mono
      (prod_mono subset_rfl (subset_univ _))).abs
  obtain ⟨K, hK⟩ := hS.exists_bound_of_continuousOn hg
  refine ⟨K, fun τ hτ x hx => ?_⟩
  have h1 := hK (τ, x) ⟨hτ, by simpa using hx⟩
  refine (sa12y_opnorm_le_sum _).trans ?_
  have h2 : ∑ idx : Fin n → Fin d, |partialDeriv idx (F τ) x| ≤ K := by
    refine le_trans (le_abs_self _) ?_
    simpa [Real.norm_eq_abs] using h1
  exact h2

theorem sa12y_norm_D1 {h : Euc d → ℝ} (hh : ContDiff ℝ ∞ h) (i : Fin d) (n : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (HRS.MS.UniqT3.D1 i h) x‖ ≤ ‖iteratedFDeriv ℝ (n + 1) h x‖ := by
  have e : HRS.MS.UniqT3.D1 i h =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)) ∘ (fderiv ℝ h) := rfl
  rw [e]
  have hf : ContDiffAt ℝ ∞ (fderiv ℝ h) x := (hh.fderiv_right (m := ∞) (by simp)).contDiffAt
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hf (by exact_mod_cast le_top)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  have hL : ‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => by
      simpa using L.le_opNorm (EuclideanSpace.single i (1 : ℝ) : Euc d)
  exact mul_le_of_le_one_left (norm_nonneg _) hL

theorem sa12y_D1_contDiff {h : Euc d → ℝ} (hh : ContDiff ℝ ∞ h) (i : Fin d) :
    ContDiff ℝ ∞ (HRS.MS.UniqT3.D1 i h) :=
  (hh.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem sa12y_grad_contDiff {h : Euc d → ℝ} (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (gradient h) :=
  (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp (hh.fderiv_right (m := ∞) (by simp))

theorem sa12y_rate_bound {m : ℕ} {Cb T t ν : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb T b) {G F : ℝ → Euc d → ℝ} (hF : IsClassicalSol m ν b G t F)
    (htT : t ≤ T) (R : ℝ) (hR : 0 ≤ R) :
    ∀ j ≤ m, ∃ K : ℝ, ∀ idx : Fin j → Fin d, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R →
      |partialDeriv idx (fun y => ν * Laplacian.laplacian (F τ) y +
        inner ℝ (b τ y) (gradient (F τ) y) + G τ y) x| ≤ K := by
  intro j hj
  choose KF hKF using fun n => sa12y_jet_bound hF.contF n R
  obtain ⟨KG, hKG⟩ := sa12y_jet_bound hF.contG j R
  set Kmax : ℝ := ∑ n ∈ Finset.range (m + 3), |KF n| with hKmax
  have hKm : ∀ n ≤ m + 2, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ n (F τ) x‖ ≤ Kmax := by
    intro n hn τ hτ x hx
    refine (hKF n τ hτ x hx).trans ?_
    refine (le_abs_self _).trans ?_
    exact Finset.single_le_sum (f := fun n => |KF n|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  set Cbb : ℝ := |Cb| * (1 + R) + |Cb| with hCbb
  have hCbb0 : 0 ≤ Cbb := by rw [hCbb]; positivity
  set Bn : ℝ := ‖innerSL ℝ (E := Euc d)‖ with hBn
  refine ⟨|ν| * (d * Kmax) + Bn * (2 ^ m * (Cbb * Kmax)) + |KG|, fun idx τ hτ x hx => ?_⟩
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans htT⟩
  have hf : ContDiff ℝ ∞ (F τ) := (hF.smooth τ hτ).1
  have hg : ContDiff ℝ ∞ (G τ) := (hF.smooth τ hτ).2
  have hβ : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (b τ) := by exact_mod_cast hb.smooth τ hτT
  have hKm' : ∀ n ≤ m + 2, ‖iteratedFDeriv ℝ n (F τ) x‖ ≤ Kmax := fun n hn => hKm n hn τ hτ x hx
  have hKmnn : 0 ≤ Kmax := Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- the three pieces
  have hlap : (fun y => ν * Laplacian.laplacian (F τ) y) =
      fun y => ν • ∑ i : Fin d, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i (F τ)) y := by
    funext y
    rw [HRS.MS.UniqT3.lap_eq (hf.of_le (by simp)) y]
    rfl
  have hcd1 : ∀ i : Fin d, ContDiff ℝ ∞ (HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i (F τ))) := fun i =>
    sa12y_D1_contDiff (sa12y_D1_contDiff hf i) i
  have hcdΔ : ContDiff ℝ ∞ (fun y => ∑ i : Fin d, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i (F τ)) y) :=
    ContDiff.sum fun i _ => hcd1 i
  have hcdβg : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞)
      (fun y => innerSL ℝ (b τ y) (gradient (F τ) y)) := by
    have := hβ.inner ℝ ((sa12y_grad_contDiff hf).of_le (by exact_mod_cast le_top))
    simpa [innerSL_apply_apply] using this
  have h1 : ‖iteratedFDeriv ℝ j (fun y => ν * Laplacian.laplacian (F τ) y) x‖ ≤ |ν| * (d * Kmax) := by
    rw [hlap, iteratedFDeriv_const_smul_apply' (hcdΔ.contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, Real.norm_eq_abs, iteratedFDeriv_fun_sum_apply
        (fun i _ => (hcd1 i).contDiffAt.of_le (by exact_mod_cast le_top))]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin d, ‖iteratedFDeriv ℝ j (HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i (F τ))) x‖
        ≤ ∑ _i : Fin d, Kmax := Finset.sum_le_sum fun i _ => by
          refine (sa12y_norm_D1 (sa12y_D1_contDiff hf i) i j x).trans ?_
          refine (sa12y_norm_D1 hf i (j + 1) x).trans ?_
          exact hKm' (j + 1 + 1) (by omega)
      _ = d * Kmax := by simp
  have h2 : ‖iteratedFDeriv ℝ j (fun y => innerSL ℝ (b τ y) (gradient (F τ) y)) x‖ ≤
      Bn * (2 ^ m * (Cbb * Kmax)) := by
    have hbil := (innerSL ℝ (E := Euc d)).norm_iteratedFDeriv_le_of_bilinear (f := b τ)
      (g := gradient (F τ)) (N := ((m + 1 : ℕ) : WithTop ℕ∞)) hβ
      ((sa12y_grad_contDiff hf).of_le (by exact_mod_cast le_top)) x
      (n := j) (by exact_mod_cast (Nat.le_succ_of_le hj))
    refine hbil.trans (mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _))
    have hterm : ∀ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * ‖iteratedFDeriv ℝ k (b τ) x‖ *
        ‖iteratedFDeriv ℝ (j - k) (gradient (F τ)) x‖ ≤ (j.choose k : ℝ) * (Cbb * Kmax) := by
      intro k hk
      have hkj : k ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hbk : ‖iteratedFDeriv ℝ k (b τ) x‖ ≤ Cbb := by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [norm_iteratedFDeriv_zero]
          refine (hb.growth τ hτT x).trans ?_
          rw [hCbb]
          have : 1 + ‖x‖ ≤ 1 + R := by linarith
          nlinarith [le_abs_self Cb, abs_nonneg Cb, norm_nonneg x]
        · refine (hb.deriv_bdd τ hτT k hk0 (by omega) x).trans ?_
          rw [hCbb]
          nlinarith [le_abs_self Cb, abs_nonneg Cb]
      have hgk : ‖iteratedFDeriv ℝ (j - k) (gradient (F τ)) x‖ ≤ Kmax := by
        have e : gradient (F τ) = ((InnerProductSpace.toDual ℝ (Euc d)).symm : _ → _) ∘ (fderiv ℝ (F τ)) := rfl
        rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]
        exact hKm' (j - k + 1) (by omega)
      calc (j.choose k : ℝ) * ‖iteratedFDeriv ℝ k (b τ) x‖ * ‖iteratedFDeriv ℝ (j - k) (gradient (F τ)) x‖
          = (j.choose k : ℝ) * (‖iteratedFDeriv ℝ k (b τ) x‖ * ‖iteratedFDeriv ℝ (j - k) (gradient (F τ)) x‖) := by ring
        _ ≤ (j.choose k : ℝ) * (Cbb * Kmax) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hbk hgk (norm_nonneg _) hCbb0) (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hsum : ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) = 2 ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    rw [hsum]
    have : (2 : ℝ) ^ j ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hj
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h3 : ‖iteratedFDeriv ℝ j (G τ) x‖ ≤ |KG| := (hKG τ hτ x hx).trans (le_abs_self _)
  have hP : (fun y => ν * Laplacian.laplacian (F τ) y + inner ℝ (b τ y) (gradient (F τ) y) + G τ y) =
      ((fun y => ν * Laplacian.laplacian (F τ) y) + (fun y => innerSL ℝ (b τ y) (gradient (F τ) y))) + G τ := by
    funext y; simp [innerSL_apply_apply]
  have hcd1' : ContDiff ℝ j (fun y => ν * Laplacian.laplacian (F τ) y) := by
    rw [hlap]
    exact (hcdΔ.const_smul ν).of_le (by exact_mod_cast le_top)
  have hcd2' : ContDiff ℝ j (fun y => innerSL ℝ (b τ y) (gradient (F τ) y)) :=
    hcdβg.of_le (by exact_mod_cast Nat.le_succ_of_le hj)
  have hcd3' : ContDiff ℝ j (G τ) := hg.of_le (by exact_mod_cast le_top)
  have hsplit : iteratedFDeriv ℝ j (fun y => ν * Laplacian.laplacian (F τ) y +
      inner ℝ (b τ y) (gradient (F τ) y) + G τ y) x =
      iteratedFDeriv ℝ j (fun y => ν * Laplacian.laplacian (F τ) y) x +
      iteratedFDeriv ℝ j (fun y => innerSL ℝ (b τ y) (gradient (F τ) y)) x +
      iteratedFDeriv ℝ j (G τ) x := by
    rw [hP, iteratedFDeriv_add_apply
      (f := (fun y => ν * Laplacian.laplacian (F τ) y) + (fun y => innerSL ℝ (b τ y) (gradient (F τ) y)))
      (g := G τ) (hcd1'.add hcd2').contDiffAt hcd3'.contDiffAt,
      iteratedFDeriv_add_apply (f := fun y => ν * Laplacian.laplacian (F τ) y)
        (g := fun y => innerSL ℝ (b τ y) (gradient (F τ) y)) hcd1'.contDiffAt hcd2'.contDiffAt]
  refine (HRS.MP.RdInit.mri_abs_partialDeriv_le idx _ x).trans ?_
  rw [hsplit]
  refine (norm_add₃_le).trans ?_
  linarith [h1, h2, h3]

end HRS.MH.AdjointRd.Phase2SA12Construction
