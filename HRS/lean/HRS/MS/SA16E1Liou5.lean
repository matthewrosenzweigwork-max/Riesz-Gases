import HRS.MS.SA16E1Liou4

/-!
# S.A.16 E1: Liouville's formula for `M τ v = v - ∫_0^τ A s (M s v) ds`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution

section Liou

variable {d : ℕ} {T L : ℝ} {A M : ℝ → Euc d →L[ℝ] Euc d}

theorem e1_entry_aci (hT : 0 ≤ T) (hA : ∀ s ∈ Icc (0:ℝ) T, ‖A s‖ ≤ L)
    (hAm : ∀ v : Euc d, AEStronglyMeasurable (fun s => A s v) (volume.restrict (Icc (0:ℝ) T)))
    (hMc : ∀ v : Euc d, ContinuousOn (fun s => M s v) (Icc (0:ℝ) T))
    (hM : ∀ τ ∈ Icc (0:ℝ) T, ∀ v : Euc d, M τ v = v - ∫ s in (0:ℝ)..τ, A s (M s v))
    (i j : Fin d) :
    AbsolutelyContinuousOnInterval (fun s => e1N M s i j) 0 T := by
  obtain ⟨K, hK⟩ := e1_M_lip hT hA hAm hMc hM (EuclideanSpace.single j (1:ℝ))
  refine LipschitzOnWith.absolutelyContinuousOnInterval (K := K) ?_
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have h := hK.dist_le_mul x hx y hy
  rw [dist_eq_norm] at h
  rw [Real.dist_eq]
  refine le_trans ?_ h
  have := PiLp.norm_apply_le (M x (EuclideanSpace.single j (1:ℝ)) - M y (EuclideanSpace.single j (1:ℝ))) i
  simpa [e1N] using this

theorem e1_exp_aci {c : ℝ → ℝ} {T : ℝ} (hc : IntervalIntegrable c volume 0 T) :
    AbsolutelyContinuousOnInterval (fun s => Real.exp (∫ r in (0:ℝ)..s, c r)) 0 T := by
  have hI := hc.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  obtain ⟨R, hR⟩ := isCompact_uIcc.exists_bound_of_continuousOn hI.continuousOn
  obtain ⟨K, hK⟩ := (Real.contDiff_exp (n := 1)).contDiffOn.exists_lipschitzOnWith (by decide)
    (convex_Icc (-(|R|)) |R|) isCompact_Icc
  have := hK.comp_absolutelyContinuousOnInterval (g := fun s => ∫ r in (0:ℝ)..s, c r)
    (a := 0) (b := T) (fun s hs => by
      have := hR s hs
      rw [Real.norm_eq_abs] at this
      exact ⟨by linarith [abs_nonneg R, neg_abs_le (∫ r in (0:ℝ)..s, c r), le_abs_self R],
        by linarith [le_abs_self (∫ r in (0:ℝ)..s, c r), le_abs_self R]⟩) hI
  exact this

theorem e1_liouville (hT : 0 ≤ T) (hA : ∀ s ∈ Icc (0:ℝ) T, ‖A s‖ ≤ L)
    (hAm : ∀ v : Euc d, AEStronglyMeasurable (fun s => A s v) (volume.restrict (Icc (0:ℝ) T)))
    (hMc : ∀ v : Euc d, ContinuousOn (fun s => M s v) (Icc (0:ℝ) T))
    (hM : ∀ τ ∈ Icc (0:ℝ) T, ∀ v : Euc d, M τ v = v - ∫ s in (0:ℝ)..τ, A s (M s v))
    (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) T) :
    (e1N M τ).det = Real.exp (-∫ s in (0:ℝ)..τ, ∑ i, A s (EuclideanSpace.single i (1:ℝ)) i) := by
  classical
  have hcint := e1_c_int hT hA hAm
  have hFint := e1_F_int hT hA hAm hMc
  have hdet := e1_aci_det (e1N M) (fun i j => e1_entry_aci hT hA hAm hMc hM i j)
  have hexp := e1_exp_aci hcint
  have hu := hdet.fun_mul hexp
  have hae : ∀ᵐ x : ℝ, x ∈ uIcc 0 T → HasDerivAt
      (fun s => (e1N M s).det * Real.exp (∫ r in (0:ℝ)..s, ∑ i, A r (EuclideanSpace.single i (1:ℝ)) i))
      0 x := by
    have h1 : ∀ j : Fin d, ∀ᵐ x : ℝ, x ∈ uIcc 0 T → ∀ c' ∈ uIcc (0:ℝ) T,
        HasDerivAt (fun y => ∫ t in c'..y, A t (M t (EuclideanSpace.single j (1:ℝ))))
          (A x (M x (EuclideanSpace.single j (1:ℝ)))) x := fun j =>
      (hFint (EuclideanSpace.single j (1:ℝ))).ae_hasDerivAt_integral
    have h2 := hcint.ae_hasDerivAt_integral
    have h3 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have h4 : ∀ᵐ x : ℝ, x ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_all_iff.2 h1, h2, h3, h4] with x hx1 hx2 hx3 hx4 hxI
    have hxm : x ∈ Ioo 0 T := by
      rw [uIcc_of_le hT] at hxI
      exact ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx3), lt_of_le_of_ne hxI.2 hx4⟩
    have hd := e1_det_deriv hM hxm (fun j => hx1 j hxI 0 left_mem_uIcc)
    have hI := hx2 hxI 0 left_mem_uIcc
    have := hd.mul hI.exp
    convert this using 1
    ring
  obtain ⟨C, hC⟩ := hu.const_of_ae_hasDerivAt_zero hae
  have h0 : (e1N M 0).det = 1 := by
    have : e1N M 0 = 1 := by
      ext i j
      have := hM 0 ⟨le_rfl, hT⟩ (EuclideanSpace.single j (1:ℝ))
      simp only [intervalIntegral.integral_same, sub_zero] at this
      simp only [e1N, Matrix.of_apply, this, Matrix.one_apply]
      simp
    rw [this]; simp
  have hC0 := hC 0 left_mem_uIcc
  have hCτ := hC τ (by rw [uIcc_of_le hT]; exact hτ)
  simp only [intervalIntegral.integral_same, Real.exp_zero, mul_one, h0] at hC0
  rw [← hC0] at hCτ
  rw [Real.exp_neg]
  exact eq_inv_of_mul_eq_one_left hCτ

end Liou

end HRS.Whole.AppendixA.Phase2SA16Evolution
