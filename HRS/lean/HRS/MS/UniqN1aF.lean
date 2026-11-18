import HRS.MS.UniqN1aE

/-!
# N1a of `UniqPlan.md`, part (f): the local `L²` bound for the Hessian operator, `0 ≤ s < d - 2`

`n1a_hess_local`: for `ψ ∈ C²_c` with `supp ψ ⊆ B̄(c,ρ)`, `ρ ≥ 1`, and `B̄(c',r')` with `r' ≤ ρ`:
`‖1_{B̄(c',r')} ∂_j(g * ∂_iψ)‖_{L²} ≤ C ρ^{C₀} ‖ψ‖_{L²}`.
Route: `∂_j(g * ∂_iψ) = g * ∂_j∂_iψ = (∂_i∂_j g) * ψ` (`n1a_hess_repr`), near/far split of the kernel
`|∂_i∂_j g(z)| ≤ C ‖z‖^{-s-2}` (Young `L¹ * L²` on `|z| ≤ 5ρ` when `|c - c'| ≤ 3ρ`, the bound `C` and
Cauchy-Schwarz otherwise), as in `screened_local_lt_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN1a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0
  HRS.MH.Screened

variable {d : ℕ}

/-- The identification `∂_j (g * ∂_iψ) = (∂_i∂_j g) * ψ`. -/
theorem n1a_D1_kcd (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i j : Fin d) (y : Euc d) :
    D1 j (kernelConvDeriv d s i ψ) y =
      ∫ x, q09_DH s j (y - x) (EuclideanSpace.single i 1) * ψ x := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 (by linarith : s < (d : ℝ))
  have hK : kernelConvDeriv d s i ψ = HRS.Whole.convFun (rieszKernel d s) (D1 i ψ) := rfl
  rw [hK, convFun_D1 hl (D1_contDiff hψ i) (D1_supp hψc i) j y]
  exact n1a_hess_repr hd hs0 hsd hψ hψc i j y

theorem n1a_w_aesm (s : ℝ) (i j : Fin d) {v : Euc d → ℝ} (hv : AEStronglyMeasurable v volume) :
    AEStronglyMeasurable
      (fun x => ∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * v y) volume := by
  have h1 : Measurable (fun p : Euc d × Euc d =>
      q09_DH s j (p.1 - p.2) (EuclideanSpace.single i 1)) :=
    (n1a_DH_meas s i j).comp (measurable_fst.sub measurable_snd)
  have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => v p.2) (volume.prod volume) :=
    hv.comp_snd
  exact (h1.aestronglyMeasurable.mul h2).integral_prod_right'

theorem n1a_hess_local (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C₀ C : ℝ, ∀ (i j : Fin d) (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (ψ : Euc d → ℝ),
      ContDiff ℝ 2 ψ → HasCompactSupport ψ → Function.support ψ ⊆ closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
        eLpNorm ((closedBall c' r').indicator (fun y => D1 j (kernelConvDeriv d s i ψ) y)) 2 volume ≤
          ENNReal.ofReal (C * ρ ^ C₀) * eLpNorm ψ 2 volume := by
  obtain ⟨CN, hCN0, hCN⟩ := n1a_kernel_trunc hd hs0 hsd
  set V1r : ℝ := (volume (closedBall (0 : Euc d) 1)).toReal with hV1r
  have hV1r0 : 0 ≤ V1r := ENNReal.toReal_nonneg
  set m : ℝ := max 1 s * (s + 3) with hm
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
    positivity
  refine ⟨(d : ℝ), CN + m * V1r, fun i j ρ hρ c ψ hψ hψc hsupp c' r' hr' => ?_⟩
  have hρ0 : 0 ≤ ρ := by linarith
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hψL2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hvae : AEStronglyMeasurable ψ volume := hψm.aestronglyMeasurable
  set Nv := eLpNorm ψ 2 volume with hNv
  have hNv2 : Nv ^ 2 = ∫⁻ x, ‖ψ x‖ₑ ^ 2 := l1_sq_eLpNorm_ae ψ hvae
  have hfun : (fun y => D1 j (kernelConvDeriv d s i ψ) y) =
      fun x => ∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y :=
    funext fun y => n1a_D1_kcd hd hs0 hsd hψ hψc i j y
  rw [hfun]
  have hwae := n1a_w_aesm s i j hvae
  have hind : AEStronglyMeasurable ((closedBall c' r').indicator
      (fun x => ∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y)) volume :=
    hwae.indicator measurableSet_closedBall
  have hρd : 0 ≤ ρ ^ (d : ℝ) := Real.rpow_nonneg hρ0 _
  suffices hsq : (eLpNorm ((closedBall c' r').indicator
      (fun x => ∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y)) 2 volume) ^ 2 ≤
      (ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ)) * Nv) ^ 2 by
    exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq
  rw [l1_sq_eLpNorm_ae _ hind]
  by_cases hnear : dist c' c ≤ 3 * ρ
  · -- near case: truncated kernel and Young
    set k : Euc d → ℝ≥0∞ := fun u => ‖(closedBall (0 : Euc d) (5 * ρ)).indicator
      (fun u => q09_DH s j u (EuclideanSpace.single i 1)) u‖ₑ with hk
    have hkm : Measurable k :=
      (Measurable.indicator (n1a_DH_meas s i j) measurableSet_closedBall).enorm
    have hkI : ∫⁻ u, k u ≤ ENNReal.ofReal (CN * ρ ^ (d : ℝ)) := hCN i j ρ hρ
    have hk1 : ∫⁻ u, k u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkI
    set G : Euc d → ℝ≥0∞ := fun x => ∫⁻ y, k (x - y) * ‖ψ y‖ₑ with hG
    have hpt : ∀ x, ‖(closedBall c' r').indicator
        (fun x => ∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y) x‖ₑ ≤ G x := by
      intro x
      by_cases hx : x ∈ closedBall c' r'
      · rw [Set.indicator_of_mem hx]
        have hxd : dist x c' ≤ ρ := le_trans (mem_closedBall.1 hx) hr'
        calc ‖∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y‖ₑ
            ≤ ∫⁻ y, ‖q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y‖ₑ :=
              enorm_integral_le_lintegral_enorm _
          _ = ∫⁻ y, k (x - y) * ‖ψ y‖ₑ := by
              refine lintegral_congr fun y => ?_
              by_cases hv0 : ψ y = 0
              · simp [hv0]
              · have hyB : y ∈ closedBall c ρ := hsupp (Function.mem_support.2 hv0)
                have hcy : dist c y ≤ ρ := by
                  rw [dist_comm]; exact mem_closedBall.1 hyB
                have hxy : ‖x - y‖ ≤ 5 * ρ := by
                  rw [← dist_eq_norm]
                  linarith [dist_triangle4 x c' c y]
                have hmem5 : x - y ∈ closedBall (0 : Euc d) (5 * ρ) :=
                  mem_closedBall_zero_iff.2 hxy
                simp only [hk]
                rw [Set.indicator_of_mem hmem5, enorm_mul]
      · rw [Set.indicator_of_notMem hx]
        simp
    have hYoung := young_l1_l2_proof k (fun y => ‖ψ y‖ₑ) hkm hψm.enorm hk1
    have hsq1 : ∫⁻ x, ‖(closedBall c' r').indicator
        (fun x => ∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y) x‖ₑ ^ 2 ≤
        ∫⁻ x, G x ^ 2 :=
      lintegral_mono fun x => pow_le_pow_left₀ ((by positivity)) (hpt x) 2
    have hYle : ENNReal.ofReal (CN * ρ ^ (d : ℝ)) ≤
        ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ)) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hm0 hV1r0)) hρd)
    calc ∫⁻ x, ‖(closedBall c' r').indicator
          (fun x => ∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y) x‖ₑ ^ 2
        ≤ ∫⁻ x, G x ^ 2 := hsq1
      _ ≤ (∫⁻ y, k y) ^ 2 * ∫⁻ y, ‖ψ y‖ₑ ^ 2 := hYoung
      _ = (∫⁻ y, k y) ^ 2 * Nv ^ 2 := by rw [hNv2]
      _ ≤ (ENNReal.ofReal (CN * ρ ^ (d : ℝ)) * Nv) ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ((by positivity)) hkI 2)
            ((by positivity))
      _ ≤ (ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ)) * Nv) ^ 2 :=
          pow_le_pow_left₀ ((by positivity)) (mul_le_mul_of_nonneg_right hYle ((by positivity))) 2
  · -- far case: the kernel is bounded by `m`
    have hnear' : 3 * ρ < dist c' c := not_le.mp hnear
    set X : ℝ≥0∞ := ENNReal.ofReal (ρ ^ (d : ℝ) * V1r) with hX
    have hvolB : volume (closedBall c ρ) ≤ X := l1_vol_closedBall_le c le_rfl hρ0
    have hvolB' : volume (closedBall c' r') ≤ X := l1_vol_closedBall_le c' hr' hρ0
    have hm_pt : ∀ x ∈ closedBall c' r', ∀ y,
        ‖q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y‖ₑ ≤
          ENNReal.ofReal m * ‖ψ y‖ₑ := by
      intro x hx y
      by_cases hv0 : ψ y = 0
      · simp [hv0]
      · have hyB : y ∈ closedBall c ρ := hsupp (Function.mem_support.2 hv0)
        have hxd : dist x c' ≤ ρ := le_trans (mem_closedBall.1 hx) hr'
        have hyd : dist y c ≤ ρ := mem_closedBall.1 hyB
        have h1 : ρ < ‖x - y‖ := by
          rw [← dist_eq_norm]
          have h3 := dist_triangle4 c' x y c
          rw [dist_comm c' x] at h3
          linarith
        have hge : 1 ≤ ‖x - y‖ := by linarith
        have hne : x - y ≠ 0 := by
          intro h
          rw [h, norm_zero] at hge
          linarith
        have hK := n0_qDH_bound hs0 j i hne
        have hpow : ‖x - y‖ ^ (-s - 2) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hge (by linarith)
        have hKle : ‖q09_DH s j (x - y) (EuclideanSpace.single i 1)‖ ≤ m := by
          rw [Real.norm_eq_abs]
          calc |q09_DH s j (x - y) (EuclideanSpace.single i 1)|
              ≤ max 1 s * (s + 3) * ‖x - y‖ ^ (-s - 2) := hK
            _ ≤ max 1 s * (s + 3) * 1 :=
                mul_le_mul_of_nonneg_left hpow (by
                  have : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
                  positivity)
            _ = m := mul_one _
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hm0]
        apply ENNReal.ofReal_le_ofReal
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hKle (norm_nonneg _)
    have hwb : ∀ x ∈ closedBall c' r',
        ‖∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y‖ₑ ≤
          ENNReal.ofReal m * ∫⁻ y, ‖ψ y‖ₑ := by
      intro x hx
      calc ‖∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y‖ₑ
          ≤ ∫⁻ y, ‖q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y‖ₑ :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ y, ENNReal.ofReal m * ‖ψ y‖ₑ := lintegral_mono fun y => hm_pt x hx y
        _ = ENNReal.ofReal m * ∫⁻ y, ‖ψ y‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hsq2 : ∫⁻ x, ‖(closedBall c' r').indicator
        (fun x => ∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y) x‖ₑ ^ 2 ≤
        ∫⁻ x, (closedBall c' r').indicator
          (fun _ : Euc d => (ENNReal.ofReal m * ∫⁻ y, ‖ψ y‖ₑ) ^ 2) x := by
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ closedBall c' r'
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        exact pow_le_pow_left₀ ((by positivity)) (hwb x hx) 2
      · simp [Set.indicator_of_notMem hx]
    rw [lintegral_indicator_const measurableSet_closedBall] at hsq2
    have hL1 : (∫⁻ y, ‖ψ y‖ₑ) ^ 2 ≤ volume (closedBall c ρ) * Nv ^ 2 := by
      rw [hNv2]
      exact l1_holder hvae measurableSet_closedBall hsupp
    have hYle : ENNReal.ofReal m * X ≤ ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ)) := by
      rw [hX, ← ENNReal.ofReal_mul hm0]
      apply ENNReal.ofReal_le_ofReal
      have e1 : (CN + m * V1r) * ρ ^ (d : ℝ) = CN * ρ ^ (d : ℝ) + m * (ρ ^ (d : ℝ) * V1r) := by ring
      rw [e1]
      linarith [mul_nonneg hCN0 hρd]
    calc ∫⁻ x, ‖(closedBall c' r').indicator
          (fun x => ∫ y, q09_DH s j (x - y) (EuclideanSpace.single i 1) * ψ y) x‖ₑ ^ 2
        ≤ (ENNReal.ofReal m * ∫⁻ y, ‖ψ y‖ₑ) ^ 2 * volume (closedBall c' r') := hsq2
      _ = ENNReal.ofReal m ^ 2 * (∫⁻ y, ‖ψ y‖ₑ) ^ 2 * volume (closedBall c' r') := by ring
      _ ≤ ENNReal.ofReal m ^ 2 * (volume (closedBall c ρ) * Nv ^ 2) * X := by
          gcongr
      _ ≤ ENNReal.ofReal m ^ 2 * (X * Nv ^ 2) * X := by
          gcongr
      _ = (ENNReal.ofReal m * X) ^ 2 * Nv ^ 2 := by ring
      _ ≤ (ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ)) * Nv) ^ 2 := by
          rw [mul_pow (ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ))) Nv]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hYle 2) (by positivity)

end HRS.MS.UniqN1a
