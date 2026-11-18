import HRS.Equilibrium.Parametrix.PX5AuxF
import HRS.Equilibrium.Parametrix.PX2AuxB

/-!
# Prop 4.13 parametrix, packet PX5: the local part `B_xψ` of the generator is integrable

Measurability of `Δ`, `∂_j` of arbitrary functions, the slice derivative bounds
(`|Δ_xψ|`, `|∂_xψ|` against the Hessian and gradient of `lift2 ψ`), and the integrability in `x`
of `Bop ψ(·, y)` for kernels with `Px5Bnds`.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

open HRS.PDE HRS.PDE.MFAux

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem px5_measurable_partialDeriv (j : Fin d) (g : Torus d → ℝ) :
    Measurable (Torus.partialDeriv j g) := by
  unfold Torus.partialDeriv
  have h := measurable_fderiv_apply_const ℝ (Torus.lift g) (EuclideanSpace.single j (1 : ℝ))
  exact h.comp (PDE.MFSchauder.measurable_rep' d)

theorem px5_measurable_laplacian (g : Torus d → ℝ) : Measurable (Torus.laplacian g) := by
  have h : Torus.laplacian g = fun x => ∑ j : Fin d, fderiv ℝ (fderiv ℝ (Torus.lift g)) (Torus.rep x)
      (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ j) := by
    funext x
    unfold Torus.laplacian
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift g)
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedFDeriv_two_apply]
    simp
  rw [h]
  refine Finset.measurable_sum _ fun j _ => ?_
  have h1 := measurable_fderiv_apply_const ℝ (fderiv ℝ (Torus.lift g))
    (EuclideanSpace.basisFun (Fin d) ℝ j)
  exact (h1.apply_continuousLinearMap _).comp (PDE.MFSchauder.measurable_rep' d)


theorem px5_lift_slice (ψ : Torus d → Torus d → ℝ) (y : Torus d) :
    Torus.lift (fun z => ψ z y) = fun w => lift2 ψ (w, Torus.rep y) := by
  funext w; simp [Torus.lift, lift2, Torus.mk_rep]

theorem px5_iter2_slice {Φ : Euc d × Euc d → ℝ} {U : Set (Euc d × Euc d)} (hU : IsOpen U)
    (hΦ : ContDiffOn ℝ 2 Φ U) (w c : Euc d) (hmem : (w, c) ∈ U) :
    iteratedFDeriv ℝ 2 (fun w' => Φ (w', c)) w =
      (iteratedFDeriv ℝ 2 Φ (w, c)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
  set Φ' : Euc d × Euc d → ℝ := fun p => Φ (p + ((0 : Euc d), c)) with hΦ'
  set U' : Set (Euc d × Euc d) := (fun p => p + ((0 : Euc d), c)) ⁻¹' U with hU'
  have hU'o : IsOpen U' := hU.preimage (continuous_id.add continuous_const)
  have hΦ'c : ContDiffOn ℝ 2 Φ' U' :=
    hΦ.comp (contDiff_id.add contDiff_const).contDiffOn (fun p hp => hp)
  have hfun : (fun w' => Φ (w', c)) = Φ' ∘ (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
    funext w'; simp [hΦ']
  have hx : (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) w ∈ U' := by
    show (w, (0 : Euc d)) + ((0 : Euc d), c) ∈ U
    simpa using hmem
  rw [hfun, iteratedFDeriv_comp_clm_of_open' hU'o hΦ'c _ hx (by norm_num)]
  have h2 : iteratedFDeriv ℝ 2 Φ' ((ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) w) =
      iteratedFDeriv ℝ 2 Φ (w, c) := by
    rw [hΦ', iteratedFDeriv_comp_add_right]
    congr 1
    simp
  rw [h2]

theorem px5_laplacian_slice_bound {ψ : Torus d → Torus d → ℝ}
    (hs : ContDiffOn ℝ 2 (lift2 ψ) (offDiag d)) {x y : Torus d} (hxy : x ≠ y) :
    |Torus.laplacian (fun z => ψ z y) x| ≤
      d * ‖iteratedFDeriv ℝ 2 (lift2 ψ) (Torus.rep x, Torus.rep y)‖ := by
  have hp : ((Torus.rep x, Torus.rep y) : Euc d × Euc d) ∈ offDiag d := by
    show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep y)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hxy
  unfold Torus.laplacian
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only []
  rw [px5_lift_slice, px5_iter2_slice isOpen_offDiag hs _ _ hp]
  refine (Finset.abs_sum_le_sum_abs _ Finset.univ).trans ?_
  calc ∑ j : Fin d, |((iteratedFDeriv ℝ 2 (lift2 ψ) (Torus.rep x, Torus.rep y)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
          ![(EuclideanSpace.basisFun (Fin d) ℝ) j, (EuclideanSpace.basisFun (Fin d) ℝ) j]|
      ≤ ∑ _j : Fin d, ‖iteratedFDeriv ℝ 2 (lift2 ψ) (Torus.rep x, Torus.rep y)‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, ← Real.norm_eq_abs]
        refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
        have : ∏ i : Fin 2, ‖(ContinuousLinearMap.inl ℝ (Euc d) (Euc d))
            (![(EuclideanSpace.basisFun (Fin d) ℝ) j, (EuclideanSpace.basisFun (Fin d) ℝ) j] i)‖ ≤ 1 := by
          have h1 : ∀ i : Fin 2, ‖(ContinuousLinearMap.inl ℝ (Euc d) (Euc d))
              (![(EuclideanSpace.basisFun (Fin d) ℝ) j, (EuclideanSpace.basisFun (Fin d) ℝ) j] i)‖ = 1 := by
            intro i
            fin_cases i <;> simp [Prod.norm_def]
          simp [h1]
        calc _ ≤ ‖iteratedFDeriv ℝ 2 (lift2 ψ) (Torus.rep x, Torus.rep y)‖ * 1 :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = _ := mul_one _
    _ = d * ‖iteratedFDeriv ℝ 2 (lift2 ψ) (Torus.rep x, Torus.rep y)‖ := by simp

theorem px5_partialDeriv_slice_bound {ψ : Torus d → Torus d → ℝ}
    (hs : ContDiffOn ℝ 2 (lift2 ψ) (offDiag d)) {x y : Torus d} (hxy : x ≠ y) (j : Fin d) :
    |Torus.partialDeriv j (fun z => ψ z y) x| ≤ ‖fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep y)‖ := by
  have hp : ((Torus.rep x, Torus.rep y) : Euc d × Euc d) ∈ offDiag d := by
    show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep y)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hxy
  have hd : DifferentiableAt ℝ (lift2 ψ) (Torus.rep x, Torus.rep y) :=
    (hs.contDiffAt (isOpen_offDiag.mem_nhds hp)).differentiableAt (by simp)
  unfold Torus.partialDeriv
  rw [px5_lift_slice]
  have h1 := hd.hasFDerivAt.comp (Torus.rep x) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (Torus.rep x) (Torus.rep y))
  rw [show (fun w => lift2 ψ (w, Torus.rep y)) = lift2 ψ ∘ (fun e => (e, Torus.rep y)) from rfl,
    h1.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ (lift2 ψ) _).le_opNorm _).trans ?_
  have : ‖(ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) (EuclideanSpace.single j (1 : ℝ))‖ ≤ 1 := by
    simp [Prod.norm_def]
  calc _ ≤ ‖fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep y)‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _


theorem px5_wEnv_integrable (H : ParxHyp d s V β ρ) (y : Torus d) :
    Integrable (fun x => wEnv s x y) (withDensityReal ρ) := by
  have hρ := H.rho_smooth
  obtain ⟨Rm, hRm⟩ := exists_density_bound hρ
  have hs0 := px5_s_pos H
  have hm : Measurable fun p : Torus d × Torus d => wEnv s p.1 p.2 := by
    unfold wEnv rTrunc
    exact measurable_const.add ((measurable_const.min LocalDivAux.measurable_eucDist).pow_const _)
  set g : ℝ → ℝ := fun t => 2 + t ^ (-s) with hg
  have hbd : ∀ x y : Torus d, |wEnv s x y| ≤ g (Torus.eucDist x y) := by
    intro x y
    rw [abs_of_nonneg (by linarith [px5_wEnv_ge_one s x y])]
    unfold wEnv rTrunc
    simp only [hg]
    have h0 : 0 ≤ Torus.eucDist x y ^ (-s) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    by_cases h1 : 1 ≤ Torus.eucDist x y
    · rw [min_eq_left h1, Real.one_rpow]; linarith
    · push Not at h1
      rw [min_eq_right h1.le]; linarith
  have hgi : IntegrableOn (fun w : Euc d => g ‖w‖) (LocalDivAux.cube d) := by
    have hc : (volume : Measure (Euc d)) (LocalDivAux.cube d) ≠ ⊤ := by
      have hcb : Bornology.IsBounded (LocalDivAux.cube d) :=
        (Metric.isBounded_closedBall (x := (0 : Euc d)) (r := (d : ℝ))).subset (fun w hw => by
          rw [mem_closedBall_zero_iff]; exact LocalDivAux.cube_norm_le hw)
      exact hcb.measure_lt_top.ne
    exact (integrableOn_const hc).add
      (LocalDivAux.integrableOn_cube_rpow (by have := H.two_le; omega) (a := s) H.s_lt)
  have := (LocalDivAux.kernel_int hρ hRm hm hbd hgi y).1
  have e : (fun x => wEnv s x y) = fun x => wEnv s y x := funext fun x => px5_wEnv_symm s x y
  rw [e]; exact this

theorem px5_eucDist_pos {x y : Torus d} (h : x ≠ y) : 0 < Torus.eucDist x y := by
  unfold Torus.eucDist
  apply Real.sqrt_pos.mpr
  by_contra hle
  push Not at hle
  apply h
  have h0 : ∀ i ∈ Finset.univ, ‖x i - y i‖ ^ 2 = 0 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ ‖x i - y i‖ ^ 2 := fun i _ => by positivity
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hle (Finset.sum_nonneg hnn))
  funext i
  have := h0 i (Finset.mem_univ i)
  have h2 : ‖x i - y i‖ = 0 := by simpa using this
  exact sub_eq_zero.mp (norm_eq_zero.mp h2)

/-- bound of the local generator on a kernel with `Px5Bnds` -/
theorem px5_Bop_bound (H : ParxHyp d s V β ρ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ {K : ℝ} {ψ : Torus d → Torus d → ℝ}, Px5Bnds s K ψ →
      ∀ x y : Torus d, x ≠ y →
        |Bop d s V β ρ (fun z => ψ z y) x| ≤ Cb * K * wEnv s x y := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hcont : Continuous (fun x => ∑ j, |Torus.partialDeriv j ρ x / ρ x|) := by
    refine continuous_finset_sum _ fun j _ => ?_
    have h1 := PDE.continuous_partialDeriv j ρ hρ1
    have h2 : Continuous ρ := PDE.MFAux.continuous_of_isCk hρ1
    exact (h1.div h2 (fun x => (hρ.pos x).ne')).abs
  obtain ⟨Mr, hMr⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  have hMr0 : 0 ≤ Mr := (norm_nonneg _).trans (hMr (0 : Torus d) (Set.mem_univ _))
  have hβ := H.beta_pos
  refine ⟨β⁻¹ * (d + Mr), by positivity, fun {K ψ} hψ x y hxy => ?_⟩
  have hp : ((Torus.rep x, Torus.rep y) : Euc d × Euc d) ∈ offDiag d := by
    show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep y)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hxy
  have hH := hψ.hess _ hp
  have hG := hψ.grad _ hp
  simp only [Torus.mk_rep] at hH hG
  have hr0 : 0 < rTrunc x y := lt_min zero_lt_one (px5_eucDist_pos hxy)
  have hr1 : rTrunc x y ≤ 1 := min_le_left _ _
  have hT1 : px5T s 1 (rTrunc x y) ≤ px5T s 2 (rTrunc x y) := by
    show 1 + rTrunc x y ^ (1 - s) ≤ 1 + rTrunc x y ^ (-s)
    have : rTrunc x y ^ (1 - s) ≤ rTrunc x y ^ (-s) :=
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
    linarith
  have hT2 : px5T s 2 (rTrunc x y) = wEnv s x y := rfl
  have hTpos : 0 < wEnv s x y := by linarith [px5_wEnv_ge_one s x y]
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg _).trans hH
    rw [hT2] at this
    exact nonneg_of_mul_nonneg_left this hTpos
  have hlap := px5_laplacian_slice_bound hψ.smooth2 hxy
  have hpd : ∀ j, |Torus.partialDeriv j (fun z => ψ z y) x| ≤ K * wEnv s x y := fun j =>
    (px5_partialDeriv_slice_bound hψ.smooth2 hxy j).trans (hG.trans
      (mul_le_mul_of_nonneg_left (hT1.trans_eq hT2) hK0))
  rw [px5_Bop_form H]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hβ)]
  refine (mul_le_mul_of_nonneg_left (abs_add_le _ _) (inv_pos.mpr hβ).le).trans ?_
  have hs1 : |∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j (fun z => ψ z y) x| ≤
      Mr * (K * wEnv s x y) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |(Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j (fun z => ψ z y) x|
        ≤ ∑ j, |Torus.partialDeriv j ρ x / ρ x| * (K * wEnv s x y) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hpd j) (abs_nonneg _)
      _ = (∑ j, |Torus.partialDeriv j ρ x / ρ x|) * (K * wEnv s x y) := by rw [Finset.sum_mul]
      _ ≤ Mr * (K * wEnv s x y) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := hMr x (Set.mem_univ _)
          rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)] at this
          exact this
  have hs2 : |Torus.laplacian (fun z => ψ z y) x| ≤ d * (K * wEnv s x y) := by
    refine hlap.trans ?_
    exact mul_le_mul_of_nonneg_left (hH.trans (by rw [hT2])) (Nat.cast_nonneg _)
  calc β⁻¹ * (|Torus.laplacian (fun z => ψ z y) x| +
        |∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j (fun z => ψ z y) x|)
      ≤ β⁻¹ * (d * (K * wEnv s x y) + Mr * (K * wEnv s x y)) :=
        mul_le_mul_of_nonneg_left (add_le_add hs2 hs1) (inv_pos.mpr hβ).le
    _ = β⁻¹ * (d + Mr) * K * wEnv s x y := by ring

theorem px5_Bop_integrable (H : ParxHyp d s V β ρ) {K : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hψ : Px5Bnds s K ψ) (y : Torus d) :
    Integrable (fun x => Bop d s V β ρ (fun z => ψ z y) x) (withDensityReal ρ) := by
  obtain ⟨Cb, hCb0, hCb⟩ := px5_Bop_bound H
  have hmeas : Measurable (fun x => Bop d s V β ρ (fun z => ψ z y) x) := by
    have e : (fun x => Bop d s V β ρ (fun z => ψ z y) x) = fun x => β⁻¹ *
        (Torus.laplacian (fun z => ψ z y) x +
          ∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j (fun z => ψ z y) x) :=
      funext fun x => px5_Bop_form H _ x
    rw [e]
    refine measurable_const.mul ((px5_measurable_laplacian _).add ?_)
    exact Finset.measurable_sum _ fun j _ =>
      ((px5_measurable_partialDeriv j ρ).div H.rho_smooth.density.measurable).mul
        (px5_measurable_partialDeriv j _)
  refine Integrable.mono' ((px5_wEnv_integrable H y).const_mul (Cb * K)) hmeas.aestronglyMeasurable ?_
  filter_upwards [px5_ae_ne (by have := H.two_le; omega) ρ y] with x hx
  rw [Real.norm_eq_abs]
  have := hCb hψ x y hx
  calc _ ≤ Cb * K * wEnv s x y := this
    _ = _ := by ring

end HRS.Parx

end
