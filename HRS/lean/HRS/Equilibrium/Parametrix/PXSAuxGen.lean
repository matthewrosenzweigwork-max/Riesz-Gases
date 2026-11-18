import HRS.Equilibrium.Parametrix.PXSAuxGlue
import HRS.PDE.MeanFieldPairInverse
import HRS.Equilibrium.Parametrix.PX1AuxExtApply

/-!
# Packet PXS: continuity and slice bounds for the generator of a `C²` pair kernel
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

open HRS.PDE HRS.PDE.MFAux

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

/-- Jets of the slice `x' ↦ Ψ x' (mk v)` of `Lop`. -/
theorem pxS_Lop_slice_mk {ρ : Torus d → ℝ} (hρ1 : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x)
    {Ψ : Torus d → Torus d → ℝ} (hΨ : IsCk2 2 Ψ) (u v : Euc d) :
    Lop ρ (fun x' => Ψ x' (Torus.mk v)) (Torus.mk u) =
      -(∑ j : Fin d, (iteratedFDeriv ℝ 2 (PDE.lift2 Ψ) (u, v))
          ![ContinuousLinearMap.inl ℝ (Euc d) (Euc d) (EuclideanSpace.single j 1),
            ContinuousLinearMap.inl ℝ (Euc d) (Euc d) (EuclideanSpace.single j 1)]) -
      ∑ j : Fin d, (Torus.partialDeriv j ρ (Torus.mk u) / ρ (Torus.mk u)) *
        (iteratedFDeriv ℝ 1 (PDE.lift2 Ψ) (u, v))
          ![ContinuousLinearMap.inl ℝ (Euc d) (Euc d) (EuclideanSpace.single j 1)] := by
  have hf : Torus.IsCk 2 (fun x' => Ψ x' (Torus.mk v)) := by
    have := MFPair.isCk_slice 2 Ψ hΨ (Torus.mk v)
    exact this
  have hG : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (PDE.lift2 Ψ) := hΨ
  have hl : Torus.lift (fun x' => Ψ x' (Torus.mk v)) = fun u' => PDE.lift2 Ψ (u', v) := rfl
  rw [MFPair.Lop_eq hρ1 hpos hf (Torus.mk u), ClassicalAux.laplacian_mk _ hf u, hl,
    MFPair.iteratedFDeriv_partial_left (PDE.lift2 Ψ) hG (by norm_num : 2 ≤ 2) u v]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [partialDeriv_mk j _ (hf.of_le (by norm_num)) u, hl]
    have h1 : fderiv ℝ (fun u' => PDE.lift2 Ψ (u', v)) u (EuclideanSpace.single j 1) =
        iteratedFDeriv ℝ 1 (fun u' => PDE.lift2 Ψ (u', v)) u ![EuclideanSpace.single j 1] := by
      rw [iteratedFDeriv_one_apply]; rfl
    rw [h1, MFPair.iteratedFDeriv_partial_left (PDE.lift2 Ψ) hG (by norm_num : 1 ≤ 2) u v]
    simp

theorem pxS_Lop_pair_continuous {ρ : Torus d → ℝ} (hρ1 : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x)
    {Ψ : Torus d → Torus d → ℝ} (hΨ : IsCk2 2 Ψ) :
    Continuous (fun p : Torus d × Torus d => Lop ρ (fun x' => Ψ x' p.2) p.1) := by
  have hG : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (PDE.lift2 Ψ) := hΨ
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  have hc2 : Continuous (fun p : Euc d × Euc d => iteratedFDeriv ℝ 2 (PDE.lift2 Ψ) p) :=
    hG.continuous_iteratedFDeriv (by norm_num)
  have hc1 : Continuous (fun p : Euc d × Euc d => iteratedFDeriv ℝ 1 (PDE.lift2 Ψ) p) :=
    hG.continuous_iteratedFDeriv (by norm_num)
  refine MFPair.continuous_pair_of_continuous_lift2 (Φ := fun x y => Lop ρ (fun x' => Ψ x' y) x) ?_
  have e : PDE.lift2 (fun x y => Lop ρ (fun x' => Ψ x' y) x) = fun p : Euc d × Euc d =>
      -(∑ j : Fin d, (iteratedFDeriv ℝ 2 (PDE.lift2 Ψ) p)
          ![ContinuousLinearMap.inl ℝ (Euc d) (Euc d) (EuclideanSpace.single j 1),
            ContinuousLinearMap.inl ℝ (Euc d) (Euc d) (EuclideanSpace.single j 1)]) -
      ∑ j : Fin d, (Torus.partialDeriv j ρ (Torus.mk p.1) / ρ (Torus.mk p.1)) *
        (iteratedFDeriv ℝ 1 (PDE.lift2 Ψ) p)
          ![ContinuousLinearMap.inl ℝ (Euc d) (Euc d) (EuclideanSpace.single j 1)] := by
    funext p
    exact pxS_Lop_slice_mk hρ1 hpos hΨ p.1 p.2
  rw [e]
  refine (continuous_finsetSum _ fun j _ => ?_).neg.sub (continuous_finsetSum _ fun j _ => ?_)
  · exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d × Euc d) ℝ _).continuous.comp hc2
  · refine Continuous.mul ?_ ?_
    · exact ((continuous_partialDeriv j ρ hρ1).comp (Torus.continuous_mk.comp continuous_fst)).div
        (hρc.comp (Torus.continuous_mk.comp continuous_fst)) fun p => (hpos _).ne'
    · exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d × Euc d) ℝ _).continuous.comp hc1

/-- Parametric convolution with an integrable kernel is jointly continuous. -/
theorem pxS_continuous_conv_pair {g : Torus d → ℝ} (hg : Integrable g)
    {W : Torus d × Torus d → ℝ} (hW : Continuous W) :
    Continuous (fun p : Torus d × Torus d => convFun g (fun u => W (u, p.2)) p.1) := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn hW.continuousOn
  have e : (fun p : Torus d × Torus d => convFun g (fun u => W (u, p.2)) p.1) =
      fun p => ∫ z, g z * W (p.1 - z, p.2) := by
    funext p
    unfold convFun
    rw [← integral_sub_left_eq_self (fun z => g z * W (p.1 - z, p.2)) volume p.1]
    simp
  rw [e]
  refine continuous_of_dominated (bound := fun z => ‖g z‖ * B) (fun p => ?_) (fun p => ?_)
    (hg.norm.mul_const B) (Filter.Eventually.of_forall fun z => ?_)
  · exact hg.aestronglyMeasurable.mul
      (hW.comp ((continuous_const.sub continuous_id).prodMk continuous_const)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _ (Set.mem_univ _)) (norm_nonneg _)
  · exact continuous_const.mul (hW.comp (((continuous_fst.sub continuous_const)).prodMk continuous_snd))

/-- `∑_j ∂_j(ρ ∂_j f) = -ρ L f`. -/
theorem pxS_Dh_eq {ρ : Torus d → ℝ} (hρ1 : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x)
    {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (u : Torus d) :
    ∑ j, Torus.partialDeriv j (fun y' => ρ y' * Torus.partialDeriv j f y') u = -(ρ u * Lop ρ f u) := by
  have : Lop ρ f u = -(ρ u)⁻¹ * ∑ j, Torus.partialDeriv j
      (fun y' => ρ y' * Torus.partialDeriv j f y') u := by
    unfold Lop
    rw [MFAux.div_smul_grad ρ f hρ1 hf u]
  rw [this]
  have := (hpos u).ne'
  field_simp

/-- The kernel of `projGen` of the first-variable slices, before centring. -/
def pxS_K (d : ℕ) (β : ℝ) (ρ : Torus d → ℝ) (g : Torus d → ℝ) (Ψ : Torus d → Torus d → ℝ)
    (x y : Torus d) : ℝ :=
  -(β⁻¹ * Lop ρ (fun x' => Ψ x' y) x) +
    convFun g (fun u => -(ρ u * Lop ρ (fun x' => Ψ x' y) u)) x

theorem pxS_projGen_slice (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ} (hΨ : IsCk2 2 Ψ)
    (x y : Torus d) :
    projGen d s V β ρ (fun x' => Ψ x' y) x =
      pxS_K d β ρ (periodicRiesz d s) Ψ x y - ∫ z, ρ z * pxS_K d β ρ (periodicRiesz d s) Ψ z y := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hd1 : 1 ≤ d := le_trans (by norm_num) H.two_le
  have hf : Torus.IsCk 2 (fun x' => Ψ x' y) := MFPair.isCk_slice 2 Ψ hΨ y
  have hK : ∀ z, Bop d s V β ρ (fun x' => Ψ x' y) z + Jop d s ρ (fun x' => Ψ x' y) z =
      pxS_K d β ρ (periodicRiesz d s) Ψ z y := by
    intro z
    rw [pxS_Bop_eq H hf z, pxS_Jop_eq hd1 H.s_nonneg H.s_lt hρ1 hf z]
    unfold pxS_K
    congr 1
    congr 1
    funext u
    exact pxS_Dh_eq hρ1 hρ.pos hf u
  unfold projGen projMean
  rw [MFAdjoint.pair_mu hρ.density]
  simp only [hK]

theorem pxS_K_continuous (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ} (hΨ : IsCk2 2 Ψ) :
    Continuous (fun p : Torus d × Torus d => pxS_K d β ρ (periodicRiesz d s) Ψ p.1 p.2) := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  have hd1 : 1 ≤ d := le_trans (by norm_num) H.two_le
  have hg := MFOneLe.integrable_periodicRiesz hd1 s H.s_nonneg H.s_lt
  have hL := pxS_Lop_pair_continuous hρ1 hρ.pos hΨ
  unfold pxS_K
  refine (continuous_const.mul hL).neg.add ?_
  exact pxS_continuous_conv_pair hg (W := fun p => -(ρ p.1 * Lop ρ (fun x' => Ψ x' p.2) p.1))
    ((hρc.comp continuous_fst).mul hL).neg

theorem pxS_projGen_slice_continuous (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ}
    (hΨ : IsCk2 2 Ψ) :
    Continuous (fun p : Torus d × Torus d => projGen d s V β ρ (fun x' => Ψ x' p.2) p.1) := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  have hKc := pxS_K_continuous H hΨ
  have e : (fun p : Torus d × Torus d => projGen d s V β ρ (fun x' => Ψ x' p.2) p.1) =
      fun p => pxS_K d β ρ (periodicRiesz d s) Ψ p.1 p.2 -
        ∫ z, ρ z * pxS_K d β ρ (periodicRiesz d s) Ψ z p.2 := by
    funext p
    exact pxS_projGen_slice H hΨ p.1 p.2
  rw [e]
  refine hKc.sub ?_
  have h2 : Continuous (fun y : Torus d => ∫ z in Set.univ, ρ z *
      pxS_K d β ρ (periodicRiesz d s) Ψ z y ∂(volume : Measure (Torus d))) :=
    continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
      (f := fun y z => ρ z * pxS_K d β ρ (periodicRiesz d s) Ψ z y)
      ((hρc.comp continuous_snd).mul (hKc.comp (continuous_snd.prodMk continuous_fst)))
      isCompact_univ
  have h3 : Continuous (fun y : Torus d => ∫ z, ρ z * pxS_K d β ρ (periodicRiesz d s) Ψ z y) := by
    simpa using h2
  exact h3.comp continuous_snd

theorem pxS_isCk2_swap {Ψ : Torus d → Torus d → ℝ} (n : ℕ) (hΨ : IsCk2 n Ψ) :
    IsCk2 n (fun a b => Ψ b a) := by
  unfold IsCk2 at hΨ ⊢
  have : PDE.lift2 (fun a b => Ψ b a) = PDE.lift2 Ψ ∘ Prod.swap := rfl
  rw [this]
  exact hΨ.comp (contDiff_snd.prodMk contDiff_fst)

theorem pxS_pairGen_continuous (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ}
    (hΨ : IsCk2 2 Ψ) :
    Continuous (fun p : Torus d × Torus d => projGen d s V β ρ (fun x' => Ψ x' p.2) p.1 +
      projGen d s V β ρ (fun y' => Ψ p.1 y') p.2) := by
  have h1 := pxS_projGen_slice_continuous H hΨ
  have h2 := pxS_projGen_slice_continuous H (pxS_isCk2_swap 2 hΨ)
  have h2' : Continuous (fun p : Torus d × Torus d => projGen d s V β ρ (fun y' => Ψ p.1 y') p.2) :=
    by
    have h3 := h2.comp (continuous_snd.prodMk continuous_fst)
    simpa only [Function.comp_def] using h3
  exact Continuous.add h1 h2'

theorem pxS_pairGen_diag (hd : 0 < d) (H : ParxHyp d s V β ρ) {Ψ R : Torus d → Torus d → ℝ}
    (hΨ : IsCk2 2 Ψ) (hR : Continuous (fun p : Torus d × Torus d => R p.1 p.2))
    (h : ∀ x y, x ≠ y → projGen d s V β ρ (fun x' => Ψ x' y) x +
      projGen d s V β ρ (fun y' => Ψ x y') y = R x y) (x y : Torus d) :
    projGen d s V β ρ (fun x' => Ψ x' y) x + projGen d s V β ρ (fun y' => Ψ x y') y = R x y := by
  have hT : Continuous (fun p : Torus d × Torus d => (projGen d s V β ρ (fun x' => Ψ x' p.2) p.1 +
      projGen d s V β ρ (fun y' => Ψ p.1 y') p.2) - R p.1 p.2) :=
    (pxS_pairGen_continuous H hΨ).sub hR
  have hE : Continuous (fun p : Euc d × Euc d =>
      (projGen d s V β ρ (fun x' => Ψ x' (Torus.mk p.2)) (Torus.mk p.1) +
      projGen d s V β ρ (fun y' => Ψ (Torus.mk p.1) y') (Torus.mk p.2)) -
        R (Torus.mk p.1) (Torus.mk p.2)) :=
    by
    have h4 : Continuous (fun p : Euc d × Euc d => ((Torus.mk p.1, Torus.mk p.2) : Torus d × Torus d)) :=
      (Torus.continuous_mk.comp continuous_fst).prodMk (Torus.continuous_mk.comp continuous_snd)
    have h5 := hT.comp h4
    simpa only [Function.comp_def] using h5
  have hz : (fun p : Euc d × Euc d =>
      (projGen d s V β ρ (fun x' => Ψ x' (Torus.mk p.2)) (Torus.mk p.1) +
      projGen d s V β ρ (fun y' => Ψ (Torus.mk p.1) y') (Torus.mk p.2)) -
        R (Torus.mk p.1) (Torus.mk p.2)) = fun _ => 0 :=
    Continuous.ext_on (dense_offDiag hd) hE continuous_const (fun p hp => by
      have hne : Torus.mk p.1 ≠ Torus.mk p.2 := hp
      show _ = (0 : ℝ)
      rw [h _ _ hne, sub_self])
  have := congrFun hz (Torus.rep x, Torus.rep y)
  simp only [Torus.mk_rep] at this
  linarith

/-! ### Changing a function at one point does not change the generator elsewhere -/

theorem pxS_lift_eventuallyEq {f f' : Torus d → ℝ} {y : Torus d}
    (h : ∀ z, z ≠ y → f z = f' z) (u : Euc d) (hu : Torus.mk u ≠ y) :
    Torus.lift f =ᶠ[𝓝 u] Torus.lift f' := by
  have ho : IsOpen {v : Euc d | Torus.mk v ≠ y} :=
    (isOpen_compl_singleton (x := y)).preimage Torus.continuous_mk
  filter_upwards [ho.mem_nhds hu] with v hv
  exact h _ hv

theorem pxS_partialDeriv_congr {f f' : Torus d → ℝ} {y : Torus d}
    (h : ∀ z, z ≠ y → f z = f' z) (j : Fin d) (z : Torus d) (hz : z ≠ y) :
    Torus.partialDeriv j f z = Torus.partialDeriv j f' z := by
  unfold Torus.partialDeriv
  rw [(pxS_lift_eventuallyEq h (Torus.rep z) (by rwa [Torus.mk_rep])).fderiv_eq]

theorem pxS_Bop_congr {f f' : Torus d → ℝ} {y : Torus d}
    (h : ∀ z, z ≠ y → f z = f' z) (z : Torus d) (hz : z ≠ y) :
    Bop d s V β ρ f z = Bop d s V β ρ f' z := by
  have hev := pxS_lift_eventuallyEq h (Torus.rep z) (by rwa [Torus.mk_rep])
  unfold Bop Torus.laplacian Torus.grad
  have h2 := (hev.iteratedFDeriv ℝ 2).eq_of_nhds
  rw [hev.gradient_eq, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ), InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [h2]

theorem pxS_Jop_congr (hd : 0 < d) {f f' : Torus d → ℝ} {y : Torus d}
    (h : ∀ z, z ≠ y → f z = f' z) (z : Torus d) :
    Jop d s ρ f z = Jop d s ρ f' z := by
  have hae : ∀ᵐ w : Torus d, w ≠ y := by
    have := (measure_eq_zero_iff_ae_notMem (μ := (volume : Measure (Torus d))) (s := {y})).1
      (volume_singleton_torus hd y)
    filter_upwards [this] with w hw using hw
  have e : ∀ j : Fin d, convFun (periodicRiesz d s) (fun y' => ρ y' * Torus.partialDeriv j f y') =
      convFun (periodicRiesz d s) (fun y' => ρ y' * Torus.partialDeriv j f' y') := by
    intro j
    funext z'
    unfold convFun
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw
    rw [pxS_partialDeriv_congr h j w hw]
  unfold Jop
  simp only [e]

theorem pxS_projGen_congr (hd : 0 < d) {f f' : Torus d → ℝ} {y : Torus d}
    (h : ∀ z, z ≠ y → f z = f' z) (x : Torus d) (hx : x ≠ y) :
    projGen d s V β ρ f x = projGen d s V β ρ f' x := by
  have hae : ∀ᵐ w ∂(withDensityReal ρ), w ≠ y := by
    have h0 : (withDensityReal ρ) {y} = 0 :=
      withDensity_absolutelyContinuous _ _ (volume_singleton_torus hd y)
    have := (measure_eq_zero_iff_ae_notMem (μ := withDensityReal ρ) (s := {y})).1 h0
    filter_upwards [this] with w hw using hw
  unfold projGen projMean pair
  simp only []
  rw [pxS_Bop_congr h x hx, pxS_Jop_congr hd h x]
  have hint : ∫ w, (Bop d s V β ρ f w + Jop d s ρ f w) ∂(withDensityReal ρ) =
      ∫ w, (Bop d s V β ρ f' w + Jop d s ρ f' w) ∂(withDensityReal ρ) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw
    rw [pxS_Bop_congr h w hw, pxS_Jop_congr hd h w]
  rw [hint]

end HRS.Parx

end
