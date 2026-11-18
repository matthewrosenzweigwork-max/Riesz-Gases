import HRS.Equilibrium.Parametrix.PXSAuxGen
import HRS.Energy.Coercivity
import HRS.Duality.PairingExpansion

/-!
# Packet PXS: `jpair_smooth` (canonicity and bound of `𝒥Ψ` for a doubly centred `C²` kernel)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

/-- Differentiation under the integral sign in the first variable of a periodic `C¹` function:
if the `ν`-mean of `G(w, ·)` vanishes for all `w`, so does that of `D_a G(w, ·)`. -/
theorem pxS_dui (ν : Measure (Torus d)) [IsFiniteMeasure ν] (G : Euc d × Euc d → ℝ)
    (hG : ContDiff ℝ 1 G) {C0 C1 : ℝ} (hb0 : ∀ p, |G p| ≤ C0) (hb1 : ∀ p, ‖fderiv ℝ G p‖ ≤ C1)
    (h0 : ∀ w, ∫ y, G (w, Torus.rep y) ∂ν = 0) (w a : Euc d) :
    ∫ y, fderiv ℝ G (w, Torus.rep y) (a, 0) ∂ν = 0 := by
  have hrep : Measurable (Torus.rep : Torus d → Euc d) := PDE.MFSchauder.measurable_rep' d
  have hGc : Continuous G := hG.continuous
  have hdiff : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hfc : Continuous (fun p => fderiv ℝ G p) := hG.continuous_fderiv (by norm_num)
  set F : ℝ → Torus d → ℝ := fun t y => G (w + t • a, Torus.rep y) with hF
  set F' : ℝ → Torus d → ℝ := fun t y => fderiv ℝ G (w + t • a, Torus.rep y) (a, 0) with hF'
  have hmeasF : ∀ t, AEStronglyMeasurable (F t) ν := fun t =>
    (hGc.measurable.comp (measurable_const.prodMk hrep)).aestronglyMeasurable
  have hmeasF' : ∀ t, AEStronglyMeasurable (F' t) ν := fun t => by
    have : Continuous (fun p : Euc d × Euc d => fderiv ℝ G p (a, 0)) := hfc.clm_apply continuous_const
    exact (this.measurable.comp (measurable_const.prodMk hrep)).aestronglyMeasurable
  have hint : Integrable (F 0) ν :=
    Integrable.of_bound (hmeasF 0) C0 (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb0 _)
  have hbound : ∀ y, ∀ t ∈ (Set.univ : Set ℝ), ‖F' t y‖ ≤ C1 * ‖(a, (0 : Euc d))‖ := by
    intro y t _
    rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact ((fderiv ℝ G _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb1 _) (norm_nonneg _))
  have hd : ∀ y, ∀ t ∈ (Set.univ : Set ℝ), HasDerivAt (fun t => F t y) (F' t y) t := by
    intro y t _
    have h1 : HasDerivAt (fun t : ℝ => ((w + t • a, Torus.rep y) : Euc d × Euc d)) ((a, (0 : Euc d))) t :=
      by
        have := (((hasDerivAt_id t).smul_const a).const_add w).prodMk (hasDerivAt_const t (Torus.rep y))
        simpa using this
    exact (hdiff (w + t • a, Torus.rep y)).hasFDerivAt.comp_hasDerivAt t h1
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F')
    (x₀ := 0) (s := Set.univ) Filter.univ_mem (Filter.Eventually.of_forall hmeasF) hint (hmeasF' 0)
    (Filter.Eventually.of_forall hbound) (integrable_const _) (Filter.Eventually.of_forall hd)
  have hz : (fun t : ℝ => ∫ y, F t y ∂ν) = fun _ => 0 := funext fun t => h0 _
  rw [hz] at hderiv
  have := hderiv.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  simpa [hF'] using this

theorem pxS_dui2 (ν : Measure (Torus d)) [IsFiniteMeasure ν] (G : Euc d × Euc d → ℝ)
    (hG : ContDiff ℝ 2 G) {C : ℝ} (hb : ∀ i ≤ 2, ∀ p, ‖iteratedFDeriv ℝ i G p‖ ≤ C)
    (h0 : ∀ w, ∫ y, G (w, Torus.rep y) ∂ν = 0) (w a : Euc d) :
    ∫ y, fderiv ℝ G (w, Torus.rep y) (a, 0) ∂ν = 0 ∧
    ∫ y, fderiv ℝ (fderiv ℝ G) (w, Torus.rep y) (a, 0) (a, 0) ∂ν = 0 := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hb0 : ∀ p, |G p| ≤ C := fun p => by
    have := hb 0 (by norm_num) p
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hb1 : ∀ p, ‖fderiv ℝ G p‖ ≤ C := fun p => by
    have := hb 1 (by norm_num) p
    rwa [norm_iteratedFDeriv_one] at this
  have hb2 : ∀ p, ‖fderiv ℝ (fderiv ℝ G) p‖ ≤ C := fun p => by
    have := hb 2 (by norm_num) p
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
  have h1 : ∀ w a, ∫ y, fderiv ℝ G (w, Torus.rep y) (a, 0) ∂ν = 0 :=
    fun w a => pxS_dui ν G hG1 hb0 hb1 h0 w a
  refine ⟨h1 w a, ?_⟩
  set v : Euc d × Euc d := (a, 0) with hv
  set G' : Euc d × Euc d → ℝ := fun p => fderiv ℝ G p v with hG'
  have hfd : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hG'c : ContDiff ℝ 1 G' := hfd.clm_apply contDiff_const
  have hfd_diff : Differentiable ℝ (fderiv ℝ G) := hfd.differentiable (by norm_num)
  have hderiv : ∀ p b, fderiv ℝ G' p b = fderiv ℝ (fderiv ℝ G) p b v := by
    intro p b
    have : HasFDerivAt G' ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ G) p)) p :=
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp p (hfd_diff p).hasFDerivAt
    rw [this.fderiv]
    simp
  have hb0' : ∀ p, |G' p| ≤ C * ‖v‖ := fun p => by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ G p).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hb1 p) (norm_nonneg _))
  have hb1' : ∀ p, ‖fderiv ℝ G' p‖ ≤ C * ‖v‖ := fun p => by
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg ((norm_nonneg _).trans (hb1 p)) (norm_nonneg _))
      fun b => ?_
    rw [hderiv]
    calc ‖fderiv ℝ (fderiv ℝ G) p b v‖ ≤ ‖fderiv ℝ (fderiv ℝ G) p b‖ * ‖v‖ :=
          (fderiv ℝ (fderiv ℝ G) p b).le_opNorm v
      _ ≤ (‖fderiv ℝ (fderiv ℝ G) p‖ * ‖b‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ G) p).le_opNorm b) (norm_nonneg _)
      _ ≤ (C * ‖b‖) * ‖v‖ := by gcongr; exact hb2 p
      _ = C * ‖v‖ * ‖b‖ := by ring
  have := pxS_dui ν G' hG'c hb0' hb1' (fun w' => h1 w' a) w a
  simpa [hderiv] using this

theorem pxS_int_bdd (ν : Measure (Torus d)) [IsFiniteMeasure ν] {Q : Euc d × Euc d → ℝ}
    (hQ : Continuous Q) {M : ℝ} (hM : ∀ p, |Q p| ≤ M) (w : Euc d) :
    Integrable (fun y => Q (w, Torus.rep y)) ν := by
  have hrep : Measurable (Torus.rep : Torus d → Euc d) := PDE.MFSchauder.measurable_rep' d
  exact Integrable.of_bound ((hQ.measurable.comp (measurable_const.prodMk hrep)).aestronglyMeasurable) M
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _)

/-- The `μ`-mean (in the second variable) of `L_ρ` of the first-variable slices vanishes for a kernel
with vanishing row means. -/
theorem pxS_Lop_mean (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ} (hΨ : PDE.IsCk2 2 Ψ)
    (hc : ∀ x, pair (withDensityReal ρ) (fun y => Ψ x y) = 0) (u : Torus d) :
    ∫ y, Lop ρ (fun x' => Ψ x' y) u ∂(withDensityReal ρ) = 0 := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have : IsProbabilityMeasure (withDensityReal ρ) := PDE.MFSemigroup.isProb_withDensityReal hρ.density
  set G : Euc d × Euc d → ℝ := PDE.lift2 Ψ with hGdef
  have hG : ContDiff ℝ 2 G := by
    have : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) G := hΨ
    simpa using this
  have hb : ∀ i ≤ 2, ∀ p, ‖iteratedFDeriv ℝ i G p‖ ≤ PDE.cbNorm2 2 Ψ :=
    fun i hi p => PDE.MFPair.norm_iteratedFDeriv_le_cbNorm2 hΨ hi p
  set C := PDE.cbNorm2 2 Ψ with hC
  have h0 : ∀ w, ∫ y, G (w, Torus.rep y) ∂(withDensityReal ρ) = 0 := by
    intro w
    have := hc (Torus.mk w)
    unfold pair at this
    simpa [hGdef, PDE.lift2, Torus.mk_rep] using this
  have hfd : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hfc : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  have hfdc : Continuous (fderiv ℝ (fderiv ℝ G)) := hfd.continuous_fderiv one_ne_zero
  have hb1 : ∀ p, ‖fderiv ℝ G p‖ ≤ C := fun p => by
    have := hb 1 (by norm_num) p
    rwa [norm_iteratedFDeriv_one] at this
  have hb2 : ∀ p, ‖fderiv ℝ (fderiv ℝ G) p‖ ≤ C := fun p => by
    have := hb 2 (by norm_num) p
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
  set ũ := Torus.rep u with hũ
  set c : Fin d → ℝ := fun j => Torus.partialDeriv j ρ u / ρ u with hcdef
  set a : Fin d → Euc d × Euc d := fun j => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)
    (EuclideanSpace.single j 1) with hadef
  have hint1 : ∀ j, Integrable (fun y => fderiv ℝ G (ũ, Torus.rep y) (a j)) (withDensityReal ρ) := by
    intro j
    refine pxS_int_bdd _ (Q := fun p => fderiv ℝ G p (a j)) (hfc.clm_apply continuous_const)
      (M := C * ‖a j‖) (fun p => ?_) ũ
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ G p).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb1 p) (norm_nonneg _))
  have hint2 : ∀ j, Integrable (fun y => fderiv ℝ (fderiv ℝ G) (ũ, Torus.rep y) (a j) (a j))
      (withDensityReal ρ) := by
    intro j
    refine pxS_int_bdd _ (Q := fun p => fderiv ℝ (fderiv ℝ G) p (a j) (a j))
      ((hfdc.clm_apply continuous_const).clm_apply continuous_const) (M := C * ‖a j‖ * ‖a j‖)
      (fun p => ?_) ũ
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (fderiv ℝ G) p (a j) (a j)‖ ≤ ‖fderiv ℝ (fderiv ℝ G) p (a j)‖ * ‖a j‖ :=
          (fderiv ℝ (fderiv ℝ G) p (a j)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ G) p‖ * ‖a j‖) * ‖a j‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ G) p).le_opNorm _) (norm_nonneg _)
      _ ≤ (C * ‖a j‖) * ‖a j‖ := by gcongr; exact hb2 p
  have hrw : ∀ y, Lop ρ (fun x' => Ψ x' y) u =
      -(∑ j, fderiv ℝ (fderiv ℝ G) (ũ, Torus.rep y) (a j) (a j)) -
        ∑ j, c j * fderiv ℝ G (ũ, Torus.rep y) (a j) := by
    intro y
    have h := pxS_Lop_slice_mk hρ1 hρ.pos hΨ ũ (Torus.rep y)
    rw [Torus.mk_rep, Torus.mk_rep] at h
    rw [h]
    have e1 : ∑ j : Fin d, (iteratedFDeriv ℝ 2 (PDE.lift2 Ψ) (ũ, Torus.rep y))
        ![ContinuousLinearMap.inl ℝ (Euc d) (Euc d) (EuclideanSpace.single j 1),
          ContinuousLinearMap.inl ℝ (Euc d) (Euc d) (EuclideanSpace.single j 1)] =
        ∑ j : Fin d, fderiv ℝ (fderiv ℝ G) (ũ, Torus.rep y) (a j) (a j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iteratedFDeriv_two_apply]
      rfl
    have e2 : ∑ j : Fin d, (Torus.partialDeriv j ρ u / ρ u) *
        (iteratedFDeriv ℝ 1 (PDE.lift2 Ψ) (ũ, Torus.rep y))
          ![ContinuousLinearMap.inl ℝ (Euc d) (Euc d) (EuclideanSpace.single j 1)] =
        ∑ j : Fin d, c j * fderiv ℝ G (ũ, Torus.rep y) (a j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iteratedFDeriv_one_apply]
      rfl
    rw [e1, e2]
  simp_rw [hrw]
  rw [integral_sub, integral_neg, integral_finsetSum _ (fun j _ => hint2 j),
    integral_finsetSum _ (fun j _ => (hint1 j).const_mul (c j))]
  · have k1 : ∀ j : Fin d, ∫ y, fderiv ℝ G (ũ, Torus.rep y) (a j) ∂(withDensityReal ρ) = 0 :=
      fun j => (pxS_dui2 _ G hG (C := C) hb h0 ũ (EuclideanSpace.single j 1)).1
    have k2 : ∀ j : Fin d, ∫ y, fderiv ℝ (fderiv ℝ G) (ũ, Torus.rep y) (a j) (a j)
        ∂(withDensityReal ρ) = 0 :=
      fun j => (pxS_dui2 _ G hG (C := C) hb h0 ũ (EuclideanSpace.single j 1)).2
    have e1 : ∀ j : Fin d, ∫ y, c j * fderiv ℝ G (ũ, Torus.rep y) (a j) ∂(withDensityReal ρ) = 0 :=
      fun j => by rw [integral_const_mul, k1 j, mul_zero]
    simp [k2, e1]
  · exact (integrable_finsetSum _ fun j _ => hint2 j).neg
  · exact integrable_finsetSum _ fun j _ => (hint1 j).const_mul (c j)

/-- The integrand `u ↦ -ρ(u) L_ρ(Ψ(·,y))(u)` of the nonlocal term. -/
def pxS_W (ρ : Torus d → ℝ) (Ψ : Torus d → Torus d → ℝ) (p : Torus d × Torus d) : ℝ :=
  -(ρ p.1 * Lop ρ (fun x' => Ψ x' p.2) p.1)

theorem pxS_Jop_slice (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ} (hΨ : PDE.IsCk2 2 Ψ)
    (y z : Torus d) :
    Jop d s ρ (fun w => Ψ w y) z =
      convFun (periodicRiesz d s) (fun u => pxS_W ρ Ψ (u, y)) z := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hd1 : 1 ≤ d := le_trans (by norm_num) H.two_le
  have hf : Torus.IsCk 2 (fun x' => Ψ x' y) := PDE.MFPair.isCk_slice 2 Ψ hΨ y
  rw [pxS_Jop_eq hd1 H.s_nonneg H.s_lt hρ1 hf z]
  congr 1
  funext u
  exact pxS_Dh_eq hρ1 hρ.pos hf u

theorem pxS_W_continuous (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ}
    (hΨ : PDE.IsCk2 2 Ψ) : Continuous (pxS_W ρ Ψ) := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := PDE.MFAux.continuous_of_isCk hρ1
  exact ((hρc.comp continuous_fst).mul (pxS_Lop_pair_continuous hρ1 hρ.pos hΨ)).neg

/-- Rows of `𝒥` have vanishing `μ`-mean after the first-variable slices: `∫ J(Ψ(·,y))(z) μ(dy) = 0`. -/
theorem pxS_Jop_mean (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ} (hΨ : PDE.IsCk2 2 Ψ)
    (hc : ∀ x, pair (withDensityReal ρ) (fun y => Ψ x y) = 0) (z : Torus d) :
    ∫ y, Jop d s ρ (fun w => Ψ w y) z ∂(withDensityReal ρ) = 0 := by
  have hρ := H.rho_smooth
  have hd1 : 1 ≤ d := le_trans (by norm_num) H.two_le
  have : IsProbabilityMeasure (withDensityReal ρ) := PDE.MFSemigroup.isProb_withDensityReal hρ.density
  have hg := PDE.MFOneLe.integrable_periodicRiesz hd1 s H.s_nonneg H.s_lt
  have hgm : Measurable (periodicRiesz d s) :=
    CoercAux.measurable_periodicRiesz_one hd1 H.s_nonneg H.s_lt
  have hWc := pxS_W_continuous H hΨ
  obtain ⟨Bw, hBw⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn hWc.continuousOn
  have hgz : Integrable (fun u => periodicRiesz d s (z - u)) := hg.comp_sub_left z
  simp_rw [pxS_Jop_slice H hΨ _ z]
  unfold convFun
  have hint : Integrable (Function.uncurry fun (y u : Torus d) => periodicRiesz d s (z - u) *
      pxS_W ρ Ψ (u, y)) ((withDensityReal ρ).prod volume) := by
    refine Integrable.mono' ((integrable_const Bw).mul_prod hgz.norm) ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact (hgm.comp (measurable_const.sub measurable_snd)).mul
        (hWc.measurable.comp (measurable_snd.prodMk measurable_fst))
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, norm_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right ((hBw (p.2, p.1) (Set.mem_univ _))) (norm_nonneg _)
  rw [integral_integral_swap hint]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.zero_apply]
  rw [integral_const_mul]
  have : ∫ y, pxS_W ρ Ψ (u, y) ∂(withDensityReal ρ) = 0 := by
    unfold pxS_W
    simp only []
    rw [integral_neg, integral_const_mul, pxS_Lop_mean H hΨ hc u]
    simp
  rw [this, mul_zero]

/-- The mean-zero first-variable part of `𝒥`. -/
def pxS_ak (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (Ψ : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  projMean (withDensityReal ρ) (fun z => Jop d s ρ (fun w => Ψ w y) z) x

theorem pxS_ak_eq (H : ParxHyp d s V β ρ) (Ψ : Torus d → Torus d → ℝ) (x y : Torus d) :
    pxS_ak d s ρ Ψ x y = Jop d s ρ (fun w => Ψ w y) x - ∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z := by
  unfold pxS_ak projMean
  rw [PDE.MFAdjoint.pair_mu H.rho_smooth.density]

theorem pxS_Phi_continuous (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ}
    (hΨ : PDE.IsCk2 2 Ψ) :
    Continuous (fun p : Torus d × Torus d => Jop d s ρ (fun w => Ψ w p.2) p.1) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) H.two_le
  have hg := PDE.MFOneLe.integrable_periodicRiesz hd1 s H.s_nonneg H.s_lt
  have h1 := pxS_continuous_conv_pair hg (pxS_W_continuous H hΨ)
  have h2 : (fun p : Torus d × Torus d => Jop d s ρ (fun w => Ψ w p.2) p.1) =
      fun p : Torus d × Torus d => convFun (periodicRiesz d s) (fun u => pxS_W ρ Ψ (u, p.2)) p.1 := by
    funext p
    exact pxS_Jop_slice H hΨ p.2 p.1
  rw [h2]
  exact h1

theorem pxS_I_continuous (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ}
    (hΨ : PDE.IsCk2 2 Ψ) :
    Continuous (fun y : Torus d => ∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z) := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := PDE.MFAux.continuous_of_isCk hρ1
  have hΦ := pxS_Phi_continuous H hΨ
  have hΦ' : Continuous (fun q : Torus d × Torus d => Jop d s ρ (fun w => Ψ w q.1) q.2) := by
    have := hΦ.comp (continuous_snd.prodMk continuous_fst)
    simpa only [Function.comp_def] using this
  have hρ2 : Continuous (fun q : Torus d × Torus d => ρ q.2) := hρc.comp continuous_snd
  have hint : Continuous (fun q : Torus d × Torus d => ρ q.2 * Jop d s ρ (fun w => Ψ w q.1) q.2) :=
    Continuous.mul hρ2 hΦ'
  have h2 : Continuous (fun y : Torus d => ∫ z in Set.univ, ρ z * Jop d s ρ (fun w => Ψ w y) z
      ∂(volume : Measure (Torus d))) :=
    continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
      (f := fun y z => ρ z * Jop d s ρ (fun w => Ψ w y) z) hint isCompact_univ
  simpa using h2

theorem pxS_ak_continuous (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ}
    (hΨ : PDE.IsCk2 2 Ψ) : Continuous (fun p : Torus d × Torus d => pxS_ak d s ρ Ψ p.1 p.2) := by
  have hΦ := pxS_Phi_continuous H hΨ
  have hB : Continuous (fun p : Torus d × Torus d => ∫ z, ρ z * Jop d s ρ (fun w => Ψ w p.2) z) :=
    (pxS_I_continuous H hΨ).comp continuous_snd
  have e : (fun p : Torus d × Torus d => pxS_ak d s ρ Ψ p.1 p.2) = fun p : Torus d × Torus d =>
      Jop d s ρ (fun w => Ψ w p.2) p.1 - ∫ z, ρ z * Jop d s ρ (fun w => Ψ w p.2) z := by
    funext p; exact pxS_ak_eq H Ψ p.1 p.2
  rw [e]
  exact Continuous.sub hΦ hB

/-- Jet bound for first-variable slices. -/
theorem pxS_slice_cbNorm {Ψ : Torus d → Torus d → ℝ} (hΨ : PDE.IsCk2 2 Ψ) {B : ℝ}
    (hb : ∀ i ≤ 2, ∀ p, ‖iteratedFDeriv ℝ i (PDE.lift2 Ψ) p‖ ≤ B) (y : Torus d) :
    Torus.cbNorm 2 (fun x' => Ψ x' y) ≤ 3 * B := by
  have hG : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (PDE.lift2 Ψ) := hΨ
  have hl : Torus.lift (fun x' => Ψ x' y) = fun u' => PDE.lift2 Ψ (u', Torus.rep y) := by
    funext u'; simp [Torus.lift, PDE.lift2, Torus.mk_rep]
  have := PDE.MFPair.cbNorm_le_of_jets (L := 2) (f := fun x' => Ψ x' y) (B := B) (fun i hi u => by
    rw [hl]
    refine (PDE.MFPair.norm_iteratedFDeriv_partial_left_le (PDE.lift2 Ψ) hG hi u (Torus.rep y)).trans
      (hb i hi _))
  simpa using (by norm_num [mul_comm] : ((2 : ℕ) : ℝ) + 1 = 3) ▸ this

theorem pxS_ak_bound (H : ParxHyp d s V β ρ) :
    ∃ CJ0 : ℝ, 0 ≤ CJ0 ∧ ∀ (Ψ : Torus d → Torus d → ℝ) (B : ℝ), PDE.IsCk2 2 Ψ → 0 ≤ B →
      (∀ i ≤ 2, ∀ p, ‖iteratedFDeriv ℝ i (PDE.lift2 Ψ) p‖ ≤ B) →
        ∀ x y, |pxS_ak d s ρ Ψ x y| ≤ CJ0 * B := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := PDE.MFAux.continuous_of_isCk hρ1
  have hd1 : 1 ≤ d := le_trans (by norm_num) H.two_le
  have hg := PDE.MFOneLe.integrable_periodicRiesz hd1 s H.s_nonneg H.s_lt
  obtain ⟨K1, hK1, hL⟩ := PDE.MFPair.abs_Lop_le hρ1 hρ.pos
  obtain ⟨Λ, hΛ0, hΛ⟩ := Duality.bounded_of_continuous hρc
  set G1 := ∫ y, |periodicRiesz d s y| with hG1
  have hG10 : 0 ≤ G1 := integral_nonneg fun _ => abs_nonneg _
  refine ⟨2 * (G1 * (Λ * (K1 * 3))), by positivity, fun Ψ B hΨ hB0 hb x y => ?_⟩
  set M : ℝ := G1 * (Λ * (K1 * (3 * B))) with hM
  have hM0 : 0 ≤ M := by positivity
  have hW : ∀ y' u : Torus d, |pxS_W ρ Ψ (u, y')| ≤ Λ * (K1 * (3 * B)) := by
    intro y' u
    unfold pxS_W
    rw [abs_neg, abs_mul]
    have h1 := hL (fun x' => Ψ x' y') (PDE.MFPair.isCk_slice 2 Ψ hΨ y') u
    have h2 := pxS_slice_cbNorm hΨ hb y'
    have h3 : |Lop ρ (fun x' => Ψ x' y') u| ≤ K1 * (3 * B) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 hK1)
    exact mul_le_mul (hΛ u) h3 (abs_nonneg _) hΛ0
  have hΦ : ∀ z, |Jop d s ρ (fun w => Ψ w y) z| ≤ M := by
    intro z
    rw [pxS_Jop_slice H hΨ y z]
    exact PDE.MFThermalExist.convFun_bound_of_le hg (hW y) z
  rw [pxS_ak_eq H Ψ x y]
  have h2 : |∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z| ≤ M := by
    rw [← Real.norm_eq_abs]
    have hi : Integrable (fun z => ρ z * M) :=
      (PDE.MFAdjoint.integrable_of_cont hρc).mul_const _
    calc ‖∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z‖ ≤ ∫ z, ρ z * M := by
          refine norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall fun z => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.density.nonneg z)]
          exact mul_le_mul_of_nonneg_left (hΦ z) (hρ.density.nonneg z)
      _ = M := by rw [integral_mul_const, hρ.density.integral_one, one_mul]
  calc |Jop d s ρ (fun w => Ψ w y) x - ∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z|
      ≤ |Jop d s ρ (fun w => Ψ w y) x| + |∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z| := abs_sub _ _
    _ ≤ M + M := add_le_add (hΦ x) h2
    _ = 2 * (G1 * (Λ * (K1 * 3))) * B := by rw [hM]; ring

theorem pxS_ak_mean (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ} (hΨ : PDE.IsCk2 2 Ψ)
    (hc : ∀ x, pair (withDensityReal ρ) (fun y => Ψ x y) = 0) (x : Torus d) :
    ∫ y, pxS_ak d s ρ Ψ x y ∂(withDensityReal ρ) = 0 := by
  have hρ := H.rho_smooth
  have : IsProbabilityMeasure (withDensityReal ρ) := PDE.MFSemigroup.isProb_withDensityReal hρ.density
  have hΦ := pxS_Phi_continuous H hΨ
  have hΦx : Continuous (fun y : Torus d => Jop d s ρ (fun w => Ψ w y) x) :=
    (hΦ.comp (continuous_const.prodMk continuous_id)).congr fun y => rfl
  have hI := pxS_I_continuous H hΨ
  have hi1 : Integrable (fun y : Torus d => Jop d s ρ (fun w => Ψ w y) x) (withDensityReal ρ) :=
    hΦx.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun y : Torus d => ∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z)
      (withDensityReal ρ) := hI.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [pxS_ak_eq H Ψ x]
  rw [integral_sub hi1 hi2, pxS_Jop_mean H hΨ hc x, zero_sub, neg_eq_zero]
  -- Fubini
  have hρc : Continuous ρ := PDE.MFAux.continuous_of_isCk (PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1)
  have hF : Continuous (fun q : Torus d × Torus d => ρ q.2 * Jop d s ρ (fun w => Ψ w q.1) q.2) := by
    have hΦ' : Continuous (fun q : Torus d × Torus d => Jop d s ρ (fun w => Ψ w q.1) q.2) := by
      have := hΦ.comp (continuous_snd.prodMk continuous_fst)
      simpa only [Function.comp_def] using this
    exact Continuous.mul (hρc.comp continuous_snd) hΦ'
  obtain ⟨Bf, hBf⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn hF.continuousOn
  have hint : Integrable (Function.uncurry fun (y z : Torus d) => ρ z * Jop d s ρ (fun w => Ψ w y) z)
      ((withDensityReal ρ).prod volume) :=
    Integrable.of_bound (hF.measurable.aestronglyMeasurable) Bf
      (Filter.Eventually.of_forall fun q => hBf q (Set.mem_univ _))
  rw [integral_integral_swap hint]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.zero_apply]
  rw [integral_const_mul, pxS_Jop_mean H hΨ hc z, mul_zero]

theorem pxS_ak_swap_mean (H : ParxHyp d s V β ρ) {Ψ : Torus d → Torus d → ℝ}
    (hΨ : PDE.IsCk2 2 Ψ) (x : Torus d) :
    ∫ y, pxS_ak d s ρ (fun a b => Ψ b a) y x ∂(withDensityReal ρ) = 0 := by
  have hρ := H.rho_smooth
  have : IsProbabilityMeasure (withDensityReal ρ) := PDE.MFSemigroup.isProb_withDensityReal hρ.density
  have hΨT := pxS_isCk2_swap 2 hΨ
  have hΦ := pxS_Phi_continuous H hΨT
  have hh : Continuous (fun z : Torus d => Jop d s ρ (fun w => Ψ x w) z) :=
    (hΦ.comp (continuous_id.prodMk continuous_const)).congr fun z => rfl
  have hi : Integrable (fun z : Torus d => Jop d s ρ (fun w => Ψ x w) z) (withDensityReal ρ) :=
    hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold pxS_ak projMean
  rw [integral_sub hi (integrable_const _)]
  simp [pair]

theorem pxS_jpair_smooth (H : ParxHyp d s V β ρ) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ Ψ : Torus d → Torus d → ℝ, PDE.IsCk2 2 Ψ →
      PDE.DoublyCentered (withDensityReal ρ) Ψ →
        IsCanonicalPair (withDensityReal ρ) (Jpair d s ρ Ψ) ∧
        ∀ x y, |Jpair d s ρ Ψ x y| ≤ CJ * PDE.cbNorm2 2 Ψ := by
  have hρ := H.rho_smooth
  have : IsProbabilityMeasure (withDensityReal ρ) := PDE.MFSemigroup.isProb_withDensityReal hρ.density
  obtain ⟨CJ0, hCJ0, hCJ⟩ := pxS_ak_bound H
  refine ⟨2 * CJ0, by positivity, fun Ψ hΨ hdc => ⟨fun x => ?_, fun x y => ?_⟩⟩
  · have hΨT := pxS_isCk2_swap 2 hΨ
    have c1 := pxS_ak_continuous H hΨ
    have c2 := pxS_ak_continuous H hΨT
    have h1 : Continuous (fun y : Torus d => pxS_ak d s ρ Ψ x y) :=
      (c1.comp (continuous_const.prodMk continuous_id)).congr fun y => rfl
    have h2 : Continuous (fun y : Torus d => pxS_ak d s ρ (fun a b => Ψ b a) y x) :=
      (c2.comp (continuous_id.prodMk continuous_const)).congr fun y => rfl
    have hJ : (Jpair d s ρ Ψ x) = fun y => pxS_ak d s ρ Ψ x y +
        pxS_ak d s ρ (fun a b => Ψ b a) y x := rfl
    rw [hJ]
    have hi1 := h1.integrable_of_hasCompactSupport (μ := withDensityReal ρ) (HasCompactSupport.of_compactSpace _)
    have hi2 := h2.integrable_of_hasCompactSupport (μ := withDensityReal ρ) (HasCompactSupport.of_compactSpace _)
    refine ⟨hi1.add hi2, ?_⟩
    rw [integral_add hi1 hi2, pxS_ak_mean H hΨ hdc.2 x, pxS_ak_swap_mean H hΨ x, add_zero]
  · have hB0 := PDE.MFPair.cbNorm2_nonneg 2 Ψ
    have hΨT := pxS_isCk2_swap 2 hΨ
    have hb1 : ∀ i ≤ 2, ∀ p, ‖iteratedFDeriv ℝ i (PDE.lift2 Ψ) p‖ ≤ PDE.cbNorm2 2 Ψ :=
      fun i hi p => PDE.MFPair.norm_iteratedFDeriv_le_cbNorm2 hΨ hi p
    have hb2 : ∀ i ≤ 2, ∀ p, ‖iteratedFDeriv ℝ i (PDE.lift2 (fun a b => Ψ b a)) p‖ ≤
        PDE.cbNorm2 2 Ψ := by
      intro i hi p
      have e : PDE.lift2 (fun a b => Ψ b a) = PDE.lift2 Ψ ∘ ⇑(LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d)) :=
        rfl
      rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
      exact hb1 i hi _
    have a1 := hCJ Ψ _ hΨ hB0 hb1 x y
    have a2 := hCJ (fun a b => Ψ b a) _ hΨT hB0 hb2 y x
    have hJ : Jpair d s ρ Ψ x y = pxS_ak d s ρ Ψ x y + pxS_ak d s ρ (fun a b => Ψ b a) y x := rfl
    rw [hJ]
    calc |pxS_ak d s ρ Ψ x y + pxS_ak d s ρ (fun a b => Ψ b a) y x|
        ≤ |pxS_ak d s ρ Ψ x y| + |pxS_ak d s ρ (fun a b => Ψ b a) y x| := abs_add_le _ _
      _ ≤ CJ0 * PDE.cbNorm2 2 Ψ + CJ0 * PDE.cbNorm2 2 Ψ := add_le_add a1 a2
      _ = 2 * CJ0 * PDE.cbNorm2 2 Ψ := by ring

end HRS.Parx

end
