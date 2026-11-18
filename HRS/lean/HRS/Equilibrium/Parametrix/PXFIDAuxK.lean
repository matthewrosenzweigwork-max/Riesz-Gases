import HRS.Equilibrium.Parametrix.PXFIDAuxJ

/-!
# Packet PX-FID, file K: joint (a.e.) measurability of slice derivatives
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

theorem ae_ne_prod (hd : 1 ≤ d) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) :
    ∀ᵐ p : Torus d × Torus d ∂((withDensityReal ρ).prod (withDensityReal ρ)), p.1 ≠ p.2 := by
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hmeas : MeasurableSet {p : Torus d × Torus d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  refine (Measure.ae_prod_mem_iff_ae_ae_mem hmeas).2 ?_
  filter_upwards [Filter.Eventually.of_forall (fun x : Torus d => ae_ne_withDensity hd ρ x)]
    with x hx
  filter_upwards [hx] with y hy
  exact Ne.symm hy

/-- Explicit first-variable gradient of `lift2 ψ`. -/
def g1 (ψ : Torus d → Torus d → ℝ) (p : Torus d × Torus d) : Euc d :=
  WithLp.toLp 2 fun j => fderiv ℝ (lift2 ψ) (Torus.rep p.1, Torus.rep p.2) (EuclideanSpace.single j 1, 0)

/-- Explicit second-variable gradient of `lift2 ψ`. -/
def g2 (ψ : Torus d → Torus d → ℝ) (p : Torus d × Torus d) : Euc d :=
  WithLp.toLp 2 fun j => fderiv ℝ (lift2 ψ) (Torus.rep p.1, Torus.rep p.2) (0, EuclideanSpace.single j 1)

/-- Explicit first-variable Laplacian. -/
def l1 (ψ : Torus d → Torus d → ℝ) (p : Torus d × Torus d) : ℝ :=
  ∑ j : Fin d, fderiv ℝ (fderiv ℝ (lift2 ψ)) (Torus.rep p.1, Torus.rep p.2)
    (EuclideanSpace.single j 1, 0) (EuclideanSpace.single j 1, 0)

/-- Explicit second-variable Laplacian. -/
def l2 (ψ : Torus d → Torus d → ℝ) (p : Torus d × Torus d) : ℝ :=
  ∑ j : Fin d, fderiv ℝ (fderiv ℝ (lift2 ψ)) (Torus.rep p.1, Torus.rep p.2)
    (0, EuclideanSpace.single j 1) (0, EuclideanSpace.single j 1)

theorem measurable_rep_prod (d : ℕ) :
    Measurable (fun p : Torus d × Torus d => (Torus.rep p.1, Torus.rep p.2)) :=
  ((measurable_rep' d).comp measurable_fst).prodMk ((measurable_rep' d).comp measurable_snd)

theorem measurable_g1 (ψ : Torus d → Torus d → ℝ) : Measurable (g1 ψ) := by
  unfold g1
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun j => ?_)
  exact (measurable_fderiv_apply_const ℝ (lift2 ψ) _).comp (measurable_rep_prod d)

theorem measurable_g2 (ψ : Torus d → Torus d → ℝ) : Measurable (g2 ψ) := by
  unfold g2
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun j => ?_)
  exact (measurable_fderiv_apply_const ℝ (lift2 ψ) _).comp (measurable_rep_prod d)

theorem measurable_fderiv2_apply (ψ : Torus d → Torus d → ℝ) (u v : Euc d × Euc d) :
    Measurable (fun p : Torus d × Torus d =>
      fderiv ℝ (fderiv ℝ (lift2 ψ)) (Torus.rep p.1, Torus.rep p.2) u v) :=
  (((measurable_fderiv_apply_const ℝ (fderiv ℝ (lift2 ψ)) u).apply_continuousLinearMap v).comp
    (measurable_rep_prod d))

theorem measurable_l1 (ψ : Torus d → Torus d → ℝ) : Measurable (l1 ψ) := by
  unfold l1
  exact Finset.measurable_sum _ fun j _ => measurable_fderiv2_apply ψ _ _

theorem measurable_l2 (ψ : Torus d → Torus d → ℝ) : Measurable (l2 ψ) := by
  unfold l2
  exact Finset.measurable_sum _ fun j _ => measurable_fderiv2_apply ψ _ _

theorem fderiv_slice_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → ℝ)
    (A : Euc d →L[ℝ] E) (c : E) {p : Euc d} (hG : DifferentiableAt ℝ G (A p + c)) :
    fderiv ℝ (fun p' : Euc d => G (A p' + c)) p = (fderiv ℝ G (A p + c)).comp A := by
  have hι : HasFDerivAt (fun p' : Euc d => A p' + c) A p := A.hasFDerivAt.add_const c
  exact (hG.hasFDerivAt.comp p hι).fderiv

theorem lift_slice_fst (ψ : Torus d → Torus d → ℝ) (y : Torus d) :
    Torus.lift (fun z => ψ z y) =
      fun p => lift2 ψ ((ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) p + (0, Torus.rep y)) := by
  funext p
  simp [Torus.lift, lift2, Torus.mk_rep]

theorem lift_slice_snd (ψ : Torus d → Torus d → ℝ) (x : Torus d) :
    Torus.lift (fun z => ψ x z) =
      fun p => lift2 ψ ((ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) p + (Torus.rep x, 0)) := by
  funext p
  simp [Torus.lift, lift2, Torus.mk_rep]

theorem gradFst_eq_g1 (ψ : Torus d → Torus d → ℝ) (x y : Torus d)
    (h : DifferentiableAt ℝ (lift2 ψ) (Torus.rep x, Torus.rep y)) :
    gradFst ψ x y = g1 ψ (x, y) := by
  ext j
  unfold gradFst g1
  rw [PDE.MFAux.grad_apply]
  show fderiv ℝ (Torus.lift (fun z => ψ z y)) (Torus.rep x) (EuclideanSpace.single j 1) = _
  rw [lift_slice_fst, fderiv_slice_diff (lift2 ψ) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))
    (0, Torus.rep y) (by simpa using h)]
  simp

theorem gradSnd_eq_g2 (ψ : Torus d → Torus d → ℝ) (x y : Torus d)
    (h : DifferentiableAt ℝ (lift2 ψ) (Torus.rep x, Torus.rep y)) :
    gradSnd ψ x y = g2 ψ (x, y) := by
  ext j
  unfold gradSnd g2
  rw [PDE.MFAux.grad_apply]
  show fderiv ℝ (Torus.lift (fun z => ψ x z)) (Torus.rep y) (EuclideanSpace.single j 1) = _
  rw [lift_slice_snd, fderiv_slice_diff (lift2 ψ) (ContinuousLinearMap.inr ℝ (Euc d) (Euc d))
    (Torus.rep x, 0) (by simpa using h)]
  simp

theorem laplacian_fst_eq_l1 {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K ψ)
    (x y : Torus d) (hxy : x ≠ y) :
    Torus.laplacian (fun z => ψ z y) x = l1 ψ (x, y) := by
  have hS := isOpen_offDiag'' d
  have hG : ContDiffOn ℝ 2 (lift2 ψ) (offDiag d) :=
    (hψ.smooth).of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  have hp : (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) (Torus.rep x) + (0, Torus.rep y) ∈
      offDiag d := by
    simp [offDiag, Torus.mk_rep, hxy]
  rw [laplacian_eq_sum_fderiv, lift_slice_fst]
  unfold l1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [slice_fderiv2 (lift2 ψ) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) (0, Torus.rep y) hS hG hp]
  simp

theorem laplacian_snd_eq_l2 {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K ψ)
    (x y : Torus d) (hxy : x ≠ y) :
    Torus.laplacian (fun z => ψ x z) y = l2 ψ (x, y) := by
  have hS := isOpen_offDiag'' d
  have hG : ContDiffOn ℝ 2 (lift2 ψ) (offDiag d) :=
    (hψ.smooth).of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  have hp : (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) (Torus.rep y) + (Torus.rep x, 0) ∈
      offDiag d := by
    simp [offDiag, Torus.mk_rep, hxy]
  rw [laplacian_eq_sum_fderiv, lift_slice_snd]
  unfold l2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [slice_fderiv2 (lift2 ψ) (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) (Torus.rep x, 0) hS hG hp]
  simp

end HRS.Parx.PXFID

end
