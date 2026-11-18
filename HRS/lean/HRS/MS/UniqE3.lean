import HRS.MS.UniqE2e
import HRS.MS.UniqM2Moll
import HRS.MS.UniqM3

/-!
# E3 of `UniqPlan.md`, part 1: splitting of `forwardPairing` and calculus on the mollifier

* `fpDiff`, `fpTrans`, `fpNonloc`: the three groups of terms of `forwardPairing`
  (`forwardPairing_split : forwardPairing D ρ t σ z ψ = fpDiff D z ψ - fpTrans (b^σ) z ψ - fpNonloc D ρ t σ z ψ`).
* `e3_phi_eq_moll`: `y ↦ ∫ ψ(x) η_ε(x - y) dx` is `moll d ε ψ` (`η` even).
* `e3_integral_mul_moll`: `∫ u · (η_ε * ψ) = ∫ (η_ε * u) ψ` for `LocMass u`, `ψ ∈ C_c`.
* `e3_D1_moll`: `∂_j (η_ε * f) = η_ε * ∂_j f` for `f ∈ C¹_c`.
* integration by parts `e3_ibp`, gradient/inner product/operator-norm formulas, compact support of `moll`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3

variable {d : ℕ}

/-! ### The three groups of terms of `forwardPairing` -/

/-- Diffusion part `ν ∫ u Δφ`. -/
def fpDiff (D : WholeDyn d) (u φ : Euc d → ℝ) : ℝ :=
  D.invβ * ∫ x, u x * Laplacian.laplacian φ x

/-- Transport part `∫ u ∑_i ∂_i(b_i φ)` (enters `forwardPairing` with a minus sign). -/
def fpTrans (b : Euc d → Euc d) (u φ : Euc d → ℝ) : ℝ :=
  ∫ x, u x * ∑ i : Fin d, fderiv ℝ (fun y => b y i * φ y) x (EuclideanSpace.single i (1 : ℝ))

/-- Nonlocal part `∑_{ij} M_{ji} ∫ u ∂_j(ρ · kernelConvDeriv d s i φ)` (enters with a minus sign). -/
def fpNonloc (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t σ : ℝ) (z ψ : Euc d → ℝ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, D.M j i *
    ∫ x, z x * fderiv ℝ (fun y => ρ (t - σ) y * kernelConvDeriv d D.s i ψ y) x
      (EuclideanSpace.single j (1 : ℝ))

theorem forwardPairing_split (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t σ : ℝ) (z ψ : Euc d → ℝ) :
    forwardPairing D ρ t σ z ψ =
      fpDiff D z ψ - fpTrans (meanFieldDriftW D (ρ (t - σ))) z ψ - fpNonloc D ρ t σ z ψ := rfl

/-! ### Elementary calculus -/

theorem e3_gradient_apply (f : Euc d → ℝ) (x : Euc d) (j : Fin d) :
    (gradient f x) j = fderiv ℝ f x (EuclideanSpace.single j 1) := by
  have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := (EuclideanSpace.single j 1 : Euc d))
    (y := fderiv ℝ f x)
  rw [← this, EuclideanSpace.inner_single_right]
  simp [gradient]

theorem e3_inner_gradient (v : Euc d) (f : Euc d → ℝ) (x : Euc d) :
    inner ℝ v (gradient f x) = ∑ i, v i * D1 i f x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e3_gradient_apply]
  simp [D1, mul_comm]

theorem e3_norm_sq_fderiv (L : Euc d →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ j, (L (EuclideanSpace.single j 1)) ^ 2 := by
  set g := (InnerProductSpace.toDual ℝ (Euc d)).symm L with hg
  have h1 : ‖L‖ = ‖g‖ := ((InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map L).symm
  have h2 : ∀ j, g j = L (EuclideanSpace.single j 1) := fun j => by
    have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
      (x := (EuclideanSpace.single j 1 : Euc d)) (y := L)
    rw [← this, EuclideanSpace.inner_single_right]
    simp [hg]
  rw [h1, EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs, h2]

theorem e3_abs_apply_le (L : Euc d →L[ℝ] ℝ) (j : Fin d) :
    |L (EuclideanSpace.single j 1)| ≤ ‖L‖ := by
  have h := L.le_opNorm (EuclideanSpace.single j (1 : ℝ))
  simpa [Real.norm_eq_abs] using h

theorem e3_integrable_mul {u f : Euc d → ℝ} (hu : LocallyIntegrable u volume)
    (hf : Continuous f) (hfc : HasCompactSupport f) : Integrable (fun x => u x * f x) volume :=
  (hu.integrable_smul_left_of_hasCompactSupport hf hfc).congr
    (Eventually.of_forall fun x => by simp [mul_comm])

theorem e3_continuous_D1 {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin d) :
    Continuous (D1 j f) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Integration by parts for `C¹` functions, one of which has compact support. -/
theorem e3_ibp {f g : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport f ∨ HasCompactSupport g) (j : Fin d) :
    ∫ x, f x * D1 j g x = - ∫ x, D1 j f x * g x := by
  have c1 := e3_continuous_D1 hf j
  have c2 := e3_continuous_D1 hg j
  have hs1 : HasCompactSupport (fun x => D1 j f x * g x) := by
    rcases hc with h | h
    · exact (D1_supp h j).mul_right
    · exact h.mul_left
  have hs2 : HasCompactSupport (fun x => f x * D1 j g x) := by
    rcases hc with h | h
    · exact h.mul_right
    · exact (D1_supp h j).mul_left
  have hs3 : HasCompactSupport (fun x => f x * g x) := by
    rcases hc with h | h
    · exact h.mul_right
    · exact h.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := EuclideanSpace.single j (1 : ℝ))
    ((c1.mul hg.continuous).integrable_of_hasCompactSupport hs1)
    ((hf.continuous.mul c2).integrable_of_hasCompactSupport hs2)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hs3)
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)

/-! ### The mollifier -/

theorem e3_phi_eq_moll {ε : ℝ} (ψ : Euc d → ℝ) :
    (fun y => ∫ x, ψ x * eta d ε (x - y)) = moll d ε ψ := by
  funext y
  unfold moll
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← eta_neg ε (x - y), neg_sub, mul_comm]

theorem e3_integral_mul_moll {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u)
    {ψ : Euc d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, u x * moll d ε ψ x = ∫ x, moll d ε u x * ψ x :=
  (integral_moll_mul' hε hu hψ hψc).symm

theorem e3_isWeakGrad {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    IsWeakGrad f (gradient f) := by
  refine ⟨?_, fun ψ hψ hψc j => ?_⟩
  · have : Continuous (gradient f) :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hf.continuous_fderiv (by simp))
    exact this.measurable
  · have h := e3_ibp (f := f) (g := ψ) hf (hψ.of_le (by simp)) (Or.inl hc) j
    simp only [e3_gradient_apply]
    exact h

theorem e3_D1_moll {ε : ℝ} (hε : 0 < ε) {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (j : Fin d) : D1 j (moll d ε f) = moll d ε (D1 j f) := by
  funext x
  have hli : LocallyIntegrable f volume := hf.continuous.locallyIntegrable
  have := fderiv_moll_apply hε hli (e3_isWeakGrad hf hc) j x
  show fderiv ℝ (moll d ε f) x (EuclideanSpace.single j 1) = _
  rw [this]
  simp only [e3_gradient_apply]
  rfl

theorem e3_moll_add {ε : ℝ} (hε : 0 < ε) {a b : Euc d → ℝ} (ha : LocallyIntegrable a volume)
    (hb : LocallyIntegrable b volume) (y : Euc d) :
    moll d ε (fun x => a x + b x) y = moll d ε a y + moll d ε b y := by
  unfold moll
  simp_rw [mul_add]
  exact integral_add (m3_kernel_integrable hε y ha) (m3_kernel_integrable hε y hb)

theorem e3_moll_hasCompactSupport {ε : ℝ} (hε : 0 < ε) {f : Euc d → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (moll d ε f) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) (R + ε)) ?_
  intro x hx
  by_contra hxR
  apply hx
  unfold moll
  have : ∀ y, eta d ε (x - y) * f y = 0 := by
    intro y
    by_cases hy : y ∈ tsupport f
    · have h1 : ‖y‖ ≤ R := by simpa using hR hy
      have : eta d ε (x - y) = 0 := by
        by_contra hne
        have := eta_support hε (Function.mem_support.2 hne)
        rw [mem_ball_zero_iff] at this
        apply hxR
        rw [mem_closedBall_zero_iff]
        calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
          _ ≤ R + ε := by linarith
      rw [this, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
  simp [this]

/-- `moll` of a locally integrable function is continuous. -/
theorem e3_moll_continuous {ε : ℝ} (hε : 0 < ε) {f : Euc d → ℝ} (hf : LocallyIntegrable f volume) :
    Continuous (moll d ε f) :=
  (moll_contDiff hε hf).continuous

end HRS.MS.UniqE3
