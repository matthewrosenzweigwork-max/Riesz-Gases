import HRS.MS.S111K4R4

/-!
# S11.1 / V02 (S11K4), Pro `R26-T6C.V07` (part): identification of the `r ≤ u` integrands, continuity of the gradient in `r`
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)
open HRS.MS.S111X1 (KData kA kG_measurable prod_integrable_kernel kA_nonneg)

variable {d : ℕ}

theorem k4_fderiv_eq (g : Euc d → ℝ) (x : Euc d) :
    fderiv ℝ g x = continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 g x) := by
  ext v
  simp [continuousMultilinearCurryFin1_apply]

/-- Pointwise continuity in `r` of the gradient of a classical adjoint orbit. -/
theorem k4_grad_cont_r {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (x : Euc d) :
    ContinuousOn (fun r => gradient (f r) x) (Icc 0 t) := by
  have h := hf.cont_c2 1 (by norm_num)
  have hc : Continuous fun r : Icc (0 : ℝ) t => gradient (f r) x := by
    have e : (fun r : Icc (0 : ℝ) t => gradient (f r) x) = fun r : Icc (0 : ℝ) t =>
        (InnerProductSpace.toDual ℝ (Euc d)).symm
          (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 (f r) x)) := by
      funext r
      rw [← k4_fderiv_eq]
      rfl
    rw [e]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
      ((continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp (h.comp (continuous_id.prodMk continuous_const)))
  exact continuousOn_iff_continuous_restrict.2 hc

theorem k4_ae_comm {κ : Euc d × Euc d → ℝ} {A A' B B' : Euc d → ℝ} (hA : A =ᵐ[volume] A')
    (hB : B =ᵐ[volume] B') :
    (fun p : Euc d × Euc d => κ p * A p.1 * B p.2) =ᵐ[(volume.prod volume : Measure (Euc d × Euc d))]
      fun p => κ p * A' p.1 * B' p.2 := by
  have h1 : (fun p : Euc d × Euc d => A p.1) =ᵐ[(volume.prod volume : Measure (Euc d × Euc d))]
      fun p => A' p.1 := Measure.quasiMeasurePreserving_fst.ae_eq_comp hA
  have h2 : (fun p : Euc d × Euc d => B p.2) =ᵐ[(volume.prod volume : Measure (Euc d × Euc d))]
      fun p => B' p.2 := Measure.quasiMeasurePreserving_snd.ae_eq_comp hB
  filter_upwards [h1, h2] with p hp1 hp2
  have e1 : A p.1 = A' p.1 := hp1
  have e2 : B p.2 = B' p.2 := hp2
  rw [e1, e2]

/-- Commutator term for densities of the form `ρ h`. -/
theorem k4_comm_low {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) (hρ : HRS.Whole.IsProbDensity ρ)
    {w : Euc d → Euc d} (hwm : Measurable w) {B1 : ℝ} (hB1 : ∀ x, ‖w x‖ ≤ B1)
    {hA hB A B : Euc d → ℝ} (hAm : Measurable hA) (hBm : Measurable hB) {Bh : ℝ}
    (hbA : ∀ x, |hA x| ≤ Bh) (hbB : ∀ x, |hB x| ≤ Bh)
    (hAe : A =ᵐ[volume] fun x => ρ x * hA x) (hBe : B =ᵐ[volume] fun x => ρ x * hB x) :
    Integrable (fun p : Euc d × Euc d => commutatorKernel d s w p.1 p.2 * A p.1 * B p.2)
        (volume.prod volume) ∧
      (∫ x, ∫ y, commutatorKernel d s w x y * A x * B y) =
        ∫ p, commutatorKernel d s w p.1 p.2 * hA p.1 * hB p.2
          ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  have hint := (k4_integrable_prod_nu hρ _).1 (k4_comm_integrable K hρ hwm hB1 hAm hbA hBm hbB)
  have hae : (fun p : Euc d × Euc d => commutatorKernel d s w p.1 p.2 * A p.1 * B p.2) =ᵐ[volume.prod volume]
      fun p => ρ p.1 * ρ p.2 * (commutatorKernel d s w p.1 p.2 * hA p.1 * hB p.2) := by
    have := k4_ae_comm (κ := fun p => commutatorKernel d s w p.1 p.2) hAe hBe
    filter_upwards [this] with p hp
    have hp' : commutatorKernel d s w p.1 p.2 * A p.1 * B p.2 =
        commutatorKernel d s w p.1 p.2 * (ρ p.1 * hA p.1) * (ρ p.2 * hB p.2) := hp
    rw [hp']
    ring
  have hI := hint.congr hae.symm
  refine ⟨hI, ?_⟩
  calc (∫ x, ∫ y, commutatorKernel d s w x y * A x * B y)
      = ∫ p : Euc d × Euc d, commutatorKernel d s w p.1 p.2 * A p.1 * B p.2 ∂(volume.prod volume) :=
        (integral_prod (fun p : Euc d × Euc d => commutatorKernel d s w p.1 p.2 * A p.1 * B p.2) hI).symm
    _ = ∫ p : Euc d × Euc d, ρ p.1 * ρ p.2 * (commutatorKernel d s w p.1 p.2 * hA p.1 * hB p.2)
          ∂(volume.prod volume) := integral_congr_ae hae
    _ = _ := (k4_integral_prod_nu hρ _).symm

/-- Dirichlet term for a density of the form `ρ h`. -/
theorem k4_dir_low {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {G hB B : Euc d → ℝ}
    (hGm : Measurable G) {BG : ℝ} (hbG : ∀ x, |G x| ≤ BG) (hBm : Measurable hB) {Bh : ℝ}
    (hbB : ∀ x, |hB x| ≤ Bh) (hBe : B =ᵐ[volume] fun x => ρ x * hB x) :
    Integrable (fun x => G x * B x) ∧
      ∫ x, G x * B x = ∫ x, G x * hB x ∂(HRS.Whole.withDensityReal ρ) := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hi : Integrable (fun x => G x * hB x) (HRS.Whole.withDensityReal ρ) := by
    refine (integrable_const (BG * Bh)).mono' (hGm.mul hBm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hbG x) (hbB x) (abs_nonneg _) ((abs_nonneg _).trans (hbG x))
  have hi' := (tc2_integrable_nu hρ _).1 hi
  have hae : (fun x => G x * B x) =ᵐ[volume] fun x => ρ x * (G x * hB x) := by
    filter_upwards [hBe] with x hx
    rw [hx]
    ring
  refine ⟨hi'.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, tc2_integral_nu hρ]

end HRS.MS.S111K4
