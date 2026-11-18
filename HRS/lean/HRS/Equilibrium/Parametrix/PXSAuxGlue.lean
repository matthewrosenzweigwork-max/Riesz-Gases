import HRS.Equilibrium.Parametrix.Defs
import HRS.PDE.MeanFieldOneLe

/-!
# Packet PXS: the convention bridge `projGen = centeredGen`

`Bop f + Jop f = backwardGenerator D ρ f` pointwise for `C²` `f`, `D = H.dyn` (`M = -I`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

open HRS.PDE HRS.PDE.MFAux

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

/-- `Jop f = g * ∑_j ∂_j(ρ ∂_j f)`. -/
theorem pxS_Jop_eq (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ1 : Torus.IsCk 1 ρ) {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (x : Torus d) :
    Jop d s ρ f x = convFun (periodicRiesz d s) (fun y => ∑ j, Torus.partialDeriv j
        (fun y' => ρ y' * Torus.partialDeriv j f y') y) x := by
  have hg := MFOneLe.integrable_periodicRiesz hd s hs0 hsd
  have hH : ∀ j, Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j f y) :=
    fun j => MFAux.isCk_mul_partialDeriv ρ f hρ1 hf j
  have hDc : ∀ j, Continuous (Torus.partialDeriv j
      (fun y' => ρ y' * Torus.partialDeriv j f y')) := fun j => continuous_partialDeriv j _ (hH j)
  unfold Jop Torus.div
  set v : Torus d → Euc d := fun z => (WithLp.toLp 2 fun j =>
      convFun (periodicRiesz d s) (fun y => ρ y * Torus.partialDeriv j f y) z : Euc d) with hv
  have hcomp : ∀ j y, Torus.lift v y j =
      Torus.lift (convFun (periodicRiesz d s) (fun y => ρ y * Torus.partialDeriv j f y)) y :=
    fun j y => rfl
  have hdiff : DifferentiableAt ℝ (Torus.lift v) (Torus.rep x) := by
    rw [differentiableAt_euclidean]
    intro j
    have : (fun y => Torus.lift v y j) =
        Torus.lift (convFun (periodicRiesz d s) (fun y => ρ y * Torus.partialDeriv j f y)) :=
      funext (hcomp j)
    rw [this]
    exact ((PDE.MFSchauder.convFun_isCk_one hg (hH j)).differentiable one_ne_zero) _
  have step : ∀ i, (fderiv ℝ (Torus.lift v) (Torus.rep x) (EuclideanSpace.single i 1)) i =
      convFun (periodicRiesz d s) (Torus.partialDeriv i
        (fun y' => ρ y' * Torus.partialDeriv i f y')) x := by
    intro i
    have h1 : HasFDerivAt (fun y => Torus.lift v y i) ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp
        (fderiv ℝ (Torus.lift v) (Torus.rep x))) (Torus.rep x) :=
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp _ hdiff.hasFDerivAt
    have h2 := h1.fderiv
    have h3 : (fun y => Torus.lift v y i) =
        Torus.lift (convFun (periodicRiesz d s) (fun y => ρ y * Torus.partialDeriv i f y)) :=
      funext (hcomp i)
    rw [h3] at h2
    have h4 : Torus.partialDeriv i (convFun (periodicRiesz d s)
        (fun y => ρ y * Torus.partialDeriv i f y)) x =
        fderiv ℝ (Torus.lift (convFun (periodicRiesz d s)
          (fun y => ρ y * Torus.partialDeriv i f y))) (Torus.rep x) (EuclideanSpace.single i 1) := rfl
    rw [← PDE.MFSchauder.convFun_partialDeriv hg (hH i) i x, h4, h2]
    simp
  simp_rw [step]
  unfold convFun
  symm
  rw [show (fun y => periodicRiesz d s (x - y) * (fun y => ∑ j, Torus.partialDeriv j
      (fun y' => ρ y' * Torus.partialDeriv j f y') y) y) = fun y => ∑ j, periodicRiesz d s (x - y) *
      Torus.partialDeriv j (fun y' => ρ y' * Torus.partialDeriv j f y') y from
      funext fun y => by simp only [Finset.mul_sum]]
  exact integral_finsetSum _ fun j _ => PDE.MFPair.integrable_kernel_mul hg x (hDc j)

/-- `Bop f = -β⁻¹ L_β f` (Gibbs relation). -/
theorem pxS_Bop_eq (H : ParxHyp d s V β ρ) {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (x : Torus d) :
    Bop d s V β ρ f x = -(β⁻¹ * Lop ρ f x) := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hV1 : Torus.IsCk 1 V := PDE.MFPair.isCk_of_smooth_ps H.V_smooth 1
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  obtain ⟨-, hdiff⟩ := MFAux.gibbs_partialDeriv V ρ (convFun (periodicRiesz d s) ρ) β H.beta_pos.ne'
    (∫ y, Real.exp (-β * (V y + convFun (periodicRiesz d s) ρ y))) hρ1 hV1 hρ.pos H.thermal.2
  have hconv : convMeasure (periodicRiesz d s) (withDensityReal ρ) = convFun (periodicRiesz d s) ρ := by
    funext z
    unfold convMeasure convFun
    rw [integral_withDensityReal_eq ρ hρc.measurable (fun y => (hρ.pos y).le)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  have hforce : ∀ j, Torus.partialDeriv j V x + (forceField d s ρ x) j =
      -β⁻¹ * (Torus.partialDeriv j ρ x / ρ x) := by
    intro j
    unfold forceField
    rw [hconv, MFAux.grad_apply, hdiff j x]
    ring
  unfold Bop
  rw [PDE.MFPair.Lop_eq hρ1 hρ.pos hf x, PiLp.inner_apply]
  have e : ∀ i, inner ℝ ((Torus.grad V x + forceField d s ρ x).ofLp i) ((Torus.grad f x).ofLp i) =
      -β⁻¹ * (Torus.partialDeriv i ρ x / ρ x) * Torus.partialDeriv i f x := by
    intro i
    rw [real_inner_eq_re_inner, ← hforce i] 
    simp [MFAux.grad_apply]
    ring
  simp_rw [e]
  rw [mul_sub, mul_neg]
  have e2 : ∑ i, -β⁻¹ * (Torus.partialDeriv i ρ x / ρ x) * Torus.partialDeriv i f x =
      -β⁻¹ * ∑ j, Torus.partialDeriv j ρ x / ρ x * Torus.partialDeriv j f x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e2]
  ring

theorem pxS_projGen_eq_centeredGen (H : ParxHyp d s V β ρ) (f : Torus d → ℝ) (hf : Torus.IsCk 2 f) :
    projGen d s V β ρ f = PDE.centeredGen H.dyn ρ f := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρ2 : Torus.IsCk 2 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 2
  have hV2 : Torus.IsCk 2 V := PDE.MFPair.isCk_of_smooth_ps H.V_smooth 2
  have hd1 : 1 ≤ d := le_trans (by norm_num) H.two_le
  unfold projGen PDE.centeredGen
  congr 1
  funext x
  have hg := MFOneLe.generator_eq hd1 H.dyn rfl β H.beta_pos rfl hV2 ρ H.thermal hρ2 hρ.pos f hf x
  rw [hg, pxS_Bop_eq H hf x, pxS_Jop_eq hd1 H.s_nonneg H.s_lt hρ1 hf x]
  rfl

end HRS.Parx

end
