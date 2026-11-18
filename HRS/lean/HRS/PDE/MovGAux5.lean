import HRS.PDE.MovGAux4

/-!
# MOVG Aux5: the one-body identity (OB) and the IBP identity for `∫ G_ρ ρt`

With `u = mfeTransport D ρ`, `K = ∇g * ρ` (cancellation convention), `ρt = pdeRHS = ∑_j ∂_j f_j`, `f_j = ρ u_j`
and `ob(x) = ∫ ρ(y) h_u(x,y) dy` (`h_u = commKernel ∇g u`):

* `movg_OB`: `g * ρt (x) = ∑_j u_j(x) K_j(x) - ob(x)`;
* `movg_Gint`: `∫ (g*ρ) ρt = -∫ ρ ∑_j u_j K_j`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movg_int_g_mul_cont (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ}
    (hf : Continuous f) (x : Torus d) :
    Integrable (fun y => periodicRiesz d s (x - y) * f y) := by
  obtain ⟨C, -, hC⟩ := mova_bound_of_continuous hf
  exact ((mova_integrable_periodicRiesz hd hs0 hsd).comp_sub_left x).mul_bdd hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa using hC y)

/-- The one-body commutator function `ob(x) = ∫ ρ(y) h_u(x,y) dy`. -/
def movg_ob (D : DynData d) (ρ : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, ρ y * commKernel (periodicRieszGrad d D.s) (mfeTransport D ρ) x y

theorem movg_rho_u (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) (hpos : ∀ x, 0 < ρ x)
    (j : Fin d) (y : Torus d) :
    ρ y * (mfeTransport D ρ y).ofLp j = mova_fj D ρ j y := by
  have hρ1 := mova_isCk_one_of_two hρ
  rw [mova_mfeTransport_apply D hρ hpos j y]
  unfold mova_fj
  rw [mova_F_eq D hρ1 j]
  have := (hpos y).ne'
  field_simp
  ring

theorem movg_OB (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) (hpos : ∀ x, 0 < ρ x)
    (hV : Torus.IsCk 2 D.V) (x : Torus d) :
    convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ) x =
      ∑ j, (mfeTransport D ρ x).ofLp j * (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j -
        movg_ob D ρ x := by
  have hd := b15_one_le_d D
  have hρ1 := mova_isCk_one_of_two hρ
  have hρc := mova_continuous_of_isCk hρ
  set u : Fin d → Torus d → ℝ := fun j y => (mfeTransport D ρ y).ofLp j with hu
  set F : Fin d → Torus d → ℝ := fun j y => mova_fj D ρ j y - u j x * ρ y with hF
  have hFck : ∀ j, Torus.IsCk 1 (F j) := fun j =>
    mova_isCk_sub (mova_fj_isCk D hρ hV j) (mova_isCk_const_mul _ hρ1)
  have hFx : ∀ j, F j x = 0 := fun j => by
    simp only [hF, hu]
    rw [← movg_rho_u D hρ hpos j x]; ring
  have hcore := movg_OBcore hd D.hs0 D.hsd hFck hFx
  have hdF : ∀ y, ∑ j, Torus.partialDeriv j (F j) y =
      mova_pdeRHS D ρ y - ∑ j, u j x * Torus.partialDeriv j ρ y := by
    intro y
    rw [mova_pdeRHS_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hF]
    rw [mova_partialDeriv_sub j (mova_fj_isCk D hρ hV j) (mova_isCk_const_mul _ hρ1),
      mova_partialDeriv_const_mul j hρ1]
  have hpc : Continuous (mova_pdeRHS D ρ) := by
    have : mova_pdeRHS D ρ = fun x => ∑ j, Torus.partialDeriv j (mova_fj D ρ j) x :=
      funext fun x => mova_pdeRHS_eq D ρ x
    rw [this]
    exact continuous_finsetSum _ fun j _ => mova_continuous_partialDeriv (mova_fj_isCk D hρ hV j) j
  have hdρc : ∀ j, Continuous (Torus.partialDeriv j ρ) := fun j => mova_continuous_partialDeriv hρ1 j
  -- left side
  have hint_j : ∀ j, Integrable (fun y => periodicRiesz d D.s (x - y) * (u j x * Torus.partialDeriv j ρ y)) :=
    fun j => movg_int_g_mul_cont hd D.hs0 D.hsd (continuous_const.mul (hdρc j)) x
  have hL : ∫ y, periodicRiesz d D.s (x - y) * ∑ j, Torus.partialDeriv j (F j) y =
      convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ) x -
        ∑ j, u j x * (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j := by
    simp_rw [hdF, mul_sub]
    rw [integral_sub (movg_int_g_mul_cont hd D.hs0 D.hsd hpc x)
      (by simp only [Finset.mul_sum]; exact integrable_finsetSum _ fun j _ => hint_j j)]
    refine congrArg₂ (· - ·) rfl ?_
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ fun j _ => hint_j j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mova_convGradConv_eq hd D.hs0 D.hsd hρ1 j x]
    unfold convFun
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  -- right side
  have hR : ∫ y, ∑ j, (periodicRieszGrad d D.s (x - y)).ofLp j * F j y = -movg_ob D ρ x := by
    unfold movg_ob
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [movg_ae_ne hd x] with y hy
    simp only [commKernel, if_neg (Ne.symm hy), hF, hu, mova_inner_eq_sum]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← movg_rho_u D hρ hpos j y]
    simp only [PiLp.sub_apply]
    ring
  rw [hcore, hR] at hL
  linarith

theorem movg_Gint (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) (hpos : ∀ x, 0 < ρ x)
    (hV : Torus.IsCk 2 D.V) :
    ∫ x, convFun (periodicRiesz d D.s) ρ x * mova_pdeRHS D ρ x =
      -∫ x, ρ x * ∑ j, (mfeTransport D ρ x).ofLp j *
        (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j := by
  have hd := b15_one_le_d D
  have hρ1 := mova_isCk_one_of_two hρ
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have hG1 : Torus.IsCk 1 (convFun (periodicRiesz d D.s) ρ) := mova_isCk_one_convFun hgi hρ1
  have hfc : ∀ j, Continuous (mova_fj D ρ j) := fun j => mova_continuous_of_isCk (mova_fj_isCk D hρ hV j)
  have hdfc : ∀ j, Continuous (Torus.partialDeriv j (mova_fj D ρ j)) := fun j =>
    mova_continuous_partialDeriv (mova_fj_isCk D hρ hV j) j
  have hGc : Continuous (convFun (periodicRiesz d D.s) ρ) := mova_continuous_of_isCk hG1
  have hdGc : ∀ j, Continuous (Torus.partialDeriv j (convFun (periodicRiesz d D.s) ρ)) := fun j =>
    mova_continuous_partialDeriv hG1 j
  have hKj : ∀ j x, Torus.partialDeriv j (convFun (periodicRiesz d D.s) ρ) x =
      (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j := fun j x => by
    rw [mova_partialDeriv_convFun hgi hρ1 j x, mova_convGradConv_eq hd D.hs0 D.hsd hρ1 j x]
  have hj : ∀ j, ∫ x, convFun (periodicRiesz d D.s) ρ x * Torus.partialDeriv j (mova_fj D ρ j) x =
      -∫ x, (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j * mova_fj D ρ j x := by
    intro j
    have h := mova_integral_ibp j hG1 (mova_fj_isCk D hρ hV j)
    have h2 : ∫ x, Torus.partialDeriv j (convFun (periodicRiesz d D.s) ρ) x * mova_fj D ρ j x =
        ∫ x, (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j * mova_fj D ρ j x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hKj])
    rw [h2] at h
    linarith
  have e1 : ∀ x, convFun (periodicRiesz d D.s) ρ x * mova_pdeRHS D ρ x =
      ∑ j, convFun (periodicRiesz d D.s) ρ x * Torus.partialDeriv j (mova_fj D ρ j) x := fun x => by
    rw [mova_pdeRHS_eq, Finset.mul_sum]
  have e2 : ∀ x, ρ x * ∑ j, (mfeTransport D ρ x).ofLp j *
      (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j =
      ∑ j, (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j * mova_fj D ρ j x := fun x => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← movg_rho_u D hρ hpos j x]; ring
  have hKc : ∀ j, Continuous fun x => (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j := fun j => by
    have : (fun x => (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j) =
        Torus.partialDeriv j (convFun (periodicRiesz d D.s) ρ) := funext fun x => (hKj j x).symm
    rw [this]; exact hdGc j
  simp_rw [e1, e2]
  have i1 : ∫ x, ∑ j, convFun (periodicRiesz d D.s) ρ x * Torus.partialDeriv j (mova_fj D ρ j) x =
      ∑ j, ∫ x, convFun (periodicRiesz d D.s) ρ x * Torus.partialDeriv j (mova_fj D ρ j) x :=
    integral_finsetSum _ fun j _ => mova_int_cont (hGc.mul (hdfc j))
  have i2 : ∫ x, ∑ j, (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j * mova_fj D ρ j x =
      ∑ j, ∫ x, (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j * mova_fj D ρ j x :=
    integral_finsetSum _ fun j _ => mova_int_cont ((hKc j).mul (hfc j))
  rw [i1, i2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => hj j

theorem movg_pde_continuous (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hV : Torus.IsCk 2 D.V) : Continuous (mova_pdeRHS D ρ) := by
  have : mova_pdeRHS D ρ = fun x => ∑ j, Torus.partialDeriv j (mova_fj D ρ j) x :=
    funext fun x => mova_pdeRHS_eq D ρ x
  rw [this]
  exact continuous_finsetSum _ fun j _ => mova_continuous_partialDeriv (mova_fj_isCk D hρ hV j) j

theorem movg_K_continuous (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) (j : Fin d) :
    Continuous fun x => (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j := by
  have hd := b15_one_le_d D
  have hρ1 := mova_isCk_one_of_two hρ
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have : (fun x => (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j) =
      convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) :=
    funext fun x => mova_convGradConv_eq hd D.hs0 D.hsd hρ1 j x
  rw [this]
  exact mova_continuous_of_isCk (mova_isCk_one_convFun hgi (mova_isCk_partialDeriv hρ j))

theorem movg_u_continuous (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) (hpos : ∀ x, 0 < ρ x)
    (hV : Torus.IsCk 2 D.V) (j : Fin d) : Continuous fun x => (mfeTransport D ρ x).ofLp j := by
  have hd := b15_one_le_d D
  have hρ1 := mova_isCk_one_of_two hρ
  have hρc := mova_continuous_of_isCk hρ
  have : (fun x => (mfeTransport D ρ x).ofLp j) = fun x => D.invβ * (Torus.partialDeriv j ρ x / ρ x) +
      (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j + Torus.partialDeriv j D.V x := by
    funext x
    rw [mova_mfeTransport_apply D hρ hpos j x, mova_convGradConv_eq hd D.hs0 D.hsd hρ1 j x]
  rw [this]
  exact ((continuous_const.mul ((mova_continuous_partialDeriv hρ1 j).div hρc (fun x => (hpos x).ne'))).add
    (movg_K_continuous D hρ j)).add (mova_continuous_partialDeriv (mova_isCk_one_of_two hV) j)

theorem movg_convpde_continuous (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hV : Torus.IsCk 2 D.V) : Continuous (convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ)) :=
  PDE.MFAux.continuous_convFun (mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd)
    (movg_pde_continuous D hρ hV)

theorem movg_ob_continuous (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) (hpos : ∀ x, 0 < ρ x)
    (hV : Torus.IsCk 2 D.V) : Continuous (movg_ob D ρ) := by
  have : movg_ob D ρ = fun x => ∑ j, (mfeTransport D ρ x).ofLp j *
      (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j - convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ) x :=
    funext fun x => by rw [movg_OB D hρ hpos hV x]; ring
  rw [this]
  exact (continuous_finsetSum _ fun j _ => (movg_u_continuous D hρ hpos hV j).mul (movg_K_continuous D hρ j)).sub
    (movg_convpde_continuous D hρ hV)

/-- `d/dt c₃ = ∫ ρt (g*ρ) + ∫ ρ (g*ρt) = -∫ ρ ob`. -/
theorem movg_c3_deriv (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) (hpos : ∀ x, 0 < ρ x)
    (hV : Torus.IsCk 2 D.V) :
    (∫ x, ρ x * convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ) x) +
      ∫ x, convFun (periodicRiesz d D.s) ρ x * mova_pdeRHS D ρ x =
    -∫ x, ρ x * movg_ob D ρ x := by
  have hρc := mova_continuous_of_isCk hρ
  have h1 := movg_Gint D hρ hpos hV
  have hS : Continuous fun x => ρ x * ∑ j, (mfeTransport D ρ x).ofLp j *
      (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j :=
    hρc.mul (continuous_finsetSum _ fun j _ => (movg_u_continuous D hρ hpos hV j).mul (movg_K_continuous D hρ j))
  have hO : Continuous fun x => ρ x * movg_ob D ρ x := hρc.mul (movg_ob_continuous D hρ hpos hV)
  have h2 : ∫ x, ρ x * convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ) x =
      (∫ x, ρ x * ∑ j, (mfeTransport D ρ x).ofLp j *
        (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j) - ∫ x, ρ x * movg_ob D ρ x := by
    rw [← integral_sub (mova_int_cont hS) (mova_int_cont hO)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [movg_OB D hρ hpos hV x]; ring
  rw [h2, h1]; ring

end HRS
