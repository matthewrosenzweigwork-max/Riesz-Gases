import HRS.PDE.MovAAux9
import HRS.PDE.ClassicalPart
import HRS.PDE.EnergyR2Fn

/-!
# MOVA Aux10: the one-body function is `O(‖g - g_M‖_{L¹})`: the `Δ`-formula from the mean-field equation.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_abs_le_cbNorm_two {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (x : Torus d) :
    |f x| ≤ Torus.cbNorm 2 f :=
  PDE.R2Aux.abs_le_cbNorm (k := 2) (by exact_mod_cast hf) x

theorem mova_abs_partialDeriv_le {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (j : Fin d) (x : Torus d) :
    |Torus.partialDeriv j f x| ≤ Torus.cbNorm 2 f := by
  obtain ⟨h1, h2⟩ := PDE.ClassicalPart.cbNorm_partialDeriv_le 1 f (by exact_mod_cast hf) j
  have := PDE.R2Aux.abs_le_cbNorm (k := 1) (by exact_mod_cast h1) x
  have h3 : Torus.cbNorm 1 (Torus.partialDeriv j f) ≤ Torus.cbNorm 2 f := h2
  linarith

theorem mova_abs_partialDeriv2_le {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (j : Fin d) (x : Torus d) :
    |Torus.partialDeriv j (Torus.partialDeriv j f) x| ≤ Torus.cbNorm 2 f := by
  obtain ⟨h1, h2⟩ := PDE.ClassicalPart.cbNorm_partialDeriv_le 1 f (by exact_mod_cast hf) j
  obtain ⟨h1', h2'⟩ := PDE.ClassicalPart.cbNorm_partialDeriv_le 0 (Torus.partialDeriv j f)
    (by exact_mod_cast h1) j
  have := PDE.R2Aux.abs_le_cbNorm (k := 0) (by exact_mod_cast h1') x
  have h3 : Torus.cbNorm 1 (Torus.partialDeriv j f) ≤ Torus.cbNorm 2 f := h2
  have h4 : Torus.cbNorm 0 (Torus.partialDeriv j (Torus.partialDeriv j f)) ≤
      Torus.cbNorm 1 (Torus.partialDeriv j f) := h2'
  linarith

theorem mova_isLipschitz_partialDeriv {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (j : Fin d) :
    KernelGrad.IsLipschitz (Torus.cbNorm 2 f) (Torus.partialDeriv j f) := by
  obtain ⟨h1, h2⟩ := PDE.ClassicalPart.cbNorm_partialDeriv_le 1 f (by exact_mod_cast hf) j
  have h1' : Torus.IsCk 1 (Torus.partialDeriv j f) := by exact_mod_cast h1
  have hL := PDE.R2Aux.isLipschitz_of_cbNorm h1'
  have h3 : Torus.cbNorm 1 (Torus.partialDeriv j f) ≤ Torus.cbNorm 2 f := h2
  intro x y
  refine (hL x y).trans ?_
  exact mul_le_mul_of_nonneg_right h3 (KernelGrad.tdist_nonneg x y)

/-- The force `F_j = (∇g * ρ)_j` (cancellation convention). -/
def mova_F (D : DynData d) (ρ : Torus d → ℝ) (j : Fin d) (y : Torus d) : ℝ :=
  (convGradConv (periodicRieszGrad d D.s) ρ y).ofLp j

/-- Right-hand side of the mean-field equation `∂_tρ = ∑_j ∂_j(β⁻¹∂_jρ + ρ(∂_jV + F_j))`. -/
def mova_pdeRHS (D : DynData d) (ρ : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∑ j, Torus.partialDeriv j
    (fun y => D.invβ * Torus.partialDeriv j ρ y + ρ y * (Torus.partialDeriv j D.V y + mova_F D ρ j y)) x

/-- The difference kernel `g_M - g`. -/
def mova_kM (D : DynData d) (M : ℝ) (z : Torus d) : ℝ := b15c_gReg d D.s M z - periodicRiesz d D.s z

theorem mova_integrable_kM (D : DynData d) (M : ℝ) : Integrable (mova_kM D M) :=
  (mova_integrable_gReg D M).sub (mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd)

theorem mova_F_eq (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (j : Fin d) :
    mova_F D ρ j = convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) :=
  funext fun y => mova_convGradConv_eq (b15_one_le_d D) D.hs0 D.hsd hρ j y

theorem mova_Delta_eq (D : DynData d) (M : ℝ) {ρ ρt : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hpos : ∀ x, 0 < ρ r x) (hV : Torus.IsCk 2 D.V)
    (hPDE : ∀ x, ρt r x = mova_pdeRHS D (ρ r) x) (x : Torus d) :
    mova_Delta D M ρ ρt r x = ∑ j, (Torus.partialDeriv j (ρ r) x * convFun (mova_kM D M)
      (Torus.partialDeriv j (ρ r)) x + ρ r x * convFun (mova_kM D M)
        (Torus.partialDeriv j (Torus.partialDeriv j (ρ r))) x) := by
  have hρ1 := mova_isCk_one_of_two hρ
  have hV1 := mova_isCk_one_of_two hV
  have hρc := mova_continuous_of_isCk hρ
  have hwc := mova_wc_isCk_one D M hρ hpos hV
  have hgi := mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd
  have hgMi := mova_integrable_gReg D M
  have hki := mova_integrable_kM D M
  have hdρ : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j (ρ r)) := fun j => mova_isCk_partialDeriv hρ j
  have hdρc : ∀ j, Continuous (Torus.partialDeriv j (ρ r)) := fun j =>
    mova_continuous_partialDeriv hρ1 j
  have hFj : ∀ j, Torus.IsCk 1 (mova_F D (ρ r) j) := fun j => by
    rw [mova_F_eq D hρ1]; exact mova_isCk_one_convFun hgi (hdρ j)
  have hej : ∀ j, Torus.IsCk 1 (convFun (mova_kM D M) (Torus.partialDeriv j (ρ r))) := fun j =>
    mova_isCk_one_convFun hki (hdρ j)
  unfold mova_Delta mova_divRW
  rw [hPDE x, mova_pdeRHS, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hf2 : Torus.IsCk 1 (fun y => D.invβ * Torus.partialDeriv j (ρ r) y + ρ r y *
      (Torus.partialDeriv j D.V y + mova_F D (ρ r) j y)) :=
    mova_isCk_add (mova_isCk_const_mul _ (hdρ j)) (mova_isCk_mul hρ1
      (mova_isCk_add (mova_isCk_partialDeriv hV j) (hFj j)))
  have hf1 : Torus.IsCk 1 (fun z => ρ r z * mova_wc D M (ρ r) j z) := mova_isCk_mul hρ1 (hwc j)
  rw [← mova_partialDeriv_sub j hf1 hf2]
  have hfun : (fun y => ρ r y * mova_wc D M (ρ r) j y - (D.invβ * Torus.partialDeriv j (ρ r) y +
      ρ r y * (Torus.partialDeriv j D.V y + mova_F D (ρ r) j y))) =
      fun y => ρ r y * convFun (mova_kM D M) (Torus.partialDeriv j (ρ r)) y := by
    funext y
    have h1 := mova_wc_decomp D M hρ hpos j y
    have h2 : Torus.partialDeriv j (convFun (b15c_gReg d D.s M) (ρ r)) y =
        convFun (b15c_gReg d D.s M) (Torus.partialDeriv j (ρ r)) y :=
      mova_partialDeriv_convFun hgMi hρ1 j y
    have h3 : convFun (mova_kM D M) (Torus.partialDeriv j (ρ r)) y =
        convFun (b15c_gReg d D.s M) (Torus.partialDeriv j (ρ r)) y -
          convFun (periodicRiesz d D.s) (Torus.partialDeriv j (ρ r)) y :=
      mova_convFun_sub_left hgMi hgi (hdρc j) y
    rw [h3, ← h2, h1, mova_F_eq D hρ1]
    have : ρ r y ≠ 0 := (hpos y).ne'
    field_simp
    ring
  rw [hfun, mova_partialDeriv_mul j hρ1 (hej j), mova_partialDeriv_convFun hki (hdρ j) j x]

end HRS
