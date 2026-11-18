import HRS.PDE.MovAAux3

/-!
# MOVA Aux4: the regularised transport field and the one-body integral `∫ h(x,y) dμ(y)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- `j`-th component of `u^M = β⁻¹∇log ρ + ∇(g_M*ρ) + ∇V`. -/
theorem mova_uReg_apply (D : DynData d) (M : ℝ) (ρ : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    (movT_uReg D M ρ x).ofLp j =
      D.invβ * Torus.partialDeriv j (fun y => Real.log (ρ y)) x +
        Torus.partialDeriv j (convFun (b15c_gReg d D.s M) ρ) x + Torus.partialDeriv j D.V x := by
  unfold movT_uReg
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mova_grad_apply]

/-- The component functions of `u^M`. -/
def mova_wc (D : DynData d) (M : ℝ) (ρ : Torus d → ℝ) (j : Fin d) : Torus d → ℝ :=
  fun x => (movT_uReg D M ρ x).ofLp j

theorem mova_integrable_gReg (D : DynData d) (M : ℝ) : Integrable (b15c_gReg d D.s M) :=
  mova_integrable_of_continuous
    (b15c_isSmooth_continuous (b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M))

theorem mova_gReg_isCk (D : DynData d) (k : ℕ) (M : ℝ) : Torus.IsCk (k : WithTop ℕ∞) (b15c_gReg d D.s M) :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (b15c_gReg d D.s M)) from
    b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M) (by exact_mod_cast le_top)

theorem mova_wc_isCk_one (D : DynData d) (M : ℝ) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hpos : ∀ x, 0 < ρ x) (hV : Torus.IsCk 2 D.V) (j : Fin d) :
    Torus.IsCk 1 (mova_wc D M ρ j) := by
  have e : mova_wc D M ρ j = fun x => D.invβ * Torus.partialDeriv j (fun y => Real.log (ρ y)) x +
      Torus.partialDeriv j (convFun (b15c_gReg d D.s M) ρ) x + Torus.partialDeriv j D.V x :=
    funext fun x => mova_uReg_apply D M ρ x j
  rw [e]
  refine mova_isCk_add (mova_isCk_add (mova_isCk_const_mul _ (mova_isCk_partialDeriv
    (mova_isCk_log hρ hpos) j)) (mova_isCk_partialDeriv (mova_isCk_two_convFun
    (mova_integrable_gReg D M) hρ) j)) (mova_isCk_partialDeriv hV j)

/-- Integral against `ρ dx`: the `c₁` identity
`∫ h^M_{u}(x,y) ρ(y) dy = ⟨u(x), ∇(g_M*ρ)(x)⟩ - g_M * div(ρ u)(x)`. -/
theorem mova_c1_eq (D : DynData d) (M : ℝ) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hdens : IsProbDensity ρ) (hpos : ∀ x, 0 < ρ x) (hV : Torus.IsCk 2 D.V) (x : Torus d) :
    ∫ y, commKernel (Torus.grad (b15c_gReg d D.s M)) (movT_uReg D M ρ) x y ∂(withDensityReal ρ) =
      inner ℝ (movT_uReg D M ρ x) (Torus.grad (convFun (b15c_gReg d D.s M) ρ) x) -
        convFun (b15c_gReg d D.s M)
          (fun y => ∑ j, Torus.partialDeriv j (fun z => ρ z * mova_wc D M ρ j z) y) x := by
  set g := b15c_gReg d D.s M with hg
  have hg1 : Torus.IsCk 1 g := mova_gReg_isCk D 1 M
  have hρc : Continuous ρ := mova_continuous_of_isCk hρ
  have hρ1 := mova_isCk_one_of_two hρ
  have hwc : ∀ j, Torus.IsCk 1 (mova_wc D M ρ j) := mova_wc_isCk_one D M hρ hpos hV
  have hwcc : ∀ j, Continuous (mova_wc D M ρ j) := fun j => mova_continuous_of_isCk (hwc j)
  have haj : ∀ j, Continuous (Torus.partialDeriv j g) := fun j => mova_continuous_partialDeriv hg1 j
  rw [PDE.MFPairing.integral_withDensityReal hdens.measurable hdens.nonneg]
  -- expand the integrand
  have hint : ∀ y, ρ y * commKernel (Torus.grad g) (movT_uReg D M ρ) x y =
      ∑ j, (mova_wc D M ρ j x * (ρ y * Torus.partialDeriv j g (x - y)) -
        (ρ y * mova_wc D M ρ j y) * Torus.partialDeriv j g (x - y)) := by
    intro y
    rw [mova_commKernel_eq, mova_inner_eq_sum, mova_inner_eq_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mova_grad_apply]
    simp only [mova_wc]
    ring
  simp_rw [hint]
  have hc1 : ∀ j, Continuous fun y => ρ y * Torus.partialDeriv j g (x - y) := fun j =>
    hρc.mul ((haj j).comp (continuous_const.sub continuous_id))
  have hc0 : ∀ j, Continuous fun y => mova_wc D M ρ j x * (ρ y * Torus.partialDeriv j g (x - y)) :=
    fun j => continuous_const.mul (hc1 j)
  have hρw : ∀ j, Continuous fun z => ρ z * mova_wc D M ρ j z := fun j => hρc.mul (hwcc j)
  have hc2 : ∀ j, Continuous fun y => (ρ y * mova_wc D M ρ j y) * Torus.partialDeriv j g (x - y) :=
    fun j => (hρc.mul (hwcc j)).mul ((haj j).comp (continuous_const.sub continuous_id))
  have hI : ∀ j, Integrable (fun y => mova_wc D M ρ j x * (ρ y * Torus.partialDeriv j g (x - y)) -
      (ρ y * mova_wc D M ρ j y) * Torus.partialDeriv j g (x - y)) := fun j =>
    ((hc0 j).sub (hc2 j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun j _ => hI j)]
  rw [mova_inner_eq_sum]
  have e2 : convFun g (fun y => ∑ j, Torus.partialDeriv j (fun z => ρ z * mova_wc D M ρ j z) y) x =
      ∑ j, convFun (Torus.partialDeriv j g) (fun z => ρ z * mova_wc D M ρ j z) x := by
    rw [mova_convFun_sum_right Finset.univ (mova_integrable_gReg D M) (fun j _ => mova_continuous_partialDeriv
      (mova_isCk_mul hρ1 (hwc j)) j) x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mova_partialDeriv_convFun (mova_integrable_gReg D M) (mova_isCk_mul hρ1 (hwc j)) j x,
      mova_partialDeriv_convFun_kernel hg1 (hρw j) j x]
  rw [e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_sub ((hc0 j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) ((hc2 j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)), integral_const_mul, mova_grad_apply]
  have k1 : Torus.partialDeriv j (convFun g ρ) x = ∫ a, ρ a * Torus.partialDeriv j g (x - a) := by
    rw [mova_partialDeriv_convFun_kernel hg1 hρc j x]
    unfold convFun
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  have k2 : convFun (Torus.partialDeriv j g) (fun z => ρ z * mova_wc D M ρ j z) x =
      ∫ a, ρ a * mova_wc D M ρ j a * Torus.partialDeriv j g (x - a) := by
    unfold convFun
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [k1, k2]
  rfl

end HRS
