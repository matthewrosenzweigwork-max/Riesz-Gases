import HRS.MS.Fp81S21IntervalRSBV

/-!
# S2.1(iii), packet 34a: abstract recent RS functionals

The drift and covariance variation carriers are kept separate.  Their product
has total variation norm `‖d‖ + ‖j‖`.  For a fixed prediction path, each RS
value is a bounded linear functional on its variation carrier.  The family of
these functionals is Lipschitz in the prediction path, with the same constant
as the uniform operator bound.  Physical heat-kernel estimates will provide
these hypotheses in the physical adapter.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set

namespace HRS.Fp81.S21

/-- Abstract drift/covariance RS functionals on a prediction path space and
variation norm spaces.  The two operator families represent the drift and
covariance RS integrals separately. -/
structure fp81s21_RecentRSFunctional
    (C D J : Type*) [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    (C_RS : ℝ) where
  driftKernel : C → D →L[ℝ] ℝ
  covarianceKernel : C → J →L[ℝ] ℝ
  constant_nonneg : 0 ≤ C_RS
  drift_bound : ∀ y, ‖driftKernel y‖ ≤ C_RS
  covariance_bound : ∀ y, ‖covarianceKernel y‖ ≤ C_RS
  drift_lipschitz : ∀ y y', ‖driftKernel y - driftKernel y'‖ ≤ C_RS * ‖y - y'‖
  covariance_lipschitz : ∀ y y',
    ‖covarianceKernel y - covarianceKernel y'‖ ≤ C_RS * ‖y - y'‖

/-- Total variation norm on the paired drift and covariance carriers. -/
def fp81s21_recentRSTotalVariation {D J : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup J] (d : D) (j : J) : ℝ := ‖d‖ + ‖j‖

/-- The RS value at a prediction path, for drift and covariance variation data. -/
def fp81s21_recentRSValue {C D J : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup J] [NormedSpace ℝ J]
    {C_RS : ℝ} (F : fp81s21_RecentRSFunctional C D J C_RS)
    (y : C) (d : D) (j : J) : ℝ := F.driftKernel y d + F.covarianceKernel y j

/-- At a fixed path, the paired RS value is linear in the two variation inputs. -/
def fp81s21_recentRSLinear {C D J : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup J] [NormedSpace ℝ J]
    {C_RS : ℝ} (F : fp81s21_RecentRSFunctional C D J C_RS) (y : C) :
    (D × J) →ₗ[ℝ] ℝ where
  toFun ν := fp81s21_recentRSValue F y ν.1 ν.2
  map_add' ν ν' := by
    simp [fp81s21_recentRSValue, ContinuousLinearMap.map_add]
    ring
  map_smul' a ν := by
    simp [fp81s21_recentRSValue, ContinuousLinearMap.map_smul]
    ring

/-- The fixed-path RS functional is bounded by its total variation norm. -/
theorem fp81s21_recentRS_linear_bound
    {C D J : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J] {C_RS : ℝ}
    (F : fp81s21_RecentRSFunctional C D J C_RS) (y : C) (d : D) (j : J) :
    |fp81s21_recentRSValue F y d j| ≤ C_RS * fp81s21_recentRSTotalVariation d j := by
  have hd : |F.driftKernel y d| ≤ C_RS * ‖d‖ := by
    rw [← Real.norm_eq_abs]
    calc
      ‖F.driftKernel y d‖ ≤ ‖F.driftKernel y‖ * ‖d‖ := (F.driftKernel y).le_opNorm d
      _ ≤ C_RS * ‖d‖ := mul_le_mul_of_nonneg_right (F.drift_bound y) (norm_nonneg _)
  have hj : |F.covarianceKernel y j| ≤ C_RS * ‖j‖ := by
    rw [← Real.norm_eq_abs]
    calc
      ‖F.covarianceKernel y j‖ ≤ ‖F.covarianceKernel y‖ * ‖j‖ :=
        (F.covarianceKernel y).le_opNorm j
      _ ≤ C_RS * ‖j‖ := mul_le_mul_of_nonneg_right (F.covariance_bound y) (norm_nonneg _)
  calc
    |fp81s21_recentRSValue F y d j|
        ≤ |F.driftKernel y d| + |F.covarianceKernel y j| := abs_add_le _ _
    _ ≤ C_RS * ‖d‖ + C_RS * ‖j‖ := add_le_add hd hj
    _ = C_RS * fp81s21_recentRSTotalVariation d j := by
      simp [fp81s21_recentRSTotalVariation]
      ring

private theorem fp81s21_recentRS_kernel_lipschitz
    {C V : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {C_RS : ℝ}
    (K : C → V →L[ℝ] ℝ)
    (hbound : ∀ y, ‖K y‖ ≤ C_RS)
    (hlip : ∀ y y', ‖K y - K y'‖ ≤ C_RS * ‖y - y'‖)
    (y y' : C) (v v' : V) :
    |K y v - K y' v'| ≤ C_RS * (‖v - v'‖ + ‖y - y'‖ * ‖v'‖) := by
  have hsplit : K y v - K y' v' = K y (v - v') + (K y - K y') v' := by
    simp only [map_sub, sub_apply]
    ring
  rw [hsplit]
  have hfirst : |K y (v - v')| ≤ C_RS * ‖v - v'‖ := by
    rw [← Real.norm_eq_abs]
    calc
      ‖K y (v - v')‖ ≤ ‖K y‖ * ‖v - v'‖ := (K y).le_opNorm _
      _ ≤ C_RS * ‖v - v'‖ := mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg _)
  have hsecond : |(K y - K y') v'| ≤ (C_RS * ‖y - y'‖) * ‖v'‖ := by
    rw [← Real.norm_eq_abs]
    calc
      ‖(K y - K y') v'‖ ≤ ‖K y - K y'‖ * ‖v'‖ := (K y - K y').le_opNorm _
      _ ≤ (C_RS * ‖y - y'‖) * ‖v'‖ :=
        mul_le_mul_of_nonneg_right (hlip y y') (norm_nonneg _)
  calc
    |K y (v - v') + (K y - K y') v'|
        ≤ |K y (v - v')| + |(K y - K y') v'| := abs_add_le _ _
    _ ≤ C_RS * ‖v - v'‖ + (C_RS * ‖y - y'‖) * ‖v'‖ := add_le_add hfirst hsecond
    _ = C_RS * (‖v - v'‖ + ‖y - y'‖ * ‖v'‖) := by ring

/-- Uniform heat-kernel bounds and path Lipschitz bounds imply the requested
joint continuity estimate for the RS integral.  The paired variation norm is
the sum of the drift and covariance total variations. -/
theorem fp81s21_recentRS_value_lipschitz
    {C D J : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J] {C_RS : ℝ}
    (F : fp81s21_RecentRSFunctional C D J C_RS)
    (y y' : C) (d d' : D) (j j' : J) :
    |fp81s21_recentRSValue F y d j - fp81s21_recentRSValue F y' d' j'| ≤
      C_RS * ((‖d - d'‖ + ‖j - j'‖) + ‖y - y'‖ * fp81s21_recentRSTotalVariation d' j') := by
  have hd := fp81s21_recentRS_kernel_lipschitz F.driftKernel
    F.drift_bound F.drift_lipschitz y y' d d'
  have hj := fp81s21_recentRS_kernel_lipschitz F.covarianceKernel
    F.covariance_bound F.covariance_lipschitz y y' j j'
  have hsplit : fp81s21_recentRSValue F y d j - fp81s21_recentRSValue F y' d' j' =
      (F.driftKernel y d - F.driftKernel y' d') +
      (F.covarianceKernel y j - F.covarianceKernel y' j') := by
    simp [fp81s21_recentRSValue]
    ring
  rw [hsplit]
  calc
    |(F.driftKernel y d - F.driftKernel y' d') +
        (F.covarianceKernel y j - F.covarianceKernel y' j')|
        ≤ |F.driftKernel y d - F.driftKernel y' d'| +
          |F.covarianceKernel y j - F.covarianceKernel y' j'| := abs_add_le _ _
    _ ≤ C_RS * (‖d - d'‖ + ‖y - y'‖ * ‖d'‖) +
          C_RS * (‖j - j'‖ + ‖y - y'‖ * ‖j'‖) := add_le_add hd hj
    _ = C_RS * ((‖d - d'‖ + ‖j - j'‖) +
          ‖y - y'‖ * fp81s21_recentRSTotalVariation d' j') := by
      simp [fp81s21_recentRSTotalVariation]
      ring

/-- The established scalar BV adapter supplies the RS operator bound used by
these abstract functional hypotheses. -/
theorem fp81s21_recentRS_bv_integral_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q r : ℝ} (hqr : q < r) (F : ℝ → E) (A : ℝ → E →L[ℝ] ℝ)
    (hF : BoundedVariationOn F (Set.Icc q r)) (hA : ContinuousOn A (Set.Icc q r))
    {I : ℝ} (hI : fp81s21_IsRSOn q r (fun τ u v => A τ (F v - F u)) I) :
    |I| ≤ (⨆ τ : Set.Icc q r, ‖A τ‖) * (eVariationOn F (Set.Icc q r)).toReal :=
  fp81s21_rsOn_bv_bound hqr F A hF hA hI

#print axioms fp81s21_recentRS_linear_bound
#print axioms fp81s21_recentRS_value_lipschitz
#print axioms fp81s21_recentRS_bv_integral_bound

end HRS.Fp81.S21

end
