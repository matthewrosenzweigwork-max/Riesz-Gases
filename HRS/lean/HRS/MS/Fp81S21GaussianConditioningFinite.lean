import HRS.MS.Fp81S21FutureIndep43
import HRS.MC.E213TElem

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- The finite random covariance tensor with coefficients measurable from the past.
Its elementary summands are projective tensors. -/
def fp81s21_finiteRandomTensor2
    {d : ℕ} {m H : ℝ} {Ω : Type*}
    (n : ℕ) (h : Fin n → OscPath d m H)
    (c : Fin n → Fin n → Ω → ℝ) (ω : Ω) :
    TensorDual (OscPath d m H) 2 :=
  ∑ i, ∑ j, c i j ω • HRS.elemTensor ![h i, h j]

theorem fp81s21_finiteRandomTensor2_mem_projTensor
    {d : ℕ} {m H : ℝ} {Ω : Type*}
    (n : ℕ) (h : Fin n → OscPath d m H)
    (c : Fin n → Fin n → Ω → ℝ) (ω : Ω) :
    fp81s21_finiteRandomTensor2 n h c ω ∈
      projTensor (OscPath d m H) 2 := by
  classical
  unfold fp81s21_finiteRandomTensor2
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _
    (HRS.MC.E213T.elemTensor_mem_projTensor ![h i, h j])

/-- Heat derivative conditioning for a finite random drift direction. The
coefficients need only be integrable and measurable with respect to the past
sigma-field; the derivative bounds in `MemCb 5` make their products integrable. -/
theorem fp81s21_heat_derivative_finite_random_drift
    {d : ℕ} {m H : ℝ} {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (past : Ω → A)
    (Y X : Ω → OscPath d m H)
    (hY : Measurable Y)
    (hYpast : Measurable[MeasurableSpace.comap past inferInstance] Y)
    (hX : Measurable X) (hind : IndepFun past X P)
    (γ : ℝ → Measure (OscPath d m H)) (r : ℝ)
    [IsProbabilityMeasure (γ r)] (hlaw : P.map X = γ r)
    (Φ : OscPath d m H → ℝ) (hΦ : MemCb 5 Φ)
    (n : ℕ) (h : Fin n → OscPath d m H)
    (c : Fin n → Ω → ℝ)
    (hc : ∀ i, Integrable (c i) P)
    (hcpast : ∀ i,
      AEStronglyMeasurable[MeasurableSpace.comap past inferInstance] (c i) P) :
    Integrable
      (fun ω => fderiv ℝ Φ (Y ω + X ω) (∑ i, c i ω • h i)) P ∧
    Integrable
      (fun ω => fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (∑ i, c i ω • h i)) P ∧
    (∫ ω, fderiv ℝ Φ (Y ω + X ω) (∑ i, c i ω • h i) ∂P) =
      ∫ ω, fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (∑ i, c i ω • h i) ∂P := by
  classical
  have hbase (i : Fin n) :=
    fp81s21_heat_derivative_conditioning P past Y X hY hYpast hX hind γ r hlaw
      Φ hΦ 1 (by decide) (fun _ => h i) (c i) (hc i) (hcpast i)
  have hleftTerm (i : Fin n) :
      Integrable (fun ω => c i ω * fderiv ℝ Φ (Y ω + X ω) (h i)) P := by
    simpa only [iteratedFDeriv_one_apply] using (hbase i).1
  have hrightTerm (i : Fin n) :
      Integrable
        (fun ω => c i ω * fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (h i)) P := by
    simpa only [iteratedFDeriv_one_apply] using (hbase i).2.1
  have htermEq (i : Fin n) :
      (∫ ω, c i ω * fderiv ℝ Φ (Y ω + X ω) (h i) ∂P) =
        ∫ ω, c i ω * fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (h i) ∂P := by
    simpa only [iteratedFDeriv_one_apply] using (hbase i).2.2.1
  have hleftSum :
      Integrable (fun ω => ∑ i, c i ω * fderiv ℝ Φ (Y ω + X ω) (h i)) P :=
    integrable_finset_sum _ (fun i _ => hleftTerm i)
  have hrightSum :
      Integrable
        (fun ω => ∑ i, c i ω * fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (h i)) P :=
    integrable_finset_sum _ (fun i _ => hrightTerm i)
  have hleftExpand (ω : Ω) :
      fderiv ℝ Φ (Y ω + X ω) (∑ i, c i ω • h i) =
        ∑ i, c i ω * fderiv ℝ Φ (Y ω + X ω) (h i) := by
    simp only [map_sum, map_smul, smul_eq_mul]
  have hrightExpand (ω : Ω) :
      fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (∑ i, c i ω • h i) =
        ∑ i, c i ω * fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (h i) := by
    simp only [map_sum, map_smul, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun ω => fderiv ℝ Φ (Y ω + X ω) (∑ i, c i ω • h i)) =
      (fun ω => ∑ i, c i ω * fderiv ℝ Φ (Y ω + X ω) (h i)) by
        funext ω; exact hleftExpand ω]
    exact hleftSum
  · rw [show (fun ω => fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (∑ i, c i ω • h i)) =
      (fun ω => ∑ i, c i ω * fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (h i)) by
        funext ω; exact hrightExpand ω]
    exact hrightSum
  · calc
      (∫ ω, fderiv ℝ Φ (Y ω + X ω) (∑ i, c i ω • h i) ∂P) =
          ∫ ω, ∑ i, c i ω * fderiv ℝ Φ (Y ω + X ω) (h i) ∂P := by
            apply integral_congr_ae
            exact Eventually.of_forall fun ω => hleftExpand ω
      _ = ∑ i, ∫ ω, c i ω * fderiv ℝ Φ (Y ω + X ω) (h i) ∂P :=
            integral_finset_sum _ (fun i _ => hleftTerm i)
      _ = ∑ i, ∫ ω, c i ω * fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (h i) ∂P := by
            apply Finset.sum_congr rfl
            intro i hi
            exact htermEq i
      _ = ∫ ω, ∑ i, c i ω * fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (h i) ∂P := by
            symm
            exact integral_finset_sum _ (fun i _ => hrightTerm i)
      _ = ∫ ω, fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (∑ i, c i ω • h i) ∂P := by
            apply integral_congr_ae
            exact Eventually.of_forall fun ω => (hrightExpand ω).symm

/-- Heat derivative conditioning for a finite random covariance correction.
The tensor is the finite projective sum of elementary directions, and its
pairing with the Hessian is factored through the retained independent future. -/
theorem fp81s21_heat_second_derivative_finite_random_tensor
    {d : ℕ} {m H : ℝ} {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (past : Ω → A)
    (Y X : Ω → OscPath d m H)
    (hY : Measurable Y)
    (hYpast : Measurable[MeasurableSpace.comap past inferInstance] Y)
    (hX : Measurable X) (hind : IndepFun past X P)
    (γ : ℝ → Measure (OscPath d m H)) (r : ℝ)
    [IsProbabilityMeasure (γ r)] (hlaw : P.map X = γ r)
    (Φ : OscPath d m H → ℝ) (hΦ : MemCb 5 Φ)
    (n : ℕ) (h : Fin n → OscPath d m H)
    (c : Fin n → Fin n → Ω → ℝ)
    (hc : ∀ i j, Integrable (c i j) P)
    (hcpast : ∀ i j,
      AEStronglyMeasurable[MeasurableSpace.comap past inferInstance] (c i j) P) :
    Integrable
      (fun ω => fp81s21_finiteRandomTensor2 n h c ω
        (iteratedFDeriv ℝ 2 Φ (Y ω + X ω))) P ∧
    Integrable
      (fun ω => fp81s21_finiteRandomTensor2 n h c ω
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω))) P ∧
    (∫ ω, fp81s21_finiteRandomTensor2 n h c ω
        (iteratedFDeriv ℝ 2 Φ (Y ω + X ω)) ∂P) =
      ∫ ω, fp81s21_finiteRandomTensor2 n h c ω
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω)) ∂P := by
  classical
  have hbase (i j : Fin n) :=
    fp81s21_heat_derivative_conditioning P past Y X hY hYpast hX hind γ r hlaw
      Φ hΦ 2 (by decide) ![h i, h j] (c i j) (hc i j) (hcpast i j)
  have hleftTerm (i j : Fin n) :
      Integrable
        (fun ω => c i j ω * iteratedFDeriv ℝ 2 Φ (Y ω + X ω) ![h i, h j]) P :=
    (hbase i j).1
  have hrightTerm (i j : Fin n) :
      Integrable
        (fun ω => c i j ω * iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω) ![h i, h j]) P :=
    (hbase i j).2.1
  have htermEq (i j : Fin n) :
      (∫ ω, c i j ω * iteratedFDeriv ℝ 2 Φ (Y ω + X ω) ![h i, h j] ∂P) =
        ∫ ω, c i j ω * iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω) ![h i, h j] ∂P :=
    (hbase i j).2.2.1
  have hleftSum :
      Integrable
        (fun ω => ∑ i, ∑ j,
          c i j ω * iteratedFDeriv ℝ 2 Φ (Y ω + X ω) ![h i, h j]) P :=
    integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => hleftTerm i j))
  have hrightSum :
      Integrable
        (fun ω => ∑ i, ∑ j,
          c i j ω * iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω) ![h i, h j]) P :=
    integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => hrightTerm i j))
  have hleftExpand (ω : Ω) :
      fp81s21_finiteRandomTensor2 n h c ω
          (iteratedFDeriv ℝ 2 Φ (Y ω + X ω)) =
        ∑ i, ∑ j,
          c i j ω * iteratedFDeriv ℝ 2 Φ (Y ω + X ω) ![h i, h j] := by
    simp [fp81s21_finiteRandomTensor2]
  have hrightExpand (ω : Ω) :
      fp81s21_finiteRandomTensor2 n h c ω
          (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω)) =
        ∑ i, ∑ j,
          c i j ω * iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω) ![h i, h j] := by
    simp [fp81s21_finiteRandomTensor2]
  have hleftIntegralExpand :
      (∫ ω, ∑ i, ∑ j,
        c i j ω * iteratedFDeriv ℝ 2 Φ (Y ω + X ω) ![h i, h j] ∂P) =
        ∑ i, ∑ j, ∫ ω,
          c i j ω * iteratedFDeriv ℝ 2 Φ (Y ω + X ω) ![h i, h j] ∂P := by
    rw [integral_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => hleftTerm i j))]
    simp_rw [integral_finset_sum _ (fun j _ => hleftTerm _ j)]
  have hrightIntegralExpand :
      (∫ ω, ∑ i, ∑ j,
        c i j ω * iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω) ![h i, h j] ∂P) =
        ∑ i, ∑ j, ∫ ω,
          c i j ω * iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω) ![h i, h j] ∂P := by
    rw [integral_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => hrightTerm i j))]
    simp_rw [integral_finset_sum _ (fun j _ => hrightTerm _ j)]
  have hsumEq :
      (∑ i, ∑ j, ∫ ω,
        c i j ω * iteratedFDeriv ℝ 2 Φ (Y ω + X ω) ![h i, h j] ∂P) =
      ∑ i, ∑ j, ∫ ω,
        c i j ω * iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω) ![h i, h j] ∂P := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact htermEq i j
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun ω => fp81s21_finiteRandomTensor2 n h c ω
      (iteratedFDeriv ℝ 2 Φ (Y ω + X ω))) =
      (fun ω => ∑ i, ∑ j,
        c i j ω * iteratedFDeriv ℝ 2 Φ (Y ω + X ω) ![h i, h j]) by
        funext ω; exact hleftExpand ω]
    exact hleftSum
  · rw [show (fun ω => fp81s21_finiteRandomTensor2 n h c ω
      (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω))) =
      (fun ω => ∑ i, ∑ j,
        c i j ω * iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω) ![h i, h j]) by
        funext ω; exact hrightExpand ω]
    exact hrightSum
  · calc
      (∫ ω, fp81s21_finiteRandomTensor2 n h c ω
          (iteratedFDeriv ℝ 2 Φ (Y ω + X ω)) ∂P) =
          ∫ ω, ∑ i, ∑ j,
            c i j ω * iteratedFDeriv ℝ 2 Φ (Y ω + X ω) ![h i, h j] ∂P := by
              apply integral_congr_ae
              exact Eventually.of_forall hleftExpand
      _ = ∑ i, ∑ j, ∫ ω,
            c i j ω * iteratedFDeriv ℝ 2 Φ (Y ω + X ω) ![h i, h j] ∂P :=
            hleftIntegralExpand
      _ = ∑ i, ∑ j, ∫ ω,
            c i j ω * iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω) ![h i, h j] ∂P :=
            hsumEq
      _ = ∫ ω, ∑ i, ∑ j,
            c i j ω * iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω) ![h i, h j] ∂P :=
            hrightIntegralExpand.symm
      _ = ∫ ω, fp81s21_finiteRandomTensor2 n h c ω
            (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω)) ∂P := by
              apply integral_congr_ae
              exact Eventually.of_forall fun ω => (hrightExpand ω).symm

#print axioms fp81s21_finiteRandomTensor2_mem_projTensor
#print axioms fp81s21_heat_derivative_finite_random_drift
#print axioms fp81s21_heat_second_derivative_finite_random_tensor
end HRS.Fp81.S21
end
