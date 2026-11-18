import HRS.MS.Fp81S21GaussianConditioningLimits
import HRS.MS.Fp81S21CovRS3

/-! Finite-to-L¹ conditioning for the actual projective covariance increment. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

private theorem fp81s21_finite_tensor_integrable
    {d : ℕ} {m H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (n : ℕ) (h : Fin n → OscPath d m H)
    (c : Fin n → Fin n → Ω → ℝ) (hc : ∀ i j, Integrable (c i j) P) :
    Integrable (fun ω => (⟨fp81s21_finiteRandomTensor2 n h c ω,
      fp81s21_finiteRandomTensor2_mem_projTensor n h c ω⟩ :
        projTensor (OscPath d m H) 2)) P := by
  classical
  let e : Fin n → Fin n → projTensor (OscPath d m H) 2 :=
    fun i j => ⟨HRS.elemTensor ![h i, h j],
      HRS.MC.E213T.elemTensor_mem_projTensor _⟩
  have heq : (fun ω => (⟨fp81s21_finiteRandomTensor2 n h c ω,
      fp81s21_finiteRandomTensor2_mem_projTensor n h c ω⟩ :
        projTensor (OscPath d m H) 2)) =
      fun ω => ∑ i, ∑ j, c i j ω • e i j := by
    funext ω
    apply Subtype.ext
    simp [fp81s21_finiteRandomTensor2, e]
  rw [heq]
  exact integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hc i j).smul_const (e i j)))

private theorem fp81s21_pairing_equality_of_l1
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (L M : Ω → E →L[ℝ] ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hL : ∀ ω, ‖L ω‖ ≤ K) (hM : ∀ ω, ‖M ω‖ ≤ K)
    (D : Ω → E) (Dn : ℕ → Ω → E) (hD : Integrable D P)
    (hDn : ∀ n, Integrable (Dn n) P)
    (hLm : AEStronglyMeasurable (fun ω => L ω (D ω)) P)
    (hMm : AEStronglyMeasurable (fun ω => M ω (D ω)) P)
    (hfin : ∀ n, Integrable (fun ω => L ω (Dn n ω)) P ∧
      Integrable (fun ω => M ω (Dn n ω)) P ∧
      (∫ ω, L ω (Dn n ω) ∂P) = ∫ ω, M ω (Dn n ω) ∂P)
    (hlim : Tendsto (fun n => ∫ ω, ‖Dn n ω - D ω‖ ∂P) atTop (𝓝 0)) :
    Integrable (fun ω => L ω (D ω)) P ∧
    Integrable (fun ω => M ω (D ω)) P ∧
    (∫ ω, L ω (D ω) ∂P) = ∫ ω, M ω (D ω) ∂P := by
  have hu := fp81s21_integral_pairing_tendsto_of_l1 P L K hK hL D Dn hD hDn
    hLm (fun n => (hfin n).1.aestronglyMeasurable) hlim
  have hv := fp81s21_integral_pairing_tendsto_of_l1 P M K hK hM D Dn hD hDn
    hMm (fun n => (hfin n).2.1.aestronglyMeasurable) hlim
  have hseq : (fun n => ∫ ω, L ω (Dn n ω) ∂P) =
      (fun n => ∫ ω, M ω (Dn n ω) ∂P) := funext fun n => (hfin n).2.2
  exact ⟨hu.1, hv.1, tendsto_nhds_unique hu.2.2 (by rw [hseq]; exact hv.2.2)⟩

private theorem fp81s21_covariance_evaluation_continuous
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Φ : B → ℝ) (hΦ : ContDiff ℝ 5 Φ) :
    Continuous (fun z : B × projTensor B 2 =>
      fp81s21_covariance_pairingCLM (iteratedFDeriv ℝ 2 Φ z.1) z.2) :=
  ((fp81s21_covariance_pairingCLM_continuous.comp
    (hΦ.continuous_iteratedFDeriv (by norm_num))).comp
      continuous_fst).clm_apply continuous_snd

private theorem fp81s21_covariance_pairing_apply
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Q : B [×2]→L[ℝ] ℝ) (J : projTensor B 2) :
    fp81s21_covariance_pairingCLM Q J = (J : TensorDual B 2) Q := rfl

private theorem fp81s21_finite_tensor_pairing
    {d : ℕ} {m H : ℝ} {Ω : Type*}
    (n : ℕ) (h : Fin n → OscPath d m H)
    (c : Fin n → Fin n → Ω → ℝ) (ω : Ω)
    (Q : OscPath d m H [×2]→L[ℝ] ℝ) :
    ((⟨fp81s21_finiteRandomTensor2 n h c ω,
      fp81s21_finiteRandomTensor2_mem_projTensor n h c ω⟩ :
        projTensor (OscPath d m H) 2) : TensorDual (OscPath d m H) 2) Q =
      fp81s21_finiteRandomTensor2 n h c ω Q := rfl

private theorem fp81s21_covariance_pairing_measurable
    {Ω B : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Ω) (Φ : B → ℝ) (hΦ : ContDiff ℝ 5 Φ)
    (Y : Ω → B) (hY : AEStronglyMeasurable Y P)
    (J : Ω → projTensor B 2) (hJ : AEStronglyMeasurable J P) :
    AEStronglyMeasurable
      (fun ω => (J ω : TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (Y ω))) P := by
  exact (fp81s21_covariance_evaluation_continuous Φ hΦ).comp_aestronglyMeasurable
    (hY.prodMk hJ)

private theorem fp81s21_covariance_pairing_equality_of_l1
    {Ω B : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Ω) (Q R : Ω → B [×2]→L[ℝ] ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hQ : ∀ ω, ‖Q ω‖ ≤ K) (hR : ∀ ω, ‖R ω‖ ≤ K)
    (J : Ω → projTensor B 2) (Jn : ℕ → Ω → projTensor B 2)
    (hJ : Integrable J P) (hJn : ∀ n, Integrable (Jn n) P)
    (hQm : AEStronglyMeasurable (fun ω => (J ω : TensorDual B 2) (Q ω)) P)
    (hRm : AEStronglyMeasurable (fun ω => (J ω : TensorDual B 2) (R ω)) P)
    (hfin : ∀ n, Integrable (fun ω => (Jn n ω : TensorDual B 2) (Q ω)) P ∧
      Integrable (fun ω => (Jn n ω : TensorDual B 2) (R ω)) P ∧
      (∫ ω, (Jn n ω : TensorDual B 2) (Q ω) ∂P) =
        ∫ ω, (Jn n ω : TensorDual B 2) (R ω) ∂P)
    (hlim : Tendsto (fun n => ∫ ω, ‖Jn n ω - J ω‖ ∂P) atTop (𝓝 0)) :
    Integrable (fun ω => (J ω : TensorDual B 2) (Q ω)) P ∧
    Integrable (fun ω => (J ω : TensorDual B 2) (R ω)) P ∧
    (∫ ω, (J ω : TensorDual B 2) (Q ω) ∂P) =
      ∫ ω, (J ω : TensorDual B 2) (R ω) ∂P := by
  let L : Ω → projTensor B 2 →L[ℝ] ℝ := fun ω => fp81s21_covariance_pairingCLM (Q ω)
  let M : Ω → projTensor B 2 →L[ℝ] ℝ := fun ω => fp81s21_covariance_pairingCLM (R ω)
  have hL : ∀ ω, ‖L ω‖ ≤ K := fun ω =>
    (fp81s21_covariance_pairingCLM_norm_le (Q ω)).trans (hQ ω)
  have hM : ∀ ω, ‖M ω‖ ≤ K := fun ω =>
    (fp81s21_covariance_pairingCLM_norm_le (R ω)).trans (hR ω)
  have hfin' : ∀ n, Integrable (fun ω => L ω (Jn n ω)) P ∧
      Integrable (fun ω => M ω (Jn n ω)) P ∧
      (∫ ω, L ω (Jn n ω) ∂P) = ∫ ω, M ω (Jn n ω) ∂P := by
    intro n
    exact hfin n
  exact fp81s21_pairing_equality_of_l1 (E := projTensor B 2)
    P L M K hK hL hM J Jn hJ hJn hQm hRm hfin' hlim

private theorem fp81s21_covariance_pairing_congr_ae
    {Ω B : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Ω) (Φ : B → ℝ) (Y Z : Ω → B)
    (hZ : Z =ᵐ[P] Y) (J : Ω → projTensor B 2) :
    (fun ω => (J ω : TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (Z ω))) =ᵐ[P]
      fun ω => (J ω : TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (Y ω)) := by
  filter_upwards [hZ] with ω hω
  rw [hω]

/-- Condition an integrable projective covariance increment obtained as the L¹
limit of finite past-measurable elementary tensors. Both Hessian bounds use a
supplied constant. The pairing is the literal evaluation of the tensor on the
Hessian, with no extra covariance normalization. -/
theorem fp81s21_conditioned_covariance_limit
    {d : ℕ} {m H : ℝ} {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (past : Ω → A)
    (Y X Z : Ω → OscPath d m H) (hY : Measurable Y)
    (hYpast : Measurable[MeasurableSpace.comap past inferInstance] Y)
    (hX : Measurable X) (hind : IndepFun past X P)
    (hZ : Z =ᵐ[P] fun ω => Y ω + X ω)
    (γ : ℝ → Measure (OscPath d m H)) (r : ℝ)
    [IsProbabilityMeasure (γ r)] (hlaw : P.map X = γ r)
    (Φ : OscPath d m H → ℝ) (hΦ : MemCb 5 Φ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ K)
    (hheat : ∀ ω, ‖iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω)‖ ≤ K)
    (J : Ω → projTensor (OscPath d m H) 2) (hJ : Integrable J P)
    (k : ℕ → ℕ) (h : (n : ℕ) → Fin (k n) → OscPath d m H)
    (c : (n : ℕ) → Fin (k n) → Fin (k n) → Ω → ℝ)
    (hc : ∀ n i j, Integrable (c n i j) P)
    (hcpast : ∀ n i j,
      AEStronglyMeasurable[MeasurableSpace.comap past inferInstance] (c n i j) P)
    (hlim : Tendsto (fun n => ∫ ω,
      ‖(⟨fp81s21_finiteRandomTensor2 (k n) (h n) (c n) ω,
        fp81s21_finiteRandomTensor2_mem_projTensor (k n) (h n) (c n) ω⟩ :
          projTensor (OscPath d m H) 2) - J ω‖ ∂P) atTop (𝓝 0)) :
    Integrable (fun ω => (J ω : TensorDual (OscPath d m H) 2)
      (iteratedFDeriv ℝ 2 Φ (Z ω))) P ∧
    Integrable (fun ω => (J ω : TensorDual (OscPath d m H) 2)
      (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω))) P ∧
    (∫ ω, (J ω : TensorDual (OscPath d m H) 2)
      (iteratedFDeriv ℝ 2 Φ (Z ω)) ∂P) =
      ∫ ω, (J ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω)) ∂P := by
  classical
  let Jn : ℕ → Ω → projTensor (OscPath d m H) 2 := fun n ω =>
    ⟨fp81s21_finiteRandomTensor2 (k n) (h n) (c n) ω,
      fp81s21_finiteRandomTensor2_mem_projTensor (k n) (h n) (c n) ω⟩
  have hJn (n : ℕ) : Integrable (Jn n) P :=
    fp81s21_finite_tensor_integrable P (k n) (h n) (c n) (hc n)
  have hfin (n : ℕ) :
      Integrable (fun ω => (Jn n ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 Φ (Y ω + X ω))) P ∧
      Integrable (fun ω => (Jn n ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω))) P ∧
      (∫ ω, (Jn n ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 Φ (Y ω + X ω)) ∂P) =
      ∫ ω, (Jn n ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω)) ∂P := by
    exact fp81s21_heat_second_derivative_finite_random_tensor
      P past Y X hY hYpast hX hind γ r hlaw Φ hΦ (k n) (h n) (c n)
      (hc n) (hcpast n)
  have hleft : AEStronglyMeasurable
      (fun ω => (J ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 Φ (Y ω + X ω))) P :=
    fp81s21_covariance_pairing_measurable P Φ hΦ.1
      (fun ω => Y ω + X ω) (hY.add hX).aestronglyMeasurable
      J hJ.aestronglyMeasurable
  have hright : AEStronglyMeasurable
      (fun ω => (J ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω))) P :=
    fp81s21_covariance_pairing_measurable P (r2HeatFn γ Φ r)
      (s102_r2HeatFn_derivs γ r hΦ).1 Y hY.aestronglyMeasurable
      J hJ.aestronglyMeasurable
  have hresult :
      Integrable (fun ω => (J ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 Φ (Y ω + X ω))) P ∧
      Integrable (fun ω => (J ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω))) P ∧
      (∫ ω, (J ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 Φ (Y ω + X ω)) ∂P) =
      ∫ ω, (J ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω)) ∂P :=
    fp81s21_covariance_pairing_equality_of_l1 (B := OscPath d m H) P
      (fun ω => iteratedFDeriv ℝ 2 Φ (Y ω + X ω))
      (fun ω => iteratedFDeriv ℝ 2 (r2HeatFn γ Φ r) (Y ω))
      K hK (fun ω => hbound (Y ω + X ω)) hheat
      J Jn hJ hJn hleft hright hfin
      (show Tendsto (fun n => ∫ ω, ‖Jn n ω - J ω‖ ∂P) atTop (𝓝 0) from hlim)
  have hz : (fun ω => (J ω : TensorDual (OscPath d m H) 2)
      (iteratedFDeriv ℝ 2 Φ (Z ω))) =ᵐ[P]
      fun ω => (J ω : TensorDual (OscPath d m H) 2)
        (iteratedFDeriv ℝ 2 Φ (Y ω + X ω)) :=
    fp81s21_covariance_pairing_congr_ae P Φ (fun ω => Y ω + X ω) Z hZ J
  exact ⟨hresult.1.congr hz.symm, hresult.2.1, (integral_congr_ae hz).trans hresult.2.2⟩

#print axioms fp81s21_finite_tensor_integrable
#print axioms fp81s21_pairing_equality_of_l1
#print axioms fp81s21_covariance_evaluation_continuous
#print axioms fp81s21_covariance_pairing_apply
#print axioms fp81s21_finite_tensor_pairing
#print axioms fp81s21_covariance_pairing_measurable
#print axioms fp81s21_covariance_pairing_equality_of_l1
#print axioms fp81s21_covariance_pairing_congr_ae
#print axioms fp81s21_conditioned_covariance_limit
end HRS.Fp81.S21
end
