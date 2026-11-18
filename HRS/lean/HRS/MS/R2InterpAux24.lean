import HRS.MS.R2InterpAux23
import HRS.MC.S7PIG5Core

/-!
# S10.2 (worker S102), part 24 (packet G5): the `J` Riemann--Stieltjes integral, removal of the projection

Whole-space port of `s7_PIG_RS_J_proof`.  `Jc s = 𝒥_z((0,s])` is a hypothesis (it is produced by S10.1), together with the Lipschitz bound
`‖Jc b - Jc a‖ ≤ K (b - a)`; `r2JPair` equals the increment of `Jc` by the uniqueness `s102_J_unique`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Sec7

variable {d : ℕ} {m T : ℝ}

/-- `r2JPair` of an interval is the increment of the cumulative tensor path. -/
theorem s102_jPair_eq (C : WholeCoeff d) (hT : 0 < T) (z : ℝ → (Euc d → ℝ) → ℝ)
    (Jc : ℝ → TensorDual (OscPath d m T) 2)
    (hJ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsR2JValue C m T z (Set.Ioc a b) (Jc b - Jc a))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (M : OscPath d m T [×2]→L[ℝ] ℝ) :
    r2JPair C m T z (Set.Ioc a b) M = (Jc b - Jc a) M := by
  have h : ∃ J, IsR2JValue C m T z (Set.Ioc a b) J := ⟨_, hJ a b ha hab hb⟩
  unfold r2JPair
  rw [dif_pos h]
  have := s102_J_unique C hT z (Set.Ioc a b) h.choose_spec (hJ a b ha hab hb)
  rw [this]

/-- The second derivative of the heat function of a projected functional. -/
theorem s102_deriv_eq (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (P : OscPath d m T →L[ℝ] OscPath d m T) {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ)
    (u : ℝ) (y : OscPath d m T) :
    iteratedFDeriv ℝ 2 (r2HeatFn γ (fun x => Φ (P x)) u) y =
      (s102_projHeatD γ Φ P 2 u y).compContinuousLinearMap (fun _ => P) := by
  ext v
  rw [s102_proj_deriv γ hγp P hΦ 2 (by norm_num) u y v]
  rfl

theorem s102_projHeatD_norm_le (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (P : OscPath d m T →L[ℝ] OscPath d m T) {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) (u : ℝ)
    (y : OscPath d m T) : ‖s102_projHeatD γ Φ P 2 u y‖ ≤ cbNorm 5 Φ := by
  haveI := hγp u
  unfold s102_projHeatD
  have hb := norm_integral_le_of_norm_le_const (μ := γ u)
    (f := fun z => iteratedFDeriv ℝ 2 Φ (P (y + z))) (C := cbNorm 5 Φ)
    (Filter.Eventually.of_forall fun z => HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hΦ (by norm_num) _)
  simpa [Measure.real] using hb

theorem s102_deriv_norm_le (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (P : OscPath d m T →L[ℝ] OscPath d m T) (hP : ‖P‖ ≤ 1) {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ)
    (u : ℝ) (y : OscPath d m T) :
    ‖iteratedFDeriv ℝ 2 (r2HeatFn γ (fun x => Φ (P x)) u) y‖ ≤ cbNorm 5 Φ := by
  rw [s102_deriv_eq γ hγp P hΦ u y]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin 2, ‖P‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hP
  calc ‖s102_projHeatD γ Φ P 2 u y‖ * ∏ _i : Fin 2, ‖P‖ ≤ ‖s102_projHeatD γ Φ P 2 u y‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ cbNorm 5 Φ := by rw [mul_one]; exact s102_projHeatD_norm_le γ hγp P hΦ u y

/-- **G5**: the `𝒥` Riemann--Stieltjes integral, removal of the projection (deterministic). -/
theorem s102_RS_J (C : WholeCoeff d) (hT : 0 < T)
    (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (Pj : ℕ → (OscPath d m T →L[ℝ] OscPath d m T)) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hTconv : ∀ (j : ℕ) (v : TensorDual (OscPath d m T) j), v ∈ projTensor (OscPath d m T) j →
      Tendsto (fun L => tensorPow j (Pj L) v) atTop (𝓝 v))
    (hLP : S102LipProj γ Pj)
    {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) (Y : ℝ → OscPath d m T) (hY : ContinuousOn Y (Set.Icc 0 T))
    (z : ℝ → (Euc d → ℝ) → ℝ)
    (Jc : ℝ → TensorDual (OscPath d m T) 2) (K : ℝ) (hJc0 : Jc 0 = 0)
    (hJ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsR2JValue C m T z (Set.Ioc a b) (Jc b - Jc a))
    (hLip : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → ‖Jc b - Jc a‖ ≤ K * (b - a)) :
    ∃ I : ℝ, IsR2RS T (fun τ a b' => r2JPair C m T z (Set.Ioc a b')
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ τ) (Y τ))) I ∧ |I| ≤ cbNorm 5 Φ * (K * T) ∧
      ∃ IL : ℕ → ℝ, (∀ L, IsR2RS T (fun τ a b' => r2JPair C m T z (Set.Ioc a b')
          (iteratedFDeriv ℝ 2 (r2HeatFn γ (fun x => Φ (Pj L x)) τ) (Y τ))) (IL L)) ∧
        (∀ L, |IL L| ≤ cbNorm 5 Φ * (K * T)) ∧ Tendsto IL atTop (𝓝 I) := by
  obtain ⟨hc, hcL, hu⟩ := s102_conv_equicont γ hγp Pj hP1 hconv hLP hΦ Y hY 2 le_rfl
  have hK0 : 0 ≤ K := by
    have h := hLip 0 T le_rfl hT.le le_rfl
    have : 0 ≤ K * (T - 0) := (ContinuousLinearMap.opNorm_nonneg _).trans h
    rw [sub_zero] at this
    exact nonneg_of_mul_nonneg_left this hT
  have hC0 : 0 ≤ cbNorm 5 Φ := HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΦ 0
  obtain ⟨I, hI, IL, hIL, hlim⟩ := HRS.MC.Sec7.S7PIG5.S7PIG5_core T hT Pj hP1 (fun v hv => hTconv 2 v hv) Jc K hJc0
    (fun a b ha hab hb => (hJ a b ha hab hb).1) hLip
    (fun τ => iteratedFDeriv ℝ 2 (r2HeatFn γ Φ τ) (Y τ))
    (fun L τ => s102_projHeatD γ Φ (Pj L) 2 τ (Y τ)) hc hcL hu
  have hI' : IsR2RS T (fun τ a b' => r2JPair C m T z (Set.Ioc a b')
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ τ) (Y τ))) I :=
    (s102_isR2RS_iff _ _ _).2 (HRS.MC.Sec7.S7PIG5.S7PIG5_rs_congr hI (fun τ a b ha haτ hτb hbT =>
      (s102_jPair_eq C hT z Jc hJ a b ha (haτ.trans hτb) hbT _).symm))
  have hIL' : ∀ L, IsR2RS T (fun τ a b' => r2JPair C m T z (Set.Ioc a b')
          (iteratedFDeriv ℝ 2 (r2HeatFn γ (fun x => Φ (Pj L x)) τ) (Y τ))) (IL L) := by
    intro L
    refine (s102_isR2RS_iff _ _ _).2 (HRS.MC.Sec7.S7PIG5.S7PIG5_rs_congr (hIL L) (fun τ a b ha haτ hτb hbT => ?_))
    rw [s102_jPair_eq C hT z Jc hJ a b ha (haτ.trans hτb) hbT, s102_deriv_eq γ hγp (Pj L) hΦ]
    rfl
  have hbound : ∀ (M : ℝ → OscPath d m T [×2]→L[ℝ] ℝ), (∀ τ, ‖M τ‖ ≤ cbNorm 5 Φ) →
      ∀ τ a b : ℝ, 0 ≤ a → a ≤ τ → τ ≤ b → b ≤ T →
        |r2JPair C m T z (Set.Ioc a b) (M τ)| ≤ (cbNorm 5 Φ * K) * (b - a) := by
    intro M hM τ a b ha haτ hτb hbT
    rw [s102_jPair_eq C hT z Jc hJ a b ha (haτ.trans hτb) hbT, ← Real.norm_eq_abs]
    calc ‖(Jc b - Jc a) (M τ)‖ ≤ ‖Jc b - Jc a‖ * ‖M τ‖ := (Jc b - Jc a).le_opNorm _
      _ ≤ (K * (b - a)) * cbNorm 5 Φ :=
          mul_le_mul (hLip a b ha (haτ.trans hτb) hbT) (hM τ) (norm_nonneg _)
            (mul_nonneg hK0 (by linarith [haτ.trans hτb]))
      _ = (cbNorm 5 Φ * K) * (b - a) := by ring
  refine ⟨I, hI', ?_, IL, hIL', ?_, hlim⟩
  · have := HRS.MC.Sec7.S7PIG5.S7PIG5_rs_bound hT ((s102_isR2RS_iff _ _ _).1 hI')
      (hbound (fun τ => iteratedFDeriv ℝ 2 (r2HeatFn γ Φ τ) (Y τ))
      (fun τ => s102_deriv_norm_le γ hγp (ContinuousLinearMap.id ℝ _) ContinuousLinearMap.norm_id_le hΦ τ _))
    calc |I| ≤ (cbNorm 5 Φ * K) * T := this
      _ = cbNorm 5 Φ * (K * T) := by ring
  · intro L
    have := HRS.MC.Sec7.S7PIG5.S7PIG5_rs_bound hT ((s102_isR2RS_iff _ _ _).1 (hIL' L)) (hbound
      (fun τ => iteratedFDeriv ℝ 2 (r2HeatFn γ (fun x => Φ (Pj L x)) τ) (Y τ))
      (fun τ => s102_deriv_norm_le γ hγp (Pj L) (hP1 L) hΦ τ _))
    calc |IL L| ≤ (cbNorm 5 Φ * K) * T := this
      _ = cbNorm 5 Φ * (K * T) := by ring

end HRS.MS.R2Interp

end
