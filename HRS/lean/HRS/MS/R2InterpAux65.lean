import HRS.MS.R2InterpAux64

/-!
# S10.2 (worker S102), part 65 (packet G5): the `𝒥` Riemann--Stieltjes integral, removal of the projection, bounded-variation version
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Sec7

variable {d : ℕ} {m T : ℝ}

set_option maxSynthPendingDepth 3 in
theorem s102_var_mono {E : Type*} [NormedAddCommGroup E] {Jc : ℝ → E} (hBV : BoundedVariationOn Jc (Set.Icc 0 T))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (eVariationOn Jc (Set.Icc 0 a)).toReal ≤ (eVariationOn Jc (Set.Icc 0 b)).toReal := by
  refine ENNReal.toReal_mono ?_ (eVariationOn.mono Jc (Set.Icc_subset_Icc le_rfl hab))
  exact ne_top_of_le_ne_top hBV (eVariationOn.mono Jc (Set.Icc_subset_Icc le_rfl hb))

set_option maxSynthPendingDepth 3 in
theorem s102_incr_le_var {E : Type*} [NormedAddCommGroup E] {Jc : ℝ → E} (hBV : BoundedVariationOn Jc (Set.Icc 0 T))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    ‖Jc b - Jc a‖ ≤ (eVariationOn Jc (Set.Icc 0 b)).toReal - (eVariationOn Jc (Set.Icc 0 a)).toReal := by
  have hsplit := eVariationOn.Icc_add_Icc Jc (s := Set.univ) ha hab (Set.mem_univ a)
  simp only [Set.univ_inter] at hsplit
  have hfin : ∀ {c : ℝ}, c ≤ T → 0 ≤ c → eVariationOn Jc (Set.Icc 0 c) ≠ ⊤ := fun hc _ =>
    ne_top_of_le_ne_top hBV (eVariationOn.mono Jc (Set.Icc_subset_Icc le_rfl hc))
  have hfin2 : eVariationOn Jc (Set.Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top hBV (eVariationOn.mono Jc (Set.Icc_subset_Icc ha hb))
  have hedist : edist (Jc b) (Jc a) ≤ eVariationOn Jc (Set.Icc a b) :=
    eVariationOn.edist_le Jc ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
  have h1 : ‖Jc b - Jc a‖ ≤ (eVariationOn Jc (Set.Icc a b)).toReal := by
    rw [← dist_eq_norm, dist_edist]
    exact ENNReal.toReal_mono hfin2 hedist
  have h2 : (eVariationOn Jc (Set.Icc 0 b)).toReal = (eVariationOn Jc (Set.Icc 0 a)).toReal +
      (eVariationOn Jc (Set.Icc a b)).toReal := by
    rw [← hsplit]
    exact ENNReal.toReal_add (hfin (hab.trans hb) ha) hfin2
  linarith

set_option maxSynthPendingDepth 3 in
/-- **G5** (bounded variation): the `𝒥` Riemann--Stieltjes integral, removal of the projection (deterministic). -/
theorem s102_RS_J_bv (C : WholeCoeff d) (hT : 0 < T)
    (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (Pj : ℕ → (OscPath d m T →L[ℝ] OscPath d m T)) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hTconv : ∀ (j : ℕ) (v : TensorDual (OscPath d m T) j), v ∈ projTensor (OscPath d m T) j →
      Tendsto (fun L => tensorPow j (Pj L) v) atTop (𝓝 v))
    (hLP : S102LipProj γ Pj)
    {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) (Y : ℝ → OscPath d m T) (hY : ContinuousOn Y (Set.Icc 0 T))
    (z : ℝ → (Euc d → ℝ) → ℝ)
    (Jc : ℝ → TensorDual (OscPath d m T) 2) (hJc0 : Jc 0 = 0)
    (hJ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsR2JValue C m T z (Set.Ioc a b) (Jc b - Jc a))
    (hBVJ : BoundedVariationOn Jc (Set.Icc 0 T)) :
    ∃ I : ℝ, IsR2RS T (fun τ a b' => r2JPair C m T z (Set.Ioc a b')
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ τ) (Y τ))) I ∧ |I| ≤ cbNorm 5 Φ * (eVariationOn Jc (Set.Icc 0 T)).toReal ∧
      ∃ IL : ℕ → ℝ, (∀ L, IsR2RS T (fun τ a b' => r2JPair C m T z (Set.Ioc a b')
          (iteratedFDeriv ℝ 2 (r2HeatFn γ (fun x => Φ (Pj L x)) τ) (Y τ))) (IL L)) ∧
        (∀ L, |IL L| ≤ cbNorm 5 Φ * (eVariationOn Jc (Set.Icc 0 T)).toReal) ∧ Tendsto IL atTop (𝓝 I) := by
  obtain ⟨hc, hcL, hu⟩ := s102_conv_equicont γ hγp Pj hP1 hconv hLP hΦ Y hY 2 le_rfl
  have hC0 : 0 ≤ cbNorm 5 Φ := HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΦ 0
  obtain ⟨I, hI, IL, hIL, hlim⟩ := s102_G5core_bv T hT Pj hP1 (fun v hv => hTconv 2 v hv) Jc hJc0
    (fun a b ha hab hb => (hJ a b ha hab hb).1) hBVJ
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
  let v : ℝ → ℝ := fun s => (eVariationOn Jc (Set.Icc 0 s)).toReal
  have hbound : ∀ (M : ℝ → OscPath d m T [×2]→L[ℝ] ℝ), (∀ τ, ‖M τ‖ ≤ cbNorm 5 Φ) →
      ∀ τ a b : ℝ, 0 ≤ a → a ≤ τ → τ ≤ b → b ≤ T →
        |r2JPair C m T z (Set.Ioc a b) (M τ)| ≤ cbNorm 5 Φ * (v b - v a) := by
    intro M hM τ a b ha haτ hτb hbT
    rw [s102_jPair_eq C hT z Jc hJ a b ha (haτ.trans hτb) hbT, ← Real.norm_eq_abs]
    calc ‖(Jc b - Jc a) (M τ)‖ ≤ ‖Jc b - Jc a‖ * ‖M τ‖ := (Jc b - Jc a).le_opNorm _
      _ ≤ (v b - v a) * cbNorm 5 Φ :=
          mul_le_mul (s102_incr_le_var hBVJ ha (haτ.trans hτb) hbT) (hM τ) (norm_nonneg _)
            (sub_nonneg.2 (s102_var_mono hBVJ ha (haτ.trans hτb) hbT))
      _ = cbNorm 5 Φ * (v b - v a) := by ring
  have hv0 : v 0 = 0 := by
    show (eVariationOn Jc (Set.Icc 0 0)).toReal = 0
    rw [Set.Icc_self, eVariationOn.constant_on (by simp)]
    simp
  refine ⟨I, hI', ?_, IL, hIL', ?_, hlim⟩
  · have := s102_rs_bound_mono hT v ((s102_isR2RS_iff _ _ _).1 hI')
      (hbound (fun τ => iteratedFDeriv ℝ 2 (r2HeatFn γ Φ τ) (Y τ))
      (fun τ => s102_deriv_norm_le γ hγp (ContinuousLinearMap.id ℝ _) ContinuousLinearMap.norm_id_le hΦ τ _))
    rw [hv0, sub_zero] at this; exact this
  · intro L
    have := s102_rs_bound_mono hT v ((s102_isR2RS_iff _ _ _).1 (hIL' L)) (hbound
      (fun τ => iteratedFDeriv ℝ 2 (r2HeatFn γ (fun x => Φ (Pj L x)) τ) (Y τ))
      (fun τ => s102_deriv_norm_le γ hγp (Pj L) (hP1 L) hΦ τ _))
    rw [hv0, sub_zero] at this; exact this

end HRS.MS.R2Interp

end
