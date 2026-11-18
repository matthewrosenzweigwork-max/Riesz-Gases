import HRS.MH.ScreenedFarAux1

/-! Packet FAR of `B:lem:screened` (S.B.4): proof of the statement of `far_core` in `ScreenedSpec.lean`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

section Cells

variable {s : ℝ}

theorem far_core_proof (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Λ : ℝ) (χ χh : Euc d → ℝ)
    (hχ : IsCutoffPair χ χh) (L B : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ψ : ℝ → Euc d → Euc d) (τ : ℝ), Function.Bijective (Ψ τ) →
      (∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ L * ‖x - y‖) →
      (∀ x y, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ L * ‖x - y‖) →
      (∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (advCutoff χ Ψ τ z) →
        y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ z y) → 4 / L ≤ ‖x - y‖) →
      ‖Ψ τ 0‖ ≤ B →
      ∀ μ : Euc d → ℝ, IsRegularDensityW (m + 3) Λ μ →
      ∀ (j : ℕ), j ≤ m + 1 → ∀ (idx : Fin j → Fin d) (i : Fin d) (ψ : Euc d → ℝ), Measurable ψ →
        ∀ z : Fin d → ℤ,
          (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z) x *
              gradGConvPlain d s (fun y => (1 - advCutoff χh Ψ τ (latticePt z) y) *
                (partialDeriv idx μ y * ψ y)) x i) 2 volume) ^ 2 ≤
            ENNReal.ofReal (C * Λ ^ 2) * ∑' z', ENNReal.ofReal (cellWeight d z') *
              (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 ∧
          (ENNReal.ofReal (C * Λ ^ 2) * ∑' z', ENNReal.ofReal (cellWeight d z') *
              (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 < ⊤ →
            ∀ x ∈ tsupport (advCutoff χ Ψ τ (latticePt z)),
              Integrable (fun y => rieszKernelGrad d s (x - y) i *
                ((1 - advCutoff χh Ψ τ (latticePt z) y) * (partialDeriv idx μ y * ψ y)))) := by
  have hL0 : 0 < L := by linarith
  obtain ⟨Lχ, -, hLχ1, hLχ2⟩ := cutoff_lipschitz_proof χ χh hχ
  obtain ⟨Kw, hKwdef⟩ : ∃ Kw : ℝ, Kw = L + L * B + Real.sqrt d + 1 := ⟨_, rfl⟩
  have hKw : 0 < Kw := by rw [hKwdef]; positivity
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = max 1 s * (4 / L) ^ (-s - 1) := ⟨_, rfl⟩
  have hκ : 0 ≤ κ := by
    rw [hκdef]
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.rpow_nonneg (by positivity) _)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = κ * Kw ^ ((d : ℝ) + 3) := ⟨_, rfl⟩
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ≥0∞, S = ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) := ⟨_, rfl⟩
  have hS : S < ⊤ := hSdef ▸ cellWeight_tsum_lt_top_proof hd
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ≥0∞, V = volume (Metric.closedBall (0 : Euc d) (L * Real.sqrt d)) :=
    ⟨_, rfl⟩
  have hV : V < ⊤ := hVdef ▸ measure_closedBall_lt_top
  obtain ⟨V2, hV2def⟩ : ∃ V2 : ℝ≥0∞, V2 = volume (Metric.closedBall (0 : Euc d) (L * 2)) := ⟨_, rfl⟩
  have hV2 : V2 < ⊤ := hV2def ▸ measure_closedBall_lt_top
  refine ⟨A ^ 2 * S.toReal * V.toReal * V2.toReal + 1, by positivity, ?_⟩
  intro Ψ τ hbij hlip hlipi hsep horig μ hμ j hj idx i ψ hψ z
  set Λ' := max Λ 0 with hΛ'def
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  have hreg := regularDensity_bounds_proof hμ hj idx
  have hfacts := advCutoff_facts_proof χ χh hχ Ψ τ L Lχ hL0.le hlipi ⟨hLχ1, hLχ2⟩ (latticePt z)
  have hgeo := flowCell_geometry_proof Ψ τ L hL0.le hbij hlip
  -- the squared cell estimate
  have hI := far_I_sq hd Ψ τ L B hL hB hbij hlip hlipi horig (κ * Λ') (mul_nonneg hκ hΛ'0) ψ hψ
  rw [← hKwdef, ← hSdef, ← hVdef] at hI
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ≥0∞, T = ∑' z' : Fin d → ℤ, ENNReal.ofReal (cellWeight d z') *
      (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 := ⟨_, rfl⟩
  rw [← hTdef] at hI ⊢
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ≥0∞, I = ∫⁻ y, ENNReal.ofReal (κ * Λ' * jbracket y ^ (-((d : ℝ) + 3))) *
      ‖ψ y‖ₑ := ⟨_, rfl⟩
  rw [← hIdef] at hI
  have hEeq : κ * Λ' * Kw ^ ((d : ℝ) + 3) = A * Λ' := by rw [hAdef]; ring
  rw [hEeq] at hI
  -- pointwise
  have hpt : ∀ x ∈ tsupport (advCutoff χ Ψ τ (latticePt z)), ∀ y,
      ‖(1 - advCutoff χh Ψ τ (latticePt z) y) * (partialDeriv idx μ y * ψ y)‖ₑ *
        ‖rieszKernelGrad d s (x - y)‖ₑ ≤
      ENNReal.ofReal (κ * Λ' * jbracket y ^ (-((d : ℝ) + 3))) * ‖ψ y‖ₑ := by
    intro x hx y
    rw [hκdef]
    exact far_ptwise hs0 χ χh hχ Ψ τ L hL hsep (latticePt z) Λ' hΛ'0 (partialDeriv idx μ) ψ
      hreg.2 x hx y
  have hGmeas : Measurable (fun y => (1 - advCutoff χh Ψ τ (latticePt z) y) *
      (partialDeriv idx μ y * ψ y)) := by
    have hΦc : Continuous (Function.invFun (Ψ τ)) := f5_cont_of_lip _ L hL0.le hlipi
    have hc : Continuous (advCutoff χh Ψ τ (latticePt z)) :=
      hχ.2.1.continuous.comp (hΦc.sub continuous_const)
    exact (continuous_const.sub hc).measurable.mul (hreg.1.measurable.mul hψ)
  -- bound for the gradient integral
  have hgrad : ∀ x ∈ tsupport (advCutoff χ Ψ τ (latticePt z)),
      ‖gradGConvPlain d s (fun y => (1 - advCutoff χh Ψ τ (latticePt z) y) *
        (partialDeriv idx μ y * ψ y)) x i‖ₑ ≤ I := by
    intro x hx
    have h1 : ‖gradGConvPlain d s (fun y => (1 - advCutoff χh Ψ τ (latticePt z) y) *
        (partialDeriv idx μ y * ψ y)) x i‖ₑ ≤
        ‖gradGConvPlain d s (fun y => (1 - advCutoff χh Ψ τ (latticePt z) y) *
        (partialDeriv idx μ y * ψ y)) x‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le _ i)
    refine h1.trans ?_
    unfold gradGConvPlain
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [hIdef]
    refine lintegral_mono fun y => ?_
    rw [enorm_smul]
    exact hpt x hx y
  have hIsq : I ^ 2 ≤ (ENNReal.ofReal (A * Λ') * S * V) * (ENNReal.ofReal (A * Λ') * T) := hI
  have hcχ : Continuous (advCutoff χ Ψ τ (latticePt z)) := by
    have hΦc : Continuous (Function.invFun (Ψ τ)) := f5_cont_of_lip _ L hL0.le hlipi
    exact hχ.1.1.continuous.comp (hΦc.sub continuous_const)
  have hFmeas : AEStronglyMeasurable (fun x => advCutoff χ Ψ τ (latticePt z) x *
      gradGConvPlain d s (fun y => (1 - advCutoff χh Ψ τ (latticePt z) y) *
        (partialDeriv idx μ y * ψ y)) x i) volume :=
    (hcχ.stronglyMeasurable.mul (far_meas_grad _ hGmeas i)).aestronglyMeasurable
  have hΛsq : Λ' ^ 2 ≤ Λ ^ 2 := by
    rcases le_total 0 Λ with h | h
    · rw [hΛ'def, max_eq_left h]
    · rw [hΛ'def, max_eq_right h]; nlinarith [sq_nonneg Λ]
  constructor
  · rw [far_eLpNorm_sq _ hFmeas]
    calc ∫⁻ x, ‖advCutoff χ Ψ τ (latticePt z) x *
          gradGConvPlain d s (fun y => (1 - advCutoff χh Ψ τ (latticePt z) y) *
            (partialDeriv idx μ y * ψ y)) x i‖ₑ ^ 2
        ≤ ∫⁻ x, (Metric.closedBall (Ψ τ (latticePt z)) (L * 2)).indicator (fun _ => I ^ 2) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ tsupport (advCutoff χ Ψ τ (latticePt z))
          · have hxb : x ∈ Metric.closedBall (Ψ τ (latticePt z)) (L * 2) :=
              hgeo.2.2.2.2 (latticePt z) 2 (by norm_num) (hfacts.2.2.1 x hx)
            rw [Set.indicator_of_mem hxb]
            have hc1 : ‖advCutoff χ Ψ τ (latticePt z) x‖ₑ ≤ 1 := by
              have hr := hfacts.1 x
              rw [Real.enorm_eq_ofReal hr.1]
              exact ENNReal.ofReal_le_one.2 hr.2
            have hF : ‖advCutoff χ Ψ τ (latticePt z) x *
                gradGConvPlain d s (fun y => (1 - advCutoff χh Ψ τ (latticePt z) y) *
                  (partialDeriv idx μ y * ψ y)) x i‖ₑ ≤ I := by
              rw [enorm_mul]
              calc _ ≤ 1 * I := mul_le_mul' hc1 (hgrad x hx)
                _ = I := one_mul I
            gcongr
          · have h0 : advCutoff χ Ψ τ (latticePt z) x = 0 := image_eq_zero_of_notMem_tsupport hx
            simp [h0]
      _ = I ^ 2 * V2 := by
          rw [lintegral_indicator_const Metric.isClosed_closedBall.measurableSet,
            Measure.addHaar_closedBall_center, hV2def]
      _ ≤ ((ENNReal.ofReal (A * Λ') * S * V) * (ENNReal.ofReal (A * Λ') * T)) * V2 := by
          gcongr
      _ = ENNReal.ofReal ((A * Λ') * (A * Λ') * S.toReal * V.toReal * V2.toReal) * T := by
          have hS' : S = ENNReal.ofReal S.toReal := (ENNReal.ofReal_toReal hS.ne).symm
          have hV' : V = ENNReal.ofReal V.toReal := (ENNReal.ofReal_toReal hV.ne).symm
          have hV2' : V2 = ENNReal.ofReal V2.toReal := (ENNReal.ofReal_toReal hV2.ne).symm
          have hAΛ : 0 ≤ A * Λ' := mul_nonneg hA hΛ'0
          have key : ENNReal.ofReal ((A * Λ') * (A * Λ') * S.toReal * V.toReal * V2.toReal) =
              ENNReal.ofReal (A * Λ') * ENNReal.ofReal (A * Λ') * S * V * V2 := by
            rw [ENNReal.ofReal_mul (p := (A * Λ') * (A * Λ') * S.toReal * V.toReal) (by positivity),
              ENNReal.ofReal_mul (p := (A * Λ') * (A * Λ') * S.toReal) (by positivity),
              ENNReal.ofReal_mul (p := (A * Λ') * (A * Λ')) (by positivity),
              ENNReal.ofReal_mul hAΛ, ← hS', ← hV', ← hV2']
          rw [key]
          ring
      _ ≤ ENNReal.ofReal ((A ^ 2 * S.toReal * V.toReal * V2.toReal + 1) * Λ ^ 2) * T := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have hP : 0 ≤ A ^ 2 * S.toReal * V.toReal * V2.toReal := by positivity
          calc (A * Λ') * (A * Λ') * S.toReal * V.toReal * V2.toReal
              = (A ^ 2 * S.toReal * V.toReal * V2.toReal) * Λ' ^ 2 := by ring
            _ ≤ (A ^ 2 * S.toReal * V.toReal * V2.toReal) * Λ ^ 2 :=
                mul_le_mul_of_nonneg_left hΛsq hP
            _ ≤ _ := by nlinarith [sq_nonneg Λ]
  · intro hfin x hx
    have hI_lt : I < ⊤ := by
      have hsq_lt : I ^ 2 < ⊤ := by
        refine lt_of_le_of_lt hIsq ?_
        by_cases hE : ENNReal.ofReal (A * Λ') = 0
        · rw [hE]; simp
        · have hpos : 0 < A * Λ' := by
            by_contra hneg
            exact hE (ENNReal.ofReal_eq_zero.2 (not_lt.1 hneg))
          have hΛ'pos : 0 < Λ' := by
            by_contra hneg
            have : Λ' = 0 := le_antisymm (not_lt.1 hneg) hΛ'0
            rw [this, mul_zero] at hpos
            exact lt_irrefl _ hpos
          have hΛpos : 0 < Λ := by
            rcases lt_max_iff.1 (hΛ'def ▸ hΛ'pos) with h | h
            · exact h
            · exact absurd h (lt_irrefl _)
          have hCpos : ENNReal.ofReal ((A ^ 2 * S.toReal * V.toReal * V2.toReal + 1) * Λ ^ 2) ≠ 0 := by
            have : 0 < (A ^ 2 * S.toReal * V.toReal * V2.toReal + 1) * Λ ^ 2 := by positivity
            exact (ENNReal.ofReal_pos.2 this).ne'
          have hT : T < ⊤ := by
            rw [lt_top_iff_ne_top]
            intro hT
            rw [hT, ENNReal.mul_top hCpos] at hfin
            exact lt_irrefl _ hfin
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
            ENNReal.ofReal_lt_top hS) hV) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT)
      by_contra hcon
      have hItop : I = ⊤ := not_lt_top_iff.1 hcon
      rw [hItop] at hsq_lt
      simp at hsq_lt
    have hKi : Measurable (fun y => rieszKernelGrad d s (x - y) i) :=
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable.comp
        ((movtr_rieszKernelGrad_measurable s).comp (measurable_const.sub measurable_id))
    refine ⟨(hKi.mul hGmeas).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt ?_ hI_lt
    rw [hIdef]
    refine lintegral_mono fun y => ?_
    rw [enorm_mul, mul_comm]
    refine le_trans (mul_le_mul' le_rfl ?_) (hpt x hx y)
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le _ i)

end Cells

end HRS.MH.Screened
