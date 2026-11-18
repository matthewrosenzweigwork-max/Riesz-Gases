import HRS.MH.ScreenedAsmCommCellAux1
import HRS.MH.ScreenedCC1
import HRS.MH.ScreenedCC2
import HRS.MH.ScreenedFarAsm

/-! Assembly of `screened_comm_cell` (frozen `HRS.Whole.screened_comm_cell`, S.B.4(iv), cell-sum part) from the
proved packets `flow_lip_sep`, `flow_origin`, `cc_near1`, `cc_near2`, `far_core`, `kcCoef_sums`.
Coefficients `Kc z z' = kcCoef d (8+√d) 1 1 z z' = 1_{|z-z'| ≤ 8+√d} + ω_{z'}`; all packet constants are
taken at the uniform Lipschitz constant `L = exp(CF |T|)` and absorbed in `C ≤ C e^{Cdτ}` (`τ ≥ 0`). -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma acc_exp_ge {C τ : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (d : ℕ) : C ≤ C * Real.exp (C * d * τ) :=
  le_mul_of_one_le_right hC (Real.one_le_exp (by positivity))

lemma acc_kc_le_one_zero {d : ℕ} (R : ℝ) (z z' : Fin d → ℤ) :
    (kcCoef d R 1 0 z z' : ℝ≥0∞) ≤ (kcCoef d R 1 1 z z' : ℝ≥0∞) := by
  have hw : 0 ≤ cellWeight d z' := Real.rpow_nonneg (by unfold jbracket; positivity) _
  refine ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal ?_)
  nlinarith

lemma acc_w_le_kc {d : ℕ} (R : ℝ) (z z' : Fin d → ℤ) :
    ENNReal.ofReal (cellWeight d z') ≤ (kcCoef d R 1 1 z z' : ℝ≥0∞) := by
  refine ENNReal.ofReal_le_ofReal ?_
  have : (0 : ℝ) ≤ (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  nlinarith

theorem screened_comm_cell_proof : type_of% @HRS.Whole.screened_comm_cell := by
  intro d hd s hs0 hs1 m Λ Cb T χ χh hχ
  have hd2 : 2 ≤ d := by
    have h1 : (1 : ℝ) < d := by linarith
    exact_mod_cast h1
  obtain ⟨CF, hCF0, hCF⟩ := flow_lip_sep_proof hd m Cb T χ χh hχ
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.exp (CF * |T|) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLdef]; exact Real.one_le_exp (mul_nonneg hCF0 (abs_nonneg T))
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.exp (|Cb| * |T|) - 1 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    have : 1 ≤ Real.exp (|Cb| * |T|) := Real.one_le_exp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    rw [hBdef]; linarith
  obtain ⟨C1, hC10, hn1⟩ := cc_near1_proof hd2 hs0 hs1 m Λ χ χh hχ L B hL1 hB0
  obtain ⟨C2, hC20, hn2⟩ := cc_near2_proof hd2 hs0 hs1 m Λ χ χh hχ L B hL1 hB0
  obtain ⟨C0, hC00, hfar⟩ := far_core_proof hd hs0 (by linarith) m Λ χ χh hχ L B hL1 hB0
  obtain ⟨Ck, hCk0, hrow, hcol⟩ := kcCoef_sums_proof hd (8 + Real.sqrt d) 1 1 (by positivity)
    zero_le_one zero_le_one
  obtain ⟨Lχ, hLχ0, hLχ1, hLχ2⟩ := cutoff_lipschitz_proof χ χh hχ
  have hP1 : 0 ≤ C1 * L ^ (2 * d) := by positivity
  have hP2 : 0 ≤ C2 * L ^ (2 * d + 2) := by positivity
  refine ⟨4 * (C1 * L ^ (2 * d) + C2 * L ^ (2 * d + 2) + C0) + Ck + 1,
    fun b Ψ hb hΨ μ hμ τ hτ => ?_⟩
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : ℝ, Cs = 4 * (C1 * L ^ (2 * d) + C2 * L ^ (2 * d + 2) + C0) + Ck + 1 :=
    ⟨_, rfl⟩
  rw [← hCsdef]
  have hCs0 : 0 ≤ Cs := by rw [hCsdef]; linarith
  have hτ0 : 0 ≤ τ := hτ.1
  have hτT : τ ≤ |T| := le_trans hτ.2 (le_abs_self T)
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Cs * Real.exp (Cs * d * τ) := ⟨_, rfl⟩
  have hCsE : Cs ≤ E := by rw [hEdef]; exact acc_exp_ge hCs0 hτ0 d
  rw [← hEdef]
  obtain ⟨hlipF, hlipI, hsep⟩ := hCF b Ψ hb hΨ τ hτ
  have hexp : Real.exp (CF * τ) ≤ L := by
    rw [hLdef]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτT hCF0)
  have hlipL : ∀ x y : Euc d, ‖Ψ τ x - Ψ τ y‖ ≤ L * ‖x - y‖ := fun x y =>
    le_trans (hlipF x y) (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  have hlipIL : ∀ x y : Euc d,
      ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ L * ‖x - y‖ := fun x y =>
    le_trans (hlipI x y) (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  have hsepL : ∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (advCutoff χ Ψ τ z) →
      y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ z y) → 4 / L ≤ ‖x - y‖ := by
    intro z x y hx hy
    rw [hLdef]
    exact le_trans (sfa_sep_le hCF0 hτT) (hsep z x y hx hy)
  have hB : ‖Ψ τ 0‖ ≤ B := by
    rw [hBdef]
    refine le_trans (flow_origin_proof m Cb T b Ψ hb hΨ τ hτ)
      (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1)
    exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self Cb) hτ0)
      (mul_le_mul_of_nonneg_left hτT (abs_nonneg _))
  have hbij : Function.Bijective (Ψ τ) := hΨ.bij τ hτ
  have h1 := hn1 Ψ τ hbij hlipL hlipIL hsepL hB μ hμ
  have h2 := hn2 Ψ τ hbij hlipL hlipIL hsepL hB μ hμ
  have h3 := hfar Ψ τ hbij hlipL hlipIL hsepL hB μ hμ
  have hΦc : Continuous (Function.invFun (Ψ τ)) := f5_cont_of_lip _ L hL0 hlipIL
  have hC1 : C1 * L ^ (2 * d) ≤ Cs / 4 := by rw [hCsdef]; linarith
  have hC2 : C2 * L ^ (2 * d + 2) ≤ Cs / 4 := by rw [hCsdef]; linarith
  have hC0' : C0 ≤ Cs / 4 := by rw [hCsdef]; linarith
  have hCk' : Ck ≤ E := by rw [hCsdef] at hCsE; linarith
  refine ⟨fun z z' => kcCoef d (8 + Real.sqrt d) 1 1 z z', ?_, ?_, ?_⟩
  · exact le_trans hrow (ENNReal.ofReal_le_ofReal hCk')
  · intro z'
    exact le_trans (hcol z') (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hCk') zero_le)
  · intro j hj idx i ψ hψ z hfin
    obtain ⟨n1a, n1b⟩ := h1 j hj idx i ψ hψ z
    obtain ⟨n2a, n2b⟩ := h2 j hj idx i ψ hψ z
    have hfar' := fun j' : Fin d => h3 j hj idx j' ψ hψ z
    have hΛ2 : 0 ≤ Λ ^ 2 := sq_nonneg Λ
    -- cell-sum comparisons
    have hA1 : ENNReal.ofReal (C1 * L ^ (2 * d) * Λ ^ 2) * ∑' z', (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞) *
          (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 ≤
        ENNReal.ofReal (E * Λ ^ 2) * ∑' z', (kcCoef d (8 + Real.sqrt d) 1 1 z z' : ℝ≥0∞) *
          (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 :=
      acc_mono _ _ (mul_le_mul_of_nonneg_right (by linarith) hΛ2) _ _ _
        (fun z' => acc_kc_le_one_zero _ z z')
    have hA2 : ENNReal.ofReal (C2 * L ^ (2 * d + 2) * Λ ^ 2) *
          ∑' z', (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞) *
            (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 ≤
        ENNReal.ofReal (E / 4 * Λ ^ 2) * ∑' z', (kcCoef d (8 + Real.sqrt d) 1 1 z z' : ℝ≥0∞) *
          (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 :=
      acc_mono _ _ (mul_le_mul_of_nonneg_right (by linarith) hΛ2) _ _ _
        (fun z' => acc_kc_le_one_zero _ z z')
    have hA0 : ENNReal.ofReal (C0 * Λ ^ 2) * ∑' z', ENNReal.ofReal (cellWeight d z') *
          (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 ≤
        ENNReal.ofReal (E / 4 * Λ ^ 2) * ∑' z', (kcCoef d (8 + Real.sqrt d) 1 1 z z' : ℝ≥0∞) *
          (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 :=
      acc_mono _ _ (mul_le_mul_of_nonneg_right (by linarith) hΛ2) _ _ _
        (fun z' => acc_w_le_kc _ z z')
    have hfar1 := fun j' : Fin d => (hfar' j').1
    have hfarlt : ∀ j' : Fin d, ENNReal.ofReal (C0 * Λ ^ 2) * ∑' z', ENNReal.ofReal (cellWeight d z') *
          (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 < ⊤ := fun _ =>
      lt_of_le_of_lt (le_trans hA0 (by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        exact mul_le_mul_of_nonneg_right (by linarith) hΛ2)) hfin
    have hA1lt := lt_of_le_of_lt hA1 hfin
    have hA2lt : ENNReal.ofReal (C2 * L ^ (2 * d + 2) * Λ ^ 2) *
          ∑' z', (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞) *
            (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 < ⊤ :=
      lt_of_le_of_lt (le_trans hA2 (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hΛ2)) le_rfl)) hfin
    -- facts on the cutoffs
    obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, -, -⟩ :=
      advCutoff_facts_proof χ χh hχ Ψ τ L Lχ hL0 hlipIL ⟨hLχ1, hLχ2⟩ (latticePt z)
    have hz : ∀ y, advCutoff χ Ψ τ (latticePt z) y * (1 - advCutoff χh Ψ τ (latticePt z) y) = 0 := by
      intro y
      by_cases hy : ‖Function.invFun (Ψ τ) y - latticePt z‖ ≤ 6
      · rw [hf6 y hy]; ring
      · rw [hf5 y (by linarith [not_le.1 hy]), zero_mul]
    have hczc : Continuous (advCutoff χ Ψ τ (latticePt z)) :=
      hχ.1.1.continuous.comp (hΦc.sub continuous_const)
    have hchc : Continuous (advCutoff χh Ψ τ (latticePt z)) :=
      hχ.2.1.continuous.comp (hΦc.sub continuous_const)
    obtain ⟨hDc, -⟩ := regularDensity_bounds_proof hμ hj idx
    have hk2 := acc_k2 (s := s) (advCutoff χ Ψ τ (latticePt z)) (advCutoff χh Ψ τ (latticePt z))
      (fun y => partialDeriv idx μ y * ψ y) i (fun x => ⟨(hf1 x).1, (hf1 x).2⟩) hczc.measurable hz _ _
      (n2b hA2lt) (fun x hx j => (hfar' j).2 (hfarlt j) x hx)
      (acc_meas_far _ _ _ _ hczc.measurable hchc.measurable hDc.measurable hψ i)
      n2a (hfar1 i)
    refine ⟨n1b hA1lt, hk2.1, le_trans n1a hA1, ?_⟩
    refine le_trans hk2.2 ?_
    have hX := acc_four (E / 4 * Λ ^ 2) (∑' z', (kcCoef d (8 + Real.sqrt d) 1 1 z z' : ℝ≥0∞) *
      (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2)
    have e4 : 4 * (E / 4 * Λ ^ 2) = E * Λ ^ 2 := by ring
    rw [e4] at hX
    rw [← hX]
    exact add_le_add (mul_le_mul' le_rfl hA2) (mul_le_mul' le_rfl hA0)

end HRS.MH.Screened
