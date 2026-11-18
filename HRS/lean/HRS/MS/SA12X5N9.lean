import HRS.MS.SA12X5N8
import HRS.MS.ToriCoefAAux4

/-!
# S.A.12 X5 N9: the operator bound for the nonlocal difference term in cell-energy form
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near
  HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRdP HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_Tfar_smul (L : ℝ) (γ : Euc d → ℝ) (c : Euc d) (η μ F : Euc d → ℝ) (k : ℝ) {n : ℕ}
    (idx : Fin n → Fin d) (i j : Fin d) (x : Euc d) :
    sa12x3_Tfar L γ c η (fun y => k * μ y) F idx i j x = k * sa12x3_Tfar L γ c η μ F idx i j x := by
  unfold sa12x3_Tfar
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem sa12x5_Tfar_zero (L : ℝ) (γ : Euc d → ℝ) (c : Euc d) (η F : Euc d → ℝ) {n : ℕ}
    (idx : Fin n → Fin d) (i j : Fin d) (x : Euc d) :
    sa12x3_Tfar L γ c η (fun _ => (0 : ℝ)) F idx i j x = 0 := by
  have := sa12x5_Tfar_smul L γ c η (fun _ => (1 : ℝ)) F 0 idx i j x
  simpa using this

theorem sa12x5_nonlocal_diff_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) (E : Finset (Fin d → ℤ))
    (hE : CoversBall8 E) :
    ∃ C L₁ : ℝ, 0 ≤ C ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T,
      ∀ (L : ℝ) (γ : Euc d → ℝ), L₁ ≤ L → HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
      ∀ M : Matrix (Fin d) (Fin d) ℝ, PDE.MatBound MB M → ∀ (a F : Euc d → ℝ),
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ F → (∀ (x : Euc d) (k : Fin d → ℤ), a (x + L • latticePt k) = a x) →
      (∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) → BddJets m F →
      ∀ A : ℝ, 0 ≤ A → (∀ j ≤ m + 2, ∀ y, ‖iteratedFDeriv ℝ j a y‖ ≤ A) →
      (∀ j ≤ m + 2, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j a x‖ ≤ A) →
      ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
        (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal C) ∧
        (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
          ENNReal.ofReal C * ENNReal.ofReal (cellWeight d z')) ∧
        ∀ z : Fin d → ℤ, jetSq m (advCutoff χ Ψ τ (cellPt d z)) (fun x => perNonlocal L γ M a F x) ≤
          C * A ^ 2 * (∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F +
            (∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)).toReal) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C8, L8, hC80, h8⟩ := sa12x5_perNL_idx hd hs0 hsd m Cb T χ χh hχ E hE
  obtain ⟨Cs, Lf, hCs, hfar⟩ := sa12x5_far_kernel hd hs0 hsd m hm 1 Cb T χ χh hχ
  set G : ℝ := ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun j _ => by positivity
  set C' : ℝ := G * (C8 * MB ^ 2 + 3 * (d : ℝ) ^ 4 * MB ^ 2 * Cs) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  refine ⟨Cs + C', max L8 Lf, by positivity, ?_⟩
  intro b Ψ hb hΨ τ hτ L γ hL hγ M hM a F ha hF hap hFp hFB A hA0 hAs hAd
  have hL8 : L8 ≤ L := (le_max_left _ _).trans hL
  have hLf : Lf ≤ L := (le_max_right _ _).trans hL
  -- the common conclusion given a Schur kernel and the far bound
  have fin : ∀ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
      (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal Cs) →
      (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
        ENNReal.ofReal Cs * ENNReal.ofReal (cellWeight d z')) →
      (∀ z : Fin d → ℤ, ∀ n ≤ m, ∀ (idx : Fin n → Fin d) (i j : Fin d),
        ∫ x, (advCutoff χ Ψ τ (cellPt d z) x * sa12x3_Tfar L γ (Ψ τ (cellPt d z))
          (advCutoff χh Ψ τ (cellPt d z)) a F idx i j x) ^ 2 ≤
          A ^ 2 * (Cs * (∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)).toReal)) →
      ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
        (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal (Cs + C')) ∧
        (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
          ENNReal.ofReal (Cs + C') * ENNReal.ofReal (cellWeight d z')) ∧
        ∀ z : Fin d → ℤ, jetSq m (advCutoff χ Ψ τ (cellPt d z)) (fun x => perNonlocal L γ M a F x) ≤
          (Cs + C') * A ^ 2 * (∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F +
            (∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)).toReal) := by
    intro Kc hrow hcol hTf
    refine ⟨Kc, hrow.trans (ENNReal.ofReal_le_ofReal (by linarith)), fun z' => (hcol z').trans ?_, fun z => ?_⟩
    · gcongr
      linarith
    · set Sg : ℝ := ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F with hSg
      set Ms : ℝ := (∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)).toReal with hMs
      have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun k _ => sa12x2_cellEnergy_nonneg (m + 2) χ Ψ τ _ F
      have hMs0 : 0 ≤ Ms := ENNReal.toReal_nonneg
      set B1 : ℝ := C8 * MB ^ 2 * A ^ 2 * Sg + 3 * (d : ℝ) ^ 4 * MB ^ 2 * (A ^ 2 * (Cs * Ms)) with hB1
      have hidx : ∀ n ≤ m, ∀ idx : Fin n → Fin d, ∫ x, (advCutoff χ Ψ τ (cellPt d z) x *
          partialDeriv idx (fun x => perNonlocal L γ M a F x) x) ^ 2 ≤ B1 := fun n hn idx =>
        h8 b Ψ hb hΨ τ hτ L γ hL8 hγ M MB hM a F ha hF hap hFp A hA0
          (fun j hj y => hAs j (by omega) y) z n hn idx _ (fun i j => hTf z n hn idx i j)
      have hB10 : 0 ≤ B1 := by positivity
      unfold jetSq
      calc ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
            ∫ x, (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx (fun x => perNonlocal L γ M a F x) x) ^ 2
          ≤ ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ((d : ℝ) ^ j * B1) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            calc ∑ idx : Fin j → Fin d, ∫ x, (advCutoff χ Ψ τ (cellPt d z) x *
                  partialDeriv idx (fun x => perNonlocal L γ M a F x) x) ^ 2
                ≤ ∑ _idx : Fin j → Fin d, B1 := Finset.sum_le_sum fun idx _ => hidx j hj' idx
              _ = (d : ℝ) ^ j * B1 := by simp
        _ = G * B1 := by
            rw [hG, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ ≤ (Cs + C') * A ^ 2 * (Sg + Ms) := by
            have e1 : G * B1 = A ^ 2 * ((G * C8 * MB ^ 2) * Sg + (G * (3 * (d : ℝ) ^ 4 * MB ^ 2 * Cs)) * Ms) := by
              rw [hB1]; ring
            have e2 : (G * C8 * MB ^ 2) * Sg + (G * (3 * (d : ℝ) ^ 4 * MB ^ 2 * Cs)) * Ms ≤
                (Cs + C') * (Sg + Ms) := by
              have h1 : G * C8 * MB ^ 2 ≤ Cs + C' := by
                rw [hC']; nlinarith [mul_nonneg hG0 (mul_nonneg (by positivity : (0:ℝ) ≤ 3 * (d : ℝ) ^ 4 * MB ^ 2) hCs)]
              have h2 : G * (3 * (d : ℝ) ^ 4 * MB ^ 2 * Cs) ≤ Cs + C' := by
                rw [hC']; nlinarith [mul_nonneg hG0 (mul_nonneg hC80 (sq_nonneg MB)), hCs]
              nlinarith [mul_le_mul_of_nonneg_right h1 hSg0, mul_le_mul_of_nonneg_right h2 hMs0]
            rw [e1]
            nlinarith [mul_le_mul_of_nonneg_left e2 (sq_nonneg A)]
  by_cases hA : A = 0
  · -- `a = 0`
    have ha0 : a = fun _ => (0 : ℝ) := by
      funext y
      have := hAs 0 (by omega) y
      rw [hA, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      exact abs_nonpos_iff.1 this
    refine fin (fun _ _ => 0) (by simp) (by simp) ?_
    intro z n hn idx i j
    rw [ha0]
    simp only [sa12x5_Tfar_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, hA]
    simp
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
    obtain ⟨μ', hμ'⟩ : ∃ μ' : Euc d → ℝ, μ' = fun y => A⁻¹ * a y := ⟨_, rfl⟩
    have ha_eq : a = fun y => A * μ' y := by
      rw [hμ']; funext y; field_simp
    have ha2 : ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) a := sa12z3_cd_of_inf ha (m + 2)
    have hμ'c : ContDiff ℝ ∞ μ' := by rw [hμ']; exact contDiff_const.mul ha
    have hμ'p : ∀ (x : Euc d) (k : Fin d → ℤ), μ' (x + L • latticePt k) = μ' x := by
      intro x k; simp only [hμ']; rw [hap x k]
    have hμ'd : ∀ j ≤ m + 2, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j μ' x‖ ≤ 1 := by
      intro j hj x
      obtain ⟨k, hk⟩ := hAd j hj x
      refine ⟨k, ?_⟩
      have hnorm : ‖iteratedFDeriv ℝ j μ' x‖ = A⁻¹ * ‖iteratedFDeriv ℝ j a x‖ := by
        rw [hμ']
        have := HRS.MS.ToriCoefA.tca_const_mul_norm a (m + 2) ha2 A⁻¹ j hj x
        rw [this, abs_of_pos (inv_pos.2 hApos)]
      rw [hnorm]
      calc jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * (A⁻¹ * ‖iteratedFDeriv ℝ j a x‖)
          = A⁻¹ * (jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j a x‖) := by ring
        _ ≤ A⁻¹ * A := mul_le_mul_of_nonneg_left hk (inv_pos.2 hApos).le
        _ = 1 := inv_mul_cancel₀ hA
    obtain ⟨Kfin, hrow, hcol, hmain⟩ := hfar b Ψ hb hΨ L γ hLf hγ μ' hμ'c hμ'p hμ'd τ hτ
    refine fin Kfin hrow hcol ?_
    intro z n hn idx i j
    have hpt : ∀ x, (advCutoff χ Ψ τ (cellPt d z) x * sa12x3_Tfar L γ (Ψ τ (cellPt d z))
        (advCutoff χh Ψ τ (cellPt d z)) a F idx i j x) ^ 2 =
        A ^ 2 * (advCutoff χ Ψ τ (cellPt d z) x * sa12x3_Tfar L γ (Ψ τ (cellPt d z))
        (advCutoff χh Ψ τ (cellPt d z)) μ' F idx i j x) ^ 2 := by
      intro x
      have := sa12x5_Tfar_smul L γ (Ψ τ (cellPt d z)) (advCutoff χh Ψ τ (cellPt d z)) μ' F A idx i j x
      rw [← ha_eq] at this
      rw [this]; ring
    simp_rw [hpt]
    rw [integral_const_mul]
    have := hmain F hFB hFp z n hn idx i j
    calc A ^ 2 * ∫ x, (advCutoff χ Ψ τ (cellPt d z) x * sa12x3_Tfar L γ (Ψ τ (cellPt d z))
          (advCutoff χh Ψ τ (cellPt d z)) μ' F idx i j x) ^ 2
        ≤ A ^ 2 * (Cs * 1 ^ 2 * (∑' z', (Kfin z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)).toReal) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12X5
