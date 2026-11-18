import HRS.MS.R26T8AR4c

/-!
# S8.2 T8A R4d: `parametrix = rawNewton(src f) + W` with `W` of class `Conormal 8 0 M (s-2)`
`r26t8a_R4_W_class`: `rawNewton β⁻¹ χ (src f)` is `Conormal 8 1 (2L) (s-2)` and `W = parametrix - rawNewton β⁻¹ χ (src f)` is `Conormal 8 0 (2L) (s-2)`
(`W = (center R_L - R_L) + localNewton E' + Σ_{j ≥ 1} localNewton F_j`, off the diagonal; every piece is log-free of order `s-2`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad HRS.MS.S82N

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_R4_W_class (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (chi : Euc d → ℝ)
    (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A → TestBound (testOrder d) A f →
      Conormal 8 1 (2 * (iterationCount d : ℝ)) (criticalS d - 2) (C * A) (rawNewton beta⁻¹ chi (r26t8a_R3_src f)) ∧
      Conormal 8 0 (2 * (iterationCount d : ℝ)) (criticalS d - 2) (C * A)
        (fun x y => r26t8a_parametrix (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f x y -
          rawNewton beta⁻¹ chi (r26t8a_R3_src f) x y) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : criticalS d < d := by unfold criticalS; linarith
  have hsd2 : criticalS d - 2 < d := by linarith
  have hM0 : (0 : ℝ) ≤ 2 * (iterationCount d : ℝ) := by positivity
  obtain ⟨L', hL'⟩ : ∃ L', iterationCount d = L' + 1 := ⟨iterationCount d - 1, by unfold iterationCount; omega⟩
  obtain ⟨CB, hCB0, hB⟩ := r26t8a_R4_lead_classes hd a beta ha hbeta hchi
  obtain ⟨C6, hC60, hC6⟩ := r26t8a_raw_newton_bound_same d hd 8 0 beta⁻¹ 0 (criticalS d) (inv_pos.2 hbeta) le_rfl hsd chi hchi
  obtain ⟨CC, hCC0, hCC⟩ := r26t8a_R4_center_smooth hchi hd a beta ha hbeta 8 1 (σ := criticalS d - 2) (M := 0) le_rfl hsd2
  obtain ⟨CZ, hCZ0, hCZ⟩ := r26t8a_newton_projection_same d hd 8 0 a beta 0 (criticalS d - 2) ha hbeta le_rfl hsd2 chi hchi
  obtain ⟨cl, hcl1, hcl⟩ := r26t8a_conormal_lower (d := d) 8 (0 + 1) 0 (criticalS d - 2 - 2)
  have hQ : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ j → j < iterationCount d →
      ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A → TestBound (testOrder d) A f →
      Conormal 8 0 (2 * (iterationCount d : ℝ)) (criticalS d - 2) (C * A)
        (localNewton (HRS.Whole.withDensityReal rho) (critCoeff d a beta rho).ν chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j))) := by
    intro j
    by_cases h : 1 ≤ j ∧ j < iterationCount d
    · obtain ⟨C, hC0, hC⟩ := r26t8a_R4_Qj_class hd a beta ha hbeta chi hchi j h.1 h.2
      exact ⟨C, hC0, fun _ _ => hC⟩
    · exact ⟨0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose CQ hCQ0 hCQ using hQ
  set K1 : ℝ := C6 * CB with hK1
  set K2 : ℝ := CC * K1 with hK2
  set K3 : ℝ := cl * (CZ * CB) with hK3
  set K4 : ℝ := ∑ j ∈ Finset.range L', CQ (j + 1) with hK4
  have hK40 : 0 ≤ K4 := Finset.sum_nonneg fun j _ => hCQ0 _
  have hK10 : 0 ≤ K1 := mul_nonneg hC60 hCB0
  have hK20 : 0 ≤ K2 := mul_nonneg hCC0 hK10
  have hK30 : 0 ≤ K3 := mul_nonneg (by linarith) (mul_nonneg hCZ0 hCB0)
  refine ⟨K1 + (K2 + K3 + K4), by linarith, fun rho hrho f A hA hf => ?_⟩
  have hnu : (critCoeff d a beta rho).ν = beta⁻¹ := r26t8a_critCoeff_nu a beta rho
  obtain ⟨hF0, hE, hLead⟩ := hB rho hrho f A hA hf
  have hCBA : 0 ≤ CB * A := mul_nonneg hCB0 hA
  -- the Newton potential of the leading source
  obtain ⟨-, hRL⟩ := hC6 _ (CB * A) hCBA hLead
  have hRL' : Conormal 8 1 0 (criticalS d - 2) (K1 * A) (rawNewton beta⁻¹ chi (r26t8a_R3_src f)) := by
    have : C6 * (CB * A) = K1 * A := by rw [hK1]; ring
    simpa [this] using hRL
  have hRLM : Conormal 8 1 (2 * (iterationCount d : ℝ)) (criticalS d - 2) ((K1 + (K2 + K3 + K4)) * A)
      (rawNewton beta⁻¹ chi (r26t8a_R3_src f)) := by
    have hK1A : 0 ≤ K1 * A := mul_nonneg hK10 hA
    refine r26t8a_conormal_mono_sA hK1A ?_ le_rfl (r26t8a_f23_conormal_M_mono hM0 hK1A hRL')
    exact mul_le_mul_of_nonneg_right (by linarith) hA
  refine ⟨hRLM, ?_⟩
  -- the smooth centring correction
  have hK1A : 0 ≤ K1 * A := mul_nonneg hK10 hA
  have hcorr := hCC rho hrho hK1A hRL' 0 (criticalS d - 2)
  have hcorr' : Conormal 8 0 (2 * (iterationCount d : ℝ)) (criticalS d - 2) (K2 * A)
      (fun x y => r2CenterKernel (HRS.Whole.withDensityReal rho) (rawNewton beta⁻¹ chi (r26t8a_R3_src f)) x y -
        rawNewton beta⁻¹ chi (r26t8a_R3_src f) x y) := by
    have : CC * (K1 * A) = K2 * A := by rw [hK2]; ring
    rw [this] at hcorr
    exact r26t8a_f23_conormal_M_mono hM0 (mul_nonneg hK20 hA) hcorr
  -- the potential of the remainder `E'`
  obtain ⟨-, hLN⟩ := hCZ rho hrho (fun x y => HSource (HRS.Whole.withDensityReal rho) f x y - r26t8a_R3_src f x y)
    (CB * A) hCBA hE
  have hLN' := hcl (CZ * (CB * A)) (mul_nonneg hCZ0 hCBA) hLN
  have hLN'' : Conormal 8 0 (2 * (iterationCount d : ℝ)) (criticalS d - 2) (K3 * A)
      (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi
        (fun x y => HSource (HRS.Whole.withDensityReal rho) f x y - r26t8a_R3_src f x y)) := by
    have hK3A : 0 ≤ K3 * A := mul_nonneg hK30 hA
    refine r26t8a_conormal_mono_sA (mul_nonneg (by linarith) (mul_nonneg hCZ0 hCBA))
      (le_of_eq (by rw [hK3] <;> ring)) ?_
      (r26t8a_f23_conormal_M_mono hM0 (mul_nonneg (by linarith) (mul_nonneg hCZ0 hCBA)) hLN')
    linarith
  -- the higher terms
  have hsum : Conormal 8 0 (2 * (iterationCount d : ℝ)) (criticalS d - 2) (K4 * A)
      (fun x y => ∑ j ∈ Finset.range L', localNewton (HRS.Whole.withDensityReal rho) (critCoeff d a beta rho).ν chi
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f (j + 1)) x y) := by
    have := r26t8a_conormal_sum hchi (Finset.range L') (k := 8) (b := 0) (M := 2 * (iterationCount d : ℝ))
      (σ := criticalS d - 2) (A := fun j => CQ (j + 1) * A)
      (F := fun j => localNewton (HRS.Whole.withDensityReal rho) (critCoeff d a beta rho).ν chi
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f (j + 1)))
      (fun j hj => hCQ (j + 1) (by omega) (by have := Finset.mem_range.1 hj; omega) rho hrho f A hA hf)
    rw [← Finset.sum_mul] at this
    exact this
  have hG := r26t8a_conormal_add hchi (r26t8a_conormal_add hchi hcorr' hLN'') hsum
  refine r26t8a_conormal_mono_sA (add_nonneg (add_nonneg (mul_nonneg hK20 hA) (mul_nonneg hK30 hA)) (mul_nonneg hK40 hA))
    (by nlinarith [mul_nonneg hK10 hA]) le_rfl (r26t8a_conormal_congr (fun x y hxy => ?_) hG)
  -- the identity off the diagonal
  have hE_s : Conormal 8 0 0 (criticalS d) (CB * A)
      (fun x y => HSource (HRS.Whole.withDensityReal rho) f x y - r26t8a_R3_src f x y) :=
    r26t8a_conormal_mono_sA hCBA le_rfl (by linarith) hE
  have e1 : r26t8a_parametrix (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f x y =
      ∑ j ∈ Finset.range (L' + 1), localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j) x y := by
    unfold r26t8a_parametrix
    simp only [Finset.sum_apply]
    rw [hL', hnu]
  have eF0 : localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi
      (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f 0) x y =
      r2CenterKernel (HRS.Whole.withDensityReal rho) (rawNewton beta⁻¹ chi (r26t8a_R3_src f)) x y +
        1 * localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi
          (fun x y => HSource (HRS.Whole.withDensityReal rho) f x y - r26t8a_R3_src f x y) x y := by
    have h0 : r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f 0 =
        HSource (HRS.Whole.withDensityReal rho) f := rfl
    rw [h0, r26t8a_T4_localNewton_congr hd rho beta⁻¹ chi
      (F2 := fun x y => r26t8a_R3_src f x y + 1 * (HSource (HRS.Whole.withDensityReal rho) f x y - r26t8a_R3_src f x y))
      (fun x y _ => by ring) hxy]
    rw [r26t8a_T2_localNewton_lin hd a beta 0 (criticalS d) ha hbeta le_rfl hsd 8 0 rho hrho hchi hCBA hCBA hLead hE_s 1 hxy]
    rfl
  rw [e1, Finset.sum_range_succ', eF0]
  simp only [hnu]
  ring

end HRS.MS.R26T8A
