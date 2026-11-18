import HRS.PDE.MeanFieldAdjointDuhamel
import HRS.PDE.MeanFieldGlobal
import HRS.PDE.MeanFieldDecayHr
import HRS.PDE.MeanFieldWeak
import HRS.PDE.MeanFieldThermal
import HRS.PDE.MeanFieldFejer
import HRS.PDE.MeanFieldThermalUnique
import HRS.PDE.MeanFieldInputs

/-!
# Wiring of Proposition 5.2 `C:prop:adjoint` (package MF-01, packet P11e)

See `HRS/PDE/MeanFieldAdjointPlan.md`, packet P11e.  The file collects the Proposition 5.1 facts
needed for the abstract adjoint decay `MFAdjoint.exists_adjoint_decay_abstract` (uniform constants
in `β ∈ [βm, βp]`), and proves `adjoint_decay_comparison_wiring`, which is the statement of
`HRS.PDE.adjoint_decay_comparison` (`HRS/PDE/MeanField.lean`).

The file imports the proof files of Proposition 5.1 and not `HRS.PDE.MeanField` itself, so that
`MeanField.lean` can import this file.  The thermal facts used are the proofs of
`finite_reg_thermal` and `finite_reg_thermal_unique` copied verbatim.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFAdjoint

variable {d : ℕ}

/-! ### Thermal facts for `FiniteRegHyp` -/

theorem wire_thermal_unique (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ ρβ' : Torus d → ℝ)
    (h1 : IsThermalDensity (periodicRiesz d s) V β ρβ) (c1 : Continuous ρβ) (p1 : ∀ x, 0 < ρβ x)
    (h2 : IsThermalDensity (periodicRiesz d s) V β ρβ') (c2 : Continuous ρβ')
    (p2 : ∀ x, 0 < ρβ' x) : ρβ' = ρβ := by
  rcases Nat.lt_or_ge d 2 with h | h
  · have hd1 : d = 1 := by omega
    exact MFThermalExist.thermal_unique' hd s H.hs0 H.hsd
      (MFInputs.mfKernelFacts_one hd1 s H.hs0 H.hsd) β (lt_of_lt_of_le H.hβm hβ.1) V ρβ ρβ'
      h1 c1 p1 h2 c2 p2
  · exact MFThermal.thermal_unique h s H.hs0 H.hsd β (lt_of_lt_of_le H.hβm hβ.1) V ρβ ρβ'
      h1 c1 p1 h2 c2 p2

theorem wire_thermal_memSobolev (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) :
    ∃ ρβ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) V β ρβ ∧
      Continuous ρβ ∧ (∀ x, 0 < ρβ x) ∧ MemSobolev K ρβ := by
  have hβ0 : 0 < β := lt_of_lt_of_le H.hβm hβ.1
  have hVc : Continuous V :=
    MFAux.continuous_of_isCk (H.hV.of_le (by exact_mod_cast (show (1 : ℕ) ≤ K + 2 by omega)))
  obtain ⟨ρ, hρ, hc, hp⟩ :=
    MFThermalAssembly.thermal_exists_continuous hd s H.hs0 H.hsd V hVc β hβ0
  exact ⟨ρ, hρ, hc, hp,
    MFThermalAssembly.thermal_memSobolev_all hd s H.hs0 H.hsd K V H.hV β hβ0 ρ hρ hc hp⟩

/-! ### Sup-norm bound from the `H^m` norm (`m > d/2`) -/

theorem wire_sup_le (m : ℝ) (hm : (d : ℝ) / 2 < m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c : Coeff d, MemHs m c → ∀ x, |toFun c x| ≤ A * hsNorm m c := by
  obtain ⟨A, hA0, hA⟩ := MFApriori.Aux.exists_l1_le (d := d) m hm
  refine ⟨A, hA0, fun c hc x => ?_⟩
  exact (MFProduct.abs_toFun_le c (hA c hc).1 x).trans (hA c hc).2

/-! ### The hypotheses of Proposition 5.2 from Proposition 5.1 -/

/-- The uniform constants of Proposition 5.1 that Proposition 5.2 needs: the frozen data
`(ρβ, V)` with bounds `Λ₀`, the lower bound `c₀`, and the exponential decay of `ρ^t - ρβ` in
`H^{j+d/2+2}` with rate `κ` and constant `Cd`, together with the uniform bounds for the
coefficient path. -/
theorem finiteReg_hypotheses (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j)
    (hK : 2 * j + 4 * d + 20 ≤ K) :
    ∃ (R : Regime) (Λ Λ₀ c₀ Cd κ : ℝ), 0 < c₀ ∧ 0 < κ ∧
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρc : ℝ → Coeff d), IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc →
      ∀ ρβ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) V β ρβ → Continuous ρβ →
        (∀ x, 0 < ρβ x) →
        FrozenHyp d s (j + mStar d + 2) βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρβ ∧
        (∀ T, 0 < T → AdjointData s j R 1 Λ (Torus.cbNorm (j + 3) V)
          (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) βp⁻¹ T (mfPath ρc)) ∧
        ∀ σ, 0 ≤ σ →
          MemHs ((j : ℝ) + (d : ℝ) / 2 + 2) (coeffOf (mfPath ρc σ) - coeffOf ρβ) ∧
          hsNorm ((j : ℝ) + (d : ℝ) / 2 + 2) (coeffOf (mfPath ρc σ) - coeffOf ρβ) ≤
            Cd * Real.exp (-κ * σ) := by
  -- arithmetic of the indices
  have hKd : (d : ℝ) / 2 < K := by linarith [H.hK]
  have hKr : 2 * (j : ℝ) + 4 * (d : ℝ) + 20 ≤ K := by exact_mod_cast hK
  have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hdr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm3 : (mStar d : ℝ) ≤ (d : ℝ) / 2 + 3 := by
    unfold mStar
    push_cast
    have := Nat.floor_le (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity)
    linarith
  have hnr : ((j + mStar d + 2 : ℕ) : ℝ) = (j : ℝ) + (mStar d : ℝ) + 2 := by push_cast; ring
  have hnn : (0 : ℝ) ≤ ((j + mStar d + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnK : j + mStar d + 2 ≤ K + 2 := by
    have h : ((j + mStar d + 2 : ℕ) : ℝ) ≤ ((K + 2 : ℕ) : ℝ) := by
      rw [hnr]; push_cast; linarith
    exact_mod_cast h
  have hK2 : (d : ℝ) / 2 + 2 < K := by linarith
  -- the two decay indices `rA = j + d/2 + 2` and `rB` (large, for the `C^n` bound)
  have hrA0 : (0 : ℝ) ≤ (j : ℝ) + (d : ℝ) / 2 + 2 := by positivity
  have hrAK : (j : ℝ) + (d : ℝ) / 2 + 2 < K := by linarith
  have hdrA : (d : ℝ) / 2 < (j : ℝ) + (d : ℝ) / 2 + 2 := by linarith
  obtain ⟨rB, hrB⟩ : ∃ r : ℝ, r = ((j + mStar d + 2 : ℕ) : ℝ) + (d : ℝ) / 2 + 1 := ⟨_, rfl⟩
  have hrB0 : (0 : ℝ) ≤ rB := by rw [hrB]; positivity
  have hrBK : rB < K := by rw [hrB, hnr]; linarith
  have hdnB : (d : ℝ) / 2 + ((j + mStar d + 2 : ℕ) : ℝ) < rB := by rw [hrB]; linarith
  have hdrB : (d : ℝ) / 2 < rB := by linarith
  have hdj : (d : ℝ) / 2 + ((j + 3 : ℕ) : ℝ) < K := by push_cast; linarith
  -- constants
  obtain ⟨cU, CU, hcU, hU⟩ := MFGlobal.finite_reg_uniform_bounds hd s βm βp K V ρ₀ H
  obtain ⟨Cd, κ, hCd, hκ, hDA⟩ := MFDecay.finite_reg_decay hd s βm βp K V ρ₀ H _ hrA0 hrAK
  obtain ⟨Cb, cb, hCb, hcb, hDB⟩ := MFDecay.finite_reg_decay hd s βm βp K V ρ₀ H rB hrB0 hrBK
  obtain ⟨Cn, hCn⟩ := toFun_isCk_le (d := d) (j + mStar d + 2) rB hdnB
  obtain ⟨Cj, hCj⟩ := toFun_isCk_le (d := d) (j + 3) (K : ℝ) hdj
  obtain ⟨A, hA0, hA⟩ := wire_sup_le (d := d) _ hdrA
  obtain ⟨R, hR⟩ : ∃ R : Regime, ∀ (M : Matrix (Fin d) (Fin d) ℝ) (invβ ν₀ T : ℝ)
      (μ : ℝ → Torus d → ℝ), 0 < ν₀ → ν₀ ≤ invβ → R.Holds d s M invβ ν₀ T μ := by
    rcases le_or_gt s ((d : ℝ) - 2) with h | h
    · exact ⟨.R1, fun _ _ _ _ _ _ _ => h⟩
    · exact ⟨.R3, fun _ _ _ _ _ h1 h2 => ⟨h, h1, h2⟩⟩
  refine ⟨R, max Cj 0 * CU, max (Torus.cbNorm (j + mStar d + 2) V) (max Cn 0 * (CU + Cb)),
    cU, Cd, κ, hcU, hκ, ?_⟩
  intro β hβ ρc hρc ρβ hρβ hρC hpos
  have hβpos : 0 < β := lt_of_lt_of_le H.hβm hβ.1
  have hβp : 0 < βp := lt_of_lt_of_le hβpos hβ.2
  have hνpos : 0 < βp⁻¹ := inv_pos.mpr hβp
  have hle : βp⁻¹ ≤ β⁻¹ := inv_anti₀ hβpos hβ.2
  have hν : β⁻¹ ∈ Set.Icc βp⁻¹ βm⁻¹ := ⟨hle, inv_anti₀ H.hβm hβ.1⟩
  have hreal := MFGlobal.isRealCoeff_of_isMFSolutionHK hd s βm βp K V ρ₀ H β hβ ρc hρc
  have hMemK : ∀ t, 0 ≤ t → MemHs (K : ℝ) (ρc t) := fun t ht => hρc.cont.1 t ht
  have hsumK : ∀ t, 0 ≤ t → Summable fun k => ‖ρc t k‖ := fun t ht =>
    summable_norm_of_memHs (K : ℝ) hKd _ (hMemK t ht)
  have hcoefPath : ∀ t, 0 ≤ t → coeffOf (mfPath ρc t) = ρc t := fun t ht =>
    coeffOf_toFun (ρc t) (hreal t ht) (hsumK t ht)
  have hUb := hU β hβ ρc hρc
  -- regularity of `ρβ`: it lies in `H^K`
  obtain ⟨ρ', hρ', c', p', hK'⟩ := wire_thermal_memSobolev hd s βm βp K V ρ₀ H β hβ
  have heq : ρ' = ρβ := wire_thermal_unique hd s βm βp K V ρ₀ H β hβ ρβ ρ' hρβ hρC hpos hρ' c' p'
  rw [heq] at hK'
  have hMK : MemSobolev (K : ℝ) ρβ := hK'
  have hMKc : MemHs (K : ℝ) (coeffOf ρβ) := (hsNormSq_coeffOf (K : ℝ) ρβ hMK).1
  have hrBle : rB ≤ K := hrBK.le
  have hMB : MemHs rB (coeffOf ρβ) := MemHs.mono hrBle hMKc
  have hreal0 : IsRealCoeff (coeffOf ρβ) := isRealCoeff_coeffOf ρβ (hMK.1.integrable one_le_two)
  have hsumB : Summable fun k => ‖coeffOf ρβ k‖ := summable_norm_of_memHs (K : ℝ) hKd _ hMKc
  have hρβ_eq : toFun (coeffOf ρβ) = ρβ := toFun_coeffOf ρβ hρC hsumB
  -- `C^n` bound for `ρβ`, uniform in `β`
  have hUb0 := hUb 0 le_rfl
  have hDB0 := hDB β hβ ρc hρc ρβ hρβ hρC hpos hMK 0 le_rfl
  have hsB : hsNorm rB (coeffOf ρβ) ≤ CU + Cb := by
    have hm0 : MemHs rB (ρc 0) := MemHs.mono hrBle (hMemK 0 le_rfl)
    calc hsNorm rB (coeffOf ρβ) = hsNorm rB (ρc 0 - (ρc 0 - coeffOf ρβ)) := by
          rw [sub_sub_cancel]
      _ ≤ hsNorm rB (ρc 0) + hsNorm rB (ρc 0 - coeffOf ρβ) := hsNorm_sub_le_add hm0 hDB0.1
      _ ≤ CU + Cb := by
          refine add_le_add ((MFApriori.hsNorm_mono_idx hrBle (hMemK 0 le_rfl)).trans hUb0.2) ?_
          exact hDB0.2.trans (le_of_eq (by simp))
  have hCnB := hCn (coeffOf ρβ) hMB hreal0
  rw [hρβ_eq] at hCnB
  have hCn' : Torus.cbNorm (j + mStar d + 2) ρβ ≤ max Cn 0 * (CU + Cb) := by
    refine hCnB.2.trans ?_
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (MFApriori.Aux.hsNorm_nonneg _ _)).trans (mul_le_mul_of_nonneg_left hsB (le_max_right _ _))
  -- lower bound `c₀ ≤ ρβ`, as a limit of `ρ^t`
  have hlim : ∀ x, Tendsto (fun t => mfPath ρc t x) atTop (𝓝 (ρβ x)) := by
    intro x
    have hbnd : ∀ t, 0 ≤ t → |mfPath ρc t x - ρβ x| ≤ A * Cd * Real.exp (-κ * t) := by
      intro t ht
      have e1 : toFun (ρc t - coeffOf ρβ) x = mfPath ρc t x - ρβ x := by
        rw [MFApriori.Aux.toFun_sub (ρc t) (coeffOf ρβ) (hsumK t ht) hsumB x,
          ← congrFun hρβ_eq x]
        rfl
      have hD := hDA β hβ ρc hρc ρβ hρβ hρC hpos hMK t ht
      calc |mfPath ρc t x - ρβ x| = |toFun (ρc t - coeffOf ρβ) x| := by rw [e1]
        _ ≤ A * hsNorm _ (ρc t - coeffOf ρβ) := hA _ hD.1 x
        _ ≤ A * (Cd * Real.exp (-κ * t)) := mul_le_mul_of_nonneg_left hD.2 hA0
        _ = A * Cd * Real.exp (-κ * t) := by ring
    have hexp : Tendsto (fun t : ℝ => A * Cd * Real.exp (-κ * t)) atTop (𝓝 0) := by
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hκ)).const_mul (A * Cd)
      rw [mul_zero] at h
      refine Tendsto.congr (fun t => ?_) h
      simp [neg_mul]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hexp
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Real.norm_eq_abs]
    exact hbnd t ht
  have hlow : ∀ x, cU ≤ ρβ x := fun x =>
    ge_of_tendsto (hlim x) (eventually_atTop.2 ⟨0, fun t ht => ((hUb t ht).1 x).1⟩)
  -- the frozen hypothesis
  have hVn : Torus.IsCk (j + mStar d + 2) V :=
    H.hV.of_le (by exact_mod_cast (show j + mStar d + 2 ≤ K + 2 from hnK))
  have hFz : FrozenHyp d s (j + mStar d + 2) βp⁻¹ βm⁻¹ cU
      (max (Torus.cbNorm (j + mStar d + 2) V) (max Cn 0 * (CU + Cb))) β V ρβ :=
    ⟨H.hs0, H.hsd, hβpos, hνpos, hν, hVn, le_max_left _ _, hρβ, hCnB.1,
      (hCn'.trans (le_max_right _ _)), hcU, hlow⟩
  -- the adjoint data
  have hMBd : MatBound 1 (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)).M :=
    fun i k => by
      show |(-1 : Matrix (Fin d) (Fin d) ℝ) i k| ≤ 1
      rw [Matrix.neg_apply, Matrix.one_apply]
      split_ifs <;> norm_num
  have hVj : Torus.IsCk (j + 3) V := H.hV.of_le (by exact_mod_cast (show j + 3 ≤ K + 2 by omega))
  have hAD : ∀ T, 0 < T → AdjointData s j R 1 (max Cj 0 * CU) (Torus.cbNorm (j + 3) V)
      (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) βp⁻¹ T (mfPath ρc) := by
    intro T hT
    have hcoh : CoeffHyp j (max Cj 0 * CU) T (mfPath ρc) := by
      refine ⟨fun r hr => MFWeak.isProbDensity_mfPath hd s βm βp K V ρ₀ H β hβ ρc hρc r hr.1,
        fun r hr => ?_, fun r hr => ?_, fun ψ hψ => ?_⟩
      · exact (hCj (ρc r) (hMemK r hr.1) (hreal r hr.1)).1
      · have h1 := (hCj (ρc r) (hMemK r hr.1) (hreal r hr.1)).2
        have h2 : hsNorm (K : ℝ) (ρc r) ≤ CU := (hU β hβ ρc hρc r hr.1).2
        calc Torus.cbNorm (j + 3) (mfPath ρc r) ≤ Cj * hsNorm (K : ℝ) (ρc r) := h1
          _ ≤ max Cj 0 * hsNorm (K : ℝ) (ρc r) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (MFApriori.Aux.hsNorm_nonneg _ _)
          _ ≤ max Cj 0 * CU := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      · exact (MFWeak.continuousOn_pairings hd s H.hs0 H.hsd K hK2 V ρ₀ H.hV β⁻¹ ρc
          ⟨MFApriori.IsMFSolutionHK.toSolOn hρc T, fun τ hτ => hreal τ hτ.1⟩ ψ hψ).1
    have hreg : R.Holds d s (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)).M
        (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)).invβ βp⁻¹ T (mfPath ρc) :=
      hR _ _ _ _ _ hνpos hle
    exact ⟨rfl, hMBd, ⟨hVj, le_rfl⟩, hcoh, hT, hreg⟩
  refine ⟨hFz, hAD, ?_⟩
  intro σ hσ
  rw [hcoefPath σ hσ]
  exact hDA β hβ ρc hρc ρβ hρβ hρC hpos hMK σ hσ

/-- Proposition 5.2 (`C:prop:adjoint`), in the form of `HRS.PDE.adjoint_decay_comparison`: the
uniform adjoint decay and comparison estimates, for the propagator of the solution `ρ^t` of
Proposition 5.1. -/
theorem adjoint_decay_comparison_wiring (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (j : ℕ) (_hjeven : Even j) (hj : (d : ℝ) / 2 + 4 < j)
    (hK : 2 * j + 4 * d + 20 ≤ K) :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρc : ℝ → Coeff d) (_ : IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc)
        (ρβ : Torus d → ℝ) (_ : IsThermalDensity (periodicRiesz d s) V β ρβ) (_ : Continuous ρβ)
        (_ : ∀ x, 0 < ρβ x) (φ : Torus d → ℝ) (_ : Continuous φ) (_ : MemSobolev j φ)
        (r t : ℝ) (_ : 0 ≤ r) (_ : r ≤ t),
        MemSobolev j (projMean (withDensityReal ρβ)
          (propagator (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) (mfPath ρc) r t φ)) ∧
        sobolevNorm j (projMean (withDensityReal ρβ)
            (propagator (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) (mfPath ρc) r t φ)) ≤
          C * Real.exp (-c * (t - r)) * sobolevNorm j (projMean (withDensityReal ρβ) φ) ∧
        sobolevNorm j (fun x => projMean (withDensityReal ρβ)
            (propagator (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) (mfPath ρc) r t φ) x -
          equilibriumSemigroup (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ (t - r)
            (projMean (withDensityReal ρβ) φ) x) ≤
          C * Real.exp (-c * (t - r)) * Real.exp (-κ * r) *
            sobolevNorm j (projMean (withDensityReal ρβ) φ) := by
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hall⟩ := finiteReg_hypotheses hd s βm βp K V ρ₀ H j hj hK
  obtain ⟨C, c, hC, hc, hmain⟩ := exists_adjoint_decay_abstract hd s j hj βp⁻¹ βm⁻¹ c₀ Λ₀
    ((j : ℝ) + (d : ℝ) / 2 + 2) (by linarith) R 1 Λ (Torus.cbNorm (j + 3) V) Cd κ hκ
  refine ⟨C, c, κ, hC, hc, hκ, ?_⟩
  intro β hβ ρc hρc ρβ hρβ hρC hpos φ hφc hφ r t hr hrt
  obtain ⟨HF, hAD, hdec⟩ := hall β hβ ρc hρc ρβ hρβ hρC hpos
  exact hmain β V ρβ HF (mfPath ρc) hAD hdec φ hφc hφ r t hr hrt

end HRS.PDE.MFAdjoint
