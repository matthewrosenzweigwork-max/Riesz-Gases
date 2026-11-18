import HRS.MS.SA12X4V3
import HRS.MS.SA12X4W6

/-!
# S.A.12 (SA12X4) V4: the weighted `varpiNormE` bound for a periodic solution

`sa12x4_periodic_varpi`: `‖F(τ)‖_{H^m(ϖ)} ≤ C e^{Λ_mτ} ‖F(0)‖_{H^m(ϖ)}` with `Λ_m = lambdaM C ν₀ θ`, for the `L`-periodic classical
solutions of the periodic approximants (`L ≥ L₁`).  From W6 (`cellWeighted` Gronwall) and the two-sided comparison of
`cellWeighted` with `varpiNormE²` through the continuous weighted jet energy (V1-V3).
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Near HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x4_periodic_varpi (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C L₁ : ℝ, 0 < C ∧ ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ)
      (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d), L₁ ≤ L → PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b →
      RdRegimeHolds Rg d s M ν ν₀ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ F : ℝ → Euc d → ℝ,
        IsPerSol m L γ M ν μ b (fun _ _ => 0) t F → ∀ τ ∈ Icc (0 : ℝ) t,
          varpiNormE m χ (F τ) ≤
            ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ)) * varpiNormE m χ (F 0) := by
  classical
  obtain ⟨χh, hχp⟩ := sa12x3_cutoffPair hχ
  obtain ⟨C6, L6, hC6, h6⟩ := sa12x4_periodic_cellWeighted hd s hs0 hsd m hm Rg MB Λ ΛV νbar Cb T χ hχ
  obtain ⟨KA, hKA0, hA⟩ := sa12x4_varpi_le_J hd m χ hχ
  obtain ⟨KB, hKB0, hB⟩ := sa12x4_J_le_varpi hd m χ hχ
  obtain ⟨KD, hKD0, hD⟩ := sa12x4_W0_le_J hd m χ hχ
  set p : ℝ := (d : ℝ) + 3 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set cT : ℝ := (4 * Real.exp (Cb * T)) ^ (-p) with hcT
  have hcT0 : 0 < cT := Real.rpow_pos_of_pos (by positivity) _
  set Kall : ℝ := KA * cT⁻¹ * (KD * KB) with hKall
  have hKall0 : 0 ≤ Kall := by rw [hKall]; positivity
  set C : ℝ := max (Real.sqrt Kall) C6 + 1 with hCdef
  have hCpos : 0 < C := by
    have : 0 ≤ max (Real.sqrt Kall) C6 := (le_max_right _ _).trans' hC6.le
    rw [hCdef]; linarith
  refine ⟨C, L6, hCpos, ?_⟩
  intro ν₀ L γ M ν μ V b hL hPD hR t ht F hF τ hτ
  have hT : 0 ≤ T := ht.1.le.trans ht.2
  have hb := hPD.b_drift
  have hCb : 0 ≤ Cb := HRS.MS.UniqC3.uc3_Cb_nonneg hT hb
  obtain ⟨Ψ, hΨ⟩ := HRS.MS.UniqG2d.g2d_flow hT hb
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans ht.2⟩
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht.1.le⟩
  have h0T : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hsm : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (F σ) := fun σ hσ => (hF.sol.smooth σ hσ).1
  have hint : ∀ σ ∈ Icc (0 : ℝ) T, ∀ (hs : σ ∈ Icc (0 : ℝ) t) (z : Fin d → ℤ) {j : ℕ} (idx : Fin j → Fin d),
      Integrable (fun x => (advCutoff χ Ψ σ (cellPt d z) x * partialDeriv idx (F σ) x) ^ 2) :=
    fun σ hσ hs z j idx => sa12x3_adv_cut_integrable hχp.1.1 hχp.1.2.1 hb hΨ hσ (cellPt d z) (hsm σ hs) idx
  -- the chain for the squares
  have hW := h6 ν₀ L γ M ν μ V b hL hPD hR t ht F hF Ψ hΨ τ hτ
  have hJW := sa12x4_J_le_W hd hT hb hΨ χ hχ hτT (hsm τ hτ) (hint τ hτT hτ)
  have hcle : ENNReal.ofReal cT ≤ ENNReal.ofReal ((4 * Real.exp (Cb * τ)) ^ (-p)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    have : Real.exp (Cb * τ) ≤ Real.exp (Cb * T) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτT.2 hCb)
    linarith
  have hW0 := hD hΨ (hsm 0 h0t) (hint 0 h0T h0t)
  have hB0 := hB (hsm 0 h0t)
  have hA1 := hA (hsm τ hτ)
  set Wτ : ℝ≥0∞ := ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
    ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d y) (F τ)) with hWτ
  have hJle : sa12x4_J m (F τ) ≤ ENNReal.ofReal cT⁻¹ * Wτ := by
    calc sa12x4_J m (F τ) = ENNReal.ofReal cT⁻¹ * (ENNReal.ofReal cT * sa12x4_J m (F τ)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hcT0.le), inv_mul_cancel₀ hcT0.ne']; simp
      _ ≤ ENNReal.ofReal cT⁻¹ * Wτ := by
          gcongr
          exact le_trans (by gcongr) hJW
  have hsq : varpiNormE m χ (F τ) ^ 2 ≤
      ENNReal.ofReal (Kall * Real.exp (Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ)) * varpiNormE m χ (F 0) ^ 2 := by
    calc varpiNormE m χ (F τ) ^ 2 ≤ ENNReal.ofReal KA * sa12x4_J m (F τ) := hA1
      _ ≤ ENNReal.ofReal KA * (ENNReal.ofReal cT⁻¹ * Wτ) := by gcongr
      _ ≤ ENNReal.ofReal KA * (ENNReal.ofReal cT⁻¹ * (ENNReal.ofReal (Real.exp (Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ)) *
            (ENNReal.ofReal KD * (ENNReal.ofReal KB * varpiNormE m χ (F 0) ^ 2)))) := by
          gcongr
          refine hW.trans ?_
          gcongr
          refine hW0.trans ?_
          gcongr
      _ = ENNReal.ofReal (Kall * Real.exp (Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ)) * varpiNormE m χ (F 0) ^ 2 := by
          rw [hKall, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hKD0]
          ring
  -- the square root
  have e1 : ∀ x : ℝ≥0∞, (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have h1 := ENNReal.rpow_le_rpow hsq (z := 1 / 2) (by norm_num)
  rw [e1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e1,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)] at h1
  refine h1.trans ?_
  gcongr
  obtain ⟨k0, hk01, hk0lam⟩ := sa12x3_lam_lin hR (PDE.thetaOrder d s)
  have hΛ6 : 0 ≤ Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) := by rw [hk0lam]; exact mul_nonneg hC6.le (by linarith)
  have hC6C : C6 ≤ C := by
    have : C6 ≤ max (Real.sqrt Kall) C6 := le_max_right _ _
    rw [hCdef]; linarith
  have hΛ := sa12x3_lam_ge hR hC6C (PDE.thetaOrder d s)
  have hΛle : Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) ≤ Rg.lambdaM C ν₀ (PDE.thetaOrder d s) := by
    linarith
  have he1 : 1 ≤ Real.exp (Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ) := Real.one_le_exp (mul_nonneg hΛ6 hτ.1)
  have hexp : Real.exp (Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ) ≤
      Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hΛle hτ.1)
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hKall0]
  have hsqe : Real.sqrt (Real.exp (Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ)) ≤
      Real.exp (Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨(Real.exp_pos _).le, by nlinarith⟩
  have hsK : Real.sqrt Kall ≤ C := by
    have : Real.sqrt Kall ≤ max (Real.sqrt Kall) C6 := le_max_left _ _
    rw [hCdef]; linarith
  calc Real.sqrt Kall * Real.sqrt (Real.exp (Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ))
      ≤ Real.sqrt Kall * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) :=
        mul_le_mul_of_nonneg_left (hsqe.trans hexp) (Real.sqrt_nonneg _)
    _ ≤ C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) :=
        mul_le_mul_of_nonneg_right hsK (Real.exp_pos _).le

end HRS.MH.AdjointRd.Phase2SA12X4
