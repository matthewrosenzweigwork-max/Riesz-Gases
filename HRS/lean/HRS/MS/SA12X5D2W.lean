import HRS.MS.SA12X5D2WB
import HRS.MS.SA12X4V4

/-!
# S.A.12 X5 D2W: the periodic weighted (`varpi`) energy bound with a source term

`sa12x5_periodic_source_varpi`: `‖F τ‖²_{H^m(ϖ)} ≤ C e^{2λτ} τ ∫₀^τ Hf` for a periodic solution with source and zero datum,
whenever the weighted sum of the moving cell energies of the source is `≤ Hf σ`.  From `sa12x5_periodic_cellWeighted_src` and the
comparison chain of `sa12x4_periodic_varpi` (V4).
-/

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Near HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12X4

variable {d : ℕ}

theorem sa12x5_periodic_source_varpi (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C L₁ : ℝ, 0 < C ∧ ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ)
      (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d), L₁ ≤ L → PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b →
      RdRegimeHolds Rg d s M ν ν₀ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ (Sc F : ℝ → Euc d → ℝ),
        IsPerSol m L γ M ν μ b Sc t F → (∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (Sc τ)) →
        F 0 = (fun _ => (0 : ℝ)) → ∀ Hf : ℝ → ℝ, (∀ σ ∈ Icc (0 : ℝ) t, 0 ≤ Hf σ) →
        IntegrableOn Hf (Icc (0 : ℝ) t) →
        (∀ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow T b Ψ → ∀ σ ∈ Icc (0 : ℝ) t,
          ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ENNReal.ofReal (cellEnergy m χ Ψ σ (cellPt d z) (Sc σ)) ≤ ENNReal.ofReal (Hf σ)) →
        ∀ τ ∈ Icc (0 : ℝ) t,
          (varpiNormE m χ (F τ)) ^ 2 ≤
            ENNReal.ofReal (C * Real.exp (2 * Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) * τ *
              ∫ σ in Icc (0 : ℝ) τ, Hf σ) := by
  classical
  obtain ⟨χh, hχp⟩ := sa12x3_cutoffPair hχ
  obtain ⟨C6, L6, hC6, h6⟩ := sa12x5_periodic_cellWeighted_src hd s hs0 hsd m hm Rg MB Λ ΛV νbar Cb T χ hχ
  obtain ⟨KA, hKA0, hA⟩ := sa12x4_varpi_le_J hd m χ hχ
  set p : ℝ := (d : ℝ) + 3 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set cT : ℝ := (4 * Real.exp (Cb * T)) ^ (-p) with hcT
  have hcT0 : 0 < cT := Real.rpow_pos_of_pos (by positivity) _
  set Kall : ℝ := KA * cT⁻¹ with hKall
  have hKall0 : 0 ≤ Kall := by rw [hKall]; positivity
  set C : ℝ := Kall * C6 + C6 + 1 with hCdef
  have hCpos : 0 < C := by
    have : 0 ≤ Kall * C6 := mul_nonneg hKall0 hC6.le
    rw [hCdef]; linarith
  refine ⟨C, L6, hCpos, ?_⟩
  intro ν₀ L γ M ν μ V b hL hPD hR t ht Sc F hF hSs hF0 Hf hHf0 hHfi hHf τ hτ
  have hT : 0 ≤ T := ht.1.le.trans ht.2
  have hb := hPD.b_drift
  have hCb : 0 ≤ Cb := HRS.MS.UniqC3.uc3_Cb_nonneg hT hb
  obtain ⟨Ψ, hΨ⟩ := HRS.MS.UniqG2d.g2d_flow hT hb
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans ht.2⟩
  have hsm : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (F σ) := fun σ hσ => (hF.sol.smooth σ hσ).1
  have hint : ∀ σ ∈ Icc (0 : ℝ) T, ∀ (hs : σ ∈ Icc (0 : ℝ) t) (z : Fin d → ℤ) {j : ℕ} (idx : Fin j → Fin d),
      Integrable (fun x => (advCutoff χ Ψ σ (cellPt d z) x * partialDeriv idx (F σ) x) ^ 2) :=
    fun σ hσ hs z j idx => sa12x3_adv_cut_integrable hχp.1.1 hχp.1.2.1 hb hΨ hσ (cellPt d z) (hsm σ hs) idx
  have hW := h6 ν₀ L γ M ν μ V b hL hPD hR t ht Sc F hF hSs hF0 Hf hHf0 hHfi Ψ hΨ (hHf Ψ hΨ) τ hτ
  have hJW := sa12x4_J_le_W hd hT hb hΨ χ hχ hτT (hsm τ hτ) (hint τ hτT hτ)
  have hcle : ENNReal.ofReal cT ≤ ENNReal.ofReal ((4 * Real.exp (Cb * τ)) ^ (-p)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    have : Real.exp (Cb * τ) ≤ Real.exp (Cb * T) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτT.2 hCb)
    linarith
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
      ENNReal.ofReal (Kall * (C6 * Real.exp (2 * Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ) * τ *
        ∫ σ in Icc (0 : ℝ) τ, Hf σ)) := by
    have hI0 : 0 ≤ ∫ σ in Icc (0 : ℝ) τ, Hf σ :=
      setIntegral_nonneg measurableSet_Icc (fun σ hσ => hHf0 σ ⟨hσ.1, hσ.2.trans hτ.2⟩)
    have hW' : Wτ ≤ ENNReal.ofReal (C6 * Real.exp (2 * Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ) * τ *
        ∫ σ in Icc (0 : ℝ) τ, Hf σ) := hW
    calc varpiNormE m χ (F τ) ^ 2 ≤ ENNReal.ofReal KA * sa12x4_J m (F τ) := hA1
      _ ≤ ENNReal.ofReal KA * (ENNReal.ofReal cT⁻¹ * Wτ) := by gcongr
      _ ≤ ENNReal.ofReal KA * (ENNReal.ofReal cT⁻¹ * ENNReal.ofReal (C6 * Real.exp (2 * Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ) * τ *
            ∫ σ in Icc (0 : ℝ) τ, Hf σ)) := by gcongr
      _ = ENNReal.ofReal (Kall * (C6 * Real.exp (2 * Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ) * τ *
            ∫ σ in Icc (0 : ℝ) τ, Hf σ)) := by
          rw [hKall, ENNReal.ofReal_mul (mul_nonneg hKA0 (inv_nonneg.2 hcT0.le)), ENNReal.ofReal_mul hKA0]
          ring
  refine hsq.trans (ENNReal.ofReal_le_ofReal ?_)
  obtain ⟨k0, hk01, hk0lam⟩ := sa12x3_lam_lin hR (PDE.thetaOrder d s)
  have hΛ6 : 0 ≤ Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) := by rw [hk0lam]; exact mul_nonneg hC6.le (by linarith)
  have hC6C : C6 ≤ C := by rw [hCdef]; have : 0 ≤ Kall * C6 := mul_nonneg hKall0 hC6.le; linarith
  have hΛ := sa12x3_lam_ge hR hC6C (PDE.thetaOrder d s)
  have hΛle : Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) ≤ Rg.lambdaM C ν₀ (PDE.thetaOrder d s) := by linarith
  have hI0 : 0 ≤ ∫ σ in Icc (0 : ℝ) τ, Hf σ :=
    setIntegral_nonneg measurableSet_Icc (fun σ hσ => hHf0 σ ⟨hσ.1, hσ.2.trans hτ.2⟩)
  have hexp : Real.exp (2 * Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ) ≤
      Real.exp (2 * Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) :=
    Real.exp_le_exp.2 (by nlinarith [hτ.1])
  have hτI : 0 ≤ τ * ∫ σ in Icc (0 : ℝ) τ, Hf σ := mul_nonneg hτ.1 hI0
  have hKC : Kall * C6 ≤ C := by rw [hCdef]; linarith
  calc Kall * (C6 * Real.exp (2 * Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ) * τ * ∫ σ in Icc (0 : ℝ) τ, Hf σ)
      = (Kall * C6) * Real.exp (2 * Rg.lambdaM C6 ν₀ (PDE.thetaOrder d s) * τ) * (τ * ∫ σ in Icc (0 : ℝ) τ, Hf σ) := by ring
    _ ≤ C * Real.exp (2 * Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) * (τ * ∫ σ in Icc (0 : ℝ) τ, Hf σ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hKC hexp (Real.exp_pos _).le hCpos.le) hτI
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12X5
