import HRS.MS.FixEqP3Aux35

/-!
# S5.7 `fixed_equation` (worker S57P), part 48: trivial pair bounds (used when `Δ_N = ⊤`) and finiteness of `‖η‖`
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K KN : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν νN : ℝ}
  {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ} {Ca CaN Cd CdN : ℝ}

theorem s57p_pairBd_triv (Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar) (FxN : S57pFx θ T n KN s M Q νN cN ρN A Λc νbar)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd)
    (hbdN : S57pOrbBd (fixedEqCoeff s M Q νN cN ρN) T n m J CaN CdN) (hCa : 0 ≤ Ca) (hCaN : 0 ≤ CaN) (hCd : 0 ≤ Cd)
    (hCdN : 0 ≤ CdN) {Cp1 Cp2 : ℝ} (h1 : Ca + CaN ≤ Cp1) (h2 : Cd + CdN ≤ Cp2) :
    S57pPairBd θ T n K KN s M Q ν νN c cN ρ ρN A Λc νbar m J Ca CaN Cd CdN Cp1 Cp2 1 := by
  have hn := Fx.hn4
  have hlam : ∀ α : MultiIndex d, 0 ≤ oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := fun α =>
    Real.rpow_nonneg (oscEigenvalue_pos α).le _
  refine ⟨Fx, FxN, hbd, hbdN, hCa, hCaN, hCd, hCdN, by linarith, by linarith, zero_le_one, ?_, ?_⟩
  · intro α t ht r hr i hi x
    obtain ⟨-, hb1⟩ := (hbd α).1 t ht
    obtain ⟨-, hb2⟩ := (hbdN α).1 t ht
    have c1 : ContDiff ℝ (i : WithTop ℕ∞) (propagatorW (fixedEqCoeff s M Q ν c ρ) r t (oscTestFun m α)) :=
      (hb1 r hr).1.of_le (by exact_mod_cast (by omega : i ≤ n + 1))
    have c2 : ContDiff ℝ (i : WithTop ℕ∞) (propagatorW (fixedEqCoeff s M Q νN cN ρN) r t (oscTestFun m α)) :=
      (hb2 r hr).1.of_le (by exact_mod_cast (by omega : i ≤ n + 1))
    have e : iteratedFDeriv ℝ i (fun y => propagatorW (fixedEqCoeff s M Q ν c ρ) r t (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q νN cN ρN) r t (oscTestFun m α) y) x =
        iteratedFDeriv ℝ i (propagatorW (fixedEqCoeff s M Q ν c ρ) r t (oscTestFun m α)) x -
          iteratedFDeriv ℝ i (propagatorW (fixedEqCoeff s M Q νN cN ρN) r t (oscTestFun m α)) x :=
      iteratedFDeriv_sub_apply c1.contDiffAt c2.contDiffAt
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := (hb1 r hr).2 i (by omega) x
    have := (hb2 r hr).2 i (by omega) x
    have := mul_le_mul_of_nonneg_right h1 (hlam α)
    nlinarith
  · intro α s₀ t₀ hs ht0 htT r hr x
    have ht1 : s₀ ∈ Set.Icc (0 : ℝ) T := ⟨hs, ht0.trans htT⟩
    have ht2 : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨hs.trans ht0, htT⟩
    have hrt : r ∈ Set.Icc (0 : ℝ) t₀ := ⟨hr.1, hr.2.trans ht0⟩
    obtain ⟨-, hb1⟩ := (hbd α).1 s₀ ht1
    obtain ⟨-, hb2⟩ := (hbdN α).1 s₀ ht1
    obtain ⟨-, hb3⟩ := (hbd α).1 t₀ ht2
    obtain ⟨-, hb4⟩ := (hbdN α).1 t₀ ht2
    have c1 : ContDiff ℝ 1 (fun y => propagatorW (fixedEqCoeff s M Q ν c ρ) r t₀ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q ν c ρ) r s₀ (oscTestFun m α) y) :=
      ((hb3 r hrt).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))).sub
        ((hb1 r hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1)))
    have c2 : ContDiff ℝ 1 (fun y => propagatorW (fixedEqCoeff s M Q νN cN ρN) r t₀ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q νN cN ρN) r s₀ (oscTestFun m α) y) :=
      ((hb4 r hrt).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))).sub
        ((hb2 r hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1)))
    have e : (fun y => (propagatorW (fixedEqCoeff s M Q ν c ρ) r t₀ (oscTestFun m α) y -
          propagatorW (fixedEqCoeff s M Q νN cN ρN) r t₀ (oscTestFun m α) y) -
        (propagatorW (fixedEqCoeff s M Q ν c ρ) r s₀ (oscTestFun m α) y -
          propagatorW (fixedEqCoeff s M Q νN cN ρN) r s₀ (oscTestFun m α) y)) =
        fun y => (propagatorW (fixedEqCoeff s M Q ν c ρ) r t₀ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q ν c ρ) r s₀ (oscTestFun m α) y) -
        (propagatorW (fixedEqCoeff s M Q νN cN ρN) r t₀ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q νN cN ρN) r s₀ (oscTestFun m α) y) := by funext y; ring
    rw [e]
    have e2 : iteratedFDeriv ℝ 1 (fun y => (propagatorW (fixedEqCoeff s M Q ν c ρ) r t₀ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q ν c ρ) r s₀ (oscTestFun m α) y) -
        (propagatorW (fixedEqCoeff s M Q νN cN ρN) r t₀ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q νN cN ρN) r s₀ (oscTestFun m α) y)) x =
        iteratedFDeriv ℝ 1 (fun y => propagatorW (fixedEqCoeff s M Q ν c ρ) r t₀ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q ν c ρ) r s₀ (oscTestFun m α) y) x -
        iteratedFDeriv ℝ 1 (fun y => propagatorW (fixedEqCoeff s M Q νN cN ρN) r t₀ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q νN cN ρN) r s₀ (oscTestFun m α) y) x :=
      iteratedFDeriv_sub_apply c1.contDiffAt c2.contDiffAt
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    have a1 := (hbd α).2 s₀ t₀ hs ht0 htT r hr 1 (by omega) x
    have a2 := (hbdN α).2 s₀ t₀ hs ht0 htT r hr 1 (by omega) x
    have hu : 0 ≤ t₀ - s₀ := sub_nonneg.2 ht0
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (hlam α)) hu
    nlinarith

theorem s57p_dual_lt_top {n : ℕ} {P : ℝ} {η : (Euc d → ℝ) → ℝ} (hη : IsBoundedLinearOnE n P η) :
    dualNormE n P η < ⊤ := by
  obtain ⟨B, hB⟩ := hη.2
  have hB0 : ∀ f, ContDiff ℝ n f → weightedSobolevE n P f < ⊤ → |η f| ≤ B * (weightedSobolevE n P f).toReal := hB
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := B))
  unfold dualNormE
  refine iSup₂_le fun f hf => ?_
  have hfin := hf.2.2.2
  have hpos := hf.2.2.1
  have hcd : ContDiff ℝ n f := hf.1.of_le (by exact_mod_cast le_top)
  have h1 := hB0 f hcd hfin
  refine ENNReal.div_le_of_le_mul ?_
  have : ENNReal.ofReal |η f| ≤ ENNReal.ofReal (B * (weightedSobolevE n P f).toReal) := ENNReal.ofReal_le_ofReal h1
  refine this.trans ?_
  have hBn : 0 ≤ B := by
    by_contra hneg
    push_neg at hneg
    have hE : 0 < (weightedSobolevE n P f).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
    have := le_trans (abs_nonneg _) h1
    nlinarith
  rw [ENNReal.ofReal_mul hBn, ENNReal.ofReal_toReal hfin.ne]

end HRS.MS.FixEq
