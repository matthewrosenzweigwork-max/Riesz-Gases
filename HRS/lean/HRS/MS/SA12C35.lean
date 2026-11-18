import HRS.MS.SA12C34
import HRS.MS.SA12X3C15L
import HRS.MS.SA12X3C15K

/-!
# S.A.12(c): full periodic box-energy estimate with exact prefactor

The constant is selected before period, viscosity, density, time, and solution.
The exponent has the prescribed regime dependence; no multiplicative
constant is permitted outside the exponential.
-/
set_option autoImplicit false
set_option maxHeartbeats 12800000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

/-- E7.06 in full periodic-data form. -/
theorem sa12c_periodic_box_energy (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hs1 : (d : ℝ) < 2 * (s + 1)) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime)
    (MB Λ ΛV νbar Cb T : ℝ) {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) :
    ∃ C Lmin : ℝ, 0 < C ∧ 40 ≤ Lmin ∧
      ∀ L : ℝ, Lmin ≤ L → ∀ γ : Euc d → ℝ,
      ∀ M : Matrix (Fin d) (Fin d) ℝ, ∀ ν ν₀ : ℝ,
      ∀ μ : ℝ → Euc d → ℝ, ∀ V : Euc d → ℝ,
      ∀ b : ℝ → Euc d → Euc d,
      PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b →
      RdRegimeHolds Rg d s M ν ν₀ →
      ∀ t ∈ Set.Ioc (0 : ℝ) T,
      ∀ F : ℝ → Euc d → ℝ,
      IsPerSol m L γ M ν μ b (fun _ _ => (0 : ℝ)) t F →
      ∀ τ ∈ Set.Icc (0 : ℝ) t,
      boxEnergy m L (F τ) ≤
        Real.exp (2 * Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) *
          boxEnergy m L (F 0) := by
  obtain ⟨E, Cnear, Crem, Lmin, hE, hCnear, hCrem, hLmin, hNL⟩ :=
    sa12c_periodic_global_nonlocal_form hd s hs0 hsd hs1 m hm Rg MB Λ hχ
  set K0 : ℝ := ((d : ℝ) + 1) ^ m * sa12cK d m Cb with hK0
  set C : ℝ := Cnear * (E.card : ℝ) + |K0| + Crem + 1 with hC
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, Lmin, hCpos, hLmin, ?_⟩
  intro L hL γ M ν ν₀ μ V b hPD hR t ht F hsol τ hτ
  have hLt : 0 < L := by linarith
  have htT : t ≤ T := ht.2
  have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans htT⟩
  have hPDν : 0 ≤ ν := hPD.hν
  have hSpill : nearSpill Rg ν₀ E * (E.card : ℝ) ≤ 2 * ν :=
    (sa12x3_spill_ok hPDν hR E).2.trans (by linarith)
  have hPperiod : ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ (x : Euc d) (k : Fin d → ℤ),
        b σ (x + L • latticePt k) = b σ x := by
    intro σ hσ x k
    rw [hPD.b_eq σ hσ]
    exact sa12c_torusDrift_periodic (hPD.μ_periodic σ hσ) hPD.V_periodic x k
  have hNLsource : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      2 * boxJetPair m L (F σ)
        (fun y => -perNonlocal L γ M (μ σ) (F σ) y + 0) ≤
      (nearSpill Rg ν₀ E * (E.card : ℝ)) * boxDissip m L (F σ) +
      (Rg.lambdaM Cnear ν₀ (PDE.thetaOrder d s) * (E.card : ℝ) + Crem) * boxEnergy m L (F σ) := by
    intro σ hσ
    have hσT : σ ∈ Set.Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans htT⟩
    have hFsm : ContDiff ℝ ∞ (F σ) := (hsol.sol.smooth σ hσ).1
    have hNsm : ContDiff ℝ ∞ (perNonlocal L γ M (μ σ) (F σ)) := by
      have h := (hsol.sol.smooth σ hσ).2.neg
      simpa only [neg_add_rev, neg_neg, neg_zero, zero_add] using h
    have hμdec : ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * |μ σ x| ≤ Λ := by
      intro x
      obtain ⟨k, hk⟩ := hPD.μ_decay σ hσT 0 (by omega) x
      refine ⟨k, ?_⟩
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hk
    have hnear := hNL L hL γ hPD.hγ M hPD.hM ν ν₀ hR (μ σ) (F σ)
      (hPD.μ_smooth σ hσT) (hPD.μ_prob σ hσT).1
      (hPD.μ_periodic σ hσT) (hPD.μ_bdd σ hσT) hμdec
      hFsm (hsol.periodic σ hσ) (hsol.bdd σ hσ) hNsm
    rw [sa12c_boxJetPair_neg] 
    linarith
  have hcore := sa12c_box_energy_bound hPD.b_drift hsol.sol htT hLt hsol.periodic
    hPperiod hSpill hNLsource τ hτ
  obtain ⟨k, hk, hlin⟩ := sa12x3_lam_lin (d := d) hR (PDE.thetaOrder d s)
  have hrate : K0 + (Rg.lambdaM Cnear ν₀ (PDE.thetaOrder d s) * (E.card : ℝ) + Crem) ≤
      2 * Rg.lambdaM C ν₀ (PDE.thetaOrder d s) := by
    rw [hlin Cnear, hlin C]
    have hecard : 0 ≤ (E.card : ℝ) := Nat.cast_nonneg _
    have hrest : 0 ≤ |K0| + Crem := add_nonneg (abs_nonneg _) hCrem
    have h1 : (|K0| + Crem) ≤ (|K0| + Crem) * k :=
      le_mul_of_one_le_right hrest hk
    have h2 : 0 ≤ (Cnear * (E.card : ℝ) + |K0| + Crem + 1) * k := by positivity
    dsimp [C]
    nlinarith [le_abs_self K0]
  have he : Real.exp ((K0 + (Rg.lambdaM Cnear ν₀ (PDE.thetaOrder d s) * (E.card : ℝ) + Crem)) * τ) ≤
      Real.exp (2 * Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hrate hτ.1)
  exact hcore.trans (mul_le_mul_of_nonneg_right he (boxEnergy_nonneg m L (F 0)))

end HRS.MH.AdjointRd.Phase2SA12C
