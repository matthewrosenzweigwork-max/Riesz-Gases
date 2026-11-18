import HRS.MS.R2GenInitTie
import HRS.MS.R2WinOrbNLAux1
import HRS.MS.MovEntFinal
import HRS.MS.WsPrepAux8
import HRS.MS.WsPrepAux9

/-!
# S10.5, nonlinear branch, part 1: the entropy clause of S6.6 for the class `IsR2WindowTrajectory`

No statement repair is needed (S21R, D1): `HRS.MS.MovEnt.movEntAt_low_of_diss` exposes the indices `(1, d/2+8)` of the proof of `mov_entropy` (`MovEntAt d s 1 (d/2+8)`),
`SuperDiss d s` is unconditional (`MovEntFinal`), and a resulting solution of the class (indices `100d+1000`, `102d+1020`) lies in the S6.3 class at the lower indices
(`s21p_resulting_in_class_low`, WsPrepAux8) provided `ε_* ≤ ε_s'` and `C₁ ε_* ≤ r` (constants of `MovEntAt`, depending on `d,s,a,β` only).  `s105n_hent` is the entropy bound
for every such resulting solution.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff



namespace HRS.MS.R2GenInit

open HRS.Whole HRS.Whole.AppendixA HRS.MS.R2WinErr

variable {d : ℕ}

theorem s105n_hent (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ εs rr Cent : ℝ, 0 < εs ∧ 0 < rr ∧ 0 ≤ Cent ∧ ∀ (εstar c₁ C₁ : ℝ), εstar ≤ εs → C₁ * εstar ≤ rr →
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
      ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction d s a β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      IsR2Realization d s a β P X₀ W X →
      HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal (ρ 0))) < ⊤ →
      ∀ t : ℝ, 0 ≤ t → HRS.relEntropy (P.map (X t.toNNReal))
        (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t))) ≤
        ENNReal.ofReal (Cent * ((HRS.relEntropy (HRS.law P X₀)
          (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
            (HRS.Whole.withDensityReal (ρ 0)))).toReal + N * deltaN d s N)) := by
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d s a β ρ0
  swap
  · exact ⟨1, 1, 0, one_pos, one_pos, le_rfl, fun _ _ _ _ _ ρβ hρ => absurd ⟨ρβ, hρ⟩ hex⟩
  obtain ⟨ρ0, hρ0⟩ := hex
  have H : HRS.MS.MovLin.Mov2dTh d s β a ρ0 := ⟨hd, hs0, hsd, hβ, ha, hρ0⟩
  have hMov : HRS.Whole.MovEntAt d s 1 (d / 2 + 8) :=
    HRS.MS.MovEnt.movEntAt_low_of_diss
      (HRS.MS.MfeConf.sb1_superDiss_of_movEnt (by omega) hd hs0 hsd (HRS.MS.MfeConf.sb1_superMovEnt (by omega) hs0 hsd))
  have hm : (d : ℝ) / 2 + ((1 : ℕ) : ℝ) + 6 < ((d / 2 + 8 : ℕ) : ℝ) := by
    have : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : d ≤ 2 * (d / 2) + 1)
    push_cast; linarith
  obtain ⟨εs', r, c₀, c, C', hε', hr, hc₀, hc, hC', hconc, C₀', -, ⟨Ce, hEnt⟩, -⟩ :=
    hMov hd hs0 hsd β a hβ ha ρ0 hρ0 le_rfl hm
  refine ⟨εs', r, max Ce 0, hε', hr, le_max_right _ _, ?_⟩
  intro εstar c₁ C₁ hεs hCr ρβ hρβ ε ψ ρ hadm hres N hN hGib Ω _ P _ X₀ W X hreal hfin t ht
  have huniq : ρβ = ρ0 := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ, HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ0]
  subst huniq
  obtain ⟨hI, hsmall⟩ := s21p_resulting_in_class_low (by omega) (by
    push_cast; have : ((d / 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.div_le_self d 2
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith) hconc hεs hCr hadm hres
  have hsetup : MovParticleSetup P d s a β N X₀ W X :=
    ⟨hreal.brownian, hreal.indep, hreal.solution, hreal.filtered⟩
  have h := hEnt (fun x => ε * ψ x) hI ρ hsmall N hN hGib P X₀ W X hsetup t ht
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hNδ : 0 ≤ (N : ℝ) * deltaN d s N := mul_nonneg (Nat.cast_nonneg _) hδ
  have hlaw : HRS.law P X₀ = P.map X₀ := rfl
  rw [hlaw] at hfin ⊢
  set H0 := HRS.relEntropy (P.map X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
    (HRS.Whole.withDensityReal (ρ 0))) with hH0
  have hH0e : H0 = ENNReal.ofReal H0.toReal := (ENNReal.ofReal_toReal hfin.ne).symm
  have hT0 : 0 ≤ H0.toReal := ENNReal.toReal_nonneg
  calc _ ≤ ENNReal.ofReal Ce * (H0 + ENNReal.ofReal (N * deltaN d s N)) := h
    _ ≤ ENNReal.ofReal (max Ce 0) * (H0 + ENNReal.ofReal (N * deltaN d s N)) :=
        by gcongr; exact le_max_left _ _
    _ = ENNReal.ofReal (max Ce 0 * (H0.toReal + N * deltaN d s N)) := by
        rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_add hT0 hNδ, ← hH0e]

end HRS.MS.R2GenInit
