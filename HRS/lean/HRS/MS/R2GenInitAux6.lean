import HRS.MS.R2GenInitAux5
import HRS.MS.CanThmAux1
import HRS.MS.R2WinErrStat

/-!
# S10.5 input `hent` for the stationary trajectory

`s105_hent_stat`: for `ρ = fun _ => ρ_β` the reference measure is the canonical Gibbs law (`Can2.can2_clause1_pos/log`), so
`GibbsEntropyContraction` gives `H(law X_t | Q_N^t) ≤ H(law X_0 | Q_N^0)` (no `Nδ_N` term needed; `Cent = 1`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace HRS.MS.R2GenInit

open HRS.Whole

variable {d : ℕ}

theorem s105_canon_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρβ) (N : ℕ) :
    HRS.Whole.canonicalGibbs (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement a) N β =
      HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρβ) := by
  have hρeq : ρβ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  subst hρeq
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    exact HRS.MS.Can2.can2_clause1_log hd ha hβ N
  · exact HRS.MS.Can2.can2_clause1_pos hd hpos hsd ha hβ N

theorem s105_hent_stat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρβ) {N : ℕ} (hN : 2 ≤ N) (hGib : GibbsEntropyContraction d s a β N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hreal : IsR2Realization d s a β P X₀ W X)
    (hfin : HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal ((fun _ : ℝ => ρβ) 0))) < ⊤) (t : ℝ) (ht : 0 ≤ t) :
    HRS.relEntropy (P.map (X t.toNNReal))
      (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ((fun _ : ℝ => ρβ) t))) ≤
      ENNReal.ofReal (1 * ((HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal ((fun _ : ℝ => ρβ) 0)))).toReal + N * deltaN d s N)) := by
  have hc := s105_canon_eq hd hs0 hsd ha hβ hρ N
  have h := hGib P t X₀ W X hreal.brownian hreal.indep (hreal.solution t) t.toNNReal (by
    rw [Real.coe_toNNReal t ht])
  beta_reduce at hfin ⊢
  rw [← hc] at hfin ⊢
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hNδ : 0 ≤ (N : ℝ) * deltaN d s N := mul_nonneg (Nat.cast_nonneg _) hδ
  refine h.trans ?_
  rw [← ENNReal.ofReal_toReal hfin.ne]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, one_mul]
  linarith

end HRS.MS.R2GenInit
