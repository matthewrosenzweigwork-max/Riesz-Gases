import HRS.Appendix.B15Final
import HRS.Appendix.B15Aux2
import HRS.Stochastic.LyonsZhengSpec

/-!
# Packet STAT (chunk D): `md_stat_gibbs_flow_stationary_proof`

Relocated proof of `HRS.MD.Stat.md_stat_gibbs_flow_stationary` (statement frozen with its `sorry` in
`HRS/MD/StatSpec.lean`; the tie `HRS/MD/StatTie.lean` checks that the statements agree).

Route: `b15_sde_entropy_law_free_proof` (entropy dissipation) with `gibbsRef D N = canonicalGibbs`
(`b15_gibbsRef_eq_canonicalGibbs_of_lower`) and the Gibbs start: `gibbsEntropy (law X₀) = - log Z_G`, so the
entropy inequality gives `klDiv (P^t) gibbsRef ≤ 0`, hence `P^t = gibbsRef = canonicalGibbs`.

The import of `HRS.Stochastic.LyonsZhengSpec` is for the definition `LZ.IsStationaryGibbsFlow` only (that module also
holds a sorried theorem, which is not used here).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MD.Stat

variable {d N : ℕ}

/-- From `(a : EReal) - L + J ≤ 0 - L` with `J ≥ 0`, `L` real: `a ≤ 0` (as `ℝ≥0∞`). -/
theorem md_stat_relEntropy_le_zero {a J : ℝ≥0∞} (L : ℝ)
    (h : ((a : ℝ≥0∞) : EReal) - (L : EReal) + (J : EReal) ≤ ((0 : ℝ≥0∞) : EReal) - (L : EReal)) :
    a = 0 := by
  by_cases ha : a = ⊤
  · subst ha
    simp at h
  · lift a to ℝ≥0 using ha
    rw [EReal.coe_nnreal_eq_coe_real] at h
    by_cases hJ : J = ⊤
    · subst hJ
      rw [← EReal.coe_sub, EReal.coe_ennreal_top, EReal.coe_add_top] at h
      simp at h
    · lift J to ℝ≥0 using hJ
      rw [EReal.coe_nnreal_eq_coe_real] at h
      simp only [EReal.coe_ennreal_zero, zero_sub] at h
      rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_neg, EReal.coe_le_coe_iff] at h
      have : (a : ℝ) ≤ 0 := by linarith [J.coe_nonneg]
      have : a = 0 := by exact_mod_cast le_antisymm this a.coe_nonneg
      simp [this]

theorem md_stat_gibbs_flow_stationary_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (T : ℝ) (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (h : LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ T X₀ W X) :
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → P.map (X t) = canonicalGibbs (periodicRiesz d s) V N β := by
  intro t ht
  have : NeZero N := ⟨by omega⟩
  set D : DynData d := PDE.mfData d s hs0 hsd V β hβ with hD
  have hDV : D.V = V := rfl
  have hDs : D.s = s := rfl
  have hDinv : D.invβ = β⁻¹ := rfl
  have hDM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ) := rfl
  have hinvpos : 0 < D.invβ := by rw [hDinv]; exact inv_pos.mpr hβ
  have hV2 : Torus.IsCk 2 D.V := by
    rw [hDV]
    exact (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hbeta : D.invβ⁻¹ = β := by rw [hDinv, inv_inv]
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) (s := s) hd hs0 hsd
  have hB' : ∀ z, -(max B 0) ≤ periodicRiesz d D.s z := fun z =>
    (neg_le_neg (le_max_left _ _)).trans (hB z)
  have hGR : gibbsRef D N = canonicalGibbs (periodicRiesz d s) V N β := by
    have := b15_gibbsRef_eq_canonicalGibbs_of_lower (N := N) D hB' hV2 hinvpos
    rwa [hbeta] at this
  have hfl := h.flow
  have hinit := h.init
  -- the strong solution
  have hS : IsStrongSolution P D T X₀ W X ∧ PathwiseUnique P D T X₀ W := by
    rcases hfl.flow with hh | ⟨hd1, -⟩
    · exact hh
    · omega
  have hX0 : P.map (X 0) = canonicalGibbs (periodicRiesz d s) V N β := by
    rw [← hinit]
    exact Measure.map_congr (by filter_upwards [hS.1.init] with ω hω using hω)
  by_cases hT : 0 < T
  · obtain ⟨ℱ, W', hF⟩ := h.filtered
    have hprob0 : IsProbabilityMeasure (selectedLaw P X 0) := b15b_selectedLaw_isProb hS.1.adapted 0
    have hsel0 : selectedLaw P X 0 = gibbsRef D N := by
      rw [hGR]
      simpa [selectedLaw, law] using hX0
    have hGprob : IsProbabilityMeasure (gibbsRef D N) := by rw [← hsel0]; exact hprob0
    have hdens0 : HasSelectedDensity P X 0 := by
      rw [HasSelectedDensity, hsel0]
      exact (withDensity_absolutelyContinuous _ _).smul_left _
    obtain ⟨hZpos, hZtop⟩ := b15_gibbsPartition_pos_lt_top (N := N) D hV2 hinvpos
    have hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤ := by
      rw [hsel0]
      unfold gibbsEntropy relEntropy
      rw [InformationTheory.klDiv_self]
      simp only [EReal.coe_ennreal_zero, zero_sub]
      rw [← EReal.coe_neg]
      exact EReal.coe_lt_top _
    have hmain := (b15_sde_entropy_law_free_proof (N := N) hN hDM hinvpos hV2 hT hfl.init_meas
      hfl.init_distinct hfl.brownian hfl.indep hS.1 hS.2 hF hdens0 hH0).1 (t : ℝ) ⟨t.coe_nonneg, ht⟩
    obtain ⟨-, hent⟩ := hmain
    rw [hsel0] at hent
    unfold gibbsEntropy relEntropy at hent
    rw [InformationTheory.klDiv_self] at hent
    have h0 := md_stat_relEntropy_le_zero _ hent
    have hprobt : IsProbabilityMeasure (selectedLaw P X t) := b15b_selectedLaw_isProb hS.1.adapted t
    have heq : selectedLaw P X t = gibbsRef D N := by
      have := hGprob
      exact InformationTheory.klDiv_eq_zero_iff.mp h0
    rw [hGR] at heq
    simpa [selectedLaw, law] using heq
  · have : t = 0 := by
      have : (t : ℝ) ≤ 0 := ht.trans (not_lt.mp hT)
      exact_mod_cast le_antisymm this t.coe_nonneg
    rw [this]
    exact hX0

end MD.Stat

end HRS
