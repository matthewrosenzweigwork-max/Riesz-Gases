import HRS.Main.FullBoundsBeta0
import HRS.Main.FullBoundsStat
import HRS.Main.FullBoundsAux

/-!
# FULLBOUNDS (Gibbs preparation): clause (ii) of `prepared_full_bounds` from the static comparison

`FbEqInitialLaw d` is the statement of `equilibrium_initial_law` (`HRS/Main/Equilibrium29Spec.lean`, chunk D, still
`sorry` there) as a `Prop`.  `fb_clause_gibbs_of` proves clause (ii) of `prepared_full_bounds` (`β₀ > 0`) from it as a
hypothesis; this file does not import the `sorry`'d statement, so `fb_clause_gibbs_of` is axiom-clean.
`FullBoundsGibbsCond.lean` instantiates the hypothesis with the frozen theorem.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- The statement of `equilibrium_initial_law` (`HRS/Main/Equilibrium29Spec.lean:399`), verbatim, as a `Prop`. -/
def FbEqInitialLaw (d : ℕ) : Prop :=
  ∀ (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : (d : ℝ) + 2 < m),
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        smoothDist 2 (law (canonicalGibbs (periodicRiesz d s) V N β)
            (fun X => etaE m X (withDensityReal ρβ))) (law P' (Z 0)) ≤
          C * (Real.sqrt N * deltaN d s N) ∧
        wassersteinE 2 (law (canonicalGibbs (periodicRiesz d s) V N β)
            (fun X => etaE m X (withDensityReal ρβ))) (law P' (Z 0)) ≤
          ENNReal.ofReal (C * (Real.sqrt N * deltaN d s N + (N : ℝ) ^ (-(1 : ℝ) / 4) +
            Real.sqrt (deltaN d s N)))

/-- Clause (ii) of `prepared_full_bounds` (Gibbs preparation, `β₀ > 0`), from the static comparison `heq`
(`equilibrium_initial_law`) at time zero.  Same binders as `prepared_full_bounds`; only the clause for `0 < β₀`
is kept. -/
theorem fb_clause_gibbs_of (heq : FbEqInitialLaw d) (S : PreparedData d) (m : ℝ)
    (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        (0 < β₀ →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.sqrt N * deltaN d S.s N) ∧
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N +
              deltaN d S.s N ^ ((1 : ℝ) / 4)))) := by
  by_cases hpos : 0 < β₀
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hinit ν hν Ω' _ P' _ Y₀ Y hY h
    exact absurd h hpos
  have hd2 := S.hd
  have hd1 : 1 ≤ d := by omega
  have hmd : (d : ℝ) / 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- the auxiliary potential and a stationary field for it
  obtain ⟨V₀, hV₀, hth, hcan⟩ := fb_aux_potential S hpos
  obtain ⟨Ceq, hCeq, heq'⟩ := heq S.hd S.hs0 S.hsd V₀ hV₀ β₀ β₀ hpos le_rfl m hm
  have hmax : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    exact max_lt (by linarith) (by linarith)
  obtain ⟨Ωz, _, Pz, hPz, Z, hZ⟩ := stationaryField_exists S.hd S.hs0 S.hsd hpos V₀ hV₀ S.ρ0 hth m hmax
  -- scales
  obtain ⟨⟨Cb0, hCb⟩, hJ⟩ := prepared_scales_proof S β₀ hpos.le
  obtain ⟨p₀, hp₀, Cj0, hCj⟩ := hJ (Or.inl hpos)
  set Cb : ℝ := max Cb0 0 with hCbdef
  set Cj : ℝ := max Cj0 0 with hCjdef
  have hsN : ∀ N : ℕ, 2 ≤ N → 0 ≤ Real.sqrt N * deltaN d S.s N := fun N hN => by
    have := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
    positivity
  have hrw : ∀ N : ℕ, 2 ≤ N → 0 ≤ Real.sqrt N * deltaN d S.s N + (N : ℝ) ^ (-(1 : ℝ) / 4) +
      Real.sqrt (deltaN d S.s N) := fun N hN => by
    have h1 := hsN N hN
    have h2 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have h3 := Real.sqrt_nonneg (deltaN d S.s N)
    linarith
  obtain ⟨C1, hC1, h1⟩ := fb_smooth S m hm T hT Cb Ceq (le_max_right _ _) hCeq.le
    (fun N => Real.sqrt N * deltaN d S.s N) hsN
  obtain ⟨C2, hC2, h2⟩ := fb_W2 S m hm T hT p₀ hp₀ Cb Cj Ceq (le_max_right _ _) (le_max_right _ _)
    hCeq.le (fun N => Real.sqrt N * deltaN d S.s N + (N : ℝ) ^ (-(1 : ℝ) / 4) +
      Real.sqrt (deltaN d S.s N)) hrw
  refine ⟨max (2 * C1) (3 * C2), lt_max_of_lt_left (by positivity), ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hinit ν hν Ω' _ P' _ Y₀ Y hY _
  have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- identification of the initial Gaussian
  have hcov : preparedCov d S.s β₀ S.μ0 =
      susceptibilityCov (periodicRiesz d S.s) (withDensityReal S.ρ0) β₀ := by
    funext φ ψ
    simp [preparedCov, hpos.ne', PreparedData.μ0]
  rw [hcov] at hν
  haveI : IsProbabilityMeasure ν := hν.1.1.toIsProbabilityMeasure
  have hlawZ : law Pz (Z 0) = ν :=
    fb_stat_time0_law S.hd S.hs0 S.hsd hpos V₀ S.ρ0 hV₀ hth S.hρ0.smooth S.hρ0.pos m Pz Z hZ ν hν
  have hcmp := heq' β₀ ⟨le_rfl, le_rfl⟩ S.ρ0 hth N hN Pz Z hZ
  rw [hlawZ, hcan N] at hcmp
  have hlaw : law P (fun ω => etaE m (X₀ ω) S.μ0) =
      law (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) (fun X => etaE m X (withDensityReal S.ρ0)) := by
    rw [fb_law_eta S m hmd (by omega) P hSel.init_meas, hinit]
    rfl
  have hBk : relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ ∧
      S.B N (law P X₀) ≤ Cb * ((N : ℝ) * deltaN d S.s N) := by
    rw [hinit]
    obtain ⟨he, hb⟩ := hCb N hN
    exact ⟨he, hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  have hJk := hCj N hN
  rw [← hinit] at hJk
  have hJk' : S.J N (law P X₀) p₀ ≤ Cj * ((N : ℝ) * deltaN d S.s N) :=
    hJk.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hx := hsN N hN
  have hq : 0 ≤ deltaN d S.s N ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hδ.le _
  constructor
  · have := h1 a ha N hN P X₀ W X hSel hfilt hBk.1 hBk.2 ν P' Y₀ Y hY (by rw [hlaw]; exact hcmp.1)
    refine this.trans ?_
    calc C1 * (Real.sqrt N * deltaN d S.s N + Real.sqrt N * deltaN d S.s N)
        = 2 * C1 * (Real.sqrt N * deltaN d S.s N) := by ring
      _ ≤ max (2 * C1) (3 * C2) * (Real.sqrt N * deltaN d S.s N) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hx
  · have := h2 a ha N hN P X₀ W X hSel hfilt hBk.1 hJk.1 hBk.2 hJk' ν P' Y₀ Y hY
      (by rw [hlaw]; exact hcmp.2)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    -- `N^{-1/4} ≤ δ_N^{1/4}` and `√δ_N ≤ δ_N^{1/4}`
    have hinv : (N : ℝ) ^ (-(1 : ℝ) / 4) ≤ deltaN d S.s N ^ ((1 : ℝ) / 4) := by
      have h1' := HRS.WeakRef.inv_le_deltaN hd1 S.hs0 S.hsd (by omega : 1 ≤ N)
      have : (N : ℝ) ^ (-(1 : ℝ) / 4) = ((N : ℝ)⁻¹) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_mul hN0.le]
        norm_num
      rw [this]
      exact Real.rpow_le_rpow (inv_nonneg.2 hN0.le) h1' (by norm_num)
    have hsq : Real.sqrt (deltaN d S.s N) ≤ deltaN d S.s N ^ ((1 : ℝ) / 4) := by
      have hle := HRS.WeakRef.deltaN_le_one hd1 S.hs0 S.hsd (by omega : 1 ≤ N)
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hle (by norm_num)
    calc C2 * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) +
          (Real.sqrt N * deltaN d S.s N + (N : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt (deltaN d S.s N)))
        ≤ C2 * (3 * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4))) :=
          mul_le_mul_of_nonneg_left (by linarith) hC2.le
      _ = 3 * C2 * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4)) := by ring
      _ ≤ max (2 * C1) (3 * C2) * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg hx hq)

end Main

end HRS

end
