import HRS.Main.FullBoundsAssembly
import HRS.Sections.IIDFinal
import HRS.Main.ThermFinal

/-!
# FULLBOUNDS (`β₀ = 0`): clauses (i) and (iii) of `prepared_full_bounds`

`fb_prepared_full_bounds_beta0` is `prepared_full_bounds` (`HRS/Main/Headline.lean`) with the clause for
`0 < β₀` removed (it is vacuous when `β₀ = 0`; for `β₀ ≠ 0` the two remaining clauses are vacuous).
Inputs: `iid_field_comparison_proof` (Prop. 5.9), `prepared_scales_proof`, `modulatedGibbs_zero`,
and the abstract assembly of `FullBoundsAssembly`.  No `sorry`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem fb_iidRateSmooth_nonneg (d : ℕ) (m : ℝ) (N : ℕ) : 0 ≤ iidRateSmooth d m N :=
  Real.rpow_nonneg (Nat.cast_nonneg N) _

theorem fb_iidRateW_nonneg (d : ℕ) (m : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 ≤ iidRateW d m N := by
  unfold iidRateW
  refine Real.rpow_nonneg (div_nonneg ?_ (Real.sqrt_nonneg _)) _
  apply Real.log_nonneg
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  nlinarith

/-- The law of `η_N^0` is the push-forward of the law of the initial configuration. -/
theorem fb_law_eta (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) / 2 < m) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {X₀ : Ω → Config d N} (h : Measurable X₀) :
    law P (fun ω => etaE m (X₀ ω) S.μ0) = (law P X₀).map (fun X => etaE m X S.μ0) := by
  haveI : IsProbabilityMeasure S.μ0 := HRS.isProb_withDensityReal S.hρ0.density
  have hm2 : (d : ℝ) < 2 * m := by linarith
  have hη : Measurable (fun X : Config d N => etaE m X S.μ0) := by
    have := measurable_ofMeasureDiff_empirical (N := N) hm2 S.μ0 hN
    unfold etaE flucE
    exact this.const_smul (Real.sqrt N)
  unfold law
  rw [Measure.map_map hη h]
  rfl

/-- Clauses (i) of `prepared_full_bounds` (`β₀ = 0`): smooth and `W_1`. -/
theorem fb_beta0_i (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = modulatedGibbs (periodicRiesz d S.s) N 0 S.μ0 →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s 0 S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.sqrt N * deltaN d S.s N + iidRateSmooth d m N) ∧
          wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N +
              deltaN d S.s N ^ ((1 : ℝ) / 4) + iidRateW d m N)) := by
  have hd2 := S.hd
  have hmd : (d : ℝ) / 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hρc : Continuous S.ρ0 := HRS.StaticLimitAux.continuous_of_smooth S.hρ0.smooth
  obtain ⟨xmin, -, hxmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hρc.continuousOn
  obtain ⟨xmax, -, hxmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hρc.continuousOn
  have hc : 0 < S.ρ0 xmin := S.hρ0.pos xmin
  obtain ⟨Cm, hCm0, hCm⟩ := HRS.iid_field_comparison_proof hd2 m hmd (S.ρ0 xmin) (S.ρ0 xmax) hc
  obtain ⟨⟨Cb0, hCb⟩, -⟩ := prepared_scales_proof S 0 le_rfl
  set Cb : ℝ := max Cb0 0 with hCbdef
  obtain ⟨C1, hC1, h1⟩ := fb_smooth_W1 S m hm T hT Cb Cm Cm (le_max_right _ _) hCm0 hCm0
    (iidRateSmooth d m) (iidRateW d m) (fun N _ => fb_iidRateSmooth_nonneg d m N)
    (fun N hN => fb_iidRateW_nonneg d m (by omega))
  refine ⟨C1, hC1, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hinit ν hν Ω' _ P' _ Y₀ Y hY
  haveI : IsProbabilityMeasure S.μ0 := HRS.isProb_withDensityReal S.hρ0.density
  have hinit' : law P X₀ = Measure.pi fun _ : Fin N => S.μ0 := by
    rw [hinit]; exact modulatedGibbs_zero _ _
  have hcov : preparedCov d S.s 0 S.μ0 = iidCov S.μ0 := by
    funext φ ψ; simp [preparedCov]
  rw [hcov] at hν
  have hlaw : law P (fun ω => etaE m (X₀ ω) S.μ0) =
      law (Measure.pi fun _ : Fin N => withDensityReal S.ρ0)
        (fun X : Config d N => etaE m X (withDensityReal S.ρ0)) := by
    rw [fb_law_eta S m hmd (by omega) P hSel.init_meas, hinit']
    rfl
  have hcmp := hCm S.ρ0 S.hρ0.density (fun x => by simpa using hxmin (Set.mem_univ x))
    (fun x => by simpa using hxmax (Set.mem_univ x)) ν hν N (by omega)
  have hBk : relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ ∧
      S.B N (law P X₀) ≤ Cb * ((N : ℝ) * deltaN d S.s N) := by
    rw [hinit]
    obtain ⟨he, hb⟩ := hCb N hN
    refine ⟨he, hb.trans ?_⟩
    have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  exact h1 a ha N hN P X₀ W X hSel hfilt hBk.1 hBk.2 ν P' Y₀ Y hY (by rw [hlaw]; exact hcmp.1)
    (by rw [hlaw]; exact hcmp.2.1)

/-- Clause (iii) of `prepared_full_bounds` (`β₀ = 0`, `s = 0`): `W_2`. -/
theorem fb_beta0_iii (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T)
    (hs : S.s = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = modulatedGibbs (periodicRiesz d S.s) N 0 S.μ0 →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s 0 S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 4) + iidRateW d m N ^ ((1 : ℝ) / 3))) := by
  have hd2 := S.hd
  have hd1 : 1 ≤ d := by omega
  have hmd : (d : ℝ) / 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hρc : Continuous S.ρ0 := HRS.StaticLimitAux.continuous_of_smooth S.hρ0.smooth
  obtain ⟨xmin, -, hxmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hρc.continuousOn
  obtain ⟨xmax, -, hxmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hρc.continuousOn
  have hc : 0 < S.ρ0 xmin := S.hρ0.pos xmin
  obtain ⟨Cm, hCm0, hCm⟩ := HRS.iid_field_comparison_proof hd2 m hmd (S.ρ0 xmin) (S.ρ0 xmax) hc
  obtain ⟨⟨Cb0, hCb⟩, hJ⟩ := prepared_scales_proof S 0 le_rfl
  obtain ⟨p₀, hp₀, Cj0, hCj⟩ := hJ (Or.inr hs)
  set Cb : ℝ := max Cb0 0 with hCbdef
  set Cj : ℝ := max Cj0 0 with hCjdef
  have hrw3 : ∀ N : ℕ, 2 ≤ N → 0 ≤ iidRateW d m N ^ ((1 : ℝ) / 3) := fun N hN =>
    Real.rpow_nonneg (fb_iidRateW_nonneg d m (by omega)) _
  obtain ⟨C2, hC2, h2⟩ := fb_W2 S m hm T hT p₀ hp₀ Cb Cj Cm (le_max_right _ _) (le_max_right _ _)
    hCm0 (fun N => iidRateW d m N ^ ((1 : ℝ) / 3)) hrw3
  refine ⟨2 * C2, by positivity, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hinit ν hν Ω' _ P' _ Y₀ Y hY
  haveI : IsProbabilityMeasure S.μ0 := HRS.isProb_withDensityReal S.hρ0.density
  have hinit' : law P X₀ = Measure.pi fun _ : Fin N => S.μ0 := by
    rw [hinit]; exact modulatedGibbs_zero _ _
  have hcov : preparedCov d S.s 0 S.μ0 = iidCov S.μ0 := by
    funext φ ψ; simp [preparedCov]
  rw [hcov] at hν
  have hlaw : law P (fun ω => etaE m (X₀ ω) S.μ0) =
      law (Measure.pi fun _ : Fin N => withDensityReal S.ρ0)
        (fun X : Config d N => etaE m X (withDensityReal S.ρ0)) := by
    rw [fb_law_eta S m hmd (by omega) P hSel.init_meas, hinit']
    rfl
  have hcmp := hCm S.ρ0 S.hρ0.density (fun x => by simpa using hxmin (Set.mem_univ x))
    (fun x => by simpa using hxmax (Set.mem_univ x)) ν hν N (by omega)
  have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hBk : relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ ∧
      S.B N (law P X₀) ≤ Cb * ((N : ℝ) * deltaN d S.s N) := by
    rw [hinit]
    obtain ⟨he, hb⟩ := hCb N hN
    refine ⟨he, hb.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hJk := hCj N hN
  rw [← hinit] at hJk
  have hJk' : S.J N (law P X₀) p₀ ≤ Cj * ((N : ℝ) * deltaN d S.s N) :=
    hJk.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hmain := h2 a ha N hN P X₀ W X hSel hfilt hBk.1 hJk.1 hBk.2 hJk' ν P' Y₀ Y hY
    (by rw [hlaw]; exact hcmp.2.2)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have e : deltaN d S.s N = deltaN d 0 N := by rw [hs]
  rw [e]
  obtain ⟨hr1, hr2⟩ := fb_zero_rates hd1 (by omega : 1 ≤ N)
  have hr := hrw3 N hN
  have hq : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hN0.le _
  rw [hr2]
  calc C2 * (Real.sqrt N * deltaN d 0 N + (N : ℝ) ^ (-(1 : ℝ) / 4) + iidRateW d m N ^ ((1 : ℝ) / 3))
      ≤ C2 * (2 * ((N : ℝ) ^ (-(1 : ℝ) / 4) + iidRateW d m N ^ ((1 : ℝ) / 3))) :=
        mul_le_mul_of_nonneg_left (by linarith) hC2.le
    _ = 2 * C2 * ((N : ℝ) ^ (-(1 : ℝ) / 4) + iidRateW d m N ^ ((1 : ℝ) / 3)) := by ring

/-- `prepared_full_bounds` (`HRS/Main/Headline.lean`) with the clause for `0 < β₀` removed: the clauses (i) and
(iii) for `β₀ = 0` (both are vacuous for `β₀ ≠ 0`).  Same binders, same constants layout. -/
theorem fb_prepared_full_bounds_beta0 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
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
        (β₀ = 0 →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.sqrt N * deltaN d S.s N + iidRateSmooth d m N) ∧
          wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N +
              deltaN d S.s N ^ ((1 : ℝ) / 4) + iidRateW d m N))) ∧
        (β₀ = 0 → S.s = 0 →
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 4) + iidRateW d m N ^ ((1 : ℝ) / 3)))) := by
  by_cases h0 : β₀ = 0
  · subst h0
    obtain ⟨C1, hC1, h1⟩ := fb_beta0_i S m hm T hT
    by_cases hs : S.s = 0
    · obtain ⟨C2, hC2, h2⟩ := fb_beta0_iii S m hm T hT hs
      refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
      intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hinit ν hν Ω' _ P' _ Y₀ Y hY
      have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hx : 0 ≤ Real.sqrt N * deltaN d S.s N := by positivity
      have hq : 0 ≤ deltaN d S.s N ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hδ.le _
      have hq2 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hN0.le _
      have hj := fb_iidRateW_nonneg d m (by omega : 1 ≤ N)
      have hj3 : 0 ≤ iidRateW d m N ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hj _
      obtain ⟨hs1, hw1⟩ := h1 a ha N hN P X₀ W X hSel hfilt hinit ν hν P' Y₀ Y hY
      refine ⟨fun _ => ⟨hs1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (add_nonneg hx (fb_iidRateSmooth_nonneg d m N))),
        hw1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (add_nonneg (add_nonneg hx hq) hj)))⟩, fun _ _ => ?_⟩
      exact (h2 a ha N hN P X₀ W X hSel hfilt hinit ν hν P' Y₀ Y hY).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (add_nonneg hq2 hj3)))
    · refine ⟨C1, hC1, ?_⟩
      intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hinit ν hν Ω' _ P' _ Y₀ Y hY
      exact ⟨fun _ => h1 a ha N hN P X₀ W X hSel hfilt hinit ν hν P' Y₀ Y hY,
        fun _ hs' => absurd hs' hs⟩
  · refine ⟨1, one_pos, ?_⟩
    intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hinit ν hν Ω' _ P' _ Y₀ Y hY
    exact ⟨fun h => absurd h h0, fun h => absurd h h0⟩

end Main

end HRS

end
