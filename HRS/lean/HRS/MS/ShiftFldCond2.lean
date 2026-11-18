import HRS.MS.ShiftFldCond

/-!
# S79: `shifted_field_path` conditional on S2.1(i) and on window stationarity

`shifted_field_path_of_S21 (h21 : type_of% @whole_space_stationary) (hX : ParticleWindowStationary d s a β)
  (hG : GaussianWindowStationary d s a β) : <the frozen conclusion of shifted_field_path at (d, s, a, β)>`.

The frozen statement quantifies a window start `a₀ ≥ 0`, while S2.1(i) is stated at `a₀ = 0`.  The two extra hypotheses are TRUE statements
that the TeX closes by "stationarity of both laws" (S L6190) and that are not in the tree:
* `ParticleWindowStationary`: for a canonical realization the exactly centered window `ζ_N^{a₀+·}` is a.e. measurable and has the law
  of `ζ_N^{·}` (time shift of the filtered strong solution, `law (X_{a₀+·}) = law (X_·)`, whose finite-dimensional marginal at one time is
  `GibbsInvariant`);
* `GaussianWindowStationary`: for the stationary Gaussian field the window `Z^{a₀+·}` is a.e. measurable and has the law of `Z^{·}`
  (semigroup property of `propagatorW` and invariance of the susceptibility covariance, the Lyapunov identity).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.Whole.S79

open HRS (Euc)

/-- Stationarity of the exactly centered particle window (a true statement; not proved here). -/
def ParticleWindowStationary (d : ℕ) (s a β : ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → ∀ N : ℕ, 2 ≤ N →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      IsCanonicalRealization d s a β N P X₀ W X → ∀ a₀ : ℝ, 0 ≤ a₀ →
        AEMeasurable (zetaPathW (wholeSpaceIndex d) T a₀ P X) P ∧
        HRS.law P (zetaPathW (wholeSpaceIndex d) T a₀ P X) =
          HRS.law P (zetaPathW (wholeSpaceIndex d) T 0 P X)

/-- Stationarity of the Gaussian field (a true statement; not proved here). -/
def GaussianWindowStationary (d : ℕ) (s a β : ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
      IsStationaryGaussianField d s a β (wholeSpaceIndex d) ρβ P' Z → ∀ a₀ : ℝ, 0 ≤ a₀ →
        AEMeasurable (processWindow (wholeSpaceIndex d) T a₀ Z) P' ∧
        HRS.law P' (processWindow (wholeSpaceIndex d) T a₀ Z) =
          HRS.law P' (processWindow (wholeSpaceIndex d) T 0 Z)

theorem s79_localizationRate_nonneg (d : ℕ) (s C₀ : ℝ) (N : ℕ) : 0 ≤ localizationRate d s C₀ N := by
  unfold localizationRate
  exact Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.sqrt_nonneg _)) _

theorem shifted_field_path_of_S21 {d : ℕ} {s : ℝ} (h21 : HRS.Whole.WholeSpaceStationaryStatement)
    (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (hX : ParticleWindowStationary d s a β) (hG : GaussianWindowStationary d s a β)
    (T : ℝ) (hT : 0 < T) :
    ∃ C₀ C : ℝ, (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (withDensityReal ρβ) + oN d s C₀ N) ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d s a β N P X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
        IsStationaryGaussianField d s a β (wholeSpaceIndex d) ρβ P' Z →
      ∀ a₀ : ℝ, 0 ≤ a₀ →
        AEMeasurable (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X (fun _ => ρβ)) P ∧
        AEMeasurable (fun ζ' => processWindow (wholeSpaceIndex d) T a₀ Z ζ' +
          constPath (wholeSpaceIndex d) T ((N : ℝ) ^ (3 / 2 - biasP d s) •
            biasField (wholeSpaceIndex d) d s β ρβ)) P' ∧
        smoothDist 2 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X (fun _ => ρβ)))
            (law P' (fun ζ' => processWindow (wholeSpaceIndex d) T a₀ Z ζ' +
              constPath (wholeSpaceIndex d) T ((N : ℝ) ^ (3 / 2 - biasP d s) •
                biasField (wholeSpaceIndex d) d s β ρβ))) ≤
          C * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N +
            (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s)) ∧
        wassersteinE 1 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X (fun _ => ρβ)))
            (law P' (fun ζ' => processWindow (wholeSpaceIndex d) T a₀ Z ζ' +
              constPath (wholeSpaceIndex d) T ((N : ℝ) ^ (3 / 2 - biasP d s) •
                biasField (wholeSpaceIndex d) d s β ρβ))) ≤
          ENNReal.ofReal (C * (deltaN d s N ^ ((3 : ℝ) / 20) +
            Real.sqrt (localizationRate d s C₀ N) +
            (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s))) := by
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs0 : 0 ≤ s := by linarith
  have hmd : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex
    push_cast
    linarith
  obtain ⟨C₀, C, hcomp, hmain⟩ := h21 hd s hs0 hsd a β ha hβ T hT
  obtain ⟨K, hK0, hK⟩ := s79_core hd hs hsd ha hβ hmd (s := s)
  refine ⟨C₀, max C 0 + K, hcomp, ?_⟩
  intro ρβ hρβ N hN Ω _ P _ X₀ W X hR Ω' _ P' _ Z hZ a₀ ha₀
  have hRN := hR
  obtain ⟨hx1, hx2⟩ := hX T hT N hN P X₀ W X hR a₀ ha₀
  obtain ⟨hg1, hg2⟩ := hG T hT ρβ hρβ P' Z hZ a₀ ha₀
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hmain ρβ hρβ N hN hRN.invariant P X₀ W X hRN.brownian hRN.indep
    hRN.init (hRN.solution T) P' Z (hZ T)
  obtain ⟨c1, c2, c3, c4⟩ := hK T a₀ ρβ hρβ N hN P X₀ W X hR P' Z hx1 hg1
  rw [hx2, hg2] at c3 c4
  have hδ0 : 0 ≤ Real.sqrt (deltaN d s N) := Real.sqrt_nonneg _
  have hw0 := s79_localizationRate_nonneg d s C₀ N
  have hpow : 0 ≤ (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hCm : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨c1, c2, ?_, ?_⟩
  · refine c3.trans ?_
    have h1 : C * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) ≤
        max C 0 * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hδ0 hw0)
    have h2 : K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) ≤
        (max C 0 + K) * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) := by
      nlinarith [mul_nonneg hCm hpow]
    have h3 : max C 0 * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) ≤
        (max C 0 + K) * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) := by
      nlinarith [mul_nonneg hK0 (add_nonneg hδ0 hw0)]
    nlinarith
  · refine c4.trans ?_
    have hδp : 0 ≤ deltaN d s N ^ ((3 : ℝ) / 20) :=
      Real.rpow_nonneg (s79_deltaN_pos hs (by omega)).le _
    have hsw : 0 ≤ Real.sqrt (localizationRate d s C₀ N) := Real.sqrt_nonneg _
    have hA : 0 ≤ max C 0 * (deltaN d s N ^ ((3 : ℝ) / 20) +
        Real.sqrt (localizationRate d s C₀ N)) := mul_nonneg hCm (add_nonneg hδp hsw)
    have hB : 0 ≤ K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) := mul_nonneg hK0 hpow
    calc _ ≤ ENNReal.ofReal (max C 0 * (deltaN d s N ^ ((3 : ℝ) / 20) +
            Real.sqrt (localizationRate d s C₀ N))) +
          ENNReal.ofReal (K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s)) :=
          add_le_add (hz4.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hδp hsw)))) le_rfl
      _ = ENNReal.ofReal (max C 0 * (deltaN d s N ^ ((3 : ℝ) / 20) +
            Real.sqrt (localizationRate d s C₀ N)) +
          K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s)) := (ENNReal.ofReal_add hA hB).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [mul_nonneg hK0 (add_nonneg hδp hsw), mul_nonneg hCm hpow]

/-- Tie: the conditional theorem has exactly the type of the frozen `shifted_field_path` (once `h21` and the two window-stationarity
statements, on the range `2 ≤ d`, `d/2 < s < d`, `a, β > 0`, are available). -/
theorem shifted_field_path_cond_tie (h21 : HRS.Whole.WholeSpaceStationaryStatement)
    (hX : ∀ (d : ℕ) (s a β : ℝ), 2 ≤ d → (d : ℝ) / 2 < s → s < d → 0 < a → 0 < β →
      ParticleWindowStationary d s a β)
    (hG : ∀ (d : ℕ) (s a β : ℝ), 2 ≤ d → (d : ℝ) / 2 < s → s < d → 0 < a → 0 < β →
      GaussianWindowStationary d s a β) :
    type_of% @HRS.Whole.shifted_field_path := by
  intro d s hd hs hsd a β ha hβ T hT
  exact shifted_field_path_of_S21 h21 hd hs hsd a β ha hβ (hX d s a β hd hs hsd ha hβ)
    (hG d s a β hd hs hsd ha hβ) T hT

end HRS.Whole.S79
