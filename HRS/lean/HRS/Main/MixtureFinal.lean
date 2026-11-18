import HRS.Main.MixEnt5
import HRS.Main.MixEnt8
import HRS.Main.FullBoundsBeta0

/-!
# MIXFIN: relocated proof of `mixture_full_bounds` (Example 2.6, TeX L848-852)

RELOCATION PATTERN: the frozen statement of `HRS/Main/Headline.lean` is not edited; it is restated VERBATIM as
`mixture_full_bounds_proof` and tied by `example := (@mixture_full_bounds_proof : type_of% @HRS.Main.mixture_full_bounds)`.

Inputs: the initial rates of Proposition 5.9 (`iid_field_mixture_proof`, rewritten with `therm_mixturePrep_eq`),
the entropy inputs `mx_B_mixture` (`B_N ≤ C Nδ_N`) and `mx_Lp_mixture` (`s = 0`: `dmix/dQ ∈ L^{p₀}`, `J_N ≤ C Nδ_N`),
and the abstract assembly `fb_smooth_W1`, `fb_W2` of Theorem 2.5.  Packet prefix `mxf_`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- The initial rates of Proposition 5.9 for the mixture preparation: all three clauses, in the form used by
`mixture_full_bounds` (limit law `ν_mix` with the factor `1 / 2`). -/
theorem mxf_init (S : PreparedData d) (m : ℝ) (hmd : (d : ℝ) / 2 < m) (b : Torus d → ℝ)
    (hb : Torus.IsSmooth b) (hb0 : pair S.μ0 b = 0) (a₀ : ℝ)
    (γ : Measure (NegSobolev d m)) (hγ : IsCenteredGaussianWithCov m γ (iidCov S.μ0)) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ N : ℕ, 2 ≤ N → 4 * a₀ ^ 2 * (⨆ x, |b x|) ^ 2 ≤ (N : ℝ) →
      smoothDist 2 (law (mixturePrep S.μ0 b a₀ N) (fun X => etaE m X S.μ0))
          ((1 / 2 : ℝ≥0∞) • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
            (1 / 2 : ℝ≥0∞) • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x))) ≤
        Cm * iidRateSmooth d m N ∧
      wassersteinE 1 (law (mixturePrep S.μ0 b a₀ N) (fun X => etaE m X S.μ0))
          ((1 / 2 : ℝ≥0∞) • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
            (1 / 2 : ℝ≥0∞) • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x))) ≤
        ENNReal.ofReal (Cm * iidRateW d m N) ∧
      wassersteinE 2 (law (mixturePrep S.μ0 b a₀ N) (fun X => etaE m X S.μ0))
          ((1 / 2 : ℝ≥0∞) • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
            (1 / 2 : ℝ≥0∞) • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x))) ≤
        ENNReal.ofReal (Cm * iidRateW d m N ^ ((1 : ℝ) / 3)) := by
  have hbc : Continuous b := therm_continuous_of_smooth hb
  have hbm : Measurable b := hbc.measurable
  have hρc : Continuous S.ρ0 := therm_continuous_of_smooth S.hρ0.smooth
  set B : ℝ := ⨆ x, |b x| with hBdef
  have hB : ∀ x, |b x| ≤ B := fun x => mx_abs_le_iSup hb x
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨xmin, -, hxmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hρc.continuousOn
  obtain ⟨xmax, -, hxmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hρc.continuousOn
  have hc : 0 < S.ρ0 xmin := S.hρ0.pos xmin
  have hbL : MemLp b ⊤ (volume : Measure (Torus d)) :=
    MemLp.of_bound hbc.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hnorm : (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal ≤ B := by
    have h1 : eLpNorm b ⊤ (volume : Measure (Torus d)) ≤ ENNReal.ofReal B := by
      rw [eLpNorm_exponent_top]
      exact eLpNormEssSup_le_of_ae_bound
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
      all_goals first | exact hbc.aestronglyMeasurable | skip
    exact ENNReal.toReal_le_of_le_ofReal hB0 h1
  obtain ⟨Cm, hCm0, hCm⟩ := HRS.iid_field_mixture_proof S.hd m hmd (S.ρ0 xmin) (S.ρ0 xmax) hc a₀ b
    hbm hbL
  refine ⟨Cm, hCm0, fun N hN2 hN4' => ?_⟩
  have h4 : 4 * a₀ ^ 2 * (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal ^ 2 ≤ N := by
    have h1 : (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg hnorm 2
    have h2 : 4 * a₀ ^ 2 * (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal ^ 2 ≤
        4 * a₀ ^ 2 * B ^ 2 := by gcongr
    linarith
  have := (hCm S.ρ0 S.hρ0.density (fun x => by simpa using hxmin (Set.mem_univ x))
    (fun x => by simpa using hxmax (Set.mem_univ x)) hb0 γ hγ N hN2 h4)
  rw [← therm_mixturePrep_eq S b hbm a₀ N] at this
  simp only [therm_ofFun_smul] at this
  simp only [one_div (2 : ℝ≥0∞)]
  exact this

/-- Clauses 1 and 2 (smooth and `W_1`) of `mixture_full_bounds`. -/
theorem mxf_part12 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (b : Torus d → ℝ) (hb : Torus.IsSmooth b) (hb0 : pair S.μ0 b = 0) (a₀ : ℝ)
    (γ : Measure (NegSobolev d m)) (hγ : IsCenteredGaussianWithCov m γ (iidCov S.μ0)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N → 4 * a₀ ^ 2 * (⨆ x, |b x|) ^ 2 ≤ (N : ℝ) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = mixturePrep S.μ0 b a₀ N →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T)
          ((1 / 2 : ℝ≥0∞) • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
            (1 / 2 : ℝ≥0∞) • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)))
          P' Y₀ Y →
        smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          C * (Real.sqrt N * deltaN d S.s N + iidRateSmooth d m N) ∧
        wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) +
            iidRateW d m N)) := by
  have hmd : (d : ℝ) / 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cm, hCm0, hCm⟩ := mxf_init S m hmd b hb hb0 a₀ γ hγ
  obtain ⟨Cb, hCb0, hCb⟩ := mx_B_mixture S b hb hb0 a₀
  obtain ⟨C1, hC1, h1⟩ := fb_smooth_W1 S m hm T hT Cb Cm Cm hCb0.le hCm0 hCm0
    (iidRateSmooth d m) (iidRateW d m) (fun N _ => fb_iidRateSmooth_nonneg d m N)
    (fun N hN => fb_iidRateW_nonneg d m (by omega))
  refine ⟨C1, hC1, ?_⟩
  intro a ha N hN hN4 Ω _ P _ X₀ W X hSel hfilt hinit Ω' _ P' _ Y₀ Y hY
  have hlaw : law P (fun ω => etaE m (X₀ ω) S.μ0) =
      law (mixturePrep S.μ0 b a₀ N) (fun X => etaE m X S.μ0) := by
    rw [fb_law_eta S m hmd (by omega) P hSel.init_meas, hinit]
  have hBk := hCb N hN hN4
  rw [← hinit] at hBk
  obtain ⟨hs1, hw1, -⟩ := hCm N hN hN4
  exact h1 a ha N hN P X₀ W X hSel hfilt hBk.1 hBk.2 _ P' Y₀ Y hY (by rw [hlaw]; exact hs1)
    (by rw [hlaw]; exact hw1)

/-- Clause 3 (`W_2`, `s = 0`) of `mixture_full_bounds`. -/
theorem mxf_part3 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (b : Torus d → ℝ) (hb : Torus.IsSmooth b) (hb0 : pair S.μ0 b = 0) (a₀ : ℝ)
    (γ : Measure (NegSobolev d m)) (hγ : IsCenteredGaussianWithCov m γ (iidCov S.μ0))
    (hs : S.s = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N → 4 * a₀ ^ 2 * (⨆ x, |b x|) ^ 2 ≤ (N : ℝ) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = mixturePrep S.μ0 b a₀ N →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T)
          ((1 / 2 : ℝ≥0∞) • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
            (1 / 2 : ℝ≥0∞) • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)))
          P' Y₀ Y →
        wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 4) + iidRateW d m N ^ ((1 : ℝ) / 3))) := by
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hmd : (d : ℝ) / 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cm, hCm0, hCm⟩ := mxf_init S m hmd b hb hb0 a₀ γ hγ
  obtain ⟨Cb, hCb0, hCb⟩ := mx_B_mixture S b hb hb0 a₀
  obtain ⟨p₀, hp₀, hLp⟩ := mx_Lp_mixture S hs
  obtain ⟨Cj, hCj0, hCj⟩ := hLp b hb hb0 a₀
  have hrw3 : ∀ N : ℕ, 2 ≤ N → 0 ≤ iidRateW d m N ^ ((1 : ℝ) / 3) := fun N hN =>
    Real.rpow_nonneg (fb_iidRateW_nonneg d m (by omega)) _
  obtain ⟨C2, hC2, h2⟩ := fb_W2 S m hm T hT p₀ hp₀ Cb Cj Cm hCb0.le hCj0.le hCm0
    (fun N => iidRateW d m N ^ ((1 : ℝ) / 3)) hrw3
  refine ⟨2 * C2, by positivity, ?_⟩
  intro a ha N hN hN4 Ω _ P _ X₀ W X hSel hfilt hinit Ω' _ P' _ Y₀ Y hY
  have hlaw : law P (fun ω => etaE m (X₀ ω) S.μ0) =
      law (mixturePrep S.μ0 b a₀ N) (fun X => etaE m X S.μ0) := by
    rw [fb_law_eta S m hmd (by omega) P hSel.init_meas, hinit]
  have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hBk := hCb N hN hN4
  have hJk := hCj N hN hN4
  rw [← hinit] at hBk hJk
  have hmain := h2 a ha N hN P X₀ W X hSel hfilt hBk.1 hJk.1 hBk.2 hJk.2 _ P' Y₀ Y hY
    (by rw [hlaw]; exact (hCm N hN hN4).2.2)
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

theorem mixture_full_bounds_proof (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (b : Torus d → ℝ) (hb : Torus.IsSmooth b) (hb0 : pair S.μ0 b = 0) (a₀ : ℝ)
    (γ : Measure (NegSobolev d m)) (hγ : IsCenteredGaussianWithCov m γ (iidCov S.μ0)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N → 4 * a₀ ^ 2 * (⨆ x, |b x|) ^ 2 ≤ (N : ℝ) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = mixturePrep S.μ0 b a₀ N →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T)
          ((1 / 2 : ℝ≥0∞) • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
            (1 / 2 : ℝ≥0∞) • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)))
          P' Y₀ Y →
        smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          C * (Real.sqrt N * deltaN d S.s N + iidRateSmooth d m N) ∧
        wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) +
            iidRateW d m N)) ∧
        (S.s = 0 →
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 4) + iidRateW d m N ^ ((1 : ℝ) / 3)))) := by
  obtain ⟨C1, hC1, h1⟩ := mxf_part12 S m hm T hT b hb hb0 a₀ γ hγ
  by_cases hs : S.s = 0
  · obtain ⟨C2, hC2, h2⟩ := mxf_part3 S m hm T hT b hb hb0 a₀ γ hγ hs
    refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
    intro a ha N hN hN4 Ω _ P _ X₀ W X hSel hfilt hinit Ω' _ P' _ Y₀ Y hY
    have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hx : 0 ≤ Real.sqrt N * deltaN d S.s N := by positivity
    have hq : 0 ≤ deltaN d S.s N ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hδ.le _
    have hq2 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hN0.le _
    have hj := fb_iidRateW_nonneg d m (by omega : 1 ≤ N)
    have hj3 : 0 ≤ iidRateW d m N ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hj _
    obtain ⟨hs1, hw1⟩ := h1 a ha N hN hN4 P X₀ W X hSel hfilt hinit P' Y₀ Y hY
    refine ⟨hs1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (add_nonneg hx (fb_iidRateSmooth_nonneg d m N))),
      hw1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (add_nonneg (add_nonneg hx hq) hj))), fun _ => ?_⟩
    exact (h2 a ha N hN hN4 P X₀ W X hSel hfilt hinit P' Y₀ Y hY).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (add_nonneg hq2 hj3)))
  · refine ⟨C1, hC1, ?_⟩
    intro a ha N hN hN4 Ω _ P _ X₀ W X hSel hfilt hinit Ω' _ P' _ Y₀ Y hY
    obtain ⟨hs1, hw1⟩ := h1 a ha N hN hN4 P X₀ W X hSel hfilt hinit P' Y₀ Y hY
    exact ⟨hs1, hw1, fun h => absurd h hs⟩

example := (@mixture_full_bounds_proof : type_of% @HRS.Main.mixture_full_bounds)

end Main

end HRS

end
