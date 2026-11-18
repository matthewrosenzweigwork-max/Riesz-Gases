import HRS.MS.CritWholeW2Shift
import HRS.MS.WsStatAux12
import HRS.MS.ShiftFldAux8

/-!
# S8.1 (worker S81W2): the burn-in removal step of `S81bW2Zero`

Namespace `HRS.Whole.S81W2`, prefix `s81w2_`.

The GPT-6 Pro proof of `S81bW2Zero` (PRO_MC/S81_physical_gaussian, Sections 5-7) consists of

1. a coupling at burn-in `u` of the exactly centered window `ζ_N^{u+·}` with a Gaussian path of the law of the
   stationary Gaussian field window `Z|_{[0,T]}`, of `L²` cost `C (e^{-cu} + N^{-1/2})`  (`S81W2Coupling`),
2. path-law stationarity of the particle window, `Law ζ_N^{u+·} = Law ζ_N^{0+·}`  (`S81W2PathStat`; this is
   `ParticleWindowStationary` of `ShiftFldCond2` for general `m`, it needs weak uniqueness of the SDE, see the handoff),
3. `u → ∞` at fixed `N`.

This file proves step 3 and the two measurability clauses: `s81w2_zero_of_coupling : S81W2Coupling → S81W2PathStat → S81bW2Zero`.
Both hypotheses are true statements (Pro paper), non-vacuous, and carry no junk values: the coupling lives on an honest
probability space with a.e.-measurable path maps whose pushforwards are the two laws.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81W2

/-- Step 1 (Pro Sections 3-6, uses S8.2 `weighted_critical_forcing`, S8.6, S8.7, S8.8): the burn-in coupling.
`C, c, u0` precede `ρβ`, `N`, the realizations and `u`. -/
def S81W2Coupling : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ (a β : ℝ), 0 < a → 0 < β → ∀ (m : ℝ), (wholeSpaceIndex d : ℝ) ≤ m →
    ∀ T : ℝ, 0 < T →
    ∃ C c u0 : ℝ, 0 < c ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ →
      ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d m),
        IsStationaryGaussianField d ((d : ℝ) / 2) a β m ρβ P' Z →
      ∀ u : ℝ, u0 ≤ u →
        ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (Q : Measure Ω'') (A G : Ω'' → OscPath d m T),
          IsProbabilityMeasure Q ∧ AEMeasurable A Q ∧ AEMeasurable G Q ∧
          Q.map A = law P (zetaPathW m T u P X) ∧ Q.map G = law P' (processWindow m T 0 Z) ∧
          (∫⁻ ω, ENNReal.ofReal (‖A ω - G ω‖ ^ (2 : ℝ)) ∂Q) ^ (1 / (2 : ℝ)) ≤
            ENNReal.ofReal (C * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ))))

/-- Step 2: path-law stationarity of the exactly centered particle window (needs weak uniqueness of the
collision-free strong solutions; `ParticleWindowStationary` of `ShiftFldCond2`, for general `m`). -/
def S81W2PathStat : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ (a β : ℝ), 0 < a → 0 < β → ∀ (m : ℝ), (wholeSpaceIndex d : ℝ) ≤ m →
    ∀ T : ℝ, 0 < T → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ u : ℝ, 0 ≤ u →
        law P (zetaPathW m T u P X) = law P (zetaPathW m T 0 P X)

/-- The zero-start window of a canonical realization is a.e. measurable. -/
theorem s81w2_zeta_aemeas {d : ℕ} (hd : 2 ≤ d) {a β : ℝ} {N : ℕ} (hN : 2 ≤ N) {m : ℝ}
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) {T : ℝ} (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X₀ : Ω → EucConfig d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hR : IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X) :
    AEMeasurable (zetaPathW m T 0 P X) P := by
  have hX := hR.solution T
  haveI : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hX.adapted 0).aemeasurable).2 inferInstance
  refine HRS.MS.S21.s21_zeta_aemeas hd (by omega) (m := m) ?_ hT.le P hX (P.map (X 0)) ?_
  · have h1 : ((24 * d + 240 : ℕ) : ℝ) = 24 * (d : ℝ) + 240 := by push_cast; ring
    have h2 : (wholeSpaceIndex d : ℝ) = 24 * (d : ℝ) + 240 := h1
    have h3 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  · intro t _
    exact (HRS.Whole.S79.s79p_law_init hR t).trans (HRS.Whole.S79.s79p_law_init hR 0).symm

/-- The window of a canonical realization starting at `u`, as the zero-start window of a canonical realization. -/
theorem s81w2_main {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) (hc : S81W2Coupling)
    (hs : S81W2PathStat) :
    ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d m),
        IsStationaryGaussianField d ((d : ℝ) / 2) a β m ρβ P' Z →
        AEMeasurable (processWindow m T 0 Z) P' ∧
          AEMeasurable (zetaPathW m T 0 P X) P ∧
          wassersteinE 2 (law P (zetaPathW m T 0 P X)) (law P' (processWindow m T 0 Z)) ≤
            ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨C, c, u0, hc0, hC⟩ := hc hd a β ha hβ m hm T hT
  refine ⟨C, fun ρβ hρβ N hN Ω _ P _ X₀ W X hR Ω' _ P' _ Z hZ => ?_⟩
  refine ⟨HRS.MS.S21.s21_Z_aemeas P' (hZ T) hT.le, s81w2_zeta_aemeas hd hN hm hT hR, ?_⟩
  have hbound : ∀ u : ℝ, max u0 0 ≤ u → wassersteinE 2 (law P (zetaPathW m T 0 P X))
      (law P' (processWindow m T 0 Z)) ≤
        ENNReal.ofReal (C * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) := by
    intro u hu
    obtain ⟨Ω'', _, Q, A, G, hQ, hA, hG, hAl, hGl, hcost⟩ :=
      hC ρβ hρβ N hN P X₀ W X hR P' Z hZ u (le_trans (le_max_left _ _) hu)
    rw [← hs hd a β ha hβ m hm T hT N hN P X₀ W X hR u (le_trans (le_max_right _ _) hu), ← hAl,
      ← hGl]
    exact (wassersteinE_le_of_coupling Q 2 (by norm_num) A G hA hG).trans hcost
  have hlim : Tendsto (fun u : ℝ => ENNReal.ofReal (C * (Real.exp (-c * u) +
      (N : ℝ) ^ (-(1 / 2 : ℝ))))) atTop (𝓝 (ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ))))) := by
    refine (ENNReal.tendsto_ofReal ?_)
    have h0 : Tendsto (fun u : ℝ => Real.exp (-c * u)) atTop (𝓝 0) := by
      have : Tendsto (fun u : ℝ => -c * u) atTop atBot := by
        exact tendsto_id.const_mul_atTop_of_neg (by linarith)
      exact Real.tendsto_exp_atBot.comp this
    simpa using (h0.add_const ((N : ℝ) ^ (-(1 / 2 : ℝ)))).const_mul C
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨max u0 0, hbound⟩)

/-- Step 3 and assembly: the burn-in coupling and path-law stationarity give `S81bW2Zero`. -/
theorem s81w2_zero_of_coupling (hc : S81W2Coupling) (hs : S81W2PathStat) :
    HRS.Whole.BreakdownS81.S81bW2Zero := by
  intro d hd a β ha hβ m hm T hT
  exact s81w2_main hd a β ha hβ m hm T hT hc hs

/-- With the two hypotheses the three remaining S8.1 rows follow through the existing ties. -/
theorem s81w2_W2_of_coupling (hc : S81W2Coupling) (hs : S81W2PathStat) :
    type_of% @HRS.Whole.critical_whole_W2 :=
  HRS.Whole.BreakdownS81.s81b_W2_of_zero (s81w2_zero_of_coupling hc hs)

end HRS.Whole.S81W2
