import HRS.MS.MfeConfAux17

/-!
# S.B.1: the frozen rows from the two analytic inputs `SbMovEnt` (F9) and `SbLogK` (F3)

`SuperParts d s`, `SubParts d s` state `SbMovEnt ∧ SbLogK` for all data of the two frozen statements (the hypotheses are exactly
those of `SuperDiss`, `SubDiss`, without the transport bound `K`).  For `d ≥ 2`:

* `sb1_superDiss_of_parts`, `sb1_subDiss_of_parts`: `SuperParts ⇒ SuperDiss`, `SubParts ⇒ SubDiss` (`sb1_diss_of_parts`);
* `sb1_super_of_parts`, `sb1_sub_of_parts`: the exact frozen conclusions of `mfe_confined_rd_gradient_super/_sub` from `SuperParts`,
  `SubParts` (composition with `sb1_super_of_diss`, `sb1_sub_of_diss`).

What remains for S.B.1 (`d ≥ 2`) is therefore exactly: prove `SbMovEnt` (whole-space `mov_ent_ineq`) and `SbLogK`
(whole-space `movT_logK_integral`) for the data of the rows (see `HANDOFF_SB1.md`); `d = 1` of the super row needs in addition a
`d = 1` pressure packet (S3.1 is proved for `2 ≤ d` only).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- `SbMovEnt ∧ SbLogK` for all data of `mfe_confined_rd_gradient_super`. -/
def SuperParts (d : ℕ) (s : ℝ) : Prop :=
  ∀ (D : Whole.WholeDyn d), D.s = s → ContDiff ℝ 3 D.V →
    (∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 D.V x‖ ≤ B) →
    (∃ cV CV : ℝ, 0 < cV ∧ ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) →
    ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → Whole.EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Whole.EucConfig d N),
      Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X →
      SbMovEnt D N T ρ P X₀ X ∧ SbLogK D N T ρ

/-- `SbMovEnt ∧ SbLogK` for all data of `mfe_confined_rd_gradient_sub`. -/
def SubParts (d : ℕ) (s : ℝ) : Prop :=
  ∀ (D : Whole.WholeDyn d), D.s = s →
    ∀ (Q : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) (c q : ℝ), 0 < q → Q.IsSymm →
      (Q - q • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef →
      (∀ x, D.V x = (1 / 2) * inner ℝ x (Torus.matVec Q x) + inner ℝ b x + c) →
    ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → Whole.EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Whole.EucConfig d N),
      Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X →
      SbMovEnt D N T ρ P X₀ X ∧ SbLogK D N T ρ

theorem sb1_superDiss_of_parts (hd2 : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hP : SuperParts d s) : SuperDiss d s := by
  intro D hDs hV3 hB hc N hN T Λ r hT Ω _ P _ ρ X₀ W X h K hKi hK
  subst hDs
  obtain ⟨hE, hL⟩ := hP D rfl hV3 hB hc N hN T Λ r hT P ρ X₀ W X h
  exact sb1_diss_of_parts hd2 hN h hs0 hsd hE hL

theorem sb1_subDiss_of_parts (hd2 : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (a : ℝ)
    (hP : SubParts d s) : SubDiss d s a := by
  intro D hDs Q b c q hq hQ hQq hVQ N hN T Λ r hT Ω _ P _ ρ X₀ W X h K hKi hK
  subst hDs
  obtain ⟨hE, hL⟩ := hP D rfl Q b c q hq hQ hQq hVQ N hN T Λ r hT P ρ X₀ W X h
  exact sb1_diss_of_parts hd2 hN h hs0 hsd hE hL

/-- The frozen alternative (i) of S.B.1 (`d ≥ 2`) from the two analytic inputs. -/
theorem sb1_super_of_parts (hd2 : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hsc : (d : ℝ) - 2 ≤ s)
    (hP : SuperParts d s) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : Whole.WholeDyn d), D.s = s → ContDiff ℝ 3 D.V →
      (∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 D.V x‖ ≤ B) →
      (∃ cV CV : ℝ, 0 < cV ∧ ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → Whole.EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Whole.EucConfig d N),
        Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X →
      ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc 0 T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (K t)) →
      ∀ t ∈ Set.Icc 0 T,
        (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
        Whole.MFEFiniteW d s (P.map (X (Real.toNNReal t))) (Whole.withDensityReal (ρ t)) ∧
        Whole.modulatedFreeEnergyW d s D.invβ (P.map (X (Real.toNNReal t)))
            (Whole.withDensityReal (ρ t)) + oNΛ d s C₀ Λ N ≤
          Real.exp (C * ∫ r in Set.Icc 0 T, K r) *
            (Whole.modulatedFreeEnergyW d s D.invβ (P.map X₀) (Whole.withDensityReal (ρ 0)) +
              oNΛ d s C₀ Λ N) :=
  sb1_super_of_diss (by omega) hs0 hsd hsc (sb1_superDiss_of_parts hd2 hs0 hsd hP)

/-- The frozen alternative (ii) of S.B.1 from the two analytic inputs (`s < d - 2` forces `d ≥ 3`). -/
theorem sb1_sub_of_parts {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) (hP : SubParts d s) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : Whole.WholeDyn d), D.s = s →
      ∀ (Q : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) (c q : ℝ), 0 < q → Q.IsSymm →
        (Q - q • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef →
        (∀ x, D.V x = (1 / 2) * inner ℝ x (Torus.matVec Q x) + inner ℝ b x + c) →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → Whole.EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Whole.EucConfig d N),
        Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X →
      ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc 0 T, Whole.HasFracTransportBound (a / 2) (2 * d / (a - 2))
          (Whole.mfeTransport0W D (ρ t))
          (K t - ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q‖)) →
        ∀ t ∈ Set.Icc 0 T,
        (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
        Whole.MFEFiniteW d s (P.map (X (Real.toNNReal t))) (Whole.withDensityReal (ρ t)) ∧
        Whole.modulatedFreeEnergyW d s D.invβ (P.map (X (Real.toNNReal t)))
            (Whole.withDensityReal (ρ t)) + oNΛ d s C₀ Λ N ≤
          Real.exp (C * ∫ r in Set.Icc 0 T, K r) *
            (Whole.modulatedFreeEnergyW d s D.invβ (P.map X₀) (Whole.withDensityReal (ρ 0)) +
              oNΛ d s C₀ Λ N) :=
  sb1_sub_of_diss hs0 hsd a ha (sb1_subDiss_of_parts (by
    have : (2 : ℝ) < d := by linarith
    exact_mod_cast this.le) hs0 (by linarith) a hP)

end HRS.MS.MfeConf
