import HRS.MS.MfeConfAux59

/-!
# S.B.1: the closing assembly with the transport bound `K` passed through

`SbLogK` is now proved for all data of the two rows, including the transport bound `K` (`sb1_superLogK`, `sb1_subLogK`,
Aux38).  What remains of S.B.1 is exactly the whole-space `mov_ent_ineq` for the same data:

* `SuperMovEnt d s`, `SubMovEnt d s a`: `SbMovEnt D N T ρ P X₀ X` for all data of the rows (with `K`);
* `sb1_super_of_movEnt`, `sb1_sub_of_movEnt`: the exact frozen conclusions of `mfe_confined_rd_gradient_super/_sub` from
  `SuperMovEnt`, `SubMovEnt` (using `sb1_superLogK`, `sb1_subLogK`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- `SbMovEnt` for all data of `mfe_confined_rd_gradient_super` (with the transport bound `K`). -/
def SuperMovEnt (d : ℕ) (s : ℝ) : Prop :=
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
      SbMovEnt D N T ρ P X₀ X

/-- `SbMovEnt` for all data of `mfe_confined_rd_gradient_sub` (with the transport bound `K`). -/
def SubMovEnt (d : ℕ) (s a : ℝ) : Prop :=
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
      SbMovEnt D N T ρ P X₀ X

theorem sb1_superDiss_of_movEnt (hd : 1 ≤ d) (hd2 : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hE : SuperMovEnt d s) : SuperDiss d s := by
  intro D hDs hV3 hB hc N hN T Λ r hT Ω _ P _ ρ X₀ W X h K hKi hK
  have hL := sb1_superLogK hd hs0 hsd D hDs hV3 hB hc N hN T Λ r hT P ρ X₀ W X h K hKi hK
  have hEn := hE D hDs hV3 hB hc N hN T Λ r hT P ρ X₀ W X h K hKi hK
  subst hDs
  exact sb1_diss_of_parts hd2 hN h hs0 hsd hEn hL

theorem sb1_subDiss_of_movEnt (hd3 : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) (hE : SubMovEnt d s a) : SubDiss d s a := by
  intro D hDs Q b c q hq hQ hQq hVQ N hN T Λ r hT Ω _ P _ ρ X₀ W X h K hKi hK
  have hL := sb1_subLogK hd3 hs0 hsd a ha D hDs Q b c q hq hQ hQq hVQ N hN T Λ r hT P ρ X₀ W X h K hKi hK
  have hEn := hE D hDs Q b c q hq hQ hQq hVQ N hN T Λ r hT P ρ X₀ W X h K hKi hK
  subst hDs
  have hd2 : 2 ≤ d := by omega
  have hsd' : D.s < d := by linarith
  exact sb1_diss_of_parts hd2 hN h hs0 hsd' hEn hL

/-- The frozen alternative (i) of S.B.1 (`d ≥ 2`) from the whole-space `mov_ent_ineq` alone. -/
theorem sb1_super_of_movEnt (hd2 : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hsc : (d : ℝ) - 2 ≤ s)
    (hE : SuperMovEnt d s) :
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
  sb1_super_of_diss (by omega) hs0 hsd hsc (sb1_superDiss_of_movEnt (by omega) hd2 hs0 hsd hE)

/-- The frozen alternative (ii) of S.B.1 from the whole-space `mov_ent_ineq` alone. -/
theorem sb1_sub_of_movEnt (hd3 : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) (hE : SubMovEnt d s a) :
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
  sb1_sub_of_diss hs0 hsd a ha (sb1_subDiss_of_movEnt hd3 hs0 hsd a ha hE)

end HRS.MS.MfeConf
