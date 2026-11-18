import HRS.MS.MfeConfAux37

/-!
# S.B.1, packet F3 (part 19): `SbLogK` for the data of the two frozen rows

`SuperLogK d s`, `SubLogK d s a`: for all data of `mfe_confined_rd_gradient_super` (resp. `_sub`), including the transport
hypothesis `HasLipBoundW (u_V^t) (K t)` (resp. `HasFracTransportBound ... (u_0^t) (K t - ‖Q‖)`) with `K` integrable on
`[0,T]`, one has `SbLogK D N T ρ` (`d ≥ 2`).  `sb1_superLogK`, `sb1_subLogK` prove them.

NOTE: `SbLogK` does not hold without the transport hypothesis in this form (the normaliser identity needs the integrable
Lipschitz bound `K` to dominate the commutator); the rows of S.B.1 carry it, so the closing assembly must pass `K` to F3.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_lip_of_frac {α p : ℝ} {v : Euc d → Euc d} {K : ℝ} (h : Whole.HasFracTransportBound α p v K) :
    Whole.HasLipBoundW v K := by
  obtain ⟨L, F, hF, hLip, -, hLK⟩ := h
  exact ⟨L, hLip, by linarith⟩

/-- F3 for the standing hypotheses -/
theorem sb1_logK_of_hyp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Whole.WholeDyn d} {N : ℕ}
    {T Λ : ℝ} {r : ℕ} {ρ : ℝ → Euc d → ℝ} {X₀ : Ω → Whole.EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Whole.EucConfig d N} (h : Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X) (hd : 1 ≤ d)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) {B : ℝ} (hV : Sb1Pot D.V B) (hN : 1 ≤ N) (hT : 0 ≤ T)
    (K : ℝ → ℝ) (hKi : IntegrableOn K (Set.Icc 0 T))
    (hK : ∀ t ∈ Set.Icc 0 T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (K t)) : SbLogK D N T ρ :=
  sb1_logK_main (sb1_tr3_of_hyp h hd hs0 hsd hV) hT h.pos_temp hN K hKi hK

/-- `SbLogK` for all data of `mfe_confined_rd_gradient_super` -/
def SuperLogK (d : ℕ) (s : ℝ) : Prop :=
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
      SbLogK D N T ρ

theorem sb1_superLogK (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) : SuperLogK d s := by
  intro D hDs hV3 hB hc N hN T Λ r hT Ω _ P _ ρ X₀ W X h K hKi hK
  subst hDs
  obtain ⟨B, hB'⟩ := hB
  exact sb1_logK_of_hyp h hd hs0 hsd ⟨hV3, hB'⟩ (by omega) hT K hKi hK

/-- `SbLogK` for all data of `mfe_confined_rd_gradient_sub` -/
def SubLogK (d : ℕ) (s a : ℝ) : Prop :=
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
      SbLogK D N T ρ

theorem sb1_subLogK (hd3 : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) : SubLogK d s a := by
  intro D hDs Q b c q hq hQs hQp hV N hN T Λ r hT Ω _ P _ ρ X₀ W X h K hKi hK
  subst hDs
  have hd : 1 ≤ d := by omega
  have hα : 1 < a / 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    linarith [ha.1]
  have hTB : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (K t) := by
    intro t ht
    have h1 := sb1_transport_add_affine hd hα (hK t ht) Q b
    have e : Whole.mfeTransportW D (ρ t) =
        fun x => Whole.mfeTransport0W D (ρ t) x + (Torus.matVec Q x + b) := by
      funext x
      unfold Whole.mfeTransportW
      rw [sb1_gradient_V hQs hV x]
    rw [e]
    exact sb1_lip_of_frac (by simpa using h1)
  obtain ⟨B, hB⟩ := sb1_pot_quad Q b c hV
  exact sb1_logK_of_hyp h hd hs0 (by linarith) hB (by omega) hT K hKi hTB

end HRS.MS.MfeConf
