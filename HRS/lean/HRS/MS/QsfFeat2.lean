import HRS.MS.QsfFeat1

/-!
# S4.5 packet B5 (part): conjunct 3 of `StaticFieldConclusion` from the derivative bound (conjunct 4)

`s45_smoothDist_le`: if for every `C²` functional `F` of `ℓ²` with `‖DF‖_∞ ≤ D₁`, `‖D²F‖_∞ ≤ D₂` one has
`|E F(Y) - E F(G)| ≤ K (A D₁ + B D₂)` (with `A, B, K ≥ 0`), then `d_{C_b²}(law Y, law G) ≤ K (A + B)`:
the unit ball of `C_b²` has `D₁, D₂ ≤ 1`.  (`smoothDist` is a real `iSup`: only the upper bound is used, so no junk value
can occur since the bound is nonnegative.)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace S45

open HRS.Whole

theorem s45_unit_ball_bounds {Φ : SeqL2 → ℝ} (hΦ : Φ ∈ HRS.CbUnitBall SeqL2 2) :
    (∀ z, ‖fderiv ℝ Φ z‖ ≤ 1) ∧ (∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ 1) := by
  obtain ⟨-, hbdd, hcb⟩ := hΦ
  have hnn : ∀ j, 0 ≤ ⨆ z : SeqL2, ‖iteratedFDeriv ℝ j Φ z‖ := fun j =>
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hle : ∀ j ∈ Finset.range 3, ∀ z : SeqL2, ‖iteratedFDeriv ℝ j Φ z‖ ≤ 1 := by
    intro j hj z
    have h1 : ‖iteratedFDeriv ℝ j Φ z‖ ≤ ⨆ z : SeqL2, ‖iteratedFDeriv ℝ j Φ z‖ :=
      le_ciSup (hbdd j (by simpa [Nat.lt_succ_iff] using hj)) z
    have h2 : ⨆ z : SeqL2, ‖iteratedFDeriv ℝ j Φ z‖ ≤ HRS.cbNorm 2 Φ := by
      unfold HRS.cbNorm
      exact Finset.single_le_sum (f := fun j => ⨆ z : SeqL2, ‖iteratedFDeriv ℝ j Φ z‖)
        (fun j _ => hnn j) hj
    linarith
  refine ⟨fun z => ?_, fun z => hle 2 (by simp) z⟩
  rw [← norm_iteratedFDeriv_one]
  exact hle 1 (by simp) z

theorem s45_smoothDist_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → SeqL2} (hY : Measurable Y) {γ : Measure SeqL2} {K A B : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (h : ∀ F : SeqL2 → ℝ, ContDiff ℝ 2 F → ∀ D₁ D₂ : ℝ, (∀ z, ‖fderiv ℝ F z‖ ≤ D₁) →
      (∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ D₂) →
      |∫ x, F (Y x) ∂P - ∫ z, F z ∂γ| ≤ K * (A * D₁ + B * D₂)) :
    HRS.smoothDist 2 (HRS.law P Y) γ ≤ K * (A + B) := by
  unfold HRS.smoothDist
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  obtain ⟨h1, h2⟩ := s45_unit_ball_bounds Φ.2
  have hcont : Continuous Φ.1 := Φ.2.1.continuous
  have e : ∫ z, Φ.1 z ∂(HRS.law P Y) = ∫ x, Φ.1 (Y x) ∂P := by
    unfold HRS.law
    exact integral_map hY.aemeasurable hcont.aestronglyMeasurable
  rw [e]
  refine (h Φ.1 Φ.2.1 1 1 h1 h2).trans ?_
  nlinarith [mul_nonneg hK hA, mul_nonneg hK hB]

end S45

end
