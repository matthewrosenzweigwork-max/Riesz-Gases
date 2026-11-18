import HRS.MC.CepN1Aux4

/-!
# Packet CEPN1, part 5: measurability of `Good` and the independence product formula
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real

noncomputable section

namespace HRS.MC.CepN1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The piece condition as a condition on the restriction of the path to `[0,h]`. -/
def cepn1_pastT (h : ℝ≥0) (ε ρ : ℝ) (g : ℝ≥0 → ℝ) : Set (Set.Iic h → ℝ) :=
  {u | |u ⟨h, Set.mem_Iic.2 le_rfl⟩ - g h| < ε ∧
    ∀ (n k : ℕ) (hk : k ≤ 2 ^ n), |u ⟨cepn1_dy h n k, Set.mem_Iic.2 (cepn1_dy_le h n k hk)⟩| ≤ ρ}

theorem cepn1_pastT_meas (h : ℝ≥0) (ε ρ : ℝ) (g : ℝ≥0 → ℝ) : MeasurableSet (cepn1_pastT h ε ρ g) := by
  unfold cepn1_pastT
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_lt (continuous_abs.measurable.comp
      ((measurable_pi_apply _).sub measurable_const)) measurable_const
  · have e : {u : Set.Iic h → ℝ | ∀ (n k : ℕ) (hk : k ≤ 2 ^ n),
        |u ⟨cepn1_dy h n k, Set.mem_Iic.2 (cepn1_dy_le h n k hk)⟩| ≤ ρ} =
        ⋂ n : ℕ, ⋂ k : ℕ, ⋂ hk : k ≤ 2 ^ n,
          {u : Set.Iic h → ℝ | |u ⟨cepn1_dy h n k, Set.mem_Iic.2 (cepn1_dy_le h n k hk)⟩| ≤ ρ} := by
      ext u; simp
    show MeasurableSet {u : Set.Iic h → ℝ | ∀ (n k : ℕ) (hk : k ≤ 2 ^ n),
        |u ⟨cepn1_dy h n k, Set.mem_Iic.2 (cepn1_dy_le h n k hk)⟩| ≤ ρ}
    rw [e]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk =>
      measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply _)) measurable_const

theorem cepn1_piece_iff (h : ℝ≥0) (ε ρ : ℝ) (g z : ℝ≥0 → ℝ) :
    cepn1_Piece h ε ρ g z ↔ (fun u : Set.Iic h => z u) ∈ cepn1_pastT h ε ρ g := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun n k hk => h2 n k hk⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun n k hk => h2 n k hk⟩

theorem cepn1_good_meas (h : ℝ≥0) (ε ρ : ℝ) :
    ∀ (M : ℕ) (g : ℝ≥0 → ℝ), MeasurableSet {z : ℝ≥0 → ℝ | cepn1_Good h ε ρ M g z}
  | 0, g => by simp [cepn1_Good]
  | M + 1, g => by
    have h1 : MeasurableSet {z : ℝ≥0 → ℝ | cepn1_Piece h ε ρ g z} := by
      have hm : Measurable (fun (z : ℝ≥0 → ℝ) (u : Set.Iic h) => z u) :=
        measurable_pi_iff.2 fun u => measurable_pi_apply _
      have := hm (cepn1_pastT_meas h ε ρ g)
      convert this using 1
      ext z
      exact cepn1_piece_iff h ε ρ g z
    have h2 : Measurable (fun (z : ℝ≥0 → ℝ) (t : ℝ≥0) => z (h + t) - z h) :=
      measurable_pi_iff.2 fun t => (measurable_pi_apply _).sub (measurable_pi_apply _)
    exact h1.inter (h2 (cepn1_good_meas h ε ρ M _))

theorem cepn1_good_succ_prob [IsProbabilityMeasure P] {Z : ℝ≥0 → Ω → ℝ} (hZ : IsPreBrownianReal Z P)
    (h : ℝ≥0) (ε ρ : ℝ) (M : ℕ) (g : ℝ≥0 → ℝ) :
    P {ω | cepn1_Good h ε ρ (M + 1) g (fun t => Z t ω)} =
      P {ω | cepn1_Piece h ε ρ g (fun t => Z t ω)} *
        P {ω | cepn1_Good h ε ρ M (fun t => g (h + t) - g h) (fun t => Z (h + t) ω - Z h ω)} := by
  have hind := hZ.indepFun_shift h
  have key := hind.measure_inter_preimage_eq_mul _ _
    (cepn1_good_meas h ε ρ M (fun t => g (h + t) - g h)) (cepn1_pastT_meas h ε ρ g)
  have e1 : {ω | cepn1_Good h ε ρ (M + 1) g (fun t => Z t ω)} =
      (fun ω (t : ℝ≥0) => Z (h + t) ω - Z h ω) ⁻¹'
        {z | cepn1_Good h ε ρ M (fun t => g (h + t) - g h) z} ∩
      (fun ω (t : Set.Iic h) => Z t ω) ⁻¹' cepn1_pastT h ε ρ g := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, cepn1_Good]
    rw [cepn1_piece_iff]
    tauto
  have e2 : {ω | cepn1_Piece h ε ρ g (fun t => Z t ω)} =
      (fun ω (t : Set.Iic h) => Z t ω) ⁻¹' cepn1_pastT h ε ρ g := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    exact cepn1_piece_iff h ε ρ g _
  rw [e1, e2, key, mul_comm]
  rfl

end HRS.MC.CepN1
