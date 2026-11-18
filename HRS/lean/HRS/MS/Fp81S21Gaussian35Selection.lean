import HRS.MS.Fp81S21VersionGTime2
import HRS.MS.Fp81S21WickApprox33
import HRS.MS.Fp81S21GaussianSourceGlue
import HRS.MS.ProClosureS111WeightedChart

/-! Packet 35, unit 1: compatible witnesses and their origin-zero histories.
The implicit radius binder is made explicit in the record and constructor.
Producer abbreviations are expanded to their public `fp81s21_` names.
Charts are retained as fields so already-selected packet-32 families can be reused;
the existence proof fixes both physical charts before obtaining any radius. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- One source and one pair of physical families, with compatible histories. -/
structure fp81s21_Gaussian35Selection (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) where
  Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)
  E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)
  src : fp81s21_gaussian_source_retained_data p R
    (fp81s21_initialMeasure_isProbability p R)
  εG : ℕ → ℝ
  εB : ℕ → ℝ
  εG_nonneg : ∀ m, 0 ≤ εG m
  εG_tendsto : Tendsto εG atTop (𝓝 0)
  εB_nonneg : ∀ m, 0 ≤ εB m
  εB_tendsto : Tendsto εB atTop (𝓝 0)
  MUG : ℝ
  MUG_nonneg : 0 ≤ MUG
  canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG εG
  S : fp81s21_QuadraticPhysical31 p R Es E εB
  UG : ∀ a : ℝ, 0 ≤ a → src.G0.Ω →
    Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T)))
  UB : ∀ a : ℝ, 0 ≤ a → src.G0.Ω →
    Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T)))
  hUG : ∀ a ha, fp81s21_TimeL2Rep src.G0.P
    (fp81s21_gaussian_embedFamily p Es E (canon.q src.G0))
    MUG 0 (a + p.T) (UG a ha)
  hUB : ∀ a ha, fp81s21_TimeL2Rep src.G0.P (S.qe src.G0)
    (S.Kstar ^ 4 * S.B / 2) 0 (a + p.T) (UB a ha)

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

/-- These are definitions on the retained witnesses, never additional choices. -/
abbrev fp81s21_gaussian35_G0 (Q : fp81s21_Gaussian35Selection p R) := Q.src.G0
abbrev fp81s21_gaussian35_P (Q : fp81s21_Gaussian35Selection p R) := Q.src.G0.P
abbrev fp81s21_gaussian35_ξ' (Q : fp81s21_Gaussian35Selection p R) :=
  fp81s21_gaussian_source_measurableXi Q.src
abbrev fp81s21_gaussian35_T (Q : fp81s21_Gaussian35Selection p R) := Q.S.T Q.src.G0
abbrev fp81s21_gaussian35_W₂ (Q : fp81s21_Gaussian35Selection p R) := Q.S.W Q.src.G0
abbrev fp81s21_gaussian35_qG (Q : fp81s21_Gaussian35Selection p R) :=
  fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q Q.src.G0)
abbrev fp81s21_gaussian35_qB (Q : fp81s21_Gaussian35Selection p R) := Q.S.qe Q.src.G0

/-- Reuse already-selected families; select only their supplied histories. -/
def fp81s21_gaussian35_selection_of_selected
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (src : fp81s21_gaussian_source_retained_data p R
      (fp81s21_initialMeasure_isProbability p R))
    (εG εB : ℕ → ℝ) (hεG : ∀ m, 0 ≤ εG m)
    (hεGlim : Tendsto εG atTop (𝓝 0)) (hεB : ∀ m, 0 ≤ εB m)
    (hεBlim : Tendsto εB atTop (𝓝 0)) (MUG : ℝ) (hMUG : 0 ≤ MUG)
    (canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG εG)
    (S : fp81s21_QuadraticPhysical31 p R Es E εB) :
    fp81s21_Gaussian35Selection p R := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  have hG := fun (a : ℝ) (ha : 0 ≤ a) =>
    (canon.payload src.G0).time_representation 0 le_rfl (a + p.T)
      (add_pos_of_nonneg_of_pos ha p.hT)
  have hB := fun (a : ℝ) (ha : 0 ≤ a) =>
    (S.payload src.G0).2.2.2.2.2.2.2 0 le_rfl (a + p.T)
      (add_pos_of_nonneg_of_pos ha p.hT)
  choose UG hUG using hG
  choose UB hUB using hB
  refine {
    Es := Es, E := E, src := src, εG := εG, εB := εB
    εG_nonneg := hεG, εG_tendsto := hεGlim
    εB_nonneg := hεB, εB_tendsto := hεBlim
    MUG := MUG, MUG_nonneg := hMUG, canon := canon, S := S
    UG := UG, UB := UB, hUB := fun a ha => (hUB a ha).1
    hUG := ?_ }
  intro a ha
  have ht := (hUG a ha).1
  refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
  filter_upwards [ht.2.2.2] with ω hω
  refine ⟨hω.1, ?_⟩
  filter_upwards [hω.2] with t ht
  exact ht.1

/-- The physical charts precede all radii; every later selector uses the same
retained source, canonical family, and quadratic family. -/
theorem fp81s21_gaussian35_selection (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        Nonempty (fp81s21_Gaussian35Selection p R) := by
  let Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4) :=
    Classical.choice (physical_weighted_chart (by have := p.hd; omega) (by nlinarith [Nat.cast_nonneg (α := ℝ) p.d]))
  let E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2) :=
    Classical.choice (physical_weighted_chart (by have := p.hd; omega) (by nlinarith [Nat.cast_nonneg (α := ℝ) p.d]))
  obtain ⟨δs, hδs, hδshalf, hsrc⟩ := fp81s21_gaussian_source_retained p
  obtain ⟨εG, hεG, hεGlim, δg, hδg, _, hcanon⟩ :=
    fp81s21_gaussian_V2_G_physical p Es E
  obtain ⟨εB, hεB, hεBlim, δb, hδb, _, hquad⟩ :=
    fp81s21_quadraticPhysical31_exists p Es E
  refine ⟨min δs (min δg δb), lt_min hδs (lt_min hδg hδb),
    (min_le_left _ _).trans hδshalf, ?_⟩
  intro δ hδ hδle R
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  have hs : δ ≤ δs := hδle.trans (min_le_left _ _)
  have hg : δ ≤ δg := (hδle.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hb : δ ≤ δb := (hδle.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨src⟩ := hsrc δ hδ hs R
  obtain ⟨_, _, _, _, MUG, hMUG, canon, _⟩ := hcanon δ hδ hg R
  obtain ⟨S⟩ := hquad δ hδ hb R
  exact ⟨fp81s21_gaussian35_selection_of_selected Es E src εG εB
    hεG hεGlim hεB hεBlim MUG hMUG canon S⟩

#print axioms fp81s21_gaussian35_selection_of_selected
#print axioms fp81s21_gaussian35_selection
end HRS.Fp81.S21
end
