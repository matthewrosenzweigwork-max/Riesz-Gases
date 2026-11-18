import HRS.MS.CritForcePartition
import HRS.MS.CritForceGeometric
import HRS.MS.CritForceCoordinates

/-!
# S8.2.06: assembly of the uniform-history estimate from scalar block estimates
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

/-- Pointwise: the absolute value of the full integral is at most the recent block plus the
sum of absolute values of the old blocks (in `ℝ≥0∞`). -/
lemma s82_partition_abs_le (f : ℝ → ℝ) (a₀ t : ℝ) (ha₀ : 0 ≤ a₀) (ht : 0 ≤ t)
    (hf : IntegrableOn f (Set.Icc 0 (a₀ + t))) :
    ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) (a₀ + t), f r| ≤
      ENNReal.ofReal |∫ r in Set.Icc a₀ (a₀ + t), f r| +
        ∑' j : ℕ, ENNReal.ofReal |∫ r in Set.Icc
          (max 0 (a₀ - ((j : ℝ) + 1))) (max 0 (a₀ - (j : ℝ))), f r| := by
  obtain ⟨hs, heq⟩ := s82_history_partition f a₀ t ha₀ ht hf
  rw [heq]
  have habs : Summable (fun j : ℕ => |∫ r in Set.Icc
      (max 0 (a₀ - ((j : ℝ) + 1))) (max 0 (a₀ - (j : ℝ))), f r|) := hs.abs
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => abs_nonneg _) habs,
    ← ENNReal.ofReal_add (abs_nonneg _) (tsum_nonneg fun j => abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun j : ℕ => ∫ r in Set.Icc
    (max 0 (a₀ - ((j : ℝ) + 1))) (max 0 (a₀ - (j : ℝ))), f r) (by simpa only [Real.norm_eq_abs] using habs)

theorem s82_history_bound {ι Ω : Type} [Countable ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → ℝ → ℝ → Ω → ℝ) (w : ι → ℝ) (C q ε T a₀ : ℝ)
    (hC : 0 ≤ C) (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 ≤ ε)
    (hT : 0 ≤ T) (ha₀ : 0 ≤ a₀)
    (hw : ∀ i, 0 ≤ w i) (hws : Summable (fun i => (w i) ^ 2))
    (hF : ∀ᵐ ζ ∂P, ∀ i, ∀ t : Set.Icc (0 : ℝ) T,
      IntegrableOn (fun r => F i (a₀ + t) r ζ) (Set.Icc 0 (a₀ + t)))
    (hblocks : ∀ i,
      AEMeasurable (s82RecentSup F T a₀ i) P ∧
      (∫⁻ ζ, (s82RecentSup F T a₀ i ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * w i * ε) ∧
      ∀ j : ℕ, AEMeasurable (s82PastSup F T a₀ j i) P ∧
        (∫⁻ ζ, (s82PastSup F T a₀ j i ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * w i * ε * q ^ j)) :
    (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T,
      l2NormE (fun i => ∫ r in Set.Icc (0 : ℝ) (a₀ + t),
        F i (a₀ + t) r ζ)) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (s82HistoryConstant C q w * ε) := by
  -- the envelope of each coordinate
  have hEnv : ∀ i, AEMeasurable (fun ζ => s82RecentSup F T a₀ i ζ +
        ∑' j : ℕ, s82PastSup F T a₀ j i ζ) P ∧
      (∫⁻ ζ, (s82RecentSup F T a₀ i ζ + ∑' j : ℕ, s82PastSup F T a₀ j i ζ) ^ 2 ∂P) ^
        (1 / 2 : ℝ) ≤ ENNReal.ofReal ((C * ε * (1 + (1 - q)⁻¹)) * w i) := by
    intro i
    obtain ⟨hRm, hR, hP⟩ := hblocks i
    have h := s82_geometric_L2 P (s82RecentSup F T a₀ i) (fun j => s82PastSup F T a₀ j i)
      (C * w i * ε) q (by have := hw i; positivity) hq0 hq1 hRm (fun j => (hP j).1) hR
      (fun j => (hP j).2)
    refine ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))⟩
    ring
  have hB : 0 ≤ C * ε * (1 + (1 - q)⁻¹) :=
    mul_nonneg (mul_nonneg hC hε) (by have : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith)
                                      linarith)
  have hZA : ∀ᵐ ζ ∂P, ∀ t : Set.Icc (0 : ℝ) T, ∀ i,
      ENNReal.ofReal |(fun (s : ℝ) (i : ι) (ζ : Ω) =>
        ∫ r in Set.Icc (0 : ℝ) (a₀ + s), F i (a₀ + s) r ζ) t i ζ| ≤
        s82RecentSup F T a₀ i ζ + ∑' j : ℕ, s82PastSup F T a₀ j i ζ := by
    filter_upwards [hF] with ζ hζ t i
    have h := s82_partition_abs_le (fun r => F i (a₀ + t) r ζ) a₀ t ha₀ t.property.1 (hζ i t)
    refine h.trans (add_le_add ?_ (ENNReal.tsum_le_tsum fun j => ?_))
    · exact le_iSup (fun t : Set.Icc (0 : ℝ) T =>
        ENNReal.ofReal |s82Recent F a₀ t i ζ|) t
    · exact le_iSup (fun t : Set.Icc (0 : ℝ) T =>
        ENNReal.ofReal |s82Past F a₀ j t i ζ|) t
  have h3 := s82_coordinate_L2 P T
    (fun (s : ℝ) (i : ι) (ζ : Ω) => ∫ r in Set.Icc (0 : ℝ) (a₀ + s), F i (a₀ + s) r ζ)
    (fun i ζ => s82RecentSup F T a₀ i ζ + ∑' j : ℕ, s82PastSup F T a₀ j i ζ) w
    (C * ε * (1 + (1 - q)⁻¹)) hB hw hws
    (fun i => (hEnv i).1) (fun i => (hEnv i).2) hZA
  refine h3.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold s82HistoryConstant
  ring

end HRS.MS.S82BD
