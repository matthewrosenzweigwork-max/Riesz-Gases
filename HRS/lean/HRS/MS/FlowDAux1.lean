import HRS.Whole.AppendixALemmas

/-!
# MS-FLOW-D, elementary counting lemmas (S.A.32 (iii), (iv))

Integer points in a box, multiplicity of lattice cells and `lintegral` comparison for a covering
with bounded multiplicity.  Route: `FlowDPlan.md`.
-/

open Set MeasureTheory
open scoped ENNReal
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

namespace HRS.MS.FlowD

variable {d : ℕ}

theorem toNat_cast_le (n : ℤ) (r : ℝ) (hr : (n : ℝ) ≤ r) (hr0 : 0 ≤ r) :
    ((n.toNat : ℕ) : ℝ) ≤ r := by
  rcases le_or_gt 0 n with h | h
  · have : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg h
    have h2 : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast this
    rw [h2]; exact hr
  · have : n.toNat = 0 := Int.toNat_of_nonpos h.le
    rw [this]; simpa using hr0

/-- Integer points of a box of half-width `R` are covered by a finset of at most `(2R+1)^d` points. -/
theorem box_finset (c : Fin d → ℝ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ F : Finset (Fin d → ℤ), (∀ z : Fin d → ℤ, (∀ i, |(z i : ℝ) - c i| ≤ R) → z ∈ F) ∧
      (F.card : ℝ) ≤ (2 * R + 1) ^ d := by
  refine ⟨Fintype.piFinset (fun i => Finset.Icc ⌈c i - R⌉ ⌊c i + R⌋), ?_, ?_⟩
  · intro z hz
    rw [Fintype.mem_piFinset]
    intro i
    have := abs_le.1 (hz i)
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.2 (by linarith [this.1]), Int.le_floor.2 (by linarith [this.2])⟩
  · rw [Fintype.card_piFinset]
    push_cast
    calc (∏ i : Fin d, ((Finset.Icc ⌈c i - R⌉ ⌊c i + R⌋).card : ℝ))
        ≤ ∏ _i : Fin d, (2 * R + 1) := by
          refine Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => ?_)
          rw [Int.card_Icc]
          refine toNat_cast_le _ _ ?_ (by linarith)
          have h1 := Int.floor_le (c i + R)
          have h2 := Int.le_ceil (c i - R)
          push_cast
          linarith
      _ = (2 * R + 1) ^ d := by simp

theorem latticePt_apply (z : Fin d → ℤ) (i : Fin d) : latticePt z i = (z i : ℝ) := rfl

theorem mem_cell_iff (z : Fin d → ℤ) (w : Euc d) :
    w ∈ latticeCell z ↔ ∀ i, (z i : ℝ) ≤ w i ∧ w i ≤ (z i : ℝ) + 1 := by
  simp only [latticeCell, mem_setOf_eq, latticePt_apply]

theorem isClosed_cell (z : Fin d → ℤ) : IsClosed (latticeCell z) := by
  have : latticeCell z = ⋂ i : Fin d,
      ({x : Euc d | (z i : ℝ) ≤ x i} ∩ {x : Euc d | x i ≤ (z i : ℝ) + 1}) := by
    ext x; simp [mem_cell_iff]
  rw [this]
  refine isClosed_iInter fun i => IsClosed.inter ?_ ?_
  · exact isClosed_le continuous_const (EuclideanSpace.proj i).continuous
  · exact isClosed_le (EuclideanSpace.proj i).continuous continuous_const

/-- Every point lies in some cell. -/
theorem exists_cell (w : Euc d) : ∃ z : Fin d → ℤ, w ∈ latticeCell z :=
  ⟨fun i => ⌊w i⌋, (mem_cell_iff _ _).2 fun i =>
    ⟨Int.floor_le (w i), (Int.lt_floor_add_one (w i)).le⟩⟩

/-- A point lies in at most `2^d` cells. -/
theorem cell_multiplicity (w : Euc d) :
    ∃ F : Finset (Fin d → ℤ), (F.card : ℝ) ≤ 2 ^ d ∧ ∀ z, w ∈ latticeCell z → z ∈ F := by
  obtain ⟨F, hF1, hF2⟩ := box_finset (fun i => w i - 1 / 2) (1 / 2) (by norm_num)
  have e2 : (2 * (1 / 2 : ℝ) + 1) = 2 := by norm_num
  rw [e2] at hF2
  refine ⟨F, hF2, fun z hz => hF1 z ?_⟩
  intro i
  have := (mem_cell_iff z w).1 hz i
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

/-- `lintegral` comparison for a measurable covering with multiplicity at most `N`. -/
theorem lintegral_cover (S : (Fin d → ℤ) → Set (Euc d)) (hS : ∀ z, MeasurableSet (S z)) (N : ℕ)
    (hlow : ∀ x, ∃ z, x ∈ S z)
    (hup : ∀ x, ∃ F : Finset (Fin d → ℤ), F.card ≤ N ∧ ∀ z, x ∈ S z → z ∈ F)
    (G : Euc d → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ≤ ∑' z, ∫⁻ x in S z, G x ∧
      ∑' z, ∫⁻ x in S z, G x ≤ (N : ℝ≥0∞) * ∫⁻ x, G x := by
  have h : ∑' z, ∫⁻ x in S z, G x = ∫⁻ x, ∑' z, (S z).indicator G x := by
    simp_rw [← lintegral_indicator (hS _)]
    exact (lintegral_tsum fun z => (hG.indicator (hS z)).aemeasurable).symm
  rw [h]
  constructor
  · refine lintegral_mono fun x => ?_
    obtain ⟨z, hz⟩ := hlow x
    calc G x = (S z).indicator G x := (indicator_of_mem hz G).symm
      _ ≤ _ := ENNReal.le_tsum (f := fun z => (S z).indicator G x) z
  · calc ∫⁻ x, ∑' z, (S z).indicator G x ≤ ∫⁻ x, (N : ℝ≥0∞) * G x := by
          refine lintegral_mono fun x => ?_
          obtain ⟨F, hF1, hF2⟩ := hup x
          rw [tsum_eq_sum (s := F) (fun z hz => indicator_of_notMem (fun hx => hz (hF2 z hx)) G)]
          calc ∑ z ∈ F, (S z).indicator G x ≤ ∑ _z ∈ F, G x :=
                Finset.sum_le_sum fun z _ => indicator_le_self' (fun _ _ => zero_le) x
            _ = F.card * G x := by simp
            _ ≤ N * G x := by gcongr
      _ = (N : ℝ≥0∞) * ∫⁻ x, G x := lintegral_const_mul _ hG

end HRS.MS.FlowD
