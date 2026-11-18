import HRS.MS.MfeConfAux123
import HRS.MS.MfeConfAux144
import HRS.MS.MfeConfAux155
import HRS.MS.MfeConfAux160

/-!
# S.B.1 (SB5), R3d (part 1): the canonical Gibbs ensemble as a multiple of `sb1Dm sb1Gw`, and bounded-density events

* `sb1_canon_eq`: `canonicalGibbs (rieszKernel) V N (1/β') = c • sb1Dm (sb1Gw D rieszKernel N)` (the canonical Hamiltonian is `sb1Hs`);
* `sb1_event_bdd`: for `μ ≪ sb1Dm w` the restriction of `μ` to `{dμ/d(sb1Dm w) ≤ k}` is dominated by `k • sb1Dm w`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_pairSum_two {k : Euc d → ℝ} (hev : ∀ x, k (-x) = k x) (Z : Whole.EucConfig d N) :
    p4k_pairSum k N Z = 2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), k (Z i - Z j) := by
  unfold p4k_pairSum
  have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, k (Z i - Z j) =
      ∑ j ∈ Finset.univ.filter (fun j => i < j), k (Z i - Z j) +
        ∑ j ∈ Finset.univ.filter (fun j => j < i), k (Z i - Z j) := by
    intro i
    have : Finset.univ.erase i = Finset.univ.filter (fun j => i < j) ∪ Finset.univ.filter (fun j => j < i) := by
      ext j; simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h; rcases lt_or_gt_of_ne h with h' | h'
        · exact Or.inr ⟨trivial, h'⟩
        · exact Or.inl ⟨trivial, h'⟩
      · rintro (h | h)
        · exact h.2.ne'
        · exact h.2.ne
    rw [this, Finset.sum_union]
    rw [Finset.disjoint_filter]
    intro j _ h1 h2; exact lt_asymm h1 h2
  simp only [h1, Finset.sum_add_distrib]
  have h2 : ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => j < i), k (Z i - Z j) =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), k (Z i - Z j) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i < j
    · simp only [h, if_true]
      rw [← hev, neg_sub]
    · simp [h]
  rw [h2]; ring

theorem sb1_canonH_eq (D : Whole.WholeDyn d) (hN : 0 < N) (Z : Whole.EucConfig d N) :
    Whole.canonicalHamiltonian (Whole.rieszKernel d D.s) D.V Z = sb1Hs D (Whole.rieszKernel d D.s) N Z := by
  have hev : ∀ x : Euc d, Whole.rieszKernel d D.s (-x) = Whole.rieszKernel d D.s x := fun x => by
    simp [Whole.rieszKernel]
  unfold sb1Hs Whole.canonicalHamiltonian
  rw [sb1_pairSum_two hev]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem sb1_canon_eq (D : Whole.WholeDyn d) (hN : 0 < N) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ Whole.canonicalGibbs (Whole.rieszKernel d D.s) D.V N (1 / D.invβ) =
      c • sb1Dm (fun Z => sb1Gw D (Whole.rieszKernel d D.s) N Z) := by
  refine ⟨(ENNReal.ofReal (Whole.canonicalPartition (Whole.rieszKernel d D.s) D.V N (1 / D.invβ)))⁻¹,
    ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top, ?_⟩
  unfold Whole.canonicalGibbs sb1Dm
  congr 2
  funext Z
  unfold sb1Gw
  rw [sb1_canonH_eq D hN Z, one_div]

theorem sb1_event_bdd {α : Type*} [MeasurableSpace α] (μ R : Measure α) [IsFiniteMeasure μ] [SigmaFinite R]
    (hac : μ ≪ R) (k : ℕ) :
    MeasurableSet {Z | μ.rnDeriv R Z ≤ k} ∧ μ.restrict {Z | μ.rnDeriv R Z ≤ k} ≤ (k : ℝ≥0∞) • R := by
  have hE : MeasurableSet {Z | μ.rnDeriv R Z ≤ k} := measurableSet_le (Measure.measurable_rnDeriv _ _) measurable_const
  refine ⟨hE, Measure.le_iff.2 fun t ht => ?_⟩
  set E : Set α := {Z | μ.rnDeriv R Z ≤ k} with hEdef
  rw [Measure.restrict_apply ht, ← Measure.setLIntegral_rnDeriv hac, Measure.smul_apply, smul_eq_mul]
  have h1 : (∫⁻ x, μ.rnDeriv R x ∂(R.restrict (t ∩ E))) ≤ ∫⁻ _x, (k : ℝ≥0∞) ∂(R.restrict (t ∩ E)) :=
    setLIntegral_mono measurable_const fun x hx => hx.2
  rw [lintegral_const, Measure.restrict_apply_univ] at h1
  calc (∫⁻ x, μ.rnDeriv R x ∂(R.restrict (t ∩ E))) ≤ (k : ℝ≥0∞) * R (t ∩ E) := h1
    _ ≤ (k : ℝ≥0∞) * R t := mul_le_mul' le_rfl (measure_mono Set.inter_subset_left)
