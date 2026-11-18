import HRS.MS.S82P2Defs

/-!
# S8.2 observed-time layer, packet T8A.A05: exact `N - 2` triple projection counting

`tripleSum (tripleT rho Q) X = tripleSum (tripleG C rho Q) X + (N-2) * pairSum (pairJ ..) X`.  The identity is pure
combinatorics of ordered distinct triples (the symmetry hypotheses of the packet are not needed).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

/-- the sum over ordered distinct triples of labels -/
def r26t8a_a05_S {N : ℕ} (g : Fin N → Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, g i j k

theorem r26t8a_a05_swap_inner {N : ℕ} (g : Fin N → Fin N → Fin N → ℝ) :
    r26t8a_a05_S (fun i j k => g i k j) = r26t8a_a05_S g := by
  unfold r26t8a_a05_S
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_comm' (s := Finset.univ.erase i) (t := fun j => (Finset.univ.erase i).erase j)
    (t' := Finset.univ.erase i) (s' := fun k => (Finset.univ.erase i).erase k)
    (f := fun j k => g i j k) ?_).symm
  intro x y
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

theorem r26t8a_a05_swap_outer {N : ℕ} (g : Fin N → Fin N → Fin N → ℝ) :
    r26t8a_a05_S (fun i j k => g j i k) = r26t8a_a05_S g := by
  unfold r26t8a_a05_S
  have h := Finset.sum_comm' (s := (Finset.univ : Finset (Fin N))) (t := fun i => Finset.univ.erase i)
    (t' := (Finset.univ : Finset (Fin N))) (s' := fun j => Finset.univ.erase j)
    (f := fun i j => ∑ k ∈ (Finset.univ.erase i).erase j, g j i k) (by
      intro x y
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      tauto)
  rw [h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.erase_right_comm]

theorem r26t8a_a05_cyc {N : ℕ} (g : Fin N → Fin N → Fin N → ℝ) :
    r26t8a_a05_S (fun i j k => g j k i) = r26t8a_a05_S g := by
  have c1 : ∀ h : Fin N → Fin N → Fin N → ℝ,
      r26t8a_a05_S (fun i j k => h k i j) = r26t8a_a05_S h := fun h =>
    (r26t8a_a05_swap_inner (fun i j k => h j i k)).trans (r26t8a_a05_swap_outer h)
  exact (c1 (fun a b c => g b c a)).symm

theorem r26t8a_a05_count {N : ℕ} (hN : 2 ≤ N) (h : Fin N → Fin N → ℝ) :
    r26t8a_a05_S (fun i j _ => h i j) = ((N : ℝ) - 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h i j := by
  unfold r26t8a_a05_S
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_const, Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((N - 1 - 1 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [show N - 1 - 1 = N - 2 by omega, Nat.cast_sub hN]; norm_num
  rw [this]

theorem r26t8a_triple_count {d N : ℕ} (hN : 2 ≤ N) (C : WholeCoeff d)
    (rho : Euc d → ℝ) (Q : Euc d → Euc d → ℝ) (X : EucConfig d N)
    (hQ : ∀ x y, Q x y=Q y x)
    (hJ : ∀ x y, HRS.MS.Phase2S82.pairJ C (HRS.Whole.withDensityReal rho) Q x y=HRS.MS.Phase2S82.pairJ C (HRS.Whole.withDensityReal rho) Q y x) :
    HRS.MS.Phase2S82.tripleSum (HRS.MS.Phase2S82.tripleT rho Q) X = HRS.MS.Phase2S82.tripleSum (HRS.MS.Phase2S82.tripleG C rho Q) X +
      (N-2:ℝ)*HRS.MS.Phase2S82.pairSum (HRS.MS.Phase2S82.pairJ C (HRS.Whole.withDensityReal rho) Q) X := by
  set g : Fin N → Fin N → Fin N → ℝ := fun i j k => HRS.MS.Phase2S82.tripleT rho Q (X i) (X j) (X k) with hg
  set h : Fin N → Fin N → ℝ := fun i j => HRS.MS.Phase2S82.pairJ C (HRS.Whole.withDensityReal rho) Q (X i) (X j) with hh
  have e1 : HRS.MS.Phase2S82.tripleSum (HRS.MS.Phase2S82.tripleT rho Q) X = r26t8a_a05_S g := rfl
  have e2 : HRS.MS.Phase2S82.tripleSum (HRS.MS.Phase2S82.tripleG C rho Q) X = r26t8a_a05_S
      (fun i j k => (g i j k + g i k j + g j k i - h i j - h i k - h j k) / 3) := rfl
  have e3 : HRS.MS.Phase2S82.pairSum (HRS.MS.Phase2S82.pairJ C (HRS.Whole.withDensityReal rho) Q) X = ∑ i, ∑ j ∈ Finset.univ.erase i, h i j := rfl
  have hlin : ∀ a b c d e f : Fin N → Fin N → Fin N → ℝ,
      r26t8a_a05_S (fun i j k => (a i j k + b i j k + c i j k - d i j k - e i j k - f i j k) / 3) =
        (r26t8a_a05_S a + r26t8a_a05_S b + r26t8a_a05_S c - r26t8a_a05_S d - r26t8a_a05_S e -
          r26t8a_a05_S f) / 3 := by
    intro a b c d e f
    simp only [r26t8a_a05_S, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have s1 : r26t8a_a05_S (fun i j k => g i k j) = r26t8a_a05_S g := r26t8a_a05_swap_inner g
  have s2 : r26t8a_a05_S (fun i j k => g j k i) = r26t8a_a05_S g := r26t8a_a05_cyc g
  have G0 : Fin N → Fin N → Fin N → ℝ := fun i j _ => h i j
  have s3 := r26t8a_a05_count hN h
  have s4 : r26t8a_a05_S (fun i j k => h i k) = ((N : ℝ) - 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h i j := by
    rw [← s3]; exact r26t8a_a05_swap_inner (fun i j _ => h i j)
  have s5 : r26t8a_a05_S (fun i j k => h j k) = ((N : ℝ) - 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h i j := by
    rw [← s3]; exact r26t8a_a05_cyc (fun i j _ => h i j)
  rw [e1, e2, e3]
  have := hlin g (fun i j k => g i k j) (fun i j k => g j k i) (fun i j _ => h i j) (fun i j k => h i k)
    (fun i j k => h j k)
  rw [show (fun i j k => (g i j k + g i k j + g j k i - h i j - h i k - h j k) / 3) =
    (fun i j k => (g i j k + (fun i j k => g i k j) i j k + (fun i j k => g j k i) i j k -
      (fun i j _ => h i j) i j k - (fun i j k => h i k) i j k - (fun i j k => h j k) i j k) / 3) from rfl,
    this, s1, s2, s3, s4, s5]
  ring

end HRS.MS.R26T8A

end
