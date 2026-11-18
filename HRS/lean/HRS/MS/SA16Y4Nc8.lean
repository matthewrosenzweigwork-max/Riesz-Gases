import HRS.MS.SA16Y4Nc7
import HRS.MS.SA16SNl4

/-!
# S.A.16 (SA16Y4) Nc8: the nonlocal operator of a finite weighted sum of coefficients (`SA16SubOp` is linear)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Nc8
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- `C^1` with bounded value and derivative -/
def sa16y4_Good (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ ∃ B0 B1 : ℝ, (∀ x, |f x| ≤ B0) ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ B1

lemma sa16y4_good_add {a b : EuclideanSpace ℝ (Fin d) → ℝ} (ha : sa16y4_Good a) (hb : sa16y4_Good b) :
    sa16y4_Good (fun y => a y + b y) := by
  obtain ⟨ha1, B0, B1, h0, h1⟩ := ha
  obtain ⟨hb1, B0', B1', h0', h1'⟩ := hb
  refine ⟨ha1.add hb1, B0 + B0', B1 + B1', fun y => (abs_add_le _ _).trans (add_le_add (h0 y) (h0' y)), fun y => ?_⟩
  rw [fderiv_fun_add (ha1.differentiable (by simp) y) (hb1.differentiable (by simp) y)]
  exact (norm_add_le _ _).trans (add_le_add (h1 y) (h1' y))

lemma sa16y4_good_smul (c : ℝ) {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : sa16y4_Good a) :
    sa16y4_Good (fun y => c * a y) := by
  obtain ⟨ha1, B0, B1, h0, h1⟩ := ha
  refine ⟨contDiff_const.mul ha1, |c| * B0, |c| * B1, fun y => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h0 y) (abs_nonneg _), fun y => ?_⟩
  rw [fderiv_const_mul (ha1.differentiable (by simp) y)]
  calc ‖c • fderiv ℝ a y‖ = |c| * ‖fderiv ℝ a y‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |c| * B1 := mul_le_mul_of_nonneg_left (h1 y) (abs_nonneg _)

lemma sa16y4_subop_add (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {a b : EuclideanSpace ℝ (Fin d) → ℝ} (ha : sa16y4_Good a) (hb : sa16y4_Good b)
    {T T' : WmpSpace d m p →L[ℝ] WmpSpace d m p} (hT : SA16SubOp d m p s M a T) (hT' : SA16SubOp d m p s M b T') :
    SA16SubOp d m p s M (fun y => a y + b y) (T + T') := by
  obtain ⟨ha1, B0, B1, h0, h1⟩ := ha
  obtain ⟨hb1, B0', B1', h0', h1'⟩ := hb
  intro φ
  filter_upwards [hT φ, hT' φ, sa16r_wrep_add d m p (T (sa16r_Jcc d m p φ)) (T' (sa16r_Jcc d m p φ))] with x e1 e2 e3
  rw [ContinuousLinearMap.add_apply, e3, e1, e2]
  exact (sa16y4_F_add hd hs hs2 M ha1 hb1 h0 h1 h0' h1' (sa16so_schw φ) x).symm

lemma sa16y4_subop_smul (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    (c : ℝ) {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : sa16y4_Good a)
    {T : WmpSpace d m p →L[ℝ] WmpSpace d m p} (hT : SA16SubOp d m p s M a T) :
    SA16SubOp d m p s M (fun y => c * a y) (c • T) := by
  obtain ⟨ha1, B0, B1, h0, h1⟩ := ha
  intro φ
  filter_upwards [hT φ, sa16r_wrep_smul d m p c (T (sa16r_Jcc d m p φ))] with x e1 e2
  rw [ContinuousLinearMap.smul_apply, e2, e1]
  exact (sa16y4_F_smul hd hs hs2 M ha1 h0 h1 c (sa16so_schw φ) x).symm

theorem sa16y4_subop_sum (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (a : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (T : ι → WmpSpace d m p →L[ℝ] WmpSpace d m p) (S : Finset ι)
    (hG : ∀ i ∈ S, sa16y4_Good (a i)) (hT : ∀ i ∈ S, SA16SubOp d m p s M (a i) (T i)) :
    sa16y4_Good (fun y => ∑ i ∈ S, w i * a i y) ∧
      SA16SubOp d m p s M (fun y => ∑ i ∈ S, w i * a i y) (∑ i ∈ S, w i • T i) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⟨contDiff_const, 0, 0, fun y => by simp, fun y => by simp⟩, fun φ => ?_⟩
    simp only [Finset.sum_empty, ContinuousLinearMap.zero_apply]
    filter_upwards [sa16r_wrep_zero (d := d) (k := m) (p := p)] with x hx
    rw [hx]
    have h0 := sa16q_F_pointwise hd hs hs2 M (a := fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) contDiff_const
      (B0 := 0) (B1 := 0) (fun y => by simp) (fun y => by simp) (sa16so_schw φ) x
    rw [sa16so_schw_coe] at h0
    rw [h0]
    simp
  | insert i S hi ih =>
    obtain ⟨ihG, ihT⟩ := ih (fun j hj => hG j (Finset.mem_insert_of_mem hj)) (fun j hj => hT j (Finset.mem_insert_of_mem hj))
    have hGi := sa16y4_good_smul (w i) (hG i (Finset.mem_insert_self _ _))
    have hTi := sa16y4_subop_smul hd hs hs2 M (w i) (hG i (Finset.mem_insert_self _ _)) (hT i (Finset.mem_insert_self _ _))
    have e1 : (fun y => ∑ j ∈ insert i S, w j * a j y) = fun y => w i * a i y + ∑ j ∈ S, w j * a j y := by
      funext y; rw [Finset.sum_insert hi]
    rw [e1, Finset.sum_insert hi]
    exact ⟨sa16y4_good_add hGi ihG, sa16y4_subop_add hd hs hs2 M hGi ihG hTi ihT⟩

end Nc8

end HRS.Whole.AppendixA.Phase2SA16R
