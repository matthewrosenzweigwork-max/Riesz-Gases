import HRS.MS.SA16Y5Op1
import HRS.MS.SA16Y4Nc8

/-!
# S.A.16 (SA16Y5) Sm1: linearity in the coefficient of the order-one nonlocal operator (finite weighted sums)

`SA16IsoOp d m p s M a T`: `T : W^{m+1,p} →L W^{m,p}` has zeroth component `eucNonlocal s M a φ` on `Jcc φ`.
`sa16y5_isoop_sum`: the weighted sum of the operators of `a_i` is the operator of `∑ w_i a_i` (order-one copy of `sa16y4_subop_sum`,
`0 ≤ s < d-1`).  Hence the time-interpolated nonlocal operators of the approximation are again nonlocal operators.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Sm1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- `T` is an order-one operator with zeroth component `eucNonlocal s M μ φ` on the jets of `φ ∈ C_c^∞` -/
def SA16IsoOp (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ : Euc d → ℝ)
    (T : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d m p) : Prop :=
  ∀ φ : ccSub d, wrep d m p (T (sa16r_Jcc d (m + 1) p φ)) =ᵐ[volume] HRS.MH.AdjointRd.eucNonlocal s M μ φ.1

lemma sa16y5_F_add_a (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ)
    {a b : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) (hb1 : ContDiff ℝ 1 b) {B0 B1 B0' B1' : ℝ}
    (hB0 : ∀ x, |a x| ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (hB0' : ∀ x, |b x| ≤ B0')
    (hB1' : ∀ x, ‖fderiv ℝ b x‖ ≤ B1') (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => a y + b y) ⇑u x =
      HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x + HRS.MH.AdjointRd.eucNonlocal s M b ⇑u x := by
  have had : Differentiable ℝ a := ha1.differentiable (by simp)
  have hbd : Differentiable ℝ b := hb1.differentiable (by simp)
  rw [sa16y4io_F_pointwise hd hs hs1 M (ha1.add hb1) (B0 := B0 + B0') (B1 := B1 + B1')
      (fun y => (abs_add_le _ _).trans (add_le_add (hB0 y) (hB0' y)))
      (fun y => by
        rw [fderiv_fun_add (had y) (hbd y)]
        exact (norm_add_le _ _).trans (add_le_add (hB1 y) (hB1' y))) u x,
    sa16y4io_F_pointwise hd hs hs1 M ha1 hB0 hB1 u x, sa16y4io_F_pointwise hd hs hs1 M hb1 hB0' hB1' u x,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add, ← integral_add (sa16y4io_Fint_integrable hd hs hs1 ha1 hB0 hB1 u i j x)
    (sa16y4io_Fint_integrable hd hs hs1 hb1 hB0' hB1' u i j x)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

lemma sa16y5_F_smul_a (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ)
    {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) {B0 B1 : ℝ} (hB0 : ∀ x, |a x| ≤ B0)
    (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (c : ℝ) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => c * a y) ⇑u x = c * HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x := by
  have had : Differentiable ℝ a := ha1.differentiable (by simp)
  rw [sa16y4io_F_pointwise hd hs hs1 M (contDiff_const.mul ha1) (B0 := |c| * B0) (B1 := |c| * B1)
      (fun y => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB0 y) (abs_nonneg _))
      (fun y => by
        rw [fderiv_const_mul (had y)]
        calc ‖c • fderiv ℝ a y‖ = |c| * ‖fderiv ℝ a y‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |c| * B1 := mul_le_mul_of_nonneg_left (hB1 y) (abs_nonneg _)) u x,
    sa16y4io_F_pointwise hd hs hs1 M ha1 hB0 hB1 u x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ∫ y, sa16q_K1E s 0 i y * ((c * a (x - y)) * fderiv ℝ u (x - y) (EuclideanSpace.single j (1 : ℝ))) =
      c * ∫ y, sa16q_K1E s 0 i y * (a (x - y) * fderiv ℝ u (x - y) (EuclideanSpace.single j (1 : ℝ))) by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)]
  ring

lemma sa16y5_isoop_add (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {a b : EuclideanSpace ℝ (Fin d) → ℝ} (ha : sa16y4_Good a) (hb : sa16y4_Good b)
    {T T' : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d m p} (hT : SA16IsoOp d m p s M a T) (hT' : SA16IsoOp d m p s M b T') :
    SA16IsoOp d m p s M (fun y => a y + b y) (T + T') := by
  obtain ⟨ha1, B0, B1, h0, h1⟩ := ha
  obtain ⟨hb1, B0', B1', h0', h1'⟩ := hb
  intro φ
  filter_upwards [hT φ, hT' φ, sa16r_wrep_add d m p (T (sa16r_Jcc d (m + 1) p φ)) (T' (sa16r_Jcc d (m + 1) p φ))] with x e1 e2 e3
  rw [ContinuousLinearMap.add_apply, e3, e1, e2]
  exact (sa16y5_F_add_a hd hs hs1 M ha1 hb1 h0 h1 h0' h1' (sa16so_schw φ) x).symm

lemma sa16y5_isoop_smul (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    (c : ℝ) {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : sa16y4_Good a)
    {T : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d m p} (hT : SA16IsoOp d m p s M a T) :
    SA16IsoOp d m p s M (fun y => c * a y) (c • T) := by
  obtain ⟨ha1, B0, B1, h0, h1⟩ := ha
  intro φ
  filter_upwards [hT φ, sa16r_wrep_smul d m p c (T (sa16r_Jcc d (m + 1) p φ))] with x e1 e2
  rw [ContinuousLinearMap.smul_apply, e2, e1]
  exact (sa16y5_F_smul_a hd hs hs1 M ha1 h0 h1 c (sa16so_schw φ) x).symm

theorem sa16y5_isoop_sum (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (a : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (T : ι → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d m p) (S : Finset ι)
    (hG : ∀ i ∈ S, sa16y4_Good (a i)) (hT : ∀ i ∈ S, SA16IsoOp d m p s M (a i) (T i)) :
    sa16y4_Good (fun y => ∑ i ∈ S, w i * a i y) ∧
      SA16IsoOp d m p s M (fun y => ∑ i ∈ S, w i * a i y) (∑ i ∈ S, w i • T i) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⟨contDiff_const, 0, 0, fun y => by simp, fun y => by simp⟩, fun φ => ?_⟩
    simp only [Finset.sum_empty, ContinuousLinearMap.zero_apply]
    filter_upwards [sa16r_wrep_zero (d := d) (k := m) (p := p)] with x hx
    rw [hx]
    have h0 := sa16y4io_F_pointwise hd hs hs1 M (a := fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) contDiff_const
      (B0 := 0) (B1 := 0) (fun y => by simp) (fun y => by simp) (sa16so_schw φ) x
    rw [sa16so_schw_coe] at h0
    rw [h0]
    simp
  | insert i S hi ih =>
    obtain ⟨ihG, ihT⟩ := ih (fun j hj => hG j (Finset.mem_insert_of_mem hj)) (fun j hj => hT j (Finset.mem_insert_of_mem hj))
    have hGi := sa16y4_good_smul (w i) (hG i (Finset.mem_insert_self _ _))
    have hTi := sa16y5_isoop_smul hd hs hs1 M (w i) (hG i (Finset.mem_insert_self _ _)) (hT i (Finset.mem_insert_self _ _))
    have e1 : (fun y => ∑ j ∈ insert i S, w j * a j y) = fun y => w i * a i y + ∑ j ∈ S, w j * a j y := by
      funext y; rw [Finset.sum_insert hi]
    rw [e1, Finset.sum_insert hi]
    exact ⟨sa16y4_good_add hGi ihG, sa16y5_isoop_add hd hs hs1 M hGi ihG hTi ihT⟩


end Sm1

end HRS.Whole.AppendixA.Phase2SA16R
