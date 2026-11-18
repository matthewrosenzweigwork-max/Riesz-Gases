import HRS.MS.SA16Y4Ip1
import HRS.MS.SA16Y4Fam1

/-!
# S.A.16 (SA16Y4) Ip2: the transport operator of a convex combination of coefficients

`sa16y4_wrep_sum`: `wrep (∑ w_i • G_i) =ᵐ ∑ w_i wrep G_i`.
`sa16y4_B_convex`: `sa16so_B (∑ w_i c_i) = ∑ w_i • sa16so_B c_i` for `SA16BddCoef` families (linearity in the coefficient).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Ip2
variable {d : ℕ} {ι : Type*} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_wrep_sum {k : ℕ} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ) (G : ι → WmpSpace d k p) :
    wrep d k p (∑ i ∈ s, w i • G i) =ᵐ[volume] fun x => ∑ i ∈ s, w i * wrep d k p (G i) x := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact sa16r_wrep_zero (d := d) (k := k) (p := p)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [sa16r_wrep_add d k p (w a • G a) (∑ i ∈ s, w i • G i), sa16r_wrep_smul d k p (w a) (G a), ih]
      with x h1 h2 h3
    rw [h1, h2, h3, Finset.sum_insert ha]

lemma sa16y4_B_convex {k : ℕ} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ) (hw0 : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) {B : ℝ} {c : ι → Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : ∀ i ∈ s, SA16BddCoef k B (c i)) :
    sa16so_B d k p (fun j x => ∑ i ∈ s, w i * c i j x) = ∑ i ∈ s, w i • sa16so_B d k p (c i) := by
  have hsum := sa16y4_bddCoef_convex s w hw0 hw1 hc
  refine sa16so_clm_ext fun φ => sa16r_wrep_inj d k p _ _ ?_
  have h1 := sa16so_B_Jcc (p := p) hsum φ
  have h2 : wrep d k p ((∑ i ∈ s, w i • sa16so_B d k p (c i)) (sa16r_Jcc d (k + 1) p φ)) =ᵐ[volume]
      fun x => ∑ i ∈ s, w i * wrep d k p (sa16so_B d k p (c i) (sa16r_Jcc d (k + 1) p φ)) x := by
    have : (∑ i ∈ s, w i • sa16so_B d k p (c i)) (sa16r_Jcc d (k + 1) p φ) =
        ∑ i ∈ s, w i • sa16so_B d k p (c i) (sa16r_Jcc d (k + 1) p φ) := by
      simp [ContinuousLinearMap.sum_apply]
    rw [this]
    exact sa16y4_wrep_sum s w _
  have h3 : ∀ i ∈ s, wrep d k p (sa16so_B d k p (c i) (sa16r_Jcc d (k + 1) p φ)) =ᵐ[volume]
      sa16so_transportFun (c i) φ.1 := fun i hi => sa16so_B_Jcc (p := p) (hc i hi) φ
  have h4 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ∀ i ∈ s,
      wrep d k p (sa16so_B d k p (c i) (sa16r_Jcc d (k + 1) p φ)) x = sa16so_transportFun (c i) φ.1 x :=
    (Filter.eventually_all_finset s).2 h3
  filter_upwards [h1, h2, h4] with x e1 e2 e4
  rw [e1, e2]
  have : ∀ i ∈ s, wrep d k p (sa16so_B d k p (c i) (sa16r_Jcc d (k + 1) p φ)) x =
      sa16so_transportFun (c i) φ.1 x := e4
  rw [Finset.sum_congr rfl fun i hi => by rw [this i hi]]
  unfold sa16so_transportFun
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Ip2

end HRS.Whole.AppendixA.Phase2SA16R
