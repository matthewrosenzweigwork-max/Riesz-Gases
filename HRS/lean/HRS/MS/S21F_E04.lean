import HRS.MP.SelfSimP4LscM
import HRS.MS.S21F_E00

/-!
# S21F, packet R26-T3.E04: eventually exact cutoff weights off the collision diagonal

For a collision-free configuration `X`, the exact cutoff `sb1kM d s M` (radius `1/(M+1)`) agrees with the Riesz kernel at
every pair distance for all large `M`, so `r26t3_weightM = r26t3_weight` eventually.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem r26t3_weights_eventually (d N : ℕ) (s a β : ℝ) (hs : 0 ≤ s)
    (X : EucConfig d N) (hX : X ∉ eucCollisionSet d N) :
    ∀ᶠ M : ℕ in atTop, r26t3_weightM d N s a β M X = r26t3_weight d N s a β X := by
  filter_upwards [HRS.MP.SelfSimP4Impl.p4m_ev_far X hX] with M hM
  have hk := HRS.MS.MfeConf.sb1kM_isKernel (d := d) s hs M
  have hsum : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), r26t3_regKernel d s M (X i - X j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), rieszKernel d s (X i - X j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i < j := (Finset.mem_filter.1 hj).2
    exact hk.eq_far _ (hM i j hij.ne)
  have hH : HRS.Whole.canonicalHamiltonian (r26t3_regKernel d s M) (confinement a) X =
      HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement a) X := by
    unfold HRS.Whole.canonicalHamiltonian
    rw [hsum]
  classical
  simp only [r26t3_weightM, r26t3_weight, if_neg hX, hH]

end HRS.MS.R26T3
