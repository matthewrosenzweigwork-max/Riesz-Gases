/-
# HRS.Equilibrium.Q84eAuxM — packet Q84e: measurability of the pair and triple sums
-/
import HRS.Equilibrium.Q84eAuxL

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

variable {d : ℕ} {N : ℕ}

theorem q84e_measurable_pairSum {b : Torus d → Torus d → ℝ}
    (hb : Measurable (fun p : Torus d × Torus d => b p.1 p.2)) :
    Measurable (fun X : Config d N => pairSumOrdered b X) := by
  unfold pairSumOrdered
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have := hb.comp ((measurable_pi_apply (X := fun _ : Fin N => Torus d) i).prodMk
    (measurable_pi_apply (X := fun _ : Fin N => Torus d) j))
  exact this

theorem q84e_measurable_tripleSum {g : Torus d → Torus d → Torus d → ℝ}
    (hg : Measurable (fun p : Torus d × Torus d × Torus d => g p.1 p.2.1 p.2.2)) :
    Measurable (fun X : Config d N => tripleSum g X) := by
  unfold tripleSum
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    Finset.measurable_sum _ fun k _ => ?_
  have := hg.comp ((measurable_pi_apply (X := fun _ : Fin N => Torus d) i).prodMk
    ((measurable_pi_apply (X := fun _ : Fin N => Torus d) j).prodMk
      (measurable_pi_apply (X := fun _ : Fin N => Torus d) k)))
  exact this

theorem q84e_measurable_Fstat {b : Torus d → Torus d → ℝ}
    (hb : Measurable (fun p : Torus d × Torus d => b p.1 p.2)) :
    Measurable (fun X : Config d N => Fstat b X) :=
  measurable_const.mul (q84e_measurable_pairSum hb)

theorem q84e_measurable_scaledPair {b : Torus d → Torus d → ℝ}
    (hb : Measurable (fun p : Torus d × Torus d => b p.1 p.2)) (c : ℝ) :
    Measurable (fun X : Config d N => c * pairSumOrdered b X) :=
  measurable_const.mul (q84e_measurable_pairSum hb)

theorem q84e_measurable_scaledTriple {g : Torus d → Torus d → Torus d → ℝ}
    (hg : Measurable (fun p : Torus d × Torus d × Torus d => g p.1 p.2.1 p.2.2)) (c : ℝ) :
    Measurable (fun X : Config d N => c * tripleSum g X) :=
  measurable_const.mul (q84e_measurable_tripleSum hg)

end HRS.Q84e

end
