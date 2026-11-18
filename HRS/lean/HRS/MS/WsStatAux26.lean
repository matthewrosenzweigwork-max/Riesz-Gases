import HRS.MS.WsStatAux25

/-!
# S21 packet I-4: the stationary master comparison (see `WsStatAux25`)
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.GF HRS.Uniform HRS.Whole.AppendixA
open HRS (Euc)

variable {d : ℕ}

theorem s21_law_add_of_indep {Ω B : Type*} [MeasurableSpace Ω] [NormedAddCommGroup B] [MeasurableSpace B]
    [BorelSpace B] [SecondCountableTopology B] (P : Measure Ω) [IsProbabilityMeasure P]
    (U V : Ω → B) (hU : AEMeasurable U P) (hV : AEMeasurable V P) (hind : IndepFun U V P) :
    law P (fun ζ => U ζ + V ζ) = ((law P U).prod (law P V)).map (fun z : B × B => z.1 + z.2) := by
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hU hV).1 hind
  have hm : AEMeasurable (fun ω => (U ω, V ω)) P := hU.prodMk hV
  unfold law
  rw [← h1, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hm]
  rfl

end HRS.MS.S21
