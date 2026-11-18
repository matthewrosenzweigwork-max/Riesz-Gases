import HRS.MS.GenPathAux47

/-!
# S5.6 packet P8g: the law of a sum of independent finite-dimensional vectors, transferred between spaces
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

variable {d : ℕ}

theorem s56_sum_law {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    (P : Measure Ω) (P₂ : Measure Ω₂) [IsProbabilityMeasure P] [IsProbabilityMeasure P₂]
    (Vc VD : Ω → E) (Wc WF : Ω₂ → E) (hVc : AEMeasurable Vc P) (hVD : AEMeasurable VD P)
    (hWc : AEMeasurable Wc P₂) (hWF : AEMeasurable WF P₂)
    (hV : IndepFun VD Vc P) (hW : IndepFun WF Wc P₂)
    (h1 : P.map Vc = P₂.map Wc) (h2 : P.map VD = P₂.map WF) :
    P.map (fun ζ => VD ζ + Vc ζ) = P₂.map (fun ζ => WF ζ + Wc ζ) := by
  have e1 := (indepFun_iff_map_prod_eq_prod_map_map hVD hVc).1 hV
  have e2 := (indepFun_iff_map_prod_eq_prod_map_map hWF hWc).1 hW
  have hadd : Measurable fun x : E × E => x.1 + x.2 := measurable_fst.add measurable_snd
  have a1 : P.map (fun ζ => VD ζ + Vc ζ) = (P.map fun ζ => (VD ζ, Vc ζ)).map (fun x : E × E => x.1 + x.2) := by
    rw [AEMeasurable.map_map_of_aemeasurable hadd.aemeasurable (hVD.prodMk hVc)]
    rfl
  have a2 : P₂.map (fun ζ => WF ζ + Wc ζ) =
      (P₂.map fun ζ => (WF ζ, Wc ζ)).map (fun x : E × E => x.1 + x.2) := by
    rw [AEMeasurable.map_map_of_aemeasurable hadd.aemeasurable (hWF.prodMk hWc)]
    rfl
  rw [a1, a2, e1, e2, h1, h2]

end HRS.MS.GenPath
