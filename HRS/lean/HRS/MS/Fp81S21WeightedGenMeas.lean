import HRS.MS.Fp81S21WeightedGenAdj2
import HRS.MS.ProClosureS111ChartMeas

/-! Measurable chart encoding from finite weighted Sobolev data. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_weighted_chart_encode_sub
    {d r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart d r Pw)
    {f g : Euc d → ℝ}
    (hf : IsR2WeightedTest r Pw f) (hg : IsR2WeightedTest r Pw g) :
    E.encode (f - g) = E.encode f - E.encode g := by
  let fw : weightedTestSubmodule d r Pw := ⟨f, weightedTestSubmodule_iff.2 hf⟩
  let gw : weightedTestSubmodule d r Pw := ⟨g, weightedTestSubmodule_iff.2 hg⟩
  have hneg : IsR2WeightedTest r Pw ((-1 : ℝ) • g) := by
    exact weightedTestSubmodule_iff.1 ((-1 : ℝ) • gw).property
  calc
    E.encode (f - g) = E.encode (f + (-1 : ℝ) • g) := by
      congr 1
      simp only [neg_one_smul, sub_eq_add_neg]
    _ = E.encode f + E.encode ((-1 : ℝ) • g) := E.add _ _ hf hneg
    _ = E.encode f + (-1 : ℝ) • E.encode g := by rw [E.smul _ _ hg]
    _ = _ := by simp only [neg_one_smul, sub_eq_add_neg]

/-- Joint spatial strong measurability and weighted-test membership suffice to
encode a family measurably in the frozen weighted chart. -/
theorem fp81s21_chart_encode_stronglyMeasurable_of_weighted
    {A : Type*} [MeasurableSpace A] {d r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart d r Pw) (hP : (d : ℝ) < 2 * Pw)
    (F : A → Euc d → ℝ)
    (hF : StronglyMeasurable (fun p : A × Euc d => F p.1 p.2))
    (hreg : ∀ a, IsR2WeightedTest r Pw (F a)) :
    StronglyMeasurable (fun a => E.encode (F a)) := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  apply Measurable.stronglyMeasurable
  refine measurable_of_dist_dense_range
    (fun f : {f : Euc d → ℝ // IsR2Test f} => E.encode f) E.dense _ ?_
  intro f
  have hf : IsR2WeightedTest r Pw f :=
    chart_weighted_of_memCb hP (chart_memCb_of_test f.property)
  have hsub : StronglyMeasurable
      (fun p : A × Euc d => (F p.1 - (f : Euc d → ℝ)) p.2) :=
    hF.sub (f.property.1.continuous.measurable.comp measurable_snd).stronglyMeasurable
  have hregSub : ∀ a, ContDiff ℝ r (F a - (f : Euc d → ℝ)) :=
    fun a => (hreg a).1.sub hf.1
  have hm := (weightedSobolev_family_measurable
    (fun a => F a - (f : Euc d → ℝ)) hsub hregSub (Pw := Pw)).ennreal_toReal
  convert hm using 1
  funext a
  let fw : weightedTestSubmodule d r Pw :=
    ⟨F a, weightedTestSubmodule_iff.2 (hreg a)⟩
  let gw : weightedTestSubmodule d r Pw :=
    ⟨(f : Euc d → ℝ), weightedTestSubmodule_iff.2 hf⟩
  have hsubWeighted : IsR2WeightedTest r Pw (F a - (f : Euc d → ℝ)) := by
    exact weightedTestSubmodule_iff.1 (fw - gw).property
  rw [dist_eq_norm,
    ← fp81s21_weighted_chart_encode_sub E (hreg a) hf,
    E.norm _ hsubWeighted]

#print axioms HRS.Fp81.S21.fp81s21_chart_encode_stronglyMeasurable_of_weighted

end HRS.Fp81.S21
