import HRS.MS.R26T8AC03

/-!
# S8.2 observed-time layer, packet T8A.C04: coupled single-site updates preserve the two finite laws

If a coupling `pi` of `P`, `Q` is updated at site `i` by a kernel `K` coupling the two heat-bath kernels `KP`, `KQ`,
and `P`, `Q` are invariant for their own single-site updates, then the updated coupling has the same marginals.  For every
measurable set the two marginal masses agree pointwise in the integrand (`K XY ∘ fst⁻¹ = KP XY.1`), which gives the identity.
The only addition to the packet statement is the typeclass hypothesis that `K`, `KP`, `KQ` are s-finite kernels (needed for the measurability
of `X ↦ KP X {y | update X i y ∈ s}`; all heat-bath and coupling kernels in the application are probability kernels).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_coupled_update_marginals {d n : ℕ}
    (P Q : Measure (EucConfig d n)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (pi : Measure (EucConfig d n × EucConfig d n))
    (hfst : pi.map Prod.fst = P) (hsnd : pi.map Prod.snd = Q)
    (i : Fin n) (K : ProbabilityTheory.Kernel (EucConfig d n × EucConfig d n) (Euc d × Euc d))
    (KP KQ : ProbabilityTheory.Kernel (EucConfig d n) (Euc d))
    [ProbabilityTheory.IsSFiniteKernel K] [ProbabilityTheory.IsSFiniteKernel KP]
    [ProbabilityTheory.IsSFiniteKernel KQ]
    (hK1 : ∀ XY, (K XY).map Prod.fst = KP XY.1)
    (hK2 : ∀ XY, (K XY).map Prod.snd = KQ XY.2)
    (hP : (P.bind (fun X => (KP X).map (fun y => Function.update X i y))) = P)
    (hQ : (Q.bind (fun X => (KQ X).map (fun y => Function.update X i y))) = Q) :
    let pi' := pi.bind (fun XY => (K XY).map (fun xy =>
      (Function.update XY.1 i xy.1, Function.update XY.2 i xy.2)))
    pi'.map Prod.fst = P ∧ pi'.map Prod.snd = Q := by
  intro pi'
  have hupd : Measurable fun p : EucConfig d n × Euc d => Function.update p.1 i p.2 :=
    measurable_update' (a := i)
  have hupd1 : ∀ X : EucConfig d n, Measurable fun y : Euc d => Function.update X i y := fun X =>
    hupd.comp (measurable_const.prodMk measurable_id)
  have hg : Measurable fun p : (EucConfig d n × EucConfig d n) × (Euc d × Euc d) =>
      (Function.update p.1.1 i p.2.1, Function.update p.1.2 i p.2.2) :=
    (measurable_update'.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).prodMk
      (measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd)))
  have hg1 : ∀ XY : EucConfig d n × EucConfig d n, Measurable fun xy : Euc d × Euc d =>
      (Function.update XY.1 i xy.1, Function.update XY.2 i xy.2) := fun XY =>
    hg.comp (measurable_const.prodMk measurable_id)
  have hmeasK : Measurable fun XY : EucConfig d n × EucConfig d n => (K XY).map (fun xy : Euc d × Euc d =>
      (Function.update XY.1 i xy.1, Function.update XY.2 i xy.2)) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.map_apply (hg1 _) hs]
    exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := K) (hg hs)
  have hmeasP : Measurable fun X : EucConfig d n => (KP X).map (fun y => Function.update X i y) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.map_apply (hupd1 _) hs]
    exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := KP) (hupd hs)
  have hmeasQ : Measurable fun X : EucConfig d n => (KQ X).map (fun y => Function.update X i y) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.map_apply (hupd1 _) hs]
    exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := KQ) (hupd hs)
  constructor
  · ext s hs
    have e1 : pi'.map Prod.fst s = ∫⁻ XY, KP XY.1 {y | Function.update XY.1 i y ∈ s} ∂pi := by
      rw [Measure.map_apply measurable_fst hs]
      simp only [pi']
      rw [Measure.bind_apply (measurable_fst hs) hmeasK.aemeasurable]
      refine lintegral_congr fun XY => ?_
      rw [Measure.map_apply (hg1 XY) (measurable_fst hs)]
      have : (fun xy : Euc d × Euc d => (Function.update XY.1 i xy.1, Function.update XY.2 i xy.2)) ⁻¹'
          (Prod.fst ⁻¹' s) = Prod.fst ⁻¹' {y | Function.update XY.1 i y ∈ s} := rfl
      rw [this, ← Measure.map_apply measurable_fst (hupd1 XY.1 hs |> fun h => by exact h), hK1]
    have e2 : P s = ∫⁻ XY, KP XY.1 {y | Function.update XY.1 i y ∈ s} ∂pi := by
      conv_lhs => rw [← hP]
      rw [Measure.bind_apply hs hmeasP.aemeasurable]
      have h1 : ∀ X : EucConfig d n, (Measure.map (fun y => Function.update X i y) (KP X)) s =
          KP X {y | Function.update X i y ∈ s} := fun X => Measure.map_apply (hupd1 X) hs
      simp_rw [h1]
      have hF : Measurable fun X : EucConfig d n => KP X {y | Function.update X i y ∈ s} :=
        ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := KP) (hupd hs)
      rw [← hfst, lintegral_map hF measurable_fst]
    rw [e1, e2]
  · ext s hs
    have e1 : pi'.map Prod.snd s = ∫⁻ XY, KQ XY.2 {y | Function.update XY.2 i y ∈ s} ∂pi := by
      rw [Measure.map_apply measurable_snd hs]
      simp only [pi']
      rw [Measure.bind_apply (measurable_snd hs) hmeasK.aemeasurable]
      refine lintegral_congr fun XY => ?_
      rw [Measure.map_apply (hg1 XY) (measurable_snd hs)]
      have : (fun xy : Euc d × Euc d => (Function.update XY.1 i xy.1, Function.update XY.2 i xy.2)) ⁻¹'
          (Prod.snd ⁻¹' s) = Prod.snd ⁻¹' {y | Function.update XY.2 i y ∈ s} := rfl
      rw [this, ← Measure.map_apply measurable_snd (hupd1 XY.2 hs |> fun h => by exact h), hK2]
    have e2 : Q s = ∫⁻ XY, KQ XY.2 {y | Function.update XY.2 i y ∈ s} ∂pi := by
      conv_lhs => rw [← hQ]
      rw [Measure.bind_apply hs hmeasQ.aemeasurable]
      have h1 : ∀ X : EucConfig d n, (Measure.map (fun y => Function.update X i y) (KQ X)) s =
          KQ X {y | Function.update X i y ∈ s} := fun X => Measure.map_apply (hupd1 X) hs
      simp_rw [h1]
      have hF : Measurable fun X : EucConfig d n => KQ X {y | Function.update X i y ∈ s} :=
        ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := KQ) (hupd hs)
      rw [← hsnd, lintegral_map hF measurable_snd]
    rw [e1, e2]

end HRS.MS.R26T8A
