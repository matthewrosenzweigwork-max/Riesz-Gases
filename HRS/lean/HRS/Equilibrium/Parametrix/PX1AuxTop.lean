import HRS.Equilibrium.Parametrix.Defs

/-!
# Prop 4.13 parametrix, packet PX1: topological helpers

`Torus.mk` is an open quotient map, `offDiag` is open, and kernels that are continuous on the
open off-diagonal set and set to `0` on the diagonal are jointly measurable.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ}

theorem isOpenQuotientMap_mk : IsOpenQuotientMap (Torus.mk : Euc d → Torus d) := by
  have h1 : IsOpenQuotientMap (Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  have h2 : IsOpenQuotientMap (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) :=
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  exact h1.comp h2

theorem isOpen_offDiag : IsOpen (offDiag d) := by
  unfold offDiag
  have : Continuous fun p : Euc d × Euc d => (Torus.mk p.1, Torus.mk p.2) :=
    (Torus.continuous_mk.comp continuous_fst).prodMk (Torus.continuous_mk.comp continuous_snd)
  exact (isClosed_diagonal.isOpen_compl).preimage this

theorem measurable_offZero_of_contDiffOn {F : Torus d → Torus d → ℝ} {m : ℕ}
    (hs : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 F) (offDiag d)) :
    Measurable (Function.uncurry (offZero F)) := by
  have hq : IsOpenQuotientMap
      (Prod.map (Torus.mk : Euc d → Torus d) (Torus.mk : Euc d → Torus d)) :=
    isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk
  have hc : ContinuousOn (Function.uncurry F) {p : Torus d × Torus d | p.1 ≠ p.2} := by
    intro p hp
    have hp' : ((Torus.rep p.1, Torus.rep p.2) : Euc d × Euc d) ∈ offDiag d := by
      show Torus.mk (Torus.rep p.1) ≠ Torus.mk (Torus.rep p.2)
      rw [Torus.mk_rep, Torus.mk_rep]; exact hp
    have h1 : ContinuousAt (lift2 F) (Torus.rep p.1, Torus.rep p.2) :=
      (hs.continuousOn.continuousAt ((isOpen_offDiag).mem_nhds hp'))
    have h2 : ContinuousAt (Function.uncurry F ∘ Prod.map Torus.mk Torus.mk)
        (Torus.rep p.1, Torus.rep p.2) := h1
    rw [hq.continuousAt_comp_iff] at h2
    simp only [Prod.map, Torus.mk_rep] at h2
    exact h2.continuousWithinAt
  have hfun : Function.uncurry (offZero F) =
      {p : Torus d × Torus d | p.1 = p.2}.piecewise (fun _ => 0) (Function.uncurry F) := by
    ext ⟨x, y⟩
    simp [offZero, Set.piecewise]
  rw [hfun]
  refine ContinuousOn.measurable_piecewise (continuousOn_const) ?_ ?_
  · exact hc
  · exact isClosed_diagonal.measurableSet

end HRS.Parx

end
