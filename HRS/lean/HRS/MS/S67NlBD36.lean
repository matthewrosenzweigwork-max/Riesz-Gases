import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovLinAux15
import HRS.MS.S67NlBD00
import HRS.MS.S67NlBD34

/-!
# S6.7nl.36: the lifted Bochner integral agrees with the original `L²` integral
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.

The continuous linear map `L = Φ ∘ j : Σ^qlev → Σ^0 ≃ L²` (the actual `mov2d_j` and `mov2d_Phi`)
sends the lift to the inclusion of the original integrand for every `v ∈ (r, T]`, hence a.e. on
`[r, T]`.  `L` commutes with the lifted Bochner integral (`hI`) and the centered-submodule inclusion
with the original integral (`hL`); `movlin_memOsc_of_lev` returns physical membership.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

theorem s67bd_lift_compatibility (H : Mov2dTh d s β q ρ₀)
    (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x))
    (qlev r T : ℝ) (hqlev : 0 ≤ qlev) (hrT : r ≤ T)
    (h : ℝ → MovL2Zero ρ₀)
    (hm : ∀ v ∈ Ioc r T, MemOsc qlev (movFun (s67bd_Tdag H g hg (v - r) (h v))))
    (hI : IntegrableOn (s67bd_lift H g hg qlev r h) (Icc r T) volume)
    (hL : IntegrableOn (fun v => s67bd_Tdag H g hg (v - r) (h v)) (Icc r T) volume) :
    mov2d_Phi d (mov2d_j hqlev (∫ v in Icc r T, s67bd_lift H g hg qlev r h v)) =
      ((∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v)) :
        Lp ℝ 2 (volume : Measure (Euc d))) ∧
    MemOsc qlev (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v))) := by
  obtain ⟨Lm, hLapp⟩ : ∃ Lm : OscSpace d qlev →L[ℝ] Lp ℝ 2 (volume : Measure (Euc d)),
      ∀ z, Lm z = mov2d_Phi d (mov2d_j hqlev z) :=
    ⟨((mov2d_Phi d).toLinearIsometry.toContinuousLinearMap).comp (mov2d_j hqlev), fun z => rfl⟩
  obtain ⟨ι, hιapp⟩ : ∃ ι : MovL2Zero ρ₀ →L[ℝ] Lp ℝ 2 (volume : Measure (Euc d)),
      ∀ x, ι x = (x : Lp ℝ 2 (volume : Measure (Euc d))) :=
    ⟨(MovL2Zero ρ₀).subtypeL, fun x => rfl⟩
  -- pointwise compatibility off the diagonal
  have hpt : ∀ v ∈ Ioc r T, Lm (s67bd_lift H g hg qlev r h v) =
      ((s67bd_Tdag H g hg (v - r) (h v) : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d))) := by
    intro v hv
    have hmv := hm v hv
    have hl : s67bd_lift H g hg qlev r h v =
        OscSpace.ofFun qlev (movFun (s67bd_Tdag H g hg (v - r) (h v))) := by
      simp only [s67bd_lift, hv.1, ↓reduceIte]
    rw [hl, hLapp, mov2d_j_ofFun hqlev hmv, mov2d_Phi_ofFun hmv.1]
    exact Lp.toLp_coeFn _ hmv.1
  have hae : ∀ᵐ v ∂(volume.restrict (Icc r T)),
      Lm (s67bd_lift H g hg qlev r h v) =
        ((s67bd_Tdag H g hg (v - r) (h v) : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d))) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hpt)
  have h1 : Lm (∫ v in Icc r T, s67bd_lift H g hg qlev r h v) =
      ∫ v in Icc r T, Lm (s67bd_lift H g hg qlev r h v) :=
    (ContinuousLinearMap.integral_comp_comm Lm hI).symm
  have h2 : ((∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v) : MovL2Zero ρ₀) :
        Lp ℝ 2 (volume : Measure (Euc d))) =
      ∫ v in Icc r T, ((s67bd_Tdag H g hg (v - r) (h v) : MovL2Zero ρ₀) :
        Lp ℝ 2 (volume : Measure (Euc d))) :=
    by
    have := (ContinuousLinearMap.integral_comp_comm ι hL).symm
    simpa only [hιapp] using this
  have hmain : mov2d_Phi d (mov2d_j hqlev (∫ v in Icc r T, s67bd_lift H g hg qlev r h v)) =
      ((∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v)) :
        Lp ℝ 2 (volume : Measure (Euc d))) := by
    rw [← hLapp, h1]
    exact integral_congr_ae hae
  refine ⟨hmain, ?_⟩
  have hfL : MemLp (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v))) 2 (volume : Measure (Euc d)) :=
    Lp.memLp ((∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v) : MovL2Zero ρ₀) :
      Lp ℝ 2 (volume : Measure (Euc d)))
  have hz : mov2d_j hqlev (∫ v in Icc r T, s67bd_lift H g hg qlev r h v) =
      OscSpace.ofFun 0 (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v))) := by
    apply (mov2d_Phi d).injective
    rw [hmain, mov2d_Phi_ofFun hfL, ← h2]
    exact (Lp.toLp_coeFn _ hfL).symm
  exact (movlin_memOsc_of_lev hqlev hfL hz).1

end HRS.MS.BreakdownS67
