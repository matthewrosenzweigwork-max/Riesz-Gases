import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.WhoAux8

/-!
# S6.7 nonlinear, packet S6.7nl.65: measurability of the finite real gradient-norm path

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4844-4851, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definition: `s67bd_Y`.
The `C_b^j` norm of `grad f_r` equals `sum_{i<=j} sup_x |D^{i+1} f_r(x)|` (the Riesz isometry
`toDual` preserves iterated-derivative norms); each spatial supremum of a continuous function is
a supremum along one dense sequence, and `who_sm_iter` on the time subtype gives measurability of
each evaluation of the iterated derivative.
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

def s67bd_Y (j : ℕ) (f : ℝ → Euc d → ℝ) (r : ℝ) : ℝ :=
  (cbNormVecE j (fun x => gradient (f r) x)).toReal

lemma s67bd_cbNormVecE_gradient (j : ℕ) (g : Euc d → ℝ) :
    cbNormVecE j (fun x => gradient g x) =
      ∑ i ∈ Finset.range (j + 1), ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ (i + 1) g x‖ := by
  unfold cbNormVecE
  refine Finset.sum_congr rfl fun i _ => ?_
  refine iSup_congr fun x => ?_
  congr 1
  let L : StrongDual ℝ (Euc d) ≃ₗᵢ[ℝ] Euc d :=
    { toLinearEquiv :=
        { toFun := (InnerProductSpace.toDual ℝ (Euc d)).symm
          map_add' := map_add _
          map_smul' := fun c φ => by simp
          invFun := InnerProductSpace.toDual ℝ (Euc d)
          left_inv := fun φ => by simp
          right_inv := fun x => by simp }
      norm_map' := fun φ => LinearIsometryEquiv.norm_map _ φ }
  have e : (fun x => gradient g x) = L ∘ fderiv ℝ g := rfl
  rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

lemma s67bd_iSup_denseSeq {E : Type*} [TopologicalSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    {g : E → ℝ≥0∞} (hg : Continuous g) :
    ⨆ x, g x = ⨆ n, g (TopologicalSpace.denseSeq E n) := by
  refine le_antisymm ?_ (iSup_le fun n => le_iSup g _)
  refine iSup_le fun x => ?_
  have hcl : IsClosed (g ⁻¹' Set.Iic (⨆ n, g (TopologicalSpace.denseSeq E n))) :=
    isClosed_Iic.preimage hg
  have hsub : Set.range (TopologicalSpace.denseSeq E) ⊆
      g ⁻¹' Set.Iic (⨆ n, g (TopologicalSpace.denseSeq E n)) := by
    rintro _ ⟨n, rfl⟩
    exact le_iSup (fun n => g (TopologicalSpace.denseSeq E n)) n
  have h2 : x ∈ closure (Set.range (TopologicalSpace.denseSeq E)) := by
    rw [(TopologicalSpace.denseRange_denseSeq E).closure_eq]; trivial
  exact closure_minimal hsub hcl h2

theorem s67bd_gradient_norm_measurable (d j : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → Euc d → ℝ)
    (hc : ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))))
    (hreg : ∀ r ∈ Icc (0 : ℝ) T, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (f r))
    (hfin : ∀ r ∈ Icc (0 : ℝ) T, cbNormVecE j (fun x => gradient (f r) x) < ⊤) :
    Measurable (fun r : Icc (0 : ℝ) T => cbNormVecE j (fun x => gradient (f r) x)) ∧
    AEStronglyMeasurable (s67bd_Y j f) (volume.restrict (Icc (0 : ℝ) T)) := by
  have hmeasf : ∀ x : Euc d, StronglyMeasurable (fun r : Icc (0 : ℝ) T => f r.1 x) := fun x => by
    have : Continuous (fun r : Icc (0 : ℝ) T => f r.1 x) :=
      hc.comp_continuous (continuous_subtype_val.prodMk continuous_const)
        (fun r => ⟨r.2, mem_univ _⟩)
    exact this.stronglyMeasurable
  have hsm := HRS.MS.Who.who_sm_iter (Ω := Icc (0 : ℝ) T) (G := fun r x => f r.1 x) (k := j + 1)
    (fun r => hreg r.1 r.2) hmeasf
  have hmeas : Measurable (fun r : Icc (0 : ℝ) T => cbNormVecE j (fun x => gradient (f r) x)) := by
    have e : (fun r : Icc (0 : ℝ) T => cbNormVecE j (fun x => gradient (f r) x)) = fun r =>
        ∑ i ∈ Finset.range (j + 1), ⨆ n : ℕ,
          ENNReal.ofReal ‖iteratedFDeriv ℝ (i + 1) (f r.1) (TopologicalSpace.denseSeq (Euc d) n)‖ := by
      funext r
      rw [s67bd_cbNormVecE_gradient]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i + 1 ≤ j + 1 := by have := Finset.mem_range.1 hi; omega
      exact s67bd_iSup_denseSeq (g := fun x => ENNReal.ofReal ‖iteratedFDeriv ℝ (i + 1) (f r.1) x‖)
        (ENNReal.continuous_ofReal.comp
          ((hreg r.1 r.2).continuous_iteratedFDeriv (by exact_mod_cast hi')).norm)
    rw [e]
    refine Finset.measurable_sum _ fun i hi => Measurable.iSup fun n => ?_
    have hi' : i + 1 ≤ j + 1 := by have := Finset.mem_range.1 hi; omega
    exact ENNReal.measurable_ofReal.comp (hsm (i + 1) hi' _).norm.measurable
  refine ⟨hmeas, ?_⟩
  have h2 : Measurable (fun r : Icc (0 : ℝ) T => s67bd_Y j f r.1) :=
    ENNReal.measurable_toReal.comp hmeas
  have h3 : AEMeasurable (s67bd_Y j f) (volume.restrict (Icc (0 : ℝ) T)) :=
    (aemeasurable_restrict_iff_comap_subtype measurableSet_Icc).2 h2.aemeasurable
  exact h3.aestronglyMeasurable

end HRS.MS.BreakdownS67
