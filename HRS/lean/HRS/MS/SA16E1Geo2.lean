import HRS.MS.SA16E1Geo1

/-!
# S.A.16 E1: the Jacobian determinant of `charFlow`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.Whole.AppendixALemmas

theorem e1_fderiv_bt {d : ℕ} (ν : ℝ) (w : ℝ≥0 → Fin d → ℝ) (b : ℝ → Euc d → Euc d) (s : ℝ)
    (y : Euc d) : fderiv ℝ (e1bt d ν w b s) y = fderiv ℝ (b s) (y + e1a d ν w s) :=
  fderiv_comp_add_right (f := b s) (e1a d ν w s)

theorem e1_det_formula {d m : ℕ} {B T : ℝ} (hT : 0 ≤ T) {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d (m+1) B b) (ν : ℝ) {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) (x : Euc d) {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    LinearMap.det (fderiv ℝ (fun y => charFlow d b ν w t y - e1a d ν w t) x : Euc d →ₗ[ℝ] Euc d) =
      Real.exp (-∫ s in (0:ℝ)..t, movDiv (b s) (charFlow d b ν w s x)) := by
  have hk : 1 ≤ m + 1 := by omega
  obtain ⟨Λg, -, hDB⟩ := e1_driftBounds hb ν hw (T := T)
  have hflow := e1_negFlow hk hb ν hw hw0 T
  set Ψ : ℝ → Euc d → Euc d := fun τ y => charFlow d b ν w τ y - e1a d ν w τ with hΨ
  have hB := e1_B_nonneg hb
  have hAeq : ∀ s, fderiv ℝ (e1bt d ν w b s) (Ψ s x) = fderiv ℝ (b s) (charFlow d b ν w s x) := by
    intro s
    rw [e1_fderiv_bt]
    simp [hΨ]
  have hG : Continuous (Function.uncurry fun s : ℝ => b (max s 0)) := by
    have h1 : Continuous (fun p : ℝ × Euc d => (max p.1 0, p.2)) :=
      ((continuous_fst.max continuous_const).prodMk continuous_snd)
    have := hb.1.comp_continuous h1 (fun p => ⟨show (0:ℝ) ≤ max p.1 0 from le_max_right _ _, trivial⟩)
    exact this
  have hmeas : ∀ v : Euc d, Measurable (fun s : ℝ =>
      fderiv ℝ (b (max s 0)) (charFlow d b ν w (max s 0) x) v) := by
    intro v
    have hc : Continuous (fun s : ℝ => (s, charFlow d b ν w (max s 0) x)) :=
      continuous_id.prodMk ((e1_flow_cont hk hb ν hw x).comp (continuous_id.max continuous_const))
    exact (measurable_fderiv_apply_const_with_param ℝ hG v).comp hc.measurable
  have hLiou := e1_liouville (A := fun s => fderiv ℝ (e1bt d ν w b s) (Ψ s x))
    (M := fun τ => fderiv ℝ (Ψ τ) x) (T := T) (L := B) hT
    (fun s hs => by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
      exact e1_hdb hb ν w s hs 1 le_rfl (by omega) _)
    (fun v => by
      refine (hmeas v).aestronglyMeasurable.congr ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
      simp only [hAeq s, max_eq_left hs.1])
    (fun v => e1_col_cont hT hDB hflow x v)
    (fun τ hτ v => HRS.MS.FlowB.flow_fderiv_integral hT hDB hflow τ hτ x v) t ht
  have hdet := e1_det_eq (fderiv ℝ (Ψ t) x)
  have hN : e1N (fun _ => fderiv ℝ (Ψ t) x) 0 = e1N (fun τ => fderiv ℝ (Ψ τ) x) t := rfl
  rw [hN, hLiou] at hdet
  rw [hdet]
  congr 2
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [movDiv, hAeq s]

end HRS.Whole.AppendixA.Phase2SA16Evolution
